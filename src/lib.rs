use std::collections::HashMap;
use std::convert::TryFrom;
use std::convert::TryInto;
use std::ffi::c_void;
use std::{ptr, slice};

/// Parses LLVM stackmaps version 3 from a given address. Provides a way to query relevant
/// locations given the return address of a `__llvm_deoptimize` function.
/// Note that LLVM currently only supports stackmaps for 64 bit architectures. Once they support
/// others we will need to either make this parser more dynamic or create a new one for each
/// architecture.
struct StackMapParser<'a> {
    data: &'a [u8],
    offset: usize,
}

struct Function {
    addr: u64,
    record_count: u64,
}

struct Record {
    offset: u32,
    locs: Vec<Location>,
    liveouts: Vec<LiveOut>,
}

#[derive(Debug)]
enum Location {
    Register(u16),
    Direct(u16, i32),
    Indirect(u16, i32),
    Constant(u32),
    LargeConstant(u64),
}

#[allow(dead_code)]
struct LiveOut {
    dwreg: u16,
    size: u8,
}

impl StackMapParser<'_> {
    pub fn parse(data: &[u8]) -> Result<SMQuery, &'static str> {
        let mut smp = StackMapParser { data, offset: 0 };
        smp.read()
    }

    fn read(&mut self) -> Result<SMQuery, &'static str> {
        // Read version number.
        if self.read_u8() != 3 {
            return Err("Only stackmap format version 3 is supported.");
        }

        // Reserved
        assert_eq!(self.read_u8(), 0);
        assert_eq!(self.read_u16(), 0);

        let num_funcs = self.read_u32();
        let num_consts = self.read_u32();
        let num_recs = self.read_u32();

        let funcs = self.read_functions(num_funcs);
        let consts = self.read_consts(num_consts);

        let mut map = HashMap::new();

        // Check that the records match the sum of the expected records per function.
        assert_eq!(
            funcs.iter().map(|f| f.record_count).sum::<u64>(),
            u64::from(num_recs)
        );

        // Parse records.
        for f in funcs {
            let records = self.read_records(f.record_count, &consts);
            for r in records {
                let key = f.addr + u64::from(r.offset);
                map.insert(key, r);
            }
        }

        Ok(SMQuery { map })
    }

    fn read_functions(&mut self, num: u32) -> Vec<Function> {
        let mut v = Vec::new();
        for _ in 0..num {
            let addr = self.read_u64();
            println!("f: {:x}", addr);
            let _stack_size = self.read_u64();
            let record_count = self.read_u64();
            v.push(Function { addr, record_count });
        }
        v
    }

    fn read_consts(&mut self, num: u32) -> Vec<u64> {
        let mut v = Vec::new();
        for _ in 0..num {
            v.push(self.read_u64());
        }
        v
    }

    fn read_records(&mut self, num: u64, consts: &Vec<u64>) -> Vec<Record> {
        let mut v = Vec::new();
        for _ in 0..num {
            let _id = self.read_u64();
            let offset = self.read_u32();
            self.read_u16();
            let num_locs = self.read_u16();
            let locs = self.read_locations(num_locs, consts);
            // Padding
            self.align_8();
            self.read_u16();
            let num_liveouts = self.read_u16();
            let liveouts = self.read_liveouts(num_liveouts);
            self.align_8();
            v.push(Record {
                offset,
                locs,
                liveouts,
            });
        }
        v
    }

    fn read_locations(&mut self, num: u16, consts: &Vec<u64>) -> Vec<Location> {
        let mut v = Vec::new();
        for _ in 0..num {
            let kind = self.read_u8();
            self.read_u8();
            let _size = self.read_u16();
            let dwreg = self.read_u16();
            self.read_u16();

            let location = match kind {
                0x01 => {
                    self.read_i32();
                    Location::Register(dwreg)
                }
                0x02 => {
                    let offset = self.read_i32();
                    Location::Direct(dwreg, offset)
                }
                0x03 => {
                    let offset = self.read_i32();
                    Location::Indirect(dwreg, offset)
                }
                0x04 => {
                    let offset = self.read_u32();
                    Location::Constant(offset)
                }
                0x05 => {
                    let offset = self.read_i32();
                    Location::LargeConstant(consts[usize::try_from(offset).unwrap()])
                }
                _ => unreachable!(),
            };

            v.push(location)
        }
        v
    }

    fn read_liveouts(&mut self, num: u16) -> Vec<LiveOut> {
        let mut v = Vec::new();
        for _ in 0..num {
            let dwreg = self.read_u16();
            let size = self.read_u8();
            v.push(LiveOut { dwreg, size });
        }
        v
    }

    fn align_8(&mut self) {
        self.offset += (8 - (self.offset % 8)) % 8;
    }

    fn read_u8(&mut self) -> u8 {
        let d = u8::from_ne_bytes(self.data[self.offset..self.offset + 1].try_into().unwrap());
        self.offset += 1;
        d
    }

    fn read_u16(&mut self) -> u16 {
        let d = u16::from_ne_bytes(self.data[self.offset..self.offset + 2].try_into().unwrap());
        self.offset += 2;
        d
    }

    fn read_u32(&mut self) -> u32 {
        let d = u32::from_ne_bytes(self.data[self.offset..self.offset + 4].try_into().unwrap());
        self.offset += 4;
        d
    }

    fn read_i32(&mut self) -> i32 {
        let d = i32::from_ne_bytes(self.data[self.offset..self.offset + 4].try_into().unwrap());
        self.offset += 4;
        d
    }

    fn read_u64(&mut self) -> u64 {
        let d = u64::from_ne_bytes(self.data[self.offset..self.offset + 8].try_into().unwrap());
        self.offset += 8;
        d
    }
}

/// Maps stackmap records to the addresses where they are relevant. Allows users to retrieve the
/// appropriate record during deoptimisation.
struct SMQuery {
    map: HashMap<u64, Record>,
}

impl SMQuery {
    #[allow(dead_code)]
    fn get_record(&self, addr: u64) -> Option<&Record> {
        self.map.get(&addr)
    }

    #[allow(dead_code)]
    fn get_liveout(&self, addr: u64) -> Option<&Vec<LiveOut>> {
        self.map.get(&addr).map(|r| &r.liveouts)
    }

    /// Get all locations given the return address of a __llvm_deoptimize function.
    fn get_locations(&self, addr: u64) -> Option<&Vec<Location>> {
        self.map.get(&addr).map(|r| &r.locs)
    }
}

struct Registers {
    rax: usize,
    rdx: usize,
    rcx: usize,
    rbx: usize,
    rsi: usize,
    rdi: usize,
    rsp: usize,
}

impl Registers {
    fn from_ptr(ptr: *const c_void) -> Registers {
        Registers {
            rax: Registers::read_from_stack(ptr, 0),
            rdx: Registers::read_from_stack(ptr, 1),
            rcx: Registers::read_from_stack(ptr, 2),
            rbx: Registers::read_from_stack(ptr, 3),
            rsi: Registers::read_from_stack(ptr, 4),
            rdi: Registers::read_from_stack(ptr, 5),
            rsp: Registers::read_from_stack(ptr, 6),
        }
    }

    fn read_from_stack(rsp: *const c_void, off: isize) -> usize {
        unsafe {
            let ptr = rsp as *const usize;
            ptr::read::<usize>(ptr.offset(off))
        }
    }

    fn get(&self, id: u16) -> usize {
        match id {
            0 => self.rax,
            1 => self.rdx,
            2 => self.rcx,
            3 => self.rbx,
            4 => self.rsi,
            5 => self.rdi,
            6 => unreachable!("We currently have no way to access RBP of the previous stackframe."),
            7 => self.rsp,
            _ => unreachable!(),
        }
    }
}

#[no_mangle]
pub extern "C" fn __yk_stopgap(
    addr: *const c_void,
    size: usize,
    retaddr: usize,
    rsp: *const c_void,
) {
    // Restore saved registers from the stack.
    let registers = Registers::from_ptr(rsp);

    // Parse the stackmap.
    let slice = unsafe { slice::from_raw_parts(addr as *mut u8, size) };
    let smq = StackMapParser::parse(slice).unwrap();
    let locs = smq.get_locations(retaddr.try_into().unwrap()).unwrap();

    // Extract live values from the stackmap.
    // FIXME: Until we have a stopgap interpreter we simply print the values.
    for l in locs {
        match l {
            Location::Direct(reg, off) => {
                // When using `llvm.experimental.deoptimize` then direct locations should always be
                // in relation to RSP.
                assert_eq!(*reg, 7);
                // We need to add 2 bytes to the value of RSP to factor in the return address and
                // the pushed RBP value of the previous frame.
                let addr = registers.get(*reg) + (*off as usize) + 16;
                let v = unsafe { ptr::read::<u8>(addr as *mut u8) };
                println!("Direct: {}", v);
            }
            Location::Constant(v) => {
                println!("Constant: {}", v);
            }
            _ => todo!(),
        }
    }
}

#[cfg(test)]
mod test {

    use super::{Location, StackMapParser};
    use object::{Object, ObjectSection};
    use std::env;
    use std::fs;
    use std::path::PathBuf;
    use std::process::Command;

    fn build_test(target: &str) {
        let md = env::var("CARGO_MANIFEST_DIR").unwrap();
        let mut src = PathBuf::from(md);
        src.push("tests");
        env::set_current_dir(&src).unwrap();

        let res = Command::new("make").arg(target).output().unwrap();
        if !res.status.success() {
            eprintln!("Building test input failed: {:?}", res);
            panic!();
        }
    }

    fn load_bin(target: &str) -> Vec<u8> {
        build_test(target);
        let md = env::var("CARGO_MANIFEST_DIR").unwrap();
        let mut src = PathBuf::from(md);
        src.push("tests");
        src.push(target);
        fs::read(src).unwrap()
    }

    #[test]
    fn test_simple() {
        let data = load_bin("simple.o");
        let objfile = object::File::parse(&*data).unwrap();
        let smsec = objfile.section_by_name(".llvm_stackmaps").unwrap();
        let smq = StackMapParser::parse(smsec.data().unwrap()).unwrap();
        let locs = &smq.map.iter().nth(0).unwrap().1.locs;
        assert_eq!(locs.len(), 2);
        assert!(matches!(locs[0], Location::Direct(6, -4)));
        assert!(matches!(locs[1], Location::Direct(6, -8)));
    }

    #[test]
    fn test_deopt() {
        let data = load_bin("deopt.o");
        let objfile = object::File::parse(&*data).unwrap();
        let smsec = objfile.section_by_name(".llvm_stackmaps").unwrap();
        let smq = StackMapParser::parse(smsec.data().unwrap()).unwrap();
        let locs = &smq.map.iter().nth(0).unwrap().1.locs;
        assert_eq!(locs.len(), 5);
        assert!(matches!(locs[0], Location::Constant(0)));
        assert!(matches!(locs[1], Location::Constant(0)));
        assert!(matches!(locs[2], Location::Constant(2)));
        assert!(matches!(locs[3], Location::Direct(7, 12)));
        assert!(matches!(locs[4], Location::Direct(7, 8)));
    }
}
