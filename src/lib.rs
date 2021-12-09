use std::convert::TryInto;
use std::collections::HashMap;
use std::ffi::c_void;
use std::{ptr, slice};

struct StackMapParser<'a> {
    data: &'a[u8],
    offset: usize,
}

struct Function {
    addr: u64,
    stack_size: u64,
    record_count: u64,
}

struct Record {
    id: u64,
    offset: u32,
    locs: Vec<Location>,
    liveouts: Vec<LiveOut>,
}

enum Location {
    Register(u16),
    Direct(u16, u32),
    Indirect(u16, u32),
    Constant(i32),
    ConstIndex(u32),
}

enum LocOffset {
    Off(u32),
    Const(i32),
}

struct LiveOut {
    dwreg: u16,
    size: u8,
}

impl StackMapParser<'_> {
    pub fn parse(data: &[u8]) -> Result<SMQuery, &'static str> {
        let mut smp = StackMapParser {
            data,
            offset: 0,
        };
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

        println!("{} {} {}", num_funcs, num_consts, num_recs);

        let funcs = self.read_functions(num_funcs);
        let consts = self.read_consts(num_consts);

        let mut map = HashMap::new();

        // Check that the records match the sum of the expected records per function.
        assert_eq!(funcs.iter().map(|f| f.record_count).sum::<u64>(), u64::from(num_recs));
        for f in funcs {
            let records = self.read_records(f.record_count);
            for r in records {
                let key = f.addr + u64::from(r.offset);
                println!("key: {:x}", key);
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
            let stack_size = self.read_u64();
            let record_count = self.read_u64();
            v.push(Function { addr, stack_size, record_count });
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

    fn read_records(&mut self, num: u64) -> Vec<Record> {
        let mut v = Vec::new();
        for _ in 0..num {
            let id = self.read_u64();
            let offset = self.read_u32();
            println!("{} {}", id, offset);
            self.read_u16();
            let num_locs = self.read_u16();
            let locs = self.read_locations(num_locs);
            // Padding
            self.align_8();
            self.read_u16();
            let num_liveouts = self.read_u16();
            let liveouts = self.read_liveouts(num_liveouts);
            self.align_8();
            v.push(Record{ id, offset, locs, liveouts });
        }
        v
    }

    fn read_locations(&mut self, num: u16) -> Vec<Location> {
        let mut v = Vec::new();
        for _ in 0..num {
            let kind = self.read_u8();
            self.read_u8();
            let size = self.read_u16();
            let dwreg = self.read_u16();
            self.read_u16();
            println!("kind: {}", kind); 
            println!("dwreg: {}", dwreg); 

            let location = match kind {
                0x01 => {
                    self.read_u32();
                    Location::Register(dwreg)
                },
                0x02 => {
                    let offset = self.read_u32();
                    println!("offset: {}", offset); 
                    Location::Direct(dwreg, offset)
                },
                0x03 => {
                    let offset = self.read_u32();
            println!("offset: {}", offset); 
                    Location::Indirect(dwreg, offset)
                },
                0x04 => {
                    let offset = self.read_i32();
            println!("offset: {}", offset); 
                    Location::Constant(offset)
                },
                0x05 => {
                    let offset = self.read_u32();
            println!("offset: {}", offset); 
                    Location::ConstIndex(offset)
                },
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
            v.push(LiveOut{ dwreg, size});
        }
        v
    }

    fn align_8(&mut self) {
        self.offset += (8 - (self.offset % 8)) % 8;
    }

    fn read_u8(&mut self) -> u8 {
        let d = u8::from_ne_bytes(self.data[self.offset..self.offset+1].try_into().unwrap());
        self.offset += 1;
        d
    }

    fn read_u16(&mut self) -> u16 {
        let d = u16::from_ne_bytes(self.data[self.offset..self.offset+2].try_into().unwrap());
        self.offset += 2;
        d
    }

    fn read_u32(&mut self) -> u32 {
        let d = u32::from_ne_bytes(self.data[self.offset..self.offset+4].try_into().unwrap());
        self.offset += 4;
        d
    }

    fn read_i32(&mut self) -> i32 {
        let d = i32::from_ne_bytes(self.data[self.offset..self.offset+4].try_into().unwrap());
        self.offset += 4;
        d
    }

    fn read_u64(&mut self) -> u64 {
        let d = u64::from_ne_bytes(self.data[self.offset..self.offset+8].try_into().unwrap());
        self.offset += 8;
        d
    }
}

struct SMQuery {
    map: HashMap<u64, Record>,
}

impl SMQuery {
    fn get_record(&self, addr: u64) -> Option<&Record> {
        self.map.get(&addr)
    }

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
            println!("readfromstack: {:?} {} {:?}", ptr, off, ptr.offset(off));
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
pub extern "C" fn __yk_stopgap(addr: *const c_void, size: usize, retaddr: usize, rsp: *const c_void) {
    // Read stackmap here?
    // Then init stopgap interp, basically never returning to the llvm_deopt call?
    println!("stopgap! {:?} {}", addr as *mut u8, size);
    println!("ret addr: {:x}", retaddr);
    println!("rsp addr: {:?}", rsp);

    let registers = Registers::from_ptr(rsp);
    println!("registers.rsp: {}", registers.rsp);

    let slice = unsafe { slice::from_raw_parts(addr as *mut u8, size) };
    let smq = StackMapParser::parse(slice).unwrap();
    let locs = smq.get_locations(retaddr.try_into().unwrap()).unwrap();
    for l in locs {
        match l {
            Location::Direct(reg, off) => {
                // A direct location should always be in relation to RSP.
                assert_eq!(*reg, 7);
                // We need to add 2 bytes to the value of RSP to factor in the return address and
                // the pushed RBP value of the previous frame.
                // FIXME: Only on x64. Other architectures need different values.
                let addr = registers.get(*reg) + (*off as usize) + 16;
                let v = unsafe { ptr::read::<u8>((registers.get(*reg) + (*off as usize) + 16) as *mut u8) };
                println!("Direct: {}", v);
            }
            Location::Constant(v) => {
                println!("Constant: {}", v);
            }
            _ => todo!()
        }
    }
}

#[cfg(test)]
mod test {

    use super::{StackMapParser, Location};
    use std::fs::File;
    use std::io::{Cursor, Read};

    #[test]
    fn test_basic() {
        let mut file = File::open("stackmap.dump").unwrap();
        let mut data = Vec::new();
        file.read_to_end(&mut data);
        let smq = StackMapParser::parse(data.as_slice()).unwrap();
        let faddr = 0x7f0c6bb32050;
        let off = 113;
        let locs = smq.get_locations(faddr + off);
        assert!(locs.is_some());
        let mut iter = locs.unwrap().iter();
        assert!(matches!(iter.next().unwrap(), Location::Constant(0)));
        assert!(matches!(iter.next().unwrap(), Location::Constant(0)));
        assert!(matches!(iter.next().unwrap(), Location::Constant(3)));
        assert!(matches!(iter.next().unwrap(), Location::Direct(7, 28)));
        assert!(matches!(iter.next().unwrap(), Location::Direct(7, 24)));
        assert!(matches!(iter.next().unwrap(), Location::Direct(7, 20)));
    } 
}
