simple.o:
	clang simple.ll -o simple.o

deopt.o:
	clang deopt.ll -o deopt.o

simple.ll:
	clang -emit-llvm -S -o simple.ll -c simple.c

deopt.ll:
	clang -emit-llvm -S -o deopt.ll -c deopt.c

clean:
	rm simple.o
	rm deopt.o
