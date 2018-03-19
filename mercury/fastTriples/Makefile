all: clean
	mmc --make libadts
	mmc --make libparser
	mmc --make main

debug: clean
	mmc --make --grade=asm_fast.gc.debug.stseg --debug main

clean:
	rm -rf Mercury
	rm -f main *.mh *.init *.o *.c *.d *.err *.c_date *.a *.so

