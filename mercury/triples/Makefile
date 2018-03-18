all: clean
	mmc --make libadts
	mmc --make libparser
	mmc --make main

debug: clean
	mmc --use-grade-subdirs --decl-debug --stack-segments adts.m
	mmc --use-grade-subdirs --decl-debug --stack-segments parser.m
	mmc --use-grade-subdirs --decl-debug --stack-segments main.m

clean:
	rm -rf Mercury
	rm -f *.mh *.init *.o *.c *.d *.err *.c_date *.a *.so

