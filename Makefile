CFLAGS=-std=c11 -g -static

xcc: xcc.c

test: xcc
	./test.sh

clean:
	rm -f xcc *.o *~ tmp*

.PHONY: test clean