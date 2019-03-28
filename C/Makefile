# From https://fastcompression.blogspot.com/2019/01/compiler-warnings.html
CWARN := -Werror -Wall -Wextra -Wcast-qual -Wcast-align -Wstrict-aliasing -Wpointer-arith -Winit-self -Wshadow -Wswitch-enum -Wstrict-prototypes -Wmissing-prototypes -Wredundant-decls -Wfloat-equal -Wundef -Wconversion

ifneq ($(doCheck), 1)
CPPFLAGS := $(CPPFLAGS) -DNDEBUG
endif

LDLIBS := -lsha256compression

jetTable.c: jetTable.gperf
	gperf --output-file=$@ $^

jetTable.o: jetTable.c
	$(CC) -c $(CFLAGS) $(CPPFLAGS) -o $@ $<

%.o: %.c
	$(CC) -c $(CFLAGS) $(CWARN) $(CPPFLAGS) -o $@ $<

test: test.o dag.o deserialize.o eval.o frame.o hashBlock.o jets.o jetTable.o schnorr1.o schnorr8.o type.o typeInference.o
	$(CC) $^ -o $@ $(LDLIBS)

install: test
	mkdir -p $(out)/bin
	cp $^ $(out)/bin/

check: test
	./test
