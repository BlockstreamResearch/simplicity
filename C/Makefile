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

# In some cases jets may not use their 'src' or 'env' parameters.
jets.o: jets.c
	$(CC) -c $(CFLAGS) $(CWARN) -Wno-unused-parameter $(CPPFLAGS) -o $@ $<

primitive/elements/jets.o: primitive/elements/jets.c
	$(CC) -c $(CFLAGS) $(CWARN) -Wno-unused-parameter -Wno-switch-enum -Wswitch $(CPPFLAGS) -o $@ $<

%.o: %.c
	$(CC) -c $(CFLAGS) $(CWARN) $(CPPFLAGS) -o $@ $<

test: test.o bitstream.o dag.o deserialize.o eval.o frame.o hashBlock.o jets.o jetTable.o schnorr1.o schnorr8.o sha256.o type.o typeInference.o primitive/elements/jets.o
	$(CC) $^ -o $@ $(LDLIBS)

install: test
	mkdir -p $(out)/bin
	cp $^ $(out)/bin/

check: test
	./test
