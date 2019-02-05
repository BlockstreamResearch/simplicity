# From https://fastcompression.blogspot.com/2019/01/compiler-warnings.html
CFLAGS := -Werror -Wall -Wextra -Wcast-qual -Wcast-align -Wstrict-aliasing -Wpointer-arith -Winit-self -Wshadow -Wswitch-enum -Wstrict-prototypes -Wmissing-prototypes -Wredundant-decls -Wfloat-equal -Wundef -Wconversion

ifneq ($(doCheck), 1)
CFLAGS := $(CFLAGS) -DNDEBUG
endif

LDLIBS := -lsha256compression
test_deserialize: test_deserialize.o dag.o deserialize.o hashBlock.o type.o typeInference.o
	$(CC) $^ -o $@ $(LDLIBS)

install: test_deserialize
	mkdir -p $(out)/bin
	cp $^ $(out)/bin/

check: test_deserialize
	./test_deserialize
