CFLAGS = -Wall
LDLIBS = -lsha256compression
test_deserialize: test_deserialize.o dag.o deserialize.o hashBlock.o
	$(CC) $^ -o $@ $(LDLIBS)

install: test_deserialize
	mkdir -p $(out)/bin
	cp $^ $(out)/bin/

check: test_deserialize
	./test_deserialize
