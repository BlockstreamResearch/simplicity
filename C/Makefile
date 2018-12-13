test_deserialize: test_deserialize.o deserialize.o
	$(CC) $(CFLAGS) $^ -o $@

install: test_deserialize
	mkdir -p $(out)/bin
	cp $^ $(out)/bin/

check: test_deserialize
	./test_deserialize
