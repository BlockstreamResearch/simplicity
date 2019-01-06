CFLAGS = -I include -fPIC

libsha256compression.so: sha256/compression.o
	$(CC) $(CFLAGS) -shared $^ -o $@

install: libsha256compression.so
	mkdir -p $(out)/lib
	cp $^ $(out)/lib/
	cp -r include $(out)/
