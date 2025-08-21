FROM debian:stable-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /simplicity

COPY C/ .

RUN make -j$(nproc) X86_SHANI_CXXFLAGS="-msse4.1 -msha"

RUN make install out=/usr/local

RUN make check

# The library is at /usr/local/lib/libElementsSimplicity.a
# The headers are in /usr/local/include/
CMD ["/bin/bash"]