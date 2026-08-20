# Builds the differential corpus: real ELF binaries, each kept twice.
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
	build-essential gcc-x86-64-linux-gnu binutils-x86-64-linux-gnu \
	gcc-aarch64-linux-gnu binutils-aarch64-linux-gnu \
	curl ca-certificates xz-utils file make autoconf automake libtool bison \
	&& rm -rf /var/lib/apt/lists/*

WORKDIR /src
COPY build.sh /usr/local/bin/build-corpus
RUN chmod +x /usr/local/bin/build-corpus
ENTRYPOINT ["/usr/local/bin/build-corpus"]
