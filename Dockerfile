FROM ubuntu:latest
COPY configure /configure
RUN apt-get -qq update \
    && apt install -y \
	libc6-dev-i386 \
        gcc \
        make \
        m4 \
        ocaml-nox \
        ocaml-native-compilers \
        camlp4-extra opam \
    && opam init \
    && eval `opam config env` \
    && ./configure \
    && git clone https://github.com/weakmemory/imm.git \
    && cd imm \
    && make -j4 \
