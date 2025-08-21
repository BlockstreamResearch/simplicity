FROM coqorg/coq:8.17.1
USER root
RUN DEBIAN_FRONTEND=noninteractive TZ=Etc/UTC \
    apt-get update && apt-get install -y --no-install-recommends \
        make \
        wget

USER coq

RUN opam update
RUN opam install --yes -j$(nproc) coq-compcert=3.13.1

ENV PATH="/home/coq/.opam/4.13.1+flambda/bin:${PATH}"

RUN set -ex && \
    wget https://github.com/sipa/safegcd-bounds/archive/06abb7f7aba9b00eb4ead96bdd7dbcc04ec45c4f.tar.gz -O safegcd-bounds.tar.gz && \
    tar -xvzf safegcd-bounds.tar.gz && \
    cd safegcd-bounds-06abb7f7aba9b00eb4ead96bdd7dbcc04ec45c4f/coq/divsteps && \
    sed -i 's/Time Qed./Admitted./g' divsteps724.v && \
    coq_makefile -f _CoqProject -o Makefile && \
    make -j$(nproc) && \
    make install

    # unfortunately the following opam install for coq-vst doesn't work and so we have a long workaround
# RUN opam install --yes -j$(nproc) coq-vst=2.14
RUN set -ex && \
    wget https://github.com/PrincetonUniversity/VST/archive/refs/tags/v2.14.tar.gz -O vst.tar.gz && \
    tar -xvzf vst.tar.gz && \
    cd VST-2.14 && \
    COMPCERT_DIR=$(coqc -where)/user-contrib/compcert && \
    make -j$(nproc) default_target sha COMPCERT=inst_dir COMPCERT_INST_DIR="$COMPCERT_DIR" && \
    gcc -c sha/sha.c -o sha/sha.o && \
    make install && \
    install -d $(coqc -where)/user-contrib/sha && \
    install -m 0644 -t $(coqc -where)/user-contrib/sha sha/*.v sha/*.vo

WORKDIR /home/coq/simplicity
COPY --chown=coq:coq . .
WORKDIR /home/coq/simplicity/Coq
RUN coq_makefile -f _CoqProject -o CoqMakefile -docroot /tmp
RUN make -f CoqMakefile clean && make -f CoqMakefile -j$(nproc)
RUN make -f CoqMakefile install

RUN echo "Require Import Simplicity.Semantics." > /home/coq/coq-init.v
CMD ["coqtop", "-q", "-init-file", "/home/coq/coq-init.v"]