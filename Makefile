COQMODULE    := imm 
COQTHEORIES  := src/basic/*.v src/imm/*.v src/hardware/*.v src/rc11/*.v src/c11/*.v src/jsmm/*.v src/ocamlmm/*.v src/traversal/*.v src/travorder/*.v src/simhelpers/*.v

.PHONY: all theories clean tounicode

all: build

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

vio: Makefile.coq
	$(MAKE) -f Makefile.coq vio 

checkproofs: Makefile.coq
	$(MAKE) -f Makefile.coq checkproofs

quick-check: Makefile.coq
	$(MAKE) -f Makefile.coq vio2vo J=6

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R src $(COQMODULE)"; \
	echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f _CoqProject Makefile.coq

tounicode:
	sed -i 's/<</⟪/g' $(COQTHEORIES) 
	sed -i 's/>>/⟫/g' $(COQTHEORIES)
	sed -i 's/;;/⨾/g' $(COQTHEORIES)
	sed -i 's/<|/⦗/g' $(COQTHEORIES)
	sed -i 's/|>/⦘/g' $(COQTHEORIES)
	sed -i 's/\^+/⁺/g' $(COQTHEORIES)
	sed -i 's/\^\*/＊/g' $(COQTHEORIES)
