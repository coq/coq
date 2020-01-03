-include ../../Makefile.conf

CO="$(COQMF_OCAMLFIND)" opt
CB="$(COQMF_OCAMLFIND)" ocamlc

all:
	$(CO) -c foolib.ml
	$(CO) -a foolib.cmx -o foo.cmxa
	$(CB) -c foolib.ml
	$(CB) -a foolib.cmo -o foo.cma
	$(CB) -c foo.mli # empty .mli file, to be understood

clean:
	rm -f *.cmo *.cma *.cmx *.cmxa *.cmi *.o *.a
