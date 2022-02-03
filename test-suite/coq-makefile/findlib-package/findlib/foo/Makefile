-include ../../Makefile.conf

CO="$(COQMF_OCAMLFIND)" opt
CB="$(COQMF_OCAMLFIND)" ocamlc

all:
	$(CO) -c foolib.ml -thread
	$(CO) -linkall -a foolib.cmx -o foo.cmxa
	$(CO) -shared -linkall foo.cmxa -o foo.cmxs
	$(CB) -c foolib.ml -thread
	$(CB) -linkall -a foolib.cmo -o foo.cma
	$(CB) -c foo.mli -thread # empty .mli file, to be understood

clean:
	rm -f *.cmo *.cma *.cmx *.cmxa *.cmi *.o *.a
