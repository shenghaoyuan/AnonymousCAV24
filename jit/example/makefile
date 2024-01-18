OCAMLOPT ?= ocamlopt

%: %.ml
	test ! -f $*.mli || rm $*.mli \
	&& $(OCAMLOPT) -o $@ $< \
	&& ./$@ \
	&& rm $@ && rm $@.cmi && rm $@.cmx && rm $@.o

