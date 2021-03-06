# Here is a hack to make $(eval $(shell works:
define donewline


endef
includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\r' | tr '\n' '@'; })))
$(call includecmdwithout@,$(COQBIN)coqtop -config)

.DEFAULT_GOAL := all

SRC:= 	print.ml print.mli \
	context.ml context.mli telescope.ml telescope.mli \
	invertlib.ml \
	invert_tactic.ml invert.ml4 \
	test1.v test2.v test3.v test4.v test5.v test6.v test7.v test8.v test9.v test10.v



COQDEP = ${COQBIN}coqdep -c
COQC = ${COQBIN}coqc

COQLIB = $(shell ${COQC} -where)/
COQLIBS =-R . Invert

COQSRCLIBS?=-I $(COQLIB)kernel/ -I $(COQLIB)lib \
  -I $(COQLIB)library -I $(COQLIB)parsing -I $(COQLIB)pretyping \
  -I $(COQLIB)interp -I $(COQLIB)printing -I $(COQLIB)intf \
  -I $(COQLIB)proofs -I $(COQLIB)tactics -I $(COQLIB)tools \
  -I $(COQLIB)toplevel -I $(COQLIB)grammar


OCAMLC=ocamlfind ocamlc -package pprint -linkpkg -rectypes 
OCAMLOPT=ocamlfind ocamlopt -package pprint -linkpkg -rectypes
OCAMLDEP=ocamlfind ocamldep -package pprint
LIBS= $(COQSRCLIBS)

GRAMMARS?=grammar.cma
ifeq ($(CAMLP4),camlp5)
CAMLP4EXTEND=pa_extend.cmo q_MLast.cmo pa_macro.cmo
else
CAMLP4EXTEND=
endif
PP?=-pp '"$(CAMLP4O)" -I . $(COQSRCLIBS) compat5.cmo \
  $(CAMLP4EXTEND) $(GRAMMARS) $(CAMLP4OPTIONS) -impl'

ML4FILES:= $(filter %.ml4, $(SRC))
MLFILES:=  $(filter %.ml, $(SRC))
VFILES :=  $(filter %.v, $(SRC))

# DEPENDENCIES

-include $(addsuffix .d,$(SRC))
.SECONDARY: $(addsuffix .d,$(SRC))

CMO:= $(MLFILES:.ml=.cmo) $(MLPACKFILES:.mlpack=.cmo) $(ML4FILES:.ml4=.cmo)
CMX:= $(MLFILES:.ml=.cmx) $(MLPACKFILES:.mlpack=.cmx) $(ML4FILES:.ml4=.cmx)
CMIFILES=$(CMO:.cmo=.cmi)
VOFILES := $(VFILES:.v=.vo)
CMXS := invert.cmxs
CMA := invert.cma

all: $(CMO) $(CMX) invert.cma invert.cmxs $(VOFILES)

clean:
	rm -f $(CMO) $(CMX) $(CMA) $(VOFILES) invert.cmxs
	rm -f *.d *.
	rm -f *.o *.cmi *.glob
	rm -f *.cmxs *.native

printenv:
	@echo 'PP =	$(PP)'
	@echo 'CMX=	$(CMX)'

# implicit rules

%.cmo: %.ml4
	$(OCAMLC) $(LIBS) -c $(PP) -impl $<

%.cmo: %.ml
	$(OCAMLC) $(LIBS) -c -impl $<

%.cmxs: $(CMX)
	$(OCAMLOPT)  -shared -o $@  $^

%.cma: $(CMO)
	$(OCAMLC) $(LIBS) -a -o $@  $^

%.cmx: %.ml4
	$(OCAMLOPT) $(LIBS) -c $(PP) -impl $<

%.cmx: %.ml
	$(OCAMLOPT) $(LIBS) -c $<

%.cmi: %.mli
	$(OCAMLC) $(LIBS) -c $<

%.ml4.d: %.ml4
	$(COQDEP) -slash $(LIBS) $(COQLIBS) $< > $@

%.ml.d: %.ml
	$(OCAMLDEP) -slash $(LIBS) $< > $@

%.v.d: %.v
	$(COQDEP) -slash $(COQLIBS) "$<" > "$@"

%.vo %.glob: %.v $(CMXS)
	$(COQC) $(COQDEBUG) $(COQLIBS) $*
