SRC:= print.ml invert_tactic.ml invert.ml4 test.v

COQLIB = $(shell coqc -where)/

COQSRCLIBS?=-I $(COQLIB)kernel/ -I $(COQLIB)lib \
  -I $(COQLIB)library -I $(COQLIB)parsing -I $(COQLIB)pretyping \
  -I $(COQLIB)interp -I $(COQLIB)printing -I $(COQLIB)intf \
  -I $(COQLIB)proofs -I $(COQLIB)tactics -I $(COQLIB)tools \
  -I $(COQLIB)toplevel -I $(COQLIB)grammar 


OCAMLC=ocamlfind ocamlc -package pprint -linkpkg -rectypes
OCAMLOPT=ocamlfind ocamlopt -package pprint -linkpkg -rectypes
OCAMLDEP=ocamlfind ocamldep -package pprint 
LIBS= $(COQSRCLIBS)

COQDEP = coqdep
COQC = coqc

GRAMMARS?=grammar.cma
ifeq ($(CAMLP4),camlp5)
CAMLP4EXTEND=pa_extend.cmo q_MLast.cmo pa_macro.cmo
else
CAMLP4EXTEND=
endif
PP?=-pp 'camlp4o -I . $(COQSRCLIBS) compat5.cmo \
  $(CAMLP4EXTEND) $(GRAMMARS) $(CAMLP4OPTIONS) -impl'

ML4FILES:= $(filter %.ml4, $(SRC))
MLFILES:=  $(filter %.ml, $(SRC))
VFILES :=  $(filter %.v, $(SRC))

# DEPENDENCIES 

-include $(addsuffix .d,$(SRC))
.SECONDARY: $(addsuffix .d,$(SRC))

CMO:= $(MLFILES:.ml=.cmo) $(MLPACKFILES:.mlpack=.cmo) $(ML4FILES:.ml4=.cmo)
CMX:= $(MLFILES:.ml=.cmx) $(MLPACKFILES:.mlpack=.cmx) $(ML4FILES:.ml4=.cmx)
VOFILES := $(VFILES:.v=.vo)

all: $(CMO) $(CMX) invert.cmo invert.cmxs $(VOFILES)

clean:
	rm -f $(CMO) $(CMX) invert.cmxs
	rm -f *.d
	rm -f *.o *.cmi *.glob

# depend: 
# 	$(OCAMLDEP) $(PP) $(LIBS) $(MLFILES) $(ML4FILES) > .depend

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

%.cmx: %.ml4
	$(OCAMLOPT) $(LIBS) -c $(PP) -impl $<

%.cmx: %.ml
	$(OCAMLOPT) $(LIBS) -c $<

%.ml4.d: %.ml4
	$(OCAMLDEP) $(PP) -slash $(LIBS) $< > $@ 

%.ml.d: %.ml
	$(OCAMLDEP) -slash $(LIBS) $< > $@

%.v.d: %.v
	$(COQDEP) -slash $(COQLIBS) "$<" > "$@" 

%.vo %.glob: %.v
	$(COQC) $(COQDEBUG) $(COQFLAGS) $*