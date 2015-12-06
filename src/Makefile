CMX=lang/ast.cmx lang/lexer.cmx lang/parser.cmx \
	typedefs.cmx typer.cmx main.cmx
BIN=pscala
GENERATED=lang/lexer.ml lang/parser.ml lang/parser.mli 
RECDIR=lang
FLAGS=-I $(RECDIR)
CMP=ocamlopt

COMMA_RECDIR=$(shell echo $(RECDIR) | sed -s 's/ /,/g')

all: $(BIN)

$(BIN): $(CMX)
	$(CMP) $(FLAGS) -o $(BIN) $(CMX)

.SUFFIXES: .mli .ml .cmi .cmx .mll .mly

.mli.cmi:
	$(CMP) $(FLAGS) -c  $<

.ml.cmx:
	$(CMP) $(FLAGS) -c  $<

.mll.ml:
	ocamllex $<

.mly.ml:
	@# How can I include a directory in menhir?! -I is not defined.
	cd `dirname $<` && menhir --infer -v `basename $<`

lang/parser.ml: lang/ast.cmx

clean:
	rm -f {.,$(RECDIR)}/*{.cmi,.cmx,.o,~} $(GENERATED) lang/parser.automaton

.depend depend: $(GENERATED)
	rm -f .depend
	ocamldep -I $(RECDIR) {.,$(RECDIR)}/*.{ml,mli} > .depend

include .depend
