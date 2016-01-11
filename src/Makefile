##############################################################################
# Project: pscala
# By: Théophile Bastian <contact@tobast.fr>
#
# This project implements a compiler for "Petit Scala", as defined in
# <https://www.lri.fr/~filliatr/ens/compil/projet/sujet1-v1.pdf>
# It is developped as a school project for J-C. Filliâtre's Compilation course
# at the Ecole Normale Superieure, Paris.
##############################################################################
# Makefile
#
# This makefile is somehow quite dirty, as the dependancies are hardcoded.
# Yet, I could not find why the previous one, with dynamically generated
# dependancies, would not run on some systems.
##############################################################################

CMX=lang/ast.cmx lang/typedAst.cmx lang/parser.cmx lang/lexer.cmx \
	x86_64/x86_64.cmx \
	typer.cmx compile.cmx main.cmx
OBJS= lang/ast.cmx lang/typedAst.cmx \
	lang/parser.ml lang/parser.cmx\
	lang/lexer.ml lang/lexer.cmx \
	x86_64/x86_64.cmx \
	typer.cmx compile.cmx main.cmx
BIN=pscala
RECDIR=lang x86_64
INCLUDE_RECDIR=$(shell echo $(RECDIR) | sed -s 's/ / -I /g')
FLAGS=-g -I $(INCLUDE_RECDIR)
CMP=ocamlopt

COMMA_RECDIR=$(shell echo $(RECDIR) | sed -s 's/ /,/g')

all: $(BIN)

$(BIN): $(OBJS)
	$(CMP) $(FLAGS) -o $(BIN) $(CMX)

#.SUFFIXES: .mli .ml .cmi .cmx .mll .mly

#.mli.cmi:
#	$(CMP) $(FLAGS) -c  $<
#
#.ml.cmx:
#	$(CMP) $(FLAGS) -c  $<
#
#.mll.ml:
#	ocamllex $<
#
#.mly.ml:
#	@# How can I include a directory in menhir?! -I is not defined.
#	cd `dirname $<` && menhir --infer -v `basename $<`

%.cmx: %.ml
	if [ -f $<i ] ; then $(CMP) $(FLAGS) -c $<i ; fi
	$(CMP) $(FLAGS) -c $<

lang/parser.ml: lang/parser.mly
	cd `dirname $<` && menhir --infer -v `basename $<`

clean:
	rm -f {.,$(COMMA_RECDIR)}/*{.cmi,.cmx,.o,~} $(GENERATED) \
		lang/parser.automaton ${BIN}
