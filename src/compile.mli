
(******************************************************************************
 * Project: pscala
 * By: Théophile Bastian <contact@tobast.fr>
 *
 * This project implements a compiler for "Petit Scala", as defined in
 * <https://www.lri.fr/~filliatr/ens/compil/projet/sujet1-v1.pdf>
 * It is developped as a school project for J-C. Filliâtre's Compilation course
 * at the Ecole Normale Superieure, Paris.
 ******************************************************************************
 * File: compile.mli
 * Compiles a typed AST.
 *****************************************************************************)

exception InternalError of string

(***
 * Compiles a typed program
 ***)
val compileTypPrgm : TypedAst.typPrgm -> X86_64.program
