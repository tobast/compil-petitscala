(******************************************************************************
 * Project: pscala
 * By: Théophile Bastian <contact@tobast.fr>
 *
 * This project implements a compiler for "Petit Scala", as defined in
 * <https://www.lri.fr/~filliatr/ens/compil/projet/sujet1-v1.pdf>
 * It is developped as a school project for J-C. Filliâtre's Compilation course
 * at the Ecole Normale Superieure, Paris.
 ******************************************************************************
 * File: typer.mli
 *
 * Deduces and checks types consistency
 *****************************************************************************)

exception InternalError of string
exception TyperError of Ast.codeLoc * string

(***
 * Types the program. Returns a type-decorated AST.
 * Raises:
 *   - TyperError of loc,str when the program is badly typed
 *   - InternalError of str when the typer encountered an error
 ***)
val doPrgmTyping : Ast.prgm -> TypedAst.typPrgm
