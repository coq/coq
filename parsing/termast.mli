(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Termops
open Sign
open Environ
open Libnames
open Nametab
open Rawterm
open Pattern
(*i*)

(* Translation of pattern, cases pattern, rawterm and term into syntax
   trees for printing *)

val ast_of_cases_pattern : cases_pattern -> Coqast.t
val ast_of_rawconstr : rawconstr -> Coqast.t
val ast_of_pattern : env -> names_context -> constr_pattern -> Coqast.t

(* If [b=true] in [ast_of_constr b env c] then the variables in the first 
   level of quantification clashing with the variables in [env] are renamed *)

val ast_of_constr : bool -> env -> constr -> Coqast.t

val ast_of_constant     : env -> constant -> Coqast.t
val ast_of_existential  : env -> existential -> Coqast.t
val ast_of_constructor  : env -> constructor -> Coqast.t
val ast_of_inductive    : env -> inductive -> Coqast.t
val ast_of_ref          : global_reference -> Coqast.t
val ast_of_qualid       : qualid -> Coqast.t

(*i Now in constrextern.mli
val print_implicits : bool ref
val print_casts : bool ref
val print_arguments : bool ref
val print_evar_arguments : bool ref
val print_coercions : bool ref
val print_universes : bool ref

val with_casts : ('a -> 'b) -> 'a -> 'b
val with_implicits : ('a -> 'b) -> 'a -> 'b
val with_arguments : ('a -> 'b) -> 'a -> 'b
val with_coercions : ('a -> 'b) -> 'a -> 'b
val with_universes : ('a -> 'b) -> 'a -> 'b
i*)
