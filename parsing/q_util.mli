(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

val patt_of_expr : MLast.expr -> MLast.patt

val mlsensitive_list :  ('a -> MLast.expr) -> 'a list -> MLast.expr

val mlexpr_of_pair :
  ('a -> MLast.expr) -> ('b -> MLast.expr)
    -> 'a * 'b -> MLast.expr

val mlexpr_of_triple :
  ('a -> MLast.expr) -> ('b -> MLast.expr) -> ('c -> MLast.expr)
    -> 'a * 'b * 'c -> MLast.expr

val mlexpr_of_bool : bool -> MLast.expr

val mlexpr_of_int : int -> MLast.expr

val mlexpr_of_string : string -> MLast.expr

val mlexpr_of_option : ('a -> MLast.expr) -> 'a option -> MLast.expr

val interp_entry_name : Util.loc -> string -> string -> 
  Pcoq.entry_type * MLast.expr
