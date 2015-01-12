(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Compat (* necessary for camlp4 *)

val mlexpr_of_list :  ('a -> MLast.expr) -> 'a list -> MLast.expr

val mlexpr_of_pair :
  ('a -> MLast.expr) -> ('b -> MLast.expr)
    -> 'a * 'b -> MLast.expr

val mlexpr_of_triple :
  ('a -> MLast.expr) -> ('b -> MLast.expr) -> ('c -> MLast.expr)
    -> 'a * 'b * 'c -> MLast.expr

val mlexpr_of_quadruple :
  ('a -> MLast.expr) -> ('b -> MLast.expr) ->
    ('c -> MLast.expr) -> ('d -> MLast.expr) -> 'a * 'b * 'c * 'd -> MLast.expr

val mlexpr_of_bool : bool -> MLast.expr

val mlexpr_of_int : int -> MLast.expr

val mlexpr_of_string : string -> MLast.expr

val mlexpr_of_option : ('a -> MLast.expr) -> 'a option -> MLast.expr

val mlexpr_of_prod_entry_key : Pcoq.prod_entry_key -> MLast.expr
