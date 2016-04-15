(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Vernacexpr
open Tacexpr

type 'a grammar_tactic_prod_item_expr =
| TacTerm of string
| TacNonTerm of Loc.t * 'a * Names.Id.t

val add_tactic_notation :
  locality_flag -> int -> (string * string option) grammar_tactic_prod_item_expr list ->
  raw_tactic_expr -> unit
(** [add_tactic_notation local level prods expr] adds a tactic notation in the
    environment at level [level] with locality [local] made of the grammar
    productions [prods] and returning the body [expr] *)

val add_ml_tactic_notation : ml_tactic_name ->
  Genarg.ArgT.any Extend.user_symbol grammar_tactic_prod_item_expr list list -> unit

val register_ltac : bool -> Vernacexpr.tacdef_body list -> unit

(** {5 Adding tactic quotations} *)

val create_ltac_quotation : string ->
  ('grm Loc.located -> raw_tactic_arg) -> ('grm Pcoq.Gram.entry * int option) -> unit
(** [create_ltac_quotation name f e] adds a quotation rule to Ltac, that is,
    Ltac grammar now accepts arguments of the form ["name" ":" "(" <e> ")"], and
    generates an argument using [f] on the entry parsed by [e]. *)
