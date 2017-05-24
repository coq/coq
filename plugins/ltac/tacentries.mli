(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Ltac toplevel command entries. *)

open Vernacexpr
open Tacexpr

(** {5 Tactic Definitions} *)

val register_ltac : locality_flag -> Tacexpr.tacdef_body list -> unit
(** Adds new Ltac definitions to the environment. *)

(** {5 Tactic Notations} *)

type 'a grammar_tactic_prod_item_expr = 'a Pptactic.grammar_tactic_prod_item_expr =
| TacTerm of string
| TacNonTerm of ('a * Names.Id.t option) Loc.located

type raw_argument = string * string option
(** An argument type as provided in Tactic notations, i.e. a string like
    "ne_foo_list_opt" together with a separator that only makes sense in the
    "_sep" cases. *)

type argument = Genarg.ArgT.any Extend.user_symbol
(** A fully resolved argument type given as an AST with generic arguments on the
    leaves. *)

val add_tactic_notation :
  locality_flag -> int -> raw_argument grammar_tactic_prod_item_expr list ->
  raw_tactic_expr -> unit
(** [add_tactic_notation local level prods expr] adds a tactic notation in the
    environment at level [level] with locality [local] made of the grammar
    productions [prods] and returning the body [expr] *)

val register_tactic_notation_entry : string -> ('a, 'b, 'c) Genarg.genarg_type -> unit
(** Register an argument under a given entry name for tactic notations. When
    translating [raw_argument] into [argument], atomic names will be first
    looked up according to names registered through this function and fallback
    to finding an argument by name (as in {!Genarg}) if there is none
    matching. *)

val add_ml_tactic_notation : ml_tactic_name -> level:int ->
  argument grammar_tactic_prod_item_expr list list -> unit
(** A low-level variant of {!add_tactic_notation} used by the TACTIC EXTEND
    ML-side macro. *)

(** {5 Tactic Quotations} *)

val create_ltac_quotation : string ->
  ('grm Loc.located -> raw_tactic_arg) -> ('grm Pcoq.Gram.entry * int option) -> unit
(** [create_ltac_quotation name f e] adds a quotation rule to Ltac, that is,
    Ltac grammar now accepts arguments of the form ["name" ":" "(" <e> ")"], and
    generates an argument using [f] on the entry parsed by [e]. *)

(** {5 Queries} *)

val print_ltacs : unit -> unit
(** Display the list of ltac definitions currently available. *)
