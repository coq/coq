(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Ltac toplevel command entries. *)

open Vernacexpr
open Tacexpr
open Vernacinterp

(** {5 Tactic Definitions} *)

val register_ltac : locality_flag -> ?deprecation:deprecation ->
  Tacexpr.tacdef_body list -> unit
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
  locality_flag -> int -> ?deprecation:deprecation -> raw_argument
  grammar_tactic_prod_item_expr list -> raw_tactic_expr -> unit
(** [add_tactic_notation local level prods expr] adds a tactic notation in the
    environment at level [level] with locality [local] made of the grammar
    productions [prods] and returning the body [expr] *)

val register_tactic_notation_entry : string -> ('a, 'b, 'c) Genarg.genarg_type -> unit
(** Register an argument under a given entry name for tactic notations. When
    translating [raw_argument] into [argument], atomic names will be first
    looked up according to names registered through this function and fallback
    to finding an argument by name (as in {!Genarg}) if there is none
    matching. *)

val add_ml_tactic_notation : ml_tactic_name -> level:int -> ?deprecation:deprecation ->
  argument grammar_tactic_prod_item_expr list list -> unit
(** A low-level variant of {!add_tactic_notation} used by the TACTIC EXTEND
    ML-side macro. *)

(** {5 Tactic Quotations} *)

val create_ltac_quotation : string ->
  ('grm Loc.located -> raw_tactic_arg) -> ('grm Pcoq.Entry.t * int option) -> unit
(** [create_ltac_quotation name f e] adds a quotation rule to Ltac, that is,
    Ltac grammar now accepts arguments of the form ["name" ":" "(" <e> ")"], and
    generates an argument using [f] on the entry parsed by [e]. *)

(** {5 Queries} *)

val print_ltacs : unit -> unit
(** Display the list of ltac definitions currently available. *)

val print_located_tactic : Libnames.qualid -> unit
(** Display the absolute name of a tactic. *)

type _ ty_sig =
| TyNil : (Geninterp.interp_sign -> unit Proofview.tactic) ty_sig
| TyIdent : string * 'r ty_sig -> 'r ty_sig
| TyArg :
  ('a, 'b, 'c) Extend.ty_user_symbol * string * 'r ty_sig -> ('c -> 'r) ty_sig
| TyAnonArg :
  ('a, 'b, 'c) Extend.ty_user_symbol * 'r ty_sig -> 'r ty_sig

type ty_ml = TyML : 'r ty_sig * 'r -> ty_ml

val tactic_extend : string -> string -> level:Int.t ->
  ?deprecation:deprecation -> ty_ml list -> unit
