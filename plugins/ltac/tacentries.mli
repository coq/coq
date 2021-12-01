(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Ltac toplevel command entries. *)

open Vernacexpr
open Tacexpr

(** {5 Tactic Definitions} *)

val register_ltac : locality_flag -> ?deprecation:Deprecation.t ->
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
  locality_flag -> int -> ?deprecation:Deprecation.t -> raw_argument
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

val add_ml_tactic_notation : ml_tactic_name -> level:int -> ?deprecation:Deprecation.t ->
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

val print_ltac : Libnames.qualid -> Pp.t
(** Display the definition of a tactic. *)

(** {5 Low-level registering of tactics} *)

type (_, 'a) ml_ty_sig =
| MLTyNil : ('a, 'a) ml_ty_sig
| MLTyArg : ('r, 'a) ml_ty_sig -> (Geninterp.Val.t -> 'r, 'a) ml_ty_sig

val ml_tactic_extend : plugin:string -> name:string -> local:locality_flag ->
  ?deprecation:Deprecation.t -> ('r, unit Proofview.tactic) ml_ty_sig -> 'r -> unit
(** Helper function to define directly an Ltac function in OCaml without any
    associated parsing rule nor further shenanigans. The Ltac function will be
    defined as [name] in the Coq file that loads the ML plugin where this
    function is called. It will have the arity given by the [ml_ty_sig]
    argument. *)

val ml_val_tactic_extend : plugin:string -> name:string -> local:locality_flag ->
  ?deprecation:Deprecation.t -> ('r, Geninterp.Val.t Ftactic.t) ml_ty_sig -> 'r -> unit
(** Same as {!ml_tactic_extend} but the function can return an argument
    instead. *)

(** {5 TACTIC EXTEND} *)

type _ ty_sig =
| TyNil : (Geninterp.interp_sign -> unit Proofview.tactic) ty_sig
| TyIdent : string * 'r ty_sig -> 'r ty_sig
| TyArg : ('a, 'b, 'c) Extend.ty_user_symbol * 'r ty_sig -> ('c -> 'r) ty_sig

type ty_ml = TyML : 'r ty_sig * 'r -> ty_ml

val tactic_extend : string -> string -> level:Int.t ->
  ?deprecation:Deprecation.t -> ty_ml list -> unit

val eval_of_ty_ml :
  ty_ml ->
  Geninterp.Val.t list ->
  Geninterp.interp_sign ->
  unit Proofview.tactic

(** grammar rule for [add_tactic_notation] *)
val clause_of_ty_ml :
  ty_ml ->
  Genarg.ArgT.any Extend.user_symbol grammar_tactic_prod_item_expr list

(** {5 ARGUMENT EXTEND} *)

(**

  This is the main entry point for the ARGUMENT EXTEND macro that allows to
  easily create user-made Ltac arguments.


  Each argument has three type parameters. See {!Genarg} for more details.
  There are two kinds of Ltac arguments, uniform and non-uniform. The former
  have the same type at each level (raw, glob, top) while the latter may vary.

  When declaring an argument one must provide the following data:
  - Internalization : raw -> glob
  - Substitution : glob -> glob
  - Interpretation : glob -> Ltac dynamic value
  - Printing for every level
  - An optional toplevel tag of type top (with the proviso that the
    interpretation function only produces values with this tag)

  This data can be either given explicitly with the [Fun] constructors, or it
  can be inherited from another argument with the [Wit] constructors.

*)

type ('a, 'b, 'c) argument_printer =
  'a Pptactic.raw_extra_genarg_printer *
  'b Pptactic.glob_extra_genarg_printer *
  'c Pptactic.extra_genarg_printer

type ('a, 'b) argument_intern =
| ArgInternFun : ('a, 'b) Genintern.intern_fun -> ('a, 'b) argument_intern
| ArgInternWit : ('a, 'b, 'c) Genarg.genarg_type -> ('a, 'b) argument_intern

type 'b argument_subst =
| ArgSubstFun : 'b Genintern.subst_fun -> 'b argument_subst
| ArgSubstWit : ('a, 'b, 'c) Genarg.genarg_type -> 'b argument_subst

type ('b, 'c) argument_interp =
| ArgInterpRet : ('c, 'c) argument_interp
| ArgInterpFun : ('b, Geninterp.Val.t) Geninterp.interp_fun -> ('b, 'c) argument_interp
| ArgInterpWit : ('a, 'b, 'r) Genarg.genarg_type -> ('b, 'c) argument_interp
| ArgInterpSimple :
  (Geninterp.interp_sign -> Environ.env -> Evd.evar_map -> 'b -> 'c) -> ('b, 'c) argument_interp

type ('a, 'b, 'c) tactic_argument = {
  arg_parsing : 'a Vernacextend.argument_rule;
  arg_tag : 'c Geninterp.Val.tag option;
  arg_intern : ('a, 'b) argument_intern;
  arg_subst : 'b argument_subst;
  arg_interp : ('b, 'c) argument_interp;
  arg_printer : ('a, 'b, 'c) argument_printer;
}

val argument_extend : name:string -> ('a, 'b, 'c) tactic_argument ->
  ('a, 'b, 'c) Genarg.genarg_type * 'a Pcoq.Entry.t
