(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val dump_global : Libnames.qualid Constrexpr.or_by_notation -> unit

(** Vernacular entries *)
val vernac_require :
  Libnames.qualid option -> bool option -> Libnames.qualid list -> unit

(** The main interpretation function of vernacular expressions *)
val interp :
  ?verbosely:bool ->
  ?proof:Proof_global.closed_proof ->
  st:Vernacstate.t -> Vernacexpr.vernac_control CAst.t -> Vernacstate.t

(** Prepare a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables.
    [Not_found] is raised if the given string isn't the qualid of
    a known inductive type. *)

val make_cases : string -> string list list

(* XXX STATE: this type hints that restoring the state should be the
   caller's responsibility *)
val with_fail : Vernacstate.t -> bool -> (unit -> unit) -> unit

val command_focus : unit Proof.focus_kind

val interp_redexp_hook : (Environ.env -> Evd.evar_map -> Genredexpr.raw_red_expr ->
  Evd.evar_map * Redexpr.red_expr) Hook.t

val universe_polymorphism_option_name : string list

(** Elaborate a [atts] record out of a list of flags.
    Also returns whether polymorphism is explicitly (un)set. *)
val attributes_of_flags : Vernacexpr.vernac_flags -> Vernacinterp.atts -> bool option * Vernacinterp.atts

(** {5 VERNAC EXTEND} *)

type classifier = Genarg.raw_generic_argument list -> Vernacexpr.vernac_classification

type (_, _) ty_sig =
| TyNil : (atts:Vernacinterp.atts -> st:Vernacstate.t -> Vernacstate.t, Vernacexpr.vernac_classification) ty_sig
| TyTerminal : string * ('r, 's) ty_sig -> ('r, 's) ty_sig
| TyNonTerminal :
  ('a, 'b, 'c) Extend.ty_user_symbol * ('r, 's) ty_sig ->
    ('a -> 'r, 'a -> 's) ty_sig

type ty_ml = TyML : bool (** deprecated *) * ('r, 's) ty_sig * 'r * 's option -> ty_ml

(** Wrapper to dynamically extend vernacular commands. *)
val vernac_extend :
  command:string ->
  ?classifier:(string -> Vernacexpr.vernac_classification) ->
  ?entry:Vernacexpr.vernac_expr Pcoq.Entry.t ->
  ty_ml list -> unit

(** {5 VERNAC ARGUMENT EXTEND} *)

type 'a argument_rule =
| Arg_alias of 'a Pcoq.Entry.t
  (** This is used because CAMLP5 parser can be dumb about rule factorization,
      which sometimes requires two entries to be the same. *)
| Arg_rules of 'a Extend.production_rule list
  (** There is a discrepancy here as we use directly extension rules and thus
    entries instead of ty_user_symbol and thus arguments as roots. *)

type 'a vernac_argument = {
  arg_printer : 'a -> Pp.t;
  arg_parsing : 'a argument_rule;
}

val vernac_argument_extend : name:string -> 'a vernac_argument ->
  ('a, unit, unit) Genarg.genarg_type * 'a Pcoq.Entry.t

(** {5 STM classifiers} *)

val get_vernac_classifier :
  Vernacexpr.extend_name -> classifier

(** Low-level API, not for casual user. *)
val declare_vernac_classifier :
  string -> classifier array -> unit
