(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Interpretation of extended vernac phrases. *)

type 'a vernac_command = 'a -> atts:Vernacexpr.vernac_flags -> st:Vernacstate.t -> Vernacstate.t

type plugin_args = Genarg.raw_generic_argument list

val call : Vernacexpr.extend_name -> plugin_args -> atts:Vernacexpr.vernac_flags -> st:Vernacstate.t -> Vernacstate.t

(** {5 VERNAC EXTEND} *)

type classifier = Genarg.raw_generic_argument list -> Vernacexpr.vernac_classification

type (_, _) ty_sig =
| TyNil : (atts:Vernacexpr.vernac_flags -> st:Vernacstate.t -> Vernacstate.t, Vernacexpr.vernac_classification) ty_sig
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
