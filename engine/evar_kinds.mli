(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** The kinds of existential variable *)

(** Should the obligation be defined (opaque or transparent (default)) or
    defined transparent and expanded in the term? *)

type obligation_definition_status = Define of bool | Expand

type matching_var_kind = FirstOrderPatVar of Id.t | SecondOrderPatVar of Id.t

type subevar_kind = Domain | Codomain | Body

(* maybe this should be a Projection.t *)
(* Represents missing record field *)
type record_field = { fieldname : Constant.t; recordname : Names.inductive }

type question_mark = {
     qm_obligation: obligation_definition_status;
     qm_name: Name.t;
     (* Tracks if the evar represents a missing record field *)
     qm_record_field: record_field option;
}

(* Default value of question_mark which is used most often *)
val default_question_mark : question_mark

type t =
  | ImplicitArg of GlobRef.t * (int * Id.t option)
     * bool (** Force inference *)
  | BinderType of Name.t
  | NamedHole of Id.t (* coming from some ?[id] syntax *)
  | QuestionMark of question_mark
  | CasesType of bool (* true = a subterm of the type *)
  | InternalHole
  | TomatchTypeParameter of inductive * int
  | GoalEvar
  | ImpossibleCase
  | MatchingVar of matching_var_kind
  | VarInstance of Id.t
  | SubEvar of subevar_kind option * Evar.t
