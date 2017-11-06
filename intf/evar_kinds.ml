(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Misctypes

(** The kinds of existential variable *)

(** Should the obligation be defined (opaque or transparent (default)) or
    defined transparent and expanded in the term? *)

type obligation_definition_status = Define of bool | Expand

type matching_var_kind = FirstOrderPatVar of patvar | SecondOrderPatVar of patvar

type t =
  | ImplicitArg of global_reference * (int * Id.t option)
     * bool (** Force inference *)
  | BinderType of Name.t
  | NamedHole of Id.t (* coming from some ?[id] syntax *)
  | QuestionMark of obligation_definition_status * Name.t
  | CasesType of bool (* true = a subterm of the type *)
  | InternalHole
  | TomatchTypeParameter of inductive * int
  | GoalEvar
  | ImpossibleCase
  | MatchingVar of matching_var_kind
  | VarInstance of Id.t
  | SubEvar of Evar.t
