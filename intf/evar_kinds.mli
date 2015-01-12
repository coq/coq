(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Globnames

(** The kinds of existential variable *)

(** Should the obligation be defined (opaque or transparent (default)) or
    defined transparent and expanded in the term? *)

type obligation_definition_status = Define of bool | Expand

type t =
  | ImplicitArg of global_reference * (int * Id.t option)
     * bool (** Force inference *)
  | BinderType of Name.t
  | QuestionMark of obligation_definition_status
  | CasesType of bool (* true = a subterm of the type *)
  | InternalHole
  | TomatchTypeParameter of inductive * int
  | GoalEvar
  | ImpossibleCase
  | MatchingVar of bool * Id.t
  | VarInstance of Id.t
  | SubEvar of Constr.existential_key
