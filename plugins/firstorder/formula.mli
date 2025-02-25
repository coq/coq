(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open EConstr

type flags = {
  reds : RedFlags.reds;
}

val (=?) : ('a -> 'a -> int) -> ('b -> 'b -> int) ->
  'a -> 'a -> 'b -> 'b -> int

val (==?) : ('a -> 'a -> 'b ->'b -> int) -> ('c -> 'c -> int) ->
  'a -> 'a -> 'b -> 'b -> 'c ->'c -> int

type ('a,'b) sum = Left of 'a | Right of 'b

type counter = bool -> metavariable

val construct_nhyps : Environ.env -> pinductive -> int array

val ind_hyps : Environ.env -> Evd.evar_map -> int -> pinductive ->
  constr list -> EConstr.rel_context array

module Env :
sig
  type t
  val empty : t
end

type atom

val hole_atom : atom
val repr_atom : Env.t -> atom -> EConstr.t
val compare_atom : atom -> atom -> int
val meta_in_atom : metavariable -> atom -> bool

type atoms = { positive:atom list; negative:atom list }

type _ side =
| Hyp : bool -> [ `Hyp ] side (* true if treated as hint *)
| Concl : [ `Goal ] side

type right_pattern =
    Rarrow
  | Rand
  | Ror
  | Rfalse
  | Rforall
  | Rexists of metavariable*constr*bool

type left_arrow_pattern=
    LLatom
  | LLfalse of pinductive*constr list
  | LLand of pinductive*constr list
  | LLor of pinductive*constr list
  | LLforall of constr
  | LLexists of pinductive*constr list
  | LLarrow of constr*constr*constr

type left_pattern=
    Lfalse
  | Land of pinductive
  | Lor of pinductive
  | Lforall of metavariable*constr*bool
  | Lexists of pinductive
  | LA of atom*left_arrow_pattern

type _ identifier = private
| GoalId : [ `Goal ] identifier
| FormulaId : GlobRef.t -> [ `Hyp ] identifier

val goal_id : [ `Goal ] identifier
val formula_id : Environ.env -> GlobRef.t -> [ `Hyp ] identifier

type _ pattern =
| LeftPattern : left_pattern -> [ `Hyp ] pattern
| RightPattern : right_pattern -> [ `Goal ] pattern

type 'a t = private {
        id: 'a identifier;
        constr: atom;
        pat: 'a pattern;
        atoms: atoms}

type any_formula = AnyFormula : 'a t -> any_formula

val build_formula : flags:flags -> Env.t -> Environ.env -> Evd.evar_map -> 'a side -> 'a identifier -> types ->
  counter -> Env.t * ('a t, atom) sum
