(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open EConstr
open Globnames

val qflag : bool ref

val red_flags: CClosure.RedFlags.reds ref

val (=?) : ('a -> 'a -> int) -> ('b -> 'b -> int) ->
  'a -> 'a -> 'b -> 'b -> int

val (==?) : ('a -> 'a -> 'b ->'b -> int) -> ('c -> 'c -> int) ->
  'a -> 'a -> 'b -> 'b -> 'c ->'c -> int

type ('a,'b) sum = Left of 'a | Right of 'b

type counter = bool -> metavariable

val construct_nhyps : Environ.env -> pinductive -> int array

val ind_hyps : Environ.env -> Evd.evar_map -> int -> pinductive ->
  constr list -> EConstr.rel_context array

type atoms = {positive:constr list;negative:constr list}

type side = Hyp | Concl | Hint

val dummy_id: global_reference

val build_atoms : Environ.env -> Evd.evar_map -> counter ->
  side -> constr -> bool * atoms

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
  | LA of constr*left_arrow_pattern

type t={id: global_reference;
	constr: constr;
	pat: (left_pattern,right_pattern) sum;
	atoms: atoms}

(*exception Is_atom of constr*)

val build_formula : Environ.env -> Evd.evar_map -> side -> global_reference -> types ->
  counter -> (t,types) sum

