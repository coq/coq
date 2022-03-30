(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ
open Univ

type univ_length_mismatch = {
  actual : int ;
  expect : int ;
}
(* Due to an OCaml bug ocaml/ocaml#10027 inlining this record will cause
compliation with -rectypes to crash. *)
exception UniverseLengthMismatch of univ_length_mismatch

(** Side-effecting functions creating new universe levels. *)

val new_univ_global : unit -> UGlobal.t
val fresh_level : unit -> Level.t

val new_global_univ : unit -> Universe.t in_universe_context_set

(** Build a fresh instance for a given context, its associated substitution and
    the instantiated constraints. *)

val fresh_instance : AbstractContext.t -> Instance.t in_universe_context_set

val fresh_instance_from : ?loc:Loc.t -> AbstractContext.t -> Instance.t option ->
  Instance.t in_universe_context_set

val fresh_sort_in_family : Sorts.family ->
  Sorts.t in_universe_context_set
val fresh_constant_instance : env -> Constant.t ->
  pconstant in_universe_context_set
val fresh_inductive_instance : env -> inductive ->
  pinductive in_universe_context_set
val fresh_constructor_instance : env -> constructor ->
  pconstructor in_universe_context_set
val fresh_array_instance : env ->
  Instance.t in_universe_context_set

val fresh_global_instance : ?loc:Loc.t -> ?names:Univ.Instance.t -> env -> GlobRef.t ->
  constr in_universe_context_set

(** Get fresh variables for the universe context.
    Useful to make tactics that manipulate constrs in universe contexts polymorphic. *)
val fresh_universe_context_set_instance : ContextSet.t ->
  universe_level_subst * ContextSet.t

(** Create a fresh global in the environment argument, without side effects.
    BEWARE: this raises an error on polymorphic constants/inductives:
    the constraints should be properly added to an evd.
    See Evd.fresh_global, Evarutil.new_global, and pf_constr_of_global for
    the proper way to get a fresh copy of a polymorphic global reference. *)
val constr_of_monomorphic_global : env -> GlobRef.t -> constr
