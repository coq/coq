(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Sign
open Term
open Environ
open Evd
open Rawterm
open Evarutil
(*i*)

(* An auxiliary function for searching for fixpoint guard indexes *)

val search_guard :
    Util.loc -> env -> int list list -> rec_declaration -> int array

type typing_constraint = OfType of types option | IsType

type var_map = (identifier * Pattern.constr_under_binders) list
type unbound_ltac_var_map = (identifier * identifier option) list
type ltac_var_map = var_map * unbound_ltac_var_map
type rawconstr_ltac_closure = ltac_var_map * rawconstr

module type S =
sig

  module Cases : Cases.S

  (* Allow references to syntaxically inexistent variables (i.e., if applied on an inductive) *)
  val allow_anonymous_refs : bool ref

  (* Generic call to the interpreter from rawconstr to open_constr, leaving
     unresolved holes as evars and returning the typing contexts of
     these evars. Work as [understand_gen] for the rest. *)

  val understand_tcc : ?resolve_classes:bool ->
    evar_map -> env -> ?expected_type:types -> rawconstr -> open_constr

  val understand_tcc_evars : ?fail_evar:bool -> ?resolve_classes:bool ->
    evar_map ref -> env -> typing_constraint -> rawconstr -> constr

  (* More general entry point with evars from ltac *)

  (* Generic call to the interpreter from rawconstr to constr, failing
     unresolved holes in the rawterm cannot be instantiated.

     In [understand_ltac expand_evars sigma env ltac_env constraint c],

     expand_evars : expand inferred evars by their value if any
     sigma : initial set of existential variables (typically dependent subgoals)
     ltac_env : partial substitution of variables (used for the tactic language)
     constraint : tell if interpreted as a possibly constrained term or a type
  *)

  val understand_ltac :
    bool -> evar_map -> env -> ltac_var_map ->
    typing_constraint -> rawconstr -> evar_map * constr

  (* Standard call to get a constr from a rawconstr, resolving implicit args *)

  val understand : evar_map -> env -> ?expected_type:Term.types ->
    rawconstr -> constr

  (* Idem but the rawconstr is intended to be a type *)

  val understand_type : evar_map -> env -> rawconstr -> constr

  (* A generalization of the two previous case *)

  val understand_gen : typing_constraint -> evar_map -> env ->
    rawconstr -> constr

  (* Idem but returns the judgment of the understood term *)

  val understand_judgment : evar_map -> env -> rawconstr -> unsafe_judgment

  (* Idem but do not fail on unresolved evars *)
  val understand_judgment_tcc : evar_map ref -> env -> rawconstr -> unsafe_judgment

  (*i*)
  (* Internal of Pretyping...
   *)
  val pretype :
    type_constraint -> env -> evar_map ref ->
    ltac_var_map -> rawconstr -> unsafe_judgment

  val pretype_type :
    val_constraint -> env -> evar_map ref ->
    ltac_var_map -> rawconstr -> unsafe_type_judgment

  val pretype_gen :
    bool -> bool -> bool -> evar_map ref -> env ->
    ltac_var_map -> typing_constraint -> rawconstr -> constr

  (*i*)

end

module Pretyping_F (C : Coercion.S) : S
module Default : S

(* To embed constr in rawconstr *)

val constr_in : constr -> Dyn.t
val constr_out : Dyn.t -> constr

val interp_sort : rawsort -> sorts
val interp_elimination_sort : rawsort -> sorts_family

