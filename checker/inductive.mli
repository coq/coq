(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Names
open Term
open Declarations
open Environ
(*i*)

(*s Extracting an inductive type from a construction *)

val find_rectype : env -> constr -> inductive * constr list

type mind_specif = mutual_inductive_body * one_inductive_body

(*s Fetching information in the environment about an inductive type.
    Raises [Not_found] if the inductive type is not found. *)
val lookup_mind_specif : env -> inductive -> mind_specif

val type_of_inductive : env -> mind_specif -> constr

(* Return type as quoted by the user *)
val type_of_constructor : constructor -> mind_specif -> constr

val arities_of_specif : mutual_inductive -> mind_specif -> constr array

(* [type_case_branches env (I,args) (p:A) c] computes useful types
   about the following Cases expression:
      <p>Cases (c :: (I args)) of b1..bn end
   It computes the type of every branch (pattern variables are
   introduced by products) and the type for the whole expression.
 *)
val type_case_branches :
  env -> inductive * constr list -> constr * constr -> constr
    -> constr array * constr

(* Check a [case_info] actually correspond to a Case expression on the
   given inductive type. *)
val check_case_info : env -> inductive -> case_info -> unit

(*s Guard conditions for fix and cofix-points. *)
val check_fix : env -> fixpoint -> unit
val check_cofix : env -> cofixpoint -> unit

(*s Support for sort-polymorphic inductive types *)

val type_of_inductive_knowing_parameters :
  env -> one_inductive_body -> constr array -> constr

val max_inductive_sort : sorts array -> Univ.universe

val instantiate_universes : env -> rel_context ->
    polymorphic_arity -> constr array -> rel_context * sorts

(***************************************************************)
(* Debug *)

type size = Large | Strict
type subterm_spec =
    Subterm of (size * wf_paths)
  | Dead_code
  | Not_subterm
type guard_env =
  { env     : env;
    (* dB of last fixpoint *)
    rel_min : int;
    (* inductive of recarg of each fixpoint *)
    inds    : inductive array;
    (* the recarg information of inductive family *)
    recvec  : wf_paths array;
    (* dB of variables denoting subterms *)
    genv    : subterm_spec Lazy.t list;
  }

type stack_element = |SClosure of guard_env*constr |SArg of subterm_spec Lazy.t
val subterm_specif : guard_env -> stack_element list -> constr -> subterm_spec
val branches_specif : guard_env -> subterm_spec Lazy.t -> case_info ->
  subterm_spec Lazy.t list array
