(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Univ
open Term
open Sign
(*i*)

(* This module defines the types of global declarations. This includes
   global constants/axioms and mutual inductive definitions *)

(*s Constants (internal representation) (Definition/Axiom) *)

type constant_body = {
  const_hyps : section_context; (* New: younger hyp at top *)
  const_body : constr option;
  const_type : types;
  const_constraints : constraints;
  const_opaque : bool }

(*s Inductive types (internal representation with redundant
    information). *)

type recarg = 
  | Norec 
  | Mrec of int 
  | Imbr of inductive

type wf_paths = recarg Rtree.t

val mk_norec : wf_paths
val mk_paths : recarg -> wf_paths list array -> wf_paths
val dest_recarg : wf_paths -> recarg
val dest_subterms : wf_paths -> wf_paths list array

(* [mind_typename] is the name of the inductive; [mind_arity] is
   the arity generalized over global parameters; [mind_lc] is the list
   of types of constructors generalized over global parameters and
   relative to the global context enriched with the arities of the
   inductives *) 

type one_inductive_body = {
  mind_typename : identifier;
  mind_nparams : int;
  mind_params_ctxt : rel_context;
  mind_nrealargs : int;
  mind_nf_arity : types;
  mind_user_arity : types;
  mind_sort : sorts;
  mind_kelim : sorts_family list;
  mind_consnames : identifier array;
  mind_nf_lc : types array; (* constrs and arity with pre-expanded ccl *)
  mind_user_lc : types array;
  mind_recargs : wf_paths;
 }

type mutual_inductive_body = {
  mind_finite : bool;
  mind_ntypes : int;
  mind_hyps : section_context;
  mind_packets : one_inductive_body array;
  mind_constraints : constraints;
  mind_singl : constr option }
