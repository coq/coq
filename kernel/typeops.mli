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
open Univ
open Term
open Environ
open Entries
open Declarations
(*i*)

(*s Typing functions (not yet tagged as safe) *)

val infer      : env -> constr       -> unsafe_judgment * constraints
val infer_v    : env -> constr array -> unsafe_judgment array * constraints
val infer_type : env -> types        -> unsafe_type_judgment * constraints

val infer_local_decls :
  env -> (identifier * local_entry) list
    -> env * Sign.rel_context * constraints

(*s Basic operations of the typing machine. *)

(* If [j] is the judgement $c:t$, then [assumption_of_judgement env j]
   returns the type $c$, checking that $t$ is a sort. *)

val assumption_of_judgment :  env -> unsafe_judgment -> types
val type_judgment          :  env -> unsafe_judgment -> unsafe_type_judgment

(*s Type of sorts. *)
val judge_of_prop_contents : contents -> unsafe_judgment
val judge_of_type          : universe -> unsafe_judgment

(*s Type of a bound variable. *)
val judge_of_relative : env -> int -> unsafe_judgment

(*s Type of variables *)
val judge_of_variable : env -> variable -> unsafe_judgment

(*s type of a constant *)
val judge_of_constant : env -> constant -> unsafe_judgment

val judge_of_constant_knowing_parameters :
  env -> constant -> unsafe_judgment array -> unsafe_judgment

(*s Type of application. *)
val judge_of_apply : 
  env -> unsafe_judgment -> unsafe_judgment array
    -> unsafe_judgment * constraints

(*s Type of an abstraction. *)
val judge_of_abstraction : 
  env -> name -> unsafe_type_judgment -> unsafe_judgment 
    -> unsafe_judgment

(*s Type of a product. *)
val judge_of_product :
  env -> name -> unsafe_type_judgment -> unsafe_type_judgment 
    -> unsafe_judgment

(* s Type of a let in. *)
val judge_of_letin :
  env -> name -> unsafe_judgment -> unsafe_type_judgment -> unsafe_judgment 
    -> unsafe_judgment

(*s Type of a cast. *)
val judge_of_cast :
  env -> unsafe_judgment -> cast_kind -> unsafe_type_judgment ->
    unsafe_judgment * constraints

(*s Inductive types. *)

val judge_of_inductive : env -> inductive -> unsafe_judgment

val judge_of_inductive_knowing_parameters : 
  env -> inductive -> unsafe_judgment array -> unsafe_judgment

val judge_of_constructor : env -> constructor -> unsafe_judgment

(*s Type of Cases. *)
val judge_of_case : env -> case_info
  -> unsafe_judgment -> unsafe_judgment -> unsafe_judgment array
    -> unsafe_judgment * constraints

(* Typecheck general fixpoint (not checking guard conditions) *)
val type_fixpoint : env -> name array -> types array 
    -> unsafe_judgment array -> constraints

(* Kernel safe typing but applicable to partial proofs *)
val typing : env -> constr -> unsafe_judgment

val type_of_constant : env -> constant -> types

val type_of_constant_type : env -> constant_type -> types

val type_of_constant_knowing_parameters : 
  env -> constant_type -> constr array -> types

(* Make a type polymorphic if an arity *)
val make_polymorphic_if_arity : env -> types -> constant_type

