(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Identifier
open Names
open Sign
open Univ
open Term
open Evd
open Environ
(*i*)


(* Basic operations of the typing machine. *)

val make_judge : constr -> types -> unsafe_judgment

val j_val : unsafe_judgment -> constr

(* If [j] is the judgement $c:t$, then [assumption_of_judgement env j]
   returns the type $c$, checking that $t$ is a sort. *)

val assumption_of_judgment : 
  env -> 'a evar_map -> unsafe_judgment -> types

val type_judgment : 
  env -> 'a evar_map -> unsafe_judgment -> unsafe_type_judgment

(*s Type of sorts. *)
val judge_of_prop_contents : contents -> unsafe_judgment

val judge_of_type : universe -> unsafe_judgment * constraints

(*s Type of atomic terms. *)
val relative : env -> int -> unsafe_judgment

val type_of_constant : env -> 'a evar_map -> constant -> types

val type_of_existential : env -> 'a evar_map -> existential -> types

(*s Type of an abstraction. *)
val abs_rel : 
  env -> 'a evar_map -> name -> types -> unsafe_judgment 
    -> unsafe_judgment * constraints

(* s Type of a let in. *)
val judge_of_letin :
  env -> 'a evar_map -> name -> unsafe_judgment -> unsafe_judgment 
    -> unsafe_judgment * constraints

(*s Type of application. *)
val apply_rel_list : 
  env -> 'a evar_map -> bool -> unsafe_judgment list -> unsafe_judgment
    -> unsafe_judgment * constraints

(*s Type of a product. *)
val gen_rel :
  env -> 'a evar_map -> name -> unsafe_type_judgment -> unsafe_type_judgment 
    -> unsafe_judgment * constraints

val sort_of_product : sorts -> sorts -> universes -> sorts * constraints

(*s Type of a cast. *)
val cast_rel :
  env -> 'a evar_map -> unsafe_judgment -> types
    -> unsafe_judgment * constraints

(*s Inductive types. *)
open Inductive

val type_of_inductive : env -> 'a evar_map -> inductive -> types

val type_of_constructor : env -> 'a evar_map -> constructor -> types

(*s Type of Cases. *)
val judge_of_case : env -> 'a evar_map -> case_info
  -> unsafe_judgment -> unsafe_judgment 
    -> unsafe_judgment array -> unsafe_judgment * constraints

val find_case_dep_nparams :
  env -> 'a evar_map -> constr * unsafe_judgment -> inductive_family
    -> bool * constraints

val type_case_branches :
  env -> 'a evar_map -> Inductive.inductive_type -> unsafe_judgment
    -> constr -> types array * types * constraints

(*s Type of fixpoints and guard condition. *)
val check_fix : env -> 'a evar_map -> fixpoint -> unit
val check_cofix : env -> 'a evar_map -> cofixpoint -> unit
val type_fixpoint : env -> 'a evar_map -> name array -> types array 
    -> unsafe_judgment array -> constraints

val control_only_guard : env -> 'a evar_map -> constr -> unit

(*i
val hyps_inclusion : env -> 'a evar_map -> named_context -> named_context -> bool
i*)

