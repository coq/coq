(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This module implements the abstract interface to goals *)

type goal

(* spiwack: this primitive is not extremely brilliant. It may be a good
    idea to define goals and proof views in the same file to avoid this
    sort of communication pipes. But I find it heavy. *)
val build : Evd.evar -> goal 

(* Gives a unique identifier to each goal. The identifier is
   guaranteed to contain no space. *)
val uid : goal -> string
(* Returns the goal (even if it has been partially solved)
   corresponding to a unique identifier obtained by {!uid}. *)
val get_by_uid : string -> goal

(* Debugging help *)
val pr_goal : goal -> Pp.std_ppcmds

val goal_ident : Evd.evar_map -> goal -> Names.Id.t

(* [advance sigma g] returns [Some g'] if [g'] is undefined and 
    is the current avatar of [g] (for instance [g] was changed by [clear]
    into [g']). It returns [None] if [g] has been (partially) solved. *)
val advance : Evd.evar_map -> goal -> goal option

val solution : Evd.evar_map -> goal -> Term.constr option

(* Equality function on goals. Return [true] if all of its hypotheses
   and conclusion are equal. *)
val equal : Evd.evar_map -> goal -> Evd.evar_map -> goal -> bool

(* [partition_unifiable sigma l] partitions [l] into a pair [(u,n)]
   where [u] is composed of the unifiable goals, i.e. the goals on
   whose definition other goals of [l] depend, and [n] are the
   non-unifiable goals. *)
val partition_unifiable : Evd.evar_map -> goal list -> goal list * goal list

(* Layer to implement v8.2 tactic engine ontop of the new architecture. 
   Types are different from what they used to be due to a change of the
   internal types. *)
module V82 : sig

  (* Old style env primitive *)
  val env : Evd.evar_map -> goal -> Environ.env

  (* same as [env], but ensures that existential variables are
     normalised *)
  val nf_env : Evd.evar_map -> goal -> Environ.env

  (* Old style hyps primitive *)
  val hyps : Evd.evar_map -> goal -> Environ.named_context_val

  (* same as [hyps], but ensures that existential variables are
     normalised. *)
  val nf_hyps : Evd.evar_map -> goal -> Environ.named_context_val

  (* Access to ".evar_concl" *)
  val concl : Evd.evar_map -> goal -> Term.constr

  (* same as [concl] but ensures that existential variables are
     normalised. *)
  val nf_concl : Evd.evar_map -> goal -> Term.constr

  (* Access to ".evar_extra" *)
  val extra : Evd.evar_map -> goal -> Evd.Store.t

  (* Old style filtered_context primitive *)
  val filtered_context : Evd.evar_map -> goal -> Context.named_context

  (* Old style mk_goal primitive, returns a new goal with corresponding 
       hypotheses and conclusion, together with a term which is precisely
       the evar corresponding to the goal, and an updated evar_map. *)
  val mk_goal : Evd.evar_map -> 
                         Environ.named_context_val ->
                         Term.constr ->
                         Evd.Store.t ->
                         goal * Term.constr * Evd.evar_map

  (* Creates a dummy [goal sigma] for use in auto *)
  val dummy_goal : goal Evd.sigma

  (* Makes a goal out of an evar *)
  (* spiwack: used by [Proofview.init], not entirely clean probably, but it is
      the only way I could think of to preserve compatibility with previous Coq
      stuff. *)
  val build : Evd.evar -> goal 

  (* Instantiates a goal with an open term *)
  val partial_solution : Evd.evar_map -> goal -> Term.constr -> Evd.evar_map

  (* Instantiates a goal with an open term, reusing name of goal for
     second goal *)
  val partial_solution_to : Evd.evar_map -> goal -> goal -> Term.constr -> Evd.evar_map

  (* Principal part of the weak-progress tactical *)
  val weak_progress : goal list Evd.sigma -> goal Evd.sigma -> bool
   
  (* Principal part of the progress tactical *)
  val progress : goal list Evd.sigma -> goal Evd.sigma -> bool
    
 (* Principal part of tclNOTSAMEGOAL *)
  val same_goal : Evd.evar_map -> goal -> Evd.evar_map -> goal -> bool

 (* Used for congruence closure *)
  val new_goal_with : Evd.evar_map -> goal -> Context.named_context -> goal Evd.sigma

  (* Used by the compatibility layer and typeclasses *)
  val nf_evar : Evd.evar_map -> goal -> goal * Evd.evar_map

  (* Goal represented as a type, doesn't take into account section variables *)
  val abstract_type : Evd.evar_map -> goal -> Term.types 

end

(*** Goal tactics. DEPRECATED. ***)

(* Goal sensitive values *)
type +'a sensitive

(* evaluates a goal sensitive value in a given goal (knowing the current evar_map). *)
val eval :
  'a sensitive -> Environ.env -> Evd.evar_map -> goal ->
    'a * Evd.evar_map

(* [enter] combines [env], [defs], [hyps] and [concl] in a single
   primitive. *)
val enter : (Environ.env -> Evd.evar_map -> Term.constr -> goal -> 'a) -> 'a sensitive

val nf_enter : (Environ.env -> Evd.evar_map -> Term.constr -> goal -> 'a) -> 'a sensitive
