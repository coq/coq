(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*s [Mod_subst] *)

open Names
open Term

type resolver
type substitution

val make_resolver :  (constant * constr option) list -> resolver

val empty_subst : substitution

val add_msid : 
  mod_self_id -> module_path -> substitution -> substitution
val add_mbid : 
  mod_bound_id -> module_path -> resolver option -> substitution -> substitution
val add_mp :
  module_path -> module_path -> substitution -> substitution

val map_msid :
  mod_self_id -> module_path -> substitution
val map_mbid :
  mod_bound_id -> module_path -> resolver option -> substitution
val map_mp :
  module_path -> module_path -> substitution

(* sequential composition: 
   [substitute (join sub1 sub2) t = substitute sub2 (substitute sub1 t)]
*)
val join : substitution -> substitution -> substitution

type 'a substituted
val from_val : 'a -> 'a substituted
val force : (substitution -> 'a -> 'a) -> 'a substituted -> 'a
val subst_substituted : substitution -> 'a substituted -> 'a substituted

(*i debugging *)
val debug_string_of_subst : substitution -> string
val debug_pr_subst : substitution -> Pp.std_ppcmds
(*i*)

(* [subst_mp sub mp] guarantees that whenever the result of the
   substitution is structutally equal [mp], it is equal by pointers 
   as well [==] *) 

val subst_mp : 
  substitution -> module_path -> module_path

val subst_kn :
  substitution -> kernel_name -> kernel_name

val subst_con :
  substitution -> constant -> constant * constr

(* Here the semantics is completely unclear.
   What does "Hint Unfold t" means when "t" is a parameter?
   Does the user mean "Unfold X.t" or does she mean "Unfold y"
   where X.t is later on instantiated with y? I choose the first
   interpretation (i.e. an evaluable reference is never expanded). *)
val subst_evaluable_reference :
  substitution -> evaluable_global_reference -> evaluable_global_reference

(* [replace_mp_in_con mp mp' con] replaces [mp] with [mp'] in [con] *)
val replace_mp_in_con : module_path -> module_path -> constant -> constant

(* [subst_mps sub c] performs the substitution [sub] on all kernel
   names appearing in [c] *)
val subst_mps : substitution -> constr -> constr

(* [occur_*id id sub] returns true iff [id] occurs in [sub] 
   on either side *)

val occur_msid : mod_self_id -> substitution -> bool
val occur_mbid : mod_bound_id -> substitution -> bool

val update_subst_alias : substitution -> substitution -> substitution

val subst_key : substitution -> substitution -> substitution

val join_alias : substitution -> substitution -> substitution

val remove_alias : substitution -> substitution
