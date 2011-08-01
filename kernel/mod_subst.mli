(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*s [Mod_subst] *)

open Names
open Term

(* A delta_resolver maps name (constant, inductive, module_path) 
   to canonical name  *)
type delta_resolver

type substitution

val empty_delta_resolver : delta_resolver

val add_inline_delta_resolver : constant -> delta_resolver -> delta_resolver

val add_inline_constr_delta_resolver :  constant -> constr -> delta_resolver 
  -> delta_resolver

val add_constant_delta_resolver : constant -> delta_resolver -> delta_resolver

val add_mind_delta_resolver : mutual_inductive -> delta_resolver -> delta_resolver

val add_mp_delta_resolver : module_path -> module_path -> delta_resolver 
  -> delta_resolver

val add_delta_resolver : delta_resolver -> delta_resolver -> delta_resolver

(* Apply the substitution on the domain of the resolver  *)
val subst_dom_delta_resolver : substitution -> delta_resolver -> delta_resolver

(* Apply the substitution on the codomain of the resolver  *)
val subst_codom_delta_resolver : substitution -> delta_resolver -> delta_resolver

val subst_dom_codom_delta_resolver : 
  substitution -> delta_resolver -> delta_resolver

(* *_of_delta return the associated name of arg2 in arg1   *)
val constant_of_delta : delta_resolver -> constant -> constant

val mind_of_delta : delta_resolver -> mutual_inductive -> mutual_inductive

val delta_of_mp : delta_resolver -> module_path -> module_path

(* Extract the set of inlined constant in the resolver *)
val inline_of_delta : delta_resolver -> kernel_name list

(* remove_mp is used for the computation of a resolver induced by Include P *)
val remove_mp_delta_resolver : delta_resolver -> module_path -> delta_resolver


(* mem tests *)
val mp_in_delta : module_path -> delta_resolver -> bool

val con_in_delta : constant -> delta_resolver -> bool

val mind_in_delta : mutual_inductive -> delta_resolver -> bool

(*substitution*)

val empty_subst : substitution

(* add_* add [arg2/arg1]{arg3} to the substitution with no 
   sequential composition  *)
val add_mbid :
  mod_bound_id -> module_path -> delta_resolver  -> substitution -> substitution
val add_mp :
  module_path -> module_path -> delta_resolver -> substitution -> substitution

(* map_* create a new substitution [arg2/arg1]{arg3} *)
val map_mbid :
  mod_bound_id -> module_path -> delta_resolver -> substitution
val map_mp :
  module_path -> module_path -> delta_resolver -> substitution

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
val debug_string_of_delta : delta_resolver -> string
val debug_pr_delta : delta_resolver -> Pp.std_ppcmds
(*i*)

(* [subst_mp sub mp] guarantees that whenever the result of the
   substitution is structutally equal [mp], it is equal by pointers
   as well [==] *)

val subst_mp :
  substitution -> module_path -> module_path

val subst_ind :
  substitution -> mutual_inductive -> mutual_inductive

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
val replace_mp_in_kn : module_path -> module_path -> kernel_name -> kernel_name

(* [subst_mps sub c] performs the substitution [sub] on all kernel
   names appearing in [c] *)
val subst_mps : substitution -> constr -> constr

(* [occur_*id id sub] returns true iff [id] occurs in [sub]
   on either side *)

val occur_mbid : mod_bound_id -> substitution -> bool

(** [repr_substituted r] dumps the representation of a substituted:
    - [None, a] when r is a value
    - [Some s, a] when r is a delayed substitution [s] applied to [a] *)

val repr_substituted : 'a substituted -> substitution list option * 'a
