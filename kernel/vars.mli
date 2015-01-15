(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Constr
open Context

(** {6 Occur checks } *)

(** [closedn n M] is true iff [M] is a (deBruijn) closed term under n binders *)
val closedn : int -> constr -> bool

(** [closed0 M] is true iff [M] is a (deBruijn) closed term *)
val closed0 : constr -> bool

(** [noccurn n M] returns true iff [Rel n] does NOT occur in term [M]  *)
val noccurn : int -> constr -> bool

(** [noccur_between n m M] returns true iff [Rel p] does NOT occur in term [M]
  for n <= p < n+m *)
val noccur_between : int -> int -> constr -> bool

(** Checking function for terms containing existential- or
   meta-variables.  The function [noccur_with_meta] does not consider
   meta-variables applied to some terms (intended to be its local
   context) (for existential variables, it is necessarily the case) *)
val noccur_with_meta : int -> int -> constr -> bool

(** {6 Relocation and substitution } *)

(** [exliftn el c] lifts [c] with lifting [el] *)
val exliftn : Esubst.lift -> constr -> constr

(** [liftn n k c] lifts by [n] indexes above or equal to [k] in [c] *)
val liftn : int -> int -> constr -> constr

(** [lift n c] lifts by [n] the positive indexes in [c] *)
val lift : int -> constr -> constr

(** [substnl [a1;...;an] k c] substitutes in parallel [a1],...,[an]
    for respectively [Rel(k+1)],...,[Rel(k+n)] in [c]; it relocates
    accordingly indexes in [a1],...,[an] and [c] *)
val substnl : constr list -> int -> constr -> constr
val substl : constr list -> constr -> constr
val subst1 : constr -> constr -> constr

val substnl_decl : constr list -> int -> rel_declaration -> rel_declaration
val substl_decl : constr list -> rel_declaration -> rel_declaration
val subst1_decl : constr -> rel_declaration -> rel_declaration

val substnl_named_decl : constr list -> int -> named_declaration -> named_declaration
val subst1_named_decl : constr -> named_declaration -> named_declaration
val substl_named_decl : constr list -> named_declaration -> named_declaration

val replace_vars : (Id.t * constr) list -> constr -> constr
(** (subst_var str t) substitute (VAR str) by (Rel 1) in t *)
val subst_var : Id.t -> constr -> constr

(** [subst_vars [id1;...;idn] t] substitute [VAR idj] by [Rel j] in [t]
   if two names are identical, the one of least indice is kept *)
val subst_vars : Id.t list -> constr -> constr

(** [substn_vars n [id1;...;idn] t] substitute [VAR idj] by [Rel j+n-1] in [t]
   if two names are identical, the one of least indice is kept *)
val substn_vars : int -> Id.t list -> constr -> constr

(** {3 Substitution of universes} *)

open Univ

val subst_univs_fn_constr : universe_subst_fn -> constr -> constr
val subst_univs_fn_puniverses : universe_level_subst_fn -> 
  'a puniverses -> 'a puniverses

val subst_univs_constr : universe_subst -> constr -> constr

(** Level substitutions for polymorphism. *)

val subst_univs_level_constr : universe_level_subst -> constr -> constr
val subst_univs_level_context : Univ.universe_level_subst -> rel_context -> rel_context

(** Instance substitution for polymorphism. *)
val subst_instance_constr : universe_instance -> constr -> constr
val subst_instance_context : universe_instance -> rel_context -> rel_context

type id_key = pconstant tableKey
val eq_id_key : id_key -> id_key -> bool
