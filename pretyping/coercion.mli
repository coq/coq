(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Evd
open Names
open Environ
open EConstr
open Glob_term

(** {6 Coercions. } *)

(** [inh_app_fun resolve_tc env isevars j] coerces [j] to a function; i.e. it
    inserts a coercion into [j], if needed, in such a way it gets as
    type a product; it returns [j] if no coercion is applicable.
    resolve_tc=false disables resolving type classes (as the last
    resort before failing) *)
val inh_app_fun : bool ->
  env -> evar_map -> unsafe_judgment -> evar_map * unsafe_judgment

(** [inh_coerce_to_sort env isevars j] coerces [j] to a type; i.e. it
    inserts a coercion into [j], if needed, in such a way it gets as
    type a sort; it fails if no coercion is applicable *)
val inh_coerce_to_sort : ?loc:Loc.t ->
  env -> evar_map -> unsafe_judgment -> evar_map * unsafe_type_judgment

(** [inh_coerce_to_base env isevars j] coerces [j] to its base type; i.e. it
    inserts a coercion into [j], if needed, in such a way it gets as
    type its base type (the notion depends on the coercion system) *)
val inh_coerce_to_base : ?loc:Loc.t ->
  env -> evar_map -> unsafe_judgment -> evar_map * unsafe_judgment

(** [inh_coerce_to_prod env isevars t] coerces [t] to a product type *)
val inh_coerce_to_prod : ?loc:Loc.t ->
  env -> evar_map -> types -> evar_map * types

(** [inh_conv_coerce_to resolve_tc Loc.t env isevars j t] coerces [j] to an 
    object of type [t]; i.e. it inserts a coercion into [j], if needed, in such
    a way [t] and [j.uj_type] are convertible; it fails if no coercion is
    applicable. resolve_tc=false disables resolving type classes (as the last
    resort before failing) *)
val inh_conv_coerce_to : ?loc:Loc.t -> bool ->
  env -> evar_map -> unsafe_judgment -> types -> evar_map * unsafe_judgment

val inh_conv_coerce_rigid_to : ?loc:Loc.t -> bool ->
  env -> evar_map -> unsafe_judgment -> types -> evar_map * unsafe_judgment

(** [inh_conv_coerces_to loc env isevars t t'] checks if an object of type [t]
    is coercible to an object of type [t'] adding evar constraints if needed;
    it fails if no coercion exists *)
val inh_conv_coerces_to : ?loc:Loc.t ->
  env -> evar_map -> types -> types -> evar_map

(** [inh_pattern_coerce_to loc env isevars pat ind1 ind2] coerces the Cases
    pattern [pat] typed in [ind1] into a pattern typed in [ind2];
    raises [Not_found] if no coercion found *)
val inh_pattern_coerce_to :
  ?loc:Loc.t -> env -> cases_pattern -> inductive -> inductive -> cases_pattern
