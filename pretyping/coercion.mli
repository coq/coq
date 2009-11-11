(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Evd
open Names
open Term
open Sign
open Environ
open Evarutil
open Rawterm
(*i*)

module type S = sig
  (*s Coercions. *)

  (* [inh_app_fun env isevars j] coerces [j] to a function; i.e. it
     inserts a coercion into [j], if needed, in such a way it gets as
     type a product; it returns [j] if no coercion is applicable *)
  val inh_app_fun :
    env -> evar_map -> unsafe_judgment -> evar_map * unsafe_judgment

  (* [inh_coerce_to_sort env isevars j] coerces [j] to a type; i.e. it
     inserts a coercion into [j], if needed, in such a way it gets as
     type a sort; it fails if no coercion is applicable *)
  val inh_coerce_to_sort : loc ->
    env -> evar_map -> unsafe_judgment -> evar_map * unsafe_type_judgment

  (* [inh_coerce_to_base env isevars j] coerces [j] to its base type; i.e. it
     inserts a coercion into [j], if needed, in such a way it gets as
     type its base type (the notion depends on the coercion system) *)
  val inh_coerce_to_base : loc ->
    env -> evar_map -> unsafe_judgment -> evar_map * unsafe_judgment

  (* [inh_coerce_to_prod env isevars t] coerces [t] to a product type *)
  val inh_coerce_to_prod : loc ->
    env -> evar_map -> type_constraint_type -> evar_map * type_constraint_type

  (* [inh_conv_coerce_to loc env isevars j t] coerces [j] to an object of type
     [t]; i.e. it inserts a coercion into [j], if needed, in such a way [t] and
     [j.uj_type] are convertible; it fails if no coercion is applicable *)
  val inh_conv_coerce_to : loc ->
    env -> evar_map -> unsafe_judgment -> type_constraint_type -> evar_map * unsafe_judgment

  val inh_conv_coerce_rigid_to : loc ->
    env -> evar_map -> unsafe_judgment -> type_constraint_type -> evar_map * unsafe_judgment

  (* [inh_conv_coerces_to loc env isevars t t'] checks if an object of type [t]
     is coercible to an object of type [t'] adding evar constraints if needed;
     it fails if no coercion exists *)
  val inh_conv_coerces_to : loc ->
    env -> evar_map -> types -> type_constraint_type -> evar_map

  (* [inh_pattern_coerce_to loc env isevars pat ind1 ind2] coerces the Cases
     pattern [pat] typed in [ind1] into a pattern typed in [ind2];
     raises [Not_found] if no coercion found *)
  val inh_pattern_coerce_to :
    loc  -> cases_pattern -> inductive -> inductive -> cases_pattern
end

module Default : S
