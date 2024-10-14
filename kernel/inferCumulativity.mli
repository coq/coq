(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val infer_inductive
  : env_params : Environ.env
  (** Environment containing the polymorphic universes and the
      parameters. *)
  -> env_ar_par : Environ.env
  (** Environment containing the polymorphic universes and the inductives then the parameters. *)
  -> arities : Constr.t list
  -> ctors : Constr.t list list
  -> (Univ.Level.t * UVars.Variance.t option) array
  (** Universes whose cumulativity we want to infer or check. *)
  -> UVars.Variance.t array
