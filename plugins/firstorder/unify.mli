(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open EConstr

module Item :
sig
  type t
  val compare : t -> t -> int
  val is_ground : t -> bool
  val repr : t -> int * constr (* nb trous * terme *)
end

type instance=
    Real of Item.t * int (* terme * valeur heuristique *)
  | Phantom of constr        (* domaine de quantification *)

val unif_atoms : check:bool -> Formula.Env.t -> Environ.env -> Evd.evar_map -> metavariable -> constr -> Formula.atom -> Formula.atom -> instance option

val more_general : Environ.env -> Evd.evar_map -> Item.t -> Item.t -> bool
