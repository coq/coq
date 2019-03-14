(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open EConstr

exception UFAIL of constr*constr

val unif : Environ.env -> Evd.evar_map -> constr -> constr -> (int*constr) list

type instance=
    Real of (int*constr)*int (* nb trous*terme*valeur heuristique *)
  | Phantom of constr        (* domaine de quantification *)

val unif_atoms : Environ.env -> Evd.evar_map -> metavariable -> constr -> constr -> constr -> instance option

val more_general : Environ.env -> Evd.evar_map -> (int*constr) -> (int*constr) -> bool
