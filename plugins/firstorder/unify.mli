(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term

exception UFAIL of constr*constr

val unif : constr -> constr -> (int*constr) list

type instance=
    Real of (int*constr)*int (* nb trous*terme*valeur heuristique *)
  | Phantom of constr        (* domaine de quantification *)

val unif_atoms : metavariable -> constr -> constr -> constr -> instance option

val more_general : (int*constr) -> (int*constr) -> bool
