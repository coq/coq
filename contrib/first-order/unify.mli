(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Libnames
open Term

type instance=
    Real of (constr*int) (* instance*valeur heuristique*)
  | Phantom of constr (* domaine de quantification *)

val unif_atoms : metavariable -> constr -> constr -> constr -> instance option
  
val give_right_instances : metavariable -> constr -> bool -> Formula.atoms -> 
  Sequent.t -> (constr*int) list option

val give_left_instances : Formula.left_formula list-> Sequent.t -> 
  (instance*global_reference) list
