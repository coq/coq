(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Ccalgo
open Names
open Term

type proof =
    Ax of constr
  | SymAx of constr
  | Refl of term
  | Trans of proof * proof
  | Congr of proof * proof
  | Inject of proof * constructor * int * int

val build_proof : 
  forest -> 
  [ `Discr of int * pa_constructor * int * pa_constructor
  | `Prove of int * int ] -> proof

val type_proof :
  (constr, (term * term)) Hashtbl.t -> proof -> term * term


