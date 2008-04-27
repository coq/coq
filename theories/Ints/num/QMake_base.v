(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id:$ *)

(** * An implementation of rational numbers based on big integers *)

(** 
- Authors: Benjamin Grégoire, Laurent Théry
- Institution: INRIA
- Date: 2007
*)

Require Export BigN.
Require Export BigZ.

(* Basic type for Q: a Z or a pair of a Z and an N *)

Inductive q_type : Set := 
 | Qz : BigZ.t -> q_type
 | Qq : BigZ.t -> BigN.t -> q_type.

Definition print_type x := 
 match x with
 | Qz _ => Z
 | _ => (Z*Z)%type
 end.

Definition print x :=
 match x return print_type x with
 | Qz zx => BigZ.to_Z zx
 | Qq nx dx => (BigZ.to_Z nx, BigN.to_Z dx)
 end.
