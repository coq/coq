(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

Require Export ZArith.
Require Export ZArith_dec.

Theorem Znotzero : (x:Z){`x<>0`}+{`x=0`}.
Proof.
Intro x. Elim (Z_eq_dec x `0`) ; Auto.
Save.
