(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(** Library for manipulating integers based on binary encoding.
    These are the basic modules, required by [Omega] and [Ring] for instance. 
    The full library is [ZArith]. *)

V7only [
Require Export fast_integer.
Require Export zarith_aux.
].
Require Export BinPos.
Require Export BinNat.
Require Export BinInt.
Require Export Zcompare.
Require Export Zorder.
Require Export Zeven.
Require Export Zmin.
Require Export Zabs.
Require Export Znat.
Require Export auxiliary.
Require Export Zsyntax.
Require Export ZArith_dec.
Require Export Zbool.
Require Export Zmisc.
Require Export Wf_Z.

Hints Resolve Zle_n Zplus_sym Zplus_assoc Zmult_sym Zmult_assoc
  Zero_left Zero_right Zmult_one Zplus_inverse_l Zplus_inverse_r 
  Zmult_plus_distr_l Zmult_plus_distr_r : zarith.

Require Export Zhints.
