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

Require Export BinPos.
Require Export BinNat.
Require Export BinInt.
Require Export Zcompare.
Require Export Old_zorder.
Require Export Zeven.
Require Export Zmin.
Require Export Zmax.
Require Export Zminmax.
Require Export Zabs.
Require Export Znat.
Require Export auxiliary.
Require Export ZArith_dec.
Require Export Zbool.
Require Export Zmisc.
Require Export Wf_Z.

Hint Resolve Zle_refl Zplus_comm Zplus_assoc Zmult_comm Zmult_assoc Zplus_0_l
  Zplus_0_r Zmult_1_l Zplus_opp_l Zplus_opp_r Zmult_plus_distr_l
  Zmult_plus_distr_r: zarith.

Require Export Zhints.
