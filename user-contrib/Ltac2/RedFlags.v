(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.
Require Import Ltac2.Std.

Ltac2 Type t := Std.red_flags.

Module Export Notations.
Ltac2 Notation "red_flags:(" s(strategy) ")" : 0 := s.
End Notations.

Ltac2 none := {
  rBeta := false; rMatch := false; rFix := false; rCofix := false;
  rZeta := false; rDelta := false; rConst := []; rStrength := Norm;
}.

Ltac2 all : t := {
  rBeta := true; rMatch := true; rFix := true; rCofix := true;
  rZeta := true; rDelta := true; rConst := []; rStrength := Norm;
}.

Ltac2 beta : t := red_flags:(beta).
Ltac2 beta_delta_zeta : t := red_flags:(beta delta zeta).
Ltac2 beta_iota : t := red_flags:(beta iota).
Ltac2 beta_iota_zeta : t := red_flags:(beta iota zeta).
Ltac2 beta_zeta : t := red_flags:(beta zeta).
Ltac2 delta : t := red_flags:(delta).
Ltac2 zeta : t := red_flags:(zeta).
