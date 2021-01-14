(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Library for manipulating integers based on binary encoding *)

Require Export ZArith_base.

(** Extra definitions *)

Require Export Zpow_def.

(** Extra modules using [Omega] or [Ring]. *)

Set Warnings "-deprecated-omega-plugin".
Require Export Omega.
Require Export Zcomplements.
Require Export Zpower.
Require Export Zdiv.

Export ZArithRing.
