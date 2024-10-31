(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
Attributes deprecated(since="9.0", note="use Init.Basics").
Require Export Init.Basics.
#[deprecated(use=compose, since="9.0")]
Notation compose := compose (only parsing).
#[deprecated(use=arrow, since="9.0")]
Notation arrow := arrow (only parsing).
#[deprecated(use=impl, since="9.0")]
Notation impl := impl (only parsing).
#[deprecated(use=const, since="9.0")]
Notation const := const (only parsing).
#[deprecated(use=flip, since="9.0")]
Notation flip := flip (only parsing).
#[deprecated(use=apply, since="9.0")]
Notation apply := apply (only parsing).
