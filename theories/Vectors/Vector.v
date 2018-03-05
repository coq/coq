(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Vectors.

   Author: Pierre Boutillier
   Institution: PPS, INRIA 12/2010

Originally from the contribution bit vector by Jean Duprat (ENS Lyon).

Based on contents from Util/VecUtil of the CoLoR contribution *)

Require Fin.
Require VectorDef.
Require VectorSpec.
Require VectorEq.
Include VectorDef.
Include VectorSpec.
Include VectorEq.
