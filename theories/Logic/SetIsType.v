(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * The Set universe seen as a synonym for Type *)

(** After loading this file, Set becomes just another name for Type.
    This allows easily performing a Set-to-Type migration, or at least
    test whether a development relies or not on specific features of
    Set: simply insert some Require Export of this file at starting
    points of the development and try to recompile...  *)

Notation "'Set'" := Type (only parsing).
