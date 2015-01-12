(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * The Set universe seen as a synonym for Type *)

(** After loading this file, Set becomes just another name for Type.
    This allows easily performing a Set-to-Type migration, or at least
    test whether a development relies or not on specific features of
    Set: simply insert some Require Export of this file at starting
    points of the development and try to recompile...  *)

Notation "'Set'" := Type (only parsing).
