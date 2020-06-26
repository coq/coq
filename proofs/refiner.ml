(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util

(* A special exception for levels for the Fail tactic *)
exception FailError of int * Pp.t Lazy.t

let catch_failerror (e, info) =
  match e with
  | FailError (lvl,s) when lvl > 0 ->
    Exninfo.iraise (FailError (lvl - 1, s), info)
  | e -> Control.check_for_interrupt ()
