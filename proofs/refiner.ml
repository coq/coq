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
open Evd

type tactic = Proofview.V82.tac

let sig_it x = x.it
let project x = x.sigma

(* Getting env *)

let pf_env gls = Global.env_of_context (Goal.V82.hyps (project gls) (sig_it gls))
let pf_hyps gls = EConstr.named_context_of_val (Goal.V82.hyps (project gls) (sig_it gls))

let refiner = Logic.refiner

(* A special exception for levels for the Fail tactic *)
exception FailError of int * Pp.t Lazy.t

let catch_failerror (e, info) =
  match e with
  | FailError (lvl,s) when lvl > 0 ->
    Exninfo.iraise (FailError (lvl - 1, s), info)
  | e -> Control.check_for_interrupt ()
