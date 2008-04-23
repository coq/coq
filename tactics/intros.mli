(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(************************************************************************)
(*                                                                      *)
(*   This file defines the high-level intro and intros tactic.          *)
(*   Those the user sees.                                               *)
(*                                                                      *)
(************************************************************************)

open Names


(*** Related functions ***)

type intro_name_flag =
  | IntroAvoid of identifier list
  | IntroBasedOn of identifier * identifier list
  | IntroMustBe of identifier

val find_name : name * Term.types option * Term.types ->
                intro_name_flag -> 
                identifier Goal.sensitive

(*** Introduction tactics ***)

val intro_gen : intro_name_flag Goal.sensitive -> 
                identifier option Goal.sensitive ->
                bool Goal.sensitive ->
                unit Proofview.tactic

val intro : unit Proofview.tactic
val intros : unit Proofview.tactic

(* arnaud: à virer ?
val intros_until :  Rawterm.quantified_hypothesis Goal.sensitive -> 
                    unit Proofview.tactic
*)
val intros_until_id : Names.identifier Goal.sensitive -> unit Proofview.tactic

