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

val is_quantified_hypothesis : Names.identifier -> bool Goal.sensitive

(*** Introduction tactics ***)

val intro_gen : intro_name_flag Goal.sensitive -> 
                identifier option Goal.sensitive ->
                bool Goal.sensitive ->
                unit Proofview.tactic

val intro : unit Proofview.tactic
val introf : unit Proofview.tactic
val intros : unit Proofview.tactic

(* arnaud: à virer ?
val intros_until :  Rawterm.quantified_hypothesis Goal.sensitive -> 
                    unit Proofview.tactic
*)
val intros_until_id : Names.identifier Goal.sensitive -> unit Proofview.tactic
val intros_until_n : int Goal.sensitive -> unit Proofview.tactic


val intros_rmove : (Names.identifier  * 
		      Names.identifier option) list Goal.sensitive -> 
                    unit Proofview.tactic

(* arnaud: pas sûr que ce "'a" soit désirable. N'était pas dehors
   dans la version originale de tactics.ml{,i}. *)
val intros_move  : (Names.identifier * 'a option) list Goal.sensitive -> 
                   unit Proofview.tactic
