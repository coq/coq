(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(*i $Id$ i*)

open Ast
open Coqast
open Hipattern
open Names
open Libnames
open Pp
open Proof_type
open Tacticals
open Tacinterp
open Tactics
open Util
   
let is_empty ist =
  if (is_empty_type (List.assoc (id_of_string "1") ist.lmatch)) then
    <:tactic<Idtac>>
  else
    <:tactic<Fail>>

let is_unit ist =
  if (is_unit_type (List.assoc (id_of_string "1") ist.lmatch)) then
    <:tactic<Idtac>>
  else
    <:tactic<Fail>>
    
let is_conj ist =
  let ind=(List.assoc (id_of_string "1") ist.lmatch) in
    if (is_conjunction ind) && (is_nodep_ind ind) then
      <:tactic<Idtac>>
    else
      <:tactic<Fail>>

let is_disj ist =
  if (is_disjunction (List.assoc (id_of_string "1") ist.lmatch)) then
    <:tactic<Idtac>>
  else
    <:tactic<Fail>>

let not_dep_intros ist =
  <:tactic<
  Repeat
    Match Context With
| [|- ?1 -> ?2 ] -> Intro
| [|- (Coq.Init.Logic.iff ? ?)] -> Unfold Coq.Init.Logic.iff
| [|- (Coq.Init.Logic.not ?)] -> Unfold Coq.Init.Logic.not
| [ H:(Coq.Init.Logic.iff ? ?)|- ?] -> Unfold Coq.Init.Logic.iff in H
| [ H:(Coq.Init.Logic.not ?)|-?] -> Unfold Coq.Init.Logic.not in H
| [ H:(Coq.Init.Logic.iff ? ?)->?|- ?] -> Unfold Coq.Init.Logic.iff in H
| [ H:(Coq.Init.Logic.not ?)->?|-?] -> Unfold Coq.Init.Logic.not in H >>
				      
let axioms ist =
  let t_is_unit = tacticIn is_unit
  and t_is_empty = tacticIn is_empty in
    <:tactic<
    Match Reverse Context With
      |[|- ?1] -> $t_is_unit;Constructor 1
      |[_:?1 |- ?] -> $t_is_empty;ElimType ?1;Assumption
      |[_:?1 |- ?1] -> Assumption>>


let simplif ist =
  let t_is_unit = tacticIn is_unit
  and t_is_conj = tacticIn is_conj
  and t_is_disj = tacticIn is_disj
  and t_not_dep_intros = tacticIn not_dep_intros in
  <:tactic<
    $t_not_dep_intros;
    Repeat
      ((Match Reverse Context With
        | [id: (?1 ? ?) |- ?] ->
            $t_is_conj;Elim id;Do 2 Intro;Clear id
        | [id: (?1 ? ?) |- ?] -> $t_is_disj;Elim id;Intro;Clear id
        | [id0: ?1-> ?2; id1: ?1|- ?] -> Generalize (id0 id1);Intro;Clear id0
        | [id: ?1 -> ?2|- ?] ->
          $t_is_unit;Cut ?2;
	    [Intro;Clear id
	    | (* id : ?1 -> ?2 |- ?2 *)
	      Cut ?1;[Exact id|Constructor 1;Fail]
	    ]
        | [id: (?1 ?2 ?3) -> ?4|- ?] ->
          $t_is_conj;Cut ?2-> ?3-> ?4;
	    [Intro;Clear id
	    | (* id: (?1 ?2 ?3) -> ?4 |- ?2 -> ?3 -> ?4 *)
	      Intro;Intro; Cut (?1 ?2 ?3);[Exact id|Split;Assumption]
	    ]
        | [id: (?1 ?2 ?3) -> ?4|- ?] ->
          $t_is_disj;
	    Cut ?3-> ?4;
	      [Cut ?2-> ?4;
	        [Intro;Intro;Clear id
		| (* id: (?1 ?2 ?3) -> ?4 |- ?2 -> ?4 *)
		  Intro; Cut (?1 ?2 ?3);[Exact id|Left;Assumption]
		]
	      | (* id: (?1 ?2 ?3) -> ?4 |- ?3 -> ?4 *)
		Intro; Cut (?1 ?2 ?3);[Exact id|Right;Assumption]
	      ]
        | [|- (?1 ? ?)] -> $t_is_conj;Split);
       $t_not_dep_intros)>>

let rec tauto_intuit t_reduce solver ist =
  let t_axioms = tacticIn axioms
  and t_simplif = tacticIn simplif
  and t_is_disj = tacticIn is_disj
  and t_tauto_intuit = tacticIn (tauto_intuit t_reduce solver) in
  let t_solver = Tacexpr.TacArg (valueIn (VTactic (dummy_loc,solver))) in
  <:tactic<
   ($t_simplif;$t_axioms
    Orelse
      (Match Reverse Context With
      | [id:(?1-> ?2)-> ?3|- ?] ->
	  Cut ?3;
	    [ Intro;Clear id;$t_tauto_intuit 
	    | Cut ?1 -> ?2;
		[ Exact id
		| Generalize [y:?2](id [x:?1]y);Intro;Clear id;
		  Solve [ $t_tauto_intuit ]]]
      | [|- (?1 ? ?)] ->
          $t_is_disj;Solve [Left;$t_tauto_intuit | Right;$t_tauto_intuit]
      )
    Orelse
    (* NB: [|- ? -> ?] matches any product *)
    (Match Context With |[ |- ? -> ? ] -> Intro;$t_tauto_intuit
    |[|-?]->$t_reduce;$t_solver)
    Orelse
    $t_solver
   ) >>
    
let reduction_not_iff=interp
 <:tactic<Repeat 
	(Match Context With 
	|[|- ?]->
	   Progress Unfold Coq.Init.Logic.not Coq.Init.Logic.iff 
	|[H:?|- ?]->
	   Progress Unfold Coq.Init.Logic.not Coq.Init.Logic.iff in H)>>


let t_reduction_not_iff =
  Tacexpr.TacArg (valueIn (VTactic (dummy_loc,reduction_not_iff)))

let intuition_gen tac =
  interp (tacticIn (tauto_intuit t_reduction_not_iff tac))

let simplif_gen = interp (tacticIn simplif)

let tauto g =
  try intuition_gen (interp <:tactic<Fail>>) g
  with
    Refiner.FailError _ | UserError _ ->
      errorlabstrm "tauto" [< str "Tauto failed" >]

let default_intuition_tac = interp <:tactic< Auto with * >>

let q_elim tac=
  <:tactic<
  Match Context With 
  [x:?1;H:?1->?|-?]->
      Generalize (H x);Clear H;$tac>>

let rec lfo n gl=
  if n=0 then (tclFAIL 0 "LinearIntuition failed" gl) else
    let p=if n<0 then n else (n-1) in
    let lfo_rec=q_elim (Tacexpr.TacArg (valueIn (VTactic(dummy_loc,lfo p)))) in
      intuition_gen (interp lfo_rec) gl

let lfo_wrap n gl= 
  try lfo n gl
  with
    Refiner.FailError _ | UserError _ ->
      errorlabstrm "LinearIntuition" [< str "LinearIntuition failed." >]

TACTIC EXTEND Tauto
| [ "Tauto" ] -> [ tauto ]
END

TACTIC EXTEND TSimplif
| [ "Simplif" ] -> [ simplif_gen ]
END

TACTIC EXTEND Intuition
| [ "Intuition" ] -> [ intuition_gen default_intuition_tac ]
| [ "Intuition" tactic(t) ] -> [ intuition_gen (snd t) ]
END

TACTIC EXTEND LinearIntuition
| [ "LinearIntuition" ] -> [ lfo_wrap (-1)]
| [ "LinearIntuition" integer(n)] -> [ lfo_wrap n]
END
