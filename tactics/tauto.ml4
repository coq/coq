(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(*i $Id$ i*)

open Term
open Hipattern
open Names
open Libnames
open Pp
open Proof_type
open Tacticals
open Tacinterp
open Tactics
open Util

let assoc_last ist =
  match List.assoc (Names.id_of_string "X1") ist.lfun with
    | VConstr c -> c
    | _ -> failwith "tauto: anomaly"

let is_empty ist =
  if is_empty_type (assoc_last ist) then
    <:tactic<idtac>>
  else
    <:tactic<fail>>

let is_unit ist =
  if is_unit_type (assoc_last ist) then
    <:tactic<idtac>>
  else
    <:tactic<fail>>

let is_record t =
  let (hdapp,args) = decompose_app t in
    match (kind_of_term hdapp) with
      | Ind ind  -> 
          let (mib,mip) = Global.lookup_inductive ind in
	    mib.Declarations.mind_record
      | _ -> false
    
let is_conj ist =
  let ind = assoc_last ist in
    if (is_conjunction ind) && (is_nodep_ind ind) && not (is_record ind) then
      <:tactic<idtac>>
    else
      <:tactic<fail>>

let is_disj ist =
  if is_disjunction (assoc_last ist) then
    <:tactic<idtac>>
  else
    <:tactic<fail>>

let not_dep_intros ist =
  <:tactic<
  repeat match goal with
  | |- (?X1 -> ?X2) => intro
  | |- (Coq.Init.Logic.iff _ _) => unfold Coq.Init.Logic.iff
  | |- (Coq.Init.Logic.not _)   => unfold Coq.Init.Logic.not
  | H:(Coq.Init.Logic.iff _ _)|- _ => unfold Coq.Init.Logic.iff in H
  | H:(Coq.Init.Logic.not _)|-_    => unfold Coq.Init.Logic.not in H
  | H:(Coq.Init.Logic.iff _ _)->_|- _ => unfold Coq.Init.Logic.iff in H
  | H:(Coq.Init.Logic.not _)->_|-_    => unfold Coq.Init.Logic.not in H
  end >>
				      
let axioms ist =
  let t_is_unit = tacticIn is_unit
  and t_is_empty = tacticIn is_empty in
    <:tactic<
    match reverse goal with
      | |- ?X1 => $t_is_unit; constructor 1
      | _:?X1 |- _ => $t_is_empty; elimtype X1; assumption
      | _:?X1 |- ?X1 => assumption
    end >>


let simplif ist =
  let t_is_unit = tacticIn is_unit
  and t_is_conj = tacticIn is_conj
  and t_is_disj = tacticIn is_disj
  and t_not_dep_intros = tacticIn not_dep_intros in
  <:tactic<
    $t_not_dep_intros;
    repeat
       (match reverse goal with
        | id: (?X1 _ _) |- _ =>
            $t_is_conj; elim id; do 2 intro; clear id
        | id: (?X1 _ _) |- _ => $t_is_disj; elim id; intro; clear id
        | id0: ?X1-> ?X2, id1: ?X1|- _ =>
	    (* generalize (id0 id1); intro; clear id0 does not work
	       (see Marco Maggiesi's bug PR#301)
	    so we instead use Assert and exact. *)
	    assert X2; [exact (id0 id1) | clear id0]
        | id: ?X1 -> ?X2|- _ =>
          $t_is_unit; cut X2;
	    [ intro; clear id
	    | (* id : ?X1 -> ?X2 |- ?X2 *)
	      cut X1; [exact id| constructor 1; fail]
	    ]
        | id: (?X1 ?X2 ?X3) -> ?X4|- _ =>
          $t_is_conj; cut (X2-> X3-> X4);
	    [ intro; clear id
	    | (* id: (?X1 ?X2 ?X3) -> ?X4 |- ?X2 -> ?X3 -> ?X4 *)
	      intro; intro; cut (X1 X2 X3); [exact id| split; assumption]
	    ]
        | id: (?X1 ?X2 ?X3) -> ?X4|- _ =>
          $t_is_disj;
	    cut (X3-> X4);
	      [cut (X2-> X4);
	        [intro; intro; clear id
		| (* id: (?X1 ?X2 ?X3) -> ?X4 |- ?X2 -> ?X4 *)
		  intro; cut (X1 X2 X3); [exact id| left; assumption]
		]
	      | (* id: (?X1 ?X2 ?X3) -> ?X4 |- ?X3 -> ?X4 *)
		intro; cut (X1 X2 X3); [exact id| right; assumption]
	      ]
        | |- (?X1 _ _) => $t_is_conj; split
        end;
        $t_not_dep_intros) >>

let rec tauto_intuit t_reduce solver ist =
  let t_axioms = tacticIn axioms
  and t_simplif = tacticIn simplif
  and t_is_disj = tacticIn is_disj
  and t_tauto_intuit = tacticIn (tauto_intuit t_reduce solver) in
  let t_solver = Tacexpr.TacArg (valueIn (VTactic (dummy_loc,solver))) in
  <:tactic<
   ($t_simplif;$t_axioms
   || match reverse goal with
      | id:(?X1-> ?X2)-> ?X3|- _ =>
	  cut X3;
	    [ intro; clear id; $t_tauto_intuit 
	    | cut (X1 -> X2);
		[ exact id
		| generalize (fun y:X2 => id (fun x:X1 => y)); intro; clear id;
		  solve [ $t_tauto_intuit ]]]
      | |- (?X1 _ _) =>
          $t_is_disj; solve [left;$t_tauto_intuit | right;$t_tauto_intuit]
      end
    ||
    (* NB: [|- _ -> _] matches any product *)
    match goal with | |- _ -> _ => intro; $t_tauto_intuit
    |  |- _  => $t_reduce;$t_solver
    end
    ||
    $t_solver
   ) >>
    
let reduction_not_iff=interp
 <:tactic<repeat 
  match goal with 
  | |- _     => progress unfold Coq.Init.Logic.not, Coq.Init.Logic.iff 
  | H:_ |- _ => progress unfold Coq.Init.Logic.not, Coq.Init.Logic.iff in H
  end >>


let t_reduction_not_iff =
  Tacexpr.TacArg (valueIn (VTactic (dummy_loc,reduction_not_iff)))

let intuition_gen tac =
  interp (tacticIn (tauto_intuit t_reduction_not_iff tac))

let simplif_gen = interp (tacticIn simplif)

let tauto g =
  try intuition_gen (interp <:tactic<fail>>) g
  with
    Refiner.FailError _ | UserError _ ->
      errorlabstrm "tauto" (str "tauto failed.")

let default_intuition_tac = interp <:tactic< auto with * >>

TACTIC EXTEND tauto
| [ "tauto" ] -> [ tauto ]
END

TACTIC EXTEND intuition
| [ "intuition" ] -> [ intuition_gen default_intuition_tac ]
| [ "intuition" tactic(t) ] -> [ intuition_gen (snd t) ]
END
