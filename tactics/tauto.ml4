(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma kernel/names.cmo parsing/ast.cmo parsing/g_tactic.cmo parsing/g_ltac.cmo parsing/g_constr.cmo" i*)

(*i $Id$ i*)

open Ast
open Coqast
open Hipattern
open Names
open Pp
open Proof_type
open Tacmach
open Tacinterp
open Tactics
open Util

let is_empty ist =
  if (is_empty_type (List.assoc 1 ist.lmatch)) then
    <:tactic<ElimType ?1;Assumption>>
  else
    failwith "is_empty"

let is_unit ist =
  if (is_unit_type (List.assoc 1 ist.lmatch)) then
    <:tactic<Idtac>>
  else
    failwith "is_unit"

let is_conj ist =
  if (is_conjunction (List.assoc 1 ist.lmatch)) then
     <:tactic<Idtac>>
  else
    failwith "is_conj"

let is_disj ist =
  if (is_disjunction (List.assoc 1 ist.lmatch)) then
     <:tactic<Idtac>>
  else
    failwith "is_disj"

let not_dep_intros ist =
  <:tactic<
    Repeat
      Match Context With
      | [|- ?1 -> ?2 ] -> Intro>>

let axioms ist =
  let t_is_unit = tacticIn is_unit
  and t_is_empty = tacticIn is_empty in
  <:tactic<
    Match Context With
    |[|- ?1] -> $t_is_unit;Constructor
    |[_:?1 |- ?] -> $t_is_empty
    |[_:?1 |- ?1] -> Assumption>>

let simplif t_reduce ist =
  let t_is_unit = tacticIn is_unit
  and t_is_conj = tacticIn is_conj
  and t_is_disj = tacticIn is_disj
  and t_not_dep_intros = tacticIn not_dep_intros in
  <:tactic<
    $t_not_dep_intros;
    Repeat
      ((Match Context With
        | [id: (?1 ? ?) |- ?] ->
            $t_is_conj;Elim id;Do 2 Intro;Clear id;$t_reduce
        | [id: (?1 ? ?) |- ?] -> $t_is_disj;Elim id;Intro;Clear id;$t_reduce
        | [id0: ?1-> ?2; id1: ?1|- ?] -> Generalize (id0 id1);Intro;Clear id0
        | [id: ?1 -> ?2|- ?] ->
          $t_is_unit;Cut ?2;[Intro;Clear id|Intros;Apply id;Constructor;Fail]
        | [id: (?1 ?2 ?3) -> ?4|- ?] ->
          $t_is_conj;Cut ?2-> ?3-> ?4;[Intro;Clear id;$t_reduce|
            Intros;Apply id;Try Split;Assumption]
        | [id: (?1 ?2 ?3) -> ?4|- ?] ->
          $t_is_disj;Cut ?3-> ?4;[Cut ?2-> ?4;[Intros;Clear id;$t_reduce|
            Intros;Apply id;
            Try Left;Assumption]|Intros;Apply id;Try Right;Assumption]
        | [|- (?1 ? ?)] -> $t_is_conj;Split;$t_reduce);
       $t_not_dep_intros)>>

let rec tauto_intuit t_reduce t_solver ist =
  let t_axioms = tacticIn axioms
  and t_simplif = tacticIn (simplif t_reduce)
  and t_is_disj = tacticIn is_disj
  and t_tauto_intuit = tacticIn (tauto_intuit t_reduce t_solver) in
  <:tactic<
   $t_reduce;
   ($t_simplif;$t_axioms
    Orelse
      (Match Context With
      | [id:(?1-> ?2)-> ?3|- ?] ->
        Cut ?2-> ?3;[Intro;Cut ?1-> ?2;[Intro;Cut ?3;[Intro;Clear id|
          Intros;Apply id;Assumption]|Clear id]|Intros;Apply id;Try Intro;
          Assumption]; Solve [ $t_tauto_intuit ]
      | [|- (?1 ? ?)] ->
        $t_is_disj;Solve [Left;$t_tauto_intuit | Right;$t_tauto_intuit]
      )
    Orelse
      (* NB: [|- ? -> ?] matches any product *)
      (Match Context With |[ |- ? -> ? ] -> Intro;$t_tauto_intuit)
    Orelse
      $t_solver
   ) >>

let tauto_main t_reduce ist =
  tauto_intuit t_reduce <:tactic< Failtac >> ist

let unfold_not_iff = function
  | None -> interp <:tactic<Unfold not iff>>
  | Some id ->
    let ast_id = nvar id in
    interp <:tactic<Unfold not iff in $ast_id>>

let reduction_not_iff = Tacticals.onAllClauses (fun ido -> unfold_not_iff ido)

let t_reduction_not_iff = valueIn (VTactic reduction_not_iff)

let tauto g =
  try
        (interp (tacticIn (tauto_main t_reduction_not_iff)))
    g
  with UserError _ -> errorlabstrm "tauto" [< str "Tauto failed" >]

let intuition_gen tac =
  interp (tacticIn (tauto_intuit t_reduction_not_iff tac))

let intuition args =
  match args with
    | [] -> intuition_gen <:tactic< Auto with * >>
    | [ Tac(_, t)] -> intuition_gen t
    | _ -> assert false

let _ = hide_atomic_tactic "Tauto" tauto
let _ = hide_tactic "Intuition" intuition

