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

let init_intros =
  (tclORELSE (tclTHEN (intros_until_n_wored 1)
                      (interp (tacticIn not_dep_intros))) intros)

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
      ($t_reduce;
       (Match Context With
        | [id: (?1 ? ?) |- ?] -> $t_is_conj;Elim id;Do 2 Intro;Clear id
        | [id: (?1 ? ?) |- ?] -> $t_is_disj;Elim id;Intro;Clear id
        | [id: (?1 ?2 ?3) -> ?4|- ?] ->
          $t_is_conj;Cut ?2-> ?3-> ?4;[Intro;Clear id|Intros;Apply id;
            Try Split;Assumption]
        | [id: (?1 ?2 ?3) -> ?4|- ?] ->
          $t_is_disj;Cut ?3-> ?4;[Cut ?2-> ?4;[Intros;Clear id|Intros;Apply id;
            Try Left;Assumption]|Intros;Apply id;Try Right;Assumption]
        | [id0: ?1-> ?2; id1: ?1|- ?] -> Generalize (id0 id1);Intro;Clear id0
        | [id: ?1 -> ?2|- ?] ->
          $t_is_unit;Cut ?2;[Intro;Clear id|Intros;Apply id;Constructor;Fail]
        | [|- (?1 ? ?)] -> $t_is_conj;Split);
       $t_not_dep_intros)>>

let rec tauto_main t_reduce ist =
  let t_axioms = tacticIn axioms
  and t_simplif = tacticIn (simplif t_reduce)
  and t_is_disj = tacticIn is_disj
  and t_tauto_main = tacticIn (tauto_main t_reduce) in
  <:tactic<
    $t_simplif;$t_axioms
    Orelse
      ($t_reduce;
      Match Context With
      | [id:(?1-> ?2)-> ?3|- ?] ->
        Cut ?2-> ?3;[Intro;Cut ?1-> ?2;[Intro;Cut ?3;[Intro;Clear id|
          Intros;Apply id;Assumption]|Clear id]|Intros;Apply id;Try Intro;
          Assumption];$t_tauto_main
      | [|- (?1 ? ?)] ->
        $t_is_disj;(Left;$t_tauto_main) Orelse (Right;$t_tauto_main))
    Orelse
      (Intro;$t_tauto_main)>>

let rec intuition_main t_reduce ist =
  let t_axioms = tacticIn axioms
  and t_simplif = tacticIn (simplif t_reduce)
  and t_intuition_main = tacticIn (intuition_main t_reduce) in
  <:tactic<
    $t_simplif;$t_axioms
    Orelse ($t_reduce; Try (Solve [Auto with *|Intro;$t_intuition_main]))>>

let unfold_not_iff = function
  | None -> interp <:tactic<Unfold not iff>>
  | Some id ->
    let ast_id = nvar id in
    interp <:tactic<Unfold not iff in $ast_id>>

let reduction_not_iff = Tacticals.onAllClauses (fun ido -> unfold_not_iff ido)

let red = function
  | None -> interp <:tactic<Repeat Red>>
  | Some id ->
    let ast_id = nvar id in
    interp <:tactic<Repeat (Red in $ast_id)>>

let reduction = Tacticals.onAllClauses red

(* Trick to coerce a tactic into an ast, since not provided in quotation *)
let _ = hide_atomic_tactic "OnAllClausesRepeatRed" reduction
let _ = hide_atomic_tactic "OnAllClausesUnfoldNotIff" reduction_not_iff

let t_reduction = ope ("OnAllClausesRepeatRed",[])
let t_reduction_not_iff = ope ("OnAllClausesUnfoldNotIff",[])

(* As a simple heuristic, first we try to avoid reduction both in tauto and
   intuition *)

let tauto g =
  try
    (tclTHEN init_intros
      (tclORELSE
        (interp (tacticIn (tauto_main t_reduction_not_iff)))
        (interp (tacticIn (tauto_main t_reduction))))) g
  with UserError _ -> errorlabstrm "tauto" [< str "Tauto failed" >]

let intuition =
  tclTHEN init_intros
    (tclORELSE
      (interp (tacticIn (intuition_main t_reduction_not_iff)))
      (interp (tacticIn (intuition_main t_reduction))))

let _ = hide_atomic_tactic "Tauto" tauto
let _ = hide_atomic_tactic "Intuition" intuition
