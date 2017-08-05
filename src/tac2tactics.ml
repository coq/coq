(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Globnames
open Misctypes
open Tactypes
open Genredexpr
open Tactics
open Proofview
open Tacmach.New
open Tacticals.New
open Proofview.Notations

(** FIXME: export a better interface in Tactics *)
let delayed_of_tactic tac env sigma =
  let _, pv = Proofview.init sigma [] in
  let c, pv, _, _ = Proofview.apply env tac pv in
  (sigma, c)

let apply adv ev cb cl =
  let map c = None, Loc.tag (delayed_of_tactic c) in
  let cb = List.map map cb in
  match cl with
  | None -> Tactics.apply_with_delayed_bindings_gen adv ev cb
  | Some (id, cl) -> Tactics.apply_delayed_in adv ev id cb cl

type induction_clause =
  EConstr.constr with_bindings tactic destruction_arg *
  intro_pattern_naming option *
  or_and_intro_pattern option *
  Locus.clause option

let map_destruction_arg = function
| ElimOnConstr c -> ElimOnConstr (delayed_of_tactic c)
| ElimOnIdent id -> ElimOnIdent id
| ElimOnAnonHyp n -> ElimOnAnonHyp n

let map_induction_clause ((clear, arg), eqn, as_, occ) =
  ((clear, map_destruction_arg arg), (eqn, as_), occ)

let induction_destruct isrec ev ic using =
  let ic = List.map map_induction_clause ic in
  Tactics.induction_destruct isrec ev (ic, using)

type rewriting =
  bool option *
  multi *
  EConstr.constr with_bindings tactic

let rewrite ev rw cl by =
  let map_rw (orient, repeat, c) =
    (Option.default true orient, repeat, None, delayed_of_tactic c)
  in
  let rw = List.map map_rw rw in
  let by = Option.map (fun tac -> Tacticals.New.tclCOMPLETE tac, Equality.Naive) by in
  Equality.general_multi_rewrite ev rw cl by

(** Ltac interface treats differently global references than other term
    arguments in reduction expressions. In Ltac1, this is done at parsing time.
    Instead, we parse indifferently any pattern and dispatch when the tactic is
    called. *)
let map_pattern_with_occs (pat, occ) = match pat with
| Pattern.PRef (ConstRef cst) -> (occ, Inl (EvalConstRef cst))
| Pattern.PRef (VarRef id) -> (occ, Inl (EvalVarRef id))
| _ -> (occ, Inr pat)

let simpl flags where cl =
  let where = Option.map map_pattern_with_occs where in
  Tactics.reduce (Simpl (flags, where)) cl

let vm where cl =
  let where = Option.map map_pattern_with_occs where in
  Tactics.reduce (CbvVm where) cl

let native where cl =
  let where = Option.map map_pattern_with_occs where in
  Tactics.reduce (CbvNative where) cl
