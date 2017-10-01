(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Globnames
open Genredexpr
open Tac2expr
open Tac2ffi
open Tac2types
open Tac2tactics
open Proofview.Notations

module Value = Tac2ffi

let return x = Proofview.tclUNIT x
let v_unit = Value.of_unit ()
let thaw f = Tac2ffi.apply (Value.to_closure f) [v_unit]

let to_pair f g v = match Value.to_tuple v with
| [| x; y |] -> (f x, g y)
| _ -> assert false

let to_name c = match Value.to_option Value.to_ident c with
| None -> Anonymous
| Some id -> Name id

let to_qhyp v = match Value.to_block v with
| (0, [| i |]) -> AnonHyp (Value.to_int i)
| (1, [| id |]) -> NamedHyp (Value.to_ident id)
| _ -> assert false

let to_bindings = function
| ValInt 0 -> NoBindings
| ValBlk (0, [| vl |]) ->
  ImplicitBindings (Value.to_list Value.to_constr vl)
| ValBlk (1, [| vl |]) ->
  ExplicitBindings ((Value.to_list (fun p -> to_pair to_qhyp Value.to_constr p) vl))
| _ -> assert false

let to_constr_with_bindings v = match Value.to_tuple v with
| [| c; bnd |] -> (Value.to_constr c, to_bindings bnd)
| _ -> assert false

let to_occurrences = function
| ValInt 0 -> AllOccurrences
| ValBlk (0, [| vl |]) -> AllOccurrencesBut (Value.to_list Value.to_int vl)
| ValInt 1 -> NoOccurrences
| ValBlk (1, [| vl |]) -> OnlyOccurrences (Value.to_list Value.to_int vl)
| _ -> assert false

let to_hyp_location_flag v = match Value.to_int v with
| 0 -> InHyp
| 1 -> InHypTypeOnly
| 2 -> InHypValueOnly
| _ -> assert false

let to_clause v = match Value.to_tuple v with
| [| hyps; concl |] ->
  let cast v = match Value.to_tuple v with
  | [| hyp; occ; flag |] ->
    (Value.to_ident hyp, to_occurrences occ, to_hyp_location_flag flag)
  | _ -> assert false
  in
  let hyps = Value.to_option (fun h -> Value.to_list cast h) hyps in
  { onhyps = hyps; concl_occs = to_occurrences concl; }
| _ -> assert false

let to_red_flag v = match Value.to_tuple v with
| [| beta; iota; fix; cofix; zeta; delta; const |] ->
  {
    rBeta = Value.to_bool beta;
    rMatch = Value.to_bool iota;
    rFix = Value.to_bool fix;
    rCofix = Value.to_bool cofix;
    rZeta = Value.to_bool zeta;
    rDelta = Value.to_bool delta;
    rConst = Value.to_list Value.to_reference const;
  }
| _ -> assert false

let to_pattern_with_occs pat =
  to_pair Value.to_pattern to_occurrences pat

let to_constr_with_occs c =
  to_pair Value.to_constr to_occurrences c

let rec to_intro_pattern v = match Value.to_block v with
| (0, [| b |]) -> IntroForthcoming (Value.to_bool b)
| (1, [| pat |]) -> IntroNaming (to_intro_pattern_naming pat)
| (2, [| act |]) -> IntroAction (to_intro_pattern_action act)
| _ -> assert false

and to_intro_pattern_naming = function
| ValBlk (0, [| id |]) -> IntroIdentifier (Value.to_ident id)
| ValBlk (1, [| id |]) -> IntroFresh (Value.to_ident id)
| ValInt 0 -> IntroAnonymous
| _ -> assert false

and to_intro_pattern_action = function
| ValInt 0 -> IntroWildcard
| ValBlk (0, [| op |]) -> IntroOrAndPattern (to_or_and_intro_pattern op)
| ValBlk (1, [| inj |]) ->
  let map ipat = to_intro_pattern ipat in
  IntroInjection (Value.to_list map inj)
| ValBlk (2, [| c; ipat |]) ->
  let c = Value.to_fun1 Value.unit Value.constr c in
  IntroApplyOn (c, to_intro_pattern ipat)
| ValBlk (3, [| b |]) -> IntroRewrite (Value.to_bool b)
| _ -> assert false

and to_or_and_intro_pattern v = match Value.to_block v with
| (0, [| ill |]) ->
  IntroOrPattern (Value.to_list to_intro_patterns ill)
| (1, [| il |]) ->
  IntroAndPattern (to_intro_patterns il)
| _ -> assert false

and to_intro_patterns il =
  Value.to_list to_intro_pattern il

let to_destruction_arg v = match Value.to_block v with
| (0, [| c |]) ->
  let c = thaw c >>= fun c -> return (to_constr_with_bindings c) in
  ElimOnConstr c
| (1, [| id |]) -> ElimOnIdent (Value.to_ident id)
| (2, [| n |]) -> ElimOnAnonHyp (Value.to_int n)
| _ -> assert false

let to_induction_clause v = match Value.to_tuple v with
| [| arg; eqn; as_; in_ |] ->
  let arg = to_destruction_arg arg in
  let eqn = Value.to_option to_intro_pattern_naming eqn in
  let as_ = Value.to_option to_or_and_intro_pattern as_ in
  let in_ = Value.to_option to_clause in_ in
  (arg, eqn, as_, in_)
| _ ->
  assert false

let to_assertion v = match Value.to_block v with
| (0, [| ipat; t; tac |]) ->
  let to_tac t = Value.to_fun1 Value.unit Value.unit t in
  let ipat = Value.to_option to_intro_pattern ipat in
  let t = Value.to_constr t in
  let tac = Value.to_option to_tac tac in
  AssertType (ipat, t, tac)
| (1, [| id; c |]) ->
  AssertValue (Value.to_ident id, Value.to_constr c)
| _ -> assert false

let to_multi = function
| ValBlk (0, [| n |]) -> Precisely (Value.to_int n)
| ValBlk (1, [| n |]) -> UpTo (Value.to_int n)
| ValInt 0 -> RepeatStar
| ValInt 1 -> RepeatPlus
| _ -> assert false

let to_rewriting v = match Value.to_tuple v with
| [| orient; repeat; c |] ->
  let orient = Value.to_option Value.to_bool orient in
  let repeat = to_multi repeat in
  let c = thaw c >>= fun c -> return (to_constr_with_bindings c) in
  (orient, repeat, c)
| _ -> assert false

let to_debug v = match Value.to_int v with
| 0 -> Hints.Off
| 1 -> Hints.Info
| 2 -> Hints.Debug
| _ -> assert false

let to_strategy v = match Value.to_int v with
| 0 -> Class_tactics.Bfs
| 1 -> Class_tactics.Dfs
| _ -> assert false

let to_inversion_kind v = match Value.to_int v with
| 0 -> Misctypes.SimpleInversion
| 1 -> Misctypes.FullInversion
| 2 -> Misctypes.FullInversionClear
| _ -> assert false

let to_move_location = function
| ValInt 0 -> Misctypes.MoveFirst
| ValInt 1 -> Misctypes.MoveLast
| ValBlk (0, [|id|]) -> Misctypes.MoveAfter (Value.to_ident id)
| ValBlk (1, [|id|]) -> Misctypes.MoveBefore (Value.to_ident id)
| _ -> assert false

(** Standard tactics sharing their implementation with Ltac1 *)

let pname s = { mltac_plugin = "ltac2"; mltac_tactic = s }

let lift tac = tac <*> return v_unit

let define_prim0 name tac =
  let tac _ = lift tac in
  Tac2env.define_primitive (pname name) (mk_closure arity_one tac)

let define_prim1 name tac =
  let tac x = lift (tac x) in
  Tac2env.define_primitive (pname name) (mk_closure arity_one tac)

let define_prim2 name tac =
  let tac x y = lift (tac x y) in
  Tac2env.define_primitive (pname name) (mk_closure (arity_suc arity_one) tac)

let define_prim3 name tac =
  let tac x y z = lift (tac x y z) in
  Tac2env.define_primitive (pname name) (mk_closure (arity_suc (arity_suc arity_one)) tac)

let define_prim4 name tac =
  let tac x y z u = lift (tac x y z u) in
  Tac2env.define_primitive (pname name) (mk_closure (arity_suc (arity_suc (arity_suc arity_one))) tac)

let define_prim5 name tac =
  let tac x y z u v = lift (tac x y z u v) in
  Tac2env.define_primitive (pname name) (mk_closure (arity_suc (arity_suc (arity_suc (arity_suc arity_one)))) tac)

(** Tactics from Tacexpr *)

let () = define_prim2 "tac_intros" begin fun ev ipat ->
  let ev = Value.to_bool ev in
  let ipat = to_intro_patterns ipat in
  Tac2tactics.intros_patterns ev ipat
end

let () = define_prim4 "tac_apply" begin fun adv ev cb ipat ->
  let adv = Value.to_bool adv in
  let ev = Value.to_bool ev in
  let map_cb c = thaw c >>= fun c -> return (to_constr_with_bindings c) in
  let cb = Value.to_list map_cb cb in
  let map p = Value.to_option to_intro_pattern p in
  let map_ipat p = to_pair Value.to_ident map p in
  let ipat = Value.to_option map_ipat ipat in
  Tac2tactics.apply adv ev cb ipat
end

let () = define_prim3 "tac_elim" begin fun ev c copt ->
  let ev = Value.to_bool ev in
  let c = to_constr_with_bindings c in
  let copt = Value.to_option to_constr_with_bindings copt in
  Tac2tactics.elim ev c copt
end

let () = define_prim2 "tac_case" begin fun ev c ->
  let ev = Value.to_bool ev in
  let c = to_constr_with_bindings c in
  Tac2tactics.general_case_analysis ev c
end

let () = define_prim1 "tac_generalize" begin fun cl ->
  let cast v = match Value.to_tuple v with
  | [| c; occs; na |] ->
    (Value.to_constr c, to_occurrences occs, to_name na)
  | _ -> assert false
  in
  let cl = Value.to_list cast cl in
  Tac2tactics.generalize cl
end

let () = define_prim1 "tac_assert" begin fun ast ->
  let ast = to_assertion ast in
  Tac2tactics.assert_ ast
end

let () = define_prim3 "tac_enough" begin fun c tac ipat ->
  let c = Value.to_constr c in
  let of_tac t = Proofview.tclIGNORE (thaw t) in
  let tac = Value.to_option (fun t -> Value.to_option of_tac t) tac in
  let ipat = Value.to_option to_intro_pattern ipat in
  Tac2tactics.forward false tac ipat c
end

let () = define_prim2 "tac_pose" begin fun idopt c ->
  let na = to_name idopt in
  let c = Value.to_constr c in
  Tactics.letin_tac None na c None Locusops.nowhere
end

let () = define_prim3 "tac_set" begin fun ev p cl ->
  let ev = Value.to_bool ev in
  let cl = to_clause cl in
  Proofview.tclEVARMAP >>= fun sigma ->
  thaw p >>= fun p ->
  let (na, c) = to_pair to_name Value.to_constr p in
  Tac2tactics.letin_pat_tac ev None na (sigma, c) cl
end

let () = define_prim5 "tac_remember" begin fun ev na c eqpat cl ->
  let ev = Value.to_bool ev in
  let na = to_name na in
  let cl = to_clause cl in
  let eqpat = Value.to_option to_intro_pattern eqpat in
  let eqpat = Option.default (IntroNaming IntroAnonymous) eqpat in
  match eqpat with
  | IntroNaming eqpat ->
    Proofview.tclEVARMAP >>= fun sigma ->
    thaw c >>= fun c ->
    let c = Value.to_constr c in
    Tac2tactics.letin_pat_tac ev (Some (true, eqpat)) na (sigma, c) cl
  | _ ->
    Tacticals.New.tclZEROMSG (Pp.str "Invalid pattern for remember")
end

let () = define_prim3 "tac_destruct" begin fun ev ic using ->
  let ev = Value.to_bool ev in
  let ic = Value.to_list to_induction_clause ic in
  let using = Value.to_option to_constr_with_bindings using in
  Tac2tactics.induction_destruct false ev ic using
end

let () = define_prim3 "tac_induction" begin fun ev ic using ->
  let ev = Value.to_bool ev in
  let ic = Value.to_list to_induction_clause ic in
  let using = Value.to_option to_constr_with_bindings using in
  Tac2tactics.induction_destruct true ev ic using
end

let () = define_prim1 "tac_red" begin fun cl ->
  let cl = to_clause cl in
  Tac2tactics.reduce (Red false) cl
end

let () = define_prim1 "tac_hnf" begin fun cl ->
  let cl = to_clause cl in
  Tac2tactics.reduce Hnf cl
end

let () = define_prim3 "tac_simpl" begin fun flags where cl ->
  let flags = to_red_flag flags in
  let where = Value.to_option to_pattern_with_occs where in
  let cl = to_clause cl in
  Tac2tactics.simpl flags where cl
end

let () = define_prim2 "tac_cbv" begin fun flags cl ->
  let flags = to_red_flag flags in
  let cl = to_clause cl in
  Tac2tactics.cbv flags cl
end

let () = define_prim2 "tac_cbn" begin fun flags cl ->
  let flags = to_red_flag flags in
  let cl = to_clause cl in
  Tac2tactics.cbn flags cl
end

let () = define_prim2 "tac_lazy" begin fun flags cl ->
  let flags = to_red_flag flags in
  let cl = to_clause cl in
  Tac2tactics.lazy_ flags cl
end

let () = define_prim2 "tac_unfold" begin fun refs cl ->
  let map v = to_pair Value.to_reference to_occurrences v in
  let refs = Value.to_list map refs in
  let cl = to_clause cl in
  Tac2tactics.unfold refs cl
end

let () = define_prim2 "tac_fold" begin fun args cl ->
  let args = Value.to_list Value.to_constr args in
  let cl = to_clause cl in
  Tac2tactics.reduce (Fold args) cl
end

let () = define_prim2 "tac_pattern" begin fun where cl ->
  let where = Value.to_list to_constr_with_occs where in
  let cl = to_clause cl in
  Tac2tactics.pattern where cl
end

let () = define_prim2 "tac_vm" begin fun where cl ->
  let where = Value.to_option to_pattern_with_occs where in
  let cl = to_clause cl in
  Tac2tactics.vm where cl
end

let () = define_prim2 "tac_native" begin fun where cl ->
  let where = Value.to_option to_pattern_with_occs where in
  let cl = to_clause cl in
  Tac2tactics.native where cl
end

(** Reduction functions *)

let lift tac = tac >>= fun c -> Proofview.tclUNIT (Value.of_constr c)

let define_red1 name tac =
  let tac x = lift (tac x) in
  Tac2env.define_primitive (pname name) (mk_closure arity_one tac)

let define_red2 name tac =
  let tac x y = lift (tac x y) in
  Tac2env.define_primitive (pname name) (mk_closure (arity_suc arity_one) tac)

let define_red3 name tac =
  let tac x y z = lift (tac x y z) in
  Tac2env.define_primitive (pname name) (mk_closure (arity_suc (arity_suc arity_one)) tac)

let () = define_red1 "eval_red" begin fun c ->
  let c = Value.to_constr c in
  Tac2tactics.eval_red c
end

let () = define_red1 "eval_hnf" begin fun c ->
  let c = Value.to_constr c in
  Tac2tactics.eval_hnf c
end

let () = define_red3 "eval_simpl" begin fun flags where c ->
  let flags = to_red_flag flags in
  let where = Value.to_option to_pattern_with_occs where in
  let c = Value.to_constr c in
  Tac2tactics.eval_simpl flags where c
end

let () = define_red2 "eval_cbv" begin fun flags c ->
  let flags = to_red_flag flags in
  let c = Value.to_constr c in
  Tac2tactics.eval_cbv flags c
end

let () = define_red2 "eval_cbn" begin fun flags c ->
  let flags = to_red_flag flags in
  let c = Value.to_constr c in
  Tac2tactics.eval_cbn flags c
end

let () = define_red2 "eval_lazy" begin fun flags c ->
  let flags = to_red_flag flags in
  let c = Value.to_constr c in
  Tac2tactics.eval_lazy flags c
end

let () = define_red2 "eval_unfold" begin fun refs c ->
  let map v = to_pair Value.to_reference to_occurrences v in
  let refs = Value.to_list map refs in
  let c = Value.to_constr c in
  Tac2tactics.eval_unfold refs c
end

let () = define_red2 "eval_fold" begin fun args c ->
  let args = Value.to_list Value.to_constr args in
  let c = Value.to_constr c in
  Tac2tactics.eval_fold args c
end

let () = define_red2 "eval_pattern" begin fun where c ->
  let where = Value.to_list (fun p -> to_pair Value.to_constr to_occurrences p) where in
  let c = Value.to_constr c in
  Tac2tactics.eval_pattern where c
end

let () = define_red2 "eval_vm" begin fun where c ->
  let where = Value.to_option to_pattern_with_occs where in
  let c = Value.to_constr c in
  Tac2tactics.eval_vm where c
end

let () = define_red2 "eval_native" begin fun where c ->
  let where = Value.to_option to_pattern_with_occs where in
  let c = Value.to_constr c in
  Tac2tactics.eval_native where c
end

let () = define_prim4 "tac_rewrite" begin fun ev rw cl by ->
  let ev = Value.to_bool ev in
  let rw = Value.to_list to_rewriting rw in
  let cl = to_clause cl in
  let to_tac t = Proofview.tclIGNORE (thaw t) in
  let by = Value.to_option to_tac by in
  Tac2tactics.rewrite ev rw cl by
end

let () = define_prim4 "tac_inversion" begin fun knd arg pat ids ->
  let knd = to_inversion_kind knd in
  let arg = to_destruction_arg arg in
  let pat = Value.to_option to_intro_pattern pat in
  let ids = Value.to_option (fun l -> Value.to_list Value.to_ident l) ids in
  Tac2tactics.inversion knd arg pat ids
end

(** Tactics from coretactics *)

let () = define_prim0 "tac_reflexivity" Tactics.intros_reflexivity

let () = define_prim2 "tac_move" begin fun id mv ->
  let id = Value.to_ident id in
  let mv = to_move_location mv in
  Tactics.move_hyp id mv
end

let () = define_prim2 "tac_intro" begin fun id mv ->
  let id = Value.to_option Value.to_ident id in
  let mv = Value.to_option to_move_location mv in
  let mv = Option.default Misctypes.MoveLast mv in
  Tactics.intro_move id mv
end

(*

TACTIC EXTEND exact
  [ "exact" casted_constr(c) ] -> [ Tactics.exact_no_check c ]
END

*)

let () = define_prim0 "tac_assumption" Tactics.assumption

let () = define_prim1 "tac_transitivity" begin fun c ->
  let c = Value.to_constr c in
  Tactics.intros_transitivity (Some c)
end

let () = define_prim0 "tac_etransitivity" (Tactics.intros_transitivity None)

let () = define_prim1 "tac_cut" begin fun c ->
  let c = Value.to_constr c in
  Tactics.cut c
end

let () = define_prim2 "tac_left" begin fun ev bnd ->
  let ev = Value.to_bool ev in
  let bnd = to_bindings bnd in
  Tac2tactics.left_with_bindings ev bnd
end
let () = define_prim2 "tac_right" begin fun ev bnd ->
  let ev = Value.to_bool ev in
  let bnd = to_bindings bnd in
  Tac2tactics.right_with_bindings ev bnd
end

let () = define_prim1 "tac_introsuntil" begin fun h ->
  Tactics.intros_until (to_qhyp h)
end

let () = define_prim1 "tac_exactnocheck" begin fun c ->
  Tactics.exact_no_check (Value.to_constr c)
end

let () = define_prim1 "tac_vmcastnocheck" begin fun c ->
  Tactics.vm_cast_no_check (Value.to_constr c)
end

let () = define_prim1 "tac_nativecastnocheck" begin fun c ->
  Tactics.native_cast_no_check (Value.to_constr c)
end

let () = define_prim1 "tac_constructor" begin fun ev ->
  let ev = Value.to_bool ev in
  Tactics.any_constructor ev None
end

let () = define_prim3 "tac_constructorn" begin fun ev n bnd ->
  let ev = Value.to_bool ev in
  let n = Value.to_int n in
  let bnd = to_bindings bnd in
  Tac2tactics.constructor_tac ev None n bnd
end

let () = define_prim1 "tac_symmetry" begin fun cl ->
  let cl = to_clause cl in
  Tac2tactics.symmetry cl
end

let () = define_prim2 "tac_split" begin fun ev bnd ->
  let ev = Value.to_bool ev in
  let bnd = to_bindings bnd in
  Tac2tactics.split_with_bindings ev bnd
end

let () = define_prim1 "tac_rename" begin fun ids ->
  let map c = match Value.to_tuple c with
  | [|x; y|] -> (Value.to_ident x, Value.to_ident y)
  | _ -> assert false
  in
  let ids = Value.to_list map ids in
  Tactics.rename_hyp ids
end

let () = define_prim1 "tac_revert" begin fun ids ->
  let ids = Value.to_list Value.to_ident ids in
  Tactics.revert ids
end

let () = define_prim0 "tac_admit" Proofview.give_up

let () = define_prim2 "tac_fix" begin fun idopt n ->
  let idopt = Value.to_option Value.to_ident idopt in
  let n = Value.to_int n in
  Tactics.fix idopt n
end

let () = define_prim1 "tac_cofix" begin fun idopt ->
  let idopt = Value.to_option Value.to_ident idopt in
  Tactics.cofix idopt
end

let () = define_prim1 "tac_clear" begin fun ids ->
  let ids = Value.to_list Value.to_ident ids in
  Tactics.clear ids
end

let () = define_prim1 "tac_keep" begin fun ids ->
  let ids = Value.to_list Value.to_ident ids in
  Tactics.keep ids
end

let () = define_prim1 "tac_clearbody" begin fun ids ->
  let ids = Value.to_list Value.to_ident ids in
  Tactics.clear_body ids
end

(** Tactics from extratactics *)

let () = define_prim2 "tac_discriminate" begin fun ev arg ->
  let ev = Value.to_bool ev in
  let arg = Value.to_option to_destruction_arg arg in
  Tac2tactics.discriminate ev arg
end

let () = define_prim3 "tac_injection" begin fun ev ipat arg ->
  let ev = Value.to_bool ev in
  let ipat = Value.to_option to_intro_patterns ipat in
  let arg = Value.to_option to_destruction_arg arg in
  Tac2tactics.injection ev ipat arg
end

let () = define_prim1 "tac_absurd" begin fun c ->
  Contradiction.absurd (Value.to_constr c)
end

let () = define_prim1 "tac_contradiction" begin fun c ->
  let c = Value.to_option to_constr_with_bindings c in
  Tac2tactics.contradiction c
end

let () = define_prim4 "tac_autorewrite" begin fun all by ids cl ->
  let all = Value.to_bool all in
  let by = Value.to_option (fun tac -> Proofview.tclIGNORE (thaw tac)) by in
  let ids = Value.to_list Value.to_ident ids in
  let cl = to_clause cl in
  Tac2tactics.autorewrite ~all by ids cl
end

let () = define_prim1 "tac_subst" begin fun ids ->
  let ids = Value.to_list Value.to_ident ids in
  Equality.subst ids
end

let () = define_prim0 "tac_substall" (return () >>= fun () -> Equality.subst_all ())

(** Auto *)

let () = define_prim3 "tac_trivial" begin fun dbg lems dbs ->
  let dbg = to_debug dbg in
  let map c = thaw c >>= fun c -> return (Value.to_constr c) in
  let lems = Value.to_list map lems in
  let dbs = Value.to_option (fun l -> Value.to_list Value.to_ident l) dbs in
  Tac2tactics.trivial dbg lems dbs
end

let () = define_prim5 "tac_eauto" begin fun dbg n p lems dbs ->
  let dbg = to_debug dbg in
  let n = Value.to_option Value.to_int n in
  let p = Value.to_option Value.to_int p in
  let map c = thaw c >>= fun c -> return (Value.to_constr c) in
  let lems = Value.to_list map lems in
  let dbs = Value.to_option (fun l -> Value.to_list Value.to_ident l) dbs in
  Tac2tactics.eauto dbg n p lems dbs
end

let () = define_prim4 "tac_auto" begin fun dbg n lems dbs ->
  let dbg = to_debug dbg in
  let n = Value.to_option Value.to_int n in
  let map c = thaw c >>= fun c -> return (Value.to_constr c) in
  let lems = Value.to_list map lems in
  let dbs = Value.to_option (fun l -> Value.to_list Value.to_ident l) dbs in
  Tac2tactics.auto dbg n lems dbs
end

let () = define_prim4 "tac_newauto" begin fun dbg n lems dbs ->
  let dbg = to_debug dbg in
  let n = Value.to_option Value.to_int n in
  let map c = thaw c >>= fun c -> return (Value.to_constr c) in
  let lems = Value.to_list map lems in
  let dbs = Value.to_option (fun l -> Value.to_list Value.to_ident l) dbs in
  Tac2tactics.new_auto dbg n lems dbs
end

let () = define_prim3 "tac_typeclasses_eauto" begin fun str n dbs ->
  let str = Value.to_option to_strategy str in
  let n = Value.to_option Value.to_int n in
  let dbs = Value.to_option (fun l -> Value.to_list Value.to_ident l) dbs in
  Tac2tactics.typeclasses_eauto str n dbs
end

(** Firstorder *)

let () = define_prim3 "tac_firstorder" begin fun tac refs ids ->
  let tac = Value.to_option (fun t -> Proofview.tclIGNORE (thaw t)) tac in
  let refs = Value.to_list Value.to_reference refs in
  let ids = Value.to_list Value.to_ident ids in
  Tac2tactics.firstorder tac refs ids
end
