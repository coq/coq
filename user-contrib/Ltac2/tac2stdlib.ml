(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Genredexpr
open Tac2expr
open Tac2ffi
open Tac2types
open Tac2extffi
open Proofview.Notations

module Value = Tac2ffi

(** Make a representation with a dummy from function *)
let make_to_repr f = Tac2ffi.make_repr (fun _ -> assert false) f

let return x = Proofview.tclUNIT x
let v_unit = Value.of_unit ()
let thaw r f = Tac2ffi.app_fun1 f unit r ()
let uthaw r f = Tac2ffi.app_fun1 (to_fun1 unit r f) unit r ()
let thunk r = fun1 unit r

let to_name c = match Value.to_option Value.to_ident c with
| None -> Anonymous
| Some id -> Name id

let name = make_to_repr to_name

let to_occurrences = function
| ValInt 0 -> AllOccurrences
| ValBlk (0, [| vl |]) -> AllOccurrencesBut (Value.to_list Value.to_int vl)
| ValInt 1 -> NoOccurrences
| ValBlk (1, [| vl |]) -> OnlyOccurrences (Value.to_list Value.to_int vl)
| _ -> assert false

let occurrences = make_to_repr to_occurrences

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

let clause = make_to_repr to_clause

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

let red_flags = make_to_repr to_red_flag

let pattern_with_occs = pair pattern occurrences

let constr_with_occs = pair constr occurrences

let reference_with_occs = pair reference occurrences

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

let intro_pattern = make_to_repr to_intro_pattern

let intro_patterns = make_to_repr to_intro_patterns

let to_destruction_arg v = match Value.to_block v with
| (0, [| c |]) ->
  let c = uthaw constr_with_bindings c in
  ElimOnConstr c
| (1, [| id |]) -> ElimOnIdent (Value.to_ident id)
| (2, [| n |]) -> ElimOnAnonHyp (Value.to_int n)
| _ -> assert false

let destruction_arg = make_to_repr to_destruction_arg

let to_induction_clause v = match Value.to_tuple v with
| [| arg; eqn; as_; in_ |] ->
  let arg = to_destruction_arg arg in
  let eqn = Value.to_option to_intro_pattern_naming eqn in
  let as_ = Value.to_option to_or_and_intro_pattern as_ in
  let in_ = Value.to_option to_clause in_ in
  (arg, eqn, as_, in_)
| _ ->
  assert false

let induction_clause = make_to_repr to_induction_clause

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

let assertion = make_to_repr to_assertion

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
  let c = uthaw constr_with_bindings c in
  (orient, repeat, c)
| _ -> assert false

let rewriting = make_to_repr to_rewriting

let to_debug v = match Value.to_int v with
| 0 -> Hints.Off
| 1 -> Hints.Info
| 2 -> Hints.Debug
| _ -> assert false

let debug = make_to_repr to_debug

let to_strategy v = match Value.to_int v with
| 0 -> Class_tactics.Bfs
| 1 -> Class_tactics.Dfs
| _ -> assert false

let strategy = make_to_repr to_strategy

let to_inversion_kind v = match Value.to_int v with
| 0 -> Inv.SimpleInversion
| 1 -> Inv.FullInversion
| 2 -> Inv.FullInversionClear
| _ -> assert false

let inversion_kind = make_to_repr to_inversion_kind

let to_move_location = function
| ValInt 0 -> Logic.MoveFirst
| ValInt 1 -> Logic.MoveLast
| ValBlk (0, [|id|]) -> Logic.MoveAfter (Value.to_ident id)
| ValBlk (1, [|id|]) -> Logic.MoveBefore (Value.to_ident id)
| _ -> assert false

let move_location = make_to_repr to_move_location

let to_generalize_arg v = match Value.to_tuple v with
| [| c; occs; na |] ->
  (Value.to_constr c, to_occurrences occs, to_name na)
| _ -> assert false

let generalize_arg = make_to_repr to_generalize_arg

(** Standard tactics sharing their implementation with Ltac1 *)

let pname s = { mltac_plugin = "ltac2"; mltac_tactic = s }

let lift tac = tac <*> return v_unit

let define_prim0 name tac =
  let tac _ = lift tac in
  Tac2env.define_primitive (pname name) (mk_closure arity_one tac)

let define_prim1 name r0 f =
  let tac x = lift (f (Value.repr_to r0 x)) in
  Tac2env.define_primitive (pname name) (mk_closure arity_one tac)

let define_prim2 name r0 r1 f =
  let tac x y = lift (f (Value.repr_to r0 x) (Value.repr_to r1 y)) in
  Tac2env.define_primitive (pname name) (mk_closure (arity_suc arity_one) tac)

let define_prim3 name r0 r1 r2 f =
  let tac x y z = lift (f (Value.repr_to r0 x) (Value.repr_to r1 y) (Value.repr_to r2 z)) in
  Tac2env.define_primitive (pname name) (mk_closure (arity_suc (arity_suc arity_one)) tac)

let define_prim4 name r0 r1 r2 r3 f =
  let tac x y z u = lift (f (Value.repr_to r0 x) (Value.repr_to r1 y) (Value.repr_to r2 z) (Value.repr_to r3 u)) in
  Tac2env.define_primitive (pname name) (mk_closure (arity_suc (arity_suc (arity_suc arity_one))) tac)

let define_prim5 name r0 r1 r2 r3 r4 f =
  let tac x y z u v = lift (f (Value.repr_to r0 x) (Value.repr_to r1 y) (Value.repr_to r2 z) (Value.repr_to r3 u) (Value.repr_to r4 v)) in
  Tac2env.define_primitive (pname name) (mk_closure (arity_suc (arity_suc (arity_suc (arity_suc arity_one)))) tac)

(** Tactics from Tacexpr *)

let () = define_prim2 "tac_intros" bool intro_patterns begin fun ev ipat ->
  Tac2tactics.intros_patterns ev ipat
end

let () = define_prim4 "tac_apply" bool bool (list (thunk constr_with_bindings)) (option (pair ident (option intro_pattern))) begin fun adv ev cb ipat ->
  Tac2tactics.apply adv ev cb ipat
end

let () = define_prim3 "tac_elim" bool constr_with_bindings (option constr_with_bindings) begin fun ev c copt ->
  Tac2tactics.elim ev c copt
end

let () = define_prim2 "tac_case" bool constr_with_bindings begin fun ev c ->
  Tac2tactics.general_case_analysis ev c
end

let () = define_prim1 "tac_generalize" (list generalize_arg) begin fun cl ->
  Tac2tactics.generalize cl
end

let () = define_prim1 "tac_assert" assertion begin fun ast ->
  Tac2tactics.assert_ ast
end

let () = define_prim3 "tac_enough" constr (option (option (thunk unit))) (option intro_pattern) begin fun c tac ipat ->
  let tac = Option.map (fun o -> Option.map (fun f -> thaw unit f) o) tac in
  Tac2tactics.forward false tac ipat c
end

let () = define_prim2 "tac_pose" name constr begin fun na c ->
  Tactics.letin_tac None na c None Locusops.nowhere
end

let () = define_prim3 "tac_set" bool (thunk (pair name constr)) clause begin fun ev p cl ->
  Proofview.tclEVARMAP >>= fun sigma ->
  thaw (pair name constr) p >>= fun (na, c) ->
  Tac2tactics.letin_pat_tac ev None na (sigma, c) cl
end

let () = define_prim5 "tac_remember" bool name (thunk constr) (option intro_pattern) clause begin fun ev na c eqpat cl ->
  let eqpat = Option.default (IntroNaming IntroAnonymous) eqpat in
  match eqpat with
  | IntroNaming eqpat ->
    Proofview.tclEVARMAP >>= fun sigma ->
    thaw constr c >>= fun c ->
    Tac2tactics.letin_pat_tac ev (Some (true, eqpat)) na (sigma, c) cl
  | _ ->
    Tacticals.New.tclZEROMSG (Pp.str "Invalid pattern for remember")
end

let () = define_prim3 "tac_destruct" bool (list induction_clause) (option constr_with_bindings) begin fun ev ic using ->
  Tac2tactics.induction_destruct false ev ic using
end

let () = define_prim3 "tac_induction" bool (list induction_clause) (option constr_with_bindings) begin fun ev ic using ->
  Tac2tactics.induction_destruct true ev ic using
end

let () = define_prim1 "tac_red" clause begin fun cl ->
  Tac2tactics.reduce (Red false) cl
end

let () = define_prim1 "tac_hnf" clause begin fun cl ->
  Tac2tactics.reduce Hnf cl
end

let () = define_prim3 "tac_simpl" red_flags (option pattern_with_occs) clause begin fun flags where cl ->
  Tac2tactics.simpl flags where cl
end

let () = define_prim2 "tac_cbv" red_flags clause begin fun flags cl ->
  Tac2tactics.cbv flags cl
end

let () = define_prim2 "tac_cbn" red_flags clause begin fun flags cl ->
  Tac2tactics.cbn flags cl
end

let () = define_prim2 "tac_lazy" red_flags clause begin fun flags cl ->
  Tac2tactics.lazy_ flags cl
end

let () = define_prim2 "tac_unfold" (list reference_with_occs) clause begin fun refs cl ->
  Tac2tactics.unfold refs cl
end

let () = define_prim2 "tac_fold" (list constr) clause begin fun args cl ->
  Tac2tactics.reduce (Fold args) cl
end

let () = define_prim2 "tac_pattern" (list constr_with_occs) clause begin fun where cl ->
  Tac2tactics.pattern where cl
end

let () = define_prim2 "tac_vm" (option pattern_with_occs) clause begin fun where cl ->
  Tac2tactics.vm where cl
end

let () = define_prim2 "tac_native" (option pattern_with_occs) clause begin fun where cl ->
  Tac2tactics.native where cl
end

(** Reduction functions *)

let lift tac = tac >>= fun c -> Proofview.tclUNIT (Value.of_constr c)

let define_red1 name r0 f =
  let tac x = lift (f (Value.repr_to r0 x)) in
  Tac2env.define_primitive (pname name) (mk_closure arity_one tac)

let define_red2 name r0 r1 f =
  let tac x y = lift (f (Value.repr_to r0 x) (Value.repr_to r1 y)) in
  Tac2env.define_primitive (pname name) (mk_closure (arity_suc arity_one) tac)

let define_red3 name r0 r1 r2 f =
  let tac x y z = lift (f (Value.repr_to r0 x) (Value.repr_to r1 y) (Value.repr_to r2 z)) in
  Tac2env.define_primitive (pname name) (mk_closure (arity_suc (arity_suc arity_one)) tac)

let () = define_red1 "eval_red" constr begin fun c ->
  Tac2tactics.eval_red c
end

let () = define_red1 "eval_hnf" constr begin fun c ->
  Tac2tactics.eval_hnf c
end

let () = define_red3 "eval_simpl" red_flags (option pattern_with_occs) constr begin fun flags where c ->
  Tac2tactics.eval_simpl flags where c
end

let () = define_red2 "eval_cbv" red_flags constr begin fun flags c ->
  Tac2tactics.eval_cbv flags c
end

let () = define_red2 "eval_cbn" red_flags constr begin fun flags c ->
  Tac2tactics.eval_cbn flags c
end

let () = define_red2 "eval_lazy" red_flags constr begin fun flags c ->
  Tac2tactics.eval_lazy flags c
end

let () = define_red2 "eval_unfold" (list reference_with_occs) constr begin fun refs c ->
  Tac2tactics.eval_unfold refs c
end

let () = define_red2 "eval_fold" (list constr) constr begin fun args c ->
  Tac2tactics.eval_fold args c
end

let () = define_red2 "eval_pattern" (list constr_with_occs) constr begin fun where c ->
  Tac2tactics.eval_pattern where c
end

let () = define_red2 "eval_vm" (option pattern_with_occs) constr begin fun where c ->
  Tac2tactics.eval_vm where c
end

let () = define_red2 "eval_native" (option pattern_with_occs) constr begin fun where c ->
  Tac2tactics.eval_native where c
end

let () = define_prim3 "tac_change" (option pattern) (fun1 (array constr) constr) clause begin fun pat c cl ->
  Tac2tactics.change pat c cl
end

let () = define_prim4 "tac_rewrite" bool (list rewriting) clause (option (thunk unit)) begin fun ev rw cl by ->
  Tac2tactics.rewrite ev rw cl by
end

let () = define_prim4 "tac_inversion" inversion_kind destruction_arg (option intro_pattern) (option (list ident)) begin fun knd arg pat ids ->
  Tac2tactics.inversion knd arg pat ids
end

(** Tactics from coretactics *)

let () = define_prim0 "tac_reflexivity" Tactics.intros_reflexivity

let () = define_prim2 "tac_move" ident move_location begin fun id mv ->
  Tactics.move_hyp id mv
end

let () = define_prim2 "tac_intro" (option ident) (option move_location) begin fun id mv ->
  let mv = Option.default Logic.MoveLast mv in
  Tactics.intro_move id mv
end

(*

TACTIC EXTEND exact
  [ "exact" casted_constr(c) ] -> [ Tactics.exact_no_check c ]
END

*)

let () = define_prim0 "tac_assumption" Tactics.assumption

let () = define_prim1 "tac_transitivity" constr begin fun c ->
  Tactics.intros_transitivity (Some c)
end

let () = define_prim0 "tac_etransitivity" (Tactics.intros_transitivity None)

let () = define_prim1 "tac_cut" constr begin fun c ->
  Tactics.cut c
end

let () = define_prim2 "tac_left" bool bindings begin fun ev bnd ->
  Tac2tactics.left_with_bindings ev bnd
end
let () = define_prim2 "tac_right" bool bindings begin fun ev bnd ->
  Tac2tactics.right_with_bindings ev bnd
end

let () = define_prim1 "tac_introsuntil" qhyp begin fun h ->
  Tactics.intros_until h
end

let () = define_prim1 "tac_exactnocheck" constr begin fun c ->
  Tactics.exact_no_check c
end

let () = define_prim1 "tac_vmcastnocheck" constr begin fun c ->
  Tactics.vm_cast_no_check c
end

let () = define_prim1 "tac_nativecastnocheck" constr begin fun c ->
  Tactics.native_cast_no_check c
end

let () = define_prim1 "tac_constructor" bool begin fun ev ->
  Tactics.any_constructor ev None
end

let () = define_prim3 "tac_constructorn" bool int bindings begin fun ev n bnd ->
  Tac2tactics.constructor_tac ev None n bnd
end

let () = define_prim2 "tac_specialize" constr_with_bindings (option intro_pattern) begin fun c ipat ->
  Tac2tactics.specialize c ipat
end

let () = define_prim1 "tac_symmetry" clause begin fun cl ->
  Tac2tactics.symmetry cl
end

let () = define_prim2 "tac_split" bool bindings begin fun ev bnd ->
  Tac2tactics.split_with_bindings ev bnd
end

let () = define_prim1 "tac_rename" (list (pair ident ident)) begin fun ids ->
  Tactics.rename_hyp ids
end

let () = define_prim1 "tac_revert" (list ident) begin fun ids ->
  Tactics.revert ids
end

let () = define_prim0 "tac_admit" Proofview.give_up

let () = define_prim2 "tac_fix" ident int begin fun ident n ->
  Tactics.fix ident n
end

let () = define_prim1 "tac_cofix" ident begin fun ident ->
  Tactics.cofix ident
end

let () = define_prim1 "tac_clear" (list ident) begin fun ids ->
  Tactics.clear ids
end

let () = define_prim1 "tac_keep" (list ident) begin fun ids ->
  Tactics.keep ids
end

let () = define_prim1 "tac_clearbody" (list ident) begin fun ids ->
  Tactics.clear_body ids
end

(** Tactics from extratactics *)

let () = define_prim2 "tac_discriminate" bool (option destruction_arg) begin fun ev arg ->
  Tac2tactics.discriminate ev arg
end

let () = define_prim3 "tac_injection" bool (option intro_patterns) (option destruction_arg) begin fun ev ipat arg ->
  Tac2tactics.injection ev ipat arg
end

let () = define_prim1 "tac_absurd" constr begin fun c ->
  Contradiction.absurd c
end

let () = define_prim1 "tac_contradiction" (option constr_with_bindings) begin fun c ->
  Tac2tactics.contradiction c
end

let () = define_prim4 "tac_autorewrite" bool (option (thunk unit)) (list ident) clause begin fun all by ids cl ->
  Tac2tactics.autorewrite ~all by ids cl
end

let () = define_prim1 "tac_subst" (list ident) begin fun ids ->
  Equality.subst ids
end

let () = define_prim0 "tac_substall" (return () >>= fun () -> Equality.subst_all ())

(** Auto *)

let () = define_prim3 "tac_trivial" debug (list (thunk constr)) (option (list ident)) begin fun dbg lems dbs ->
  Tac2tactics.trivial dbg lems dbs
end

let () = define_prim5 "tac_eauto" debug (option int) (option int) (list (thunk constr)) (option (list ident)) begin fun dbg n p lems dbs ->
  Tac2tactics.eauto dbg n p lems dbs
end

let () = define_prim4 "tac_auto" debug (option int) (list (thunk constr)) (option (list ident)) begin fun dbg n lems dbs ->
  Tac2tactics.auto dbg n lems dbs
end

let () = define_prim4 "tac_newauto" debug (option int) (list (thunk constr)) (option (list ident)) begin fun dbg n lems dbs ->
  Tac2tactics.new_auto dbg n lems dbs
end

let () = define_prim3 "tac_typeclasses_eauto" (option strategy) (option int) (option (list ident)) begin fun str n dbs ->
  Tac2tactics.typeclasses_eauto str n dbs
end
