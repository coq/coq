(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Genredexpr
open Tac2expr
open Tac2val
open Tac2ffi
open Tac2types
open Tac2extffi
open Proofview.Notations

module Value = Tac2ffi

(** Make a representation with a dummy from function *)
let make_to_repr f = Tac2ffi.make_repr (fun _ -> assert false) f

let return x = Proofview.tclUNIT x
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

let to_red_strength = function
  | ValInt 0 -> Norm
  | ValInt 1 -> Head
  | _ -> assert false

let to_red_flag v = match Value.to_tuple v with
| [| strength; beta; iota; fix; cofix; zeta; delta; const |] ->
  {
    rStrength = to_red_strength strength;
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

let rec of_intro_pattern = function
  | IntroForthcoming b -> of_block (0, [|of_bool b|])
  | IntroNaming pat -> of_block (1, [|of_intro_pattern_naming pat|])
  | IntroAction act -> of_block (2, [|of_intro_pattern_action act|])

and of_intro_pattern_naming = function
  | IntroIdentifier id -> of_block (0, [|of_ident id|])
  | IntroFresh id -> of_block (1, [|of_ident id|])
  | IntroAnonymous -> of_int 0

and of_intro_pattern_action = function
  | IntroWildcard -> of_int 0
  | IntroOrAndPattern op -> of_block (0, [|of_or_and_intro_pattern op|])
  | IntroInjection inj -> of_block (1, [|of_list of_intro_pattern inj|])
  | IntroApplyOn (c, ipat) ->
    let c = repr_of (fun1 unit constr) c in
    of_block (2, [|c; of_intro_pattern ipat|])
  | IntroRewrite b -> of_block (3, [|of_bool b|])

and of_or_and_intro_pattern = function
  | IntroOrPattern ill -> of_block (0, [|of_list of_intro_patterns ill|])
  | IntroAndPattern il -> of_block (1, [|of_intro_patterns il|])

and of_intro_patterns il = of_list of_intro_pattern il

let intro_pattern = make_repr of_intro_pattern to_intro_pattern

let intro_patterns = make_repr of_intro_patterns to_intro_patterns

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

open Tac2externals

let define s =
  define { mltac_plugin = "rocq-runtime.plugins.ltac2"; mltac_tactic = s }

(** Tactics from Tacexpr *)

let () =
  define "tac_intros"
    (bool @-> intro_patterns @-> tac unit)
    Tac2tactics.intros_patterns

let () =
  define "tac_apply"
    (bool @-> bool @-> list (thunk constr_with_bindings) @->
      option (pair ident (option intro_pattern)) @-> tac unit)
    Tac2tactics.apply

let () =
  define "tac_elim"
    (bool @-> constr_with_bindings @-> option constr_with_bindings @-> tac unit)
    Tac2tactics.elim

let () =
  define "tac_case"
    (bool @-> constr_with_bindings @-> tac unit)
    Tac2tactics.general_case_analysis

let () =
  define "tac_generalize"
    (list generalize_arg @-> tac unit)
    Tac2tactics.generalize

let () =
  define "tac_assert"
    (assertion @-> tac unit)
    Tac2tactics.assert_

let tac_enough c tac ipat =
  let tac = Option.map (fun o -> Option.map (fun f -> thaw unit f) o) tac in
  Tac2tactics.forward false tac ipat c
let () =
  define "tac_enough"
    (constr @-> option (option (thunk unit)) @-> option intro_pattern @-> tac unit)
    tac_enough

let tac_pose na c = Tactics.letin_tac None na c None Locusops.nowhere
let () =
  define "tac_pose"
    (name @-> constr @-> tac unit)
    tac_pose

let tac_set ev p cl =
  Proofview.tclEVARMAP >>= fun sigma ->
  thaw (pair name constr) p >>= fun (na, c) ->
  Tac2tactics.letin_pat_tac ev None na (Some sigma, c) cl
let () =
  define "tac_set"
    (bool @-> thunk (pair name constr) @-> clause @-> tac unit)
    tac_set

let tac_remember ev na c eqpat cl =
  let eqpat = Option.default (IntroNaming IntroAnonymous) eqpat in
  match eqpat with
  | IntroNaming eqpat ->
    Proofview.tclEVARMAP >>= fun sigma ->
    thaw constr c >>= fun c ->
    Tac2tactics.letin_pat_tac ev (Some (true, eqpat)) na (Some sigma, c) cl
  | _ ->
    Tacticals.tclZEROMSG (Pp.str "Invalid pattern for remember")
let () =
  define "tac_remember"
    (bool @-> name @-> thunk constr @-> option intro_pattern @-> clause @-> tac unit)
    tac_remember

let () =
  define "tac_destruct"
    (bool @-> list induction_clause @-> option constr_with_bindings @-> tac unit)
    (Tac2tactics.induction_destruct false)

let () =
  define "tac_induction"
    (bool @-> list induction_clause @-> option constr_with_bindings @-> tac unit)
    (Tac2tactics.induction_destruct true)

let () =
  define "tac_red" (clause @-> tac unit) (Tac2tactics.reduce Red)

let () =
  define "tac_hnf" (clause @-> tac unit) (Tac2tactics.reduce Hnf)

let () =
  define "tac_simpl"
    (red_flags @-> option pattern_with_occs @-> clause @-> tac unit)
    Tac2tactics.simpl

let () =
  define "tac_cbv" (red_flags @-> clause @-> tac unit) Tac2tactics.cbv

let () =
  define "tac_cbn" (red_flags @-> clause @-> tac unit) Tac2tactics.cbn

let () =
  define "tac_lazy" (red_flags @-> clause @-> tac unit) Tac2tactics.lazy_

let () =
  define "tac_unfold"
    (list reference_with_occs @-> clause @-> tac unit)
    Tac2tactics.unfold

let () =
  define "tac_fold"
    (list constr @-> clause @-> tac unit)
    (fun args cl -> Tac2tactics.reduce (Fold args) cl)

let () =
  define "tac_pattern"
    (list constr_with_occs @-> clause @-> tac unit)
    Tac2tactics.pattern

let () =
  define "tac_vm"
    (option pattern_with_occs @-> clause @-> tac unit)
    Tac2tactics.vm

let () =
  define "tac_native"
    (option pattern_with_occs @-> clause @-> tac unit)
    Tac2tactics.native

(** Reduction functions *)

let () = define "eval_red" (constr @-> tac constr) Tac2tactics.eval_red

let () = define "eval_hnf" (constr @-> tac constr) Tac2tactics.eval_hnf

let () =
  define "eval_simpl"
    (red_flags @-> option pattern_with_occs @-> constr @-> tac constr)
    Tac2tactics.eval_simpl

let () =
  define "eval_cbv" (red_flags @-> constr @-> tac constr) Tac2tactics.eval_cbv

let () =
  define "eval_cbn" (red_flags @-> constr @-> tac constr) Tac2tactics.eval_cbn

let () =
  define "eval_lazy" (red_flags @-> constr @-> tac constr) Tac2tactics.eval_lazy

let () =
  define "eval_unfold"
    (list reference_with_occs @-> constr @-> tac constr)
    Tac2tactics.eval_unfold

let () =
  define "eval_fold"
    (list constr @-> constr @-> tac constr)
    Tac2tactics.eval_fold

let () =
  define "eval_pattern"
    (list constr_with_occs @-> constr @-> tac constr)
    Tac2tactics.eval_pattern

let () =
  define "eval_vm"
    (option pattern_with_occs @-> constr @-> tac constr)
    Tac2tactics.eval_vm

let () =
  define "eval_native"
    (option pattern_with_occs @-> constr @-> tac constr)
    Tac2tactics.eval_native

let () =
  define "tac_change"
    (option pattern @-> fun1 (array constr) constr @-> clause @-> tac unit)
    Tac2tactics.change

let () =
  define "tac_rewrite"
    (bool @-> list rewriting @-> clause @-> option (thunk unit) @-> tac unit)
    Tac2tactics.rewrite

let () =
  define "tac_setoid_rewrite"
    (bool @-> uthaw constr_with_bindings @--> occurrences @-> option ident @-> tac unit)
    Tac2tactics.setoid_rewrite

let () =
  define "tac_inversion"
    (inversion_kind @-> destruction_arg @-> option intro_pattern @->
      option (list ident) @-> tac unit)
    Tac2tactics.inversion

(** Tactics from coretactics *)

let () =
  define "tac_reflexivity" (unit @-> tac unit) (fun _ -> Tactics.intros_reflexivity)

let () =
  define "tac_move" (ident @-> move_location @-> tac unit) Tactics.move_hyp

let tac_intro id mv =
  let mv = Option.default Logic.MoveLast mv in
  Tactics.intro_move id mv
let () =
  define "tac_intro" (option ident @-> option move_location @-> tac unit) tac_intro

(*

TACTIC EXTEND exact
  [ "exact" casted_constr(c) ] -> [ Tactics.exact_no_check c ]
END

*)

let () =
  define "tac_assumption" (unit @-> tac unit) (fun _ -> Tactics.assumption)

let () =
  define "tac_transitivity" (constr @-> tac unit)
    (fun c -> Tactics.intros_transitivity (Some c))

let () =
  define "tac_etransitivity" (unit @-> tac unit)
    (fun _ -> Tactics.intros_transitivity None)

let () =
  define "tac_cut" (constr @-> tac unit) Tactics.cut

let () =
  define "tac_left" (bool @-> bindings @-> tac unit) Tac2tactics.left_with_bindings

let () =
  define "tac_right" (bool @-> bindings @-> tac unit) Tac2tactics.right_with_bindings

let () =
  define "tac_introsuntil" (qhyp @-> tac unit) Tactics.intros_until

let () =
  define "tac_exactnocheck" (constr @-> tac unit) Tactics.exact_no_check

let () =
  define "tac_vmcastnocheck" (constr @-> tac unit) Tactics.vm_cast_no_check

let () =
  define "tac_nativecastnocheck" (constr @-> tac unit) Tactics.native_cast_no_check

let () =
  define "tac_constructor" (bool @-> tac unit) (fun ev -> Tactics.any_constructor ev None)

let () =
  define "tac_constructorn" (bool @-> int @-> bindings @-> tac unit)
    (fun ev n bnd -> Tac2tactics.constructor_tac ev None n bnd)

let () =
  define "tac_specialize"
    (constr_with_bindings @-> option intro_pattern @-> tac unit)
    Tac2tactics.specialize

let () =
  define "tac_symmetry" (clause @-> tac unit) Tac2tactics.symmetry

let () =
  define "tac_split" (bool @-> bindings @-> tac unit) Tac2tactics.split_with_bindings

let () =
  define "tac_rename" (list (pair ident ident) @-> tac unit) Tactics.rename_hyp

let () =
  define "tac_revert" (list ident @-> tac unit) Generalize.revert

let () =
  define "tac_admit" (unit @-> tac unit) (fun _ -> Proofview.give_up)

let () =
  define "tac_fix" (ident @-> int @-> tac unit) Tactics.fix

let () =
  define "tac_cofix" (ident @-> tac unit) Tactics.cofix

let () =
  define "tac_clear" (list ident @-> tac unit) Tactics.clear

let () =
  define "tac_keep" (list ident @-> tac unit) Tactics.keep

let () =
  define "tac_clearbody" (list ident @-> tac unit) Tactics.clear_body

(** Tactics from extratactics *)

let () =
  define "tac_discriminate"
    (bool @-> option destruction_arg @-> tac unit)
    Tac2tactics.discriminate

let () =
  define "tac_injection"
    (bool @-> option intro_patterns @-> option destruction_arg @-> tac unit)
    Tac2tactics.injection

let () =
  define "tac_absurd" (constr @-> tac unit) Contradiction.absurd

let () =
  define "tac_contradiction"
    (option constr_with_bindings @-> tac unit)
    Tac2tactics.contradiction

let () =
  define "tac_autorewrite"
    (bool @-> option (thunk unit) @-> list ident @-> clause @-> tac unit)
    (fun all by ids cl -> Tac2tactics.autorewrite ~all by ids cl)

let () =
  define "tac_subst" (list ident @-> tac unit) Equality.subst

let () =
  define "tac_substall"
    (unit @-> tac unit)
    (fun _ -> return () >>= fun () -> Equality.subst_all ())

(** Auto *)

let () =
  define "tac_trivial"
    (debug @-> list reference @-> option (list ident) @-> tac unit)
    Tac2tactics.trivial

let () =
  define "tac_eauto"
    (debug @-> option int @-> list reference @-> option (list ident) @-> tac unit)
    Tac2tactics.eauto

let () =
  define "tac_auto"
    (debug @-> option int @-> list reference @-> option (list ident) @-> tac unit)
    Tac2tactics.auto

let () =
  define "tac_typeclasses_eauto"
    (option strategy @-> option int @-> option (list ident) @-> tac unit)
    Tac2tactics.typeclasses_eauto

let () =
  define "tac_resolve_tc" (constr @-> tac unit) Class_tactics.resolve_tc

let () =
  define "tac_unify" (constr @-> constr @-> tac unit) Tac2tactics.unify

(** Tactics for [Ltac2/TransparentState.v]. *)

let () =
  define "current_transparent_state"
    (unit @-> tac transparent_state)
    Tac2tactics.current_transparent_state

let () =
  define "full_transparent_state" (ret transparent_state) TransparentState.full

let () =
  define "empty_transparent_state" (ret transparent_state) TransparentState.empty

(** Tactics around Evarconv unification (in [Ltac2/Unification.v]). *)

let () =
  define "evarconv_unify"
    (transparent_state @-> constr @-> constr @-> tac unit)
    Tac2tactics.evarconv_unify

let () =
  define "congruence"
  (option int @-> option (list constr) @-> tac unit)
  Tac2tactics.congruence

let () =
  define "simple_congruence"
  (option int @-> option (list constr) @-> tac unit)
  Tac2tactics.simple_congruence
