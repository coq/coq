(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
open Tac2ffi
open Tac2types
open Tac2extffi
open Proofview.Notations

module Value = Tac2ffi

let return x = Proofview.tclUNIT x
let v_unit = Value.of_unit ()
let thaw r f = Tac2ffi.app_fun1 f unit r ()
let thunk r = fun1 unit r

let name : Name.t repr = magic_repr ()

let occurrences : occurrences repr = magic_repr ()

let clause : clause repr = magic_repr ()

let red_flags : GlobRef.t glob_red_flag repr = magic_repr ()

let pattern_with_occs = pair pattern occurrences

let constr_with_occs = pair constr occurrences

let reference_with_occs = pair reference occurrences

let intro_pattern : intro_pattern repr = magic_repr ()

let intro_patterns = list intro_pattern

let destruction_arg : destruction_arg repr = magic_repr ()

let induction_clause : induction_clause repr = magic_repr ()

let assertion : assertion repr = magic_repr ()

let rewriting : rewriting repr = magic_repr ()

let debug : Hints.debug repr = magic_repr ()

let strategy : Class_tactics.search_strategy repr = magic_repr ()

let inversion_kind : Inv.inversion_kind repr = magic_repr ()

let move_location : Id.t Logic.move_location repr = magic_repr ()

let generalize_arg = triple constr occurrences name

(** Standard tactics sharing their implementation with Ltac1 *)

let pname s = { mltac_plugin = "coq-core.plugins.ltac2"; mltac_tactic = s }

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
    Tacticals.tclZEROMSG (Pp.str "Invalid pattern for remember")
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
  Tactics.intros_until (Tac2tactics.mk_qhyp h)
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

let () = define_prim4 "tac_eauto" debug (option int) (list (thunk constr)) (option (list ident)) begin fun dbg n lems dbs ->
  Tac2tactics.eauto dbg n lems dbs
end

let () = define_prim4 "tac_auto" debug (option int) (list (thunk constr)) (option (list ident)) begin fun dbg n lems dbs ->
  Tac2tactics.auto dbg n lems dbs
end

let () = define_prim3 "tac_typeclasses_eauto" (option strategy) (option int) (option (list ident)) begin fun str n dbs ->
  Tac2tactics.typeclasses_eauto str n dbs
end

let () = define_prim2 "tac_unify" constr constr begin fun x y ->
  Tac2tactics.unify x y
end
