From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Judge Unification.

Ltac2 unwrap r :=
  match r with
  | Val r => r
  | Err e => Control.zero e
  end.

Ltac2 pretype_in_env flags ctx c :=
  let j := pretype_judge flags ctx c in
  let j := unwrap j in
  UnsafeEnv.term_of_termj j.

(* XXX "preterm" is at level 8 but we want to accept top level *)
Ltac2 Notation "open_constr_in_env:(" ctx(tactic) "|-" x(preterm) ")" :=
  pretype_in_env Constr.Pretype.Flags.open_constr_flags_no_tc ctx x.

Ltac2 conv_in ctx c1 c2 := UnsafeEnv.conv_in_env Unification.CONV TransparentState.full ctx c1 c2.

Ltac2 unify_in ctx c1 c2 :=
  match Control.case (fun () => UnsafeEnv.unify_in_env Unification.CONV TransparentState.full ctx c1 c2) with
  | Val _ => true
  | Err _ => false
  end.

Ltac2 mkVar x := Constr.Unsafe.make (Constr.Unsafe.Var x).

Ltac2 Eval
  let ctx := Control.global_env() in
  let a := mkVar @A in
  let mk t r :=
    let ctx := UnsafeEnv.push_named_assum ctx @A t Constr.Binder.Relevant in
    let ctx := UnsafeEnv.push_named_assum ctx @x a r in
    let ctx := UnsafeEnv.push_named_assum ctx @y a r in
    ctx
  in
  let ctx1 := mk 'Prop Constr.Binder.Relevant in
  let ctx2 := mk 'SProp Constr.Binder.Irrelevant in
  Control.assert_false (conv_in ctx1 (mkVar @x) (mkVar @y));
  Control.assert_true  (conv_in ctx2 (mkVar @x) (mkVar @y));
  Control.assert_false (unify_in ctx1 (mkVar @x) (mkVar @y));
  Control.assert_true  (unify_in ctx2 (mkVar @x) (mkVar @y));
  ().

Ltac2 Eval
  let ctx := Control.global_env() in
  let j := pretype_judge Constr.Pretype.Flags.open_constr_flags_no_tc ctx preterm:(3) in
  let j := unwrap j in
  let ctx := push_named_def @x j in
  Control.assert_true (conv_in ctx (mkVar @x) '3);
  Control.assert_false (conv_in ctx (mkVar @x) '4);
  Control.assert_true  (unify_in ctx (mkVar @x) '3);
  Control.assert_false (unify_in ctx (mkVar @x) '4);
  Control.assert_false (conv_in ctx (mkVar @x) '(S _));
  Control.assert_true  (unify_in ctx (mkVar @x) '(S _));
  ().
