Require Import Ltac2.Ltac2.

Ltac2 equal_hyps h1 h2 :=
  List.equal
    (fun (id1, body1, typ1) (id2, body2, typ2) =>
       Bool.and (Ident.equal id1 id2)
         (Bool.and (Option.equal Constr.equal body1 body2)
            (Constr.equal typ1 typ2)))
    h1 h2.

Ltac2 Eval Control.assert_true (equal_hyps [] (Env.hyps_in (Env.global_env()))).
Fail Ltac2 Eval Env.goal_env().
Ltac2 Eval Control.assert_true (equal_hyps [] (Env.hyps_in (Env.current_env()))).

Lemma foo (A:Set) (x:=0) : x = x.
  Control.assert_true (equal_hyps [] (Env.hyps_in (Env.global_env()))).
  let expected_hyps := [(@A, None, constr:(Set)); (@x, Some constr:(0), constr:(nat))] in
  Control.assert_true (equal_hyps expected_hyps (Env.hyps_in (Env.goal_env())));
  Control.assert_true (equal_hyps expected_hyps (Env.hyps_in (Env.current_env()))).

  assert True.
  Control.assert_true (equal_hyps [] (Env.hyps_in (Env.global_env()))).
  Fail Ltac2 Eval Env.goal_env().
  Fail Ltac2 Eval Env.current_env().
  1:let expected_hyps := [(@A, None, constr:(Set)); (@x, Some constr:(0), constr:(nat))] in
  Control.assert_true (equal_hyps expected_hyps (Env.hyps_in (Env.goal_env())));
  Control.assert_true (equal_hyps expected_hyps (Env.hyps_in (Env.current_env()))).
Abort.

Section S.
  Variable (A:Set).

  Ltac2 Eval Control.assert_true
    (equal_hyps [(@A, None, constr:(Set))]
       (Env.hyps_in (Env.global_env()))).
  Fail Ltac2 Eval Env.goal_env().
  Ltac2 Eval Control.assert_true
    (equal_hyps [(@A, None, constr:(Set))]
       (Env.hyps_in (Env.current_env()))).

  Lemma foo (x:=0) : x = x.
    Control.assert_true (equal_hyps [(@A, None, constr:(Set))] (Env.hyps_in (Env.global_env()))).
    let expected_hyps := [(@A, None, constr:(Set)); (@x, Some constr:(0), constr:(nat))] in
    Control.assert_true (equal_hyps expected_hyps (Env.hyps_in (Env.goal_env())));
    Control.assert_true (equal_hyps expected_hyps (Env.hyps_in (Env.current_env()))).

    assert True.
    Control.assert_true (equal_hyps [(@A, None, constr:(Set))] (Env.hyps_in (Env.global_env()))).
    Fail Ltac2 Eval Env.goal_env().
    Fail Ltac2 Eval Env.current_env().
    1:let expected_hyps := [(@A, None, constr:(Set)); (@x, Some constr:(0), constr:(nat))] in
      Control.assert_true (equal_hyps expected_hyps (Env.hyps_in (Env.goal_env())));
      Control.assert_true (equal_hyps expected_hyps (Env.hyps_in (Env.current_env()))).
  Abort.
End S.

Ltac2 mkProd (env : env) (id:ident) (dom : constr) (codom : env -> constr -> constr) :=
  let dom := Constr.Binder.make_in env (Some id) dom in
  let codom_env := Env.push_named_assum dom env in
  let codom := codom codom_env (Env.hyp_in codom_env id) in
  let codom := Constr.Unsafe.subst_vars [id] codom in
  Constr.Unsafe.make (Constr.Unsafe.Prod dom codom).

Ltac2 pretype_in := Constr.pretype_in.

(* forall (A:Set) (x:A) (e:x = x), e = eq_refl
   (term construction with a relatively high amout of dependency on introduced variables) *)
Ltac2 Eval
  let env := Env.global_env() in
  let c :=
  mkProd env @A 'Set (fun env a =>
   mkProd env @x a (fun env x =>
    let refl_typ := pretype_in env preterm:($x = $x) in
    mkProd env @e refl_typ (fun env e =>
      (* NB: because we are using named and not rel, refl_typ is still valid in the extended env *)
      pretype_in env preterm:(@eq $refl_typ $e eq_refl))))
  in
  Control.assert_true (Constr.equal c '(forall (A:Set) (x:A) (e:x = x), e = eq_refl));
  let _ := Constr.type c in
  ().

(* forall x:nat, 2 + x = S (S x)
   with the RHS constructed by reducing the LHS in the extended context *)
Ltac2 Eval
  let env := Env.global_env() in
  let c :=
  mkProd env @x 'nat (fun env x =>
    let y := pretype_in env preterm:(2 + $x) in
    let y_reduced := Std.eval_simpl_in env RedFlags.all None y in
    (* 'eq is '(@eq _) which produces a type evar with empty context *)
    pretype_in env preterm:($y = $y_reduced))
  in
  Control.assert_true (Constr.equal c '(forall x, 2 + x = S (S x)));
  let _ := Constr.type c in
  ().

(* forall x:nat, (x = x) = (x = x)
   demonstrates how the locally bound variable can be referred to in preterm *)
Ltac2 Eval
  let env := Env.global_env() in
  let c :=
  mkProd env @x 'nat (fun env x =>
   (* we can refer to x as any of [x], [&x] and [$x]
      (not sure how reliable bare [x] is) *)
   let c1 := pretype_in env preterm:(&x = x) in
   let c2 := pretype_in env preterm:(&x = $x) in
   pretype_in env preterm:($c1 = $c2))
  in
  Control.assert_true (Constr.equal c '(forall x:nat, (x = x) = (x = x))).

Ltac2 push_x t env := Env.push_named_assum (Constr.Binder.make (Some @x) t) env.

Fail Ltac2 Eval
  let env := Env.global_env() in
  let env := push_x 'True env in
  let env := push_x 'False env in
  env.

Ltac2 push_x_def t v env := Env.Unsafe.push_named_def (Constr.Binder.make (Some @x) t) v env.

Fail Ltac2 Eval
  let env := Env.global_env() in
  let env := push_x 'True env in
  let env := push_x_def 'True 'I env in
  env.
