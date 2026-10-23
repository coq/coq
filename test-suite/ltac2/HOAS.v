From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Judge Sort.

Ltac2 unwrap r :=
  match r with
  | Val r => r
  | Err e => Control.zero e
  end.

Ltac2 Notation t(self) "?" : 0 := unwrap t.

Ltac2 mkProdj (id:ident) (dom : typej) (codom : termj -> typej) :=
  let codom_ctx := push_named_assum id dom in
  let codomj := codom (hypj id codom_ctx)? in
  (* XXX should assert that codomj has compatible context with dom to be safe *)
  let codom := Constr.Unsafe.subst_vars [id] (UnsafeEnv.type_of_typej codomj) in
  let r := Constr.Relevance.of_sort (sort_of_typej dom) in
  let bnd := Constr.Binder.unsafe_make (Some id) r (UnsafeEnv.type_of_typej dom) in
  let c := Constr.Unsafe.make (Constr.Unsafe.Prod bnd codom) in
  UnsafeEnv.typej (env_of_typej dom) c (Sort.sort_of_product (sort_of_typej dom) (sort_of_typej codomj)).

#[warnings="-ltac2-notation-for-abbreviation"]
Ltac2 Notation oflags := Constr.Pretype.Flags.open_constr_flags_no_tc.

(* forall (A:Set) (x:A) (e:x = x), e = eq_refl
   (term construction with a relatively high amout of dependency on introduced variables) *)
Ltac2 Eval
  let ctx := Control.global_env() in
  let c : typej :=
  mkProdj @A (pretype_type_judge oflags ctx preterm:(Set))? (fun a =>
   mkProdj @x (termj_is_typej a)? (fun x =>
    let xc := UnsafeEnv.term_of_termj x in
    let refl_typ := (pretype_type_judge oflags (env_of_termj x) preterm:($xc = $xc))? in
    mkProdj @e refl_typ (fun e =>
      (* NB: because we are using named and not rel, refl_typ is still valid in the extended ctx *)
      let ec := UnsafeEnv.term_of_termj e in
      let refl_typc := UnsafeEnv.type_of_typej refl_typ in
      (pretype_type_judge oflags (env_of_termj e) preterm:(@eq $refl_typc $ec eq_refl))?)))
  in
  c.

(** unsafe HOAS (manual ctx manipulation) *)
Ltac2 mkProd (ctx : env) (id:ident) (dom : constr) (codom : env -> constr -> constr) :=
  let domr := Constr.Relevance.UnsafeEnv.relevance_of_type_in_env ctx dom in
  let codom_ctx := UnsafeEnv.push_named_assum ctx id dom domr in
  let codom := codom codom_ctx (Constr.Unsafe.make (Constr.Unsafe.Var id)) in
  let codom := Constr.Unsafe.subst_vars [id] codom in
  Constr.Unsafe.make (Constr.Unsafe.Prod (Constr.Binder.unsafe_make (Some id) domr dom) codom).

Ltac2 pretype_in_env flags ctx c :=
  let j := pretype_judge flags ctx c in
  UnsafeEnv.term_of_termj j?.

(* XXX "preterm" is at level 8 but we want to accept top level *)
Ltac2 Notation "open_constr_in_env:(" ctx(tactic) "|-" x(preterm) ")" :=
  pretype_in_env Constr.Pretype.Flags.open_constr_flags_no_tc ctx x.

(* forall (A:Set) (x:A) (e:x = x), e = eq_refl
   (term construction with a relatively high amout of dependency on introduced variables) *)
Ltac2 Eval
  let env := Control.global_env() in
  let c :=
  mkProd env @A 'Set (fun env a =>
   mkProd env @x a (fun env x =>
    let refl_typ := open_constr_in_env:(env |- ($x = $x)) in
    mkProd env @e refl_typ (fun env e =>
      (* NB: because we are using named and not rel, refl_typ is still valid in the extended env *)
      open_constr_in_env:(env |- (@eq $refl_typ $e eq_refl)))))
  in
  Control.assert_true (Constr.equal c '(forall (A:Set) (x:A) (e:x = x), e = eq_refl));
  let _ := Constr.type c in
  ().

(* forall x:nat, (x = x) = (x = x)
   demonstrates how the locally bound variable can be referred to in terms *)
Ltac2 Eval
  let env := Control.global_env() in
  let c :=
  mkProd env @x 'nat (fun env x =>
   (* we can refer to x as any of [x], [&x] and [$x]
      (not sure how reliable bare [x] is) *)
   let c1 := open_constr_in_env:(env |- (&x = x)) in
   let c2 := open_constr_in_env:(env |- (&x = $x)) in
   open_constr_in_env:(env |- ($c1 = $c2)))
  in
  Control.assert_true (Constr.equal c '(forall x:nat, (x = x) = (x = x))).

(* forall x:nat, 2 + x = S (S x)
   with the RHS constructed by reducing the LHS in the extended context *)
Ltac2 Eval
  let env := Control.global_env() in
  let c :=
  mkProd env @x 'nat (fun env x =>
    let y := open_constr_in_env:(env |- (2 + $x)) in
    let y_reduced := Std.UnsafeEnv.eval_in_env env (Std.Red.simpl RedFlags.all None) y in
    (* 'eq is '(@eq _) which produces a type evar with empty context *)
    open_constr_in_env:(env |- ($y = $y_reduced)))
  in
  Control.assert_true (Constr.equal c '(forall x, 2 + x = S (S x)));
  let _ := Constr.type c in
  ().

Ltac2 mkLetIn (ctx : env) (id:ident) (value : constr) (typ : constr) (body : env -> constr -> constr) :=
  let r := Constr.Relevance.UnsafeEnv.relevance_of_term_in_env ctx value in
  let body_ctx := UnsafeEnv.push_named_def ctx id value typ r in
  let body := body body_ctx (Constr.Unsafe.make (Constr.Unsafe.Var id)) in
  let body := Constr.Unsafe.subst_vars [id] body in
  Constr.Unsafe.make (Constr.Unsafe.LetIn (Constr.Binder.unsafe_make (Some id) r typ) value body).

Ltac2 Eval
  let env := Control.global_env() in
  let c :=
  mkLetIn env @x '3 'nat (fun env x =>
    open_constr_in_env:(env |- (eq_refl : $x = 3)))
  in
  Control.assert_true (Constr.equal c '(let x := 3 in eq_refl : x = 3));
  let _ := Constr.type c in
  ().
