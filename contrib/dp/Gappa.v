Require Import Reals.
Require Import List.
Require Import Gappa_library.
Require Import Gappa_integer.

Inductive UnaryOp : Set :=
  | uoNeg | uoSqrt | uoAbs | uoInv.

Inductive BinaryOp : Set :=
  | boAdd | boSub | boMul | boDiv.

(* represent an expression on real numbers *)
Inductive RExpr : Set :=
  | reUnknown : R -> RExpr
  | reInteger : Z -> RExpr
  | reFloat2 : Z -> Z -> RExpr
  | reUnary : UnaryOp -> RExpr -> RExpr
  | reBinary : BinaryOp -> RExpr -> RExpr -> RExpr
  | rePow2 : Z -> RExpr
  | reINR : positive -> RExpr.

(* convert to an expression on real numbers *)
Fixpoint convert t : R :=
  match t with
  | reUnknown x => x
  | reInteger x => Float1 x
  | reFloat2 x y => float2R (Float2 x y)
  | reUnary o x =>
    match o with
    | uoNeg  => Ropp
    | uoSqrt => sqrt
    | uoAbs  => Rabs
    | uoInv  => Rinv
    end (convert x)
  | reBinary o x y =>
    match o with
    | boAdd => Rplus
    | boSub => Rminus
    | boMul => Rmult
    | boDiv => Rdiv
    end (convert x) (convert y)
  | rePow2 x =>
    powerRZ 2%R x
  | reINR x =>
    INR (nat_of_P x)
  end.

Definition is_stable f :=
  forall t, convert (f t) = convert t.

(* apply a function recursively, starting from the leafs of an expression *)
Definition recursive_transform f :=
  let fix aux (t : RExpr) := f
    match t with
    | reUnary  o x   => reUnary  o (aux x)
    | reBinary o x y => reBinary o (aux x) (aux y)
    | _ => t
    end in
  aux.

Theorem recursive_transform_correct :
  forall f,
  is_stable f ->
  is_stable (recursive_transform f).
unfold is_stable.
intros f Hf t.
induction t ; simpl ; rewrite Hf ; try apply refl_equal.
simpl.
rewrite IHt.
apply refl_equal.
simpl.
rewrite IHt1.
rewrite IHt2.
apply refl_equal.
Qed.

Record TF : Set := mkTF
  { trans_func :> RExpr -> RExpr ;
    trans_prop : is_stable trans_func }.

(* apply several recursive transformations in a row (selected from head to tail) *)
Definition multi_transform :=
  fold_left (fun v f => recursive_transform (trans_func f) v).

Theorem multi_transform_correct :
  forall l t,
  convert (multi_transform l t) = convert t.
intros l.
unfold multi_transform.
rewrite <- (rev_involutive l).
induction (rev l) ; intros t.
apply refl_equal.
simpl.
rewrite fold_left_app.
simpl.
rewrite recursive_transform_correct.
apply IHl0.
apply trans_prop.
Qed.

(* detect closed integers *)
Ltac is_natural t :=
  match t with
  | O => true
  | S ?t' => is_natural t'
  | _ => false
  end.

Ltac is_positive t :=
  match t with
  | xH => true
  | xO ?t' => is_positive t'
  | xI ?t' => is_positive t'
  | _ => false
  end.

Ltac is_integer t :=
  match t with
  | Z0 => true
  | Zpos ?t' => is_positive t'
  | Zneg ?t' => is_positive t'
  | _ => false
  end.

(* produce an inductive object u such that convert(u) is convertible to t,
   all the integers contained in u are closed expressions *)
Ltac get_inductive_term t :=
  match t with
  | 0%R =>
    constr:(reInteger 0%Z)
  | 1%R =>
    constr:(reInteger 1%Z)
  | 2%R =>
    constr:(reInteger 2%Z)
  | 3%R =>
    constr:(reInteger 3%Z)
  | (2 * ?x)%R =>
    match get_inductive_term x with
    | reInteger (Zpos (?c ?y)) => constr:(reInteger (Zpos (xO (c y))))
    | ?x' => constr:(reBinary boMul (reInteger 2%Z) x')
    end
  | (1 + 2 * ?x)%R =>
    match get_inductive_term x with
    | reInteger (Zpos (?c ?y)) => constr:(reInteger (Zpos (xI (c y))))
    | ?x' => constr:(reBinary boAdd (reInteger 1%Z) (reBinary boMul (reInteger 2%Z) x'))
    end
  | IZR 0%Z =>
    constr:(reInteger 0%Z)
  | IZR 1%Z =>
    constr:(reInteger 1%Z)
  | IZR 2%Z =>
    constr:(reInteger 2%Z)
  | IZR (-1)%Z =>
    constr:(reInteger (-1)%Z)
  | IZR (-2)%Z =>
    constr:(reInteger (-2)%Z)
  | INR 0%nat =>
    constr:(reInteger 0%Z)
  | INR 1%nat =>
    constr:(reInteger 1%Z)
  | INR 2%nat =>
    constr:(reInteger 2%Z)
  | INR (S ?x) =>
    match is_natural x with
    | true =>
      let x' := eval vm_compute in (P_of_succ_nat x) in
      constr:(reINR x')
    end
  | IZR (Zpos ?x) =>
    match is_positive x with
    | true => constr:(reINR x)
    end
  | IZR (Zneg ?x) =>
    match is_positive x with
    | true => constr:(reUnary uoNeg (reINR x))
    end
  | Ropp ?x =>
    match get_inductive_term x with
    | reInteger (Zpos ?y) => constr:(reInteger (Zneg y))
    | ?x' => constr:(reUnary uoNeg x')
    end
  | (?x + -?y)%R =>
    let x' := get_inductive_term x in
    let y' := get_inductive_term y in
    constr:(reBinary boSub x' y')
  | (?x * /?y)%R =>
    let x' := get_inductive_term x in
    let y' := get_inductive_term y in
    constr:(reBinary boDiv x' y')
  | powerRZ ?x ?y =>
    match get_inductive_term x with
    | reInteger 2%Z =>
      match is_integer y with
      | true => constr:(rePow2 y)
      end
    end
  | ?f ?x ?y =>
    let bo :=
      match f with
      | Rplus  => boAdd
      | Rminus => boSub
      | Rmult  => boMul
      | Rdiv   => boDiv
      end in
    let x' := get_inductive_term x in
    let y' := get_inductive_term y in
    constr:(reBinary bo x' y')
  | ?f ?x =>
    let bo :=
      match f with
      | Ropp => uoNeg
      | sqrt => uoSqrt
      | Rinv => uoInv
      | Rabs => uoAbs
      end in
    let x' := get_inductive_term x in
    constr:(reUnary bo x')
  | _ =>
    constr:(reUnknown t)
  end.

(* factor an integer into odd*2^e *)
Definition get_float2 x :=
  let fix aux (m : positive) e { struct m } :=
    match m with
    | xO p => aux p (Zsucc e)
    | _ => Float2 (Zpos m) e
    end in
  aux x Z0.

Lemma get_float2_correct :
  forall x, float2R (get_float2 x) = Z2R (Zpos x).
intros x.
unfold get_float2.
change (Z2R (Zpos x)) with (float2R (Float2 (Zpos x) 0%Z)).
generalize 0%Z.
induction x ; intros e ; try apply refl_equal.
rewrite IHx.
unfold float2R.
simpl.
replace (Zpos (xO x)) with (Zpos x * 2)%Z.
exact (Gappa_round_aux.float2_shift_p1 _ _).
rewrite Zmult_comm.
apply refl_equal.
Qed.

(* transform INR and IZR into real integers, change a/b and a*2^b into floats *)
Definition gen_float2_func t :=
  match t with
  | reUnary uoNeg (reInteger (Zpos x)) =>
    reInteger (Zneg x)
  | reBinary boDiv (reInteger x) (reInteger (Zpos y)) =>
    match get_float2 y with
    | Float2 1 (Zpos y') => reFloat2 x (Zneg y')
    | _ => t
    end
  | reBinary boMul (reInteger x) (rePow2 y) =>
    reFloat2 x y
  | reINR x =>
    reInteger (Zpos x)
  | _ => t
  end.

Lemma gen_float2_prop :
  is_stable gen_float2_func.
intros [x|x|x y|o x|o x y|x|x] ; try apply refl_equal.
(* unary ops *)
destruct o ; try apply refl_equal.
destruct x ; try apply refl_equal.
destruct z ; apply refl_equal.
(* binary ops *)
destruct o ; try apply refl_equal ;
  destruct x ; try apply refl_equal ;
  destruct y ; try apply refl_equal.
(* . x * 2^y *)
simpl.
unfold float2R.
rewrite F2R_split.
apply refl_equal.
(* . x / 2*2*2*2 *)
destruct z0 ; try apply refl_equal.
generalize (get_float2_correct p).
simpl.
destruct (get_float2 p) as ([|[m|m|]|m], [|e|e]) ; intros H ; try apply refl_equal.
rewrite <- H.
simpl.
unfold float2R.
do 2 rewrite F2R_split.
simpl.
rewrite Rmult_1_l.
apply refl_equal.
(* INR *)
exact (P2R_INR _).
Qed.

Definition gen_float2 := mkTF gen_float2_func gen_float2_prop.

(* remove pending powerRZ 2 *)
Definition clean_pow2_func t :=
  match t with
  | rePow2 x => reFloat2 1 x
  | _ => t
  end.

Lemma clean_pow2_prop :
  is_stable clean_pow2_func.
intros [x|x|x y|o x|o x y|x|x] ; try apply refl_equal.
simpl.
apply Gappa_round_aux.float2_pow2.
Qed.

Definition clean_pow2 := mkTF clean_pow2_func clean_pow2_prop.

(* compute on constant terms, so that they are hopefully represented by a single float *)
Definition merge_float2_func t :=
  match t with
  | reInteger x => reFloat2 x 0
  | reUnary uoNeg (reFloat2 x y) => reFloat2 (- x) y
  | reBinary boMul (reFloat2 x1 y1) (reFloat2 x2 y2) => reFloat2 (x1 * x2) (y1 + y2)
  | _ => t
  end.

Lemma merge_float2_prop :
  is_stable merge_float2_func.
intros [x|x|x y|o x|o x y|x|x] ; try apply refl_equal.
(* unary ops *)
destruct o ; try apply refl_equal.
destruct x ; try apply refl_equal.
simpl.
rewrite <- Gappa_dyadic.Fopp2_correct.
apply refl_equal.
(* binary ops *)
destruct o ; try apply refl_equal.
destruct x ; try apply refl_equal.
destruct y ; try apply refl_equal.
simpl.
rewrite <- Gappa_dyadic.Fmult2_correct.
apply refl_equal.
Qed.

Definition merge_float2 := mkTF merge_float2_func merge_float2_prop.

(* some dummy definition to ensure precise rewriting of the terms and termination *)
Definition convertTODO1 := convert.
Definition convertTODO2 := convert.
Definition convertTODO3 := convert.
Definition reUnknownTODO := reUnknown.

(* produce a compatible goal where all the Gappa-usable enclosures have been converted,
   some integers may no longer be closed terms, but they can be evaluated to closed terms *)
Ltac gappa_prepare :=
  intros ; subst ;
  let trans_expr := constr:(gen_float2 :: clean_pow2 :: nil) in
  let trans_bound := constr:(gen_float2 :: clean_pow2 :: merge_float2 :: nil) in
  (* - get an inductive object for the bounded expression without any INR, INZ, powerRZ 2
     - same for the bounds, but try harder to get single floats *)
  match goal with
  | |- (?a <= ?e <= ?b)%R =>
    let a' := get_inductive_term a in
    let b' := get_inductive_term b in
    let e' := get_inductive_term e in
    change (convertTODO1 a' <= convertTODO2 e' <= convertTODO3 b')%R ;
    let w := eval simpl in (multi_transform trans_bound a') in
    replace (convertTODO1 a') with (convert w) ; [idtac | exact (multi_transform_correct trans_bound a')] ;
    let w := eval simpl in (multi_transform trans_bound b') in
    replace (convertTODO3 b') with (convert w) ; [idtac | exact (multi_transform_correct trans_bound b')] ;
    let w := eval simpl in (multi_transform trans_expr e') in
    replace (convertTODO2 e') with (convert w) ; [idtac | exact (multi_transform_correct trans_expr e')]
  end ;
  (* apply the same transformation to the hypotheses and move them to the goal *)
  repeat
  match goal with
  | H: (?a <= ?e <= ?b)%R |- _ =>
    let a' := get_inductive_term a in
    let b' := get_inductive_term b in
    let e' := get_inductive_term e in
    change (convertTODO1 a' <= convertTODO2 e' <= convertTODO3 b')%R in H ;
    generalize H ; clear H ;
    let w := eval simpl in (multi_transform trans_bound a') in
    replace (convertTODO1 a') with (convert w) ; [idtac | exact (multi_transform_correct trans_bound a')] ;
    let w := eval simpl in (multi_transform trans_bound b') in
    replace (convertTODO3 b') with (convert w) ; [idtac | exact (multi_transform_correct trans_bound b')] ;
    let w := eval simpl in (multi_transform trans_expr e') in
    replace (convertTODO2 e') with (convert w) ; [idtac | exact (multi_transform_correct trans_expr e')]
  end ;
  (* generalize any unrecognized expression *)
  change reUnknown with reUnknownTODO ;
  repeat
  match goal with
  | z: R |- _ =>
    match goal with
    | |- context [reUnknownTODO z] =>
      change (reUnknownTODO z) with (reUnknown z)
    end
  | |- context [reUnknownTODO ?z] =>
    change (reUnknownTODO z) with (reUnknown z) ;
    generalize z ; intro
  end ;
  intros.

(*
Goal
  forall y x,
  (1 <= x + INR 7 * (y * sin y) <= IZR 12/16 * powerRZ 2 3)%R ->
  (1 <= sqrt x <= 3/2)%R.
gappa_prepare.
*)
