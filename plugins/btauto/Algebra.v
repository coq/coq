Require Import Bool PArith DecidableClass Omega Lia.

Ltac bool :=
repeat match goal with
| [ H : ?P && ?Q = true |- _ ] =>
  apply andb_true_iff in H; destruct H
| |- ?P && ?Q = true =>
  apply <- andb_true_iff; split
end.

Arguments decide P /H.

Hint Extern 5 => progress bool.

Ltac define t x H :=
set (x := t) in *; assert (H : t = x) by reflexivity; clearbody x.

Lemma Decidable_sound : forall P (H : Decidable P),
                          decide P = true -> P.
Proof.
intros P H Hp; apply -> Decidable_spec; assumption.
Qed.

Lemma Decidable_complete : forall P (H : Decidable P),
  P -> decide P = true.
Proof.
intros P H Hp; apply <- Decidable_spec; assumption.
Qed.

Lemma Decidable_sound_alt : forall P (H : Decidable P),
   ~ P -> decide P = false.
Proof.
intros P [wit spec] Hd; destruct wit; simpl; tauto. 
Qed.

Lemma Decidable_complete_alt : forall P (H : Decidable P),
  decide P = false -> ~ P.
Proof.
  intros P [wit spec] Hd Hc; simpl in *; intuition congruence.
Qed.

Ltac try_rewrite :=
repeat match goal with
| [ H : ?P |- _ ] => rewrite H
end.

(* We opacify here decide for proofs, and will make it transparent for
   reflexive tactics later on. *)

Global Opaque decide.

Ltac tac_decide :=
match goal with
| [ H : @decide ?P ?D = true |- _ ] => apply (@Decidable_sound P D) in H
| [ H : @decide ?P ?D = false |- _ ] => apply (@Decidable_complete_alt P D) in H
| [ |- @decide ?P ?D = true ] => apply (@Decidable_complete P D)
| [ |- @decide ?P ?D = false ] => apply (@Decidable_sound_alt P D)
| [ |- negb ?b = true ] => apply negb_true_iff
| [ |- negb ?b = false ] => apply negb_false_iff
| [ H : negb ?b = true |- _ ] => apply negb_true_iff in H
| [ H : negb ?b = false |- _ ] => apply negb_false_iff in H
end.

Ltac try_decide := repeat tac_decide.

Ltac make_decide P := match goal with
| [ |- context [@decide P ?D] ] =>
  let b := fresh "b" in
  let H := fresh "H" in
  define (@decide P D) b H; destruct b; try_decide
| [ X : context [@decide P ?D] |- _ ] =>
  let b := fresh "b" in
  let H := fresh "H" in
  define (@decide P D) b H; destruct b; try_decide
end.

Ltac case_decide := match goal with
| [ |- context [@decide ?P ?D] ] =>
  let b := fresh "b" in
  let H := fresh "H" in
  define (@decide P D) b H; destruct b; try_decide
| [ X : context [@decide ?P ?D] |- _ ] =>
  let b := fresh "b" in
  let H := fresh "H" in
  define (@decide P D) b H; destruct b; try_decide
| [ |- context [Pos.compare ?x ?y] ] =>
  destruct (Pos.compare_spec x y); try lia
| [ X : context [Pos.compare ?x ?y] |- _ ] =>
  destruct (Pos.compare_spec x y); try lia
end.

Section Definitions.

(** * Global, inductive definitions. *)

(** A Horner polynomial is either a constant, or a product P × (i + Q), where i 
  is a variable. *)

Inductive poly :=
| Cst : bool -> poly
| Poly : poly -> positive -> poly -> poly.

(* TODO: We should use [positive] instead of [nat] to encode variables, for 
 efficiency purpose. *)

Inductive null : poly -> Prop :=
| null_intro : null (Cst false).

(** Polynomials satisfy a uniqueness condition whenever they are valid. A 
  polynomial [p] satisfies [valid n p] whenever it is well-formed and each of 
  its variable indices is < [n]. *)

Inductive valid : positive -> poly -> Prop :=
| valid_cst : forall k c, valid k (Cst c)
| valid_poly : forall k p i q,
  Pos.lt i k -> ~ null q -> valid i p -> valid (Pos.succ i) q -> valid k (Poly p i q).

(** Linear polynomials are valid polynomials in which every variable appears at 
  most once. *)

Inductive linear : positive -> poly -> Prop :=
| linear_cst : forall k c, linear k (Cst c)
| linear_poly : forall k p i q, Pos.lt i k -> ~ null q ->
  linear i p -> linear i q -> linear k (Poly p i q).

End Definitions.

Section Computational.

Program Instance Decidable_PosEq : forall (p q : positive), Decidable (p = q) :=
  { Decidable_witness := Pos.eqb p q }.
Next Obligation.
apply Pos.eqb_eq.
Qed.

Program Instance Decidable_PosLt : forall p q, Decidable (Pos.lt p q) :=
  { Decidable_witness := Pos.ltb p q }.
Next Obligation.
apply Pos.ltb_lt.
Qed.

Program Instance Decidable_PosLe : forall p q, Decidable (Pos.le p q) :=
  { Decidable_witness := Pos.leb p q }.
Next Obligation.
apply Pos.leb_le.
Qed.

(** * The core reflexive part. *)

Hint Constructors valid.

Fixpoint beq_poly pl pr :=
match pl with
| Cst cl =>
  match pr with
  | Cst cr => decide (cl = cr)
  | Poly _ _ _ => false
  end
| Poly pl il ql =>
  match pr with
  | Cst _ => false
  | Poly pr ir qr =>
    decide (il = ir) && beq_poly pl pr && beq_poly ql qr
  end
end.

(* We could do that with [decide equality] but dependency in proofs is heavy *)
Program Instance Decidable_eq_poly : forall (p q : poly), Decidable (eq p q) := {
  Decidable_witness := beq_poly p q
}.

Next Obligation.
split.
revert q; induction p; intros [] ?; simpl in *; bool; try_decide;
  f_equal; first [intuition congruence|auto].
revert q; induction p; intros [] Heq; simpl in *; bool; try_decide; intuition;
  try injection Heq; first[congruence|intuition].
Qed.

Program Instance Decidable_null : forall p, Decidable (null p) := {
  Decidable_witness := match p with Cst false => true | _ => false end
}.
Next Obligation.
split.
  destruct p as [[]|]; first [discriminate|constructor].
  inversion 1; trivial.
Qed.

Definition list_nth {A} p (l : list A) def :=
  Pos.peano_rect (fun _ => list A -> A)
    (fun l => match l with nil => def | cons t l => t end)
    (fun _ F l => match l with nil => def | cons t l => F l end) p l.

Fixpoint eval var (p : poly) :=
match p with
| Cst c => c
| Poly p i q =>
  let vi := list_nth i var false in
  xorb (eval var p) (andb vi (eval var q))
end.

Fixpoint valid_dec k p :=
match p with
| Cst c => true
| Poly p i q =>
  negb (decide (null q)) && decide (i < k)%positive &&
    valid_dec i p && valid_dec (Pos.succ i) q
end.

Program Instance Decidable_valid : forall n p, Decidable (valid n p) := {
  Decidable_witness := valid_dec n p
}.
Next Obligation.
split.
  revert n; induction p; unfold valid_dec in *; intuition; bool; try_decide; auto.
  intros H; induction H; unfold valid_dec in *; bool; try_decide; auto.
Qed.

(** Basic algebra *)

(* Addition of polynomials *)

Fixpoint poly_add pl {struct pl} :=
match pl with
| Cst cl =>
  fix F pr := match pr with
  | Cst cr => Cst (xorb cl cr)
  | Poly pr ir qr => Poly (F pr) ir qr
  end
| Poly pl il ql =>
  fix F pr {struct pr} := match pr with
  | Cst cr => Poly (poly_add pl pr) il ql
  | Poly pr ir qr =>
    match Pos.compare il ir with
    | Eq =>
      let qs := poly_add ql qr in
      (* Ensure validity *)
      if decide (null qs) then poly_add pl pr
      else Poly (poly_add pl pr) il qs
    | Gt => Poly (poly_add pl (Poly pr ir qr)) il ql
    | Lt => Poly (F pr) ir qr
    end
  end
end.

(* Multiply a polynomial by a constant *)

Fixpoint poly_mul_cst v p :=
match p with
| Cst c => Cst (andb c v)
| Poly p i q =>
  let r := poly_mul_cst v q in
  (* Ensure validity *)
  if decide (null r) then poly_mul_cst v p
  else Poly (poly_mul_cst v p) i r
end.

(* Multiply a polynomial by a monomial *)

Fixpoint poly_mul_mon k p :=
match p with
| Cst c =>
  if decide (null p) then p
  else Poly (Cst false) k p
| Poly p i q =>
  if decide (i <= k)%positive then Poly (Cst false) k (Poly p i q)
  else Poly (poly_mul_mon k p) i (poly_mul_mon k q)
end.

(* Multiplication of polynomials *)

Fixpoint poly_mul pl {struct pl} :=
match pl with
| Cst cl => poly_mul_cst cl
| Poly pl il ql =>
  fun pr =>
    (* Multiply by a factor *)
    let qs := poly_mul ql pr in
    (* Ensure validity *)
    if decide (null qs) then poly_mul pl pr
    else poly_add (poly_mul pl pr) (poly_mul_mon il qs)
end.

(** Quotienting a polynomial by the relation X_i^2 ~ X_i *)

(* Remove the multiple occurrences of monomials x_k *)

Fixpoint reduce_aux k p :=
match p with
| Cst c => Cst c
| Poly p i q =>
  if decide (i = k) then poly_add (reduce_aux k p) (reduce_aux k q)
  else
    let qs := reduce_aux i q in
    (* Ensure validity *)
    if decide (null qs) then (reduce_aux k p)
    else Poly (reduce_aux k p) i qs
end.

(* Rewrite any x_k ^ {n + 1} to x_k *)

Fixpoint reduce p :=
match p with
| Cst c => Cst c
| Poly p i q =>
  let qs := reduce_aux i q in
  (* Ensure validity *)
  if decide (null qs) then reduce p
  else Poly (reduce p) i qs
end.

End Computational.

Section Validity.

(* Decision procedure of validity *)

Hint Constructors valid linear.

Lemma valid_le_compat : forall k l p, valid k p -> (k <= l)%positive -> valid l p.
Proof.
intros k l p H Hl; induction H; constructor; eauto.
now eapply Pos.lt_le_trans; eassumption.
Qed.

Lemma linear_le_compat : forall k l p, linear k p -> (k <= l)%positive -> linear l p.
Proof.
intros k l p H; revert l; induction H; constructor; eauto; lia.
Qed.

Lemma linear_valid_incl : forall k p, linear k p -> valid k p.
Proof.
intros k p H; induction H; constructor; auto.
eapply valid_le_compat; eauto; lia.
Qed.

End Validity.

Section Evaluation.

(* Useful simple properties *)

Lemma eval_null_zero : forall p var, null p -> eval var p = false.
Proof.
intros p var []; reflexivity.
Qed.

Lemma eval_extensional_eq_compat : forall p var1 var2,
  (forall x, list_nth x var1 false = list_nth x var2 false) -> eval var1 p = eval var2 p.
Proof.
intros p var1 var2 H; induction p; simpl; try_rewrite; auto.
Qed.

Lemma eval_suffix_compat : forall k p var1 var2,
  (forall i, (i < k)%positive -> list_nth i var1 false = list_nth i var2 false) -> valid k p ->
  eval var1 p = eval var2 p.
Proof.
intros k p var1 var2 Hvar Hv; revert var1 var2 Hvar.
induction Hv; intros var1 var2 Hvar; simpl; [now auto|].
rewrite Hvar; [|now auto]; erewrite (IHHv1 var1 var2).
  + erewrite (IHHv2 var1 var2); [ring|].
    intros; apply Hvar; zify; omega.
  + intros; apply Hvar; zify; omega.
Qed.

End Evaluation.

Section Algebra.

(* Compatibility with evaluation *)

Lemma poly_add_compat : forall pl pr var, eval var (poly_add pl pr) = xorb (eval var pl) (eval var pr).
Proof.
intros pl; induction pl; intros pr var; simpl.
+ induction pr; simpl; auto; solve [try_rewrite; ring].
+ induction pr; simpl; auto; try solve [try_rewrite; simpl; ring].
  destruct (Pos.compare_spec p p0); repeat case_decide; simpl; first [try_rewrite; ring|idtac].
    try_rewrite; ring_simplify; repeat rewrite xorb_assoc.
    match goal with [ |- context [xorb (andb ?b1 ?b2) (andb ?b1 ?b3)] ] =>
      replace (xorb (andb b1 b2) (andb b1 b3)) with (andb b1 (xorb b2 b3)) by ring
    end.
    rewrite <- IHpl2.
    match goal with [ H : null ?p |- _ ] => rewrite (eval_null_zero _ _ H) end; ring.
    simpl; rewrite IHpl1; simpl; ring.
Qed.

Lemma poly_mul_cst_compat : forall v p var,
  eval var (poly_mul_cst v p) = andb v (eval var p).
Proof.
intros v p; induction p; intros var; simpl; [ring|].
case_decide; simpl; try_rewrite; [ring_simplify|ring].
replace (v && list_nth p2 var false && eval var p3) with (list_nth p2 var false && (v && eval var p3)) by ring.
rewrite <- IHp2; inversion H; simpl; ring.
Qed.

Lemma poly_mul_mon_compat : forall i p var,
  eval var (poly_mul_mon i p) = (list_nth i var false && eval var p).
Proof.
intros i p var; induction p; simpl; case_decide; simpl; try_rewrite; try ring.
inversion H; ring.
match goal with [ |- ?u = ?t ] => set (x := t); destruct x; reflexivity end.
match goal with [ |- ?u = ?t ] => set (x := t); destruct x; reflexivity end.
Qed.

Lemma poly_mul_compat : forall pl pr var, eval var (poly_mul pl pr) = andb (eval var pl) (eval var pr).
Proof.
intros pl; induction pl; intros pr var; simpl.
  apply poly_mul_cst_compat.
  case_decide; simpl.
    rewrite IHpl1; ring_simplify.
    replace (eval var pr && list_nth p var false && eval var pl2)
    with (list_nth p var false && (eval var pl2 && eval var pr)) by ring.
    now rewrite <- IHpl2; inversion H; simpl; ring.
    rewrite poly_add_compat, poly_mul_mon_compat, IHpl1, IHpl2; ring.
Qed.

Hint Extern 5 =>
match goal with
| [ |- (Pos.max ?x ?y <= ?z)%positive ] =>
  apply Pos.max_case_strong; intros; lia
| [ |- (?z <= Pos.max ?x ?y)%positive ] =>
  apply Pos.max_case_strong; intros; lia
| [ |- (Pos.max ?x ?y < ?z)%positive ] =>
  apply Pos.max_case_strong; intros; lia
| [ |- (?z < Pos.max ?x ?y)%positive ] =>
  apply Pos.max_case_strong; intros; lia
| _ => zify; omega
end.
Hint Resolve Pos.le_max_r Pos.le_max_l.

Hint Constructors valid linear.

(* Compatibility of validity w.r.t algebraic operations *)

Lemma poly_add_valid_compat : forall kl kr pl pr, valid kl pl -> valid kr pr ->
  valid (Pos.max kl kr) (poly_add pl pr).
Proof.
intros kl kr pl pr Hl Hr; revert kr pr Hr; induction Hl; intros kr pr Hr; simpl.
{ eapply valid_le_compat; [clear k|apply Pos.le_max_r].
  now induction Hr; auto. }
{  assert (Hle : (Pos.max (Pos.succ i) kr <= Pos.max k kr)%positive) by auto.
  apply (valid_le_compat (Pos.max (Pos.succ i) kr)); [|assumption].
  clear - IHHl1 IHHl2 Hl2 Hr H0; induction Hr.
    constructor; auto.
      now rewrite <- (Pos.max_id i); intuition.
    destruct (Pos.compare_spec i i0); subst; try case_decide; repeat (constructor; intuition).
      + apply (valid_le_compat (Pos.max i0 i0)); [now auto|]; rewrite Pos.max_id; auto.
      + apply (valid_le_compat (Pos.max i0 i0)); [now auto|]; rewrite Pos.max_id; lia.
      + apply (valid_le_compat (Pos.max (Pos.succ i0) (Pos.succ i0))); [now auto|]; rewrite Pos.max_id; lia.
      + apply (valid_le_compat (Pos.max (Pos.succ i) i0)); intuition.
      + apply (valid_le_compat (Pos.max i (Pos.succ i0))); intuition.
}
Qed.

Lemma poly_mul_cst_valid_compat : forall k v p, valid k p -> valid k (poly_mul_cst v p).
Proof.
intros k v p H; induction H; simpl; [now auto|].
case_decide; [|now auto].
eapply (valid_le_compat i); [now auto|lia].
Qed.

Lemma poly_mul_mon_null_compat : forall i p, null (poly_mul_mon i p) -> null p.
Proof.
intros i p; induction p; simpl; case_decide; simpl; inversion 1; intuition.
Qed.

Lemma poly_mul_mon_valid_compat : forall k i p,
  valid k p -> valid (Pos.max (Pos.succ i) k) (poly_mul_mon i p).
Proof.
intros k i p H; induction H; simpl poly_mul_mon; case_decide; intuition.
+ apply (valid_le_compat (Pos.succ i)); auto; constructor; intuition.
  - match goal with [ H : null ?p |- _ ] => solve[inversion H] end.
+ apply (valid_le_compat k); auto; constructor; intuition.
  - assert (X := poly_mul_mon_null_compat); intuition eauto.
  - cutrewrite <- (Pos.max (Pos.succ i) i0 = i0); intuition.
  - cutrewrite <- (Pos.max (Pos.succ i) (Pos.succ i0) = Pos.succ i0); intuition.
Qed.

Lemma poly_mul_valid_compat : forall kl kr pl pr, valid kl pl -> valid kr pr ->
  valid (Pos.max kl kr) (poly_mul pl pr).
Proof.
intros kl kr pl pr Hl Hr; revert kr pr Hr.
induction Hl; intros kr pr Hr; simpl.
+ apply poly_mul_cst_valid_compat; auto.
  apply (valid_le_compat kr); now auto.
+ apply (valid_le_compat (Pos.max (Pos.max i kr) (Pos.max (Pos.succ i) (Pos.max (Pos.succ i) kr)))).
  - case_decide.
    { apply (valid_le_compat (Pos.max i kr)); auto. }
    { apply poly_add_valid_compat; auto.
      now apply poly_mul_mon_valid_compat; intuition. }
  - repeat apply Pos.max_case_strong; zify; omega.
Qed.

(* Compatibility of linearity wrt to linear operations *)

Lemma poly_add_linear_compat : forall kl kr pl pr, linear kl pl -> linear kr pr ->
  linear (Pos.max kl kr) (poly_add pl pr).
Proof.
intros kl kr pl pr Hl; revert kr pr; induction Hl; intros kr pr Hr; simpl.
+ apply (linear_le_compat kr); [|apply Pos.max_case_strong; zify; omega].
  now induction Hr; constructor; auto.
+ apply (linear_le_compat (Pos.max kr (Pos.succ i))); [|now auto].
  induction Hr; simpl.
  - constructor; auto.
    replace i with (Pos.max i i) by (apply Pos.max_id); intuition.
  - destruct (Pos.compare_spec i i0); subst; try case_decide; repeat (constructor; intuition).
    { apply (linear_le_compat (Pos.max i0 i0)); [now auto|]; rewrite Pos.max_id; auto. }
    { apply (linear_le_compat (Pos.max i0 i0)); [now auto|]; rewrite Pos.max_id; auto. }
    { apply (linear_le_compat (Pos.max i0 i0)); [now auto|]; rewrite Pos.max_id; auto. }
    { apply (linear_le_compat (Pos.max i0 (Pos.succ i))); intuition. }
    { apply (linear_le_compat (Pos.max i (Pos.succ i0))); intuition. }
Qed.

End Algebra.

Section Reduce.

(* A stronger version of the next lemma *)

Lemma reduce_aux_eval_compat : forall k p var, valid (Pos.succ k) p ->
  (list_nth k var false && eval var (reduce_aux k p) = list_nth k var false && eval var p).
Proof.
intros k p var; revert k; induction p; intros k Hv; simpl; auto.
inversion Hv; case_decide; subst.
+ rewrite poly_add_compat; ring_simplify.
  specialize (IHp1 k); specialize (IHp2 k).
  destruct (list_nth k var false); ring_simplify; [|now auto].
  rewrite <- (andb_true_l (eval var p1)), <- (andb_true_l (eval var p3)).
  rewrite <- IHp2; auto; rewrite <- IHp1; [ring|].
  apply (valid_le_compat k); [now auto|zify; omega].
+ remember (list_nth k var false) as b; destruct b; ring_simplify; [|now auto].
  case_decide; simpl.
  - rewrite <- (IHp2 p2); [inversion H|now auto]; simpl.
    replace (eval var p1) with (list_nth k var false && eval var p1) by (rewrite <- Heqb; ring); rewrite <- (IHp1 k).
    { rewrite <- Heqb; ring. }
    { apply (valid_le_compat p2); [auto|zify; omega]. }
  - rewrite (IHp2 p2); [|now auto].
    replace (eval var p1) with (list_nth k var false && eval var p1) by (rewrite <- Heqb; ring).
    rewrite <- (IHp1 k); [rewrite <- Heqb; ring|].
    apply (valid_le_compat p2); [auto|zify; omega].
Qed.

(* Reduction preserves evaluation by boolean assignations *)

Lemma reduce_eval_compat : forall k p var, valid k p ->
  eval var (reduce p) = eval var p.
Proof.
intros k p var H; induction H; simpl; auto.
case_decide; try_rewrite; simpl.
+ rewrite <- reduce_aux_eval_compat; auto; inversion H3; simpl; ring.
+ repeat rewrite reduce_aux_eval_compat; try_rewrite; now auto.
Qed.

Lemma reduce_aux_le_compat : forall k l p, valid k p -> (k <= l)%positive ->
  reduce_aux l p = reduce_aux k p.
Proof.
intros k l p; revert k l; induction p; intros k l H Hle; simpl; auto.
inversion H; subst; repeat case_decide; subst; try (exfalso; zify; omega).
+ apply IHp1; [|now auto]; eapply valid_le_compat; [eauto|zify; omega].
+ f_equal; apply IHp1; auto.
  now eapply valid_le_compat; [eauto|zify; omega].
Qed.

(* Reduce projects valid polynomials into linear ones *)

Lemma linear_reduce_aux : forall i p, valid (Pos.succ i) p -> linear i (reduce_aux i p).
Proof.
intros i p; revert i; induction p; intros i Hp; simpl.
+ constructor.
+ inversion Hp; subst; case_decide; subst.
  - rewrite <- (Pos.max_id i) at 1; apply poly_add_linear_compat.
    { apply IHp1; eapply valid_le_compat; [eassumption|zify; omega]. }
    { intuition. }
  - case_decide.
  { apply IHp1; eapply valid_le_compat; [eauto|zify; omega]. }
  { constructor; try (zify; omega); auto.
    erewrite (reduce_aux_le_compat p2); [|assumption|zify; omega].
    apply IHp1; eapply valid_le_compat; [eauto|]; zify; omega. }
Qed.

Lemma linear_reduce : forall k p, valid k p -> linear k (reduce p).
Proof.
intros k p H; induction H; simpl.
+ now constructor.
+ case_decide.
  - eapply linear_le_compat; [eauto|zify; omega].
  - constructor; auto.
    apply linear_reduce_aux; auto.
Qed.

End Reduce.
