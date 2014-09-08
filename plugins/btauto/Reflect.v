Require Import Bool DecidableClass Algebra Ring PArith ROmega Omega.

Section Bool.

(* Boolean formulas and their evaluations *)

Inductive formula :=
| formula_var : positive -> formula
| formula_btm : formula
| formula_top : formula
| formula_cnj : formula -> formula -> formula
| formula_dsj : formula -> formula -> formula
| formula_neg : formula -> formula
| formula_xor : formula -> formula -> formula
| formula_ifb : formula -> formula -> formula -> formula.

Fixpoint formula_eval var f := match f with
| formula_var x => list_nth x var false 
| formula_btm => false
| formula_top => true
| formula_cnj fl fr => (formula_eval var fl) && (formula_eval var fr)
| formula_dsj fl fr => (formula_eval var fl) || (formula_eval var fr)
| formula_neg f => negb (formula_eval var f)
| formula_xor fl fr => xorb (formula_eval var fl) (formula_eval var fr)
| formula_ifb fc fl fr =>
  if formula_eval var fc then formula_eval var fl else formula_eval var fr
end.

End Bool.

(* Translation of formulas into polynomials *)

Section Translation.

(* This is straightforward. *)

Fixpoint poly_of_formula f := match f with
| formula_var x => Poly (Cst false) x (Cst true) 
| formula_btm => Cst false
| formula_top => Cst true
| formula_cnj fl fr =>
  let pl := poly_of_formula fl in
  let pr := poly_of_formula fr in
  poly_mul pl pr
| formula_dsj fl fr =>
  let pl := poly_of_formula fl in
  let pr := poly_of_formula fr in
  poly_add (poly_add pl pr) (poly_mul pl pr)
| formula_neg f => poly_add (Cst true) (poly_of_formula f)
| formula_xor fl fr => poly_add (poly_of_formula fl) (poly_of_formula fr)
| formula_ifb fc fl fr =>
  let pc := poly_of_formula fc in
  let pl := poly_of_formula fl in
  let pr := poly_of_formula fr in
  poly_add pr (poly_add (poly_mul pc pl) (poly_mul pc pr))
end.

Opaque poly_add.

(* Compatibility of translation wrt evaluation *)

Lemma poly_of_formula_eval_compat : forall var f,
  eval var (poly_of_formula f) = formula_eval var f.
Proof.
intros var f; induction f; simpl poly_of_formula; simpl formula_eval; auto.
  now simpl; match goal with [ |- ?t = ?u ] => destruct u; reflexivity end.
  rewrite poly_mul_compat, IHf1, IHf2; ring.
  repeat rewrite poly_add_compat.
  rewrite poly_mul_compat; try_rewrite.
  now match goal with [ |- ?t = ?x || ?y ] => destruct x; destruct y; reflexivity end.
  rewrite poly_add_compat; try_rewrite.
  now match goal with [ |- ?t = negb ?x ] => destruct x; reflexivity end.
  rewrite poly_add_compat; congruence.
  rewrite ?poly_add_compat, ?poly_mul_compat; try_rewrite.
  match goal with
    [ |- ?t = if ?b1 then ?b2 else ?b3 ] => destruct b1; destruct b2; destruct b3; reflexivity
  end.
Qed.

Hint Extern 5 => change 0 with (min 0 0).
Local Hint Resolve poly_add_valid_compat poly_mul_valid_compat.
Local Hint Constructors valid.
Hint Extern 5 => zify; omega.

(* Compatibility with validity *)

Lemma poly_of_formula_valid_compat : forall f, exists n, valid n (poly_of_formula f).
Proof.
intros f; induction f; simpl.
+ exists (Pos.succ p); constructor; intuition; inversion H.
+ exists 1%positive; auto.
+ exists 1%positive; auto.
+ destruct IHf1 as [n1 Hn1]; destruct IHf2 as [n2 Hn2]; exists (Pos.max n1 n2); auto.
+ destruct IHf1 as [n1 Hn1]; destruct IHf2 as [n2 Hn2]; exists (Pos.max (Pos.max n1 n2) (Pos.max n1 n2)); auto.
+ destruct IHf as [n Hn]; exists (Pos.max 1 n); auto.
+ destruct IHf1 as [n1 Hn1]; destruct IHf2 as [n2 Hn2]; exists (Pos.max n1 n2); auto.
+ destruct IHf1 as [n1 Hn1]; destruct IHf2 as [n2 Hn2]; destruct IHf3 as [n3 Hn3]; eexists; eauto.
Qed.

(* The soundness lemma ; alas not complete! *)

Lemma poly_of_formula_sound : forall fl fr var,
  poly_of_formula fl = poly_of_formula fr -> formula_eval var fl = formula_eval var fr.
Proof.
intros fl fr var Heq.
repeat rewrite <- poly_of_formula_eval_compat.
rewrite Heq; reflexivity.
Qed.

End Translation.

Section Completeness.

(* Lemma reduce_poly_of_formula_simpl : forall fl fr var,
  simpl_eval (var_of_list var) (reduce (poly_of_formula fl)) = simpl_eval (var_of_list var) (reduce (poly_of_formula fr)) ->
  formula_eval var fl = formula_eval var fr.
Proof.
intros fl fr var Hrw.
do 2 rewrite <- poly_of_formula_eval_compat.
destruct (poly_of_formula_valid_compat fl) as [nl Hl].
destruct (poly_of_formula_valid_compat fr) as [nr Hr].
rewrite <- (reduce_eval_compat nl (poly_of_formula fl)); [|assumption].
rewrite <- (reduce_eval_compat nr (poly_of_formula fr)); [|assumption].
do 2 rewrite <- eval_simpl_eval_compat; assumption.
Qed. *)

(* Soundness of the method ; immediate *)

Lemma reduce_poly_of_formula_sound : forall fl fr var,
  reduce (poly_of_formula fl) = reduce (poly_of_formula fr) ->
  formula_eval var fl = formula_eval var fr.
Proof.
intros fl fr var Heq.
repeat rewrite <- poly_of_formula_eval_compat.
destruct (poly_of_formula_valid_compat fl) as [nl Hl].
destruct (poly_of_formula_valid_compat fr) as [nr Hr].
rewrite <- (reduce_eval_compat nl (poly_of_formula fl)); auto.
rewrite <- (reduce_eval_compat nr (poly_of_formula fr)); auto.
rewrite Heq; reflexivity.
Qed.

Definition make_last {A} n (x def : A) :=
  Pos.peano_rect (fun _ => list A)
    (cons x nil)
    (fun _ F => cons def F) n.

(* Replace the nth element of a list *)

Fixpoint list_replace l n b :=
match l with
| nil => make_last n b false
| cons a l =>
  Pos.peano_rect _
    (cons b l) (fun n _ => cons a (list_replace l n b)) n
end.

(** Extract a non-null witness from a polynomial *)

Existing Instance Decidable_null.

Fixpoint boolean_witness p :=
match p with
| Cst c => nil
| Poly p i q =>
  if decide (null p) then
    let var := boolean_witness q in
    list_replace var i true
  else
    let var := boolean_witness p in
    list_replace var i false
end.

Lemma list_nth_base : forall A (def : A) l,
  list_nth 1 l def = match l with nil => def | cons x _ => x end.
Proof.
intros A def l; unfold list_nth.
rewrite Pos.peano_rect_base; reflexivity.
Qed.

Lemma list_nth_succ : forall A n (def : A) l,
  list_nth (Pos.succ n) l def =
    match l with nil => def | cons _ l => list_nth n l def end.
Proof.
intros A def l; unfold list_nth.
rewrite Pos.peano_rect_succ; reflexivity.
Qed.

Lemma list_nth_nil : forall A n (def : A),
  list_nth n nil def = def.
Proof.
intros A n def; induction n using Pos.peano_rect.
+ rewrite list_nth_base; reflexivity.
+ rewrite list_nth_succ; reflexivity.
Qed.

Lemma make_last_nth_1 : forall A n i x def, i <> n ->
  list_nth i (@make_last A n x def) def = def.
Proof.
intros A n; induction n using Pos.peano_rect; intros i x def Hd;
  unfold make_last; simpl.
+ induction i using Pos.peano_case; [elim Hd; reflexivity|].
  rewrite list_nth_succ, list_nth_nil; reflexivity.
+ unfold make_last; rewrite Pos.peano_rect_succ; fold (make_last n x def).
  induction i using Pos.peano_case.
  - rewrite list_nth_base; reflexivity.
  - rewrite list_nth_succ; apply IHn; zify; omega.
Qed.

Lemma make_last_nth_2 : forall A n x def, list_nth n (@make_last A n x def) def = x.
Proof.
intros A n; induction n using Pos.peano_rect; intros x def; simpl.
+ reflexivity.
+ unfold make_last; rewrite Pos.peano_rect_succ; fold (make_last n x def).
  rewrite list_nth_succ; auto.
Qed.

Lemma list_replace_nth_1 : forall var i j x, i <> j ->
  list_nth i (list_replace var j x) false = list_nth i var false.
Proof.
intros var; induction var; intros i j x Hd; simpl.
+ rewrite make_last_nth_1, list_nth_nil; auto.
+ induction j using Pos.peano_rect.
  - rewrite Pos.peano_rect_base.
    induction i using Pos.peano_rect; [now elim Hd; auto|].
    rewrite 2list_nth_succ; reflexivity.
  - rewrite Pos.peano_rect_succ.
    induction i using Pos.peano_rect.
    { rewrite 2list_nth_base; reflexivity. }
    { rewrite 2list_nth_succ; apply IHvar; zify; omega. }
Qed.

Lemma list_replace_nth_2 : forall var i x, list_nth i (list_replace var i x) false = x.
Proof.
intros var; induction var; intros i x; simpl.
+ now apply make_last_nth_2.
+ induction i using Pos.peano_rect.
  - rewrite Pos.peano_rect_base, list_nth_base; reflexivity.
  - rewrite Pos.peano_rect_succ, list_nth_succ; auto.
Qed.

(* The witness is correct only if the polynomial is linear *)

Lemma boolean_witness_nonzero : forall k p, linear k p -> ~ null p ->
  eval (boolean_witness p) p = true.
Proof.
intros k p Hl Hp; induction Hl; simpl.
  destruct c; [reflexivity|elim Hp; now constructor].
  case_decide.
    rewrite eval_null_zero; [|assumption]; rewrite list_replace_nth_2; simpl.
    match goal with [ |- (if ?b then true else false) = true ] =>
      assert (Hrw : b = true); [|rewrite Hrw; reflexivity]
    end.
    erewrite eval_suffix_compat; [now eauto| |now apply linear_valid_incl; eauto].
    now intros j Hd; apply list_replace_nth_1; zify; omega.
    rewrite list_replace_nth_2, xorb_false_r.
    erewrite eval_suffix_compat; [now eauto| |now apply linear_valid_incl; eauto].
    now intros j Hd; apply list_replace_nth_1; zify; omega.
Qed.

(* This should be better when using the [vm_compute] tactic instead of plain reflexivity. *)

Lemma reduce_poly_of_formula_sound_alt : forall var fl fr,
  reduce (poly_add (poly_of_formula fl) (poly_of_formula fr)) = Cst false ->
  formula_eval var fl = formula_eval var fr.
Proof.
intros var fl fr Heq.
repeat rewrite <- poly_of_formula_eval_compat.
destruct (poly_of_formula_valid_compat fl) as [nl Hl].
destruct (poly_of_formula_valid_compat fr) as [nr Hr].
rewrite <- (reduce_eval_compat nl (poly_of_formula fl)); auto.
rewrite <- (reduce_eval_compat nr (poly_of_formula fr)); auto.
rewrite <- xorb_false_l; change false with (eval var (Cst false)).
rewrite <- poly_add_compat, <- Heq.
repeat rewrite poly_add_compat.
rewrite (reduce_eval_compat nl); [|assumption].
rewrite (reduce_eval_compat (Pos.max nl nr)); [|apply poly_add_valid_compat; assumption].
rewrite (reduce_eval_compat nr); [|assumption].
rewrite poly_add_compat; ring.
Qed.

(* The completeness lemma *)

(* Lemma reduce_poly_of_formula_complete : forall fl fr,
  reduce (poly_of_formula fl) <> reduce (poly_of_formula fr) ->
  {var | formula_eval var fl <> formula_eval var fr}.
Proof.
intros fl fr H.
pose (p := poly_add (reduce (poly_of_formula fl)) (poly_opp (reduce (poly_of_formula fr)))).
pose (var := boolean_witness p).
exists var.
  intros Hc; apply (f_equal Z_of_bool) in Hc.
  assert (Hfl : linear 0 (reduce (poly_of_formula fl))).
    now destruct (poly_of_formula_valid_compat fl) as [n Hn]; apply (linear_le_compat n); [|now auto]; apply linear_reduce; auto.
  assert (Hfr : linear 0 (reduce (poly_of_formula fr))).
    now destruct (poly_of_formula_valid_compat fr) as [n Hn]; apply (linear_le_compat n); [|now auto]; apply linear_reduce; auto.
  repeat rewrite <- poly_of_formula_eval_compat in Hc.
  define (decide (null p)) b Hb; destruct b; tac_decide.
    now elim H; apply (null_sub_implies_eq 0 0); fold p; auto;
    apply linear_valid_incl; auto.
  elim (boolean_witness_nonzero 0 p); auto.
    unfold p; rewrite <- (min_id 0); apply poly_add_linear_compat; try apply poly_opp_linear_compat; now auto.
    unfold p at 2; rewrite poly_add_compat, poly_opp_compat.
    destruct (poly_of_formula_valid_compat fl) as [nl Hnl].
    destruct (poly_of_formula_valid_compat fr) as [nr Hnr].
    repeat erewrite reduce_eval_compat; eauto.
    fold var; rewrite Hc; ring.
Defined. *)

End Completeness.

(* Reification tactics *)

(* For reflexivity purposes, that would better be transparent *)

Global Transparent decide poly_add.

(* Ltac append_var x l k :=
match l with
| nil => constr: (k, cons x l)
| cons x _ => constr: (k, l)
| cons ?y ?l =>
  let ans := append_var x l (S k) in
  match ans with (?k, ?l) => constr: (k, cons y l) end
end.

Ltac build_formula t l :=
match t with
| true => constr: (formula_top, l)
| false => constr: (formula_btm, l)
| ?fl && ?fr =>
  match build_formula fl l with (?tl, ?l) =>
    match build_formula fr l with (?tr, ?l) =>
      constr: (formula_cnj tl tr, l)
    end
  end
| ?fl || ?fr =>
  match build_formula fl l with (?tl, ?l) =>
    match build_formula fr l with (?tr, ?l) =>
      constr: (formula_dsj tl tr, l)
    end
  end
| negb ?f =>
  match build_formula f l with (?t, ?l) =>
    constr: (formula_neg t, l)
  end
| _ =>
  let ans := append_var t l 0 in
  match ans with (?k, ?l) => constr: (formula_var k, l) end
end.

(* Extract a counterexample from a polynomial and display it *)

Ltac counterexample p l :=
  let var := constr: (boolean_witness p) in
  let var := eval vm_compute in var in
  let rec print l vl :=
    match l with
    | nil => idtac
    | cons ?x ?l =>
      match vl with
      | nil =>
        idtac x ":=" "false"; print l (@nil bool)
      | cons ?v ?vl =>
        idtac x ":=" v; print l vl
      end
    end
  in
  idtac "Counter-example:"; print l var.

Ltac btauto_reify :=
lazymatch goal with
| [ |- @eq bool ?t ?u ] =>
  lazymatch build_formula t (@nil bool) with
  | (?fl, ?l) =>
    lazymatch build_formula u l with
    | (?fr, ?l) =>
      change (formula_eval l fl = formula_eval l fr)
    end
  end
| _ => fail "Cannot recognize a boolean equality"
end.

(* The long-awaited tactic *)

Ltac btauto :=
lazymatch goal with
| [ |- @eq bool ?t ?u ] =>
  lazymatch build_formula t (@nil bool) with
  | (?fl, ?l) =>
    lazymatch build_formula u l with
    | (?fr, ?l) =>
      change (formula_eval l fl = formula_eval l fr);
      apply reduce_poly_of_formula_sound_alt;
      vm_compute; (reflexivity || fail "Not a tautology")
    end
  end
| _ => fail "Cannot recognize a boolean equality"
end. *)
