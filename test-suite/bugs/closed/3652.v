Require Setoid.
Require ZArith.
Import ZArith.

Inductive Erasable(A : Set) : Prop :=
  erasable: A -> Erasable A.

Arguments erasable [A] _.

Hint Constructors Erasable.

Scheme Erasable_elim := Induction for Erasable Sort Prop.

Notation "## T" := (Erasable T) (at level 1, format "## T") : Erasable_scope.
Notation "# x" := (erasable x) (at level 1, format "# x") : Erasable_scope.
Open Scope Erasable_scope.

Axiom Erasable_inj : forall {A : Set}{a b : A}, #a=#b -> a=b.

Lemma Erasable_rw : forall (A: Set)(a b : A), (#a=#b) <-> (a=b).
Proof.
  intros A a b.
  split.
  - apply Erasable_inj.
  - congruence.
Qed.

Open Scope Z_scope.
Opaque Z.mul.

Infix "^" := Zpower_nat : Z_scope.

Notation "f ; v <- x" := (let (v) := x in f)
                            (at level 199, left associativity) : Erasable_scope.
Notation "f ; < v" := (f ; v <- v)
                         (at level 199, left associativity) : Erasable_scope.
Notation "f |# v <- x" := (#f ; v <- x)
                          (at level 199, left associativity) : Erasable_scope.
Notation "f |# < v" := (#f ; < v)
                          (at level 199, left associativity) : Erasable_scope.

Ltac name_evars id := 
  repeat match goal with |- context[?V] => 
                         is_evar V; let H := fresh id in set (H:=V) in * end.

Lemma Twoto0 : 2^0 = 1.
Proof. compute. reflexivity. Qed.

Ltac ring_simplify' := rewrite ?Twoto0; ring_simplify.

Definition mp2a1s(x : Z)(n : nat) := x * 2^n + (2^n-1).

Hint Unfold mp2a1s.

Definition zotval(n1s : nat)(is2 : bool)(next_value : Z) : Z :=
  2 * mp2a1s next_value n1s + if is2 then 2 else 0.

Inductive zot'(eis2 : ##bool)(value : ##Z) : Set :=
| Zot'(is2 : bool)
      (iseq : eis2=#is2)
      {next_is2 : ##bool}
      (ok : is2=true -> next_is2=#false)
      {next_value : ##Z}
      (n1s : nat)
      (veq : value = (zotval n1s is2 next_value |#<next_value))
      (next : zot' next_is2 next_value)
  : zot' eis2 value.

Definition de2{eis2 value}(z : zot' eis2 value) : zot' #false value.
Proof.
  case z.
  intros is2 iseq next_is2 ok next_value n1s veq next. 
  subst.
  destruct is2.
  2:trivial.
  clear z.
  specialize (ok eq_refl). subst.
  destruct n1s.
  - refine (Zot' _ _ _ _ _ _ _ _).
    all:shelve_unifiable.
    reflexivity.
    discriminate.
    name_evars e.
    case_eq next_value. intros next_valueU next_valueEU.
    case_eq e. intros eU eEU.
    f_equal.
    unfold zotval.
    unfold mp2a1s.
    ring_simplify'.
    replace 2 with (2*1) at 2 7 by omega.
    rewrite <-?Z.mul_assoc.
    rewrite <-?Z.mul_add_distr_l.
    rewrite <-Z.mul_sub_distr_l.
    rewrite Z.mul_cancel_l by omega.
    replace 1 with (2-1) at 1 by omega.
    rewrite Z.add_sub_assoc.
    rewrite Z.sub_cancel_r.
    Unshelve.
    all:case_eq next.
Abort.

