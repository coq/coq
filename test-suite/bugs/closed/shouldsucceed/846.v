Set Implicit Arguments.

Open Scope type_scope.

Inductive One : Set := inOne: One.

Definition maybe: forall A B:Set,(A -> B) -> One + A -> One + B.
Proof.
  intros A B f c.
  case c.
  left; assumption.
  right; apply f; assumption.
Defined.

Definition id (A:Set)(a:A):=a.

Definition LamF (X: Set -> Set)(A:Set) :Set :=
  A + (X A)*(X A) + X(One + A).

Definition LamF' (X: Set -> Set)(A:Set) :Set :=
  LamF X A.

Require Import List.
Require Import Bool.

Definition index := list bool.

Inductive L (A:Set) : index -> Set :=
  initL: A -> L A nil
  | pluslL: forall l:index, One -> L A (false::l)
  | plusrL: forall l:index, L A l -> L A (false::l)
  | varL: forall l:index, L A l -> L A (true::l)
  | appL: forall l:index, L A (true::l) -> L A (true::l) -> L A (true::l)
  | absL: forall l:index, L A (true::false::l) -> L A (true::l).

Scheme L_rec_simp := Minimality for L Sort Set.

Definition Lam' (A:Set) := L A (true::nil).

Definition aczelapp: forall (l1 l2: index)(A:Set), L (L A l2) l1 -> L A
  (l1++l2).
Proof.
  intros l1 l2 A.
  generalize l1.
  clear l1.
  (* Check (fun i:index => L A (i++l2)). *)
  apply (L_rec_simp (A:=L A l2) (fun i:index => L A (i++l2))).
  trivial.
  intros l o.
  simpl app.
  apply pluslL; assumption.
  intros l _ t.
  simpl app.
  apply plusrL; assumption.
  intros l _ t.
  simpl app.
  apply varL; assumption.
  intros l _ t1 _ t2.
  simpl app in *|-*.
  Check 0.
  apply appL; [exact t1| exact t2].
  intros l _ t.
  simpl app in *|-*.
  Check 0.
  apply absL; assumption.
Defined.

Definition monL: forall (l:index)(A:Set)(B:Set), (A->B) -> L A l -> L B l.
Proof.
  intros l A B f.
  intro t.
  elim t.
  intro a.
  exact (initL (f a)).
  intros i u.
  exact (pluslL _ _ u).
  intros i _ r.
  exact (plusrL r).
  intros i _ r.
  exact (varL r).
  intros i _ r1 _ r2.
  exact (appL r1 r2).
  intros i _ r.
  exact (absL r).
Defined.

Definition lam': forall (A B:Set), (A -> B) -> Lam' A -> Lam' B.
Proof.
  intros A B f t.
  unfold Lam' in *|-*.
  Check 0.
  exact (monL f t).
Defined.

Definition inLam': forall A:Set, LamF' Lam' A -> Lam' A.
Proof.
  intros A [[a|[t1 t2]]|r].
  unfold Lam'.
  exact (varL (initL a)).
  exact (appL t1 t2).
  unfold Lam' in * |- *.
  Check 0.
  apply absL.
  change (L A ((true::nil) ++ (false::nil))).
  apply aczelapp.
  (* Check (fun x:One + A =>  (match (maybe (fun a:A => initL a) x) with
    | inl u => pluslL _ _ u
    | inr t' => plusrL t' end)). *)
  exact (monL (fun x:One + A =>
    (match (maybe (fun a:A => initL a) x) with
       | inl u => pluslL _ _ u
       | inr t' => plusrL t' end)) r).
Defined.

Section minimal.

Definition sub1 (F G: Set -> Set):= forall A:Set, F A->G A.
Hypothesis G: Set -> Set.
Hypothesis step: sub1 (LamF' G) G.

Fixpoint L'(A:Set)(i:index){struct i} : Set :=
  match i with
    nil => A
    | false::l => One + L' A l
    | true::l => G (L' A l)
  end.

Definition LinL': forall (A:Set)(i:index), L A i -> L' A i.
Proof.
  intros A i t.
  elim t.
  intro a.
  unfold L'.
  assumption.
  intros l u.
  left; assumption.
  intros l _ r.
  right; assumption.
  intros l _ r.
  apply (step (A:=L' A l)).
  exact (inl _ (inl _ r)).
  intros l _ r1 _ r2.
  apply (step (A:=L' A l)).
  (* unfold L' in * |- *.
  Check 0. *)
  exact (inl _ (inr _ (pair r1 r2))).
  intros l _ r.
  apply  (step (A:=L' A l)).
  exact (inr _ r).
Defined.

Definition L'inG: forall A: Set, L' A (true::nil) -> G A.
Proof.
  intros A t.
  unfold L' in t.
  assumption.
Defined.

Definition Itbasic: sub1 Lam' G.
Proof.
  intros A t.
  apply L'inG.
  unfold Lam' in t.
  exact (LinL' t).
Defined.

End minimal.

Definition recid := Itbasic inLam'.

Definition L'Lam'inL: forall (i:index)(A:Set), L' Lam' A i -> L A i.
Proof.
  intros i A t.
  induction i.
  unfold L' in t.
  apply initL.
  assumption.
  induction a.
  simpl L' in t.
  apply (aczelapp (l1:=true::nil) (l2:=i)).
  exact (lam' IHi t).
  simpl L' in t.
  induction t.
  exact (pluslL _ _ a).
  exact (plusrL (IHi b)).
Defined.


Lemma recidgen: forall(A:Set)(i:index)(t:L A i), L'Lam'inL i A (LinL' inLam' t)
  = t.
Proof.
  intros A i t.
  induction t.
  trivial.
  trivial.
  simpl.
  rewrite IHt.
  trivial.
  simpl L'Lam'inL.
  rewrite IHt.
  trivial.
  simpl L'Lam'inL.
  simpl L'Lam'inL in IHt1.
  unfold lam' in IHt1.
  simpl L'Lam'inL in IHt2.
  unfold lam' in IHt2.

  (* going on. This fails for the original solution. *)
  rewrite IHt1.
  rewrite IHt2.
  trivial.
Abort. (* one goal still left *)

