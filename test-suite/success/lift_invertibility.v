Require Import ZArith Lia.

Open Scope Z_scope.

Inductive lift :=
| ELID
| ELSHFT (_:lift) (_:Z)
| ELLFT (_:Z) (_:lift).

Fixpoint reloc_rel n lft :=
  match lft with
  | ELID => n
  | ELLFT k lft =>
      if n <=? k then n else reloc_rel (n-k) lft + k
  | ELSHFT el k => reloc_rel (n + k) el
  end.

Fixpoint good_lift l :=
  match l with
  | ELID => True
  | ELLFT k l => good_lift l
  | ELSHFT l k => good_lift l /\ k >= 0
  end.

Lemma good_lift_increasing l : good_lift l -> forall x, reloc_rel x l >= x.
Proof.
  induction l as [|l IH k|k l IH];simpl;intros Hgood x.
  - lia.
  - destruct Hgood as [Hgood Hk].
    pose proof (IH Hgood (x+k)).
    lia.
  - destruct (x <=? k) eqn:Hx.
    + lia.
    + pose proof (IH Hgood (x - k)).
      lia.
Qed.

Fixpoint un_reloc_rel l x :=
  match l with
  | ELID => x
  | ELSHFT l k => un_reloc_rel l x - k
  | ELLFT k l => if x <=? k then x else un_reloc_rel l (x-k) + k
  end.

Lemma un_reloc_rel_ok l : good_lift l -> forall x, un_reloc_rel l (reloc_rel x l) = x.
Proof.
  induction l as [|l IH k|k l IH];simpl.
  - intros _; reflexivity.
  - intros [Hgood _] x.
    rewrite IH by assumption.
    ring.
  - intros Hgood x.
    destruct (x <=? k) eqn:H.
    + rewrite H. reflexivity.
    + assert (H' : reloc_rel (x - k) l + k <=? k = false). {
        apply good_lift_increasing with (x:=x-k) in Hgood.
        lia.
      }
      rewrite H'.
      set (y := reloc_rel _ _).
      replace (y + k - k) with y by ring.
      subst y.
      rewrite IH by assumption.
      ring.
Qed.

Corollary good_lift_injective l : good_lift l -> forall x y, reloc_rel x l = reloc_rel y l -> x = y.
Proof.
  intros Hgood x y H.
  apply (f_equal (un_reloc_rel l)) in H.
  rewrite 2 (un_reloc_rel_ok _ Hgood) in H.
  assumption.
Qed.

Lemma not_all_injective : exists l x y, reloc_rel x l = reloc_rel y l /\ x <> y.
Proof.
  exists (ELLFT 1 (ELSHFT ELID (-1))), 1, 2.
  simpl.
  lia.
Qed.

Inductive term :=
| Var (_:Z)
| Lam (_:term)
| App (_ _ : term).

Fixpoint apply_lift l t :=
  match t with
  | Var x => Var (reloc_rel x l)
  | Lam t =>
      (* NB: ELLFT 1 preserves good_lift *)
      Lam (apply_lift (ELLFT 1 l) t)
  | App x y => App (apply_lift l x) (apply_lift l y)
  end.

Fixpoint compute_lift_from prev l t :=
  match t with
  | Var x => Var (reloc_rel (un_reloc_rel prev x) l)
  | Lam t => Lam (compute_lift_from (ELLFT 1 prev) (ELLFT 1 l) t)
  | App x y => App (compute_lift_from prev l x) (compute_lift_from prev l y)
  end.

Theorem compute_lift_from_ok t : forall prev l,
    good_lift prev ->
    compute_lift_from prev l (apply_lift prev t) = apply_lift l t.
Proof.
  induction t as [x|t IH|x IHx y IHy];simpl;intros prev l Hgood.
  - rewrite un_reloc_rel_ok by assumption.
    reflexivity.
  - f_equal. apply IH.
    simpl. assumption.
  - f_equal.
    + apply IHx;assumption.
    + apply IHy;assumption.
Qed.
