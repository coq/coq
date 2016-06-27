Unset Structural Injection.

Inductive nCk : nat -> nat -> Type :=
  |zz : nCk 0 0
  | incl { m n : nat } : nCk m n -> nCk (S m) (S n)
  | excl { m n : nat } : nCk m n -> nCk (S m) n.

Definition nCkComp { l m n : nat } :
  nCk l m -> nCk m n -> nCk l n.
Proof.
  intro.
  revert n.
  induction H.
  auto.
(* ( incl w ) o zz -> contradiction *)
  intros.
    remember (S n) as sn.
    destruct H0.
      discriminate Heqsn.
    apply incl.
      apply IHnCk.
      injection Heqsn.
      intro.
      rewrite <- H1.
      auto.
    apply excl.
      apply IHnCk.
      injection Heqsn.
      intro. rewrite <- H1.
      auto.
  intros.
  apply excl.
  apply IHnCk.
  auto.
Defined.

Lemma nCkEq { k l m n : nat } ( cs : nCk k l ) (ct : nCk l m) (cr : nCk m n ):
  nCkComp cs (nCkComp ct cr) = nCkComp (nCkComp cs ct) cr.
Proof.
  revert m n ct cr.
  induction cs.
  intros. simpl. auto.
  intros.
  destruct n.
   destruct m0.
    destruct n0.
     destruct cr.
(* Anomaly: Evar ?nnn was not declared. Please report. *)
