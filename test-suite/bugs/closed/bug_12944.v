
Inductive vector A : nat -> Type :=
  |nil : vector A 0
  |cons : forall (h:A) (n:nat), vector A n -> vector A (S n).

Global Set Mangle Names.

Lemma vlookup_middle {A n} (v : vector A n) : True.
Proof.
  induction v as [|?? IHv].
  all:exact I.
Qed.
