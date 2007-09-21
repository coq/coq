Require Export NZBase.

Module Type NZOrderSig.
Declare Module Export NZBaseMod : NZBaseSig.
Open Local Scope NatIntScope.

Parameter Inline NZlt : NZ -> NZ -> Prop.
Parameter Inline NZle : NZ -> NZ -> Prop.

Add Morphism NZlt with signature NZE ==> NZE ==> iff as NZlt_wd.
Add Morphism NZle with signature NZE ==> NZE ==> iff as NZle_wd.

Notation "x < y" := (NZlt x y) : NatIntScope.
Notation "x <= y" := (NZle x y) : NatIntScope.

Axiom NZle_lt_or_eq : forall n m : NZ, n <= m <-> n < m \/ n == m.
Axiom NZlt_irrefl : forall n : NZ, ~ (n < n).
Axiom NZlt_succ_le : forall n m : NZ, n < S m <-> n <= m.
End NZOrderSig.

Module NZOrderPropFunct (Import NZOrderMod : NZOrderSig).
Module Export NZBasePropMod := NZBasePropFunct NZBaseMod.
Open Local Scope NatIntScope.

Ltac NZle_intro1 := rewrite NZle_lt_or_eq; left.
Ltac NZle_intro2 := rewrite NZle_lt_or_eq; right.
Ltac NZle_elim H := rewrite NZle_lt_or_eq in H; destruct H as [H | H].

Lemma NZlt_stepl : forall x y z : NZ, x < y -> x == z -> z < y.

Lemma NZlt_stepr : forall x y z : NZ, x < y -> y == z -> x < z.

Lemma NZle_stepl : forall x y z : NZ, x <= y -> x == z -> z <= y.

Lemma NZle_stepr : forall x y z : NZ, x <= y -> y == z -> x <= z.

Declare Left  Step NZlt_stepl.
Declare Right Step NZlt_stepr.
Declare Left  Step NZle_stepl.
Declare Right Step NZle_stepr.

Theorem NZlt_le_incl : forall n m : NZ, n < m -> n <= m.

Theorem NZlt_neq : forall n m : NZ, n < m -> n ~= m.

Theorem NZle_refl : forall n : NZ, n <= n.

Theorem NZlt_succ_r : forall n : NZ, n < S n.

Theorem NZle_succ_r : forall n : NZ, n <= S n.

Theorem NZlt_lt_succ : forall n m : NZ, n < m -> n < S m.

Theorem NZle_le_succ : forall n m : NZ, n <= m -> n <= S m.

Theorem NZle_succ_le_or_eq_succ : forall n m : NZ, n <= S m <-> n <= m \/ n == S m.

(* The following theorem is a special case of neq_succ_iter_l below,
but we prove it independently *)

Theorem neq_succ_l : forall n : NZ, S n ~= n.

Theorem nlt_succ_l : forall n : NZ, ~ S n < n.

Theorem nle_succ_l : forall n : NZ, ~ S n <= n.

Theorem NZlt_le_succ : forall n m : NZ, n < m <-> S n <= m.

Theorem NZlt_succ_lt : forall n m : NZ, S n < m -> n < m.

Theorem NZle_succ_le : forall n m : NZ, S n <= m -> n <= m.

Theorem NZsucc_lt_mono : forall n m : NZ, n < m <-> S n < S m.

Theorem NZsucc_le_mono : forall n m : NZ, n <= m <-> S n <= S m.

Theorem NZlt_lt_false : forall n m, n < m -> m < n -> False.

Theorem NZlt_asymm : forall n m, n < m -> ~ m < n.

Theorem NZlt_trans : forall n m p : NZ, n < m -> m < p -> n < p.

Theorem NZle_trans : forall n m p : NZ, n <= m -> m <= p -> n <= p.

Theorem NZle_lt_trans : forall n m p : NZ, n <= m -> m < p -> n < p.

Theorem NZlt_le_trans : forall n m p : NZ, n < m -> m <= p -> n < p.

Theorem NZle_antisymm : forall n m : NZ, n <= m -> m <= n -> n == m.

(** Trichotomy, decidability, and double negation elimination *)

Theorem NZlt_trichotomy : forall n m : NZ,  n < m \/ n == m \/ m < n.

Theorem NZle_lt_dec : forall n m : NZ, n <= m \/ m < n.

Theorem NZle_nlt : forall n m : NZ, n <= m <-> ~ m < n.

Theorem NZlt_dec : forall n m : NZ, n < m \/ ~ n < m.

Theorem NZlt_dne : forall n m, ~ ~ n < m <-> n < m.

Theorem nle_lt : forall n m : NZ, ~ n <= m <-> m < n.

Theorem NZle_dec : forall n m : NZ, n <= m \/ ~ n <= m.

Theorem NZle_dne : forall n m : NZ, ~ ~ n <= m <-> n <= m.

Theorem NZlt_nlt_succ : forall n m : NZ, n < m <-> ~ m < S n.

(* The difference between integers and natural numbers is that for
every integer there is a predecessor, which is not true for natural
numbers. However, for both classes, every number that is bigger than
some other number has a predecessor. The proof of this fact by regular
induction does not go through, so we need to use strong
(course-of-value) induction. *)

Lemma NZlt_exists_pred_strong :
  forall z n m : NZ, z < m -> m <= n -> exists k : NZ, m == S k /\ z <= k.

Theorem NZlt_exists_pred :
  forall z n : NZ, z < n -> exists k : NZ, n == S k /\ z <= k.

(** A corollary of having an order is that NZ is infinite *)

(* This section about infinity of NZ relies on the type nat and can be
safely removed *)

Definition NZsucc_iter (n : nat) (m : NZ) :=
  nat_rec (fun _ => NZ) m (fun _ l => S l) n.

Theorem NZlt_succ_iter_r :
  forall (n : nat) (m : NZ), m < NZsucc_iter (Datatypes.S n) m.

Theorem neq_succ_iter_l :
  forall (n : nat) (m : NZ), NZsucc_iter (Datatypes.S n) m ~= m.

(* End of the section about the infinity of NZ *)

(** Stronger variant of induction with assumptions n >= 0 (n < 0)
in the induction step *)

Section Induction.

Variable A : NZ -> Prop.
Hypothesis A_wd : predicate_wd NZE A.

Add Morphism A with signature NZE ==> iff as A_morph.
Proof A_wd.

Section Center.

Variable z : NZ. (* A z is the basis of induction *)

Section RightInduction.

Let A' (n : NZ) := forall m : NZ, z <= m -> m < n -> A m.

Add Morphism A' with signature NZE ==> iff as A'_pos_wd.
Proof.
unfold A'; solve_predicate_wd.
Qed.

Theorem right_induction :
  A z -> (forall n : NZ, z <= n -> A n -> A (S n)) -> forall n : NZ, z <= n -> A n.

End RightInduction.

Section LeftInduction.

Let A' (n : NZ) := forall m : NZ, m <= z -> n <= m -> A m.

Add Morphism A' with signature NZE ==> iff as A'_neg_wd.
Proof.
unfold A'; solve_predicate_wd.
Qed.

Theorem NZleft_induction :
  A z -> (forall n : NZ, n < z -> A (S n) -> A n) -> forall n : NZ, n <= z -> A n.

End LeftInduction.

Theorem central_induction :
  A z ->
  (forall n : NZ, z <= n -> A n -> A (S n)) ->
  (forall n : NZ, n < z  -> A (S n) -> A n) ->
    forall n : NZ, A n.

End Center.

Theorem induction_0 :
  A 0 ->
  (forall n : NZ, 0 <= n -> A n -> A (S n)) ->
  (forall n : NZ, n < 0  -> A (S n) -> A n) ->
    forall n : NZ, A n.

(** Elimintation principle for < *)

Theorem NZlt_ind : forall (n : NZ),
  A (S n) ->
  (forall m : NZ, n < m -> A m -> A (S m)) ->
   forall m : NZ, n < m -> A m.

(** Elimintation principle for <= *)

Theorem NZle_ind : forall (n : NZ),
  A n ->
  (forall m : NZ, n <= m -> A m -> A (S m)) ->
   forall m : NZ, n <= m -> A m.

End Induction.

End NZOrderPropFunct.

(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
