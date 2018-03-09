(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

Require Import ZArith Zwf Psatz QArith.
Open Scope Z_scope.

Lemma Zabs_square : forall x,  (Z.abs  x)^2 = x^2.
Proof.
 intros ; case (Zabs_dec x) ; intros ; psatz Z 2.
Qed.
Hint Resolve Z.abs_nonneg Zabs_square.

Lemma integer_statement :  ~exists n, exists p, n^2 = 2*p^2 /\ n <> 0.
Proof.
intros [n [p [Heq Hnz]]]; pose (n' := Z.abs n); pose (p':=Z.abs p).
assert (facts : 0 <= Z.abs n /\ 0 <= Z.abs p /\ Z.abs n^2=n^2
         /\ Z.abs p^2 = p^2) by auto.
assert (H : (0 < n' /\ 0 <= p' /\ n' ^2 = 2* p' ^2)) by
  (destruct facts as [Hf1 [Hf2 [Hf3 Hf4]]]; unfold n', p' ; psatz Z 2).
generalize p' H; elim n' using (well_founded_ind (Zwf_well_founded 0)); clear.
intros n IHn p [Hn [Hp Heq]].
assert (Hzwf : Zwf 0 (2*p-n) n) by (unfold Zwf; psatz Z 2).
assert (Hdecr : 0 < 2*p-n /\ 0 <= n-p /\ (2*p-n)^2=2*(n-p)^2) by psatz Z 2.
apply (IHn (2*p-n) Hzwf (n-p) Hdecr).
Qed.

Open Scope Q_scope.

Lemma QnumZpower : forall x : Q, Qnum (x ^ 2)%Q = ((Qnum x) ^ 2) %Z.
Proof.
  intros.
  destruct x.
  cbv beta  iota zeta delta - [Z.mul].
  ring.
Qed.


Lemma QdenZpower : forall x : Q, Zpos (Qden (x ^ 2)%Q) = (Zpos (Qden x) ^ 2) %Z.
Proof.
  intros.
  destruct x.
  simpl.
  unfold Z.pow_pos.
  simpl.
  rewrite Pos.mul_1_r.
  reflexivity.
Qed.

Theorem sqrt2_not_rational : ~exists x:Q, x^2==2#1.
Proof.
 unfold Qeq; intros (x,HQeq); simpl (Qden (2#1)) in HQeq; rewrite Z.mul_1_r in HQeq.
 assert (Heq : (Qnum x ^ 2 = 2 * Zpos (Qden x) ^ 2%Q)%Z) by
   (rewrite QnumZpower in HQeq ; rewrite QdenZpower in HQeq ; auto).
 assert (Hnx : (Qnum x <> 0)%Z)
 by (intros Hx; simpl in HQeq; rewrite Hx in HQeq; discriminate HQeq).
 apply integer_statement; exists (Qnum x); exists (Zpos (Qden x)); auto.
Qed.
