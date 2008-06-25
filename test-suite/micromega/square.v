(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

Require Import ZArith Zwf Psatz QArith.
Open Scope Z_scope.

Lemma Zabs_square : forall x,  (Zabs  x)^2 = x^2.
Proof.
 intros ; case (Zabs_dec x) ; intros ; psatz Z.
Qed.
Hint Resolve Zabs_pos Zabs_square.

Lemma integer_statement :  ~exists n, exists p, n^2 = 2*p^2 /\ n <> 0.
Proof.
intros [n [p [Heq Hnz]]]; pose (n' := Zabs n); pose (p':=Zabs p).
assert (facts : 0 <= Zabs n /\ 0 <= Zabs p /\ Zabs n^2=n^2
         /\ Zabs p^2 = p^2) by auto.
assert (H : (0 < n' /\ 0 <= p' /\ n' ^2 = 2* p' ^2)) by 
  (destruct facts as [Hf1 [Hf2 [Hf3 Hf4]]]; unfold n', p' ; psatz Z).
generalize p' H; elim n' using (well_founded_ind (Zwf_well_founded 0)); clear.
intros n IHn p [Hn [Hp Heq]].
assert (Hzwf : Zwf 0 (2*p-n) n) by (unfold Zwf; psatz Z).
assert (Hdecr : 0 < 2*p-n /\ 0 <= n-p /\ (2*p-n)^2=2*(n-p)^2) by psatz Z.
apply (IHn (2*p-n) Hzwf (n-p) Hdecr).
Qed.

Open Scope Q_scope.

Lemma QnumZpower : forall x : Q, Qnum (x ^ 2)%Q = ((Qnum x) ^ 2) %Z.
Proof.
  intros.
  destruct x.
  cbv beta  iota zeta delta - [Zmult].
  ring.
Qed.


Lemma QdenZpower : forall x : Q, ' Qden (x ^ 2)%Q = ('(Qden x) ^ 2) %Z.
Proof.
  intros.
  destruct x.
  simpl.
  unfold Zpower_pos.
  simpl.
  rewrite Pmult_1_r.
  reflexivity.
Qed.

Theorem sqrt2_not_rational : ~exists x:Q, x^2==2#1.
Proof.
 unfold Qeq; intros [x]; simpl (Qden (2#1)); rewrite Zmult_1_r.
 intros HQeq.
 assert (Heq : (Qnum x ^ 2 = 2 * ' Qden x ^ 2%Q)%Z) by 
   (rewrite QnumZpower in HQeq ; rewrite QdenZpower in HQeq ; auto).
 assert (Hnx : (Qnum x <> 0)%Z)
 by (intros Hx; simpl in HQeq; rewrite Hx in HQeq; discriminate HQeq).
 apply integer_statement; exists (Qnum x); exists (' Qden x); auto.
Qed.
