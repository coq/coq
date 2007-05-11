Require Import ZArith.
Require Import ZAux.

Set Implicit Arguments.

Open Scope Z_scope.

Lemma rel_prime_mod: forall a b, 1 < b ->
  rel_prime a b -> a mod b <> 0.
Proof.
intros a b H H1 H2.
case (not_rel_prime_0 _ H).
rewrite <- H2.
apply rel_prime_mod; auto with zarith.
Qed.

Lemma Zmodpl: forall a b n, 0 < n ->
  (a mod n + b) mod n = (a + b) mod n.
Proof.
intros a b n H.
rewrite Zmod_plus; auto.
rewrite Zmod_mod; auto.
apply sym_equal; apply Zmod_plus; auto.
Qed.

Lemma Zmodpr: forall a b n, 0 < n ->
  (b + a mod n) mod n = (b + a) mod n.
Proof.
intros a b n H; repeat rewrite (Zplus_comm b).
apply Zmodpl; auto.
Qed.

Lemma Zmodml: forall a b n, 0 < n ->
  (a mod n * b) mod n = (a * b) mod n.
Proof.
intros a b n H.
rewrite Zmod_mult; auto.
rewrite Zmod_mod; auto.
apply sym_equal; apply Zmod_mult; auto.
Qed.

Lemma Zmodmr: forall a b n, 0 < n ->
  (b * (a mod n)) mod n = (b * a) mod n.
Proof.
intros a b n H; repeat rewrite (Zmult_comm b).
apply Zmodml; auto.
Qed.


Ltac is_ok t :=
  match t with 
  | (?x mod _ + ?y mod _) mod _ => constr:false
  | (?x mod _ * (?y mod _)) mod _ => constr:false
  |  ?x mod _ => x
  end.
 
Ltac  rmod t :=
  match t with 
    (?x + ?y) mod _ => 
     match (is_ok x) with
     | false => rmod x
     | ?x1   =>  match (is_ok y) with 
                |false => rmod y
                | ?y1 => 
                   rewrite <- (Zmod_plus x1 y1)
                |false => rmod y
                end
     end
  | (?x * ?y) mod _ => 
     match (is_ok x) with
     | false => rmod x
     | ?x1 =>  match (is_ok y) with 
                |false => rmod y
                | ?y1 => rewrite <- (Zmod_mult x1 y1)
                end
     | false => rmod x
     end
  end.


Lemma Zmod_div_mod: forall n m a, 0 < n -> 0 < m ->
  (n | m) -> a mod n = (a mod m) mod n.
Proof.
intros n m a H1 H2 H3.
pattern a at 1; rewrite (Z_div_mod_eq a m); auto with zarith.
case H3; intros q Hq; pattern m at 1; rewrite Hq.
rewrite (Zmult_comm q).
rewrite Zmod_plus; auto.
rewrite <- Zmult_assoc; rewrite Zmod_mult; auto.
rewrite Z_mod_same; try rewrite Zmult_0_l; auto with zarith.
rewrite (Zmod_def_small 0); auto with zarith.
rewrite Zplus_0_l; rewrite Zmod_mod; auto with zarith.
Qed.

