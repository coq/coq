
(* $Id$ *)

Require Export Plus.
Require Export Minus.

(**********************************************************)
(* Multiplication                                         *)
(**********************************************************)

Lemma mult_plus_distr : 
      (n,m,p:nat)((mult (plus n m) p)=(plus (mult n p) (mult m p))).
Proof.
Intros; Elim n; Simpl; Intros; Auto with arith.
Elim plus_assoc_l; Elim H; Auto with arith.
Qed.
Hints Resolve mult_plus_distr : arith v62.

Lemma mult_minus_distr : (n,m,p:nat)((mult (minus n m) p)=(minus (mult n p) (mult m p))).
Proof.
Intros; Pattern n m; Apply nat_double_ind; Simpl; Intros; Auto with arith.
Elim minus_plus_simpl; Auto with arith.
Qed.
Hints Resolve mult_minus_distr : arith v62.

Lemma mult_O_le : (n,m:nat)(m=O)\/(le n (mult m n)).
Proof.
Induction m; Simpl; Auto with arith.
Qed.
Hints Resolve mult_O_le : arith v62.

Lemma mult_assoc_r : (n,m,p:nat)((mult (mult n m) p) = (mult n (mult m p))).
Proof.
Intros; Elim n; Intros; Simpl; Auto with arith.
Rewrite mult_plus_distr.
Elim H; Auto with arith.
Qed.
Hints Resolve mult_assoc_r : arith v62.

Lemma mult_assoc_l : (n,m,p:nat)(mult n (mult m p)) = (mult (mult n m) p).
Auto with arith.
Save.
Hints Resolve mult_assoc_l : arith v62.

Lemma mult_1_n : (n:nat)(mult (S O) n)=n.
Simpl; Auto with arith.
Save.
Hints Resolve mult_1_n : arith v62.

Lemma mult_sym : (n,m:nat)(mult n m)=(mult m n).
Intros; Elim n; Intros; Simpl; Auto with arith.
Elim mult_n_Sm.
Elim H; Apply plus_sym.
Save.
Hints Resolve mult_sym : arith v62.

Lemma mult_n_1 : (n:nat)(mult n (S O))=n.
Intro; Elim mult_sym; Auto with arith.
Save.
Hints Resolve mult_n_1 : arith v62.
