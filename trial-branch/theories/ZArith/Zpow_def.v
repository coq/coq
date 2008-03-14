Require Import ZArith_base.
Require Import Ring_theory.

Open Local Scope Z_scope.
 
(** [Zpower_pos z n] is the n-th power of [z] when [n] is an binary
      integer (type [positive]) and [z] a signed integer (type [Z]) *) 
Definition Zpower_pos (z:Z) (n:positive) := iter_pos n Z (fun x:Z => z * x) 1.
  
Definition Zpower (x y:Z) :=
    match y with
      | Zpos p => Zpower_pos x p
      | Z0 => 1
      | Zneg p => 0
    end.

Lemma Zpower_theory : power_theory 1 Zmult (eq (A:=Z)) Z_of_N Zpower.
Proof.
 constructor. intros.
 destruct n;simpl;trivial.
 unfold Zpower_pos.
 assert (forall k, iter_pos p Z (fun x : Z => r * x) k = pow_pos Zmult r p*k).
 induction p;simpl;intros;repeat rewrite IHp;trivial;
   repeat rewrite Zmult_assoc;trivial.
 rewrite H;rewrite Zmult_1_r;trivial.
Qed.
 
