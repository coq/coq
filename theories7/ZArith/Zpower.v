(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require ZArith_base.
Require Omega.
Require Zcomplements.
V7only [Import Z_scope.].
Open Local Scope Z_scope.

Section section1.

(** [Zpower_nat z n] is the n-th power of [z] when [n] is an unary
    integer (type [nat]) and [z] a signed integer (type [Z]) *) 

Definition Zpower_nat := 
  [z:Z][n:nat] (iter_nat n Z ([x:Z]` z * x `) `1`).

(** [Zpower_nat_is_exp] says [Zpower_nat] is a morphism for
    [plus : nat->nat] and [Zmult : Z->Z] *)

Lemma Zpower_nat_is_exp : 
  (n,m:nat)(z:Z)
  `(Zpower_nat z (plus n m)) = (Zpower_nat z n)*(Zpower_nat z m)`.

Intros; Elim n; 
[ Simpl; Elim (Zpower_nat z m); Auto with zarith
| Unfold Zpower_nat; Intros;  Simpl; Rewrite H;
  Apply Zmult_assoc].
Qed.

(** [Zpower_pos z n] is the n-th power of [z] when [n] is an binary
    integer (type [positive]) and [z] a signed integer (type [Z]) *) 

Definition Zpower_pos := 
  [z:Z][n:positive] (iter_pos n Z ([x:Z]`z * x`) `1`).

(** This theorem shows that powers of unary and binary integers
   are the same thing, modulo the function convert : [positive -> nat] *)

Theorem Zpower_pos_nat : 
  (z:Z)(p:positive)(Zpower_pos z p) = (Zpower_nat z (convert p)).

Intros; Unfold Zpower_pos; Unfold Zpower_nat; Apply iter_convert.
Qed.

(** Using the theorem [Zpower_pos_nat] and the lemma [Zpower_nat_is_exp] we
   deduce that the function [[n:positive](Zpower_pos z n)] is a morphism
   for [add : positive->positive] and [Zmult : Z->Z] *)

Theorem Zpower_pos_is_exp : 
  (n,m:positive)(z:Z) 
  ` (Zpower_pos z (add n m)) = (Zpower_pos z n)*(Zpower_pos z m)`.

Intros.
Rewrite -> (Zpower_pos_nat z n).
Rewrite -> (Zpower_pos_nat z m).
Rewrite -> (Zpower_pos_nat z (add n m)).
Rewrite -> (convert_add n m).
Apply Zpower_nat_is_exp.
Qed.

Definition Zpower :=
  [x,y:Z]Cases y of
    (POS p) => (Zpower_pos x p)
  | ZERO => `1`
  | (NEG p) => `0`
  end.

V8Infix "^" Zpower : Z_scope.

Hints Immediate Zpower_nat_is_exp : zarith.
Hints Immediate Zpower_pos_is_exp : zarith.
Hints Unfold  Zpower_pos : zarith.
Hints Unfold  Zpower_nat : zarith.

Lemma Zpower_exp : (x:Z)(n,m:Z)
  `n >= 0` -> `m >= 0` -> `(Zpower x (n+m))=(Zpower x n)*(Zpower x m)`.
NewDestruct n; NewDestruct m; Auto with zarith.
Simpl; Intros; Apply Zred_factor0.
Simpl; Auto with zarith.
Intros; Compute in H0; Absurd INFERIEUR=INFERIEUR; Auto with zarith.
Intros; Compute in H0; Absurd INFERIEUR=INFERIEUR; Auto with zarith.
Qed.

End section1.

(* Exporting notation "^" *)

V8Infix "^" Zpower : Z_scope.

Hints Immediate Zpower_nat_is_exp : zarith.
Hints Immediate Zpower_pos_is_exp : zarith.
Hints Unfold  Zpower_pos : zarith.
Hints Unfold  Zpower_nat : zarith.

Section Powers_of_2.

(** For the powers of two, that will be widely used, a more direct
   calculus is possible. We will also prove some properties such
   as [(x:positive) x < 2^x] that are true for all integers bigger
   than 2 but more difficult to prove and useless. *)     

(** [shift n m] computes [2^n * m], or [m] shifted by [n] positions *)

Definition shift_nat := 
  [n:nat][z:positive](iter_nat n positive xO z). 
Definition shift_pos :=
  [n:positive][z:positive](iter_pos n positive xO z). 
Definition shift :=
  [n:Z][z:positive]
  Cases n of
    ZERO => z
  | (POS p) => (iter_pos p positive xO z)
  | (NEG p) => z
  end.

Definition two_power_nat := [n:nat] (POS (shift_nat n xH)).
Definition two_power_pos := [x:positive] (POS (shift_pos x xH)).

Lemma two_power_nat_S : 
  (n:nat)` (two_power_nat (S n)) = 2*(two_power_nat n)`.
Intro; Simpl; Apply refl_equal.
Qed.

Lemma shift_nat_plus :
  (n,m:nat)(x:positive)
    (shift_nat (plus n m) x)=(shift_nat n (shift_nat m x)).

Intros; Unfold shift_nat; Apply iter_nat_plus.
Qed.

Theorem shift_nat_correct :
  (n:nat)(x:positive)(POS (shift_nat n x))=`(Zpower_nat 2 n)*(POS x)`.

Unfold shift_nat; Induction n; 
[ Simpl; Trivial with zarith
| Intros; Replace (Zpower_nat `2` (S n0)) with `2 * (Zpower_nat 2 n0)`;
[ Rewrite <- Zmult_assoc; Rewrite <- (H x); Simpl; Reflexivity
| Auto with zarith ]
].
Qed.

Theorem two_power_nat_correct :
  (n:nat)(two_power_nat n)=(Zpower_nat `2` n).

Intro n.
Unfold two_power_nat.
Rewrite -> (shift_nat_correct n).
Omega.
Qed.
  
(** Second we show that [two_power_pos] and [two_power_nat] are the same *)
Lemma shift_pos_nat : (p:positive)(x:positive)
  (shift_pos p x)=(shift_nat (convert p) x).

Unfold shift_pos.
Unfold shift_nat.
Intros; Apply iter_convert.
Qed.

Lemma two_power_pos_nat : 
  (p:positive) (two_power_pos p)=(two_power_nat (convert p)).

Intro; Unfold two_power_pos; Unfold two_power_nat.
Apply f_equal with f:=POS.
Apply shift_pos_nat.
Qed.

(** Then we deduce that [two_power_pos] is also correct *)

Theorem shift_pos_correct :
  (p,x:positive) ` (POS (shift_pos p x)) = (Zpower_pos 2 p) * (POS x)`.

Intros.
Rewrite -> (shift_pos_nat p x).
Rewrite -> (Zpower_pos_nat `2` p).
Apply shift_nat_correct.
Qed.

Theorem two_power_pos_correct : 
  (x:positive) (two_power_pos x)=(Zpower_pos `2` x).

Intro.
Rewrite -> two_power_pos_nat.
Rewrite -> Zpower_pos_nat.
Apply two_power_nat_correct.
Qed.

(** Some consequences *)

Theorem two_power_pos_is_exp :
  (x,y:positive) (two_power_pos (add x y))
    =(Zmult (two_power_pos x) (two_power_pos y)).
Intros.
Rewrite -> (two_power_pos_correct (add x y)).
Rewrite -> (two_power_pos_correct x).
Rewrite -> (two_power_pos_correct y).
Apply Zpower_pos_is_exp.
Qed.

(** The exponentiation [z -> 2^z] for [z] a signed integer. 
    For convenience, we assume that [2^z = 0] for all [z < 0]
    We could also define a inductive type [Log_result] with
    3 contructors [ Zero | Pos positive -> | minus_infty]
    but it's more complexe and not so useful. *)
 
Definition two_p :=
  [x:Z]Cases x of
         ZERO    => `1`
       | (POS y) => (two_power_pos y)
       | (NEG y) => `0`
       end.

Theorem two_p_is_exp :
  (x,y:Z) ` 0 <= x` -> ` 0 <= y` -> 
    ` (two_p (x+y)) = (two_p x)*(two_p y)`.
Induction x; 
[ Induction y; Simpl; Auto with zarith
| Induction y; 
  [ Unfold two_p;  Rewrite -> (Zmult_sym (two_power_pos p) `1`);
    Rewrite -> (Zmult_one (two_power_pos p)); Auto with zarith
  | Unfold Zplus; Unfold two_p;
    Intros; Apply two_power_pos_is_exp
  | Intros; Unfold Zle in H0; Unfold Zcompare in H0; 
    Absurd SUPERIEUR=SUPERIEUR; Trivial with zarith
  ]
| Induction y; 
  [ Simpl; Auto with zarith
  | Intros; Unfold Zle in H; Unfold Zcompare in H;
    Absurd (SUPERIEUR=SUPERIEUR); Trivial with zarith
  | Intros; Unfold Zle in H; Unfold Zcompare in H;
    Absurd (SUPERIEUR=SUPERIEUR); Trivial with zarith
  ]
].
Qed.

Lemma two_p_gt_ZERO : (x:Z) ` 0 <= x` -> ` (two_p x) > 0`.
Induction x; Intros;
[ Simpl; Omega
| Simpl; Unfold two_power_pos; Apply POS_gt_ZERO
| Absurd ` 0 <= (NEG p)`;
  [ Simpl; Unfold Zle; Unfold Zcompare;
    Do 2 Unfold not; Auto with zarith
  | Assumption ]
].
Qed.

Lemma two_p_S : (x:Z) ` 0 <= x` -> 
 `(two_p (Zs x)) = 2 * (two_p x)`.
Intros; Unfold Zs. 
Rewrite (two_p_is_exp x `1` H (ZERO_le_POS xH)).
Apply Zmult_sym.
Qed.

Lemma two_p_pred : 
  (x:Z)` 0 <= x` -> ` (two_p (Zpred x)) < (two_p x)`.
Intros; Apply natlike_ind 
with P:=[x:Z]` (two_p (Zpred x)) < (two_p x)`;
[ Simpl; Unfold Zlt; Auto with zarith
| Intros; Elim (Zle_lt_or_eq `0` x0 H0);
  [ Intros;
    Replace (two_p (Zpred (Zs x0)))
    with (two_p (Zs (Zpred x0)));
    [ Rewrite -> (two_p_S (Zpred x0));
      [ Rewrite -> (two_p_S x0);
      	[ Omega
      	| Assumption]
      | Apply Zlt_ZERO_pred_le_ZERO; Assumption]
    | Rewrite <- (Zs_pred x0); Rewrite <- (Zpred_Sn x0); Trivial with zarith]
  | Intro Hx0; Rewrite <- Hx0; Simpl; Unfold Zlt; Auto with zarith]
| Assumption].
Qed. 

Lemma Zlt_lt_double : (x,y:Z) ` 0 <= x < y` -> ` x < 2*y`.
Intros; Omega. Qed. 

End Powers_of_2.

Hints Resolve two_p_gt_ZERO : zarith.
Hints Immediate two_p_pred two_p_S : zarith.

Section power_div_with_rest.

(** Division by a power of two.
    To [n:Z] and [p:positive], [q],[r] are associated such that
    [n = 2^p.q + r] and [0 <= r < 2^p] *)

(** Invariant: [d*q + r = d'*q + r /\ d' = 2*d /\ 0<= r < d /\ 0 <= r' < d'] *)
Definition Zdiv_rest_aux :=
  [qrd:(Z*Z)*Z] 
  let (qr,d)=qrd in let (q,r)=qr in
  (Cases q of
     ZERO => ` (0, r)`
   | (POS xH) => ` (0, d + r)`
   | (POS (xI n)) => ` ((POS n), d + r)`
   | (POS (xO n)) => ` ((POS n), r)`
   | (NEG xH) => ` (-1, d + r)`
   | (NEG (xI n)) => ` ((NEG n) - 1, d + r)`
   | (NEG (xO n)) => ` ((NEG n), r)`
   end, ` 2*d`).

Definition Zdiv_rest := 
  [x:Z][p:positive]let (qr,d)=(iter_pos p ? Zdiv_rest_aux ((x,`0`),`1`)) in qr.

Lemma Zdiv_rest_correct1 :
  (x:Z)(p:positive)
  let (qr,d)=(iter_pos p ? Zdiv_rest_aux ((x,`0`),`1`)) in d=(two_power_pos p).

Intros x p; 
Rewrite (iter_convert p ? Zdiv_rest_aux ((x,`0`),`1`));
Rewrite (two_power_pos_nat p);
Elim (convert p); Simpl;
[ Trivial with zarith
| Intro n; Rewrite (two_power_nat_S n);
  Unfold 2 Zdiv_rest_aux;
  Elim (iter_nat n (Z*Z)*Z Zdiv_rest_aux ((x,`0`),`1`));
  NewDestruct a; Intros; Apply f_equal with f:=[z:Z]`2*z`; Assumption ]. 
Qed.

Lemma Zdiv_rest_correct2 :
  (x:Z)(p:positive)
  let (qr,d)=(iter_pos p ? Zdiv_rest_aux ((x,`0`),`1`)) in
  let (q,r)=qr in
  ` x=q*d + r` /\ ` 0 <= r < d`.

Intros; Apply iter_pos_invariant with
  f:=Zdiv_rest_aux
  Inv:=[qrd:(Z*Z)*Z]let (qr,d)=qrd in let (q,r)=qr in
                      ` x=q*d + r` /\ ` 0 <= r < d`;
[ Intro x0; Elim x0; Intro y0; Elim y0;
  Intros q r d; Unfold Zdiv_rest_aux; 
  Elim q;
  [ Omega
  | NewDestruct p0; 
    [ Rewrite POS_xI; Intro; Elim H; Intros; Split; 
      [ Rewrite H0; Rewrite Zplus_assoc;
      	Rewrite Zmult_plus_distr_l;
      	Rewrite Zmult_1_n; Rewrite Zmult_assoc;
      	Rewrite (Zmult_sym (POS p0) `2`); Apply refl_equal
      | Omega ]
    | Rewrite POS_xO; Intro; Elim H; Intros; Split;
      [ Rewrite H0;
      	Rewrite Zmult_assoc; Rewrite (Zmult_sym (POS p0) `2`);
      	Apply refl_equal  
      | Omega ]
    | Omega ]
  | NewDestruct p0; 
    [ Rewrite NEG_xI; Unfold Zminus; Intro; Elim H; Intros; Split; 
      [ Rewrite H0; Rewrite Zplus_assoc;
      	Apply f_equal with f:=[z:Z]`z+r`;
      	Do 2 (Rewrite Zmult_plus_distr_l);
       	Rewrite Zmult_assoc; 
      	Rewrite (Zmult_sym (NEG p0) `2`);
      	Rewrite <- Zplus_assoc;
	Apply f_equal with f:=[z:Z]`2 * (NEG p0) * d + z`; 
      	Omega
      | Omega ]
    | Rewrite NEG_xO; Unfold Zminus; Intro; Elim H; Intros; Split;
      [ Rewrite H0;
      	Rewrite Zmult_assoc; Rewrite (Zmult_sym (NEG p0) `2`);
      	Apply refl_equal  
      | Omega ]
    | Omega ] ]
| Omega].
Qed.

Inductive Set Zdiv_rest_proofs[x:Z; p:positive] :=
  Zdiv_rest_proof : (q:Z)(r:Z) 
     `x = q * (two_power_pos p) + r` 
       -> `0 <= r`
        -> `r < (two_power_pos p)` 
      	 -> (Zdiv_rest_proofs x p).

Lemma  Zdiv_rest_correct :
  (x:Z)(p:positive)(Zdiv_rest_proofs x p).
Intros x p.
Generalize (Zdiv_rest_correct1 x p); Generalize (Zdiv_rest_correct2 x p).
Elim  (iter_pos p (Z*Z)*Z Zdiv_rest_aux ((x,`0`),`1`)).
Induction a.
Intros.
Elim H; Intros H1 H2; Clear H.
Rewrite -> H0 in H1; Rewrite -> H0 in H2;
Elim H2; Intros;
Apply Zdiv_rest_proof with q:=a0 r:=b; Assumption.
Qed.

End power_div_with_rest.
