
(* $Id$ *)

(*********************************************************)
(*           Definition of the some functions            *)
(*                                                       *)
(*********************************************************)

Require Export Rlimit.

(*******************************)
(*      Factorial              *)
(*******************************)
(*********)
Fixpoint fact [n:nat]:nat:=
  Cases n of
     O     => (S O)
    |(S n) => (mult (S n) (fact n))
  end.
 
(*******************************)
(*          Power              *)
(*******************************)
(*********)
Fixpoint pow [r:R;n:nat]:R:=
  Cases n of
     O     => R1
    |(S n) => (Rmult r (pow r n))
  end.

(*********)
Lemma tech_pow_Rmult:(x:R)(n:nat)(Rmult x (pow x n))==(pow x (S n)).
Induction n; Simpl; Trivial.
Save.

(*********)
Lemma tech_pow_Rplus:(x:R)(a,n:nat)
  (Rplus (pow x a) (Rmult (INR n) (pow x a)))==
           (Rmult (INR (S n)) (pow x a)).
Intros; Pattern 1 (pow x a);  
 Rewrite <-(let (H1,H2)=(Rmult_ne (pow x a)) in H1); 
 Rewrite (Rmult_sym (INR n) (pow x a));
 Rewrite <- (Rmult_Rplus_distr (pow x a) R1 (INR n));
 Rewrite (Rplus_sym R1 (INR n)); Rewrite <-(S_INR n);
 Apply Rmult_sym.
Save.

(*******************************)
(*  Sum of n first naturals    *)
(*******************************)
(*********)
Fixpoint sum_nat_f_O [f:nat->nat;n:nat]:nat:=       
  Cases n of                            
    O => (f O)                               
   |(S n') => (plus (sum_nat_f_O f n') (f (S n'))) 
  end.

(*********)
Definition sum_nat_f [s,n:nat;f:nat->nat]:nat:=      
  (sum_nat_f_O [x:nat](f (plus x s)) (minus n s)).

(*********)
Definition sum_nat_O [n:nat]:nat:=
  (sum_nat_f_O [x]x n).

(*********)
Definition sum_nat [s,n:nat]:nat:=
  (sum_nat_f s n [x]x).

(*******************************)
(*             Sum             *)
(*******************************)
(*********)
Fixpoint sum_f_R0 [f:nat->R;N:nat]:R:=
  Cases N of
     O     => (f O)
    |(S i) => (Rplus (sum_f_R0 f i) (f (S i)))
  end.

(*********)
Definition sum_f [s,n:nat;f:nat->R]:R:=      
  (sum_f_R0 [x:nat](f (plus x s)) (minus n s)).

(*******************************)
(*        Infinit Sum          *)
(*******************************)
(*********)
Definition infinit_sum:(nat->R)->R->Prop:=[s:nat->R;l:R]
  (eps:R)(Ex[N:nat](n:nat)(ge n N)/\(Rlt (R_dist (sum_f_R0 s n) l) eps)).


