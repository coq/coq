
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
Fixpoint sum_nat_aux [s,n:nat]:nat:=       
  Cases n of                            
    O => s                                
   |(S n') => (sum_nat_aux (plus s n) n') 
  end.

(*********)
Definition sum_nat:=(sum_nat_aux O).  

(*******************************)
(*             Sum             *)
(*******************************)
(*********)
Fixpoint sum_aux [s:R;f:nat->R;N:nat]:R:=
  Cases N of
     O     => (Rplus s (f O))
    |(S i) => (sum_aux (Rplus s (f N)) f i)
  end.
 
(*********)
Definition sum_f:=(sum_aux R0).  

(*******************************)
(*        Infinit Sum          *)
(*******************************)
(*********)
Definition infinit_sum:(nat->R)->R->Prop:=[s:nat->R;l:R]
  (eps:R)(Ex[N:nat](n:nat)(ge n N)/\(Rlt (R_dist (sum_f s n) l) eps)).
