(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id$ i*)

(* Efficient computation of X^n using
 * 
 *    X^(2n)   =     (X^n) ^ 2
 *    X^(2n+1) = X . (X^n) ^ 2
 *
 * Proofs of both fonctional and imperative programs.
 *)

Require Even.
Require Div2.
Require Correctness.
Require ArithRing.
Require ZArithRing.

(* The specification uses the traditional definition of X^n *)

Fixpoint power [x,n:nat] : nat :=
  Cases n of
    O      => (S O)
  | (S n') => (mult x (power x n'))
  end.

Definition square := [n:nat](mult n n).


(* Three lemmas are necessary to establish the forthcoming proof obligations *)

(* n = 2*(n/2) => (x^(n/2))^2 = x^n *)

Lemma exp_div2_0 : (x,n:nat)
     n=(double (div2 n)) 
  -> (square (power x (div2 n)))=(power x n).
Proof.
Unfold square.
Intros x n. Pattern n. Apply ind_0_1_SS.
Auto.

Intro. (Absurd (1)=(double (0)); Auto).

Intros. Simpl.
Cut n0=(double (div2 n0)).
Intro. Rewrite <- (H H1).
Ring.

Simpl in H0.
Unfold double in H0.
Simpl in H0.
Rewrite <- (plus_n_Sm (div2 n0) (div2 n0)) in H0.
(Injection H0; Auto).
Save.

(* n = 2*(n/2)+1 => x*(x^(n/2))^2 = x^n *)

Lemma exp_div2_1 : (x,n:nat) 
     n=(S (double (div2 n)))
  -> (mult x (square (power x (div2 n))))=(power x n).
Proof.
Unfold square.
Intros x n. Pattern n. Apply ind_0_1_SS.

Intro. (Absurd (0)=(S (double (0))); Auto).

Auto.

Intros. Simpl.
Cut n0=(S (double (div2 n0))).
Intro. Rewrite <- (H H1).
Ring.

Simpl in H0.
Unfold double in H0.
Simpl in H0.
Rewrite <- (plus_n_Sm (div2 n0) (div2 n0)) in H0.
(Injection H0; Auto).
Save.

(* x^(2*n) = (x^2)^n *)

Lemma power_2n : (x,n:nat)(power x (double n))=(power (square x) n).
Proof.
Unfold double. Unfold square.
Induction n.
Auto.

Intros.
Simpl.
Rewrite <- H.
Rewrite <- (plus_n_Sm n0 n0).
Simpl.
Auto with arith.
Save.

Hints Resolve exp_div2_0 exp_div2_1.


(* Functional version.
 * 
 * Here we give the functional program as an incomplete CIC term,
 * using the tactic Refine.
 *
 * On this example, it really behaves as the tactic Program.
 *)

(*
Lemma f_exp : (x,n:nat) { y:nat | y=(power x n) }.
Proof.
Refine [x:nat]
  (well_founded_induction nat lt lt_wf
    [n:nat]{y:nat | y=(power x n) }
    [n:nat]
    [f:(p:nat)(lt p n)->{y:nat | y=(power x p) }]
      	     Cases (zerop n) of 
               (left _) => (exist ? ? (S O) ?)
      	     | (right _) => 
      	       	  let (y,H) = (f (div2 n) ?) in 
      	       	  Cases (even_odd_dec n) of
      	       	    (left _) => (exist ? ? (mult y y) ?)
                  | (right _) => (exist ? ? (mult x (mult y y)) ?)
		  end
	     end).
Proof.
Rewrite a. Auto.
Exact (lt_div2 n a).
Change (square y)=(power x n). Rewrite H. Auto with arith.
Change (mult x (square y))=(power x n). Rewrite H. Auto with arith.
Save.
*)

(* Imperative version. *)

Definition even_odd_bool := [x:nat](bool_of_sumbool ? ? (even_odd_dec x)).

Correctness i_exp
  fun (x:nat)(n:nat) ->
    let y = ref (S O) in
    let m = ref x in
    let e = ref n in
    begin
      while (notzerop_bool !e) do
        { invariant (power x n)=(mult y (power m e)) as Inv
          variant e for lt }
        (if not (even_odd_bool !e) then y := (mult !y !m))
          { (power x n) = (mult y (power m (double (div2 e)))) as Q };
        m := (square !m);
        e := (div2 !e)
      done;
      !y
    end
    { result=(power x n) }
.
Proof.
Rewrite (odd_double e0 Test1) in Inv. Rewrite Inv. Simpl. Auto with arith.

Rewrite (even_double e0 Test1) in Inv. Rewrite Inv. Reflexivity.

Split.
Exact (lt_div2 e0 Test2).

Rewrite Q. Unfold double. Unfold square.
Simpl. 
Change (mult y1 (power m0 (double (div2 e0))))
     = (mult y1 (power (square m0) (div2 e0))).
Rewrite (power_2n m0 (div2 e0)). Reflexivity.

Auto with arith.

Decompose [and] Inv.
Rewrite H. Rewrite H0.
Auto with arith.
Save.


(* Recursive version. *)

Correctness r_exp
  let rec exp (x:nat) (n:nat) : nat { variant n for lt} =
    (if (zerop_bool n) then
       (S O)
     else
       let y = (exp x (div2 n)) in
       if (even_odd_bool n) then
         (mult y y)
       else
         (mult x (mult y y))
    ) { result=(power x n) }
.
Proof.
Rewrite Test2. Auto.
Exact (lt_div2 n0 Test2).
Change (square y)=(power x0 n0). Rewrite Post7. Auto with arith.
Change (mult x0 (square y))=(power x0 n0). Rewrite Post7. Auto with arith.
Save.
