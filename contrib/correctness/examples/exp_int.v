(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

(* Efficient computation of X^n using
 * 
 *    X^(2n)   =     (X^n) ^ 2
 *    X^(2n+1) = X . (X^n) ^ 2
 *
 * Proofs of both fonctional and imperative programs.
 *)

Require Zpower.
Require Zcomplements.

Require Correctness.
Require ZArithRing.
Require Omega.

Definition Zdouble := [n:Z]`2*n`.

Definition Zsquare := [n:Z](Zmult n n).

(* Some auxiliary lemmas about Zdiv2 are necessary *)

Lemma Zdiv2_ge_0 : (x:Z) `x >= 0` -> `(Zdiv2 x) >= 0`.
Proof.
Destruct x; Auto with zarith.
Destruct p; Auto with zarith.
Simpl. Omega.
Intros. (Absurd `(NEG p) >= 0`; Red; Auto with zarith).
Save.

Lemma Zdiv2_lt : (x:Z) `x > 0` -> `(Zdiv2 x) < x`.
Proof.
Destruct x.
Intro. Absurd `0 > 0`; [ Omega | Assumption ].
Destruct p; Auto with zarith.

Simpl.
Intro p0.
Replace (POS (xI p0)) with `2*(POS p0)+1`.
Omega.
Simpl. Auto with zarith.

Intro p0.
Simpl.
Replace (POS (xO p0)) with `2*(POS p0)`.
Omega.
Simpl. Auto with zarith.

Simpl. Omega.

Intros. 
Absurd `(NEG p) > 0`; Red; Auto with zarith.
Elim p; Auto with zarith.
Omega.
Save.

(* A property of Zpower:  x^(2*n) = (x^2)^n *)

Lemma Zpower_2n : 
  (x,n:Z)`n >= 0` -> (Zpower x (Zdouble n))=(Zpower (Zsquare x) n).
Proof.
Unfold Zdouble.
Intros x n Hn.
Replace `2*n` with `n+n`.
Rewrite Zpower_exp.
Pattern n.
Apply natlike_ind.

Simpl. Auto with zarith.

Intros.
Unfold Zs.
Rewrite Zpower_exp.
Rewrite Zpower_exp.
Replace (Zpower x `1`) with x.
Replace (Zpower (Zsquare x) `1`) with (Zsquare x).
Rewrite <- H0.
Unfold Zsquare.
Ring.

Unfold Zpower; Unfold Zpower_pos; Simpl. Omega.

Unfold Zpower; Unfold Zpower_pos; Simpl. Omega.

Omega.
Omega.
Omega.
Omega.
Omega.
Assumption.
Assumption.
Omega.
Save.


(* The program *)

Correctness i_exp
  fun (x:Z)(n:Z) ->
    { `n >= 0` }
   (let y = ref 1 in
    let m = ref x in
    let e = ref n in
    begin
      while !e > 0 do
        { invariant (Zpower x n)=(Zmult y (Zpower m e)) /\ `e>=0` as Inv
          variant e }
        (if not (Zeven_odd_bool !e) then y := (Zmult !y !m))
          { (Zpower x n) = (Zmult y (Zpower m (Zdouble (Zdiv2 e)))) as Q };
        m := (Zsquare !m);
        e := (Zdiv2 !e)
      done;
      !y
    end)
    { result=(Zpower x n) }
.
Proof.
(* Zodd *)
Decompose [and] Inv.
Rewrite (Zodd_div2 e0 H0 Test1) in H. Rewrite H.
Rewrite Zpower_exp.
Unfold Zdouble.
Replace (Zpower m0 `1`) with m0.
Ring.
Unfold Zpower; Unfold Zpower_pos; Simpl; Ring.
Generalize (Zdiv2_ge_0 e0); Omega.
Omega.
(* Zeven *)
Decompose [and] Inv.
Rewrite (Zeven_div2 e0 Test1) in H. Rewrite H.
Auto with zarith.
Split.
(* Zwf *)
Unfold Zwf.
Repeat Split.
Generalize (Zdiv2_ge_0 e0); Omega.
Omega.
Exact (Zdiv2_lt e0 Test2).
(* invariant *)
Split.
Rewrite Q. Unfold Zdouble. Unfold Zsquare.
Rewrite (Zpower_2n).
Trivial.
Generalize (Zdiv2_ge_0 e0); Omega.
Generalize (Zdiv2_ge_0 e0); Omega.
Split; [ Ring | Assumption ].
(* exit fo loop *)
Decompose [and] Inv.
Cut `e0 = 0`. Intro.
Rewrite H1. Rewrite H.
Simpl; Ring.
Omega.
Save.


(* Recursive version. *)

Correctness r_exp
  let rec exp (x:Z) (n:Z) : Z { variant n } =
    { `n >= 0` }
    (if n = 0 then
       1
     else
       let y = (exp x (Zdiv2 n)) in
       (if (Zeven_odd_bool n) then
       	  (Zmult y y)
        else
          (Zmult x (Zmult y y))) { result=(Zpower x n) as Q }
    ) 
    { result=(Zpower x n) }
.
Proof.
Rewrite Test2. Auto with zarith.
(* w.f. *)
Unfold Zwf.
Repeat Split.
Generalize (Zdiv2_ge_0 n0) ; Omega.
Omega.
Generalize (Zdiv2_lt n0) ; Omega.
(* rec. call *)
Generalize (Zdiv2_ge_0 n0) ; Omega.
(* invariant: case even *)
Generalize (Zeven_div2 n0 Test1).
Intro Heq. Rewrite Heq.
Rewrite Post4.
Replace `2*(Zdiv2 n0)` with `(Zdiv2 n0)+(Zdiv2 n0)`.
Rewrite Zpower_exp.
Auto with zarith.
Generalize (Zdiv2_ge_0 n0) ; Omega.
Generalize (Zdiv2_ge_0 n0) ; Omega.
Omega.
(* invariant: cas odd *)
Generalize (Zodd_div2 n0 Pre1 Test1).
Intro Heq. Rewrite Heq.
Rewrite Post4.
Rewrite Zpower_exp.
Replace `2*(Zdiv2 n0)` with `(Zdiv2 n0)+(Zdiv2 n0)`.
Rewrite Zpower_exp.
Replace `(Zpower x0 1)` with x0.
Ring.
Unfold Zpower; Unfold Zpower_pos; Simpl. Omega.
Generalize (Zdiv2_ge_0 n0) ; Omega.
Generalize (Zdiv2_ge_0 n0) ; Omega.
Omega.
Generalize (Zdiv2_ge_0 n0) ; Omega.
Omega.
Save.
