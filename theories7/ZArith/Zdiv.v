(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* Contribution by Claude Marché and Xavier Urbain *)

(**

Euclidean Division

Defines first of function that allows Coq to normalize. 
Then only after proves the main required property.

*)

Require Export ZArith_base.
Require Zbool.
Require Omega.
Require ZArithRing.
Require Zcomplements.
V7only [Import Z_scope.].
Open Local Scope Z_scope.

(**

  Euclidean division of a positive by a integer 
  (that is supposed to be positive).

  total function than returns an arbitrary value when
  divisor is not positive
  
*)

Fixpoint Zdiv_eucl_POS [a:positive] : Z -> Z*Z := [b:Z]
 Cases a of
 | xH => if `(Zge_bool b 2)` then `(0,1)` else `(1,0)` 
 | (xO a') => 
    let (q,r) = (Zdiv_eucl_POS a' b) in 
    [r':=`2*r`] if `(Zgt_bool b r')` then `(2*q,r')` else `(2*q+1,r'-b)`
 | (xI a') =>
    let (q,r) = (Zdiv_eucl_POS a' b) in 
    [r':=`2*r+1`] if `(Zgt_bool b r')` then `(2*q,r')` else `(2*q+1,r'-b)`
 end.


(**

  Euclidean division of integers.
 
  Total function than returns (0,0) when dividing by 0. 

*) 
    
(* 

  The pseudo-code is:
  
  if b = 0 : (0,0)
 
  if b <> 0 and a = 0 : (0,0)

  if b > 0 and a < 0 : let (q,r) = div_eucl_pos (-a) b in 
                       if r = 0 then (-q,0) else (-(q+1),b-r)

  if b < 0 and a < 0 : let (q,r) = div_eucl (-a) (-b) in (q,-r)

  if b < 0 and a > 0 : let (q,r) = div_eucl a (-b) in 
                       if r = 0 then (-q,0) else (-(q+1),b+r)

  In other word, when b is non-zero, q is chosen to be the greatest integer 
  smaller or equal to a/b. And sgn(r)=sgn(b) and |r| < |b|.

*)

Definition Zdiv_eucl [a,b:Z] : Z*Z :=
  Cases a b of
  | ZERO _  => `(0,0)`
  | _ ZERO  => `(0,0)`
  | (POS a') (POS _) => (Zdiv_eucl_POS a' b)
  | (NEG a') (POS _) => 
      let (q,r) = (Zdiv_eucl_POS a' b) in 
      Cases r of 
      | ZERO => `(-q,0)`
      | _    => `(-(q+1),b-r)`
      end
  | (NEG a') (NEG b') => 
	 let (q,r) = (Zdiv_eucl_POS a' (POS b')) in `(q,-r)`
  | (POS a') (NEG b') =>
      let (q,r) = (Zdiv_eucl_POS a' (POS b')) in 
      Cases r of 
      | ZERO => `(-q,0)`
      | _    => `(-(q+1),b+r)`
      end
    end.


(** Division and modulo are projections of [Zdiv_eucl] *)
     
Definition Zdiv [a,b:Z] : Z := let (q,_) = (Zdiv_eucl a b) in q.

Definition Zmod [a,b:Z] : Z := let (_,r) = (Zdiv_eucl a b) in r. 

(* Tests:

Eval Compute in `(Zdiv_eucl 7 3)`. 

Eval Compute in `(Zdiv_eucl (-7) 3)`.

Eval Compute in `(Zdiv_eucl 7 (-3))`.

Eval Compute in `(Zdiv_eucl (-7) (-3))`.

*)


(**

  Main division theorem. 

  First a lemma for positive

*)

Lemma Z_div_mod_POS : (b:Z)`b > 0` -> (a:positive)
  let (q,r)=(Zdiv_eucl_POS a b) in `(POS a) = b*q + r`/\`0<=r<b`.
Proof.
Induction a; Unfold Zdiv_eucl_POS; Fold Zdiv_eucl_POS.

Intro p; Case (Zdiv_eucl_POS p b); Intros q r (H0,H1).
Generalize (Zgt_cases b `2*r+1`).
Case (Zgt_bool b `2*r+1`); 
(Rewrite POS_xI; Rewrite H0; Split ; [ Ring | Omega ]).

Intros p; Case (Zdiv_eucl_POS p b); Intros q r (H0,H1).
Generalize (Zgt_cases b `2*r`).
Case (Zgt_bool b `2*r`);
 Rewrite POS_xO; Change (POS (xO p)) with `2*(POS p)`; 
 Rewrite H0; (Split; [Ring | Omega]).

Generalize (Zge_cases b `2`).
Case (Zge_bool b `2`); (Intros; Split; [Ring | Omega ]).
Omega.
Qed.


Theorem Z_div_mod : (a,b:Z)`b > 0` -> 
  let (q,r) = (Zdiv_eucl a b) in `a = b*q + r` /\ `0<=r<b`.
Proof.
Intros a b; Case a; Case b; Try (Simpl; Intros; Omega).
Unfold Zdiv_eucl; Intros; Apply Z_div_mod_POS; Trivial.

Intros; Discriminate.

Intros.
Generalize (Z_div_mod_POS (POS p) H p0).
Unfold Zdiv_eucl.
Case (Zdiv_eucl_POS p0 (POS p)).
Intros z z0.
Case z0.

Intros [H1 H2].
Split; Trivial.
Replace (NEG p0) with `-(POS p0)`; [ Rewrite H1; Ring | Trivial ].

Intros p1 [H1 H2].
Split; Trivial.
Replace (NEG p0) with `-(POS p0)`; [ Rewrite H1; Ring | Trivial ].
Generalize (POS_gt_ZERO p1); Omega.

Intros p1 [H1 H2].
Split; Trivial.
Replace (NEG p0) with `-(POS p0)`; [ Rewrite H1; Ring | Trivial ].
Generalize (NEG_lt_ZERO p1); Omega.

Intros; Discriminate.
Qed.

(** Existence theorems *)

Theorem Zdiv_eucl_exist : (b:Z)`b > 0` -> (a:Z)
  { qr:Z*Z | let (q,r)=qr in `a=b*q+r` /\ `0 <= r < b` }.
Proof.
Intros b Hb a.
Exists (Zdiv_eucl a b).
Exact (Z_div_mod a b Hb).
Qed.

Implicits Zdiv_eucl_exist.

Theorem Zdiv_eucl_extended : (b:Z)`b <> 0` -> (a:Z)
  { qr:Z*Z | let (q,r)=qr in `a=b*q+r` /\ `0 <= r < |b|` }.
Proof.
Intros b Hb a.
Elim (Z_le_gt_dec `0` b);Intro Hb'.
Cut `b>0`;[Intro Hb''|Omega].
Rewrite Zabs_eq;[Apply Zdiv_eucl_exist;Assumption|Assumption].
Cut `-b>0`;[Intro Hb''|Omega].
Elim (Zdiv_eucl_exist Hb'' a);Intros qr.
Elim qr;Intros q r Hqr.
Exists (pair ? ? `-q` r).
Elim Hqr;Intros.
Split.
Rewrite <- Zmult_Zopp_left;Assumption.
Rewrite Zabs_non_eq;[Assumption|Omega].
Qed.

Implicits Zdiv_eucl_extended.

(** Auxiliary lemmas about [Zdiv] and [Zmod] *)

Lemma Z_div_mod_eq : (a,b:Z)`b > 0` -> `a = b * (Zdiv a b) + (Zmod a b)`.
Proof.
Unfold Zdiv Zmod.
Intros a b Hb.
Generalize (Z_div_mod a b Hb).
Case (Zdiv_eucl); Tauto.
Save.

Lemma Z_mod_lt : (a,b:Z)`b > 0` -> `0 <= (Zmod a b) < b`.
Proof.
Unfold Zmod.
Intros a b Hb.
Generalize (Z_div_mod a b Hb).
Case (Zdiv_eucl a b); Tauto.
Save.

Lemma Z_div_POS_ge0 : (b:Z)(a:positive)
  let (q,_) = (Zdiv_eucl_POS a b) in `q >= 0`.
Proof.
Induction a; Unfold Zdiv_eucl_POS; Fold Zdiv_eucl_POS.
Intro p; Case (Zdiv_eucl_POS p b).
Intros; Case (Zgt_bool b `2*z0+1`); Intros; Omega.
Intro p; Case (Zdiv_eucl_POS p b).
Intros; Case (Zgt_bool b `2*z0`); Intros; Omega.
Case (Zge_bool b `2`); Simpl; Omega.
Save.

Lemma Z_div_ge0 : (a,b:Z)`b > 0` -> `a >= 0` -> `(Zdiv a b) >= 0`.
Proof.
Intros a b Hb; Unfold Zdiv Zdiv_eucl; Case a; Simpl; Intros.
Case b; Simpl; Trivial.
Generalize Hb; Case b; Try Trivial.
Auto with zarith.
Intros p0 Hp0; Generalize (Z_div_POS_ge0 (POS p0) p).
Case (Zdiv_eucl_POS p (POS p0)); Simpl; Tauto.
Intros; Discriminate.
Elim H; Trivial.
Save.

Lemma Z_div_lt : (a,b:Z)`b >= 2` -> `a > 0` -> `(Zdiv a b) < a`.
Proof.
Intros. Cut `b > 0`; [Intro Hb | Omega].
Generalize (Z_div_mod a b Hb).
Cut `a >= 0`; [Intro Ha | Omega].
Generalize (Z_div_ge0 a b Hb Ha).
Unfold Zdiv; Case (Zdiv_eucl a b); Intros q r H1 [H2 H3].
Cut `a >= 2*q` -> `q < a`; [ Intro h; Apply h; Clear h | Intros; Omega ].
Apply Zge_trans with `b*q`.
Omega.
Auto with zarith.
Save.

(** Syntax *)

V7only[
Grammar znatural expr2 : constr :=
  expr_div  [ expr2($p) "/" expr2($c) ] -> [ (Zdiv $p $c) ]
| expr_mod  [ expr2($p) "%" expr2($c) ] -> [ (Zmod $p $c) ]
.

Syntax constr
  level 6:
    Zdiv [ (Zdiv $n1 $n2) ]
      -> [ [<hov 0> "`"(ZEXPR $n1):E "/" [0 0] (ZEXPR $n2):L "`"] ]
  | Zmod [ (Zmod $n1 $n2) ]
      -> [ [<hov 0> "`"(ZEXPR $n1):E "%" [0 0] (ZEXPR $n2):L "`"] ]
  | Zdiv_inside
      [ << (ZEXPR <<(Zdiv $n1 $n2)>>) >> ]
      	 -> [ (ZEXPR $n1):E "/" [0 0] (ZEXPR $n2):L ]
  | Zmod_inside
      [ << (ZEXPR <<(Zmod $n1 $n2)>>) >> ]
      	 -> [ (ZEXPR $n1):E " %" [1 0] (ZEXPR $n2):L ]
.
].


Infix 3 "/" Zdiv (no associativity) : Z_scope V8only.
Infix 3 "mod" Zmod (no associativity) : Z_scope.

(** Other lemmas (now using the syntax for [Zdiv] and [Zmod]). *)

Lemma Z_div_ge : (a,b,c:Z)`c > 0`->`a >= b`->`a/c >= b/c`.
Proof.
Intros a b c cPos aGeb.
Generalize (Z_div_mod_eq a c cPos).
Generalize (Z_mod_lt a c cPos).
Generalize (Z_div_mod_eq b c cPos).
Generalize (Z_mod_lt b c cPos).
Intros.
Elim (Z_ge_lt_dec `a/c` `b/c`); Trivial.
Intro.
Absurd `b-a >= 1`.
Omega.
Rewrite -> H0.
Rewrite -> H2.
Assert `c*(b/c)+b % c-(c*(a/c)+a % c) = c*(b/c - a/c) + b % c - a % c`.
Ring.
Rewrite H3.
Assert `c*(b/c-a/c) >= c*1`.
Apply Zge_Zmult_pos_left.
Omega.
Omega.
Assert `c*1=c`.
Ring.
Omega.
Save.

Lemma Z_mod_plus : (a,b,c:Z)`c > 0`->`(a+b*c) % c = a % c`.
Proof.
Intros a b c cPos.
Generalize (Z_div_mod_eq a c cPos).
Generalize (Z_mod_lt a c cPos).
Generalize (Z_div_mod_eq `a+b*c` c cPos).
Generalize (Z_mod_lt `a+b*c` c cPos).
Intros.

Assert `(a+b*c) % c - a % c = c*(b+a/c - (a+b*c)/c)`.
Replace `(a+b*c) % c` with `a+b*c - c*((a+b*c)/c)`.
Replace `a % c` with `a - c*(a/c)`.
Ring.
Omega.
Omega.
LetTac q := `b+a/c-(a+b*c)/c`.
Apply (Zcase_sign q); Intros.
Assert `c*q=0`.
Rewrite H4; Ring.
Rewrite H5 in H3.
Omega.

Assert `c*q >= c`.
Pattern 2 c; Replace c with `c*1`.
Apply Zge_Zmult_pos_left; Omega.
Ring.
Omega.

Assert `c*q <= -c`.
Replace `-c` with `c*(-1)`.
Apply Zle_Zmult_pos_left; Omega.
Ring.
Omega.
Save.

Lemma Z_div_plus : (a,b,c:Z)`c > 0`->`(a+b*c)/c = a/c+b`.
Proof.
Intros a b c cPos.
Generalize (Z_div_mod_eq a c cPos).
Generalize (Z_mod_lt a c cPos).
Generalize (Z_div_mod_eq `a+b*c` c cPos).
Generalize (Z_mod_lt `a+b*c` c cPos).
Intros.
Apply Zmult_reg_left with c. Omega.
Replace `c*((a+b*c)/c)` with `a+b*c-(a+b*c) % c`.
Rewrite (Z_mod_plus a b c cPos).
Pattern 1 a; Rewrite H2.
Ring.
Pattern 1 `a+b*c`; Rewrite H0.
Ring.
Save.

Lemma Z_div_mult : (a,b:Z)`b > 0`->`(a*b)/b = a`.
Intros; Replace `a*b` with `0+a*b`; Auto.
Rewrite Z_div_plus; Auto.
Save.

Lemma Z_mult_div_ge : (a,b:Z)`b>0`->`b*(a/b) <= a`.
Proof.
Intros a b bPos.
Generalize (Z_div_mod_eq `a` ? bPos); Intros.
Generalize (Z_mod_lt `a` ? bPos); Intros.
Pattern 2 a; Rewrite H.
Omega.
Save.

Lemma Z_mod_same : (a:Z)`a>0`->`a % a=0`.
Proof.
Intros a aPos.
Generalize (Z_mod_plus `0` `1` a aPos).
Replace `0+1*a` with `a`.
Intros.
Rewrite H.
Compute.
Trivial.
Ring.
Save.

Lemma Z_div_same : (a:Z)`a>0`->`a/a=1`.
Proof.
Intros a aPos.
Generalize (Z_div_plus `0` `1` a aPos).
Replace `0+1*a` with `a`.
Intros.
Rewrite H.
Compute.
Trivial.
Ring.
Save.

Lemma Z_div_exact_1 : (a,b:Z)`b>0` -> `a = b*(a/b)` -> `a%b = 0`.
Intros a b Hb; Generalize (Z_div_mod a b Hb); Unfold Zmod Zdiv.
Case (Zdiv_eucl a b); Intros q r; Omega.
Save.

Lemma Z_div_exact_2 : (a,b:Z)`b>0` -> `a%b = 0` -> `a = b*(a/b)`.
Intros a b Hb; Generalize (Z_div_mod a b Hb); Unfold Zmod Zdiv.
Case (Zdiv_eucl a b); Intros q r; Omega.
Save.

Lemma Z_mod_zero_opp : (a,b:Z)`b>0` -> `a%b = 0` -> `(-a)%b = 0`.
Intros a b Hb.
Intros.
Rewrite Z_div_exact_2 with a b; Auto.
Replace `-(b*(a/b))` with `0+(-(a/b))*b`.
Rewrite Z_mod_plus; Auto.
Ring.
Save.

