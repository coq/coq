(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(* Contribution by Claude Marché and Xavier Urbain *)

(**

Euclidean Division

Defines first of function that allows Coq to normalize. 
Then only after proves the main required property.

*)

Require Export ZArith.
Require Omega.
Require ZArithRing.

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
    if `(Zgt_bool b (r+r))` then `(q+q,r+r)` else `(q+q+1,r+r-b)`
 | (xI a') =>
    let (q,r) = (Zdiv_eucl_POS a' b) in 
    if `(Zgt_bool b (r+r+1))` then `(q+q,r+r+1)` else `(q+q+1,r+r+1-b)`
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
Induction a; Simpl.
Intro p.
Case (Zdiv_eucl_POS p b).
Intros q r H1.
Decompose [and] H1.
Generalize (Zgt_cases b `r+r+1`).
Case (Zgt_bool b `r+r+1`); 
(Rewrite POS_xI; Rewrite H0; Split ; [ Ring | Omega ]).

Intros p.
Case (Zdiv_eucl_POS p b).
Intros q r H1.
Decompose [and] H1.
Generalize (Zgt_cases b `r+r`).
Case (Zgt_bool b `r+r`);
(Rewrite POS_xO; Rewrite H0; Split ; [ Ring | Omega ]).

Generalize (Zge_cases b `2`).
Case (Zge_bool b `2`); (Intros; Split; [Ring | Omega ]).
Omega.
Save.



Theorem Z_div_mod : (a,b:Z)`b > 0` -> 
  let (q,r) = (Zdiv_eucl a b) in `a = b*q + r` /\ `0<=r<b`.
Proof.
Intros a b; Case a; Case b; Try (Simpl; Intros; Omega).
Unfold Zdiv_eucl; Intros; Apply Z_div_mod_POS; Trivial.

Intros.
Absurd `(NEG p) > 0`; [ Generalize (NEG_lt_ZERO p); Omega | Trivial ].

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

Intros.
Absurd `(NEG p)>0`; [ Generalize (NEG_lt_ZERO p); Omega | Omega ].
Save.


(** Existence theorems *)

Implicit Arguments On.

Theorem Zdiv_eucl_exist : (b:Z)`b > 0` -> (a:Z)
  { qr:Z*Z | let (q,r)=qr in `a=b*q+r` /\ `0 <= r < b` }.
Proof.
Intros b Hb a.
Exists (Zdiv_eucl a b).
Exact (Z_div_mod a b Hb).
Save.

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
Save.


(** Syntax *)

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
      	 -> [ (ZEXPR $n1):E "%" [0 0] (ZEXPR $n2):L ]
.
