
(* $Id$ *)

Require ZArith.
Require Omega.
Require Wf_nat.

(* Multiplication by a number >0 preserves Zcompare. It also perserves
  Zle, Zlt, Zge, Zgt *)

Implicit Arguments On.

Lemma Zmult_zero : (x,y:Z)`x*y=0` -> `x=0` \/ `y=0`.
Destruct x; Destruct y; Auto.
Simpl; Intros; Discriminate H.
Simpl; Intros; Discriminate H.
Simpl; Intros; Discriminate H.
Simpl; Intros; Discriminate H.
Save.

Lemma Zeq_Zminus : (x,y:Z)x=y -> `x-y = 0`.
Intros; Omega.
Save.

Lemma Zminus_Zeq : (x,y:Z)`x-y=0` -> x=y.
Intros; Omega.
Save.

Lemma Zmult_Zminus_distr_l : (x,y,z:Z)`(x-y)*z = x*z - y*z`.
Intros; Unfold Zminus.
Rewrite <- Zopp_Zmult.
Apply Zmult_plus_distr_l.
Save.

Lemma  Zmult_Zminus_distr_r : (x,y,z:Z)`z*(x-y) = z*x - z*y`.
Intros; Rewrite (Zmult_sym z `x-y`).
Rewrite (Zmult_sym  z x).
Rewrite (Zmult_sym z y).
Apply Zmult_Zminus_distr_l.
Save.

Lemma Zmult_reg_left : (x,y,z:Z)`z>0` -> `z*x=z*y` -> x=y.
Intros.
Generalize (Zeq_Zminus H0).
Intro.
Apply Zminus_Zeq.
Rewrite <- (Zmult_Zminus_distr_r x y z) in H1. 
Elim (Zmult_zero H1).
Omega.
Trivial.
Save.

Lemma Zmult_reg_right : (x,y,z:Z)`z>0` -> `x*z=y*z` -> x=y.
Intros x y z Hz.
Rewrite (Zmult_sym x z).
Rewrite (Zmult_sym y z).
Intro; Apply Zmult_reg_left with z; Assumption.
Save.
    
Lemma Zgt0_le_pred : (y:Z) `y > 0` -> `0 <= (Zpred y)`.
Intro; Unfold Zpred; Omega.
Save.

Lemma Zlt_Zplus : 
  (x1,x2,y1,y2:Z)`x1 < x2` -> `y1 < y2` -> `x1 + y1 < x2 + y2`.
Intros; Omega.
Save.

Lemma Zlt_Zmult_right : (x,y,z:Z)`z>0` -> `x < y` -> `x*z < y*z`.

Intros; Rewrite (Zs_pred z); Generalize (Zgt0_le_pred H); Intro;
Apply natlike_ind with P:=[z:Z]`x*(Zs z) < y*(Zs z)`;
[ Simpl; Do 2 '(Rewrite Zmult_n_1); Assumption
| Unfold Zs; Intros x0 Hx0; Do 6 '(Rewrite Zmult_plus_distr_r);
  Repeat Rewrite Zmult_n_1;
  Intro; Apply Zlt_Zplus; Assumption
| Assumption ].
Save.

Lemma Zlt_Zmult_right2 : (x,y,z:Z)`z>0`  -> `x*z < y*z` -> `x < y`.
Intros x y z H; Rewrite (Zs_pred z).
Apply natlike_ind with P:=[z:Z]`x*(Zs z) < y*(Zs z)`->`x < y`.
Simpl; Do 2 Rewrite Zmult_n_1; Auto 1.
Unfold Zs.
Intros x0 Hx0; Repeat Rewrite Zmult_plus_distr_r.
Repeat Rewrite Zmult_n_1.
Auto with zarith.
Unfold Zpred; Omega.
Save.

Lemma Zle_Zmult_right : (x,y,z:Z)`z>0` -> `x <= y` -> `x*z <= y*z`.
Intros x y z Hz Hxy.
Elim (Zle_lt_or_eq x y Hxy).
Intros; Apply Zlt_le_weak.
Apply Zlt_Zmult_right; Trivial.
Intros; Apply Zle_refl.
Rewrite H; Trivial.
Save.

Lemma Zle_Zmult_right2 :  (x,y,z:Z)`z>0` -> `x*z <= y*z` -> `x <= y`.
Intros x y z Hz Hxy.
Elim (Zle_lt_or_eq `x*z` `y*z` Hxy).
Intros; Apply Zlt_le_weak.
Apply Zlt_Zmult_right2 with z; Trivial.
Intros; Apply Zle_refl.
Apply Zmult_reg_right with z; Trivial.
Save.

Lemma Zgt_Zmult_right : (x,y,z:Z)`z>0` -> `x > y` -> `x*z > y*z`.

Intros; Apply Zlt_gt; Apply Zlt_Zmult_right; 
[ Assumption | Apply Zgt_lt ; Assumption ].
Save.

Lemma Zlt_Zmult_left : (x,y,z:Z)`z>0` -> `x < y` -> `z*x < z*y`.

Intros;
Rewrite (Zmult_sym z x); Rewrite (Zmult_sym z y);
Apply Zlt_Zmult_right; Assumption.
Save.

Lemma Zgt_Zmult_left : (x,y,z:Z)`z>0` -> `x > y` -> `z*x > z*y`.
Intros;
Rewrite (Zmult_sym z x); Rewrite (Zmult_sym z y);
Apply Zgt_Zmult_right; Assumption.
Save.

Theorem Zcompare_Zmult_right : (x,y,z:Z)` z>0` -> `x ?= y`=`x*z ?= y*z`.

Intros; Apply Zcompare_egal_dec;
[ Intros; Apply Zlt_Zmult_right; Trivial
| Intro Hxy; Apply [a,b:Z](let (t1,t2)=(Zcompare_EGAL a b) in t2);
  Rewrite ((let (t1,t2)=(Zcompare_EGAL x y) in t1) Hxy); Trivial
| Intros; Apply Zgt_Zmult_right; Trivial
].
Save.

Theorem  Zcompare_Zmult_left : (x,y,z:Z)`z>0` -> `x ?= y`=`z*x ?= z*y`.
Intros;
Rewrite (Zmult_sym z x);
Rewrite (Zmult_sym z y);
Apply Zcompare_Zmult_right; Assumption.
Save.


Section diveucl.

Lemma two_or_two_plus_one : (x:Z) { y:Z | `x = 2*y`}+{ y:Z | `x = 2*y+1`}. 
Destruct x.
Left ; Split with ZERO; Reflexivity.

Destruct p.
Right ; Split with (POS p0); Reflexivity.

Left ; Split with (POS p0); Reflexivity.

Right ; Split with ZERO; Reflexivity.

Destruct p.
Right ; Split with (NEG (add xH p0)).
Rewrite NEG_xI.
Rewrite NEG_add.
Omega.

Left ; Split with (NEG p0); Reflexivity.

Right ; Split with `-1`; Reflexivity.
Save.

(* The biggest power of 2 that is stricly less than a *)
(* Easy to compute : replace all "1" of the binary representation by
   "0", except the first "1" (or the first one :-) *)
Fixpoint floor_pos [a : positive] : positive :=
  Cases a of
  | xH => xH
  | (xO a') => (xO (floor_pos a'))
  | (xI b') => (xO (floor_pos b'))
  end.

Definition floor := [a:positive](POS (floor_pos a)).

Lemma floor_gt0 : (x:positive) `(floor x) > 0`.
Intro.
Compute.
Trivial.
Save.

Lemma floor_ok : (a:positive) 
  `(floor a) <=  (POS a) < 2*(floor a)`. 
Unfold floor.
Induction a.

Intro p; Simpl.
Repeat Rewrite POS_xI.
Rewrite (POS_xO (xO (floor_pos p))).
Rewrite (POS_xO (floor_pos p)).
Omega.

Intro p; Simpl.
Repeat Rewrite POS_xI.
Rewrite (POS_xO (xO (floor_pos p))).
Rewrite (POS_xO (floor_pos p)).
Rewrite (POS_xO p).
Omega.

Simpl; Omega.
Save.

Lemma Zdiv_eucl_POS : (b:Z)`b > 0` -> (p:positive)
  { qr:Z*Z | let (q,r)=qr in `(POS p)=b*q+r` /\ `0 <= r < b` }.

Induction p.

(* p => (xI p) *)
(* Notez l'utilisation des nouveaux patterns Intro *)
Intros p' ((q,r), (Hrec1, Hrec2)).
Elim (Z_lt_ge_dec `2*r+1` b); 
[ Exists `(2*q, 2*r+1)`;
  Rewrite POS_xI;
  Rewrite Hrec1;
  Split; 
  [ Rewrite Zmult_Zplus_distr; 
    Rewrite Zplus_assoc_l;
    Rewrite (Zmult_permute b `2`);
    Reflexivity
  | Omega ]
| Exists `(2*q+1, 2*r+1-b)`;
  Rewrite POS_xI;
  Rewrite Hrec1;
  Split; 
  [ Do 2 Rewrite Zmult_Zplus_distr; 
    Unfold Zminus;
    Do 2 Rewrite Zplus_assoc_l;
    Rewrite <- (Zmult_permute `2` b);
    Generalize `b*q`; Intros; Omega
  | Omega ]
].

(* p => (xO p) *)
Intros p' ((q,r), (Hrec1, Hrec2)).
Elim (Z_lt_ge_dec `2*r` b); 
[ Exists `(2*q,2*r)`;
  Rewrite POS_xO;
  Rewrite Hrec1;
  Split; 
  [ Rewrite Zmult_Zplus_distr; 
    Rewrite (Zmult_permute b `2`);
    Reflexivity
  | Omega ]
| Exists `(2*q+1, 2*r-b)`;
  Rewrite POS_xO;
  Rewrite Hrec1;
  Split; 
  [ Do 2 Rewrite Zmult_Zplus_distr; 
    Unfold Zminus;
    Rewrite <- (Zmult_permute `2` b);
    Generalize `b*q`; Intros; Omega
  | Omega ]
].
(* xH *)
Elim (Z_le_gt_dec `2` b);
[ Exists `(0,1)`; Omega
| Exists `(1,0)`; Omega 
].
Save.

Theorem Zdiv_eucl : (b:Z)`b > 0` -> (a:Z)
  { qr:Z*Z | let (q,r)=qr in `a=b*q+r` /\ `0 <= r < b` }.
Destruct a;

[ (* a=0 *) Exists `(0,0)`; Omega
| (* a = (POS p) *) Intros; Apply Zdiv_eucl_POS; Auto
| (* a = (NEG p) *) Intros; Elim (Zdiv_eucl_POS H p);
  Intros (q,r) (Hp1, Hp2);
  Elim (Z_le_gt_dec r `0`); 
  [ Exists `(-q,0)`; Split;
    [ Apply Zopp_intro; Simpl; Rewrite Hp1;
      Rewrite Zero_right; 
      Rewrite <- Zopp_Zmult;
      Rewrite Zmult_Zopp_Zopp;
      Generalize `b*q`; Intro; Omega 
    | Omega
    ]
  | Exists `(-(q+1),b-r)`; Split;
    [ Apply Zopp_intro;
      Unfold Zminus; Simpl; Rewrite Hp1;
      Repeat Rewrite Zopp_Zplus;
      Repeat Rewrite <- Zopp_Zmult;
      Rewrite Zmult_Zplus_distr;
      Rewrite Zmult_Zopp_Zopp;
      Rewrite Zplus_assoc_r;
      Apply f_equal with f:=[c:Z]`b*q+c`;
      Omega
    | Omega ]
  ]
].
Save.

End diveucl.
