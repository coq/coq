
(* $Id$ *)

(**************************************************************************)
(*              Basic lemmas for the classical reals numbers              *)
(**************************************************************************)

Require Export Raxioms.
Require Export ZArithRing.
Require Classical_Prop.
Require Omega.

(**************************************************************************)
(*       On commence par instancier la tactique Ring sur les réels        *)
(**************************************************************************)


Lemma RTheory : (Ring_Theory Rplus Rmult R1 R0 Ropp [x,y:R]false).
  Split.
  Exact Rplus_sym.
  Symmetry; Apply Rplus_assoc.
  Exact Rmult_sym.
  Symmetry; Apply Rmult_assoc.
  Intro; Apply (let (H1,H2)=(Rplus_ne n) in H2).
  Intro; Apply (let (H1,H2)=(Rmult_ne n) in H2).
  Exact Rplus_Ropp_r.
  Intros.
  Rewrite Rmult_sym.
  Rewrite (Rmult_sym n p).
  Rewrite (Rmult_sym m p).
  Apply Rmult_Rplus_distr.
  Intros; Contradiction.
Defined.

Add Abstract Ring R Rplus Rmult R1 R0 Ropp [x,y:R]false RTheory.

(**************************************************************************)
(*                            Basic Lemmas                                *)
(**************************************************************************)

(**********)
Lemma Req_EM:(r1,r2:R)(r1==r2)\/(~r1==r2).
Intros;Apply (classic r1==r2).
Save.
Hints Resolve Req_EM : real v62.

(**********)
Lemma total_order:(r1,r2:R)((Rlt r1 r2)\/(r1==r2)\/(Rgt r1 r2)).
Intros;Elim (total_order_T r1 r2);Intro;Auto.
Elim y;Intro;Auto.
Save.

(**********)
Lemma not_Req:(r1,r2:R)(~(r1==r2))->((Rlt r1 r2)\/(Rgt r1 r2)).
Intros; Case (total_order r1 r2); Intros.
Left; Exact H0.
Case H0; Intros.
Absurd r1==r2; Auto with zarith real.
Right; Exact H1.
Save.

(**********)
Lemma imp_not_Req:(r1,r2:R)((Rlt r1 r2)\/(Rgt r1 r2))->(~(r1==r2)).
Intros; Elim H; Intro; Clear H;Red; Intro;Rewrite H in H0.
Generalize (Rlt_antisym r2 r2 H0); Intro; Auto with zarith real.
Unfold Rgt in H0;Generalize (Rlt_antisym r2 r2 H0);Intro; Auto with zarith real.
Save.

(**********)
Lemma Rlt_antirefl:(r:R)~(Rlt r r).
  Red; Intros; Apply (Rlt_antisym r r H); Auto with zarith real.
Save.

(**********)
Lemma total_order_Rlt:(r1,r2:R)(sumboolT (Rlt r1 r2) ~(Rlt r1 r2)).
Intros;Elim (total_order_T r1 r2);Intros.
Elim y;Intro.
Left;Assumption.
Right;Rewrite y0;Apply Rlt_antirefl.
Right;Unfold Rgt in y;Apply Rlt_antisym;Assumption.
Save.

(**********)
Lemma total_order_Rle:(r1,r2:R)(sumboolT (Rle r1 r2) ~(Rle r1 r2)).
Intros;Elim (total_order_T r1 r2);Intros.
Left;Unfold Rle;Elim y;Intro;Auto.
Right;Red;Intro;Elim H;Intro.
Unfold Rgt in y;Generalize (Rlt_antisym r2 r1 y);Auto.
Generalize (imp_not_Req r1 r2 (or_intror (Rlt r1 r2) (Rgt r1 r2) y));Auto.
Save.

(**********)
Lemma total_order_Rgt:(r1,r2:R)(sumboolT (Rgt r1 r2) ~(Rgt r1 r2)).
Unfold Rgt;Intros;Apply total_order_Rlt.
Save.

(**********)
Lemma total_order_Rge:(r1,r2:R)(sumboolT (Rge r1 r2) ~(Rge r1 r2)).
Unfold Rge;Unfold Rgt;Intros;Elim (total_order_Rle r2 r1);Intro.
Left;Unfold Rle in y;Elim y;Auto.
Right;Unfold Rle in y;Red;Intro;Elim H;Intro.
Elim y;Left;Assumption.
Elim y;Right;Auto.
Save.

(*********************************************************)
(*         Field Lemmas                                  *)
(*********************************************************)
(*********************************************************)
(*       Addition                                        *)
(*********************************************************)

(**********)
Lemma Rplus_Ropp_l:(r:R)((Rplus (Ropp r) r)==R0).
  Intro; Ring.
Save.

(**********)
Lemma Rplus_Ropp:(x,y:R)((Rplus x y)==R0)->(y==(Ropp x)).
  Intros; Replace y with (Rplus (Rplus (Ropp x) x) y);
  [ Rewrite -> Rplus_assoc; Rewrite -> H; Ring
  | Ring ].
Save.

(* New *)
Hint eqT_R_congr : real := Resolve (congr_eqT R).

Lemma Rplus_plus_r:(r,r1,r2:R)(r1==r2)->((Rplus r r1)==(Rplus r r2)).
  Auto with real.
Save.

(* Old *)
Hints Resolve Rplus_plus_r : v62.

(**********)
Lemma r_Rplus_plus:(r,r1,r2:R)((Rplus r r1)==(Rplus r r2))->(r1==r2).
  Intros;
   Cut (Rplus (Rplus (Ropp r) r) r1)==(Rplus (Rplus (Ropp r) r) r2).
  Ring (Rplus (Rplus (Ropp r) r) r1) (Rplus (Rplus (Ropp r) r) r2); Trivial.
  Repeat Rewrite -> Rplus_assoc; Rewrite <- H; Reflexivity.
Save.

Hints Resolve r_Rplus_plus : real.

(**********)
Lemma Rplus_ne_i:(r,b:R)((Rplus r b)==r)->(b==R0).
  Intros r b; Replace r with (Rplus r R0).
  Rewrite -> Rplus_assoc; Ring (Rplus R0 b); EAuto with real.
  Ring.
Save.

(***********************************************************)       
(*        Multiplication                                   *)
(***********************************************************)

(**********)
Lemma Rinv_r:(r:R)(~(r==R0))->((Rmult r (Rinv r))==R1).
  Intros; Rewrite -> Rmult_sym; Apply (Rinv_l r H); Auto with zarith real.
Save.

(**********)
Lemma Rmult_Or:(r:R)((Rmult r R0)==R0).
Intro; Ring.
Save.
Hints Resolve Rmult_Or : real v62.

(**********)
Lemma Rmult_Ol:(r:R)((Rmult R0 r)==R0).
Intro; Ring.
Save.
Hints Resolve Rmult_Ol : real v62.

(**********)
Lemma Rmult_mult_r:(r,r1,r2:R)(r1==r2)->((Rmult r r1)==(Rmult r r2)).
  Auto with real.
Save.
(* OLD *)
Hints Resolve Rmult_mult_r : v62.

(**********)
Lemma r_Rmult_mult:(r,r1,r2:R)((Rmult r r1)==(Rmult r r2))->
  (~(r==R0))->(r1==r2).
  Intros;
   Cut (Rmult (Rmult (Rinv r) r) r1)==(Rmult (Rmult (Rinv r) r) r2).
  Rewrite -> Rinv_l with r; Ring (Rmult R1 r1) (Rmult R1 r2); Trivial.

  Repeat Rewrite -> Rmult_assoc.
  Rewrite H; Trivial.
Save.

(**********)
Lemma without_div_Od:(r1,r2:R)(Rmult r1 r2)==R0 -> r1==R0 \/ r2==R0.
  Intros; Cut r1==R0\/~r1==R0.
  Intros [Hz | Hnotz].
  Left; Auto.
  Replace r2 with (Rmult R0 (Rinv r1)); Auto with real.
  Apply r_Rmult_mult with r1.
  Rewrite H; Ring.
  Assumption.
  Auto with real.
Save.

(**********)
Lemma without_div_Oi1:(r1,r2:R) r1==R0 -> (Rmult r1 r2)==R0.
  Intros; Rewrite -> H; Ring.
Save.

(**********)
Lemma without_div_Oi2:(r1,r2:R) r2==R0 -> (Rmult r1 r2)==R0.
  Intros; Rewrite -> H; Ring.
Save.

(**********)
Lemma without_div_Oi:(r1,r2:R) (r1==R0)\/(r2==R0) -> (Rmult r1 r2)==R0.
  Intros r1 r2 [H | H]; Rewrite H; Ring.
Save.

(**********) 
Lemma without_div_O_contr:(r1,r2:R)
   ~(Rmult r1 r2)==R0 -> ~r1==R0 /\ ~r2==R0.
Intros; Cut (P,Q,R:Prop)(P\/Q->R)->~R->~P/\~Q.
Intro;Generalize (H0 r1==R0 r2==R0 (Rmult r1 r2)==R0
       (without_div_Oi r1 r2));Intro;Apply (H1 H).
Tauto.
Save.

(**********) 
Lemma Rmult_Rplus_distrl:
   (r1,r2,r3:R) ((Rmult (Rplus r1 r2) r3)==
                (Rplus (Rmult r1 r3) (Rmult r2 r3))).
Intros; Ring.
Save.

(***********)
Definition Rsqr:R->R:=[r:R](Rmult r r).

(***********)
Lemma Rsqr_O:((Rsqr R0)==R0).
  Unfold Rsqr; Ring.
Save.

(***********)
Lemma Rsqr_r_R0:(r:R)(Rsqr r)==R0->r==R0.
Unfold Rsqr;Intros;Elim (without_div_Od r r H);Trivial.
Save.

(*********************************************************)
(*       Opposite                                        *)
(*********************************************************)

(**********)
Lemma Ropp_Ropp:(r:R)((Ropp (Ropp r))==r).
  Intro; Ring.
Save.

(**********)
Lemma Ropp_O:((Ropp R0)==R0).
  Ring.
Save.
Hints Resolve Ropp_O : real v62.

(**********)
Lemma Ropp_distr1:(r1,r2:R)
 ((Ropp (Rplus r1 r2))==(Rplus (Ropp r1) (Ropp r2))).
  Intros; Ring.
Save.

(**********)
Lemma Ropp_distr2:(r1,r2:R)((Ropp (Rminus r1 r2))==(Rminus r2 r1)).
  Intros; Ring.
Save.

(**********)
Lemma eq_Rminus:(r1,r2:R)(r1==r2)->((Rminus r1 r2)==R0).
  Intros; Rewrite H; Ring.
Save.

(**********)
Lemma Rminus_eq:(r1,r2:R)(Rminus r1 r2)==R0 -> r1==r2.
  Intros r1 r2; Unfold Rminus; Rewrite -> Rplus_sym; Intro.
  Rewrite <- (Ropp_Ropp r2); Apply (Rplus_Ropp (Ropp r2) r1 H).
Save.

(**********)
Lemma Rminus_eq_contra:(r1,r2:R)~r1==r2->~(Rminus r1 r2)==R0.
Intros;Cut (P,Q:Prop)(P->Q)->(~Q->~P).
Intro cla;Apply (cla (Rminus r1 r2)==R0  r1==r2 (Rminus_eq r1 r2));Assumption.
Tauto.
Save.

(**********)
Lemma Rminus_distr:
  (x,y,z:R) (Rmult x (Rminus y z))==
            (Rminus (Rmult x y) (Rmult x z)).
Intros; Ring.
Save.

(**********)
Lemma eq_Ropp:(r1,r2:R)(r1==r2)->((Ropp r1)==(Ropp r2)).
  Auto with real.
Save.

(**********)
Lemma eq_RoppO:(r:R)(r==R0)->((Ropp r)==R0).
  Intros; Rewrite -> H; Ring.
Save.

(**********)
Lemma minus_R0:(r:R)(Rminus r R0)==r.
Intro;Unfold Rminus;Rewrite (eq_RoppO R0 (refl_eqT R R0));
 Elim(Rplus_ne r);Intros a b;Rewrite a;Clear a b;Auto with zarith real.
Save.

(**********)
Lemma Ropp_mul1:(r1,r2:R)(Rmult (Ropp r1) r2)==(Ropp (Rmult r1 r2)).
  Intros; Ring.
Save.

(**********)
Lemma Ropp_mul2:(r1,r2:R)(Rmult (Ropp r1) (Ropp r2))==(Rmult r1 r2).
  Intros; Ring.
Save.

(*********)
Lemma Ropp_neq:(r:R)~r==R0->~(Ropp r)==R0.
Intros;Red;Intro;Generalize (Rplus_plus_r r (Ropp r) R0 H0);Intro;
 Rewrite (Rplus_Ropp_r r) in H1;
 Rewrite (let (H1,H2)=(Rplus_ne r) in H1) in H1;
 Generalize (sym_eqT R R0 r H1);Intro;Auto.
Save.

(*********)
Lemma Rinv_R1:(Rinv R1)==R1.
Apply (r_Rmult_mult R1 (Rinv R1) R1);
 [Rewrite (Rinv_r R1 R1_neq_R0);
  Rewrite (let (H1,H2)=(Rmult_ne R1) in H1);Trivial|
  Red;Intro;Apply R1_neq_R0;Assumption].
Save.

(*********)
Lemma Rinv_neq_R0:(r:R)(~r==R0)->~(Rinv r)==R0.
Intros;Red;Intro;Generalize (Rmult_mult_r r (Rinv r) R0 H0);
 Clear H0;Intro;Rewrite (Rinv_r r H) in H0;Rewrite (Rmult_Or r) in H0;
 Generalize R1_neq_R0;Intro;Auto. 
Save.

(*********)
Lemma Rinv_Rinv:(r:R)(~r==R0)->(Rinv (Rinv r))==r.
Intros;Apply (r_Rmult_mult (Rinv r) (Rinv (Rinv r)) r);
 [Rewrite (Rinv_r (Rinv r) (Rinv_neq_R0 r H));
  Rewrite (Rinv_l r H);Trivial |Apply Rinv_neq_R0;Assumption].
Save.

(*********)
Lemma Rinv_Rmult:(r1,r2:R)(~r1==R0)->(~r2==R0)->
  (Rinv (Rmult r1 r2))==(Rmult (Rinv r1) (Rinv r2)).
Intros;Cut ~(Rmult r1 r2)==R0.
Intro;Apply (r_Rmult_mult (Rmult r1 r2));Auto.
Rewrite (Rinv_r (Rmult r1 r2) H1);
 Rewrite (Rmult_sym (Rinv r1) (Rinv r2));
 Rewrite (Rmult_assoc r1 r2  (Rmult (Rinv r2) (Rinv r1)));
 Rewrite <-(Rmult_assoc r2 (Rinv r2) (Rinv r1));
 Rewrite (Rinv_r r2 H0);
 Rewrite (let (H1,H2)=(Rmult_ne (Rinv r1)) in H2);
 Rewrite (Rinv_r r1 H);Trivial.
Red;Intro;Generalize (without_div_Od r1 r2 H1);Intro;Elim H2;Intro;Auto.
Save.

(*********)
Lemma Ropp_Rinv:(r:R)~r==R0->(Ropp (Rinv r))==(Rinv (Ropp r)).
Intros;Generalize (refl_eqT R R1);Pattern 1 R1;
 Rewrite <-(Rinv_l r H);Rewrite <-(Rinv_l (Ropp r) (Ropp_neq r H));
 Intro;Rewrite <-(Ropp_mul2 (Rinv r) r) in H0;
 Rewrite (Rmult_sym (Ropp (Rinv r)) (Ropp r)) in H0;
 Rewrite (Rmult_sym (Rinv (Ropp r)) (Ropp r)) in H0;
 Apply (r_Rmult_mult (Ropp r) (Ropp (Rinv r)) (Rinv (Ropp r))
    H0 (Ropp_neq r H)).
Save.

(*********)
Lemma Rinv_Rmult_simpl:(a,b,c:R)(~a==R0)->
      (Rmult (Rmult a (Rinv b))(Rmult c (Rinv a)))==
      (Rmult c (Rinv b)).
Intros; Rewrite (Rmult_sym (Rmult a (Rinv b)) (Rmult c (Rinv a)));
 Rewrite (Rmult_assoc c (Rinv a) (Rmult a (Rinv b)));
 Rewrite <-(Rmult_assoc (Rinv a) a (Rinv b));
 Rewrite (Rinv_l a H);Rewrite (let (H1,H2)=(Rmult_ne (Rinv b)) in H2);
 Reflexivity.
Save.

(*********************************************************)
(*       Order Lemma                                     *)
(*********************************************************)
(*********************************************************)
(*       Lower                                       *)
(*********************************************************)

(**********)
Lemma not_Rle:(r1,r2:R)~(Rle r1 r2)->(Rgt r1 r2).
Intros; Unfold Rle in H; Elim (total_order r1 r2); Intro.
Elim H;Left; Assumption.
Elim H0; Intro;Auto with zarith real.
Elim H;Right; Assumption.
Save.

(**********)
Lemma Rle_not:(r1,r2:R)(Rlt r2 r1)->~(Rle r1 r2).
Intros; Red; Intro;Unfold Rle in H0;Elim H0; Intro.
Generalize (Rlt_antisym r1 r2 H1); Intro; Auto with zarith real.
Elim (imp_not_Req r2 r1);Auto with zarith real.
Save.

(**********)
Lemma Rlt_ge_not:(r1,r2:R)(Rlt r1 r2)->~(Rge r1 r2).
Intros;Red;Intro;Unfold Rge in H0;Unfold Rgt in H0;Elim H0;Intro.
Apply (Rlt_antisym r1 r2 H H1).
Rewrite H1 in H;Exact (Rlt_antisym r2 r2 H H).
Save.

(**********)
Lemma Rle_le_eq:(r1,r2:R)(Rle r1 r2)/\(Rle r2 r1)<->(r1==r2).
Intros; Split; Intro.
Elim H; Unfold Rle; Intros.
Elim H0; Elim H1; Intros.
Absurd (Rlt r2 r1).
Red; Intro.
Apply (Rlt_antisym r1 r2 H3 H4).
Auto with zarith real.
Auto with zarith real.
Auto with zarith real.
Auto with zarith real.
Rewrite <- H; Split; Unfold Rle; Right; Auto with zarith real.
Save.

(**********)
Lemma Rlt_le:(r1,r2:R)(Rlt r1 r2)->(Rle r1 r2).
Intros; Unfold Rle; Left; Auto with zarith real.
Save.

(**********)
Lemma eq_Rle:(r1,r2:R)(r1==r2)->(Rle r1 r2).
Intros; Unfold Rle; Right; Auto with zarith real.
Save.

(**********)
Lemma Rle_trans:(r1,r2,r3:R)
  (Rle r1 r2)->(Rle r2 r3)->(Rle r1 r3).
Intros r1 r2 r3; Unfold Rle; Intros.
Elim H; Elim H0; Intros.
Cut (Rlt r1 r3).
Intro.
Apply (Rlt_le r1 r3); Auto with zarith real.
Apply (Rlt_trans r1 r2 r3); Auto with zarith real.
Rewrite <- H1; Auto with zarith real.
Rewrite -> H2; Auto with zarith real.
Rewrite -> H2; Auto with zarith real.
Save.

(**********)
Lemma Rle_lt_trans:(r1,r2,r3:R)
  (Rle r1 r2)->(Rlt r2 r3)->(Rlt r1 r3).
Intros; Unfold Rle in H; Elim H; Intro.
Apply (Rlt_trans r1 r2 r3 H1 H0).
Rewrite -> H1; Auto with zarith real.
Save.

(**********)
Lemma Rlt_le_trans:(r1,r2,r3:R)
  (Rlt r1 r2)->(Rle r2 r3)->(Rlt r1 r3).
Intros; Unfold Rle in H0; Elim H0; Intro.
Apply (Rlt_trans r1 r2 r3 H H1).
Rewrite <- H1; Auto with zarith real.
Save.

(**********)
Lemma Rlt_anti_compatibility:
    (r,r1,r2:R)(Rlt (Rplus r r1) (Rplus r r2))->(Rlt r1 r2).
Intros;
 Cut (Rlt (Rplus (Rplus (Ropp r) r) r1) 
          (Rplus (Rplus (Ropp r) r) r2)).
Rewrite -> Rplus_Ropp_l.
Elim (Rplus_ne r1); Elim (Rplus_ne r2); Intros; Rewrite <- H3;
 Rewrite <- H1; Auto with zarith real.
Rewrite -> Rplus_assoc; Rewrite -> Rplus_assoc;
 Apply (Rlt_compatibility (Ropp r) (Rplus r r1) (Rplus r r2) H).
Save.

(**********)
Lemma Rle_compatibility:(r,r1,r2:R)(Rle r1 r2)->
      (Rle (Rplus r r1) (Rplus r r2)).
Unfold Rle; Intros; Elim H; Intro.
Left; Apply (Rlt_compatibility r r1 r2 H0).
Right; Rewrite <- H0; Auto with zarith real.
Save.

(**********)
Lemma Rle_anti_compatibility:
   (r,r1,r2:R)(Rle (Rplus r r1) (Rplus r r2))->(Rle r1 r2).
Unfold Rle; Intros; Elim H; Intro.
Left; Apply (Rlt_anti_compatibility r r1 r2 H0).
Right; Apply (r_Rplus_plus r r1 r2 H0).
Save.

(**********)
Lemma Rgt_Ropp:(r1,r2:R)
 (Rgt r1 r2)->(Rlt (Ropp r1) (Ropp r2)).
Intros;Unfold Rgt in H;
 Generalize (Rlt_compatibility (Ropp r2) r2 r1 H);Intro;
 Generalize (Rlt_compatibility (Ropp r1) (Rplus (Ropp r2) r2) 
               (Rplus (Ropp r2) r1) H0);
 Rewrite (Rplus_Ropp_l r2);Rewrite (Rplus_sym (Ropp r2) r1);
 Rewrite <-(Rplus_assoc (Ropp r1) r1 (Ropp r2)); 
 Rewrite (Rplus_Ropp_l r1);Elim (Rplus_ne (Ropp r1));Intros a b;
 Rewrite a;Clear a b;Elim (Rplus_ne (Ropp r2));Intros a b;
 Rewrite b;Clear a b;Auto with zarith real.
Save.

(**********)
Lemma Rlt_Ropp:(r1,r2:R)
 (Rlt r1 r2)->(Rgt (Ropp r1) (Ropp r2)).
Intros; Cut (Rgt r2 r1).
Intro; Cut (Rlt (Ropp r2) (Ropp r1)); Auto with zarith real.
Apply (Rgt_Ropp r2 r1 H0).
Auto with zarith real.
Save.

(**********)
Lemma Rlt_anti_monotony:(r,r1,r2:R)(Rlt r R0)->(Rlt r1 r2)->
      (Rgt (Rmult r r1) (Rmult r r2)).
Intros;Generalize (Rlt_Ropp r1 r2 H0);Intro;Unfold Rgt;
 Rewrite <-(Ropp_mul2 r r2);Rewrite <-(Ropp_mul2 r r1);
 Apply (Rlt_monotony (Ropp r) (Ropp r2) (Ropp r1));Auto with zarith real.
Apply (Rlt_anti_compatibility r R0 (Ropp r));
 Elim (Rplus_ne r);Intros a b;Rewrite a;Clear a b;
 Rewrite (Rplus_Ropp_r r);Assumption.
Save.

(**********)
Lemma Rle_monotony: 
  (r,r1,r2:R)
        (Rle R0 r)
        ->(Rle r1 r2)->(Rle (Rmult r r1) (Rmult r r2)).
Intros r r1 r2;Unfold Rle;Intros;Elim H;Elim H0;Intros.
Left;Apply Rlt_monotony;Assumption.
Right;Rewrite H1;Reflexivity.
Right;Rewrite <- H2;Rewrite Rmult_Ol;Rewrite Rmult_Ol;Reflexivity.
Right;Rewrite H1;Reflexivity.
Save.

(**********)
Lemma Rlt_minus:(r1,r2:R)(Rlt r1 r2)->(Rlt (Rminus r1 r2) R0).
Intros; Cut (Rlt (Rminus r1 r2) (Rminus r2 r2)).
Rewrite -> (eq_Rminus r2); Auto with zarith real.
Unfold Rminus; Rewrite -> (Rplus_sym r1 (Ropp r2));
 Rewrite -> (Rplus_sym r2 (Ropp r2));
 Apply (Rlt_compatibility (Ropp r2) r1 r2 H).
Save.

(**********)
Lemma Rle_minus:(r1,r2:R)(Rle r1 r2)->(Rle (Rminus r1 r2) R0).
Unfold Rle; Intros; Elim H; Intro.
Left; Apply (Rlt_minus r1 r2 H0).
Right; Apply (eq_Rminus r1 r2 H0).
Save.

(**********)
Lemma Rminus_lt:(r1,r2:R)(Rlt (Rminus r1 r2) R0)->(Rlt r1 r2).
Intros;Unfold Rminus in H;
  Generalize (Rlt_compatibility r2 (Rplus r1 (Ropp r2)) R0 H);
  Intro;Clear H;
  Rewrite (Rplus_sym r1 (Ropp r2)) in H0;
  Rewrite <- (Rplus_assoc r2 (Ropp r2) r1) in H0;
  Rewrite (Rplus_Ropp_r r2) in H0;Elim (Rplus_ne r1); Elim (Rplus_ne r2); 
  Intros;
  Rewrite H3 in H0; Rewrite H in H0; Auto with zarith real.
Save.

(**********)
Lemma Rminus_le:(r1,r2:R)(Rle (Rminus r1 r2) R0)->(Rle r1 r2).
Unfold Rle;Intros;Elim H; Intro;Clear H.
Left;Apply Rminus_lt;Auto with zarith real.
Right;Apply Rminus_eq;Auto with zarith real.
Save.

(**********)
Lemma sum_inequa_Rle_lt:(a,x,b,c,y,d:R)(Rle a x)->(Rlt x b)->
           (Rlt c y)->(Rle y d)->
        (Rlt (Rplus a c) (Rplus x y))/\(Rlt (Rplus x y) (Rplus b d)).
Intros;Split.
Apply (Rlt_le_trans (Rplus a c) (Rplus a y) (Rplus x y)).
Apply (Rlt_compatibility a c y H1).
Rewrite (Rplus_sym a y);Rewrite (Rplus_sym x y);
 Apply (Rle_compatibility y a x H).
Apply (Rle_lt_trans (Rplus x y) (Rplus d x) (Rplus b d)).
Rewrite (Rplus_sym d x);Apply (Rle_compatibility x y d H2).
Rewrite (Rplus_sym b d);Apply (Rlt_compatibility d x b H0).
Save.

(*********)
Lemma Rplus_lt:(r1,r2,r3,r4:R)(Rlt r1 r2)->(Rlt r3 r4)->
 (Rlt (Rplus r1 r3) (Rplus r2 r4)).
Intros; Generalize (Rlt_compatibility r3 r1 r2 H);
 Generalize (Rlt_compatibility r2 r3 r4 H0);Intros;
 Rewrite (Rplus_sym r3 r2) in H2;Rewrite (Rplus_sym r3 r1) in H2;
 Apply (Rlt_trans (Rplus r1 r3) (Rplus r2 r3) (Rplus r2 r4) H2 H1).
Save.

(*********)
Lemma Rmult_lt:(r1,r2,r3,r4:R)(Rgt r3 R0)->(Rgt r2 R0)->
  (Rlt r1 r2)->(Rlt r3 r4)->(Rlt (Rmult r1 r3) (Rmult r2 r4)).
Intros;Unfold Rgt in H H0;Generalize (Rlt_monotony r3 r1 r2 H H1);Intro;
 Generalize (Rlt_monotony r2 r3 r4 H0 H2);Intro;
 Rewrite (Rmult_sym r3 r1) in H3;Rewrite (Rmult_sym r3 r2) in H3;
 Apply (Rlt_trans (Rmult r1 r3) (Rmult r2 r3) (Rmult r2 r4) H3 H4). 
Save.

(**********)
Lemma inser_trans_R:(n,m,p,q:R)(Rle n m)/\(Rlt m p)->
      (sumboolT ((Rle n m)/\(Rlt m q)) ((Rle q m)/\(Rlt m p))).
Intros; Cut (sumboolT (Rle q m) (Rlt m q)).
Intro;Cut (Rle n m);[Intro;Cut (Rlt m p)|Elim H;Auto with zarith real].
Intro;Elim X;Intro.
Right; Auto with zarith real.
Left; Auto with zarith real.
Elim H;Auto with zarith real.
Generalize (total_order_Rle q m); Intro; Elim X; Intro.
Left;Auto with zarith real.
Right; Generalize (not_Rle q m y); Auto with zarith real.
Save.

(**********)
Lemma tech_Rplus:(r,s:R)(Rle R0 r)->(Rlt R0 s)->~(Rplus r s)==R0.
Red;Intros;Cut (Rlt R0 (Rplus r s)).
Intro;Elim (imp_not_Req R0 (Rplus r s));Auto with zarith real.
Clear H1;Generalize (Rlt_compatibility r R0 s H0);Intro;
 Elim (Rplus_ne r);Intros a b;Rewrite a in H1;Clear a b;
 Apply (Rle_lt_trans R0 r (Rplus r s) H H1).
Save.

(***********)
Lemma pos_Rsqr:(r:R)(Rle R0 (Rsqr r)).
Intro; Cut (Rlt r R0)\/r==R0\/(Rgt r R0).
Intro; Elim H; Intro; Unfold Rle.
Left; Replace R0 with (Rmult r R0).
Unfold Rsqr; Apply (Rlt_anti_monotony r r R0 H0 H0).
Auto with zarith real.
Elim H0; Intro.
Right; Rewrite -> H1; Apply sym_eqT; Apply Rsqr_O.
Left; Unfold Rgt in H1; Replace R0 with (Rmult r R0).
Unfold Rsqr; Apply (Rlt_monotony r R0 r H1 H1).
Auto with zarith real.
Apply (total_order r R0).
Save.

(***********)
Lemma pos_Rsqr1:(r:R)(~(r==R0))->(Rlt R0 (Rsqr r)).
Intros; Cut (Rlt r R0)\/(Rgt r R0).
Intro; Elim H0; Intro.
Replace R0 with (Rmult r R0); Unfold Rsqr.
Apply (Rlt_anti_monotony r r R0 H1 H1).
Auto with zarith real.
Unfold Rgt in H1; Replace R0 with (Rmult r R0).
Unfold Rsqr; Apply (Rlt_monotony r R0 r H1 H1).
Auto with zarith real.
Apply (not_Req r R0 H).
Save.

(**********)
Lemma Rlt_R0_R1:(Rlt R0 R1).
Cut ~R1==R0->(Rlt R0 (Rsqr R1)).
Intro; Replace R1 with (Rsqr R1); Cut ~R1==R0; Auto with zarith real.
Red; Intro; Apply (R1_neq_R0 H0).
Unfold Rsqr; Elim (Rmult_ne R1); Auto with zarith real.
Red; Intro; Apply (R1_neq_R0 H0).
Intro; Apply (pos_Rsqr1 R1 H).
Save.

(*********)
Lemma Rlt_Rinv:(r:R)(Rlt R0 r)->(Rlt R0 (Rinv r)).
Intros; Fold (Rgt (Rinv r) R0); Apply (not_Rle (Rinv r) R0);Red;
 Intro;Unfold Rle in H0;Elim H0; Intro;Clear H0.
Generalize (Rlt_monotony r (Rinv r) R0 H H1);Rewrite (Rinv_r r).
Rewrite (Rmult_Or r);Intro;Generalize (Rle_not R0 R1 H0);
 Generalize (Rlt_le R0 R1 Rlt_R0_R1);Intros;Auto.
Apply (sym_not_eqT R R0 r);Apply (imp_not_Req R0 r);Left;Assumption.
Generalize (Rmult_mult_r r (Rinv r) R0 H1);Rewrite (Rinv_r r).
Rewrite (Rmult_Or r);Intro;Generalize R1_neq_R0;Auto.
Apply (sym_not_eqT R R0 r);Apply (imp_not_Req R0 r);Left;Assumption.
Save.

(*********)
Lemma Rlt_Rinv2:(r:R)(Rlt r R0)->(Rlt (Rinv r) R0).
Intros;Fold (Rgt R0 (Rinv r)); Apply (not_Rle R0 (Rinv r));Red;
 Intro;Unfold Rle in H0;Elim H0; Intro;Clear H0.
Generalize (Rlt_monotony (Rinv r) r R0 H1 H);Rewrite (Rinv_l r).
Rewrite (Rmult_Or (Rinv r));Intro;Generalize (Rle_not R0 R1 H0);
 Generalize (Rlt_le R0 R1 Rlt_R0_R1);Intros;Auto.
Apply (imp_not_Req r R0);Left;Assumption.
Generalize (Rmult_mult_r r R0 (Rinv r) H1);Rewrite (Rinv_r r).
Rewrite (Rmult_Or r);Intro;Generalize R1_neq_R0;Auto.
Apply (imp_not_Req r R0);Left;Assumption.
Save.

(*********)
Lemma Rinv_lt:(r1,r2:R)(Rlt R0 (Rmult r1 r2))->(Rlt r1 r2)->
                       (Rlt (Rinv r2) (Rinv r1)).  
Intros;Generalize (Rlt_monotony (Rinv (Rmult r1 r2)) r1 r2 
                  (Rlt_Rinv (Rmult r1 r2) H) H0);Intro;
 Elim (without_div_O_contr r1 r2  
       (sym_not_eqT R R0 (Rmult r1 r2) (imp_not_Req R0 (Rmult r1 r2) 
       (or_introl (Rlt R0 (Rmult r1 r2)) (Rgt R0 (Rmult r1 r2)) H))));
 Intros;Rewrite Rinv_Rmult in H1;Auto;
 Rewrite (Rmult_assoc (Rinv r1) (Rinv r2) r2) in H1;
 Rewrite (Rinv_l r2 H3) in H1;
 Rewrite (let (H1,H2)=(Rmult_ne (Rinv r1)) in H1) in H1;
 Rewrite (Rmult_sym (Rinv r1) (Rinv r2)) in H1;
 Rewrite (Rmult_assoc (Rinv r2) (Rinv r1) r1 ) in H1;
 Rewrite (Rinv_l r1 H2) in H1;
 Rewrite (let (H1,H2)=(Rmult_ne (Rinv r2)) in H1) in H1;Assumption.
Save.

(**********)
Lemma Rlt_monotony_rev:
  (r,r1,r2:R)(Rlt R0 r)->(Rlt (Rmult r r1) (Rmult r r2))
             ->(Rlt r1 r2).
Intros;Cut (s:R) (Rmult (Rinv r) (Rmult r s))==s.
Intros; Rewrite <- (H1 r1); Rewrite <- (H1 r2);Apply Rlt_monotony. 
Apply Rlt_Rinv; Assumption.
Assumption.
Intro;Rewrite <- Rmult_assoc;Rewrite Rinv_l.
Ring.
Apply imp_not_Req; Right; Unfold Rgt; Assumption.
Save.

(*********************************************************)        
(*       Greater                                         *)
(*********************************************************)

(**********)
Lemma Rge_ge_eq:(r1,r2:R)(Rge r1 r2)->(Rge r2 r1)->r1==r2.
Unfold Rge; Intros; Elim H; Intro; Auto with zarith real.
Elim H0; Intro; Auto with zarith real.
Absurd (Rgt r1 r2); Auto with zarith real.
Unfold Rgt; Unfold Rgt in H2; Apply Rlt_antisym; Auto with zarith real.
Save.

(**********)
Lemma Rlt_not_ge:(r1,r2:R)~(Rlt r1 r2)->(Rge r1 r2).
Intros; Unfold Rge; Elim (total_order r1 r2); Intro.
ElimType False; Auto with zarith real.
Elim H0; Auto with zarith real.
Save.

(**********)
Lemma Rgt_not_le:(r1,r2:R)~(Rgt r1 r2)->(Rle r1 r2).
Intros; Unfold Rgt in H; Unfold Rle; Elim (total_order r1 r2); Intro.
Left ; Auto with zarith real.
Elim H0; Intro; Auto with zarith real.
Unfold Rgt in H1; ElimType False; Auto with zarith real.
Save.

(**********)
Lemma Rgt_ge:(r1,r2:R)(Rgt r1 r2)->(Rge r1 r2).
Intros; Unfold Rge; Left; Auto with zarith real.
Save.

(**********)
Lemma Rlt_sym:(r1,r2:R)
 (((Rlt r1 r2)->(Rgt r2 r1))/\((Rgt r2 r1)->(Rlt r1 r2))).
Intros; Split; Intro; Unfold Rgt; Auto with zarith real.
Save.

(**********)
Lemma Rle_sym1:(r1,r2:R)(Rle r1 r2)->(Rge r2 r1).
Intros r1 r2; Unfold Rge; Unfold Rle; Intro; Elim H; Intro.
Left; Unfold Rgt; Auto with zarith real.
Right; Auto with zarith real.
Save.

(**********)
Lemma Rle_sym2:(r1,r2:R)(Rge r2 r1)->(Rle r1 r2).
Intros r1 r2; Unfold Rge; Unfold Rle; Intro; Elim H; Intro.
Left; Unfold Rgt in H0; Auto with zarith real.
Right; Auto with zarith real.
Save.

(**********)
Lemma Rle_sym:(r1,r2:R)
 (((Rle r1 r2)->(Rge r2 r1))/\((Rge r2 r1)->(Rle r1 r2))).
Intros; Split; Intro.
Apply Rle_sym1; Auto with zarith real.
Apply Rle_sym2; Auto with zarith real.
Save.

(**********)
Lemma Rge_gt_trans:(r1,r2,r3:R)
 (Rge r1 r2)->(Rgt r2 r3)->(Rgt r1 r3).
Intros r1 r2 r3; Unfold Rgt; Unfold Rge; Intros; Elim H; Intros.
Unfold Rgt in H1; Apply (Rlt_trans r3 r2 r1 H0 H1).
Rewrite -> H1; Auto with zarith real.
Save.

(**********)
Lemma Rgt_ge_trans:(r1,r2,r3:R)
 (Rgt r1 r2)->(Rge r2 r3)->(Rgt r1 r3).
Intros r1 r2 r3; Unfold Rgt; Unfold Rge; Intros; Elim H0; Intros.
Apply (Rlt_trans r3 r2 r1 H1 H).
Rewrite <- H1; Auto with zarith real.
Save.

(**********)
Lemma Rgt_trans:(r1,r2,r3:R)
 (Rgt r1 r2)->(Rgt r2 r3)->(Rgt r1 r3).
Intros; Cut (Rge r1 r2).
Intro; Apply (Rge_gt_trans r1 r2 r3 H1 H0).
Apply (Rgt_ge r1 r2 H).
Save.

(**********)
Lemma Rge_trans:(r1,r2,r3:R)
 (Rge r1 r2)->(Rge r2 r3)->(Rge r1 r3).
Intros; Cut (Rle r2 r1).
Cut (Rle r3 r2); Intros.
Cut (Rle r3 r1).
Intro; Apply (Rle_sym1 r3 r1 H3).
Apply (Rle_trans r3 r2 r1 H1 H2).
Apply (Rle_sym2 r3 r2 H0).
Apply (Rle_sym2 r2 r1 H).
Save.

(**********)
Lemma eq_Rge:(r1,r2:R)(r1==r2)->(Rge r1 r2).
Intros; Unfold Rge; Right; Auto with zarith real.
Save.

(**********)
Lemma Rle_Ropp:(r1,r2:R)
 (Rle r1 r2)->(Rge (Ropp r1) (Ropp r2)).
Unfold Rle; Intros; Unfold Rge; Elim H; Intro.
Left; Apply (Rlt_Ropp r1 r2 H0).
Right; Apply (eq_Ropp r1 r2 H0).
Save.

(**********)
Lemma Rgt_RoppO:(r:R)(Rgt r R0)->(Rlt (Ropp r) R0).
Intros; Rewrite <- Ropp_O; Apply (Rgt_Ropp r R0); Auto with zarith real.
Save.

(**********)
Lemma Rlt_RoppO:(r:R)(Rlt r R0)->(Rgt (Ropp r) R0).
Intros; Rewrite <- Ropp_O; Apply (Rlt_Ropp r R0); Auto with zarith real.
Save.

(**********)
Lemma Rlt_r_plus_R1:(r:R)(Rle R0 r)->(Rlt R0 (Rplus r R1)).
Unfold Rle; Intros; Elim H; Intro; Clear H.
Apply (Rlt_anti_compatibility (Ropp r) R0 (Rplus r R1));
 Elim (Rplus_ne (Ropp r)); Intros; Rewrite H; Clear H H1;
 Rewrite <- (Rplus_assoc (Ropp r) r R1); Rewrite Rplus_Ropp_l;
 Elim (Rplus_ne R1); Intros; Rewrite H1; Clear H H1;
 Fold (Rgt r R0) in H0; Generalize (Rgt_RoppO r H0); Intro;
 Generalize Rlt_R0_R1; Intro; Apply (Rlt_trans (Ropp r) R0 R1 H H1).
Rewrite <- H0; Elim (Rplus_ne R1); Intros; Rewrite H1; Clear H H1;
 Apply Rlt_R0_R1.
Save.

(**********)
Lemma tech_Rgt_minus:(r1,r2:R)(Rlt R0 r2)->(Rgt r1 (Rminus r1 r2)).
Intros;Fold (Rgt r2 R0) in H;Generalize (Rgt_RoppO r2 H); Intro;
  Generalize (Rlt_compatibility r1 (Ropp r2) R0 H0); Intro;
  Elim (Rplus_ne r1); Intros a b; Rewrite a in H1; Clear a b;
  Unfold Rgt;Unfold Rminus;Assumption.
Save.

(***********)
Lemma Rgt_plus_plus_r:(r,r1,r2:R)(Rgt r1 r2)->
      (Rgt (Rplus r r1) (Rplus r r2)).
Unfold Rgt; Intros; Apply (Rlt_compatibility r r2 r1 H).
Save.

(***********)
Lemma Rgt_r_plus_plus:(r,r1,r2:R)(Rgt (Rplus r r1) (Rplus r r2))->
                              (Rgt r1 r2).
Unfold Rgt; Intros; Apply (Rlt_anti_compatibility r r2 r1 H).
Save.

(***********)
Lemma Rge_plus_plus_r:(r,r1,r2:R)(Rge r1 r2)->
      (Rge (Rplus r r1) (Rplus r r2)).
Unfold Rge; Intros; Elim H; Intro.
Left; Apply (Rgt_plus_plus_r r r1 r2 H0).
Right; Apply (Rplus_plus_r r r1 r2 H0).
Save.

(***********)
Lemma Rge_r_plus_plus:(r,r1,r2:R)(Rge (Rplus r r1) (Rplus r r2))->
                              (Rge r1 r2).
Unfold Rge; Intros; Elim H; Intro.
Left; Apply (Rgt_r_plus_plus r r1 r2 H0).
Right; Apply (r_Rplus_plus r r1 r2 H0).
Save.

(***********)
Lemma Rge_monotony:
 (x,y,z:R) (Rge z R0) -> (Rge x y) -> (Rge (Rmult x z) (Rmult y z)).
Intros;Apply Rle_sym1;
 Rewrite (Rmult_sym y z); Rewrite (Rmult_sym x z);
 Apply Rle_monotony;Apply Rle_sym2; Assumption.
Save.

(***********)
Lemma Rgt_minus:(r1,r2:R)(Rgt r1 r2)->(Rgt (Rminus r1 r2) R0).
Intros; Cut (Rgt (Rminus r1 r2) (Rminus r2 r2)).
Rewrite -> (eq_Rminus r2 r2); Auto with zarith real.
Unfold Rminus; Rewrite -> (Rplus_sym r1 (Ropp r2));
 Rewrite -> (Rplus_sym r2 (Ropp r2));
 Apply (Rgt_plus_plus_r (Ropp r2) r1 r2 H).
Save.

(*********)
Lemma minus_Rgt:(r1,r2:R)(Rgt (Rminus r1 r2) R0)->(Rgt r1 r2).
Intros;Generalize (Rgt_plus_plus_r r2 (Rminus r1 r2) R0 H); Intro;
 Rewrite (Rplus_sym r2 (Rminus r1 r2)) in H0;Unfold Rminus in H0;
 Rewrite (Rplus_assoc r1 (Ropp r2) r2) in H0;
 Rewrite (Rplus_Ropp_l r2) in H0;
 Elim (Rplus_ne r1); Intros a b; Rewrite a in H0; Clear a b;
 Elim (Rplus_ne r2); Intros a b; Rewrite a in H0; Clear a b;Exact H0.
Save.

(**********)
Lemma Rge_minus:(r1,r2:R)(Rge r1 r2)->(Rge (Rminus r1 r2) R0).
Unfold Rge; Intros; Elim H; Intro.
Left; Apply (Rgt_minus r1 r2 H0).
Right; Apply (eq_Rminus r1 r2 H0).
Save.

(*********)
Lemma minus_Rge:(r1,r2:R)(Rge (Rminus r1 r2) R0)->(Rge r1 r2).
Intros;Generalize (Rge_plus_plus_r r2 (Rminus r1 r2) R0 H); Intro;
 Rewrite (Rplus_sym r2 (Rminus r1 r2)) in H0;Unfold Rminus in H0;
 Rewrite (Rplus_assoc r1 (Ropp r2) r2) in H0;
 Rewrite (Rplus_Ropp_l r2) in H0;
 Elim (Rplus_ne r1); Intros a b; Rewrite a in H0; Clear a b;
 Elim (Rplus_ne r2); Intros a b; Rewrite a in H0; Clear a b;Exact H0.
Save.

(*********)
Lemma Rmult_gt:(r1,r2:R)(Rgt r1 R0)->(Rgt r2 R0)->(Rgt (Rmult r1 r2) R0).
Unfold Rgt;Intros;Generalize (Rlt_monotony r1 R0 r2 H H0);Intro;
 Rewrite (Rmult_Or r1) in H1;Assumption.
Save.

(*********)
Lemma Rmult_lt_pos:(x,y:R)(Rlt R0 x)->(Rlt R0 y)->(Rlt R0 (Rmult x y)).
Generalize Rmult_gt;Unfold Rgt;Auto.
Save.


(***********)
Lemma Rplus_eq_R0:(a,b:R)(Rle R0 a)->(Rle R0 b)->(Rplus a b)==R0->
                         (a==R0)/\(b==R0).
Intros;Generalize (Rle_Ropp R0 b H0);Intro;Rewrite Ropp_O in H2;
 Generalize (Rle_Ropp R0 a H);Intro;Rewrite Ropp_O in H3;
 Generalize (Rplus_Ropp a b H1);Intro;Rewrite Rplus_sym in H1;
 Generalize (Rplus_Ropp b a H1);Intro;Clear H1;Rewrite <- H4 in H3;
 Rewrite <-H5 in H2;Clear H4 H5; Generalize (Rle_sym1 R0 a H);Clear H;
 Intro;Generalize (Rle_sym1 R0 b H0);Clear H0;Intro;Split;Apply Rge_ge_eq;
 Assumption.
Save.

(***********)
Lemma Rplus_Rsr_eq_R0:(a,b:R)(Rplus (Rsqr a) (Rsqr b))==R0->
                         (a==R0)/\(b==R0).
Intros;Elim (Rplus_eq_R0 (Rsqr a) (Rsqr b) (pos_Rsqr a) (pos_Rsqr b) H);
 Intros;Clear H;Split;Apply Rsqr_r_R0;Assumption.
Save.

(**********************************************************) 
(*       Injection from N to R                            *)
(**********************************************************)

(**********)
Lemma S_INR:(n:nat)(INR (S n))==(Rplus (INR n) R1).
Intro; Simpl; Case n.
Simpl; Elim (Rplus_ne R1); Auto with zarith real.
Auto with zarith real.
Save.

(**********)
Lemma S_O_plus_INR:(n:nat)
    (INR (plus (S O) n))==(Rplus (INR (S O)) (INR n)).
Intro; Replace (plus (S O) n) with (S (plus O n)).
Replace (INR (S (plus O n))) with (Rplus (INR (plus O n)) R1).
Replace (INR (S O)) with (Rplus (INR O) R1).
Replace (INR (S O)) with (Rplus (INR O) R1); Simpl; Elim (Rplus_ne R1);
 Intros; Rewrite -> H0; Auto with zarith real; Rewrite -> Rplus_sym;
 Auto with zarith real.
Simpl.
Elim (Rplus_ne R1); Auto with zarith real.
Apply sym_eqT; Apply (S_INR (plus O n)).
Auto with zarith real.
Save.

(**********)
Lemma plus_INR:(n,m:nat)(INR (plus n m))==(Rplus (INR n) (INR m)). 
Induction n.
Simpl; Intro; Elim (Rplus_ne (INR m)); Auto with zarith real.
Intros; Rewrite -> plus_Snm_nSm;
 Replace (INR (S n0)) with (Rplus (INR n0) R1).
Rewrite -> Rplus_assoc; Rewrite -> (Rplus_sym R1 (INR m));
 Replace (Rplus (INR m) R1) with (INR (S m)).
Apply (H (S m)).
Apply (S_INR m).
Apply sym_eqT; Apply (S_INR n0).
Save.

(**********)
Lemma minus_INR:(n,m:nat)(le m n)->
   (INR (minus n m))==(Rminus (INR n) (INR m)).
Intros;
 Cut (Rplus (INR m) (INR (minus n m)))
      ==(Rplus (INR m) (Rminus (INR n) (INR m))).
Intro;
 Apply (r_Rplus_plus (INR m) (INR (minus n m)) 
                  (Rminus (INR n) (INR m)) H0).
Rewrite <- plus_INR; Rewrite -> le_plus_minus_r.
Unfold Rminus; Rewrite -> Rplus_sym; Rewrite -> Rplus_assoc;
 Rewrite -> Rplus_Ropp_l; Elim (Rplus_ne (INR n)); Auto with zarith real.
Auto with zarith real.
Save.

(*********)
Lemma mult_INR:(n,m:nat)(INR (mult n m))==(Rmult (INR n) (INR m)).
Induction n.
Simpl; Intro;Apply sym_eqT;Apply Rmult_Ol.
Intros;Unfold 1 mult;Cbv Beta Iota;Fold mult;
 Rewrite (plus_INR m (mult n0 m));Rewrite (H m);
 Pattern 1 (INR m); 
 Rewrite <-(let (H1,H2)=(Rmult_ne (INR m)) in H1);
 Rewrite (Rmult_sym (INR n0) (INR m));
 Rewrite <-(Rmult_Rplus_distr (INR m) R1 (INR n0));
 Rewrite (Rplus_sym R1 (INR n0));Rewrite <-(S_INR n0);
 Apply Rmult_sym. 
Save. 


(*********)
Lemma INR_lt_0:(n:nat)(lt O n)->(Rlt R0 (INR n)).
Induction n;Intros.
Absurd (lt (0) (0));[Apply lt_n_n|Assumption].
Elim (le_lt_or_eq (0) n0 (lt_n_Sm_le (0) n0 H0));Intro.
Generalize (H H1);Clear H H1;Intro;Rewrite (S_INR n0);
 Generalize (Rlt_compatibility R1 R0 (INR n0) H);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne R1) in H1) in H1;
 Rewrite (Rplus_sym (INR n0) R1);
 Apply (Rlt_trans R0 R1 (Rplus R1 (INR n0)) (Rlt_R0_R1) H1).
Rewrite <-H1;Simpl;Apply Rlt_R0_R1.
Save.

(**********)
Lemma INR_le:(n:nat)(Rle R0 (INR n)).
Induction n.
Simpl; Apply (eq_Rle R0 R0 (refl_eqT R R0)).
Intros;Rewrite (S_INR n0);Apply (Rlt_le R0 (Rplus (INR n0) R1));
 Apply (Rlt_r_plus_R1 (INR n0) H).
Save.

(*********)
Lemma INR_le_nm:(n,m:nat)(le n m)->(Rle (INR n) (INR m)).
Intros;Elim (le_lt_or_eq n m H);Intro.
Cut (lt (0) (minus m n)).
Intro;Generalize (INR_lt_0 (minus m n) H1);
 Intro;Rewrite minus_INR in H2;Auto;
 Apply (Rlt_le (INR n) (INR m));Fold (Rgt (INR m) (INR n));
 Apply (minus_Rgt (INR m) (INR n));Unfold Rgt;Assumption.
Omega.
Rewrite H0;Unfold Rle;Right;Trivial.
Save.

(**********)
Lemma not_INR_O:(n:nat)~(INR n)==R0->~n=O.
Intros;Cut n=(0)->(INR n)==R0.
Tauto.
Intro;Rewrite H0;Auto with zarith real.
Save.

(**********)
Lemma not_O_INR:(n:nat)~n=O->~(INR n)==R0.
Intros;Cut (INR n)==R0->n=O.
Tauto.
Elim n;Intros;Auto with zarith real.
Rewrite (S_INR n0) in H1;Generalize (Rplus_Ropp (INR n0) R1 H1);Intro;
 Generalize (tech_Rplus (INR n0) R1 (INR_le n0) Rlt_R0_R1);Intro;
 ElimType False;Auto with zarith real.
Save. 

(**********************************************************) 
(*       Injection from Z to R                            *)
(**********************************************************)

(**********)
Definition INZ:=inject_nat.

(**********)
Lemma IZN:(z:Z)(`0<=z`)->(Ex [n:nat] z=(INZ n)).
Unfold INZ;Intros;Apply inject_nat_complete;Assumption.
Save.

(**********)
Lemma INR_IZR_INZ:(n:nat)(INR n)==(IZR (INZ n)).
Induction n;Auto with zarith real.
Intros;Rewrite S_INR;Simpl;Rewrite bij1;Rewrite <-S_INR;Auto with zarith real.
Save.

(**********)
Lemma plus_IZR:(z,t:Z)(IZR (Zplus z t))==(Rplus (IZR z) (IZR t)). 
Destruct z;
 [Simpl;Intro; Elim (Rplus_ne (IZR t)); Intros a b; Rewrite b; Auto with zarith real|
 Destruct t|Destruct t].
Simpl;Elim (Rplus_ne (INR (convert p))); Intros a b; Rewrite a; Auto with zarith real.
Simpl;Intro;Rewrite <- (plus_INR (convert p) (convert p0));
 Rewrite (convert_add p p0);Trivial with zarith real.
Unfold Zplus;Intro;Simpl;
 Generalize (refl_equal relation (compare p p0 EGAL));
 Pattern 2 3 (compare p p0 EGAL);Case (compare p p0 EGAL);Intro.
Rewrite (compare_convert_EGAL p p0 H);
 Rewrite (Rplus_Ropp_r (INR (convert p0)));Auto with zarith real.
Simpl;Rewrite (true_sub_convert p0 p (ZC2 p p0 H));
 Rewrite (minus_INR (convert p0) (convert p) 
  (lt_le_weak (convert p) (convert p0) 
   (compare_convert_INFERIEUR p p0 H)));
 Rewrite (Ropp_distr2 (INR (convert p0)) (INR (convert p)));
 Unfold Rminus;Trivial with zarith real.
Simpl;Rewrite (true_sub_convert p p0 H);
 Rewrite (minus_INR (convert p) (convert p0));[Unfold Rminus;Trivial with zarith real|
 Generalize (compare_convert_SUPERIEUR p p0 H);Intro;Unfold gt in H0;
  Apply (lt_le_weak (convert p0) (convert p) H0)].
Simpl;Elim (Rplus_ne (Ropp (INR (convert p)))); Intros a b; 
 Rewrite a; Auto with zarith real.
Intro;Rewrite (Zplus_sym (NEG p) (POS p0));
 Rewrite (Rplus_sym (IZR (NEG p)) (IZR (POS p0)));
 Unfold Zplus;Simpl;
 Generalize (refl_equal relation (compare p0 p EGAL));
 Pattern 2 3 (compare p0 p EGAL);Case (compare p0 p EGAL);Intro.
Rewrite (compare_convert_EGAL p0 p H);
 Rewrite (Rplus_Ropp_r (INR (convert p)));Auto with zarith real.
Simpl;Rewrite (true_sub_convert p p0 (ZC2 p0 p H));
 Rewrite (minus_INR (convert p) (convert p0) 
  (lt_le_weak (convert p0) (convert p) 
   (compare_convert_INFERIEUR p0 p H)));
 Rewrite (Ropp_distr2 (INR (convert p)) (INR (convert p0)));
 Unfold Rminus;Trivial with zarith real.
Simpl;Rewrite (true_sub_convert p0 p H);
 Rewrite (minus_INR (convert p0) (convert p));[Unfold Rminus;Trivial with zarith real|
 Generalize (compare_convert_SUPERIEUR p0 p H);Intro;Unfold gt in H0;
  Apply (lt_le_weak (convert p) (convert p0) H0)].
Simpl;Intro;
 Rewrite <-(Ropp_distr1 (INR (convert p)) (INR (convert p0)));
 Rewrite <- (plus_INR (convert p) (convert p0));
 Rewrite (convert_add p p0);Trivial with zarith real.
Save.

(**********)
Lemma Ropp_Ropp_IZR:(z:Z)(IZR (`-z`))==(Ropp (IZR z)).
Induction z; Simpl.
Apply sym_eqT; Apply Ropp_O.
Trivial with zarith real.
Intro;Rewrite (Ropp_Ropp (INR (convert p)));Trivial with zarith real.
Save.

(**********)
Lemma Z_R_minus:(z1,z2:Z)
  (Rminus (IZR z1) (IZR z2))==(IZR (Zminus z1 z2)).
Unfold Rminus; Unfold Zminus; Intros; Apply sym_eqT;
 Rewrite <-(Ropp_Ropp_IZR z2);Apply plus_IZR.
Save. 

(**********)
Lemma lt_O_IZR:(z:Z)(Rlt R0 (IZR z))->(Zlt ZERO z). 
Induction z; Simpl; Intros.
Generalize (Rlt_antirefl R0);Intro;ElimType False;Auto with zarith real.
Unfold Zlt;Simpl;Trivial with zarith real.
Absurd (Rlt R0 (Ropp (INR (convert p))));Auto with zarith real.
Apply (Rlt_antisym (Ropp (INR (convert p))));
 Apply (Rgt_RoppO (INR (convert p)));Unfold Rgt;
 Cut (~(INR (convert p))==R0).
Intro;Generalize (not_INR_O (convert p) H0);Elim (convert p).
Intro;Absurd O=O;Auto with zarith real.
Intros;Rewrite (S_INR n);Apply (Rlt_r_plus_R1 (INR n) (INR_le n)).
Apply (imp_not_Req (INR (convert p)) R0);
 Fold (Rgt (Ropp (INR (convert p))) R0) in H;
 Generalize (Rgt_RoppO (Ropp (INR (convert p))) H);Intro;
 Rewrite (Ropp_Ropp (INR (convert p))) in H0;Left;Assumption.
Save.

(**********)
Lemma lt_IZR:(z1,z2:Z)(Rlt (IZR z1) (IZR z2))->(`z1<z2`).
Intros;Fold (Rgt (IZR z2) (IZR z1)) in H;
 Generalize (Rgt_minus (IZR z2) (IZR z1) H);Intro;Unfold Rgt in H0;
 Rewrite (Z_R_minus z2 z1) in H0;
 Generalize (lt_O_IZR `z2-z1` H0);Intro;Omega.
Save.

(**********)
Lemma eq_IZR_R0:(z:Z)(IZR z)==R0->`z=0`.
Destruct z; Auto with zarith real;
 [ Simpl; Intros; ElimType False | Simpl; Intros; ElimType False ].
Absurd (INR (convert p))==R0; Auto with zarith real.
Apply (not_O_INR (convert p));Red; Intro;Clear H;Unfold convert in H0;
 Generalize H0; Elim p;Intros.
Simpl in H1;Absurd (S (positive_to_nat p0 (2)))=(0); Auto with zarith real.
Simpl in H1;Cut (2)=(plus (1) (1)); Auto with zarith real.
Intro; Rewrite H2 in H1;Rewrite (ZL2 p0 (1)) in H1;Clear H2;
 Cut (positive_to_nat p0 (1))=(0);Auto with zarith real.
Simpl in H1;Absurd (1)=(0); Auto with zarith real.
Generalize (eq_Ropp (Ropp (INR (convert p))) R0 H);Intro;Clear H;
 Rewrite (Ropp_Ropp (INR (convert p))) in H0;Rewrite Ropp_O in H0;
 Absurd (INR (convert p))==R0; Auto with zarith real.
Apply (not_O_INR (convert p));Red; Intro;Clear H0;
 Unfold convert in H;Generalize H; Elim p;Intros.
Simpl in H1;Absurd (S (positive_to_nat p0 (2)))=(0); Auto with zarith real.
Simpl in H1;Cut (2)=(plus (1) (1)); Auto with zarith real.
Intro; Rewrite H2 in H1;Rewrite (ZL2 p0 (1)) in H1;Clear H2;
 Cut (positive_to_nat p0 (1))=(0);Auto with zarith real.
Simpl in H0;Absurd (1)=(0); Auto with zarith real.
Save.

(**********)
Lemma eq_IZR:(z1,z2:Z)(IZR z1)==(IZR z2)->z1=z2.
Intros;Generalize (eq_Rminus (IZR z1) (IZR z2) H);
 Rewrite (Z_R_minus z1 z2);Intro;Generalize (eq_IZR_R0 `z1-z2` H0);
 Intro;Omega.
Save.

(*********)
Lemma le_O_IZR:(z:Z)(Rle R0 (IZR z))->(Zle ZERO z).
Unfold Rle;Intros;Elim H;Clear H;Intro.
Unfold Zle;Red;Intro;Apply (Zlt_le_weak `0` z (lt_O_IZR z H));
 Assumption.
Generalize (eq_IZR_R0 z (sym_eqT R R0 (IZR z) H));Intro;Omega.
Save.

(**********)
Lemma le_IZR_R1:(z:Z)(Rle (IZR z) R1)->(Zle z `1`).
Induction z; Intros.
Omega.
Unfold Rle in H;Cut `(POS p) < 1`\/`(POS p) = 1`.
Omega.
Elim H;Intro.
Left;Apply (Zlt_O_minus_lt `1` (POS p));Apply (lt_O_IZR `1-(POS p)`);
 Cut (R1==(IZR `1`));Auto with zarith real. 
Intro;Rewrite H1 in H0;Clear H1;Fold (Rgt (IZR `1`) (IZR (POS p))) in H0;
 Generalize (Rgt_minus (IZR `1`) (IZR (POS p)) H0);Intro;
 Unfold Rgt in H1;Rewrite (Z_R_minus `1` (POS p)) in H1;
 Assumption.
Right;Cut (R1==(IZR `1`));Auto with zarith real.
Intro;Rewrite H1 in H0;Clear H1 H;Apply (eq_IZR (POS p) `1` H0).
Unfold Rle in H;Cut `(NEG p) < 1`\/`(NEG p) = 1`.
Omega.
Elim H;Intro.
Left;Apply (Zlt_O_minus_lt `1` (NEG p));Apply (lt_O_IZR `1-(NEG p)`);
 Cut (R1==(IZR `1`));Auto with zarith real.
Intro;Rewrite H1 in H0;Clear H1;Fold (Rgt (IZR `1`) (IZR (NEG p))) in H0;
 Generalize (Rgt_minus (IZR `1`) (IZR (NEG p)) H0);Intro;
 Unfold Rgt in H1;Rewrite (Z_R_minus `1` (NEG p)) in H1;
 Assumption.
Right;Cut (R1==(IZR `1`));Auto with zarith real.
Intro;Rewrite H1 in H0;Clear H1 H;Apply (eq_IZR (NEG p) `1` H0).
Save.

(**********)
Lemma IZR_ge: 
  (m,n:Z) `m>= n` ->(Rge (IZR m) (IZR n)).
Intros;Apply Rlt_not_ge;Red;Intro;Generalize (lt_IZR m n H0);Intro; Omega.
Save.

(**********)
Lemma single_z_r_R1:(r:R)(z,x:Z)(Rlt r (IZR z))->(Rle (IZR z) (Rplus r R1))
  ->(Rlt r (IZR x))->(Rle (IZR x) (Rplus r R1))->z=x.
Intros;Generalize (Rlt_Ropp r (IZR x) H1);Intro;
 Generalize (Rle_Ropp (IZR x) (Rplus r R1) H2);Intro;Clear H1 H2;
 Unfold Rgt in H3;
 Generalize (Rle_sym2 (Ropp (Rplus r R1)) (Ropp (IZR x)) H4);
 Intro;Clear H4;
 Generalize (sum_inequa_Rle_lt (Ropp (Rplus r R1)) (Ropp (IZR x))
   (Ropp r) r (IZR z) (Rplus r R1) H1 H3 H H0);Intro;Elim H2;Intros;
 Clear H2 H H0 H3 H1;Rewrite (Rplus_sym (Ropp (IZR x)) (IZR z)) in 
 H4;Rewrite (Rplus_sym (Ropp (IZR x)) (IZR z)) in H5;
 Fold (Rminus (IZR z) (IZR x)) in H4;
 Fold (Rminus (IZR z) (IZR x)) in H5;
 Rewrite <-(Rplus_assoc (Ropp r) r R1) in H5;
 Rewrite (Rplus_Ropp_l r) in H5;Rewrite (Ropp_distr1 r R1) in H4;
 Rewrite (Rplus_sym (Ropp r) (Ropp R1)) in H4;
 Rewrite (Rplus_assoc (Ropp R1) (Ropp r) r) in H4;
 Rewrite (Rplus_Ropp_l r) in H4;Elim (Rplus_ne R1);Intros a b;Rewrite b in H5;
 Clear a b;Elim (Rplus_ne (Ropp R1));Intros a b;Rewrite a in H4;
 Clear a b;Rewrite (Z_R_minus z x) in H4;Rewrite (Z_R_minus z x) in H5;
 Cut (R1==(IZR `1`));Auto with zarith real.
Cut (Ropp R1)==(IZR `-1`);Auto with zarith real.
Intros;Rewrite H0 in H5;Rewrite H in H4;Clear H H0;
 Generalize (lt_IZR `-1` `z-x` H4);Intro;
 Generalize (lt_IZR `z-x` `1` H5);Intro;Clear H4 H5;Omega.
Save.

(**********)
Lemma tech_single_z_r_R1:(r:R)(z:Z)(Rlt r (IZR z))->
 (Rle (IZR z) (Rplus r R1))->
 (Ex [s:Z] (~s=z/\(Rlt r (IZR s))/\(Rle (IZR s) (Rplus r R1))))->False.
Intros;Elim H1;Intros;Elim H2;Intros;Elim H4;Intros;Clear H1 H2 H4;
 Generalize (single_z_r_R1 r z x H H0 H5 H6);Intro;Auto with zarith real.
Save.
