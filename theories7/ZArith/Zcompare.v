(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $$ i*)

Require Export BinPos.
Require Export BinInt.
Require Zsyntax.
Require Lt.
Require Gt.
Require Plus.
Require Mult.

Open Local Scope Z_scope.

(**********************************************************************)
(** Binary Integers (Pierre Crégut, CNET, Lannion, France)            *)
(**********************************************************************)

(**********************************************************************)
(** Comparison on integers *)

Lemma Zcompare_x_x : (x:Z) (Zcompare x x) = EGAL.
Proof.
Intro x; NewDestruct x as [|p|p]; Simpl; [ Reflexivity | Apply convert_compare_EGAL
  | Rewrite convert_compare_EGAL; Reflexivity ].
Qed.

Lemma Zcompare_EGAL_eq : (x,y:Z) (Zcompare x y) = EGAL -> x = y.
Proof.
Intros x y; NewDestruct x as [|x'|x'];NewDestruct y as [|y'|y'];Simpl;Intro H; Reflexivity Orelse Try Discriminate H; [
    Rewrite (compare_convert_EGAL x' y' H); Reflexivity
  | Rewrite (compare_convert_EGAL x' y'); [
      Reflexivity
    | NewDestruct (compare x' y' EGAL);
      Reflexivity Orelse Discriminate]].
Qed.

Lemma Zcompare_EGAL : (x,y:Z) (Zcompare x y) = EGAL <-> x = y.
Proof.
Intros x y;Split; Intro E; [ Apply Zcompare_EGAL_eq; Assumption
  | Rewrite E; Apply Zcompare_x_x ].
Qed.

Lemma Zcompare_antisym :
  (x,y:Z)(Op (Zcompare x y)) = (Zcompare y x).
Proof.
Intros x y; NewDestruct x; NewDestruct y; Simpl;
  Reflexivity Orelse Discriminate H Orelse 
  Rewrite Pcompare_antisym; Reflexivity.
Qed.

Lemma Zcompare_ANTISYM : 
  (x,y:Z) (Zcompare x y) = SUPERIEUR <->  (Zcompare y x) = INFERIEUR.
Proof.
Intros x y; Split; Intro H; [ 
  Change INFERIEUR with (Op SUPERIEUR); 
  Rewrite <- Zcompare_antisym; Rewrite H; Reflexivity
| Change SUPERIEUR with (Op INFERIEUR); 
  Rewrite <- Zcompare_antisym; Rewrite H; Reflexivity ].
Qed.

(** Transitivity of comparison *)

Lemma Zcompare_trans_SUPERIEUR : 
  (x,y,z:Z) (Zcompare x y) = SUPERIEUR ->  
            (Zcompare y z) = SUPERIEUR ->
            (Zcompare x z) = SUPERIEUR.
Proof.
Intros x y z;Case x;Case y;Case z; Simpl;
Try (Intros; Discriminate H Orelse Discriminate H0);
Auto with arith; [
  Intros p q r H H0;Apply convert_compare_SUPERIEUR; Unfold gt;
  Apply lt_trans with m:=(convert q);
  Apply compare_convert_INFERIEUR;Apply ZC1;Assumption
| Intros p q r; Do 3 Rewrite <- ZC4; Intros H H0;
  Apply convert_compare_SUPERIEUR;Unfold gt;Apply lt_trans with m:=(convert q);
  Apply compare_convert_INFERIEUR;Apply ZC1;Assumption ].
Qed.

(** Comparison and opposite *)

Lemma Zcompare_Zopp :
  (x,y:Z) (Zcompare x y) = (Zcompare (Zopp y) (Zopp x)).
Proof.
(Intros x y;Case x;Case y;Simpl;Auto with arith);
Intros;Rewrite <- ZC4;Trivial with arith.
Qed.

Hints Local Resolve convert_compare_EGAL.

(** Comparison first-order specification *)

Lemma SUPERIEUR_POS :
  (x,y:Z) (Zcompare x y) = SUPERIEUR ->
  (EX h:positive |(Zplus x (Zopp y)) = (POS h)).
Proof.
Intros x y;Case x;Case y; [
  Simpl; Intros H; Discriminate H
| Simpl; Intros p H; Discriminate H
| Intros p H; Exists p; Simpl; Auto with arith
| Intros p H; Exists p; Simpl; Auto with arith
| Intros q p H; Exists (true_sub p q); Unfold Zplus Zopp;
  Unfold Zcompare in H; Rewrite H; Trivial with arith
| Intros q p H; Exists (add p q); Simpl; Trivial with arith
| Simpl; Intros p H; Discriminate H
| Simpl; Intros q p H; Discriminate H
| Unfold Zcompare; Intros q p; Rewrite <- ZC4; Intros H; Exists (true_sub q p);
  Simpl; Rewrite (ZC1 q p H); Trivial with arith].
Qed.

(** Comparison and addition *)

Lemma weaken_Zcompare_Zplus_compatible : 
  ((n,m:Z) (p:positive) 
    (Zcompare (Zplus (POS p) n) (Zplus (POS p) m)) = (Zcompare n m)) ->
   (x,y,z:Z) (Zcompare (Zplus z x) (Zplus z y)) = (Zcompare x y).
Proof.
Intros H x y z; NewDestruct z; [
  Reflexivity
| Apply H
| Rewrite (Zcompare_Zopp x y); Rewrite Zcompare_Zopp; 
  Do 2 Rewrite Zopp_Zplus; Rewrite Zopp_NEG; Apply H ].
Qed.

Hints Local Resolve ZC4.

Lemma weak_Zcompare_Zplus_compatible : 
  (x,y:Z) (z:positive) 
    (Zcompare (Zplus (POS z) x) (Zplus (POS z) y)) = (Zcompare x y).
Proof.
Intros x y z;Case x;Case y;Simpl;Auto with arith; [
  Intros p;Apply convert_compare_INFERIEUR; Apply ZL17
| Intros p;ElimPcompare z p;Intros E;Rewrite E;Auto with arith;
  Apply convert_compare_SUPERIEUR; Rewrite true_sub_convert; [ Unfold gt ;
  Apply ZL16 | Assumption ]
| Intros p;ElimPcompare z p;
  Intros E;Auto with arith; Apply convert_compare_SUPERIEUR;
  Unfold gt;Apply ZL17
| Intros p q;
  ElimPcompare q p;
  Intros E;Rewrite E;[
    Rewrite (compare_convert_EGAL q p E); Apply convert_compare_EGAL
  | Apply convert_compare_INFERIEUR;Do 2 Rewrite convert_add;Apply lt_reg_l;
    Apply compare_convert_INFERIEUR with 1:=E
  | Apply convert_compare_SUPERIEUR;Unfold gt ;Do 2 Rewrite convert_add;
    Apply lt_reg_l;Exact (compare_convert_SUPERIEUR q p E) ]
| Intros p q; 
  ElimPcompare z p;
  Intros E;Rewrite E;Auto with arith;
  Apply convert_compare_SUPERIEUR; Rewrite true_sub_convert; [
    Unfold gt; Apply lt_trans with m:=(convert z); [Apply ZL16 | Apply ZL17]
  | Assumption ]
| Intros p;ElimPcompare z p;Intros E;Rewrite E;Auto with arith; Simpl;
  Apply convert_compare_INFERIEUR;Rewrite true_sub_convert;[Apply ZL16|
  Assumption]
| Intros p q;
  ElimPcompare z q;
  Intros E;Rewrite E;Auto with arith; Simpl;Apply convert_compare_INFERIEUR;
  Rewrite true_sub_convert;[
    Apply lt_trans with m:=(convert z) ;[Apply ZL16|Apply ZL17]
  | Assumption]
| Intros p q; ElimPcompare z q; Intros E0;Rewrite E0;
  ElimPcompare z p; Intros E1;Rewrite E1; ElimPcompare q p;
  Intros E2;Rewrite E2;Auto with arith; [
    Absurd (compare q p EGAL)=INFERIEUR; [
      Rewrite <- (compare_convert_EGAL z q E0);
      Rewrite <- (compare_convert_EGAL z p E1); 
      Rewrite (convert_compare_EGAL z); Discriminate
    | Assumption ]
  | Absurd (compare q p EGAL)=SUPERIEUR; [
      Rewrite <- (compare_convert_EGAL z q E0);
      Rewrite <- (compare_convert_EGAL z p E1);
      Rewrite (convert_compare_EGAL z);Discriminate
    | Assumption]
  | Absurd (compare z p EGAL)=INFERIEUR; [
      Rewrite (compare_convert_EGAL z q E0); 
      Rewrite <- (compare_convert_EGAL q p E2);
      Rewrite (convert_compare_EGAL q);Discriminate
    | Assumption ]
  | Absurd (compare z p EGAL)=INFERIEUR; [
      Rewrite (compare_convert_EGAL z q E0); Rewrite E2;Discriminate
    | Assumption]
  | Absurd (compare z p EGAL)=SUPERIEUR;[
      Rewrite (compare_convert_EGAL z q E0);
      Rewrite <- (compare_convert_EGAL q p E2);
      Rewrite (convert_compare_EGAL q);Discriminate
    | Assumption]
  | Absurd (compare z p EGAL)=SUPERIEUR;[
      Rewrite (compare_convert_EGAL z q E0);Rewrite E2;Discriminate
    | Assumption]
  | Absurd (compare z q EGAL)=INFERIEUR;[
      Rewrite (compare_convert_EGAL z p E1);
      Rewrite (compare_convert_EGAL q p E2);
      Rewrite (convert_compare_EGAL p); Discriminate
    | Assumption]
  | Absurd (compare p q EGAL)=SUPERIEUR; [
      Rewrite <- (compare_convert_EGAL z p E1);
      Rewrite E0; Discriminate
    | Apply ZC2;Assumption ]
  | Simpl; Rewrite (compare_convert_EGAL q p E2);
    Rewrite (convert_compare_EGAL (true_sub p z)); Auto with arith
  | Simpl; Rewrite <- ZC4; Apply convert_compare_SUPERIEUR;
    Rewrite true_sub_convert; [
      Rewrite true_sub_convert; [
        Unfold gt; Apply simpl_lt_plus_l with p:=(convert z);
        Rewrite le_plus_minus_r; [
          Rewrite le_plus_minus_r; [
            Apply compare_convert_INFERIEUR;Assumption
          | Apply lt_le_weak; Apply compare_convert_INFERIEUR;Assumption ]
        | Apply lt_le_weak; Apply compare_convert_INFERIEUR;Assumption ]
      | Apply ZC2;Assumption ]
    | Apply ZC2;Assumption ]
  | Simpl; Rewrite <- ZC4; Apply convert_compare_INFERIEUR; 
    Rewrite true_sub_convert; [
      Rewrite true_sub_convert; [
        Apply simpl_lt_plus_l with p:=(convert z);
        Rewrite le_plus_minus_r; [
          Rewrite le_plus_minus_r; [
            Apply compare_convert_INFERIEUR;Apply ZC1;Assumption
          | Apply lt_le_weak; Apply compare_convert_INFERIEUR;Assumption ]
        | Apply lt_le_weak; Apply compare_convert_INFERIEUR;Assumption ]
      | Apply ZC2;Assumption]
    | Apply ZC2;Assumption ]
  | Absurd (compare z q EGAL)=INFERIEUR; [
      Rewrite (compare_convert_EGAL q p E2);Rewrite E1;Discriminate
    | Assumption ]
  | Absurd (compare q p EGAL)=INFERIEUR; [
      Cut (compare q p EGAL)=SUPERIEUR; [
        Intros E;Rewrite E;Discriminate
      | Apply convert_compare_SUPERIEUR; Unfold gt;
        Apply lt_trans with m:=(convert z); [
          Apply compare_convert_INFERIEUR;Apply ZC1;Assumption
        | Apply compare_convert_INFERIEUR;Assumption ]]
    | Assumption ]
  | Absurd (compare z q EGAL)=SUPERIEUR; [
      Rewrite (compare_convert_EGAL z p E1);
      Rewrite (compare_convert_EGAL q p E2);
      Rewrite (convert_compare_EGAL p); Discriminate
    | Assumption ]
  | Absurd (compare z q EGAL)=SUPERIEUR; [
      Rewrite (compare_convert_EGAL z p E1);
      Rewrite ZC1; [Discriminate | Assumption ]
    | Assumption ]
  | Absurd (compare z q EGAL)=SUPERIEUR; [
      Rewrite (compare_convert_EGAL q p E2); Rewrite E1; Discriminate
    | Assumption ]
  | Absurd (compare q p EGAL)=SUPERIEUR; [
      Rewrite ZC1; [ 
        Discriminate 
      | Apply convert_compare_SUPERIEUR; Unfold gt; 
        Apply lt_trans with m:=(convert z); [
          Apply compare_convert_INFERIEUR;Apply ZC1;Assumption
        | Apply compare_convert_INFERIEUR;Assumption ]]
    | Assumption ]
  | Simpl; Rewrite (compare_convert_EGAL q p E2); Apply convert_compare_EGAL
  | Simpl; Apply convert_compare_SUPERIEUR; Unfold gt;
    Rewrite true_sub_convert; [
      Rewrite true_sub_convert; [
        Apply simpl_lt_plus_l with p:=(convert p); Rewrite le_plus_minus_r; [
          Rewrite plus_sym; Apply simpl_lt_plus_l with p:=(convert q);
          Rewrite plus_assoc_l; Rewrite le_plus_minus_r; [
            Rewrite (plus_sym (convert q)); Apply lt_reg_l;
            Apply compare_convert_INFERIEUR;Assumption
          | Apply lt_le_weak; Apply compare_convert_INFERIEUR;
            Apply ZC1;Assumption ]
        | Apply lt_le_weak; Apply compare_convert_INFERIEUR;Apply ZC1; 
          Assumption ]
      | Assumption ]
    | Assumption ]
  | Simpl; Apply convert_compare_INFERIEUR; Rewrite true_sub_convert; [
      Rewrite true_sub_convert; [
        Apply simpl_lt_plus_l with p:=(convert q); Rewrite le_plus_minus_r; [
          Rewrite plus_sym; Apply simpl_lt_plus_l with p:=(convert p);
          Rewrite plus_assoc_l; Rewrite le_plus_minus_r; [
            Rewrite (plus_sym (convert p)); Apply lt_reg_l;
            Apply compare_convert_INFERIEUR;Apply ZC1;Assumption 
          | Apply lt_le_weak; Apply compare_convert_INFERIEUR;Apply ZC1;
            Assumption ]
        | Apply lt_le_weak;Apply compare_convert_INFERIEUR;Apply ZC1;Assumption]
      | Assumption]
    | Assumption]]].
Qed.

Lemma Zcompare_Zplus_compatible : 
   (x,y,z:Z) (Zcompare (Zplus z x) (Zplus z y)) = (Zcompare x y).
Proof.
Exact (weaken_Zcompare_Zplus_compatible weak_Zcompare_Zplus_compatible).
Qed.

Lemma Zcompare_Zplus_compatible2 :
  (r:relation)(x,y,z,t:Z)
    (Zcompare x y) = r -> (Zcompare z t) = r ->
    (Zcompare (Zplus x z) (Zplus y t)) = r.
Proof.
Intros r x y z t; Case r; [
  Intros H1 H2; Elim (Zcompare_EGAL x y); Elim (Zcompare_EGAL z t);
  Intros H3 H4 H5 H6; Rewrite H3; [ 
    Rewrite H5; [ Elim (Zcompare_EGAL (Zplus y t) (Zplus y t)); Auto with arith | Auto with arith ]
  | Auto with arith ]
| Intros H1 H2; Elim (Zcompare_ANTISYM (Zplus y t) (Zplus x z));
  Intros H3 H4; Apply H3;
  Apply Zcompare_trans_SUPERIEUR with y:=(Zplus y z) ; [
    Rewrite Zcompare_Zplus_compatible;
    Elim (Zcompare_ANTISYM t z); Auto with arith
  | Do 2 Rewrite <- (Zplus_sym z); 
    Rewrite Zcompare_Zplus_compatible;
    Elim (Zcompare_ANTISYM y x); Auto with arith]
| Intros H1 H2;
  Apply Zcompare_trans_SUPERIEUR with y:=(Zplus x t) ; [
    Rewrite Zcompare_Zplus_compatible; Assumption
  | Do 2 Rewrite <- (Zplus_sym t);
    Rewrite Zcompare_Zplus_compatible; Assumption]].
Qed.

Lemma Zcompare_Zs_SUPERIEUR : (x:Z)(Zcompare (Zs x) x)=SUPERIEUR.
Proof.
Intro x; Unfold Zs; Pattern 2 x; Rewrite <- (Zero_right x); 
Rewrite Zcompare_Zplus_compatible;Reflexivity.
Qed.

Lemma Zcompare_et_un: 
  (x,y:Z) (Zcompare x y)=SUPERIEUR <-> 
    ~(Zcompare x (Zplus y (POS xH)))=INFERIEUR.
Proof.
Intros x y; Split; [
  Intro H; (ElimCompare 'x '(Zplus y (POS xH)));[
    Intro H1; Rewrite H1; Discriminate
  | Intros H1; Elim SUPERIEUR_POS with 1:=H; Intros h H2; 
    Absurd (gt (convert h) O) /\ (lt (convert h) (S O)); [
      Unfold not ;Intros H3;Elim H3;Intros H4 H5; Absurd (gt (convert h) O); [
        Unfold gt ;Apply le_not_lt; Apply le_S_n; Exact H5
      | Assumption]
    | Split; [
        Elim (ZL4 h); Intros i H3;Rewrite H3; Apply gt_Sn_O
      | Change (lt (convert h) (convert xH)); 
        Apply compare_convert_INFERIEUR;
        Change (Zcompare (POS h) (POS xH))=INFERIEUR;
        Rewrite <- H2; Rewrite <- [m,n:Z](Zcompare_Zplus_compatible m n y);
        Rewrite (Zplus_sym x);Rewrite Zplus_assoc; Rewrite Zplus_inverse_r;
        Simpl; Exact H1 ]]
  | Intros H1;Rewrite -> H1;Discriminate ]
| Intros H; (ElimCompare 'x '(Zplus y (POS xH))); [
    Intros H1;Elim (Zcompare_EGAL x (Zplus y (POS xH))); Intros H2 H3;
    Rewrite  (H2 H1); Exact (Zcompare_Zs_SUPERIEUR y)
  | Intros H1;Absurd (Zcompare x (Zplus y (POS xH)))=INFERIEUR;Assumption
  | Intros H1; Apply Zcompare_trans_SUPERIEUR with y:=(Zs y); 
      [ Exact H1 | Exact (Zcompare_Zs_SUPERIEUR y)]]].
Qed.

(** Successor and comparison *)

Lemma Zcompare_n_S : (n,m:Z)(Zcompare (Zs n) (Zs m)) = (Zcompare n m).
Proof.
Intros n m;Unfold Zs ;Do 2 Rewrite -> [t:Z](Zplus_sym t (POS xH));
Rewrite -> Zcompare_Zplus_compatible;Auto with arith.
Qed.
 
(** Multiplication and comparison *)

Lemma Zcompare_Zmult_compatible : 
   (x:positive)(y,z:Z)
      (Zcompare (Zmult (POS x) y) (Zmult (POS x) z)) = (Zcompare y z).
Proof.
Intros x; NewInduction x as [p H|p H|]; [
  Intros y z;
  Cut (POS (xI p))=(Zplus (Zplus (POS p) (POS p)) (POS xH)); [
    Intros E; Rewrite E; Do 4 Rewrite Zmult_plus_distr_l; 
    Do 2 Rewrite Zmult_one;
    Apply Zcompare_Zplus_compatible2; [
      Apply Zcompare_Zplus_compatible2; Apply H
    | Trivial with arith]
  | Simpl; Rewrite (add_x_x p); Trivial with arith]
| Intros y z; Cut (POS (xO p))=(Zplus (POS p) (POS p)); [
    Intros E; Rewrite E; Do 2 Rewrite Zmult_plus_distr_l;
      Apply Zcompare_Zplus_compatible2; Apply H
    | Simpl; Rewrite (add_x_x p); Trivial with arith]
  | Intros y z; Do 2 Rewrite Zmult_one; Trivial with arith].
Qed.


(** Reverting [x ?= y] to trichotomy *)

Lemma rename : (A:Set)(P:A->Prop)(x:A) ((y:A)(x=y)->(P y)) -> (P x).
Proof.
Auto with arith. 
Qed.

Lemma Zcompare_elim :
  (c1,c2,c3:Prop)(x,y:Z)
    ((x=y) -> c1) ->(`x<y` -> c2) ->(`x>y`-> c3)
     -> Cases (Zcompare x y) of EGAL => c1 | INFERIEUR => c2 | SUPERIEUR => c3 end.
Proof.
Intros c1 c2 c3 x y; Intros.
Apply rename with x:=(Zcompare x y); Intro r; Elim r;
[ Intro; Apply H; Apply (Zcompare_EGAL_eq x y); Assumption
| Unfold Zlt in H0; Assumption
| Unfold Zgt in H1; Assumption ].
Qed.

Lemma Zcompare_eq_case : 
  (c1,c2,c3:Prop)(x,y:Z) c1 -> x=y ->
  Cases (Zcompare x y) of EGAL => c1 | INFERIEUR => c2 | SUPERIEUR => c3 end.
Proof.
Intros c1 c2 c3 x y; Intros.
Rewrite H0; Rewrite (Zcompare_x_x).
Assumption.
Qed.

(** Decompose an egality between two [?=] relations into 3 implications *)

Lemma Zcompare_egal_dec :
   (x1,y1,x2,y2:Z)
    (`x1<y1`->`x2<y2`)
     ->((Zcompare x1 y1)=EGAL -> (Zcompare x2 y2)=EGAL)
        ->(`x1>y1`->`x2>y2`)->(Zcompare x1 y1)=(Zcompare x2 y2).
Proof.
Intros x1 y1 x2 y2.
Unfold Zgt; Unfold Zlt;
Case (Zcompare x1 y1); Case (Zcompare x2 y2); Auto with arith; Symmetry; Auto with arith.
Qed.

(** Relating [x ?= y] to [Zle], [Zlt], [Zge] or [Zgt] *)

Lemma Zle_Zcompare :
  (x,y:Z)`x<=y` ->
  Cases (Zcompare x y) of EGAL => True | INFERIEUR => True | SUPERIEUR => False end.
Proof.
Intros x y; Unfold Zle; Elim (Zcompare x y); Auto with arith.
Qed.

Lemma Zlt_Zcompare :
  (x,y:Z)`x<y`  ->
  Cases (Zcompare x y) of EGAL => False | INFERIEUR => True | SUPERIEUR => False end.
Proof.
Intros x y; Unfold Zlt; Elim (Zcompare x y); Intros; Discriminate Orelse Trivial with arith.
Qed.

Lemma Zge_Zcompare :
  (x,y:Z)`x>=y`->
  Cases (Zcompare x y) of EGAL => True | INFERIEUR => False | SUPERIEUR => True end.
Proof.
Intros x y; Unfold Zge; Elim (Zcompare x y); Auto with arith. 
Qed.

Lemma Zgt_Zcompare :
  (x,y:Z)`x>y` ->
  Cases (Zcompare x y) of EGAL => False | INFERIEUR => False | SUPERIEUR => True end.
Proof.
Intros x y; Unfold Zgt; Elim (Zcompare x y); Intros; Discriminate Orelse Trivial with arith.
Qed.

(**********************************************************************)
(* Other properties *)

V7only [Set Implicit Arguments.].

Lemma  Zcompare_Zmult_left : (x,y,z:Z)`z>0` -> `x ?= y`=`z*x ?= z*y`.
Proof.
Intros x y z H; NewDestruct z.
  Discriminate H.
  Rewrite Zcompare_Zmult_compatible; Reflexivity.
  Discriminate H.
Qed.

Lemma Zcompare_Zmult_right : (x,y,z:Z)` z>0` -> `x ?= y`=`x*z ?= y*z`.
Proof.
Intros x y z H;
Rewrite (Zmult_sym x z);
Rewrite (Zmult_sym y z);
Apply Zcompare_Zmult_left; Assumption.
Qed.

V7only [Unset Implicit Arguments.].

