(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(** Binary Integers (Pierre Crégut, CNET, Lannion, France) *)

Require Le.
Require Lt.
Require Plus.
Require Mult.
Require Minus.

(** Definition of fast binary integers *)
Section fast_integers.

Inductive positive : Set :=
  xI : positive -> positive
| xO : positive -> positive
| xH : positive.

Inductive Z : Set := 
  ZERO : Z | POS : positive -> Z | NEG : positive -> Z.

Inductive relation : Set := 
  EGAL :relation | INFERIEUR : relation | SUPERIEUR : relation.

(** Addition *)
Fixpoint add_un [x:positive]:positive :=
  <positive> Cases x of
               (xI x') => (xO (add_un x'))
             | (xO x') => (xI x')
             | xH => (xO xH)
             end.

Fixpoint add [x,y:positive]:positive :=
  <positive>Cases x of
     (xI x') => <positive>Cases y of
                    (xI y') => (xO (add_carry x' y'))
                  | (xO y') => (xI (add x' y'))
                  | xH      => (xO (add_un x'))
                  end
   | (xO x') => <positive>Cases y of
                    (xI y') => (xI (add x' y'))
                  | (xO y') => (xO (add x' y'))
                  | xH      => (xI x')
                  end
   | xH      => <positive>Cases y of
                    (xI y') => (xO (add_un y'))
                  | (xO y') => (xI y')
                  | xH      => (xO xH)
                  end
   end
with add_carry [x,y:positive]:positive :=
  <positive>Cases x of
     (xI x') => <positive>Cases y of
            (xI y') => (xI (add_carry x' y'))
          | (xO y') => (xO (add_carry x' y'))
          | xH      => (xI (add_un x'))
          end
   | (xO x') => <positive>Cases y of
            (xI y') => (xO (add_carry x' y'))
          | (xO y') => (xI (add x' y'))
          | xH      => (xO (add_un x'))
          end
   | xH      => <positive>Cases y of
            (xI y') => (xI (add_un y'))
          | (xO y') => (xO (add_un y'))
          | xH      => (xI xH)
          end
  end.

Infix LEFTA 4 "+" add : positive_scope.

Open Scope positive_scope.

(** From positive to natural numbers *)
Fixpoint positive_to_nat [x:positive]:nat -> nat :=
  [pow2:nat]
    <nat> Cases x of
     (xI x') => (plus pow2 (positive_to_nat x' (plus pow2 pow2)))
   | (xO x') => (positive_to_nat x' (plus pow2 pow2))
   | xH      => pow2
   end.

Definition convert := [x:positive] (positive_to_nat x (S O)).

(** From natural numbers to positive *)
Fixpoint anti_convert [n:nat]: positive :=
  <positive> Cases n of
                O => xH
             | (S x') => (add_un (anti_convert x'))
             end.

(* Correctness of addition *)
Lemma convert_add_un :
  (x:positive)(m:nat)
    (positive_to_nat (add_un x) m) = (plus m (positive_to_nat x m)).
Proof.
Induction x; Simpl; Auto with arith; Intros x' H0 m; Rewrite H0;
Rewrite plus_assoc_l; Trivial with arith.
Qed.

Theorem convert_add_carry :
  (x,y:positive)(m:nat)
    (positive_to_nat (add_carry x y) m) =
    (plus m (positive_to_nat (add x y) m)).
Proof.
Induction x; Induction y; Simpl; Auto with arith; [
  Intros y' H1 m; Rewrite H; Rewrite plus_assoc_l; Trivial with arith
| Intros y' H1 m; Rewrite H; Rewrite plus_assoc_l; Trivial with arith
| Intros m; Rewrite convert_add_un; Rewrite plus_assoc_l; Trivial with arith
| Intros y' H m; Rewrite convert_add_un; Apply plus_assoc_r ].
Qed.

Theorem cvt_carry :
  (x,y:positive)(convert (add_carry x y)) = (S (convert (add x y))).
Proof.
Intros;Unfold convert; Rewrite convert_add_carry; Simpl; Trivial with arith.
Qed.

Theorem add_verif :
  (x,y:positive)(m:nat)
    (positive_to_nat (add x y) m) = 
    (plus (positive_to_nat x m) (positive_to_nat y m)).
Proof.
Induction x;Induction y;Simpl;Auto with arith; [
  Intros y' H1 m;Rewrite convert_add_carry; Rewrite H; 
  Rewrite plus_assoc_r; Rewrite plus_assoc_r; 
  Rewrite (plus_permute m (positive_to_nat p (plus m m))); Trivial with arith
| Intros y' H1 m; Rewrite H; Apply plus_assoc_l
| Intros m; Rewrite convert_add_un; 
  Rewrite (plus_sym (plus m (positive_to_nat p (plus m m))));
  Apply plus_assoc_r
| Intros y' H1 m; Rewrite H; Apply plus_permute
| Intros y' H1 m; Rewrite convert_add_un; Apply plus_assoc_r ].
Qed.

Theorem convert_add:
  (x,y:positive) (convert (add x y)) = (plus (convert x) (convert y)).
Proof.
Intros x y; Exact (add_verif x y (S O)).
Qed.

(** Correctness of conversion *)
Theorem bij1 : (m:nat) (convert (anti_convert m)) = (S m).
Proof.
Induction m; [
  Unfold convert; Simpl; Trivial with arith
| Unfold convert; Intros n H; Simpl; Rewrite convert_add_un; Rewrite H; Auto with arith].
Qed.

Theorem compare_positive_to_nat_O : 
	(p:positive)(m:nat)(le m  (positive_to_nat p m)).
Induction p; Simpl; Auto with arith.
Intros; Apply le_trans with (plus m m);  Auto with arith.
Qed.

Theorem compare_convert_O : (p:positive)(lt O (convert p)).
Intro; Unfold convert; Apply lt_le_trans with (S O); Auto with arith.
Apply compare_positive_to_nat_O.
Qed.

Hints Resolve compare_convert_O.

(** Subtraction *)
Fixpoint double_moins_un [x:positive]:positive :=
  <positive>Cases x of
      (xI x') => (xI (xO x'))
    | (xO x') => (xI (double_moins_un x'))
    | xH => xH
    end.

Definition sub_un := [x:positive]
  <positive> Cases x of
             (xI x') => (xO x')
           | (xO x') => (double_moins_un x')
           | xH => xH
           end.

Lemma sub_add_one : (x:positive) (sub_un (add_un x)) = x.
Proof.
(Induction x; [Idtac | Idtac | Simpl;Auto with arith ]);
(Intros p; Elim p; [Idtac | Idtac | Simpl;Auto with arith]);
Simpl; Intros q H1 H2; Case H2; Simpl; Trivial with arith.
Qed.

Lemma is_double_moins_un : (x:positive) (add_un (double_moins_un x)) = (xO x).
Proof.
(Induction x;Simpl;Auto with arith); Intros m H;Rewrite H;Trivial with arith.
Qed.

Lemma add_sub_one : (x:positive) (x=xH) \/ (add_un (sub_un x)) = x.
Proof.
Induction x; [
  Simpl; Auto with arith
| Simpl; Intros;Right;Apply is_double_moins_un
| Auto with arith ].
Qed.

Lemma ZL0 : (S (S O))=(plus (S O) (S O)).
Proof. Auto with arith. Qed.

Lemma ZL1: (y:positive)(xO (add_un y)) = (add_un (add_un (xO y))).
Proof.
Induction y; Simpl; Auto with arith.
Qed.

Lemma ZL2:
  (y:positive)(m:nat)
    (positive_to_nat y (plus m m)) =
              (plus (positive_to_nat y m) (positive_to_nat y m)).
Proof.
Induction y; [
  Intros p H m; Simpl; Rewrite H; Rewrite plus_assoc_r; 
  Rewrite (plus_permute m (positive_to_nat p (plus m m)));
  Rewrite plus_assoc_r; Auto with arith
| Intros p H m; Simpl; Rewrite H; Auto with arith
| Intro;Simpl; Trivial with arith ].
Qed.

Lemma ZL3: (x:nat) (add_un (anti_convert (plus x x))) =  (xO (anti_convert x)).
Proof.
Induction x; [
  Simpl; Auto with arith
| Intros y H; Simpl; Rewrite  plus_sym; Simpl; Rewrite  H; Rewrite  ZL1;Auto with arith].
Qed.

Lemma ZL4: (y:positive) (EX h:nat |(convert y)=(S h)).
Proof.
Induction y; [
  Intros p H;Elim H; Intros x H1; Exists (plus (S x) (S x));
  Unfold convert ;Simpl; Rewrite ZL0; Rewrite ZL2; Unfold convert in H1;
  Rewrite H1; Auto with arith
| Intros p H1;Elim H1;Intros x H2; Exists (plus x (S x)); Unfold convert;
  Simpl; Rewrite ZL0; Rewrite ZL2;Unfold convert in H2; Rewrite H2; Auto with arith
| Exists O ;Auto with arith ].
Qed.

Lemma ZL5: (x:nat) (anti_convert (plus (S x) (S x))) =  (xI (anti_convert x)).
Proof.
Induction x;Simpl; [
  Auto with arith
| Intros y H; Rewrite <- plus_n_Sm; Simpl; Rewrite H; Auto with arith].
Qed.

Lemma bij2 : (x:positive) (anti_convert (convert x)) = (add_un x).
Proof.
Induction x; [
  Intros p H; Simpl; Rewrite <- H; Rewrite ZL0;Rewrite ZL2; Elim (ZL4 p); 
  Unfold convert; Intros n H1;Rewrite H1; Rewrite ZL3; Auto with arith

| Intros p H; Unfold convert ;Simpl; Rewrite ZL0; Rewrite ZL2;
  Rewrite <- (sub_add_one
               (anti_convert
                 (plus (positive_to_nat p (S O)) (positive_to_nat p (S O)))));
  Rewrite <- (sub_add_one (xI p));
  Simpl;Rewrite <- H;Elim (ZL4 p); Unfold convert ;Intros n H1;Rewrite H1;
  Rewrite ZL5; Simpl; Trivial with arith
| Unfold convert; Simpl; Auto with arith ].
Qed.

(** Comparison of positive *)
Fixpoint compare [x,y:positive]: relation -> relation :=
  [r:relation] <relation> Cases x of
            (xI x') => <relation>Cases y of
                          (xI y') => (compare x' y' r)
                        | (xO y') => (compare x' y' SUPERIEUR)
                        | xH => SUPERIEUR
                        end
          | (xO x') => <relation>Cases y of
                          (xI y') => (compare x' y' INFERIEUR)
                        | (xO y') => (compare x' y' r)
                        | xH => SUPERIEUR
                        end
          | xH => <relation>Cases y of
                     (xI y') => INFERIEUR
                   | (xO y') => INFERIEUR
                   | xH => r
                   end
  end.

Theorem compare_convert1 : 
 (x,y:positive) 
  ~(compare x y SUPERIEUR) = EGAL /\ ~(compare x y INFERIEUR) = EGAL.
Proof.
Induction x;Induction y;Split;Simpl;Auto with arith;
  Discriminate Orelse (Elim (H p0); Auto with arith).
Qed.

Theorem compare_convert_EGAL : (x,y:positive) (compare x y EGAL) = EGAL -> x=y.
Proof.
Induction x;Induction y;Simpl;Auto with arith; [
  Intros z H1 H2; Rewrite (H z); Trivial with arith
| Intros z H1 H2; Absurd (compare p z SUPERIEUR)=EGAL ;
   [ Elim (compare_convert1 p z);Auto with arith | Assumption ]
| Intros H1;Discriminate H1
| Intros z H1 H2; Absurd (compare p z INFERIEUR) = EGAL; 
    [ Elim (compare_convert1 p z);Auto with arith | Assumption ]
| Intros z H1 H2 ;Rewrite (H z);Auto with arith 
| Intros H1;Discriminate H1
| Intros p H H1;Discriminate H1
| Intros p H H1;Discriminate H1 ].
Qed.

Lemma ZL6:
  (p:positive) (positive_to_nat p (S(S O))) = (plus (convert p) (convert p)).
Proof.
Intros p;Rewrite ZL0; Rewrite ZL2; Trivial with arith.
Qed.
 
Lemma ZL7:
  (m,n:nat) (lt m n) -> (lt (plus m m) (plus n n)).
Proof.
Intros m n H; Apply lt_trans with m:=(plus m n); [
  Apply lt_reg_l with 1:=H
| Rewrite (plus_sym m n); Apply lt_reg_l with 1:=H ].
Qed.

Lemma ZL8:
  (m,n:nat) (lt m n) -> (lt (S (plus m m)) (plus n n)).
Proof.
Intros m n H; Apply le_lt_trans with m:=(plus m n); [
  Change (lt (plus m m) (plus m n)) ; Apply lt_reg_l with 1:=H
| Rewrite (plus_sym m n); Apply lt_reg_l with 1:=H ].
Qed.

Lemma ZLSI:
 (x,y:positive) (compare x y SUPERIEUR) = INFERIEUR -> 
                (compare x y EGAL) = INFERIEUR.
Proof.
Induction x;Induction y;Simpl;Auto with arith; 
  Discriminate Orelse Intros H;Discriminate H.
Qed.

Lemma ZLIS:
 (x,y:positive) (compare x y INFERIEUR) = SUPERIEUR -> 
                (compare x y EGAL) = SUPERIEUR.
Proof.
Induction x;Induction y;Simpl;Auto with arith; 
  Discriminate Orelse Intros H;Discriminate H.
Qed.

Lemma ZLII:
 (x,y:positive) (compare x y INFERIEUR) = INFERIEUR ->
                (compare x y EGAL) = INFERIEUR \/ x = y.
Proof.
(Induction x;Induction y;Simpl;Auto with arith;Try Discriminate);
 Intros z H1 H2; Elim (H z H2);Auto with arith; Intros E;Rewrite E;
 Auto with arith.
Qed.

Lemma ZLSS:
 (x,y:positive) (compare x y SUPERIEUR) = SUPERIEUR ->
                (compare x y EGAL) = SUPERIEUR \/ x = y.
Proof.
(Induction x;Induction y;Simpl;Auto with arith;Try Discriminate);
 Intros z H1 H2; Elim (H z H2);Auto with arith; Intros E;Rewrite E;
 Auto with arith.
Qed.

Theorem compare_convert_INFERIEUR : 
  (x,y:positive) (compare x y EGAL) = INFERIEUR -> 
    (lt (convert x) (convert y)).
Proof.
Induction x;Induction y; [
  Intros z H1 H2; Unfold convert ;Simpl; Apply lt_n_S; 
  Do 2 Rewrite ZL6; Apply ZL7; Apply H; Simpl in H2; Assumption
| Intros q H1 H2; Unfold convert ;Simpl; Do 2 Rewrite ZL6; 
  Apply ZL8; Apply H;Simpl in H2; Apply ZLSI;Assumption
| Simpl; Intros H1;Discriminate H1
| Simpl; Intros q H1 H2; Unfold convert ;Simpl;Do 2 Rewrite ZL6; 
  Elim (ZLII p q H2); [
    Intros H3;Apply lt_S;Apply ZL7; Apply H;Apply H3
  | Intros E;Rewrite E;Apply lt_n_Sn]
| Simpl;Intros q H1 H2; Unfold convert ;Simpl;Do 2 Rewrite ZL6; 
  Apply ZL7;Apply H;Assumption
| Simpl; Intros H1;Discriminate H1
| Intros q H1 H2; Unfold convert ;Simpl; Apply lt_n_S; Rewrite ZL6;
  Elim (ZL4 q);Intros h H3; Rewrite H3;Simpl; Apply lt_O_Sn
| Intros q H1 H2; Unfold convert ;Simpl; Rewrite ZL6; Elim (ZL4 q);Intros h H3;
  Rewrite H3; Simpl; Rewrite <- plus_n_Sm; Apply lt_n_S; Apply lt_O_Sn
| Simpl; Intros H;Discriminate H ].
Qed.

Theorem compare_convert_SUPERIEUR : 
  (x,y:positive) (compare x y EGAL)=SUPERIEUR -> (gt (convert x) (convert y)).
Proof.
Unfold gt; Induction x;Induction y; [
  Simpl;Intros q H1 H2; Unfold convert ;Simpl;Do 2 Rewrite ZL6; 
  Apply lt_n_S; Apply ZL7; Apply H;Assumption
| Simpl;Intros q H1 H2; Unfold convert ;Simpl; Do 2 Rewrite ZL6;
  Elim (ZLSS p q H2); [
    Intros H3;Apply lt_S;Apply ZL7;Apply H;Assumption
  | Intros E;Rewrite E;Apply lt_n_Sn]
| Intros H1;Unfold convert ;Simpl; Rewrite ZL6;Elim (ZL4 p);
  Intros h H3;Rewrite H3;Simpl; Apply lt_n_S; Apply lt_O_Sn
| Simpl;Intros q H1 H2;Unfold convert ;Simpl;Do 2 Rewrite ZL6; 
  Apply ZL8; Apply H; Apply ZLIS; Assumption
| Simpl;Intros q H1 H2; Unfold convert ;Simpl;Do 2 Rewrite ZL6; 
  Apply ZL7;Apply H;Assumption
| Intros H1;Unfold convert ;Simpl; Rewrite ZL6; Elim (ZL4 p);
  Intros h H3;Rewrite H3;Simpl; Rewrite <- plus_n_Sm;Apply lt_n_S;
  Apply lt_O_Sn
| Simpl; Intros q H1 H2;Discriminate H2
| Simpl; Intros q H1 H2;Discriminate H2
| Simpl;Intros H;Discriminate H ].
Qed.

Lemma Dcompare : (r:relation) r=EGAL \/ r = INFERIEUR \/ r = SUPERIEUR.
Proof.
Induction r; Auto with arith. 
Qed.

Theorem convert_compare_INFERIEUR : 
  (x,y:positive)(lt (convert x) (convert y)) -> (compare x y EGAL) = INFERIEUR.
Proof.
Intros x y; Unfold gt; Elim (Dcompare (compare x y EGAL)); [
  Intros E; Rewrite (compare_convert_EGAL x y E); 
  Intros H;Absurd (lt (convert y) (convert y)); [ Apply lt_n_n | Assumption ]
| Intros H;Elim H; [
    Auto with arith
  | Intros H1 H2; Absurd (lt (convert x) (convert y)); [
      Apply lt_not_sym; Change (gt (convert x) (convert y)); 
      Apply compare_convert_SUPERIEUR; Assumption
    | Assumption ]]].
Qed.

Theorem convert_compare_SUPERIEUR : 
  (x,y:positive)(gt (convert x) (convert y)) -> (compare x y EGAL) = SUPERIEUR.
Proof.
Intros x y; Unfold gt; Elim (Dcompare (compare x y EGAL)); [
  Intros E; Rewrite (compare_convert_EGAL x y E); 
  Intros H;Absurd (lt (convert y) (convert y)); [ Apply lt_n_n | Assumption ]
| Intros H;Elim H; [
    Intros H1 H2; Absurd (lt (convert y) (convert x)); [
      Apply lt_not_sym; Apply compare_convert_INFERIEUR; Assumption
    | Assumption ]
  | Auto with arith]].
Qed.

Theorem convert_compare_EGAL: (x:positive)(compare x x EGAL)=EGAL.
Induction x; Auto with arith.
Qed.

(** Natural numbers coded with positive *)

Inductive entier: Set := Nul : entier | Pos : positive -> entier.

Definition Un_suivi_de := 
  [x:entier]<entier> Cases x of Nul => (Pos xH) | (Pos p) => (Pos (xI p)) end.

Definition Zero_suivi_de := 
  [x:entier]<entier> Cases x of Nul => Nul | (Pos p) => (Pos (xO p)) end.

Definition double_moins_deux :=
  [x:positive] <entier>Cases x of
           (xI x') => (Pos (xO (xO x')))
         | (xO x') => (Pos (xO (double_moins_un x')))
         | xH => Nul
         end.
Lemma ZS: (p:entier) (Zero_suivi_de p) = Nul -> p = Nul.
Proof.
Induction p;Simpl; [ Trivial with arith | Intros q H;Discriminate H ].
Qed.

Lemma US: (p:entier) ~(Un_suivi_de p)=Nul.
Proof.
Induction p; Intros; Discriminate.
Qed.

Lemma USH: (p:entier) (Un_suivi_de p) = (Pos xH) -> p = Nul.
Proof.
Induction p;Simpl; [ Trivial with arith | Intros q H;Discriminate H ].
Qed.

Lemma ZSH: (p:entier) ~(Zero_suivi_de p)= (Pos xH).
Proof.
Induction p; Intros; Discriminate.
Qed.

Fixpoint sub_pos[x,y:positive]:entier :=
  <entier>Cases x of
         (xI x') => <entier>Cases y of
                           (xI y') => (Zero_suivi_de (sub_pos x' y'))
                         | (xO y') => (Un_suivi_de (sub_pos x' y'))
                         | xH => (Pos (xO x'))
                         end
       | (xO x') => <entier>Cases y of
                           (xI y') => (Un_suivi_de (sub_neg x' y'))
                         | (xO y') => (Zero_suivi_de (sub_pos x' y'))
                         | xH => (Pos (double_moins_un x'))
                         end
       | xH => <entier>Cases y of
                           (xI y') => (Pos (double_moins_un y'))
                         | (xO y') => (double_moins_deux y')
                         | xH => Nul
                         end
       end
with sub_neg [x,y:positive]:entier :=
  <entier>Cases x of
       (xI x') => <entier>Cases y of
                            (xI y') => (Un_suivi_de (sub_neg x' y'))
                          | (xO y') => (Zero_suivi_de (sub_pos x' y'))
                          | xH => (Pos (double_moins_un x'))
                          end
     | (xO x') => <entier>Cases y of
                            (xI y') => (Zero_suivi_de (sub_neg x' y'))
                          | (xO y') => (Un_suivi_de (sub_neg x' y'))
                          | xH => (double_moins_deux x')
                          end
     | xH => <entier>Cases y of
                            (xI y') => (Pos (xO y'))
                          | (xO y') => (Pos (double_moins_un y'))
                          | xH => Nul
                          end
     end.

Theorem sub_pos_x_x : (x:positive) (sub_pos x x) = Nul.
Proof.
Induction x; [
  Simpl; Intros p H;Rewrite H;Simpl; Trivial with arith
| Intros p H;Simpl;Rewrite H;Auto with arith
| Auto with arith ].
Qed.

Theorem ZL10: (x,y:positive)
 (compare x y EGAL) = SUPERIEUR ->
 (sub_pos x y) = (Pos xH) -> (sub_neg x y) = Nul.
Proof.
Induction x;Induction y; [
  Intros q H1 H2 H3; Absurd (sub_pos (xI p) (xI q))=(Pos xH); 
    [ Simpl; Apply ZSH | Assumption ]
| Intros q H1 H2 H3; Simpl in H3; Cut (sub_pos p q)=Nul; [
     Intros H4;Simpl;Rewrite H4; Simpl; Trivial with arith
   | Apply USH;Assumption ]
| Simpl; Intros H1 H2;Discriminate H2
| Intros q H1 H2;
  Change (Un_suivi_de (sub_neg p q))=(Pos xH) 
            -> (Zero_suivi_de (sub_neg p q))=Nul;
  Intros H3; Rewrite (USH (sub_neg p q) H3); Simpl; Auto with arith
| Intros q H1 H2 H3; Absurd (sub_pos (xO p) (xO q))=(Pos xH);
    [ Simpl; Apply ZSH | Assumption ]
| Intros H1; Elim p; [ 
    Simpl; Intros q H2 H3;Discriminate H3
  | Simpl; Intros q H2 H3;Discriminate H3
  | Simpl; Auto with arith ]
| Simpl; Intros q H1 H2 H3;Discriminate H2
| Simpl; Intros q H1 H2 H3;Discriminate H2 
| Simpl; Intros H;Discriminate H ].
Qed.

Lemma ZL11: (x:positive) (x=xH) \/ ~(x=xH).
Proof.
Intros x;Case x;Intros; (Left;Reflexivity) Orelse (Right;Discriminate).
Qed.

Lemma ZL12: (q:positive) (add_un q) = (add q xH).
Proof.
Induction q; Intros; Simpl; Trivial with arith.
Qed.

Lemma ZL12bis: (q:positive) (add_un q) = (add xH q).
Proof.
Induction q; Intros; Simpl; Trivial with arith.
Qed.

Theorem ZL13:
  (x,y:positive)(add_carry x y) = (add_un (add x y)).
Proof.
(Induction x;Induction y;Simpl;Auto with arith); Intros q H1;Rewrite H;
 Auto with arith.
Qed.

Theorem ZL14:
  (x,y:positive)(add x (add_un y)) = (add_un (add x y)).
Proof.
Induction x;Induction y;Simpl;Auto with arith; [
  Intros q H1; Rewrite ZL13; Rewrite  H; Auto with arith
| Intros q H1; Rewrite ZL13; Auto with arith
| Elim p;Simpl;Auto with arith
| Intros q H1;Rewrite H;Auto with arith
| Elim p;Simpl;Auto with arith ].
Qed.

Theorem ZL15:
  (q,z:positive) ~z=xH -> (add_carry q (sub_un z)) = (add q z).
Proof.
Intros q z H; Elim (add_sub_one z); [
  Intro;Absurd z=xH;Auto with arith
| Intros E;Pattern 2 z ;Rewrite <- E; Rewrite ZL14; Rewrite ZL13; Trivial with arith ].
Qed. 

Theorem sub_pos_SUPERIEUR:
  (x,y:positive)(compare x y EGAL)=SUPERIEUR -> 
    (EX h:positive | (sub_pos x y) = (Pos h) /\ (add y h) = x /\
                     (h = xH \/ (sub_neg x y) = (Pos (sub_un h)))).
Proof.
Induction x;Induction y; [
  Intros q H1 H2; Elim (H q H2); Intros z H3;Elim H3;Intros H4 H5; 
  Elim H5;Intros H6 H7;   Exists (xO z); Split; [
    Simpl; Rewrite H4; Auto with arith
  | Split; [
      Simpl; Rewrite H6; Auto with arith
    | Right; Simpl; Elim (ZL11 z); [
        Intros H8; Simpl; Rewrite ZL10; [
          Rewrite H8; Auto with arith
        | Exact H2
        | Rewrite <- H8; Auto with arith ]
     | Intro H8; Elim H7; [
         Intro H9; Absurd z=xH; Auto with arith
       | Intros H9;Simpl;Rewrite H9;Generalize H8 ;Case z;Auto with arith; 
         Intros H10;Absurd xH=xH;Auto with arith ]]]]
| Intros q H1 H2; Simpl in H2; Elim ZLSS with 1:=H2; [
    Intros H3;Elim (H q H3); Intros z H4; Exists (xI z);
    Elim H4;Intros H5 H6;Elim H6;Intros H7 H8; Split; [
      Simpl;Rewrite H5;Auto with arith
    | Split; [
        Simpl; Rewrite H7; Trivial with arith
      | Right;Change (Zero_suivi_de (sub_pos p q))=(Pos (sub_un (xI z)));
        Rewrite H5; Auto with arith ]]
  | Intros H3; Exists xH; Rewrite H3; Split; [
      Simpl; Rewrite sub_pos_x_x; Auto with arith
    | Split; Auto with arith ]]
| Intros H1; Exists (xO p); Auto with arith
| Intros q H1 H2; Simpl in H2; Elim (H q); [
    Intros z H3; Elim H3;Intros H4 H5;Elim H5;Intros H6 H7; 
    Elim (ZL11 z); [
      Intros vZ; Exists xH; Split; [
        Change (Un_suivi_de (sub_neg p q))=(Pos xH); 
        Rewrite ZL10; [ Auto with arith | Apply ZLIS;Assumption | Rewrite <- vZ;Assumption ]
      | Split; [
          Simpl; Rewrite ZL12; Rewrite <- vZ; Rewrite H6; Trivial with arith
        | Auto with arith ]]
    | Exists (xI (sub_un z)); Elim H7;[
        Intros H8; Absurd z=xH;Assumption
      | Split; [
          Simpl;Rewrite H8; Trivial with arith
        | Split; [
            Change (xO (add_carry q (sub_un z)))=(xO p); Rewrite ZL15; [
              Rewrite H6;Trivial with arith
            | Assumption ]
          | Right; Change (Zero_suivi_de (sub_neg p q)) =
                           (Pos (sub_un (xI (sub_un z))));
            Rewrite H8; Auto with arith]]]]
  | Apply ZLIS; Assumption ]
| Intros q H1 H2; Simpl in H2; Elim (H q H2); Intros z H3; 
  Exists (xO z); Elim H3;Intros H4 H5;Elim H5;Intros H6 H7; Split; [
    Simpl; Rewrite H4;Auto with arith
  | Split; [
      Simpl;Rewrite H6;Auto with arith
    | Right; Change (Un_suivi_de (sub_neg p q))=(Pos (double_moins_un z));
      Elim (ZL11 z); [
        Simpl; Intros H8;Rewrite H8; Simpl;
        Cut (sub_neg p q)=Nul;[
          Intros H9;Rewrite H9;Auto with arith
        | Apply ZL10;[Assumption|Rewrite <- H8;Assumption]]
      | Intros H8;Elim H7; [
          Intros H9;Absurd z=xH;Auto with arith
        | Intros H9;Rewrite H9; Generalize H8 ;Elim z; Simpl; Auto with arith;
          Intros H10;Absurd xH=xH;Auto with arith ]]]]
| Intros H1; Exists (double_moins_un p); Split; [
    Auto with arith
  | Split; [
      Elim p;Simpl;Auto with arith; Intros q H2; Rewrite ZL12bis; Rewrite H2; Trivial with arith
    | Change (double_moins_un p)=xH \/ 
             (double_moins_deux p)=(Pos (sub_un (double_moins_un p))); 
      Case p;Simpl;Auto with arith ]]
| Intros p H1 H2;Simpl in H2; Discriminate H2
| Intros p H1 H2;Simpl in H2;Discriminate H2
| Intros H1;Simpl in H1;Discriminate H1 ].
Qed.

Lemma ZC1:
  (x,y:positive)(compare x y EGAL)=SUPERIEUR -> (compare y x EGAL)=INFERIEUR.
Proof.
Intros x y H;Apply convert_compare_INFERIEUR; 
Change (gt (convert x) (convert y));Apply compare_convert_SUPERIEUR;
Assumption.
Qed.

Lemma ZC2:
  (x,y:positive)(compare x y EGAL)=INFERIEUR -> (compare y x EGAL)=SUPERIEUR.
Proof.
Intros x y H;Apply convert_compare_SUPERIEUR;Unfold gt;
Apply compare_convert_INFERIEUR;Assumption.
Qed.

Lemma ZC3: (x,y:positive)(compare x y EGAL)=EGAL -> (compare y x EGAL)=EGAL.
Proof.
Intros x y H; Rewrite (compare_convert_EGAL x y H);
Apply convert_compare_EGAL.
Qed.

Definition Op := [r:relation]
 <relation>Cases r of
             EGAL => EGAL
           | INFERIEUR => SUPERIEUR
           | SUPERIEUR => INFERIEUR
           end.

Lemma ZC4: (x,y:positive) (compare x y EGAL) = (Op (compare y x EGAL)).
Proof.
(((Intros x y;Elim (Dcompare (compare y x EGAL));[Idtac | Intros H;Elim H]);
Intros E;Rewrite E;Simpl); [Apply ZC3 | Apply ZC2 | Apply ZC1 ]); Assumption.
Qed.

Theorem add_sym : (x,y:positive) (add x y) = (add y x).
Proof.
Induction x;Induction y;Simpl;Auto with arith; Intros q H1; [
  Clear  H1; Do 2 Rewrite ZL13; Rewrite H;Auto with arith
| Rewrite H;Auto with arith | Rewrite H;Auto with arith | Rewrite H;Auto with arith ].
Qed. 

Lemma bij3: (x:positive)(sub_un (anti_convert (convert x))) = x.
Proof.
Intros x; Rewrite bij2; Rewrite sub_add_one; Trivial with arith.
Qed.

Lemma convert_intro : (x,y:positive)(convert x)=(convert y) -> x=y.
Proof.
Intros x y H;Rewrite <- (bij3 x);Rewrite <- (bij3 y); Rewrite H; Trivial with arith.
Qed.

Lemma simpl_add_r : (x,y,z:positive) (add x z)=(add y z) -> x=y.
Proof.
Intros x y z H;Apply convert_intro;
Apply (simpl_plus_l (convert z)); Do 2 Rewrite (plus_sym (convert z)); 
Do 2 Rewrite <- convert_add; Rewrite H; Trivial with arith.
Qed.

Lemma simpl_add_l : (x,y,z:positive) (add x y)=(add x z) -> y=z.
Proof.
Intros x y z H;Apply convert_intro;
Apply (simpl_plus_l (convert x)); Do 2 Rewrite <- convert_add; 
Rewrite H; Trivial with arith.
Qed.

Theorem add_assoc: (x,y,z:positive)(add x (add y z)) = (add (add x y) z).
Proof.
Intros x y z; Apply convert_intro; Do 4 Rewrite convert_add; 
Apply plus_assoc_l.
Qed.

Local true_sub := [x,y:positive] 
  <positive> Cases (sub_pos x y) of Nul => xH | (Pos z) => z end.
Proof.
Theorem sub_add: 
(x,y:positive) (compare x y EGAL) = SUPERIEUR -> (add y (true_sub x y)) = x.

Intros x y H;Elim sub_pos_SUPERIEUR with 1:=H;
Intros z H1;Elim H1;Intros H2 H3; Elim H3;Intros H4 H5; 
Unfold true_sub ;Rewrite H2; Exact H4.
Qed.
 
Theorem true_sub_convert:
  (x,y:positive) (compare x y EGAL) = SUPERIEUR -> 
     (convert (true_sub x y)) = (minus (convert x) (convert y)).
Proof.
Intros x y H; Apply (simpl_plus_l (convert y));
Rewrite le_plus_minus_r; [
  Rewrite <- convert_add; Rewrite sub_add; Auto with arith
| Apply lt_le_weak; Exact (compare_convert_SUPERIEUR x y H)].
Qed.

(** Addition on integers *)
Definition Zplus := [x,y:Z]
  <Z>Cases x of
      ZERO => y
    | (POS x') =>
          <Z>Cases y of
               ZERO => x
             | (POS y') => (POS (add x' y'))
             | (NEG y') =>
                   <Z>Cases (compare x' y' EGAL) of
                        EGAL => ZERO
                      | INFERIEUR => (NEG (true_sub y' x'))
                      | SUPERIEUR => (POS (true_sub x' y'))
                      end
             end
    | (NEG x') =>
          <Z>Cases y of
               ZERO => x
             | (POS y') =>
                   <Z>Cases (compare x' y' EGAL) of
                        EGAL => ZERO
                      | INFERIEUR => (POS (true_sub y' x'))
                      | SUPERIEUR => (NEG (true_sub x' y'))
                      end
             | (NEG y') => (NEG (add x' y'))
             end
    end.

(** Opposite *)

Definition Zopp := [x:Z]
 <Z>Cases x of
      ZERO => ZERO
    | (POS x) => (NEG x)
    | (NEG x) => (POS x)
    end.

Theorem Zero_left: (x:Z) (Zplus ZERO x) = x.
Proof.
Induction x; Auto with arith.
Qed.

Theorem Zopp_Zopp: (x:Z) (Zopp (Zopp x)) = x.
Proof.
Induction x; Auto with arith.
Qed.

(** Addition and opposite *)
Theorem Zero_right: (x:Z) (Zplus x ZERO) = x.
Proof.
Induction x; Auto with arith.
Qed.

Theorem Zplus_inverse_r: (x:Z) (Zplus x (Zopp x)) = ZERO.
Proof.
Induction x; [
  Simpl;Auto with arith
| Simpl; Intros p;Rewrite (convert_compare_EGAL p); Auto with arith
| Simpl; Intros p;Rewrite (convert_compare_EGAL p); Auto with arith ].
Qed.

Theorem Zopp_Zplus: 
  (x,y:Z) (Zopp (Zplus x y)) = (Zplus (Zopp x) (Zopp y)).
Proof.
(Intros x y;Case x;Case y;Auto with arith);
Intros p q;Simpl;Case (compare q p EGAL);Auto with arith.
Qed.

Theorem Zplus_sym: (x,y:Z) (Zplus x y) = (Zplus y x).
Proof.
Induction x;Induction y;Simpl;Auto with arith; [
  Intros q;Rewrite add_sym;Auto with arith
| Intros q; Rewrite (ZC4 q p);
  (Elim (Dcompare (compare p q EGAL));[Idtac|Intros H;Elim H]);
  Intros E;Rewrite E;Auto with arith
| Intros q; Rewrite (ZC4 q p);
  (Elim (Dcompare (compare p q EGAL));[Idtac|Intros H;Elim H]);
  Intros E;Rewrite E;Auto with arith
| Intros q;Rewrite add_sym;Auto with arith ].
Qed.

Theorem Zplus_inverse_l: (x:Z) (Zplus (Zopp x) x) = ZERO.
Proof.
Intro; Rewrite Zplus_sym; Apply Zplus_inverse_r.
Qed.

Theorem Zopp_intro : (x,y:Z) (Zopp x) = (Zopp y) -> x = y.
Proof.
Intros x y;Case x;Case y;Simpl;Intros; [
  Trivial with arith | Discriminate H | Discriminate H | Discriminate H
| Simplify_eq H; Intro E; Rewrite E; Trivial with arith
| Discriminate H | Discriminate H | Discriminate H
| Simplify_eq H; Intro E; Rewrite E; Trivial with arith ].
Qed.

Theorem Zopp_NEG : (x:positive) (Zopp (NEG x)) = (POS x).
Proof.
Induction x; Auto with arith.
Qed.

Hints Resolve Zero_left Zero_right.

Theorem weak_assoc :
  (x,y:positive)(z:Z) (Zplus (POS x) (Zplus (POS y) z))=
                       (Zplus (Zplus (POS x) (POS y)) z).
Proof.
Intros x y z';Case z'; [
  Auto with arith
| Intros z;Simpl; Rewrite add_assoc;Auto with arith
| Intros z; Simpl;
  (Elim (Dcompare (compare y z EGAL));[Idtac|Intros H;Elim H;Clear  H]);
  Intros E0;Rewrite E0;
  (Elim (Dcompare (compare (add x y) z EGAL));[Idtac|Intros H;Elim H;
    Clear H]);Intros E1;Rewrite E1; [
    Absurd (compare (add x y) z EGAL)=EGAL; [    (* Cas 1 *)
      Rewrite convert_compare_SUPERIEUR; [
        Discriminate
      | Rewrite convert_add; Rewrite (compare_convert_EGAL y z E0);
        Elim (ZL4 x);Intros k E2;Rewrite E2; Simpl; Unfold gt lt; Apply le_n_S;
        Apply le_plus_r ]
    | Assumption ]
  | Absurd (compare (add x y) z EGAL)=INFERIEUR; [ (* Cas 2 *)
      Rewrite convert_compare_SUPERIEUR; [
        Discriminate
      | Rewrite convert_add; Rewrite (compare_convert_EGAL y z E0);
        Elim (ZL4 x);Intros k E2;Rewrite E2; Simpl; Unfold gt lt; Apply le_n_S;
        Apply le_plus_r]
    | Assumption ]
  | Rewrite (compare_convert_EGAL y z E0); (* Cas 3 *)
    Elim (sub_pos_SUPERIEUR (add x z) z);[
      Intros t H; Elim H;Intros H1 H2;Elim H2;Intros H3 H4;
      Unfold true_sub; Rewrite H1; Cut x=t; [
        Intros E;Rewrite E;Auto with arith
      | Apply simpl_add_r with z:=z; Rewrite <- H3; Rewrite add_sym; Trivial with arith ]
    | Pattern 1 z; Rewrite <- (compare_convert_EGAL y z E0); Assumption ]
  | Elim (sub_pos_SUPERIEUR z y); [ (* Cas 4 *)
      Intros k H;Elim H;Intros H1 H2;Elim H2;Intros H3 H4; Unfold 1 true_sub;
      Rewrite H1; Cut x=k; [
        Intros E;Rewrite E; Rewrite (convert_compare_EGAL k); Trivial with arith
      | Apply simpl_add_r with z:=y; Rewrite (add_sym k y); Rewrite H3;
        Apply compare_convert_EGAL; Assumption ]
    | Apply ZC2;Assumption]
  | Elim (sub_pos_SUPERIEUR z y); [ (* Cas 5 *)
      Intros k H;Elim H;Intros H1 H2;Elim H2;Intros H3 H4;
      Unfold 1 3 5 true_sub; Rewrite H1;
      Cut (compare x k EGAL)=INFERIEUR; [
        Intros E2;Rewrite E2; Elim (sub_pos_SUPERIEUR k x); [
          Intros i H5;Elim H5;Intros H6 H7;Elim H7;Intros H8 H9;
          Elim (sub_pos_SUPERIEUR z (add x y)); [
            Intros j H10;Elim H10;Intros H11 H12;Elim H12;Intros H13 H14;
            Unfold true_sub ;Rewrite H6;Rewrite H11; Cut i=j; [
              Intros E;Rewrite E;Auto with arith
            | Apply (simpl_add_l (add x y)); Rewrite H13; 
              Rewrite (add_sym x y); Rewrite <- add_assoc; Rewrite H8;
              Assumption ]
          | Apply ZC2; Assumption]
        | Apply ZC2;Assumption]
      | Apply convert_compare_INFERIEUR;
        Apply simpl_lt_plus_l with p:=(convert y);
        Do 2 Rewrite <- convert_add; Apply compare_convert_INFERIEUR;
        Rewrite H3; Rewrite add_sym; Assumption ]
    | Apply ZC2; Assumption ]
  | Elim (sub_pos_SUPERIEUR z y); [ (* Cas 6 *)
      Intros k H;Elim H;Intros H1 H2;Elim H2;Intros H3 H4;
      Elim (sub_pos_SUPERIEUR (add x y) z); [
        Intros i H5;Elim H5;Intros H6 H7;Elim H7;Intros H8 H9;
        Unfold true_sub; Rewrite H1;Rewrite H6;
        Cut (compare x k EGAL)=SUPERIEUR; [
          Intros H10;Elim (sub_pos_SUPERIEUR x k H10);
          Intros j H11;Elim H11;Intros H12 H13;Elim H13;Intros H14 H15;
          Rewrite H10; Rewrite H12; Cut i=j; [
            Intros H16;Rewrite H16;Auto with arith
          | Apply (simpl_add_l (add z k)); Rewrite <- (add_assoc z k j);
            Rewrite H14; Rewrite (add_sym z k); Rewrite <- add_assoc;
            Rewrite H8; Rewrite (add_sym x y); Rewrite add_assoc;
            Rewrite (add_sym k y); Rewrite H3; Trivial with arith]
        | Apply convert_compare_SUPERIEUR; Unfold lt gt;
          Apply simpl_lt_plus_l with p:=(convert y);
          Do 2 Rewrite <- convert_add; Apply compare_convert_INFERIEUR;
          Rewrite H3; Rewrite add_sym; Apply ZC1; Assumption ]
      | Assumption ]
    | Apply ZC2;Assumption ]
  | Absurd (compare (add x y) z EGAL)=EGAL; [ (* Cas 7 *)
      Rewrite convert_compare_SUPERIEUR; [
        Discriminate
      | Rewrite convert_add; Unfold gt;Apply lt_le_trans with m:=(convert y);[
          Apply compare_convert_INFERIEUR; Apply ZC1; Assumption
        | Apply le_plus_r]]
    | Assumption ]
  | Absurd (compare (add x y) z EGAL)=INFERIEUR; [ (* Cas 8 *)
      Rewrite convert_compare_SUPERIEUR; [
        Discriminate
      | Unfold gt; Apply lt_le_trans with m:=(convert y);[
          Exact (compare_convert_SUPERIEUR y z E0)
        | Rewrite convert_add; Apply le_plus_r]]
    | Assumption ]
  | Elim sub_pos_SUPERIEUR with 1:=E0;Intros k H1; (* Cas 9 *)
    Elim sub_pos_SUPERIEUR with 1:=E1; Intros i H2;Elim H1;Intros H3 H4;
    Elim H4;Intros H5 H6; Elim H2;Intros H7 H8;Elim H8;Intros H9 H10; 
    Unfold true_sub ;Rewrite H3;Rewrite H7; Cut (add x k)=i; [
      Intros E;Rewrite E;Auto with arith
    | Apply (simpl_add_l z);Rewrite (add_sym x k);
      Rewrite add_assoc; Rewrite H5;Rewrite H9;
      Rewrite add_sym; Trivial with arith ]]].
Qed.

Hints Resolve weak_assoc.

Theorem Zplus_assoc :
  (x,y,z:Z) (Zplus x (Zplus y z))= (Zplus (Zplus x y) z).
Proof.
Intros x y z;Case x;Case y;Case z;Auto with arith; Intros; [
(*i  Apply weak_assoc
| Apply weak_assoc 
| i*) Rewrite (Zplus_sym (NEG p0)); Rewrite weak_assoc;
  Rewrite (Zplus_sym (Zplus (POS p1) (NEG p0))); Rewrite weak_assoc;
  Rewrite (Zplus_sym (POS p1)); Trivial with arith
| Apply Zopp_intro; Do 4 Rewrite Zopp_Zplus; 
  Do 2 Rewrite Zopp_NEG; Rewrite Zplus_sym; Rewrite <- weak_assoc;
  Rewrite (Zplus_sym (Zopp (POS p1)));
  Rewrite (Zplus_sym (Zplus (POS p0) (Zopp (POS p1))));
  Rewrite (weak_assoc p); Rewrite weak_assoc; Rewrite (Zplus_sym (POS p0)); 
  Trivial with arith
| Rewrite Zplus_sym; Rewrite (Zplus_sym (POS p0) (POS p));
  Rewrite <- weak_assoc; Rewrite Zplus_sym; Rewrite (Zplus_sym (POS p0));
  Trivial with arith
| Apply Zopp_intro; Do 4 Rewrite Zopp_Zplus; 
  Do 2 Rewrite Zopp_NEG; Rewrite (Zplus_sym (Zopp (POS p0)));
  Rewrite weak_assoc; Rewrite (Zplus_sym (Zplus (POS p1) (Zopp (POS p0))));
  Rewrite weak_assoc;Rewrite (Zplus_sym (POS p)); Trivial with arith
| Apply Zopp_intro; Do 4 Rewrite Zopp_Zplus; Do 2 Rewrite Zopp_NEG;
  Apply weak_assoc
| Apply Zopp_intro; Do 4 Rewrite Zopp_Zplus; Do 2 Rewrite Zopp_NEG;
   Apply weak_assoc]
.
Qed.

Lemma Zplus_simpl : (n,m,p,q:Z) n=m -> p=q -> (Zplus n p)=(Zplus m q).
Proof.
Intros; Elim H; Elim H0; Auto with arith.
Qed.

(** Addition on positive numbers *)

Fixpoint times [x:positive] : positive -> positive:=
  [y:positive]
  Cases x of
    (xI x') => (add y (xO (times x' y)))
  | (xO x') => (xO (times x' y))
  | xH => y
  end.

Infix LEFTA 3 "*" times : positive_scope.

(** Correctness of multiplication on positive *)
Theorem times_convert :
  (x,y:positive) (convert x*y) = (mult (convert x) (convert y)).
Proof.
Intros x y; NewInduction x as [ x' H | x' H | ]; [
  Change (xI x')*y with (add y (xO x'*y)); Rewrite convert_add;
  Unfold 2 3 convert; Simpl; Do 2 Rewrite ZL6; Rewrite H;
  Rewrite -> mult_plus_distr; Reflexivity
| Unfold 1 2 convert; Simpl; Do 2 Rewrite ZL6;
  Rewrite H; Rewrite mult_plus_distr; Reflexivity
| Simpl; Rewrite <- plus_n_O; Reflexivity ].
Qed.

Theorem times_assoc :
  ((x,y,z:positive) (times x (times y z))= (times (times x y) z)).
Proof.
Intros x y z;Apply convert_intro; Do 4 Rewrite times_convert;
Apply mult_assoc_l.
Qed.

Theorem times_sym : (x,y:positive) (times x y) = (times y x).
Proof.
Intros x y; Apply convert_intro; Do 2 Rewrite times_convert; Apply mult_sym.
Qed.

(** Multiplication on integers *)
Definition Zmult := [x,y:Z]
  <Z>Cases x of
      ZERO => ZERO
    | (POS x') =>
          <Z>Cases y of
               ZERO => ZERO
             | (POS y') => (POS (times x' y'))
             | (NEG y') => (NEG (times x' y'))
             end
    | (NEG x') =>
          <Z>Cases y of
               ZERO => ZERO
             | (POS y') => (NEG (times x' y'))
             | (NEG y') => (POS (times x' y'))
             end
    end.

Infix LEFTA 3 "*" Zmult : Z_scope.

Open Scope Z_scope.

Theorem Zmult_sym : (x,y:Z) (Zmult x y) = (Zmult y x).
Proof.
Induction x; Induction y; Simpl; Auto with arith; Intro q; Rewrite (times_sym p q); Auto with arith.
Qed.

Theorem Zmult_assoc :
  (x,y,z:Z) (Zmult x (Zmult y z))= (Zmult (Zmult x y) z).
Proof.
Induction x; Induction y; Induction z; Simpl; Auto with arith; Intro p1; 
Rewrite times_assoc; Auto with arith.
Qed.

Theorem Zmult_one:
  (x:Z) (Zmult (POS xH) x) = x.
Proof.
Induction x; Simpl; Unfold times; Auto with arith.
Qed.

Theorem times_add_distr:
  (x,y,z:positive) (times x (add y z)) = (add (times x y) (times x z)).
Proof.
Intros x y z;Apply convert_intro;Rewrite times_convert;
Do 2 Rewrite convert_add; Do 2 Rewrite times_convert;
Do 3 Rewrite (mult_sym (convert x)); Apply mult_plus_distr.
Qed.

Theorem lt_mult_left :
 (x,y,z:nat) (lt x y) -> (lt (mult (S z) x) (mult (S z) y)).
Proof.
Intros x y z H;Elim z; [
  Simpl; Do 2 Rewrite <- plus_n_O; Assumption
| Simpl; Intros n H1; Apply lt_trans with m:=(plus y (plus x (mult n x))); [
    Rewrite (plus_sym x (plus x (mult n x)));
    Rewrite (plus_sym y (plus x (mult n x))); Apply lt_reg_l; Assumption
  | Apply lt_reg_l;Assumption ]].
Qed.

Theorem times_true_sub_distr:
  (x,y,z:positive) (compare y z EGAL) = SUPERIEUR -> 
      (times x (true_sub y z)) = (true_sub (times x y) (times x z)).
Proof.
Intros x y z H; Apply convert_intro;
Rewrite times_convert; Rewrite true_sub_convert; [
  Rewrite true_sub_convert; [
    Do 2 Rewrite times_convert;
    Do 3 Rewrite (mult_sym (convert x));Apply mult_minus_distr
  | Apply convert_compare_SUPERIEUR; Do 2 Rewrite times_convert; 
    Unfold gt; Elim (ZL4 x);Intros h H1;Rewrite H1; Apply lt_mult_left;
    Exact (compare_convert_SUPERIEUR y z H) ]
| Assumption ].
Qed.

Theorem Zero_mult_left: (x:Z) (Zmult ZERO x) = ZERO.
Proof.
Induction x; Auto with arith.
Qed.

Theorem Zero_mult_right: (x:Z) (Zmult x ZERO) = ZERO.
Proof.
Induction x; Auto with arith.
Qed.

Hints Resolve Zero_mult_left Zero_mult_right.

(* Multiplication and Opposite *)
Theorem Zopp_Zmult:
  (x,y:Z) (Zmult (Zopp x) y) = (Zopp (Zmult x y)).
Proof.
Intros x y; Case x; Case y; Simpl; Auto with arith.
Qed.

Theorem Zmult_Zopp_Zopp:
  (x,y:Z) (Zmult (Zopp x) (Zopp y)) = (Zmult x y).
Proof.
NewDestruct x; NewDestruct y; Reflexivity.
Qed.

Theorem weak_Zmult_plus_distr_r:
  (x:positive)(y,z:Z)
   (Zmult (POS x) (Zplus y z)) = (Zplus (Zmult (POS x) y) (Zmult (POS x) z)).
Proof.
Intros x y' z';Case y';Case z';Auto with arith;Intros y z;
  (Simpl; Rewrite times_add_distr; Trivial with arith)
Orelse
  (Simpl; (Elim (Dcompare (compare z y EGAL));[Idtac|Intros H;Elim H;
   Clear  H]);Intros E0;Rewrite E0; [
    Rewrite (compare_convert_EGAL z y E0);
    Rewrite (convert_compare_EGAL (times x y)); Trivial with arith
  | Cut (compare (times x z) (times x y) EGAL)=INFERIEUR; [
      Intros E;Rewrite E; Rewrite times_true_sub_distr; [
        Trivial with arith
      | Apply ZC2;Assumption ]
    | Apply convert_compare_INFERIEUR;Do 2 Rewrite times_convert; 
      Elim (ZL4 x);Intros h H1;Rewrite H1;Apply lt_mult_left;
      Exact (compare_convert_INFERIEUR z y E0)]
  | Cut (compare (times x z) (times x y) EGAL)=SUPERIEUR; [
      Intros E;Rewrite E; Rewrite times_true_sub_distr; Auto with arith
    | Apply convert_compare_SUPERIEUR; Unfold gt; Do 2 Rewrite times_convert;
      Elim (ZL4 x);Intros h H1;Rewrite H1;Apply lt_mult_left;
      Exact (compare_convert_SUPERIEUR z y E0) ]]).
Qed.

Theorem Zmult_plus_distr_r:
  (x,y,z:Z) (Zmult x (Zplus y z)) = (Zplus (Zmult x y) (Zmult x z)).
Proof.
Intros x y z; Case x; [
  Auto with arith
| Intros x';Apply weak_Zmult_plus_distr_r
| Intros p; Apply Zopp_intro; Rewrite Zopp_Zplus; 
  Do 3 Rewrite <- Zopp_Zmult; Rewrite Zopp_NEG; 
  Apply weak_Zmult_plus_distr_r ].
Qed.

(** Comparison on integers *)
Definition Zcompare := [x,y:Z]
  <relation>Cases x of
      ZERO => <relation>Cases y of
                ZERO => EGAL
              | (POS y') => INFERIEUR
              | (NEG y') => SUPERIEUR
              end
   | (POS x') => <relation>Cases y of
                ZERO => SUPERIEUR
              | (POS y') => (compare x' y' EGAL)
              | (NEG y') => SUPERIEUR
              end
   | (NEG x') => <relation>Cases y of
               ZERO => INFERIEUR
             | (POS y') => INFERIEUR
             | (NEG y') => (Op (compare x' y' EGAL))
             end
  end.

Theorem Zcompare_EGAL : (x,y:Z) (Zcompare x y) = EGAL <-> x = y.
Proof.
Intros x y;Split; [
  Case x;Case y;Simpl;Auto with arith; Try (Intros;Discriminate H); [
    Intros x' y' H; Rewrite (compare_convert_EGAL y' x' H); Trivial with arith
  | Intros x' y' H; Rewrite (compare_convert_EGAL y' x'); [
      Trivial with arith
    | Generalize H; Case (compare y' x' EGAL);
      Trivial with arith Orelse (Intros C;Discriminate C)]]
| Intros E;Rewrite E; Case y; [
    Trivial with arith
  | Simpl;Exact convert_compare_EGAL
  | Simpl; Intros p;Rewrite convert_compare_EGAL;Auto with arith ]].
Qed.

Theorem Zcompare_ANTISYM : 
  (x,y:Z) (Zcompare x y) = SUPERIEUR <->  (Zcompare y x) = INFERIEUR.
Proof.
Intros x y;Split; [
  Case x;Case y;Simpl;Intros;(Trivial with arith Orelse Discriminate H Orelse
    (Apply ZC1; Assumption) Orelse
    (Cut (compare p p0 EGAL)=SUPERIEUR; [
       Intros H1;Rewrite H1;Auto with arith
     | Apply ZC2; Generalize H ; Case (compare p0 p EGAL);
       Trivial with arith Orelse (Intros H2;Discriminate H2)]))
| Case x;Case y;Simpl;Intros;(Trivial with arith Orelse Discriminate H Orelse
    (Apply ZC2; Assumption) Orelse
    (Cut (compare p0 p EGAL)=INFERIEUR; [
       Intros H1;Rewrite H1;Auto with arith
     | Apply ZC1; Generalize H ; Case (compare p p0 EGAL);
       Trivial with arith Orelse (Intros H2;Discriminate H2)]))].
Qed.

Theorem le_minus: (i,h:nat) (le (minus i h) i).
Proof.
Intros i h;Pattern i h; Apply nat_double_ind; [
  Auto with arith
| Auto with arith
| Intros m n H; Simpl; Apply le_trans with m:=m; Auto with arith ].
Qed.

Lemma ZL16: (p,q:positive)(lt (minus (convert p) (convert q)) (convert p)).
Proof.
Intros p q; Elim (ZL4 p);Elim (ZL4 q); Intros h H1 i H2; 
Rewrite H1;Rewrite H2; Simpl;Unfold lt; Apply le_n_S; Apply le_minus.
Qed.
 
Lemma ZL17: (p,q:positive)(lt (convert p) (convert (add p q))).
Proof.
Intros p q; Rewrite convert_add;Unfold lt;Elim (ZL4 q); Intros k H;Rewrite H;
Rewrite plus_sym;Simpl; Apply le_n_S; Apply le_plus_r.
Qed.

Theorem Zcompare_Zopp :
  (x,y:Z) (Zcompare x y) = (Zcompare (Zopp y) (Zopp x)).
Proof.
(Intros x y;Case x;Case y;Simpl;Auto with arith);
Intros;Rewrite <- ZC4;Trivial with arith.
Qed.

Hints Resolve convert_compare_EGAL.

Theorem weaken_Zcompare_Zplus_compatible : 
  ((x,y:Z) (z:positive) 
    (Zcompare (Zplus (POS z) x) (Zplus (POS z) y)) = (Zcompare x y)) ->
   (x,y,z:Z) (Zcompare (Zplus z x) (Zplus z y)) = (Zcompare x y).
Proof.
(Intros H x y z;Case x;Case y;Case z;Auto with arith;
Try (Intros; Rewrite Zcompare_Zopp; Do 2 Rewrite Zopp_Zplus;
     Rewrite Zopp_NEG; Rewrite H; Simpl; Auto with arith));
Try (Intros; Simpl; Rewrite <- ZC4; Auto with arith).
Qed.

Hints Resolve ZC4.

Theorem weak_Zcompare_Zplus_compatible : 
  (x,y:Z) (z:positive) 
    (Zcompare (Zplus (POS z) x) (Zplus (POS z) y)) = (Zcompare x y).
Proof.
Intros x y z;Case x;Case y;Simpl;Auto with arith; [
  Intros p;Apply convert_compare_INFERIEUR; Apply ZL17
| Intros p;(Elim (Dcompare(compare z p EGAL));[Idtac|Intros H;Elim H;
  Clear H]);Intros E;Rewrite E;Auto with arith;
  Apply convert_compare_SUPERIEUR; Rewrite true_sub_convert; [ Unfold gt ;
  Apply ZL16 | Assumption ]
| Intros p;(Elim (Dcompare(compare z p EGAL));[Idtac|Intros H;Elim H;
  Clear H]);Intros E;Auto with arith; Apply convert_compare_SUPERIEUR;
  Unfold gt;Apply ZL17
| Intros p q;
  (Elim (Dcompare (compare q p EGAL));[Idtac|Intros H;Elim H;Clear  H]);
  Intros E;Rewrite E;[
    Rewrite (compare_convert_EGAL q p E); Apply convert_compare_EGAL
  | Apply convert_compare_INFERIEUR;Do 2 Rewrite convert_add;Apply lt_reg_l;
    Apply compare_convert_INFERIEUR with 1:=E
  | Apply convert_compare_SUPERIEUR;Unfold gt ;Do 2 Rewrite convert_add;
    Apply lt_reg_l;Exact (compare_convert_SUPERIEUR q p E) ]
| Intros p q; 
  (Elim (Dcompare (compare z p EGAL));[Idtac|Intros H;Elim H;Clear  H]);
  Intros E;Rewrite E;Auto with arith;
  Apply convert_compare_SUPERIEUR; Rewrite true_sub_convert; [
    Unfold gt; Apply lt_trans with m:=(convert z); [Apply ZL16 | Apply ZL17]
  | Assumption ]
| Intros p;(Elim (Dcompare(compare z p EGAL));[Idtac|Intros H;Elim H;
  Clear H]);Intros E;Rewrite E;Auto with arith; Simpl;
  Apply convert_compare_INFERIEUR;Rewrite true_sub_convert;[Apply ZL16|
  Assumption]
| Intros p q;
  (Elim (Dcompare (compare z q EGAL));[Idtac|Intros H;Elim H;Clear  H]);
  Intros E;Rewrite E;Auto with arith; Simpl;Apply convert_compare_INFERIEUR;
  Rewrite true_sub_convert;[
    Apply lt_trans with m:=(convert z) ;[Apply ZL16|Apply ZL17]
  | Assumption]
| Intros p q;
  (Elim (Dcompare (compare z q EGAL));[Idtac|Intros H;Elim H;Clear  H]);
  Intros E0;Rewrite E0;
  (Elim (Dcompare (compare z p EGAL));[Idtac|Intros H;Elim H;Clear  H]);
  Intros E1;Rewrite E1;
  (Elim (Dcompare (compare q p EGAL));[Idtac|Intros H;Elim H;Clear  H]);
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

Theorem Zcompare_Zplus_compatible : 
   (x,y,z:Z) (Zcompare (Zplus z x) (Zplus z y)) = (Zcompare x y).
Proof.
Exact (weaken_Zcompare_Zplus_compatible weak_Zcompare_Zplus_compatible).
Qed.

Theorem Zcompare_trans_SUPERIEUR : 
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
End fast_integers.

V7only [
  Comments "Compatibility with the old version of times and times_convert".
  Syntactic Definition times1 :=
    [x:positive;_:positive->positive;y:positive](times x y).
  Syntactic Definition times1_convert :=
    [x,y:positive;_:positive->positive](times_convert x y).
].
