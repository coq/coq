(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(***********************************************************)
(** Binary Integers (Pierre Crégut, CNET, Lannion, France) *)
(***********************************************************)

(**********************************************************************)
(** Binary positive numbers *)

Inductive positive : Set :=
  xI : positive -> positive
| xO : positive -> positive
| xH : positive.

(* Declare Scope positive_scope with Key P *)
Delimits Scope positive_scope with P.

(* Automatically open scope positive_scope for type positive, xO and xI *)
Bind Scope positive_scope with positive.
Arguments Scope xO [ positive_scope ].
Arguments Scope xI [ positive_scope ].

(** Successor *)

Fixpoint add_un [x:positive]:positive :=
  Cases x of
    (xI x') => (xO (add_un x'))
  | (xO x') => (xI x')
  | xH => (xO xH)
  end.

(** Addition *)

Fixpoint add [x:positive]:positive -> positive := [y:positive]
  Cases x y of
  | (xI x') (xI y') => (xO (add_carry x' y'))
  | (xI x') (xO y') => (xI (add x' y'))
  | (xI x') xH      => (xO (add_un x'))
  | (xO x') (xI y') => (xI (add x' y'))
  | (xO x') (xO y') => (xO (add x' y'))
  | (xO x') xH      => (xI x')
  | xH      (xI y') => (xO (add_un y'))
  | xH      (xO y') => (xI y')
  | xH      xH      => (xO xH)
  end
with add_carry [x:positive]:positive -> positive := [y:positive]
  Cases x y of
  | (xI x') (xI y') => (xI (add_carry x' y'))
  | (xI x') (xO y') => (xO (add_carry x' y'))
  | (xI x') xH      => (xI (add_un x'))
  | (xO x') (xI y') => (xO (add_carry x' y'))
  | (xO x') (xO y') => (xI (add x' y'))
  | (xO x') xH      => (xO (add_un x'))
  | xH      (xI y') => (xI (add_un y'))
  | xH      (xO y') => (xO (add_un y'))
  | xH      xH      => (xI xH)
  end.

V7only [Notation "x + y" := (add x y) : positive_scope.].
V8Infix "+" add : positive_scope.

Open Local Scope positive_scope.

(** From binary positive numbers to Peano natural numbers *)

Fixpoint positive_to_nat [x:positive]:nat -> nat :=
  [pow2:nat]
    <nat> Cases x of
     (xI x') => (plus pow2 (positive_to_nat x' (plus pow2 pow2)))
   | (xO x') => (positive_to_nat x' (plus pow2 pow2))
   | xH      => pow2
   end.

Definition convert := [x:positive] (positive_to_nat x (S O)).

(** From Peano natural numbers to binary positive numbers *)

Fixpoint anti_convert [n:nat]: positive :=
   Cases n of
                O => xH
             | (S x') => (add_un (anti_convert x'))
             end.

(** Subtraction *)

Fixpoint double_moins_un [x:positive]:positive :=
  Cases x of
      (xI x') => (xI (xO x'))
    | (xO x') => (xI (double_moins_un x'))
    | xH => xH
    end.

(** Predecessor *)

Definition sub_un := [x:positive]
   Cases x of
             (xI x') => (xO x')
           | (xO x') => (double_moins_un x')
           | xH => xH
           end.

(** An auxiliary type for subtraction *)

Inductive positive_mask: Set :=
   IsNul : positive_mask
 | IsPos : positive -> positive_mask
 | IsNeg : positive_mask.

(** Operation x -> 2*x+1 *)

Definition Un_suivi_de_mask := [x:positive_mask]
  Cases x of IsNul => (IsPos xH) | IsNeg => IsNeg | (IsPos p) => (IsPos (xI p)) end.

(** Operation x -> 2*x *)

Definition Zero_suivi_de_mask := [x:positive_mask]
  Cases x of IsNul => IsNul | IsNeg => IsNeg | (IsPos p) => (IsPos (xO p)) end.

(** Operation x -> 2*x-2 *)

Definition double_moins_deux :=
  [x:positive] Cases x of
           (xI x') => (IsPos (xO (xO x')))
         | (xO x') => (IsPos (xO (double_moins_un x')))
         | xH => IsNul
         end.

(** Subtraction of binary positive numbers into a positive numbers mask *)

Fixpoint sub_pos[x,y:positive]:positive_mask :=
  Cases x y of
  | (xI x') (xI y') => (Zero_suivi_de_mask (sub_pos x' y'))
  | (xI x') (xO y') => (Un_suivi_de_mask (sub_pos x' y'))
  | (xI x') xH      => (IsPos (xO x'))
  | (xO x') (xI y') => (Un_suivi_de_mask (sub_neg x' y'))
  | (xO x') (xO y') => (Zero_suivi_de_mask (sub_pos x' y'))
  | (xO x') xH      => (IsPos (double_moins_un x'))
  | xH      xH      => IsNul
  | xH      _       => IsNeg
  end
with sub_neg [x,y:positive]:positive_mask :=
  Cases x y of
    (xI x') (xI y') => (Un_suivi_de_mask (sub_neg x' y'))
  | (xI x') (xO y') => (Zero_suivi_de_mask (sub_pos x' y'))
  | (xI x') xH      => (IsPos (double_moins_un x'))
  | (xO x') (xI y') => (Zero_suivi_de_mask (sub_neg x' y'))
  | (xO x') (xO y') => (Un_suivi_de_mask (sub_neg x' y'))
  | (xO x') xH      => (double_moins_deux x')
  | xH      _       => IsNeg
  end.

(** Subtraction of binary positive numbers x and y, returns 1 if x<=y *)

Definition true_sub := [x,y:positive] 
  Cases (sub_pos x y) of (IsPos z) => z | _ => xH  end.

(** Multiplication on binary positive numbers *)

Fixpoint times [x:positive] : positive -> positive:=
  [y:positive]
  Cases x of
    (xI x') => (add y (xO (times x' y)))
  | (xO x') => (xO (times x' y))
  | xH => y
  end.

V8Infix "*" times : positive_scope.

(**********************************************************************)
(** Comparison on binary positive numbers *)

Fixpoint compare [x,y:positive]: relation -> relation :=
  [r:relation] 
  Cases x y of
  | (xI x') (xI y') => (compare x' y' r)
  | (xI x') (xO y') => (compare x' y' SUPERIEUR)
  | (xI x')  xH     => SUPERIEUR
  | (xO x') (xI y') => (compare x' y' INFERIEUR)
  | (xO x') (xO y') => (compare x' y' r)
  | (xO x')  xH     => SUPERIEUR
  | xH      (xI y') => INFERIEUR
  | xH      (xO y') => INFERIEUR
  | xH       xH     => r
  end.

Theorem compare_convert1 : 
 (x,y:positive) 
  ~(compare x y SUPERIEUR) = EGAL /\ ~(compare x y INFERIEUR) = EGAL.
Proof.
Induction x;Induction y;Split;Simpl;Auto;
  Discriminate Orelse (Elim (H p0); Auto).
Qed.

Theorem compare_convert_EGAL : (x,y:positive) (compare x y EGAL) = EGAL -> x=y.
Proof.
Induction x;Induction y;Simpl;Auto; [
  Intros z H1 H2; Rewrite (H z); Trivial
| Intros z H1 H2; Absurd (compare p z SUPERIEUR)=EGAL ;
   [ Elim (compare_convert1 p z);Auto | Assumption ]
| Intros H1;Discriminate H1
| Intros z H1 H2; Absurd (compare p z INFERIEUR) = EGAL; 
    [ Elim (compare_convert1 p z);Auto | Assumption ]
| Intros z H1 H2 ;Rewrite (H z);Auto 
| Intros H1;Discriminate H1
| Intros p H H1;Discriminate H1
| Intros p H H1;Discriminate H1 ].
Qed.

Lemma ZLSI:
 (x,y:positive) (compare x y SUPERIEUR) = INFERIEUR -> 
                (compare x y EGAL) = INFERIEUR.
Proof.
Induction x;Induction y;Simpl;Auto; 
  Discriminate Orelse Intros H;Discriminate H.
Qed.

Lemma ZLIS:
 (x,y:positive) (compare x y INFERIEUR) = SUPERIEUR -> 
                (compare x y EGAL) = SUPERIEUR.
Proof.
Induction x;Induction y;Simpl;Auto; 
  Discriminate Orelse Intros H;Discriminate H.
Qed.

Lemma ZLII:
 (x,y:positive) (compare x y INFERIEUR) = INFERIEUR ->
                (compare x y EGAL) = INFERIEUR \/ x = y.
Proof.
(Induction x;Induction y;Simpl;Auto;Try Discriminate);
 Intros z H1 H2; Elim (H z H2);Auto; Intros E;Rewrite E;
 Auto.
Qed.

Lemma ZLSS:
 (x,y:positive) (compare x y SUPERIEUR) = SUPERIEUR ->
                (compare x y EGAL) = SUPERIEUR \/ x = y.
Proof.
(Induction x;Induction y;Simpl;Auto;Try Discriminate);
 Intros z H1 H2; Elim (H z H2);Auto; Intros E;Rewrite E;
 Auto.
Qed.

Lemma Dcompare : (r:relation) r=EGAL \/ r = INFERIEUR \/ r = SUPERIEUR.
Proof.
Induction r; Auto. 
Qed.

Theorem convert_compare_EGAL: (x:positive)(compare x x EGAL)=EGAL.
Induction x; Auto.
Qed.

(**********************************************************************)
(** Miscellaneous properties of binary positive numbers *)

Lemma ZL11: (x:positive) (x=xH) \/ ~(x=xH).
Proof.
Intros x;Case x;Intros; (Left;Reflexivity) Orelse (Right;Discriminate).
Qed.

(**********************************************************************)
(** Properties of successor on binary positive numbers *)

(** Specification of [xI] in term of [Psucc] and [xO] *)

Lemma xI_add_un_xO : (p:positive)(xI p) = (add_un (xO p)).
Proof.
Reflexivity.
Qed.

(** Successor and double *)

Lemma is_double_moins_un : (x:positive) (add_un (double_moins_un x)) = (xO x).
Proof.
NewInduction x as [x IHx|x|]; Simpl; Try Rewrite IHx; Reflexivity.
Qed.

Lemma double_moins_un_add_un_xI : 
 (x:positive)(double_moins_un (add_un x))=(xI x).
Proof.
NewInduction x as [x IHx|x|]; Simpl; Try Rewrite IHx; Reflexivity.
Qed.

Lemma ZL1: (y:positive)(xO (add_un y)) = (add_un (add_un (xO y))).
Proof.
Induction y; Simpl; Auto.
Qed.

(** Successor and predecessor *)

Lemma add_un_not_un : (x:positive) (add_un x) <> xH.
Proof.
NewDestruct x as [x|x|]; Discriminate.
Qed.

Lemma sub_add_one : (x:positive) (sub_un (add_un x)) = x.
Proof.
(Induction x; [Idtac | Idtac | Simpl;Auto]);
(Intros p; Elim p; [Idtac | Idtac | Simpl;Auto]);
Simpl; Intros q H1 H2; Case H2; Simpl; Trivial.
Qed.

Lemma add_sub_one : (x:positive) (x=xH) \/ (add_un (sub_un x)) = x.
Proof.
Induction x; [
  Simpl; Auto
| Simpl; Intros;Right;Apply is_double_moins_un
| Auto ].
Qed.

(** Injectivity of successor *)

Lemma add_un_inj : (x,y:positive) (add_un x)=(add_un y) -> x=y.
Proof.
NewInduction x; NewDestruct y as [y|y|]; Simpl; 
  Intro H; Discriminate H Orelse Try (Injection H; Clear H; Intro H).
Rewrite (IHx y H); Reflexivity.
Absurd (add_un x)=xH; [ Apply add_un_not_un | Assumption ].
Apply f_equal with 1:=H; Assumption.
Absurd (add_un y)=xH; [ Apply add_un_not_un | Symmetry; Assumption ].
Reflexivity.
Qed.

(**********************************************************************)
(** Properties of addition on binary positive numbers *)

(** Specification of [Psucc] in term of [Pplus] *)

Lemma ZL12: (q:positive) (add_un q) = (add q xH).
Proof.
NewDestruct q; Reflexivity.
Qed.

Lemma ZL12bis: (q:positive) (add_un q) = (add xH q).
Proof.
NewDestruct q; Reflexivity.
Qed.

(** Specification of [Pplus_carry] *)

Theorem ZL13: (x,y:positive)(add_carry x y) = (add_un (add x y)).
Proof.
(Induction x;Induction y;Simpl;Auto); Intros q H1;Rewrite H;
 Auto.
Qed.

(** Commutativity *)

Theorem add_sym : (x,y:positive) (add x y) = (add y x).
Proof.
Induction x;Induction y;Simpl;Auto; Intros q H1; [
  Clear  H1; Do 2 Rewrite ZL13; Rewrite H;Auto
| Rewrite H;Auto | Rewrite H;Auto | Rewrite H;Auto ].
Qed. 

(** Permutation of [Pplus] and [Psucc] *)

Theorem ZL14: (x,y:positive)(add x (add_un y)) = (add_un (add x y)).
Proof.
Induction x;Induction y;Simpl;Auto; [
  Intros q H1; Rewrite ZL13; Rewrite  H; Auto
| Intros q H1; Rewrite ZL13; Auto
| Elim p;Simpl;Auto
| Intros q H1;Rewrite H;Auto
| Elim p;Simpl;Auto ].
Qed.

Theorem ZL14bis: (x,y:positive)(add (add_un x) y) = (add_un (add x y)).
Proof.
Intros x y; Rewrite add_sym; Rewrite add_sym with x:=x; Apply ZL14.
Qed.

Theorem ZL15: (q,z:positive) ~z=xH -> (add_carry q (sub_un z)) = (add q z).
Proof.
Intros q z H; Elim (add_sub_one z); [
  Intro;Absurd z=xH;Auto
| Intros E;Pattern 2 z ;Rewrite <- E; Rewrite ZL14; Rewrite ZL13; Trivial ].
Qed. 

(** No neutral for addition on strictly positive numbers *)

Lemma add_no_neutral : (x,y:positive) ~(add y x)=x.
Proof.
NewInduction x; NewDestruct y as [y|y|]; Simpl; Intro H;
  Discriminate H Orelse Injection H; Clear H; Intro H; Apply (IHx y H).
Qed.

Lemma add_carry_not_add_un : (x,y:positive) ~(add_carry y x)=(add_un x).
Proof.
Intros x y H; Absurd (add y x)=x; 
      [ Apply add_no_neutral
      | Apply add_un_inj; Rewrite <- ZL13; Assumption ].
Qed.

(** Simplification *)

Lemma add_carry_add :
  (x,y,z,t:positive) (add_carry x z)=(add_carry y t) -> (add x z)=(add y t).
Proof.
Intros x y z t H; Apply add_un_inj; Do 2 Rewrite <- ZL13; Assumption.
Qed.

Lemma simpl_add_r : (x,y,z:positive) (add x z)=(add y z) -> x=y.
Proof.
Intros x y z; Generalize x y; Clear x y.
NewInduction z as [z|z|].
  NewDestruct x as [x|x|]; NewDestruct y as [y|y|]; Simpl; Intro H; 
  Discriminate H Orelse Try (Injection H; Clear H; Intro H).
    Rewrite IHz with 1:=(add_carry_add ? ? ? ? H); Reflexivity.
    Absurd (add_carry x z)=(add_un z);
      [ Apply add_carry_not_add_un | Assumption ].
    Rewrite IHz with 1:=H; Reflexivity.
    Symmetry in H; Absurd (add_carry y z)=(add_un z);
      [ Apply add_carry_not_add_un | Assumption ].
    Reflexivity.
  NewDestruct x as [x|x|]; NewDestruct y as [y|y|]; Simpl; Intro H; 
  Discriminate H Orelse Try (Injection H; Clear H; Intro H).
    Rewrite IHz with 1:=H; Reflexivity.
    Absurd (add x z)=z; [ Apply add_no_neutral | Assumption ].
    Rewrite IHz with 1:=H; Reflexivity.
    Symmetry in H; Absurd y+z=z; [ Apply add_no_neutral | Assumption ].
    Reflexivity.
  Intros H x y; Apply add_un_inj; Do 2 Rewrite ZL12; Assumption.
Qed.

Lemma simpl_add_carry_r :
 (x,y,z:positive) (add_carry x z)=(add_carry y z) -> x=y.
Proof.
Intros x y z H; Apply simpl_add_r with z:=z; Apply add_carry_add; Assumption.
Qed.

Lemma simpl_add_l : (x,y,z:positive) (add x y)=(add x z) -> y=z.
Proof.
Intros x y z H;Apply simpl_add_r with z:=x; 
  Rewrite add_sym with x:=z; Rewrite add_sym with x:=y; Assumption.
Qed.

Lemma simpl_add_carry_l :
  (x,y,z:positive) (add_carry x y)=(add_carry x z) -> y=z.
Proof.
Intros x y z H;Apply simpl_add_r with z:=x; 
Rewrite add_sym with x:=z; Rewrite add_sym with x:=y; Apply add_carry_add; 
Assumption.
Qed.

(** Addition on positive is associative *)

Theorem add_assoc: (x,y,z:positive)(add x (add y z)) = (add (add x y) z).
Proof.
Intros x y; Generalize x; Clear x.
NewInduction y as [y|y|].
  NewDestruct x as [x|x|]; NewDestruct z as [z|z|]; Simpl; Repeat Rewrite ZL13;
    Repeat Rewrite ZL14; Repeat Rewrite ZL14bis; Reflexivity Orelse
    Repeat Apply f_equal with A:=positive; Apply IHy.
  NewDestruct x as [x|x|]; NewDestruct z as [z|z|]; Simpl; Repeat Rewrite ZL13;
    Repeat Rewrite ZL14; Repeat Rewrite ZL14bis; Reflexivity Orelse
    Repeat Apply f_equal with A:=positive; Apply IHy.
  Intros x z; Rewrite add_sym with x:=xH; Do 2 Rewrite <- ZL12; Rewrite ZL14bis; Rewrite ZL14; Reflexivity.
Qed.

(** Commutation of addition with the double of a positive number *)

Lemma xO_xI_plus_double_moins_un :
  (p,q:positive) (xO (add p q)) = (add (xI p) (double_moins_un q)).
Proof.
NewDestruct q; Simpl.
  Rewrite ZL13; Rewrite <- ZL14; Reflexivity.
  Rewrite ZL13; Rewrite <- ZL14; Rewrite -> is_double_moins_un;
    Reflexivity.
  Rewrite -> ZL12; Reflexivity.
Qed.

Lemma double_moins_un_plus_xO_double_moins_un :
 (p,q:positive) (double_moins_un (add p q)) = (add (xO p) (double_moins_un q)).
Proof.
NewInduction p as [p|p|]; NewDestruct q as [q|q|]; Simpl;
  Try Rewrite ZL13; Try Rewrite is_double_moins_un; 
  Try Rewrite double_moins_un_add_un_xI; Try Reflexivity.
  NewDestruct q; Simpl.
    Rewrite ZL13; Rewrite <- ZL14; Reflexivity.
    Rewrite ZL13; Rewrite <- ZL14; Rewrite is_double_moins_un;
      Reflexivity.
    Rewrite ZL12; Reflexivity.
  Rewrite IHp; Reflexivity.
  NewDestruct q; Simpl; Try Rewrite is_double_moins_un; Reflexivity.
Qed.

Lemma add_xI_double_moins_un :
  (p,q:positive)(xO (add p q)) = (add (xI p) (double_moins_un q)).
Proof.
Intros; Change (xI p) with (add (xO p) xH).
Rewrite <- add_assoc; Rewrite <- ZL12bis; Rewrite is_double_moins_un.
Reflexivity.
Qed.

Lemma double_moins_un_add :
  (p,q:positive)(double_moins_un (add p q)) = (add (xO p) (double_moins_un q)).
Proof.
NewInduction p as [p IHp|p IHp|]; NewDestruct q as [q|q|];
 Simpl; Try Rewrite ZL13; Try Rewrite double_moins_un_add_un_xI;
 Try Rewrite IHp; Try Rewrite add_xI_double_moins_un; Try Reflexivity.
 Rewrite <- is_double_moins_un; Rewrite ZL12bis; Reflexivity. 
Qed.

(** Misc *)

Lemma add_x_x : (x:positive) (add x x) = (xO x).
Proof.
NewInduction x; Simpl; Try Rewrite ZL13; Try Rewrite IHx; Reflexivity.
Qed.

(**********************************************************************)
(** Properties of minus on binary positive numbers *)

(* Properties of subtraction *)

Lemma ZS: (p:positive_mask) (Zero_suivi_de_mask p) = IsNul -> p = IsNul.
Proof.
NewDestruct p; Simpl; [ Trivial | Discriminate 1 | Discriminate 1 ].
Qed.

Lemma US: (p:positive_mask) ~(Un_suivi_de_mask p)=IsNul.
Proof.
Induction p; Intros; Discriminate.
Qed.

Lemma USH: (p:positive_mask) (Un_suivi_de_mask p) = (IsPos xH) -> p = IsNul.
Proof.
NewDestruct p; Simpl; [ Trivial | Discriminate 1 | Discriminate 1 ].
Qed.

Lemma ZSH: (p:positive_mask) ~(Zero_suivi_de_mask p)= (IsPos xH).
Proof.
Induction p; Intros; Discriminate.
Qed.

Theorem sub_pos_x_x : (x:positive) (sub_pos x x) = IsNul.
Proof.
Induction x; [
  Simpl; Intros p H;Rewrite H;Simpl; Trivial
| Intros p H;Simpl;Rewrite H;Auto
| Auto ].
Qed.

Theorem ZL10: (x,y:positive)
 (sub_pos x y) = (IsPos xH) -> (sub_neg x y) = IsNul.
Proof.
NewInduction x as [p|p|]; NewDestruct y as [q|q|]; Simpl; Intro H;
Try Discriminate H; [
  Absurd (Zero_suivi_de_mask (sub_pos p q))=(IsPos xH);
   [ Apply ZSH | Assumption ]
| Assert Heq : (sub_pos p q)=IsNul;
   [ Apply USH;Assumption | Rewrite Heq; Reflexivity ]
| Assert Heq : (sub_neg p q)=IsNul;
   [ Apply USH;Assumption | Rewrite Heq; Reflexivity ]
| Absurd (Zero_suivi_de_mask (sub_pos p q))=(IsPos xH); 
   [ Apply ZSH | Assumption ]
| NewDestruct p; Simpl; [ Discriminate H | Discriminate H | Reflexivity ] ].
Qed.

(* Properties valid only for x>y *)

Theorem sub_pos_SUPERIEUR:
  (x,y:positive)(compare x y EGAL)=SUPERIEUR -> 
    (EX h:positive | (sub_pos x y) = (IsPos h) /\ (add y h) = x /\
                     (h = xH \/ (sub_neg x y) = (IsPos (sub_un h)))).
Proof.
NewInduction x as [p|p|];NewDestruct y as [q|q|]; Simpl; Intro H;
  Try Discriminate H.
  NewDestruct (IHp q H) as [z [H4 [H6 H7]]]; Exists (xO z); Split.
    Rewrite H4; Reflexivity.
    Split.
      Simpl; Rewrite H6; Reflexivity.
      Right; Clear H6; NewDestruct (ZL11 z) as [H8|H8]; [
        Rewrite H8; Rewrite H8 in H4;
        Rewrite ZL10; [ Reflexivity | Assumption ]
      | Clear H4; NewDestruct H7 as [H9|H9]; [
          Absurd z=xH; Assumption
        | Rewrite H9; Clear H9; NewDestruct z; 
            [ Reflexivity | Reflexivity | Absurd xH=xH; Trivial ]]].
  Case ZLSS with 1:=H; [
    Intros H3;Elim (IHp q H3); Intros z H4; Exists (xI z);
    Elim H4;Intros H5 H6;Elim H6;Intros H7 H8; Split; [
      Simpl;Rewrite H5;Auto
    | Split; [
        Simpl; Rewrite H7; Trivial
      | Right;
        Change (Zero_suivi_de_mask (sub_pos p q))=(IsPos (sub_un (xI z)));
        Rewrite H5; Auto ]]
  | Intros H3; Exists xH; Rewrite H3; Split; [
      Simpl; Rewrite sub_pos_x_x; Auto
    | Split; Auto ]].
  Exists (xO p); Auto.
  NewDestruct (IHp q) as [z [H4 [H6 H7]]].
    Apply ZLIS; Assumption.
    NewDestruct (ZL11 z) as [vZ|]; [
      Exists xH; Split; [
        Rewrite ZL10; [ Reflexivity | Rewrite vZ in H4;Assumption ]
      | Split; [
          Simpl; Rewrite ZL12; Rewrite <- vZ; Rewrite H6; Trivial
        | Auto ]]
    | Exists (xI (sub_un z)); NewDestruct H7 as [|H8];[
        Absurd z=xH;Assumption
      | Split; [
          Rewrite H8; Trivial
        | Split; [ Simpl; Rewrite ZL15; [
              Rewrite H6;Trivial
            | Assumption ]
          | Right; Rewrite H8; Reflexivity]]]].
  NewDestruct (IHp q H) as [z [H4 [H6 H7]]].
  Exists (xO z); Split; [
    Rewrite H4;Auto
  | Split; [
      Simpl;Rewrite H6;Reflexivity
    | Right; 
      Change (Un_suivi_de_mask (sub_neg p q))=(IsPos (double_moins_un z));
      NewDestruct (ZL11 z) as [H8|H8]; [
        Rewrite H8; Simpl;
        Assert H9:(sub_neg p q)=IsNul;[
          Apply ZL10;Rewrite <- H8;Assumption
        | Rewrite H9;Reflexivity ]
      | NewDestruct H7 as [H9|H9]; [
          Absurd z=xH;Auto
        | Rewrite H9; NewDestruct z; Simpl; 
            [ Reflexivity
            | Reflexivity
            | Absurd xH=xH; [Assumption | Reflexivity]]]]]].
  Exists (double_moins_un p); Split; [
    Reflexivity
  | Clear IHp; Split; [
      NewDestruct p; Simpl; [
        Reflexivity
      | Rewrite is_double_moins_un; Reflexivity
      | Reflexivity ]
    | NewDestruct p; [Right|Right|Left]; Reflexivity ]].
Qed.

Theorem sub_add: 
(x,y:positive) (compare x y EGAL) = SUPERIEUR -> (add y (true_sub x y)) = x.
Proof.
Intros x y H;Elim sub_pos_SUPERIEUR with 1:=H;
Intros z H1;Elim H1;Intros H2 H3; Elim H3;Intros H4 H5; 
Unfold true_sub ;Rewrite H2; Exact H4.
Qed.

(**********************************************************************)
(** Properties of the injection from binary positive numbers to Peano 
    natural numbers *)

Require Le.
Require Lt.
Require Plus.
Require Mult.
Require Minus.

(** [IPN] is a morphism for addition *)

Lemma convert_add_un :
  (x:positive)(m:nat)
    (positive_to_nat (add_un x) m) = (plus m (positive_to_nat x m)).
Proof.
Induction x; Simpl; Auto; Intros x' H0 m; Rewrite H0;
Rewrite plus_assoc_l; Trivial.
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

(** [IPN_shift] is a morphism for addition wrt the factor *)

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

Lemma ZL6:
  (p:positive) (positive_to_nat p (S (S O))) = (plus (convert p) (convert p)).
Proof.
Intro p;Change (2) with (plus (S O) (S O)); Rewrite ZL2; Trivial.
Qed.
 
(** [IPN] is a morphism for multiplication *)

Lemma positive_to_nat_mult : (p:positive) (n,m:nat)
    (positive_to_nat p (mult m n))=(mult m (positive_to_nat p n)).
Proof.
  Induction p. Intros. Simpl. Rewrite mult_plus_distr_r. Rewrite <- (mult_plus_distr_r m n n).
  Rewrite (H (plus n n) m). Reflexivity.
  Intros. Simpl. Rewrite <- (mult_plus_distr_r m n n). Apply H.
  Trivial.
Qed.

Theorem times_convert :
  (x,y:positive) (convert (times x y)) = (mult (convert x) (convert y)).
Proof.
Intros x y; NewInduction x as [ x' H | x' H | ]; [
  Change (times (xI x') y) with (add y (xO (times x' y))); Rewrite convert_add;
  Unfold 2 3 convert; Simpl; Do 2 Rewrite ZL6; Rewrite H;
  Rewrite -> mult_plus_distr; Reflexivity
| Unfold 1 2 convert; Simpl; Do 2 Rewrite ZL6;
  Rewrite H; Rewrite mult_plus_distr; Reflexivity
| Simpl; Rewrite <- plus_n_O; Reflexivity ].
Qed.

(** IPN is strictly positive *)

Theorem compare_positive_to_nat_O : 
	(p:positive)(m:nat)(le m (positive_to_nat p m)).
Induction p; Simpl; Auto with arith.
Intros; Apply le_trans with (plus m m);  Auto with arith.
Qed.

Theorem compare_convert_O : (p:positive)(lt O (convert p)).
Intro; Unfold convert; Apply lt_le_trans with (S O); Auto with arith.
Apply compare_positive_to_nat_O.
Qed.

(** Mapping of 2 and 4 through IPN_shift *)

Lemma positive_to_nat_2 : (p:positive)
    (positive_to_nat p (2))=(mult (2) (positive_to_nat p (1))).
Proof.
  Intros. Rewrite <- positive_to_nat_mult. Reflexivity.
Qed.

Lemma positive_to_nat_4 : (p:positive)
    (positive_to_nat p (4))=(mult (2) (positive_to_nat p (2))).
Proof.
  Intros. Rewrite <- positive_to_nat_mult. Reflexivity.
Qed.

(** Mapping of xH, xO and xI through IPN *)

Lemma convert_xH : (convert xH)=(1).
Proof.
  Reflexivity.
Qed.

Lemma convert_xO : (p:positive) (convert (xO p))=(mult (2) (convert p)).
Proof.
  Induction p. Unfold convert. Simpl. Intros. Rewrite positive_to_nat_2.
  Rewrite positive_to_nat_4. Rewrite H. Simpl. Rewrite <- plus_Snm_nSm. Reflexivity.
  Unfold convert. Simpl. Intros. Rewrite positive_to_nat_2. Rewrite positive_to_nat_4.
  Rewrite H. Reflexivity.
  Reflexivity.
Qed.

Lemma convert_xI : (p:positive) (convert (xI p))=(S (mult (2) (convert p))).
Proof.
  Induction p. Unfold convert. Simpl. Intro p0. Intro. Rewrite positive_to_nat_2.
  Rewrite positive_to_nat_4; Injection H; Intro H1; Rewrite H1; Rewrite <- plus_Snm_nSm; Reflexivity.
  Unfold convert. Simpl. Intros. Rewrite positive_to_nat_2. Rewrite positive_to_nat_4.
  Injection H; Intro H1; Rewrite H1; Reflexivity.
  Reflexivity.
Qed.

(**********************************************************************)
(** Properties of the shifted injection from Peano natural numbers to 
    binary positive numbers *)

(** Composition of [INP] and [IPN] is shifted identity on [nat] *)

Theorem bij1 : (m:nat) (convert (anti_convert m)) = (S m).
Proof.
Induction m; [
  Unfold convert; Simpl; Trivial
| Unfold convert; Intros n H; Simpl; Rewrite convert_add_un; Rewrite H; Auto ].
Qed.

(** Miscellaneous lemmas on [INP] *)

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
  Unfold convert ;Simpl; Change (2) with (plus (1) (1)); Rewrite ZL2; Unfold convert in H1;
  Rewrite H1; Auto with arith
| Intros p H1;Elim H1;Intros x H2; Exists (plus x (S x)); Unfold convert;
  Simpl; Change (2) with (plus (1) (1)); Rewrite ZL2;Unfold convert in H2; Rewrite H2; Auto with arith
| Exists O ;Auto with arith ].
Qed.

Lemma ZL5: (x:nat) (anti_convert (plus (S x) (S x))) =  (xI (anti_convert x)).
Proof.
Induction x;Simpl; [
  Auto with arith
| Intros y H; Rewrite <- plus_n_Sm; Simpl; Rewrite H; Auto with arith].
Qed.

(** Composition of [IPN] and [INP] is shifted identity on [positive] *)

Theorem bij2 : (x:positive) (anti_convert (convert x)) = (add_un x).
Proof.
Induction x; [
  Intros p H; Simpl; Rewrite <- H; Change (2) with (plus (1) (1));
  Rewrite ZL2; Elim (ZL4 p); 
  Unfold convert; Intros n H1;Rewrite H1; Rewrite ZL3; Auto with arith
| Intros p H; Unfold convert ;Simpl; Change (2) with (plus (1) (1));
  Rewrite ZL2;
  Rewrite <- (sub_add_one
               (anti_convert
                 (plus (positive_to_nat p (S O)) (positive_to_nat p (S O)))));
  Rewrite <- (sub_add_one (xI p));
  Simpl;Rewrite <- H;Elim (ZL4 p); Unfold convert ;Intros n H1;Rewrite H1;
  Rewrite ZL5; Simpl; Trivial with arith
| Unfold convert; Simpl; Auto with arith ].
Qed.

(** Composition of [IPN], [INP] and [Ppred] is identity on [positive] *)

Theorem bij3: (x:positive)(sub_un (anti_convert (convert x))) = x.
Proof.
Intros x; Rewrite bij2; Rewrite sub_add_one; Trivial with arith.
Qed.

(** Extra lemmas on [lt] on Peano natural numbers *)

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

(** [IPN] is a morphism from [positive] to [nat] for [lt] (expressed
    from [compare] on [positive])

    Part 1: [lt] on [positive] is finer than [lt] on [nat]
*)

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

(** [IPN] is a morphism from [positive] to [nat] for [gt] (expressed
    from [compare] on [positive])

    Part 1: [gt] on [positive] is finer than [gt] on [nat]
*)

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

(** [IPN] is a morphism from [positive] to [nat] for [lt] (expressed
    from [compare] on [positive])

    Part 2: [lt] on [nat] is finer than [lt] on [positive]
*)

Theorem convert_compare_INFERIEUR : 
  (x,y:positive)(lt (convert x) (convert y)) -> (compare x y EGAL) = INFERIEUR.
Proof.
Intros x y; Unfold gt; Elim (Dcompare (compare x y EGAL)); [
  Intros E; Rewrite (compare_convert_EGAL x y E); 
  Intros H;Absurd (lt (convert y) (convert y)); [ Apply lt_n_n | Assumption ]
| Intros H;Elim H; [
    Auto
  | Intros H1 H2; Absurd (lt (convert x) (convert y)); [
      Apply lt_not_sym; Change (gt (convert x) (convert y)); 
      Apply compare_convert_SUPERIEUR; Assumption
    | Assumption ]]].
Qed.

(** [IPN] is a morphism from [positive] to [nat] for [gt] (expressed
    from [compare] on [positive])

    Part 2: [gt] on [nat] is finer than [gt] on [positive]
*)

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
  | Auto]].
Qed.

(**********************************************************************)
(** Extra properties of the comparison on binary positive numbers *)

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

Lemma ZC4: (x,y:positive) (compare x y EGAL) = (Op (compare y x EGAL)).
Proof.
(((Intros x y;Elim (Dcompare (compare y x EGAL));[Idtac | Intros H;Elim H]);
Intros E;Rewrite E;Simpl); [Apply ZC3 | Apply ZC2 | Apply ZC1 ]); Assumption.
Qed.

(**********************************************************************)
(** Extra properties of the injection from binary positive numbers to Peano 
    natural numbers *)

(** [IPN] is a morphism for subtraction on positive numbers *)

Theorem true_sub_convert:
  (x,y:positive) (compare x y EGAL) = SUPERIEUR -> 
     (convert (true_sub x y)) = (minus (convert x) (convert y)).
Proof.
Intros x y H; Apply (simpl_plus_l (convert y));
Rewrite le_plus_minus_r; [
  Rewrite <- convert_add; Rewrite sub_add; Auto with arith
| Apply lt_le_weak; Exact (compare_convert_SUPERIEUR x y H)].
Qed.

(** [IPN] is injective *)

Lemma convert_intro : (x,y:positive)(convert x)=(convert y) -> x=y.
Proof.
Intros x y H;Rewrite <- (bij3 x);Rewrite <- (bij3 y); Rewrite H; Trivial with arith.
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

(* Comparison and subtraction *)

Lemma compare_true_sub_right :
  (p,q,z:positive)
  (compare q p EGAL)=INFERIEUR->
  (compare z p EGAL)=SUPERIEUR->
  (compare z q EGAL)=SUPERIEUR->
  (compare (true_sub z p) (true_sub z q) EGAL)=INFERIEUR.
Proof.
Intros; Apply convert_compare_INFERIEUR; Rewrite true_sub_convert; [
  Rewrite true_sub_convert; [
    Apply simpl_lt_plus_l with p:=(convert q); Rewrite le_plus_minus_r; [
      Rewrite plus_sym; Apply simpl_lt_plus_l with p:=(convert p);
        Rewrite plus_assoc_l; Rewrite le_plus_minus_r; [
          Rewrite (plus_sym (convert p)); Apply lt_reg_l;
          Apply compare_convert_INFERIEUR; Assumption 
        | Apply lt_le_weak; Apply compare_convert_INFERIEUR;
          Apply ZC1; Assumption ]
      | Apply lt_le_weak;Apply compare_convert_INFERIEUR;
        Apply ZC1; Assumption ]
    | Assumption ]
  | Assumption ].
Qed.

Lemma compare_true_sub_left :
  (p,q,z:positive)
  (compare q p EGAL)=INFERIEUR->
  (compare p z EGAL)=SUPERIEUR->
  (compare q z EGAL)=SUPERIEUR->
  (compare (true_sub q z) (true_sub p z) EGAL)=INFERIEUR.
Proof.
Intros; Apply convert_compare_INFERIEUR; Rewrite true_sub_convert; [
  Rewrite true_sub_convert; [
    Unfold gt; Apply simpl_lt_plus_l with p:=(convert z);
    Rewrite le_plus_minus_r; [
      Rewrite le_plus_minus_r; [
        Apply compare_convert_INFERIEUR;Assumption
      | Apply lt_le_weak; Apply compare_convert_INFERIEUR;Apply ZC1;Assumption]
    | Apply lt_le_weak; Apply compare_convert_INFERIEUR;Apply ZC1; Assumption]
  | Assumption]
| Assumption].
Qed.

(**********************************************************************)
(** Properties of multiplication on binary positive numbers *)

(** One is right neutral for multiplication *)

Lemma times_x_1 : (x:positive) (times x xH) = x.
Proof.
NewInduction x; Simpl.
  Rewrite IHx; Reflexivity.
  Rewrite IHx; Reflexivity.
  Reflexivity.
Qed.

(** Right reduction properties for multiplication *)

Lemma times_x_double : (x,y:positive) (times x (xO y)) = (xO (times x y)).
Proof.
Intros; NewInduction x; Simpl.
  Rewrite IHx; Reflexivity.
  Rewrite IHx; Reflexivity.
  Reflexivity.
Qed.

Lemma times_x_double_plus_one :
 (x,y:positive) (times x (xI y)) = (add x (xO (times x y))).
Proof.
Intros; NewInduction x; Simpl.
  Rewrite IHx; Do 2 Rewrite add_assoc; Rewrite add_sym with x:=y; Reflexivity.
  Rewrite IHx; Reflexivity.
  Reflexivity.
Qed.

(** Commutativity of multiplication *)

Theorem times_sym : (x,y:positive) (times x y) = (times y x).
Proof.
NewInduction y; Simpl.
  Rewrite <- IHy; Apply times_x_double_plus_one.
  Rewrite <- IHy; Apply times_x_double.
  Apply times_x_1.
Qed.

(** Distributivity of multiplication over addition *)

Theorem times_add_distr:
  (x,y,z:positive) (times x (add y z)) = (add (times x y) (times x z)).
Proof.
Intros; NewInduction x; Simpl.
  Rewrite IHx; Rewrite <- add_assoc with y := (xO (times x y));
    Rewrite -> add_assoc with x := (xO (times x y));
    Rewrite -> add_sym with x := (xO (times x y));
    Rewrite <- add_assoc with y := (xO (times x y));
    Rewrite -> add_assoc with y := z; Reflexivity.
  Rewrite IHx; Reflexivity.
  Reflexivity.
Qed.

Theorem times_add_distr_l:
  (x,y,z:positive) (times (add x y) z) = (add (times x z) (times y z)).
Proof.
Intros x y z; Do 3 Rewrite times_sym with y:=z; Apply times_add_distr.
Qed.

(** Associativity of multiplication *)

Theorem times_assoc :
  ((x,y,z:positive) (times x (times y z))= (times (times x y) z)).
Proof.
NewInduction x as [x|x|]; Simpl; Intros y z.
  Rewrite IHx; Rewrite times_add_distr_l; Reflexivity.
  Rewrite IHx; Reflexivity.
  Reflexivity.
Qed.

(** Distributivity of multiplication over subtraction *)

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

(** Parity properties of multiplication *)

Theorem times_discr_xO_xI : 
  (x,y,z:positive)(times (xI x) z)<>(times (xO y) z).
Proof.
NewInduction z as [|z IHz|]; Try Discriminate.
Intro H; Apply IHz; Clear IHz.
Do 2 Rewrite times_x_double in H.
Injection H; Clear H; Intro H; Exact H.
Qed.

Theorem times_discr_xO : (x,y:positive)(times (xO x) y)<>y.
Proof.
NewInduction y; Try Discriminate.
Rewrite times_x_double; Injection; Assumption.
Qed.

(** Simplification properties of multiplication *)

Theorem simpl_times_r : (x,y,z:positive) (times x z)=(times y z) -> x=y.
Proof.
NewInduction x as [p IHp|p IHp|]; NewDestruct y as [q|q|]; Intros z H;
    Reflexivity Orelse Apply (f_equal positive) Orelse Apply False_ind.
  Simpl in H; Apply IHp with z := (xO z); Simpl; Do 2 Rewrite times_x_double;
    Apply simpl_add_l with 1 := H.
  Apply times_discr_xO_xI with 1 := H.
  Simpl in H; Rewrite add_sym in H; Apply add_no_neutral with 1 := H.
  Symmetry in H; Apply times_discr_xO_xI with 1 := H.
  Apply IHp with z := (xO z); Simpl; Do 2 Rewrite times_x_double; Assumption.
  Apply times_discr_xO with 1:=H.
  Simpl in H; Symmetry in H; Rewrite add_sym in H; 
    Apply add_no_neutral with 1 := H.
  Symmetry in H; Apply times_discr_xO with 1:=H.
Qed.

Theorem simpl_times_l : (x,y,z:positive) (times z x)=(times z y) -> x=y.
Proof.
Intros x y z H; Apply simpl_times_r with z:=z.
Rewrite times_sym with x:=x; Rewrite times_sym with x:=y; Assumption.
Qed.

(**********************************************************************)
(** Peano induction on binary positive positive numbers *)

Fixpoint add_iter [x:positive] : positive -> positive := 
  [y]Cases x of 
  | xH => (add_un y)
  | (xO x) => (add_iter x (add_iter x y))
  | (xI x) => (add_iter x (add_iter x (add_un y)))
  end.

Lemma add_iter_add : (p,q:positive)(add_iter p q)=(add p q).
Proof.
NewInduction p as [p IHp|p IHp|]; NewDestruct q; Simpl;
  Reflexivity Orelse Do 2 Rewrite IHp; Rewrite add_assoc; Rewrite add_x_x;
  Try Reflexivity.
Rewrite ZL13; Rewrite <- ZL14; Reflexivity.
Rewrite ZL12; Reflexivity.
Qed.

Lemma add_iter_xO : (p:positive)(add_iter p p)=(xO p).
Proof.
Intro; Rewrite <- add_x_x; Apply add_iter_add.
Qed.

Lemma add_iter_xI : (p:positive)(add_un (add_iter p p))=(xI p).
Proof.
Intro; Rewrite xI_add_un_xO; Rewrite <- add_x_x; 
  Apply (f_equal positive); Apply add_iter_add.
Qed.

Lemma iterate_add : (P:(positive->Type))
  ((n:positive)(P n) ->(P (add_un n)))->(p,n:positive)(P n) ->
  (P (add_iter p n)).
Proof.
Intros P H; NewInduction p; Simpl; Intros.
Apply IHp; Apply IHp; Apply H; Assumption.
Apply IHp; Apply IHp; Assumption.
Apply H; Assumption.
Defined.

(** Peano induction *)

Theorem Pind : (P:(positive->Prop))
  (P xH) ->((n:positive)(P n) ->(P (add_un n))) ->(n:positive)(P n).
Proof.
Intros P H1 Hsucc; NewInduction n.
Rewrite <- add_iter_xI; Apply Hsucc; Apply iterate_add; Assumption.
Rewrite <- add_iter_xO; Apply iterate_add; Assumption.
Assumption.
Qed.

(** Peano recursion *)

Definition Prec : (A:Set)A->(positive->A->A)->positive->A :=
  [A;a;f]Fix Prec { Prec [p:positive] : A :=
  Cases p of
  | xH => a
  | (xO p) => (iterate_add [_]A f p p (Prec p))
  | (xI p) => (f (add_iter p p) (iterate_add [_]A f p p (Prec p)))
  end}.

(** Test *)

Check
 let fact = (Prec positive xH [p;r](times (add_un p) r)) in
 let seven = (xI (xI xH)) in
 let five_thousand_forty= (xO(xO(xO(xO(xI(xI(xO(xI(xI(xI(xO(xO xH))))))))))))
 in ((refl_equal ? ?) :: (fact seven) = five_thousand_forty).

(**********************************************************************)
(** Binary natural numbers *)

Inductive entier: Set := Nul : entier | Pos : positive -> entier.

(** Operation x -> 2*x+1 *)

Definition Un_suivi_de := [x]
  Cases x of Nul => (Pos xH) | (Pos p) => (Pos (xI p)) end.

(** Operation x -> 2*x *)

Definition Zero_suivi_de :=
  [n] Cases n of Nul => Nul | (Pos p) => (Pos (xO p)) end.

(** Successor *)

Definition Nsucc :=
  [n] Cases n of Nul => (Pos xH) | (Pos p) => (Pos (add_un p)) end.

(** Addition *)

Definition Nplus := [n,m]
  Cases n m of
  | Nul     _       => m
  | _       Nul     => n
  | (Pos p) (Pos q) => (Pos (add p q))
  end.

(** Multiplication *)

Definition Nmult := [n,m]
  Cases n m of
  | Nul     _       => Nul
  | _       Nul     => Nul
  | (Pos p) (Pos q) => (Pos (times p q))
  end.

(** Properties of addition *)

Theorem Nplus_0_l : (n:entier)(Nplus Nul n)=n.
Proof.
Reflexivity.
Qed.

Theorem Nplus_0_r : (n:entier)(Nplus n Nul)=n.
Proof.
NewDestruct n; Reflexivity.
Qed.

Theorem Nplus_comm : (n,m:entier)(Nplus n m)=(Nplus m n).
Proof.
Intros.
NewDestruct n; NewDestruct m; Simpl; Try Reflexivity.
Rewrite add_sym; Reflexivity.
Qed.

Theorem Nplus_assoc_l : 
  (n,m,p:entier)(Nplus (Nplus n m) p)=(Nplus n (Nplus m p)).
Proof.
Intros.
NewDestruct n; Try Reflexivity.
NewDestruct m; Try Reflexivity.
NewDestruct p; Try Reflexivity.
Simpl; Rewrite add_assoc; Reflexivity.
Qed.

(** Properties of multiplication *)

Theorem Nmult_1_l : (n:entier)(Nmult (Pos xH) n)=n.
Proof.
NewDestruct n; Reflexivity.
Qed.

Theorem Nmult_1_r : (n:entier)(Nmult n (Pos xH))=n.
Proof.
NewDestruct n; Simpl; Try Reflexivity.
Rewrite times_x_1; Reflexivity.
Qed.

Theorem Nmult_comm : (n,m:entier)(Nmult n m)=(Nmult m n).
Proof.
Intros.
NewDestruct n; NewDestruct m; Simpl; Try Reflexivity.
Rewrite times_sym; Reflexivity.
Qed.

Theorem Nmult_assoc_l : 
  (n,m,p:entier)(Nmult (Nmult n m) p)=(Nmult n (Nmult m p)).
Proof.
Intros.
NewDestruct n; Try Reflexivity.
NewDestruct m; Try Reflexivity.
NewDestruct p; Try Reflexivity.
Simpl; Rewrite times_assoc; Reflexivity.
Qed.

Theorem Nmult_Nplus_distr_l :
  (n,m,p:entier)(Nmult (Nplus n m) p)=(Nplus (Nmult n p) (Nmult m p)).
Proof.
Intros.
NewDestruct n; Try Reflexivity.
NewDestruct m; NewDestruct p; Try Reflexivity.
Simpl; Rewrite times_add_distr_l; Reflexivity.
Qed.

Theorem Nmult_int_r : (n,m,p:entier) (Nmult n p)=(Nmult m p) -> n=m\/p=Nul.
Proof.
NewDestruct p; Intro H.
Right; Reflexivity.
Left; NewDestruct n; NewDestruct m; Reflexivity Orelse Try Discriminate H.
Injection H; Clear H; Intro H; Rewrite simpl_times_r with 1:=H; Reflexivity.
Qed. 

(** Peano induction on binary natural numbers *)

Theorem Nind : (P:(entier ->Prop))
  (P Nul) ->((n:entier)(P n) ->(P (Nsucc n))) ->(n:entier)(P n).
Proof.
NewDestruct n.
  Assumption.
  Apply Pind with P := [p](P (Pos p)).
Exact (H0 Nul H).
Intro p'; Exact (H0 (Pos p')).
Qed.

(**********************************************************************)
(** Binary integer numbers *)

Inductive Z : Set := 
  ZERO : Z | POS : positive -> Z | NEG : positive -> Z.

(* Declare Scope Z_scope with Key Z *)
Delimits Scope Z_scope with Z.

(* Automatically open scope Z_scope for arguments of type Z, POS and NEG *)
Bind Scope Z_scope with Z.
Arguments Scope POS [ Z_scope ].
Arguments Scope NEG [ Z_scope ].

(** Addition on integers *)

Definition Zdouble_plus_one [x:Z] :=
  Cases x of 
  | ZERO    => (POS xH)
  | (POS p) => (POS (xI p))
  | (NEG p) => (NEG (double_moins_un p))
  end.

Definition Zdouble_minus_one [x:Z] :=
  Cases x of 
  | ZERO    => (NEG xH)
  | (NEG p) => (NEG (xI p))
  | (POS p) => (POS (double_moins_un p))
  end.

Definition Zdouble [x:Z] :=
  Cases x of
  | ZERO => ZERO
  | (POS p) => (POS (xO p))
  | (NEG p) => (NEG (xO p))
 end.

Fixpoint Zsub_pos[x,y:positive]:Z :=
  Cases x y of
  | (xI x') (xI y') => (Zdouble (Zsub_pos x' y'))
  | (xI x') (xO y') => (Zdouble_plus_one (Zsub_pos x' y'))
  | (xI x') xH      => (POS (xO x'))
  | (xO x') (xI y') => (Zdouble_minus_one (Zsub_pos x' y'))
  | (xO x') (xO y') => (Zdouble (Zsub_pos x' y'))
  | (xO x') xH      => (POS (double_moins_un x'))
  | xH      (xI y') => (NEG (xO y'))
  | xH      (xO y') => (NEG (double_moins_un y'))
  | xH      xH      => ZERO
  end.

Definition Zplus := [x,y:Z]
  Cases x y of
    ZERO      y       => y
  | x         ZERO    => x
  | (POS x') (POS y') => (POS (add x' y'))
  | (POS x') (NEG y') => 
      Cases (compare x' y' EGAL) of
      | EGAL => ZERO
      | INFERIEUR => (NEG (true_sub y' x'))
      | SUPERIEUR => (POS (true_sub x' y'))
      end
  | (NEG x') (POS y') =>
      Cases (compare x' y' EGAL) of
      | EGAL => ZERO
      | INFERIEUR => (POS (true_sub y' x'))
      | SUPERIEUR => (NEG (true_sub x' y'))
      end
  | (NEG x') (NEG y') => (NEG (add x' y'))
  end.

V8Infix "+" Zplus : Z_scope.

(** Opposite *)

Definition Zopp := [x:Z]
 Cases x of
      ZERO => ZERO
    | (POS x) => (NEG x)
    | (NEG x) => (POS x)
    end.

V8Notation "- x" := (Zopp x) : Z_scope.

(** Multiplication on integers *)

Definition Zmult := [x,y:Z]
  Cases x y of
  | ZERO     _        => ZERO
  | _        ZERO     => ZERO
  | (POS x') (POS y') => (POS (times x' y'))
  | (POS x') (NEG y') => (NEG (times x' y'))
  | (NEG x') (POS y') => (NEG (times x' y'))
  | (NEG x') (NEG y') => (POS (times x' y'))
  end.

V8Infix "*" Zmult : Z_scope.

(** Comparison of integers *)

Definition Zcompare := [x,y:Z]
  Cases x y of
  | ZERO     ZERO     => EGAL
  | ZERO     (POS y') => INFERIEUR
  | ZERO     (NEG y') => SUPERIEUR
  | (POS x') ZERO     => SUPERIEUR
  | (POS x') (POS y') => (compare x' y' EGAL)
  | (POS x') (NEG y') => SUPERIEUR
  | (NEG x') ZERO     => INFERIEUR
  | (NEG x') (POS y') => INFERIEUR
  | (NEG x') (NEG y') => (Op (compare x' y' EGAL))
  end.

V8Infix "?=" Zcompare (at level 50, no associativity) : Z_scope.

Open Local Scope Z_scope.

(**********************************************************************)
(** Properties of opposite on binary integer numbers *)

Theorem Zopp_NEG : (x:positive) (Zopp (NEG x)) = (POS x).
Proof.
Reflexivity.
Qed.

(** [opp] is involutive *)

Theorem Zopp_Zopp: (x:Z) (Zopp (Zopp x)) = x.
Proof.
NewDestruct x; Reflexivity.
Qed.

(** Injectivity of the opposite *)

Theorem Zopp_intro : (x,y:Z) (Zopp x) = (Zopp y) -> x = y.
Proof.
Intros x y;Case x;Case y;Simpl;Intros; [
  Trivial | Discriminate H | Discriminate H | Discriminate H
| Simplify_eq H; Intro E; Rewrite E; Trivial
| Discriminate H | Discriminate H | Discriminate H
| Simplify_eq H; Intro E; Rewrite E; Trivial ].
Qed.

(**********************************************************************)
(** Other properties of binary integer numbers *)

Hints Local Resolve compare_convert_O.

Lemma ZL0 : (S (S O))=(plus (S O) (S O)).
Proof.
Reflexivity.
Qed.

(** Addition on integers *)

Theorem Zero_left: (x:Z) (Zplus ZERO x) = x.
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

Hints Local Resolve Zero_left Zero_right.

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

Hints Local Resolve weak_assoc.

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

Theorem Zero_mult_left: (x:Z) (Zmult ZERO x) = ZERO.
Proof.
Induction x; Auto with arith.
Qed.

Theorem Zero_mult_right: (x:Z) (Zmult x ZERO) = ZERO.
Proof.
Induction x; Auto with arith.
Qed.

Hints Local Resolve Zero_mult_left Zero_mult_right.

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

Theorem Zcompare_EGAL : (x,y:Z) (Zcompare x y) = EGAL <-> x = y.
Proof.
Intros x y;Split; [
  Case x;Case y;Simpl;Auto with arith; Try (Intros;Discriminate H); [
    Intros x' y' H; Rewrite (compare_convert_EGAL y' x' H); Trivial with arith
  | Intros x' y' H; Rewrite (compare_convert_EGAL y' x'); [
      Trivial
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

Theorem Zcompare_Zopp :
  (x,y:Z) (Zcompare x y) = (Zcompare (Zopp y) (Zopp x)).
Proof.
(Intros x y;Case x;Case y;Simpl;Auto with arith);
Intros;Rewrite <- ZC4;Trivial with arith.
Qed.

Hints Local Resolve convert_compare_EGAL.

Theorem weaken_Zcompare_Zplus_compatible : 
  ((x,y:Z) (z:positive) 
    (Zcompare (Zplus (POS z) x) (Zplus (POS z) y)) = (Zcompare x y)) ->
   (x,y,z:Z) (Zcompare (Zplus z x) (Zplus z y)) = (Zcompare x y).
Proof.
Intro H; NewDestruct z; [
  Reflexivity
| Apply H
| Rewrite (Zcompare_Zopp x y); Rewrite Zcompare_Zopp; 
  Do 2 Rewrite Zopp_Zplus; Rewrite Zopp_NEG; Apply H ].
Qed.

Hints Local Resolve ZC4.

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

V7only [
  Comments "Compatibility with the old version of times and times_convert".
  Syntactic Definition times1 :=
    [x:positive;_:positive->positive;y:positive](times x y).
  Syntactic Definition times1_convert :=
    [x,y:positive;_:positive->positive](times_convert x y).
].
