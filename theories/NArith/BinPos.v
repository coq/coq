(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(**********************************************************************)
(** Binary positive numbers *)

(** Original version by Pierre Crégut, CNET, Lannion, France *)

Inductive positive : Set :=
  xI : positive -> positive
| xO : positive -> positive
| xH : positive.

(** Declare binding key for scope positive_scope *)

Delimits Scope positive_scope with positive.

(** Automatically open scope positive_scope for type positive, xO and xI *)

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
   Cases x of
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

(** Operation x -> 2*x-1 *)

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

V8Infix "-" true_sub : positive_scope.

(** Multiplication on binary positive numbers *)

Fixpoint times [x:positive] : positive -> positive:=
  [y:positive]
  Cases x of
    (xI x') => (add y (xO (times x' y)))
  | (xO x') => (xO (times x' y))
  | xH => y
  end.

V8Infix "*" times : positive_scope.

(** Division by 2 rounded below but for 1 *)

Definition Zdiv2_pos :=
  [z:positive]Cases z of xH => xH
                       | (xO p) => p
		       | (xI p) => p
		      end.

V8Infix "/" Zdiv2_pos : positive_scope.

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

V8Infix "?=" compare (at level 70, no associativity) : positive_scope.

(**********************************************************************)
(** Properties of comparison on binary positive numbers *)

Theorem compare_convert1 : 
 (x,y:positive) 
  ~(compare x y SUPERIEUR) = EGAL /\ ~(compare x y INFERIEUR) = EGAL.
Proof.
Intro x; NewInduction x as [p IHp|p IHp|]; Intro y; NewDestruct y as [q|q|];
  Split;Simpl;Auto;
  Discriminate Orelse (Elim (IHp q); Auto).
Qed.

Theorem compare_convert_EGAL : (x,y:positive) (compare x y EGAL) = EGAL -> x=y.
Proof.
Intro x; NewInduction x as [p IHp|p IHp|]; 
  Intro y; NewDestruct y as [q|q|];Simpl;Auto; Intro H; [
  Rewrite (IHp q); Trivial
| Absurd (compare p q SUPERIEUR)=EGAL ;
   [ Elim (compare_convert1 p q);Auto | Assumption ]
| Discriminate H
| Absurd (compare p q INFERIEUR) = EGAL; 
    [ Elim (compare_convert1 p q);Auto | Assumption ]
| Rewrite (IHp q);Auto 
| Discriminate H
| Discriminate H
| Discriminate H ].
Qed.

Lemma ZLSI:
 (x,y:positive) (compare x y SUPERIEUR) = INFERIEUR -> 
                (compare x y EGAL) = INFERIEUR.
Proof.
Intro x; Induction x;Intro y; Induction y;Simpl;Auto; 
  Discriminate Orelse Intros H;Discriminate H.
Qed.

Lemma ZLIS:
 (x,y:positive) (compare x y INFERIEUR) = SUPERIEUR -> 
                (compare x y EGAL) = SUPERIEUR.
Proof.
Intro x; Induction x;Intro y; Induction y;Simpl;Auto; 
  Discriminate Orelse Intros H;Discriminate H.
Qed.

Lemma ZLII:
 (x,y:positive) (compare x y INFERIEUR) = INFERIEUR ->
                (compare x y EGAL) = INFERIEUR \/ x = y.
Proof.
(Intro x; NewInduction x as [p IHp|p IHp|];
 Intro y; NewDestruct y as [q|q|];Simpl;Auto;Try Discriminate);
 Intro H2; Elim (IHp q H2);Auto; Intros E;Rewrite E;
 Auto.
Qed.

Lemma ZLSS:
 (x,y:positive) (compare x y SUPERIEUR) = SUPERIEUR ->
                (compare x y EGAL) = SUPERIEUR \/ x = y.
Proof.
(Intro x; NewInduction x as [p IHp|p IHp|];
 Intro y; NewDestruct y as [q|q|];Simpl;Auto;Try Discriminate);
 Intro H2; Elim (IHp q H2);Auto; Intros E;Rewrite E;
 Auto.
Qed.

Lemma Dcompare : (r:relation) r=EGAL \/ r = INFERIEUR \/ r = SUPERIEUR.
Proof.
Induction r; Auto. 
Qed.

Tactic Definition ElimPcompare c1 c2:=
  Elim (Dcompare (compare c1 c2 EGAL)); [ Idtac | 
     Let x = FreshId "H" In Intro x; Case x; Clear x ].

Theorem convert_compare_EGAL: (x:positive)(compare x x EGAL)=EGAL.
Intro x; Induction x; Auto.
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

Lemma xI_add_un_xO : (x:positive)(xI x) = (add_un (xO x)).
Proof.
Reflexivity.
Qed.

Lemma add_un_discr : (x:positive)x<>(add_un x).
Proof.
Intro x; NewDestruct x; Discriminate.
Qed.

(** Successor and double *)

Lemma is_double_moins_un : (x:positive) (add_un (double_moins_un x)) = (xO x).
Proof.
Intro x; NewInduction x as [x IHx|x|]; Simpl; Try Rewrite IHx; Reflexivity.
Qed.

Lemma double_moins_un_add_un_xI : 
 (x:positive)(double_moins_un (add_un x))=(xI x).
Proof.
Intro x;NewInduction x as [x IHx|x|]; Simpl; Try Rewrite IHx; Reflexivity.
Qed.

Lemma ZL1: (y:positive)(xO (add_un y)) = (add_un (add_un (xO y))).
Proof.
Intro y; Induction y; Simpl; Auto.
Qed.

Lemma double_moins_un_xO_discr : (x:positive)(double_moins_un x)<>(xO x).
Proof.
Intro x; NewDestruct x; Discriminate.
Qed.

(** Successor and predecessor *)

Lemma add_un_not_un : (x:positive) (add_un x) <> xH.
Proof.
Intro x; NewDestruct x as [x|x|]; Discriminate.
Qed.

Lemma sub_add_one : (x:positive) (sub_un (add_un x)) = x.
Proof.
(Intro x; NewDestruct x as [p|p|]; [Idtac | Idtac | Simpl;Auto]);
(NewInduction p as [p IHp||]; [Idtac | Reflexivity | Reflexivity ]);
Simpl; Simpl in IHp; Try Rewrite <- IHp; Reflexivity.
Qed.

Lemma add_sub_one : (x:positive) (x=xH) \/ (add_un (sub_un x)) = x.
Proof.
Intro x; Induction x; [
  Simpl; Auto
| Simpl; Intros;Right;Apply is_double_moins_un
| Auto ].
Qed.

(** Injectivity of successor *)

Lemma add_un_inj : (x,y:positive) (add_un x)=(add_un y) -> x=y.
Proof.
Intro x;NewInduction x; Intro y; NewDestruct y as [y|y|]; Simpl; 
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
Intro q; NewDestruct q; Reflexivity.
Qed.

Lemma ZL12bis: (q:positive) (add_un q) = (add xH q).
Proof.
Intro q; NewDestruct q; Reflexivity.
Qed.

(** Specification of [Pplus_carry] *)

Theorem ZL13: (x,y:positive)(add_carry x y) = (add_un (add x y)).
Proof.
(Intro x; NewInduction x as [p IHp|p IHp|];Intro y; NewDestruct y;Simpl;Auto);
  Rewrite IHp; Auto.
Qed.

(** Commutativity *)

Theorem add_sym : (x,y:positive) (add x y) = (add y x).
Proof.
Intro x; NewInduction x as [p IHp|p IHp|];Intro y; NewDestruct y;Simpl;Auto;
  Try Do 2 Rewrite ZL13; Rewrite IHp;Auto.
Qed. 

(** Permutation of [Pplus] and [Psucc] *)

Theorem ZL14: (x,y:positive)(add x (add_un y)) = (add_un (add x y)).
Proof.
Intro x; NewInduction x as [p IHp|p IHp|];Intro y; NewDestruct y;Simpl;Auto; [
  Rewrite ZL13; Rewrite IHp; Auto
| Rewrite ZL13; Auto
| NewDestruct p;Simpl;Auto
| Rewrite IHp;Auto
| NewDestruct p;Simpl;Auto ].
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
Intro x;NewInduction x; Intro y; NewDestruct y as [y|y|]; Simpl; Intro H;
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
  NewDestruct x as [x|x|]; Intro y; NewDestruct y as [y|y|]; Simpl; Intro H; 
  Discriminate H Orelse Try (Injection H; Clear H; Intro H).
    Rewrite IHz with 1:=(add_carry_add ? ? ? ? H); Reflexivity.
    Absurd (add_carry x z)=(add_un z);
      [ Apply add_carry_not_add_un | Assumption ].
    Rewrite IHz with 1:=H; Reflexivity.
    Symmetry in H; Absurd (add_carry y z)=(add_un z);
      [ Apply add_carry_not_add_un | Assumption ].
    Reflexivity.
  NewDestruct x as [x|x|]; Intro y; NewDestruct y as [y|y|]; Simpl; Intro H; 
  Discriminate H Orelse Try (Injection H; Clear H; Intro H).
    Rewrite IHz with 1:=H; Reflexivity.
    Absurd (add x z)=z; [ Apply add_no_neutral | Assumption ].
    Rewrite IHz with 1:=H; Reflexivity.
    Symmetry in H; Absurd y+z=z; [ Apply add_no_neutral | Assumption ].
    Reflexivity.
  Intros H x y; Apply add_un_inj; Do 2 Rewrite ZL12; Assumption.
Qed.

Lemma simpl_add_l : (x,y,z:positive) (add x y)=(add x z) -> y=z.
Proof.
Intros x y z H;Apply simpl_add_r with z:=x; 
  Rewrite add_sym with x:=z; Rewrite add_sym with x:=y; Assumption.
Qed.

Lemma simpl_add_carry_r :
 (x,y,z:positive) (add_carry x z)=(add_carry y z) -> x=y.
Proof.
Intros x y z H; Apply simpl_add_r with z:=z; Apply add_carry_add; Assumption.
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
NewInduction y as [y|y|]; Intro x.
  NewDestruct x as [x|x|]; 
    Intro z; NewDestruct z as [z|z|]; Simpl; Repeat Rewrite ZL13;
    Repeat Rewrite ZL14; Repeat Rewrite ZL14bis; Reflexivity Orelse
    Repeat Apply f_equal with A:=positive; Apply IHy.
  NewDestruct x as [x|x|]; 
    Intro z; NewDestruct z as [z|z|]; Simpl; Repeat Rewrite ZL13;
    Repeat Rewrite ZL14; Repeat Rewrite ZL14bis; Reflexivity Orelse
    Repeat Apply f_equal with A:=positive; Apply IHy.
  Intro z; Rewrite add_sym with x:=xH; Do 2 Rewrite <- ZL12; Rewrite ZL14bis; Rewrite ZL14; Reflexivity.
Qed.

(** Commutation of addition with the double of a positive number *)

Lemma add_xI_double_moins_un :
  (p,q:positive)(xO (add p q)) = (add (xI p) (double_moins_un q)).
Proof.
Intros; Change (xI p) with (add (xO p) xH).
Rewrite <- add_assoc; Rewrite <- ZL12bis; Rewrite is_double_moins_un.
Reflexivity.
Qed.

Lemma add_xO_double_moins_un :
 (p,q:positive) (double_moins_un (add p q)) = (add (xO p) (double_moins_un q)).
Proof.
NewInduction p as [p IHp|p IHp|]; NewDestruct q as [q|q|];
 Simpl; Try Rewrite ZL13; Try Rewrite double_moins_un_add_un_xI;
 Try Rewrite IHp; Try Rewrite add_xI_double_moins_un; Try Reflexivity.
 Rewrite <- is_double_moins_un; Rewrite ZL12bis; Reflexivity. 
Qed.

(** Misc *)

Lemma add_x_x : (x:positive) (add x x) = (xO x).
Proof.
Intro x;NewInduction x; Simpl; Try Rewrite ZL13; Try Rewrite IHx; Reflexivity.
Qed.

(**********************************************************************)
(** Peano induction on binary positive positive numbers *)

Fixpoint plus_iter [x:positive] : positive -> positive := 
  [y]Cases x of 
  | xH => (add_un y)
  | (xO x) => (plus_iter x (plus_iter x y))
  | (xI x) => (plus_iter x (plus_iter x (add_un y)))
  end.

Lemma plus_iter_add : (x,y:positive)(plus_iter x y)=(add x y).
Proof.
Intro x;NewInduction x as [p IHp|p IHp|]; Intro y; NewDestruct y; Simpl;
  Reflexivity Orelse Do 2 Rewrite IHp; Rewrite add_assoc; Rewrite add_x_x;
  Try Reflexivity.
Rewrite ZL13; Rewrite <- ZL14; Reflexivity.
Rewrite ZL12; Reflexivity.
Qed.

Lemma plus_iter_xO : (x:positive)(plus_iter x x)=(xO x).
Proof.
Intro; Rewrite <- add_x_x; Apply plus_iter_add.
Qed.

Lemma plus_iter_xI : (x:positive)(add_un (plus_iter x x))=(xI x).
Proof.
Intro; Rewrite xI_add_un_xO; Rewrite <- add_x_x; 
  Apply (f_equal positive); Apply plus_iter_add.
Qed.

Lemma iterate_add : (P:(positive->Type))
  ((n:positive)(P n) ->(P (add_un n)))->(p,n:positive)(P n) ->
  (P (plus_iter p n)).
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
Intros P H1 Hsucc n; NewInduction n.
Rewrite <- plus_iter_xI; Apply Hsucc; Apply iterate_add; Assumption.
Rewrite <- plus_iter_xO; Apply iterate_add; Assumption.
Assumption.
Qed.

(** Peano recursion *)

Definition Prec : (A:Set)A->(positive->A->A)->positive->A :=
  [A;a;f]Fix Prec { Prec [p:positive] : A :=
  Cases p of
  | xH => a
  | (xO p) => (iterate_add [_]A f p p (Prec p))
  | (xI p) => (f (plus_iter p p) (iterate_add [_]A f p p (Prec p)))
  end}.

(** Test *)

Check
 let fact = (Prec positive xH [p;r](times (add_un p) r)) in
 let seven = (xI (xI xH)) in
 let five_thousand_forty= (xO(xO(xO(xO(xI(xI(xO(xI(xI(xI(xO(xO xH))))))))))))
 in ((refl_equal ? ?) :: (fact seven) = five_thousand_forty).

(**********************************************************************)
(** Properties of subtraction on binary positive numbers *)

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
Intro x; NewInduction x as [p IHp|p IHp|]; [
  Simpl; Rewrite IHp;Simpl; Trivial
| Simpl; Rewrite IHp;Auto
| Auto ].
Qed.

Lemma ZL10: (x,y:positive)
 (sub_pos x y) = (IsPos xH) -> (sub_neg x y) = IsNul.
Proof.
Intro x; NewInduction x as [p|p|]; Intro y; NewDestruct y as [q|q|]; Simpl; 
  Intro H; Try Discriminate H; [
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

(** Properties valid only for x>y *)

Lemma sub_pos_SUPERIEUR:
  (x,y:positive)(compare x y EGAL)=SUPERIEUR -> 
    (EX h:positive | (sub_pos x y) = (IsPos h) /\ (add y h) = x /\
                     (h = xH \/ (sub_neg x y) = (IsPos (sub_un h)))).
Proof.
Intro x;NewInduction x as [p|p|];Intro y; NewDestruct y as [q|q|]; Simpl; Intro H;
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
Require Gt.
Require Plus.
Require Mult.
Require Minus.

(** [nat_of_P] is a morphism for addition *)

Lemma convert_add_un :
  (x:positive)(m:nat)
    (positive_to_nat (add_un x) m) = (plus m (positive_to_nat x m)).
Proof.
Intro x; NewInduction x as [p IHp|p IHp|]; Simpl; Auto; Intro m; Rewrite IHp;
Rewrite plus_assoc_l; Trivial.
Qed.

Lemma cvt_add_un :
  (p:positive) (convert (add_un p)) = (S (convert p)).
Proof.
  Intro; Change (S (convert p)) with (plus (S O) (convert p));
  Unfold convert; Apply convert_add_un.
Qed.

Theorem convert_add_carry :
  (x,y:positive)(m:nat)
    (positive_to_nat (add_carry x y) m) =
    (plus m (positive_to_nat (add x y) m)).
Proof.
Intro x; NewInduction x as [p IHp|p IHp|];
  Intro y; NewDestruct y; Simpl; Auto with arith; Intro m; [
  Rewrite IHp; Rewrite plus_assoc_l; Trivial with arith
| Rewrite IHp; Rewrite plus_assoc_l; Trivial with arith
| Rewrite convert_add_un; Rewrite plus_assoc_l; Trivial with arith
| Rewrite convert_add_un; Apply plus_assoc_r ].
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
Intro x; NewInduction x as [p IHp|p IHp|];
  Intro y; NewDestruct y;Simpl;Auto with arith; [
  Intros m;Rewrite convert_add_carry; Rewrite IHp; 
  Rewrite plus_assoc_r; Rewrite plus_assoc_r; 
  Rewrite (plus_permute m (positive_to_nat p (plus m m))); Trivial with arith
| Intros m; Rewrite IHp; Apply plus_assoc_l
| Intros m; Rewrite convert_add_un; 
  Rewrite (plus_sym (plus m (positive_to_nat p (plus m m))));
  Apply plus_assoc_r
| Intros m; Rewrite IHp; Apply plus_permute
| Intros m; Rewrite convert_add_un; Apply plus_assoc_r ].
Qed.

Theorem convert_add:
  (x,y:positive) (convert (add x y)) = (plus (convert x) (convert y)).
Proof.
Intros x y; Exact (add_verif x y (S O)).
Qed.

(** [Pmult_nat] is a morphism for addition *)

Lemma ZL2:
  (y:positive)(m:nat)
    (positive_to_nat y (plus m m)) =
              (plus (positive_to_nat y m) (positive_to_nat y m)).
Proof.
Intro y; NewInduction y as [p H|p H|]; Intro m; [
  Simpl; Rewrite H; Rewrite plus_assoc_r; 
  Rewrite (plus_permute m (positive_to_nat p (plus m m)));
  Rewrite plus_assoc_r; Auto with arith
| Simpl; Rewrite H; Auto with arith
| Simpl; Trivial with arith ].
Qed.

Lemma ZL6:
  (p:positive) (positive_to_nat p (S (S O))) = (plus (convert p) (convert p)).
Proof.
Intro p;Change (2) with (plus (S O) (S O)); Rewrite ZL2; Trivial.
Qed.
 
(** [nat_of_P] is a morphism for multiplication *)

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
V7only [
  Comments "Compatibility with the old version of times and times_convert".
  Syntactic Definition times1 :=
    [x:positive;_:positive->positive;y:positive](times x y).
  Syntactic Definition times1_convert :=
    [x,y:positive;_:positive->positive](times_convert x y).
].

(** [nat_of_P] is strictly positive *)

Lemma compare_positive_to_nat_O : 
	(p:positive)(m:nat)(le m (positive_to_nat p m)).
NewInduction p; Simpl; Auto with arith.
Intro m; Apply le_trans with (plus m m);  Auto with arith.
Qed.

Lemma compare_convert_O : (p:positive)(lt O (convert p)).
Intro; Unfold convert; Apply lt_le_trans with (S O); Auto with arith.
Apply compare_positive_to_nat_O.
Qed.

(** Pmult_nat permutes with multiplication *)

Lemma positive_to_nat_mult : (p:positive) (n,m:nat)
    (positive_to_nat p (mult m n))=(mult m (positive_to_nat p n)).
Proof.
  Induction p. Intros. Simpl. Rewrite mult_plus_distr_r. Rewrite <- (mult_plus_distr_r m n n).
  Rewrite (H (plus n n) m). Reflexivity.
  Intros. Simpl. Rewrite <- (mult_plus_distr_r m n n). Apply H.
  Trivial.
Qed.

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

(** Mapping of xH, xO and xI through [nat_of_P] *)

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

(** Composition of [P_of_succ_nat] and [nat_of_P] is successor on [nat] *)

Theorem bij1 : (m:nat) (convert (anti_convert m)) = (S m).
Proof.
Intro m; NewInduction m as [|n H]; [
  Reflexivity
| Simpl; Rewrite cvt_add_un; Rewrite H; Auto ].
Qed.

(** Miscellaneous lemmas on [P_of_succ_nat] *)

Lemma ZL3: (x:nat) (add_un (anti_convert (plus x x))) =  (xO (anti_convert x)).
Proof.
Intro x; NewInduction x as [|n H]; [
  Simpl; Auto with arith
| Simpl; Rewrite  plus_sym; Simpl; Rewrite  H; Rewrite  ZL1;Auto with arith].
Qed.

Lemma ZL4: (y:positive) (EX h:nat |(convert y)=(S h)).
Proof.
Intro y; NewInduction y as [p H|p H|]; [
  NewDestruct H as [x H1]; Exists (plus (S x) (S x));
  Unfold convert ;Simpl; Change (2) with (plus (1) (1)); Rewrite ZL2; Unfold convert in H1;
  Rewrite H1; Auto with arith
| NewDestruct H as [x H2]; Exists (plus x (S x)); Unfold convert;
  Simpl; Change (2) with (plus (1) (1)); Rewrite ZL2;Unfold convert in H2; Rewrite H2; Auto with arith
| Exists O ;Auto with arith ].
Qed.

Lemma ZL5: (x:nat) (anti_convert (plus (S x) (S x))) =  (xI (anti_convert x)).
Proof.
Intro x; NewInduction x as [|n H];Simpl; [
  Auto with arith
| Rewrite <- plus_n_Sm; Simpl; Simpl in H; Rewrite H; Auto with arith].
Qed.

(** Composition of [nat_of_P] and [P_of_succ_nat] is successor on [positive] *)

Theorem bij2 : (x:positive) (anti_convert (convert x)) = (add_un x).
Proof.
Intro x; NewInduction x as [p H|p H|]; [
  Simpl; Rewrite <- H; Change (2) with (plus (1) (1));
  Rewrite ZL2; Elim (ZL4 p); 
  Unfold convert; Intros n H1;Rewrite H1; Rewrite ZL3; Auto with arith
| Unfold convert ;Simpl; Change (2) with (plus (1) (1));
  Rewrite ZL2;
  Rewrite <- (sub_add_one
               (anti_convert
                 (plus (positive_to_nat p (S O)) (positive_to_nat p (S O)))));
  Rewrite <- (sub_add_one (xI p));
  Simpl;Rewrite <- H;Elim (ZL4 p); Unfold convert ;Intros n H1;Rewrite H1;
  Rewrite ZL5; Simpl; Trivial with arith
| Unfold convert; Simpl; Auto with arith ].
Qed.

(** Composition of [nat_of_P], [P_of_succ_nat] and [Ppred] is identity
    on [positive] *)

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

(** [nat_of_P] is a morphism from [positive] to [nat] for [lt] (expressed
    from [compare] on [positive])

    Part 1: [lt] on [positive] is finer than [lt] on [nat]
*)

Lemma compare_convert_INFERIEUR : 
  (x,y:positive) (compare x y EGAL) = INFERIEUR -> 
    (lt (convert x) (convert y)).
Proof.
Intro x; NewInduction x as [p H|p H|];Intro y; NewDestruct y as [q|q|];
  Intro H2; [
  Unfold convert ;Simpl; Apply lt_n_S; 
  Do 2 Rewrite ZL6; Apply ZL7; Apply H; Simpl in H2; Assumption
| Unfold convert ;Simpl; Do 2 Rewrite ZL6; 
  Apply ZL8; Apply H;Simpl in H2; Apply ZLSI;Assumption
| Simpl; Discriminate H2
| Simpl; Unfold convert ;Simpl;Do 2 Rewrite ZL6; 
  Elim (ZLII p q H2); [
    Intros H3;Apply lt_S;Apply ZL7; Apply H;Apply H3
  | Intros E;Rewrite E;Apply lt_n_Sn]
| Simpl; Unfold convert ;Simpl;Do 2 Rewrite ZL6; 
  Apply ZL7;Apply H;Assumption
| Simpl; Discriminate H2
| Unfold convert ;Simpl; Apply lt_n_S; Rewrite ZL6;
  Elim (ZL4 q);Intros h H3; Rewrite H3;Simpl; Apply lt_O_Sn
| Unfold convert ;Simpl; Rewrite ZL6; Elim (ZL4 q);Intros h H3;
  Rewrite H3; Simpl; Rewrite <- plus_n_Sm; Apply lt_n_S; Apply lt_O_Sn
| Simpl; Discriminate H2 ].
Qed.

(** [nat_of_P] is a morphism from [positive] to [nat] for [gt] (expressed
    from [compare] on [positive])

    Part 1: [gt] on [positive] is finer than [gt] on [nat]
*)

Lemma compare_convert_SUPERIEUR : 
  (x,y:positive) (compare x y EGAL)=SUPERIEUR -> (gt (convert x) (convert y)).
Proof.
Unfold gt; Intro x; NewInduction x as [p H|p H|];
  Intro y; NewDestruct y as [q|q|]; Intro H2; [
  Simpl; Unfold convert ;Simpl;Do 2 Rewrite ZL6; 
  Apply lt_n_S; Apply ZL7; Apply H;Assumption
| Simpl; Unfold convert ;Simpl; Do 2 Rewrite ZL6;
  Elim (ZLSS p q H2); [
    Intros H3;Apply lt_S;Apply ZL7;Apply H;Assumption
  | Intros E;Rewrite E;Apply lt_n_Sn]
| Unfold convert ;Simpl; Rewrite ZL6;Elim (ZL4 p);
  Intros h H3;Rewrite H3;Simpl; Apply lt_n_S; Apply lt_O_Sn
| Simpl;Unfold convert ;Simpl;Do 2 Rewrite ZL6; 
  Apply ZL8; Apply H; Apply ZLIS; Assumption
| Simpl; Unfold convert ;Simpl;Do 2 Rewrite ZL6; 
  Apply ZL7;Apply H;Assumption
| Unfold convert ;Simpl; Rewrite ZL6; Elim (ZL4 p);
  Intros h H3;Rewrite H3;Simpl; Rewrite <- plus_n_Sm;Apply lt_n_S;
  Apply lt_O_Sn
| Simpl; Discriminate H2
| Simpl; Discriminate H2
| Simpl; Discriminate H2 ].
Qed.

(** [nat_of_P] is a morphism from [positive] to [nat] for [lt] (expressed
    from [compare] on [positive])

    Part 2: [lt] on [nat] is finer than [lt] on [positive]
*)

Lemma convert_compare_INFERIEUR : 
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

(** [nat_of_P] is a morphism from [positive] to [nat] for [gt] (expressed
    from [compare] on [positive])

    Part 2: [gt] on [nat] is finer than [gt] on [positive]
*)

Lemma convert_compare_SUPERIEUR : 
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
Intros x y;ElimPcompare y x; 
Intros E;Rewrite E;Simpl; [Apply ZC3 | Apply ZC2 | Apply ZC1 ]; Assumption.
Qed.

(**********************************************************************)
(** Extra properties of the injection from binary positive numbers to Peano 
    natural numbers *)

(** [nat_of_P] is a morphism for subtraction on positive numbers *)

Theorem true_sub_convert:
  (x,y:positive) (compare x y EGAL) = SUPERIEUR -> 
     (convert (true_sub x y)) = (minus (convert x) (convert y)).
Proof.
Intros x y H; Apply plus_reg_l with (convert y);
Rewrite le_plus_minus_r; [
  Rewrite <- convert_add; Rewrite sub_add; Auto with arith
| Apply lt_le_weak; Exact (compare_convert_SUPERIEUR x y H)].
Qed.

(** [nat_of_P] is injective *)

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

(** Comparison and subtraction *)

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
Intros p q z; Intros; 
  Apply convert_compare_INFERIEUR; Rewrite true_sub_convert; [
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
Intro x;NewInduction x; Simpl.
  Rewrite IHx; Reflexivity.
  Rewrite IHx; Reflexivity.
  Reflexivity.
Qed.

(** Right reduction properties for multiplication *)

Lemma times_x_double : (x,y:positive) (times x (xO y)) = (xO (times x y)).
Proof.
Intros x y; NewInduction x; Simpl.
  Rewrite IHx; Reflexivity.
  Rewrite IHx; Reflexivity.
  Reflexivity.
Qed.

Lemma times_x_double_plus_one :
 (x,y:positive) (times x (xI y)) = (add x (xO (times x y))).
Proof.
Intros x y; NewInduction x; Simpl.
  Rewrite IHx; Do 2 Rewrite add_assoc; Rewrite add_sym with x:=y; Reflexivity.
  Rewrite IHx; Reflexivity.
  Reflexivity.
Qed.

(** Commutativity of multiplication *)

Theorem times_sym : (x,y:positive) (times x y) = (times y x).
Proof.
Intros x y; NewInduction y; Simpl.
  Rewrite <- IHy; Apply times_x_double_plus_one.
  Rewrite <- IHy; Apply times_x_double.
  Apply times_x_1.
Qed.

(** Distributivity of multiplication over addition *)

Theorem times_add_distr:
  (x,y,z:positive) (times x (add y z)) = (add (times x y) (times x z)).
Proof.
Intros x y z; NewInduction x; Simpl.
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
Intro x;NewInduction x as [x|x|]; Simpl; Intros y z.
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

Lemma times_discr_xO_xI : 
  (x,y,z:positive)(times (xI x) z)<>(times (xO y) z).
Proof.
Intros x y z; NewInduction z as [|z IHz|]; Try Discriminate.
Intro H; Apply IHz; Clear IHz.
Do 2 Rewrite times_x_double in H.
Injection H; Clear H; Intro H; Exact H.
Qed.

Lemma times_discr_xO : (x,y:positive)(times (xO x) y)<>y.
Proof.
Intros x y; NewInduction y; Try Discriminate.
Rewrite times_x_double; Injection; Assumption.
Qed.

(** Simplification properties of multiplication *)

Theorem simpl_times_r : (x,y,z:positive) (times x z)=(times y z) -> x=y.
Proof.
Intro x;NewInduction x as [p IHp|p IHp|]; Intro y; NewDestruct y as [q|q|]; Intros z H;
    Reflexivity Orelse Apply (f_equal positive) Orelse Apply False_ind.
  Simpl in H; Apply IHp with (xO z); Simpl; Do 2 Rewrite times_x_double;
    Apply simpl_add_l with 1 := H.
  Apply times_discr_xO_xI with 1 := H.
  Simpl in H; Rewrite add_sym in H; Apply add_no_neutral with 1 := H.
  Symmetry in H; Apply times_discr_xO_xI with 1 := H.
  Apply IHp with (xO z); Simpl; Do 2 Rewrite times_x_double; Assumption.
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
