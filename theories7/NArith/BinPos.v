(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(**********************************************************************)
(** Binary positive numbers *)

(** Original development by Pierre Crégut, CNET, Lannion, France *)

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

(** Peano case analysis *)

Theorem Pcase : (P:(positive->Prop))
  (P xH) ->((n:positive)(P (add_un n))) ->(n:positive)(P n).
Proof.
Intros; Apply Pind; Auto.
Qed.

Check
 let fact = (Prec positive xH [p;r](times (add_un p) r)) in
 let seven = (xI (xI xH)) in
 let five_thousand_forty= (xO(xO(xO(xO(xI(xI(xO(xI(xI(xI(xO(xO xH))))))))))))
 in ((refl_equal ? ?) :: (fact seven) = five_thousand_forty).

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

(** Inversion of multiplication *)

Lemma times_one_inversion_l : (x,y:positive) (times x y)=xH -> x=xH.
Proof.
Intros x y; NewDestruct x; Simpl.
 NewDestruct y; Intro; Discriminate.
 Intro; Discriminate.
 Reflexivity.
Qed.

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

Lemma Pcompare_antisym :
  (x,y:positive)(r:relation) (Op (compare x y r)) = (compare y x (Op r)).
Proof.
Intro x; NewInduction x as [p IHp|p IHp|]; Intro y; NewDestruct y; 
Intro r; Reflexivity Orelse (Symmetry; Assumption) Orelse Discriminate H
Orelse Simpl; Apply IHp Orelse Try Rewrite IHp; Try Reflexivity.
Qed.

Lemma ZC1:
  (x,y:positive)(compare x y EGAL)=SUPERIEUR -> (compare y x EGAL)=INFERIEUR.
Proof.
Intros; Change EGAL with (Op EGAL).
Rewrite <- Pcompare_antisym; Rewrite H; Reflexivity.
Qed.

Lemma ZC2:
  (x,y:positive)(compare x y EGAL)=INFERIEUR -> (compare y x EGAL)=SUPERIEUR.
Proof.
Intros; Change EGAL with (Op EGAL).
Rewrite <- Pcompare_antisym; Rewrite H; Reflexivity.
Qed.

Lemma ZC3: (x,y:positive)(compare x y EGAL)=EGAL -> (compare y x EGAL)=EGAL.
Proof.
Intros; Change EGAL with (Op EGAL).
Rewrite <- Pcompare_antisym; Rewrite H; Reflexivity.
Qed.

Lemma ZC4: (x,y:positive) (compare x y EGAL) = (Op (compare y x EGAL)).
Proof.
Intros; Change 1 EGAL with (Op EGAL).
Symmetry; Apply Pcompare_antisym.
Qed.

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

(** Properties of subtraction valid only for x>y *)

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

