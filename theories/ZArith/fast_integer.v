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

Require Export BinPos.
Require Le.
Require Lt.
Require Gt.
Require Plus.
Require Mult.

V7only [Notation relation := Datatypes.relation.].

(**********************************************************************)
(** Binary integer numbers *)

Inductive Z : Set := 
  ZERO : Z | POS : positive -> Z | NEG : positive -> Z.

(** Declare Scope Z_scope with Key Z *)
Delimits Scope Z_scope with Z.

(** Automatically open scope positive_scope for the constructors of Z *)
Bind Scope Z_scope with Z.
Arguments Scope POS [ positive_scope ].
Arguments Scope NEG [ positive_scope ].

(** Subtraction of positive into Z *)

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

(** Addition on integers *)

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

(** Successor on integers *)

Definition Zs := [x:Z](Zplus x (POS xH)).

(** Predecessor on integers *)

Definition Zpred := [x:Z](Zplus x (NEG xH)).

(** Subtraction on integers *)

Definition Zminus := [m,n:Z](Zplus m (Zopp n)).

V8Infix "-" Zminus : Z_scope.

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

V8Infix "?=" Zcompare (at level 70, no associativity) : Z_scope.

Tactic Definition ElimCompare com1 com2:=
  Case (Dcompare (Zcompare com1 com2)); [ Idtac | 
     Let x = FreshId "H" In Intro x; Case x; Clear x ].

(** Sign function *)

Definition Zsgn [z:Z] : Z :=
  Cases z of 
     ZERO   => ZERO
  | (POS p) => (POS xH)
  | (NEG p) => (NEG xH)
  end.

(** Easier to handle variants of successor and addition *)

Definition Zs' [x:Z] :=
  Cases x of
  | ZERO => (POS xH)
  | (POS x') => (POS (add_un x'))
  | (NEG x') => (Zsub_pos xH x')
  end.

Definition Zpred' [x:Z] :=
  Cases x of
  | ZERO => (NEG xH)
  | (POS x') => (Zsub_pos x' xH)
  | (NEG x') => (NEG (add_un x'))
  end.

Definition Zplus' := [x,y:Z]
  Cases x y of
    ZERO      y       => y
  | x         ZERO    => x
  | (POS x') (POS y') => (POS (add x' y'))
  | (POS x') (NEG y') => (Zsub_pos x' y')
  | (NEG x') (POS y') => (Zsub_pos y' x')
  | (NEG x') (NEG y') => (NEG (add x' y'))
  end.

Open Local Scope Z_scope.

(**********************************************************************)
(** Inductive specification of Z *)

Theorem Zind : (P:(Z ->Prop))
  (P ZERO) -> ((x:Z)(P x) ->(P (Zs' x))) -> ((x:Z)(P x) ->(P (Zpred' x))) ->
     (z:Z)(P z).
Proof.
Intros P H0 Hs Hp; NewDestruct z.
  Assumption.
  Apply Pind with P:=[p](P (POS p)).
    Change (P (Zs' ZERO)); Apply Hs; Apply H0.
    Intro n; Exact (Hs (POS n)).
  Apply Pind with P:=[p](P (NEG p)).
    Change (P (Zpred' ZERO)); Apply Hp; Apply H0.
    Intro n; Exact (Hp (NEG n)).
Qed.

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
(** Properties of the double of an integer *)

Lemma Zopp_Zdouble : (x:Z) (Zopp (Zdouble x))=(Zdouble (Zopp x)).
Proof.
NewDestruct x as [|p|p]; Reflexivity.
Qed.

Lemma Zopp_Zdouble_plus_one :
  (x:Z) (Zopp (Zdouble_plus_one x))=(Zdouble_minus_one (Zopp x)).
Proof.
NewDestruct x as [|p|p]; Reflexivity.
Qed.

Lemma Zopp_Zdouble_minus_one :
  (x:Z) (Zopp (Zdouble_minus_one x))=(Zdouble_plus_one (Zopp x)).
Proof.
NewDestruct x as [|p|p]; Reflexivity.
Qed.

Lemma Zdouble_minus_one_spec :
  (x:Z)(Zdouble_minus_one x) = (Zplus (Zdouble x) (NEG xH)).
Proof.
NewDestruct x as [|p|p]; Reflexivity Orelse Exact (POS_Zdouble_minus_one p).
Qed.

Lemma Zdouble_minus_one_add_un_xI :
 (x:positive) (Zdouble_minus_one (POS (add_un x))) = (POS (xI x)).
Proof.
NewDestruct x; Simpl; Try Rewrite double_moins_un_add_un_xI; Reflexivity.
Qed.

(** Permutations *)

Lemma Zdouble_plus_one_Zdouble :
  (x:Z)(Zdouble_plus_one (Zdouble x))=(Zdouble_minus_one (Zdouble_plus_one x)).
Proof.
NewDestruct x; Reflexivity.
Qed.

Lemma Zdouble_plus_one_Zdouble_minus_one :
 (x:Z)(Zdouble_plus_one (Zdouble_minus_one x))=(Zdouble_minus_one (Zdouble x)).
Proof.
NewDestruct x; Reflexivity.
Qed.

Lemma Zdouble_plus_one_spec :
  (x:Z)(Zdouble_plus_one x)=(Zplus (Zdouble x) (POS xH)).
Proof.
  NewDestruct x; Reflexivity.
Qed.

Lemma Zdouble_plus_one_Zdouble_minus_one_one :
  (x:Z)(Zdouble_plus_one x)=(Zdouble_minus_one (Zs' x)).
Proof.
NewDestruct x; Simpl.
  Reflexivity.
  Rewrite -> double_moins_un_add_un_xI; Reflexivity.
  NewDestruct p; Reflexivity.
Qed.

Lemma Zdouble_one_one_Zdouble_plus_one:
  (x:Z)(Zdouble (Zs' x)) = (Zs' (Zdouble_plus_one x)).
Proof.
NewDestruct x as [|p|p]; Try Reflexivity.
  NewDestruct p; Reflexivity.
Qed.

(**********************************************************************)
(** Properties of the subtraction from positive to integers *)

Infix Local 4 "--" Zsub_pos : Z_scope.

Lemma Zsub_pos_x_x : (x:positive) x--x = ZERO.
Proof.
NewInduction x as [p IHp|p IHp|]; Simpl; Try Rewrite IHp; Reflexivity.
Qed.

Lemma Zopp_Zsub_pos : (x,y:positive) (Zopp (x--y)) = y--x.
Proof.
NewInduction x as [p IHp|p IHp|]; NewDestruct y as [q|q|]; Simpl; 
  Try Rewrite <- IHp; Try Reflexivity.
  Apply Zopp_Zdouble.
  Apply Zopp_Zdouble_plus_one.
  Apply Zopp_Zdouble_minus_one.
  Apply Zopp_Zdouble.
Qed.

Lemma Zsub_pos_add_un_permute : 
  (x,y:positive)(add_un x)--y = (Zs' (x--y)).
Proof.
NewInduction x as [x IHx|x|]; NewDestruct y as [y|y|]; Simpl.
  (* xI/xI *)
  Rewrite IHx; Simpl.
  NewDestruct (Zsub_pos x y); Simpl; Try Reflexivity.
    NewDestruct p; Simpl; Try Reflexivity.
      Rewrite double_moins_un_add_un_xI; Reflexivity.
    NewDestruct p; Reflexivity.
  (* xI/xO *)
  Rewrite IHx; Simpl.
  NewDestruct (Zsub_pos x y); Simpl; Try Reflexivity.
    NewDestruct p; Reflexivity.
  Rewrite double_moins_un_add_un_xI; Reflexivity.
  (* xO/xI *)
  NewDestruct (Zsub_pos x y); Simpl; Try Reflexivity.
  NewDestruct p; Simpl; Try Rewrite is_double_moins_un; Reflexivity.
  (* xO/xO *)
  NewDestruct (Zsub_pos x y); Simpl; Reflexivity.
  (* xO/xH *)
  NewDestruct x; Simpl; Try Reflexivity.
  Rewrite is_double_moins_un; Reflexivity.
  (* xH/xI *)
  NewDestruct y; Reflexivity.
  (* xH/xO *)
  NewDestruct y; Reflexivity.
  (* xH/xH *)
  Reflexivity.
Qed.

Lemma Zsub_pos_add_un_permute_Zopp :
  (x,y:positive) x--(add_un y) = (Zopp (Zs' (Zopp (x--y)))).
Proof.
Intros.
Rewrite Zopp_Zsub_pos; Rewrite <- Zopp_Zsub_pos; 
Rewrite Zsub_pos_add_un_permute; Reflexivity.
Qed.

Lemma Zsub_pos_double_moins_un_xO_add_un :
 (x,y:positive)(Zsub_pos (double_moins_un x) y) = (Zsub_pos (xO x) (add_un y)).
Proof.
NewInduction x as [p IHp|p|]; NewDestruct y as [q|q|]; Simpl;
  Try Rewrite -> IHp; Try Reflexivity.
  Rewrite Zsub_pos_add_un_permute_Zopp;
      Change (xI p) with (add_un (xO p));
      Rewrite Zsub_pos_add_un_permute;
      NewDestruct (Zsub_pos (xO p) q).
    Reflexivity.
    NewDestruct p0; Simpl; Try Rewrite double_moins_un_add_un_xI; Reflexivity.
    NewDestruct p0; Simpl; Try Rewrite is_double_moins_un; Try Reflexivity.
  NewDestruct q; Simpl.
    Rewrite Zdouble_plus_one_Zdouble_minus_one; Reflexivity.
    Rewrite Zdouble_plus_one_Zdouble; Reflexivity.
    Reflexivity.
  Rewrite Zsub_pos_add_un_permute_Zopp; Simpl; 
      NewDestruct (Zsub_pos (xO p) q); Simpl.
    Reflexivity.
    NewDestruct p0; Reflexivity.
    Rewrite double_moins_un_add_un_xI; Reflexivity.
  Rewrite Zsub_pos_add_un_permute_Zopp; Simpl;
    NewDestruct q; Simpl; Try Rewrite is_double_moins_un; Reflexivity.
  NewDestruct q; Reflexivity.
Qed.

Lemma Zdouble_minus_one_Zsub_pos :
  (x,y:positive)(Zdouble_minus_one (Zsub_pos x y))
     = (Zsub_pos (double_moins_un x) (xO y)).
Proof.
Intros; Rewrite Zsub_pos_double_moins_un_xO_add_un; Reflexivity.
Qed.

Lemma Zdouble_plus_one_Zsub_pos :
  (x,y:positive)(Zdouble_plus_one (x--y)) = (xO x)--(double_moins_un y).
Proof.
Intros; Rewrite <- Zopp_Zsub_pos with y := (xO x);
Rewrite <- Zdouble_minus_one_Zsub_pos;
Rewrite <- Zopp_Zsub_pos with y := y;
Rewrite <- Zopp_Zdouble_plus_one;
Rewrite Zopp_Zopp;
Reflexivity.
Qed.

Lemma Zsub_pos_xI_double_moins_un :
  (x,y:positive)
  (Zdouble (Zs' (Zsub_pos x y))) = (Zsub_pos (xI x) (double_moins_un y)).
Proof.
Intros; Change (xI x) with (add_un (xO x));
Rewrite -> Zsub_pos_add_un_permute; Rewrite <- Zdouble_plus_one_Zsub_pos.
Apply Zdouble_one_one_Zdouble_plus_one.
Qed.

Lemma Zpred'_Zs' : (x:Z)(Zpred' (Zs' x))=x.
Proof.
NewDestruct x; Simpl.
  Reflexivity.
NewDestruct p; Simpl; Try Rewrite double_moins_un_add_un_xI; Reflexivity.
NewDestruct p; Simpl; Try Rewrite is_double_moins_un; Reflexivity.
Qed.

Lemma add_un_discr : (x:positive)(add_un x)<>x.
Proof.
NewDestruct x; Discriminate.
Qed.

Lemma double_moins_un_xO_discr : (x:positive)(double_moins_un x)<>(xO x).
Proof.
NewDestruct x; Discriminate.
Qed.

Lemma Z0_Zs'_discr : (x:Z)(Zs' x)<>x.
Proof.
NewDestruct x; Simpl.
  Discriminate.
  Injection; Apply add_un_discr.
  NewDestruct p; Simpl.
    Discriminate.
    Injection; Apply double_moins_un_xO_discr.
    Discriminate.
Qed.

(**********************************************************************)
(** Other properties of binary integer numbers *)

Hints Local Resolve compare_convert_O.

Lemma ZL0 : (S (S O))=(plus (S O) (S O)).
Proof.
Reflexivity.
Qed.

(**********************************************************************)
(** Properties of the addition on integers *)

(** zero is left neutral for addition *)

Theorem Zero_left: (x:Z) (Zplus ZERO x) = x.
Proof.
NewDestruct x; Reflexivity.
Qed.

(** zero is right neutral for addition *)

Theorem Zero_right: (x:Z) (Zplus x ZERO) = x.
Proof.
NewDestruct x; Reflexivity.
Qed.

(*
Lemma Zplus_S'_n: (x,y:Z) (Zplus (Zs' x) y) = (Zs' (Zplus x y)).
Proof.
NewInduction x; NewDestruct y; Simpl.
  Reflexivity.
  NewDestruct p; Simpl; Reflexivity.
  NewDestruct p; Try Unfold true_sub; Simpl; Reflexivity.
  Reflexivity. 
  Rewrite ZL14bis; Reflexivity.
  Case (Dcompare (compare (add_un p) p0 EGAL)); Intro H; Try Rewrite H. 
    Rewrite <- (compare_convert_EGAL ? ? H); Clear H.    
    NewDestruct p; Simpl.
   Case (Dcompare (compare p (add_un p) EGAL)); Intro H'; Try Rewrite H'; Try Reflexivity.
      Assert H'' := (compare_convert_EGAL ? ? H').
      Symmetry in H''.
      Elim (add_un_discr p H'').
   Elim H'; Clear H'; Intro H.
   Case (Dcompare (compare p (add_un p) EGAL)); Intro H'; Try Rewrite H'; Try Reflexivity.
      Assert H'' := (compare_convert_EGAL ? ? H').
      Symmetry in H''.

  NewDestruct p; Simpl.
*)

(** opposite is right inverse for addition *)

Theorem Zplus_inverse_r: (x:Z) (Zplus x (Zopp x)) = ZERO.
Proof.
NewDestruct x as [|p|p]; Simpl; [
  Reflexivity
| Rewrite (convert_compare_EGAL p); Reflexivity
| Rewrite (convert_compare_EGAL p); Reflexivity ].
Qed.

(** opposite distributes over addition *)

Theorem Zopp_Zplus: 
  (x,y:Z) (Zopp (Zplus x y)) = (Zplus (Zopp x) (Zopp y)).
Proof.
NewDestruct x as [|p|p]; NewDestruct y as [|q|q]; Simpl;
  Reflexivity Orelse NewDestruct  (compare p q EGAL); Reflexivity.
Qed.

(** addition is commutative *)

Theorem Zplus_sym: (x,y:Z) (Zplus x y) = (Zplus y x).
Proof.
NewInduction x as [|p|p];NewDestruct y as [|q|q];Simpl;Try Reflexivity.
  Rewrite add_sym; Reflexivity.
  Rewrite ZC4; NewDestruct (compare q p EGAL); Reflexivity.
  Rewrite ZC4; NewDestruct (compare q p EGAL); Reflexivity.
  Rewrite add_sym; Reflexivity.
Qed.

(** opposite is left inverse for addition *)

Theorem Zplus_inverse_l: (x:Z) (Zplus (Zopp x) x) = ZERO.
Proof.
Intro; Rewrite Zplus_sym; Apply Zplus_inverse_r.
Qed.

Hints Local Resolve Zero_left Zero_right.

(** addition is associative *)

Theorem weak_assoc :
  (x,y:positive)(z:Z) (Zplus (POS x) (Zplus (POS y) z))=
                       (Zplus (Zplus (POS x) (POS y)) z).
Proof.
Intros x y z';Case z'; [
  Auto with arith
| Intros z;Simpl; Rewrite add_assoc;Auto with arith
| Intros z; Simpl; ElimPcompare y z;
  Intros E0;Rewrite E0;
  ElimPcompare '(add x y) 'z;Intros E1;Rewrite E1; [
    Absurd (compare (add x y) z EGAL)=EGAL; [    (* Case 1 *)
      Rewrite convert_compare_SUPERIEUR; [
        Discriminate
      | Rewrite convert_add; Rewrite (compare_convert_EGAL y z E0);
        Elim (ZL4 x);Intros k E2;Rewrite E2; Simpl; Unfold gt lt; Apply le_n_S;
        Apply le_plus_r ]
    | Assumption ]
  | Absurd (compare (add x y) z EGAL)=INFERIEUR; [ (* Case 2 *)
      Rewrite convert_compare_SUPERIEUR; [
        Discriminate
      | Rewrite convert_add; Rewrite (compare_convert_EGAL y z E0);
        Elim (ZL4 x);Intros k E2;Rewrite E2; Simpl; Unfold gt lt; Apply le_n_S;
        Apply le_plus_r]
    | Assumption ]
  | Rewrite (compare_convert_EGAL y z E0); (* Case 3 *)
    Elim (sub_pos_SUPERIEUR (add x z) z);[
      Intros t H; Elim H;Intros H1 H2;Elim H2;Intros H3 H4;
      Unfold true_sub; Rewrite H1; Cut x=t; [
        Intros E;Rewrite E;Auto with arith
      | Apply simpl_add_r with z:=z; Rewrite <- H3; Rewrite add_sym; Trivial with arith ]
    | Pattern 1 z; Rewrite <- (compare_convert_EGAL y z E0); Assumption ]
  | Elim (sub_pos_SUPERIEUR z y); [ (* Case 4 *)
      Intros k H;Elim H;Intros H1 H2;Elim H2;Intros H3 H4; Unfold 1 true_sub;
      Rewrite H1; Cut x=k; [
        Intros E;Rewrite E; Rewrite (convert_compare_EGAL k); Trivial with arith
      | Apply simpl_add_r with z:=y; Rewrite (add_sym k y); Rewrite H3;
        Apply compare_convert_EGAL; Assumption ]
    | Apply ZC2;Assumption]
  | Elim (sub_pos_SUPERIEUR z y); [ (* Case 5 *)
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
  | Elim (sub_pos_SUPERIEUR z y); [ (* Case 6 *)
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
  | Absurd (compare (add x y) z EGAL)=EGAL; [ (* Case 7 *)
      Rewrite convert_compare_SUPERIEUR; [
        Discriminate
      | Rewrite convert_add; Unfold gt;Apply lt_le_trans with m:=(convert y);[
          Apply compare_convert_INFERIEUR; Apply ZC1; Assumption
        | Apply le_plus_r]]
    | Assumption ]
  | Absurd (compare (add x y) z EGAL)=INFERIEUR; [ (* Case 8 *)
      Rewrite convert_compare_SUPERIEUR; [
        Discriminate
      | Unfold gt; Apply lt_le_trans with m:=(convert y);[
          Exact (compare_convert_SUPERIEUR y z E0)
        | Rewrite convert_add; Apply le_plus_r]]
    | Assumption ]
  | Elim sub_pos_SUPERIEUR with 1:=E0;Intros k H1; (* Case 9 *)
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
  (n,m,p:Z) (Zplus n (Zplus m p))= (Zplus (Zplus n m) p).
Proof.
Intros x y z;Case x;Case y;Case z;Auto with arith; Intros; [
  Rewrite (Zplus_sym (NEG p0)); Rewrite weak_assoc;
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

V7only [Notation Zplus_assoc_l := Zplus_assoc.].

Lemma Zplus_assoc_r : (n,m,p:Z)(Zplus (Zplus n m) p) =(Zplus n (Zplus m p)).
Proof.
Intros; Symmetry; Apply Zplus_assoc.
Qed.

(** Associativity mixed with commutativity *)

Lemma Zplus_permute : (n,m,p:Z) (Zplus n (Zplus m p))=(Zplus m (Zplus n p)).
Proof.
Intros n m p;
Rewrite Zplus_sym;Rewrite <- Zplus_assoc; Rewrite (Zplus_sym p n); Trivial with arith.
Qed.

(** addition simplifies *)

Lemma Zsimpl_plus_l : (n,m,p:Z)(Zplus n m)=(Zplus n p)->m=p.
Intros n m p H; Cut (Zplus (Zopp n) (Zplus n m))=(Zplus (Zopp n) (Zplus n p));[
  Do 2 Rewrite -> Zplus_assoc; Rewrite -> (Zplus_sym (Zopp n) n);
  Rewrite -> Zplus_inverse_r;Simpl; Trivial with arith
| Rewrite -> H; Trivial with arith ].
Qed.

(** addition and successor permutes *)

Lemma Zplus_S_n: (x,y:Z) (Zplus (Zs x) y) = (Zs (Zplus x y)).
Proof.
Intros x y; Unfold Zs; Rewrite (Zplus_sym (Zplus x y)); Rewrite Zplus_assoc;
Rewrite (Zplus_sym (POS xH)); Trivial with arith.
Qed.

Lemma Zplus_n_Sm : (n,m:Z) (Zs (Zplus n m))=(Zplus n (Zs m)).
Proof.
Intros n m; Unfold Zs; Rewrite Zplus_assoc; Trivial with arith.
Qed.

Lemma Zplus_Snm_nSm : (n,m:Z)(Zplus (Zs n) m)=(Zplus n (Zs m)).
Proof.
Unfold Zs ;Intros n m; Rewrite <- Zplus_assoc; Rewrite (Zplus_sym (POS xH));
Trivial with arith.
Qed.

(** Misc properties, usually redundant or non natural *)

Lemma Zplus_n_O : (n:Z) n=(Zplus n ZERO).
Proof.
Symmetry; Apply Zero_right.
Qed.

Lemma Zplus_unit_left : (n,m:Z) (Zplus n ZERO)=m -> n=m.
Proof.
Intros n m; Rewrite Zero_right; Intro; Assumption.
Qed.

Lemma Zplus_unit_right : (n,m:Z) n=(Zplus m ZERO) -> n=m.
Proof.
Intros n m; Rewrite Zero_right; Intro; Assumption.
Qed.

Lemma Zplus_simpl : (x,y,z,t:Z) x=y -> z=t -> (Zplus x z)=(Zplus y t).
Proof.
Intros; Rewrite H; Rewrite H0; Reflexivity.
Qed.

Lemma Zplus_Zopp_expand : (x,y,z:Z)
  (Zplus x (Zopp y))=(Zplus (Zplus x (Zopp z)) (Zplus z (Zopp y))).
Proof.
Intros x y z.
Rewrite <- (Zplus_assoc x).
Rewrite (Zplus_assoc (Zopp z)).
Rewrite Zplus_inverse_l.
Reflexivity.
Qed.

(**********************************************************************)
(** Properties of successor and predecessor on binary integer numbers *)

Theorem Zn_Sn : (x:Z) ~ x=(Zs x).
Proof.
Intros n;Cut ~ZERO=(POS xH);[
  Unfold not ;Intros H1 H2;Apply H1;Apply (Zsimpl_plus_l n);Rewrite Zero_right;
  Exact H2
| Discriminate ].
Qed.

Theorem add_un_Zs : (x:positive) (POS (add_un x)) = (Zs (POS x)).
Proof.
Intro; Rewrite -> ZL12; Unfold Zs; Simpl; Trivial with arith.
Qed.

(** successor and predecessor are inverse functions *)

Lemma Zs_pred : (n:Z) n=(Zs (Zpred n)).
Proof.
Intros n; Unfold Zs Zpred ;Rewrite <- Zplus_assoc; Simpl; Rewrite Zero_right;
Trivial with arith.
Qed. 

Hints Immediate Zs_pred : zarith.
 
Theorem Zpred_Sn : (x:Z) x=(Zpred (Zs x)).
Proof.
Intros m; Unfold Zpred Zs; Rewrite <- Zplus_assoc; Simpl; 
Rewrite Zplus_sym; Auto with arith.
Qed.

Theorem Zeq_add_S : (n,m:Z) (Zs n)=(Zs m) -> n=m.
Proof.
Intros n m H.
Change (Zplus (Zplus (NEG xH) (POS xH)) n)=
       (Zplus (Zplus (NEG xH) (POS xH)) m);
Do 2 Rewrite <- Zplus_assoc; Do 2 Rewrite (Zplus_sym (POS xH));
Unfold Zs in H;Rewrite H; Trivial with arith.
Qed.
 
(** Misc properties, usually redundant or non natural *)

Theorem Zeq_S : (n,m:Z) n=m -> (Zs n)=(Zs m).
Proof.
Intros n m H; Rewrite H; Reflexivity.
Qed.

Theorem Znot_eq_S : (n,m:Z) ~(n=m) -> ~((Zs n)=(Zs m)).
Proof.
Unfold not ;Intros n m H1 H2;Apply H1;Apply Zeq_add_S; Assumption.
Qed.

(**********************************************************************)
(** Properties of subtraction on binary integer numbers *)

Lemma Zminus_n_O : (x:Z) x=(Zminus x ZERO).
Proof.
Intro; Unfold Zminus; Simpl;Rewrite Zero_right; Trivial with arith.
Qed.

Lemma Zminus_n_n : (n:Z)(ZERO=(Zminus n n)).
Proof.
Intro; Unfold Zminus; Rewrite Zplus_inverse_r; Trivial with arith.
Qed.

Lemma Zplus_minus : (x,y,z:Z)(x=(Zplus y z))->(z=(Zminus x y)).
Proof.
Intros n m p H;Unfold Zminus;Apply (Zsimpl_plus_l m); 
Rewrite (Zplus_sym m (Zplus n (Zopp m))); Rewrite <- Zplus_assoc;
Rewrite Zplus_inverse_l; Rewrite Zero_right; Rewrite H; Trivial with arith.
Qed.

Lemma Zminus_plus : (x,y:Z)(Zminus (Zplus x y) x)=y.
Proof.
Intros n m;Unfold Zminus ;Rewrite -> (Zplus_sym n m);Rewrite <- Zplus_assoc;
Rewrite -> Zplus_inverse_r; Apply Zero_right.
Qed.

Lemma Zle_plus_minus : (n,m:Z) (Zplus n (Zminus m n))=m.
Proof.
Unfold Zminus; Intros n m; Rewrite Zplus_permute; Rewrite Zplus_inverse_r;
Apply Zero_right.
Qed.

Lemma Zminus_Sn_m : (n,m:Z)((Zs (Zminus n m))=(Zminus (Zs n) m)).
Proof.
Intros n m;Unfold Zminus Zs; Rewrite (Zplus_sym n (Zopp m));
Rewrite <- Zplus_assoc;Apply Zplus_sym.
Qed.

Lemma Zminus_plus_simpl : 
  (x,y,z:Z)((Zminus x y)=(Zminus (Zplus z x) (Zplus z y))).
Proof.
Intros n m p;Unfold Zminus; Rewrite Zopp_Zplus; Rewrite Zplus_assoc;
Rewrite (Zplus_sym p); Rewrite <- (Zplus_assoc n p); Rewrite Zplus_inverse_r;
Rewrite Zero_right; Trivial with arith.
Qed.

Lemma Zminus_Zplus_compatible :
  (x,y,z:Z) (Zminus (Zplus x z) (Zplus y z)) = (Zminus x y).
Intros x y n.
Unfold Zminus.
Rewrite -> Zopp_Zplus.
Rewrite -> (Zplus_sym (Zopp y) (Zopp n)).
Rewrite -> Zplus_assoc.
Rewrite <- (Zplus_assoc x n (Zopp n)).
Rewrite -> (Zplus_inverse_r n).
Rewrite <- Zplus_n_O.
Reflexivity.
Qed.

(** Misc redundant properties *)

V7only [Set Implicit Arguments.].

Lemma Zeq_Zminus : (x,y:Z)x=y -> (Zminus x y)=ZERO.
Proof.
Intros x y H; Rewrite H; Symmetry; Apply Zminus_n_n.
Qed.

Lemma Zminus_Zeq : (x,y:Z)(Zminus x y)=ZERO -> x=y.
Proof.
Intros x y H; Rewrite <- (Zle_plus_minus y x); Rewrite H; Apply Zero_right.
Qed.

V7only [Unset Implicit Arguments.].

(**********************************************************************)
(** Properties of multiplication on binary integer numbers *)

(** One is neutral for multiplication *)

Lemma Zmult_1_n : (n:Z)(Zmult (POS xH) n)=n.
Proof.
Intro x; NewDestruct x; Reflexivity.
Qed.
V7only [Notation Zmult_one := Zmult_1_n.].

Lemma Zmult_n_1 : (n:Z)(Zmult n (POS xH))=n.
Proof.
Intro x; NewDestruct x; Simpl; Try Rewrite times_x_1; Reflexivity.
Qed.

(** Zero is absorbant for multiplication *)

Theorem Zero_mult_left: (x:Z) (Zmult ZERO x) = ZERO.
Proof.
NewDestruct x; Reflexivity.
Qed.

Theorem Zero_mult_right: (x:Z) (Zmult x ZERO) = ZERO.
Proof.
NewDestruct x; Reflexivity.
Qed.

Hints Local Resolve Zero_mult_left Zero_mult_right.

(** Commutativity of multiplication *)

Theorem Zmult_sym : (x,y:Z) (Zmult x y) = (Zmult y x).
Proof.
NewDestruct x as [|p|p]; NewDestruct y as [|q|q]; Simpl; 
  Try Rewrite (times_sym p q); Reflexivity.
Qed.

(** Associativity of multiplication *)

Theorem Zmult_assoc :
  (x,y,z:Z) (Zmult x (Zmult y z))= (Zmult (Zmult x y) z).
Proof.
Intros x y z; NewDestruct x; NewDestruct y; NewDestruct z; Simpl; 
  Try Rewrite times_assoc; Reflexivity.
Qed.
V7only [Notation Zmult_assoc_l := Zmult_assoc.].

Lemma Zmult_assoc_r : (n,m,p:Z)((Zmult (Zmult n m) p) = (Zmult n (Zmult m p))).
Proof.
Intros n m p; Rewrite Zmult_assoc; Trivial with arith.
Qed.

(** Associativity mixed with commutativity *)

Theorem Zmult_permute : (n,m,p:Z)(Zmult n (Zmult m p)) = (Zmult m (Zmult n p)).
Proof.
Intros x y z; Rewrite -> (Zmult_assoc y x z); Rewrite -> (Zmult_sym y x).
Apply Zmult_assoc.
Qed.

(** Z is integral *)

Theorem Zmult_eq: (x,y:Z) ~(x=ZERO) -> (Zmult y x) = ZERO -> y = ZERO.
Proof.
Intros x y; NewDestruct x as [|p|p].
  Intro H; Absurd ZERO=ZERO; Trivial.
  Intros _ H; NewDestruct y as [|q|q]; Reflexivity Orelse Discriminate.
  Intros _ H; NewDestruct y as [|q|q]; Reflexivity Orelse Discriminate.
Qed.

V7only [Set Implicit Arguments.].

Lemma Zmult_zero : (x,y:Z)(Zmult x y)=ZERO -> x=ZERO \/ y=ZERO.
Proof.
NewDestruct x; NewDestruct y; Auto; Simpl; Intro H; Discriminate H.
Qed.

V7only [Unset Implicit Arguments.].

(** Multiplication and Opposite *)

Theorem Zopp_Zmult: (x,y:Z) (Zmult (Zopp x) y) = (Zopp (Zmult x y)).
Proof.
NewDestruct x; NewDestruct y; Reflexivity.
Qed.

Theorem Zopp_Zmult_r : (x,y:Z)(Zopp (Zmult x y)) = (Zmult x (Zopp y)).
Intros x y; Rewrite Zmult_sym; Rewrite <- Zopp_Zmult; Apply Zmult_sym.
Qed.

Theorem Zopp_Zmult_l : (x,y:Z)(Zopp (Zmult x y)) = (Zmult (Zopp x) y).
Proof.
Intros x y; Symmetry; Apply Zopp_Zmult.
Qed.

Theorem Zmult_Zopp_left :  (x,y:Z)(Zmult (Zopp x) y) = (Zmult x (Zopp y)).
Intros; Rewrite Zopp_Zmult; Rewrite Zopp_Zmult_r; Trivial with arith.
Qed.

Theorem Zmult_Zopp_Zopp: (x,y:Z) (Zmult (Zopp x) (Zopp y)) = (Zmult x y).
Proof.
NewDestruct x; NewDestruct y; Reflexivity.
Qed.

Theorem Zopp_one : (x:Z)(Zopp x)=(Zmult x (NEG xH)).
Induction x; Intros; Rewrite Zmult_sym; Auto with arith.
Qed.

(** Distributivity of multiplication over addition *)

Theorem weak_Zmult_plus_distr_r:
  (x:positive)(y,z:Z)
   (Zmult (POS x) (Zplus y z)) = (Zplus (Zmult (POS x) y) (Zmult (POS x) z)).
Proof.
Intros x y' z';Case y';Case z';Auto with arith;Intros y z;
  (Simpl; Rewrite times_add_distr; Trivial with arith)
Orelse
  (Simpl; ElimPcompare z y; Intros E0;Rewrite E0; [
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

Lemma Zmult_plus_distr_l : 
  (n,m,p:Z)((Zmult (Zplus n m) p)=(Zplus (Zmult n p) (Zmult m p))).
Proof.
Intros n m p;Rewrite Zmult_sym;Rewrite Zmult_plus_distr_r; 
Do 2 Rewrite -> (Zmult_sym p); Trivial with arith.
Qed.

(** Distributivity of multiplication over subtraction *)

Lemma Zmult_Zminus_distr_l :
  (x,y,z:Z)((Zmult (Zminus x y) z)=(Zminus (Zmult x z) (Zmult y z))).
Proof.
Intros; Unfold Zminus.
Rewrite <- Zopp_Zmult.
Apply Zmult_plus_distr_l.
Qed.

V7only [Notation Zmult_minus_distr := Zmult_Zminus_distr_l.].
 
Lemma  Zmult_Zminus_distr_r :
  (x,y,z:Z)(Zmult z (Zminus x y)) = (Zminus (Zmult z x) (Zmult z y)).
Proof.
Intros; Rewrite (Zmult_sym z (Zminus x y)).
Rewrite (Zmult_sym  z x).
Rewrite (Zmult_sym z y).
Apply Zmult_Zminus_distr_l.
Qed.

(** Simplification of multiplication for non-zero integers *)

Lemma Zmult_reg_left : (x,y,z:Z) z<>ZERO -> (Zmult z x)=(Zmult z y) -> x=y.
Proof.
Intros.
Generalize (Zeq_Zminus H0).
Intro.
Apply Zminus_Zeq.
Rewrite <- Zmult_Zminus_distr_r in H1.
Clear H0; NewDestruct (Zmult_zero H1).
Contradiction.
Trivial.
Qed.

Lemma Zmult_reg_right : (x,y,z:Z) z<>ZERO -> (Zmult x z)=(Zmult y z) -> x=y.
Proof.
Intros x y z Hz.
Rewrite (Zmult_sym x z).
Rewrite (Zmult_sym y z).
Intro; Apply Zmult_reg_left with z; Assumption.
Qed.
    
(** Addition and multiplication by 2 *)

Theorem Zplus_Zmult_2 : (x:Z) (Zplus x x) = (Zmult x (POS (xO xH))).
Proof.
Intros x; Pattern 1 2 x ; Rewrite <- (Zmult_n_1 x);
Rewrite <- Zmult_plus_distr_r; Reflexivity.
Qed.

(** Multiplication and successor *)

Lemma Zmult_n_Sm : (n,m:Z) (Zplus (Zmult n m) n)=(Zmult n (Zs m)).
Proof.
Intros n m;Unfold Zs; Rewrite Zmult_plus_distr_r;
Rewrite (Zmult_sym n (POS xH));Rewrite Zmult_one; Trivial with arith.
Qed.

Lemma Zmult_Sm_n : (n,m:Z) (Zplus (Zmult n m) m)=(Zmult (Zs n) m).
Proof.
Intros n m; Unfold Zs; Rewrite Zmult_plus_distr_l; Rewrite Zmult_1_n;
Trivial with arith.
Qed.

(** Misc redundant properties *)

Lemma Zmult_n_O : (n:Z) ZERO=(Zmult n ZERO).
Proof.
Intro;Rewrite Zmult_sym;Simpl; Trivial with arith.
Qed.

Theorem Z_eq_mult:
  (x,y:Z)  y = ZERO -> (Zmult y x) = ZERO.
Intros x y H; Rewrite H; Auto with arith.
Qed.

(**********************************************************************)
(** Comparison on integers *)

Lemma Zcompare_x_x : (x:Z) (Zcompare x x) = EGAL.
Proof.
NewDestruct x as [|p|p]; Simpl; [ Reflexivity | Apply convert_compare_EGAL
  | Rewrite convert_compare_EGAL; Reflexivity ].
Qed.

Theorem Zcompare_EGAL_eq : (x,y:Z) (Zcompare x y) = EGAL -> x = y.
Proof.
NewDestruct x as [|x'|x'];NewDestruct y as [|y'|y'];Simpl;Intro H; Reflexivity Orelse Try Discriminate H; [
    Rewrite (compare_convert_EGAL x' y' H); Reflexivity
  | Rewrite (compare_convert_EGAL x' y'); [
      Reflexivity
    | NewDestruct (compare x' y' EGAL);
      Reflexivity Orelse Discriminate]].
Qed.

Theorem Zcompare_EGAL : (x,y:Z) (Zcompare x y) = EGAL <-> x = y.
Proof.
Intros x y;Split; Intro E; [ Apply Zcompare_EGAL_eq; Assumption
  | Rewrite E; Apply Zcompare_x_x ].
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

(** Transitivity of comparison *)

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

(** Comparison and opposite *)

Theorem Zcompare_Zopp :
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

Theorem Zcompare_Zplus_compatible : 
   (x,y,z:Z) (Zcompare (Zplus z x) (Zplus z y)) = (Zcompare x y).
Proof.
Exact (weaken_Zcompare_Zplus_compatible weak_Zcompare_Zplus_compatible).
Qed.

Theorem Zcompare_Zplus_compatible2 :
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

Theorem Zcompare_et_un: 
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

Theorem Zcompare_n_S : (n,m:Z)(Zcompare (Zs n) (Zs m)) = (Zcompare n m).
Proof.
Intros n m;Unfold Zs ;Do 2 Rewrite -> [t:Z](Zplus_sym t (POS xH));
Rewrite -> Zcompare_Zplus_compatible;Auto with arith.
Qed.
 
(** Multiplication and comparison *)

Theorem Zcompare_Zmult_compatible : 
   (x:positive)(y,z:Z)
      (Zcompare (Zmult (POS x) y) (Zmult (POS x) z)) = (Zcompare y z).

Induction x; [
  Intros p H y z;
  Cut (POS (xI p))=(Zplus (Zplus (POS p) (POS p)) (POS xH)); [
    Intros E; Rewrite E; Do 4 Rewrite Zmult_plus_distr_l; 
    Do 2 Rewrite Zmult_one;
    Apply Zcompare_Zplus_compatible2; [
      Apply Zcompare_Zplus_compatible2; Apply H
    | Trivial with arith]
  | Simpl; Rewrite (add_x_x p); Trivial with arith]
| Intros p H y z; Cut (POS (xO p))=(Zplus (POS p) (POS p)); [
    Intros E; Rewrite E; Do 2 Rewrite Zmult_plus_distr_l;
      Apply Zcompare_Zplus_compatible2; Apply H
    | Simpl; Rewrite (add_x_x p); Trivial with arith]
  | Intros y z; Do 2 Rewrite Zmult_one; Trivial with arith].
Qed.

(**********************************************************************)
(** Relating binary positive numbers and binary integers *)

Lemma POS_xI : (p:positive) (POS (xI p))=(Zplus (Zmult (POS (xO xH)) (POS p)) (POS xH)).
Intro; Apply refl_equal.
Qed.

Lemma POS_xO : (p:positive) (POS (xO p))=(Zmult (POS (xO xH)) (POS p)).
Intro; Apply refl_equal.
Qed.

Lemma NEG_xI : (p:positive) (NEG (xI p))=(Zminus (Zmult (POS (xO xH)) (NEG p)) (POS xH)).
Intro; Apply refl_equal.
Qed.

Lemma NEG_xO : (p:positive) (NEG (xO p))=(Zmult (POS (xO xH)) (NEG p)).
Reflexivity.
Qed.

Lemma POS_add : (p,p':positive)(POS (add p p'))=(Zplus (POS p) (POS p')).
NewDestruct p; NewDestruct p'; Reflexivity.
Qed.

Lemma NEG_add : (p,p':positive)(NEG (add p p'))=(Zplus (NEG p) (NEG p')).
NewDestruct p; NewDestruct p'; Reflexivity.
Qed.

(**********************************************************************)
(** Order relations *)

Definition Zlt := [x,y:Z](Zcompare x y) = INFERIEUR.
Definition Zgt := [x,y:Z](Zcompare x y) = SUPERIEUR.
Definition Zle := [x,y:Z]~(Zcompare x y) = SUPERIEUR.
Definition Zge := [x,y:Z]~(Zcompare x y) = INFERIEUR.
Definition Zne := [x,y:Z] ~(x=y).

V8Infix "<=" Zle : Z_scope.
V8Infix "<"  Zlt : Z_scope.
V8Infix ">=" Zge : Z_scope.
V8Infix ">"  Zgt : Z_scope.

V8Notation "x <= y <= z" := (Zle x y)/\(Zle y z) :Z_scope.
V8Notation "x <= y < z"  := (Zle x y)/\(Zlt y z) :Z_scope.
V8Notation  "x < y < z"  := (Zlt x y)/\(Zlt y z) :Z_scope.
V8Notation  "x < y <= z" := (Zlt x y)/\(Zle y z) :Z_scope.

(**********************************************************************)
(** Absolute value on integers *)

Definition absolu [x:Z] : nat :=
  Cases x of
     ZERO   => O
  | (POS p) => (convert p)
  | (NEG p) => (convert p)
  end.

Definition Zabs [z:Z] : Z :=
  Cases z of 
     ZERO   => ZERO
  | (POS p) => (POS p)
  | (NEG p) => (POS p)
  end.

(**********************************************************************)
(** From [nat] to [Z] *)

Definition inject_nat := 
  [x:nat]Cases x of
           O => ZERO
         | (S y) => (POS (anti_convert y))
         end.

Require BinNat.

Definition entier_of_Z :=
  [z:Z]Cases z of ZERO => Nul | (POS p) => (Pos p) | (NEG p) => (Pos p) end.

Definition Z_of_entier :=
  [x:entier]Cases x of Nul => ZERO | (Pos p) => (POS p) end.
