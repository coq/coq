(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(***********************************************************)
(** Binary Integers (Pierre Crégut, CNET, Lannion, France) *)
(***********************************************************)

Require Export BinPos.
Require Export Pnat.
Require BinNat.
Require Plus.
Require Mult.
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

Fixpoint ZPminus [x,y:positive] : Z :=
  Cases x y of
  | (xI x') (xI y') => (Zdouble (ZPminus x' y'))
  | (xI x') (xO y') => (Zdouble_plus_one (ZPminus x' y'))
  | (xI x') xH      => (POS (xO x'))
  | (xO x') (xI y') => (Zdouble_minus_one (ZPminus x' y'))
  | (xO x') (xO y') => (Zdouble (ZPminus x' y'))
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

(** Direct, easier to handle variants of successor and addition *)

Definition Zsucc' [x:Z] :=
  Cases x of
  | ZERO => (POS xH)
  | (POS x') => (POS (add_un x'))
  | (NEG x') => (ZPminus xH x')
  end.

Definition Zpred' [x:Z] :=
  Cases x of
  | ZERO => (NEG xH)
  | (POS x') => (ZPminus x' xH)
  | (NEG x') => (NEG (add_un x'))
  end.

Definition Zplus' := [x,y:Z]
  Cases x y of
    ZERO      y       => y
  | x         ZERO    => x
  | (POS x') (POS y') => (POS (add x' y'))
  | (POS x') (NEG y') => (ZPminus x' y')
  | (NEG x') (POS y') => (ZPminus y' x')
  | (NEG x') (NEG y') => (NEG (add x' y'))
  end.

Open Local Scope Z_scope.

(**********************************************************************)
(** Inductive specification of Z *)

Theorem Zind : (P:(Z ->Prop))
  (P ZERO) -> ((x:Z)(P x) ->(P (Zsucc' x))) -> ((x:Z)(P x) ->(P (Zpred' x))) ->
     (z:Z)(P z).
Proof.
Intros P H0 Hs Hp z; NewDestruct z.
  Assumption.
  Apply Pind with P:=[p](P (POS p)).
    Change (P (Zsucc' ZERO)); Apply Hs; Apply H0.
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
Intro x; NewDestruct x; Reflexivity.
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
(* Properties of the direct definition of successor and predecessor *)

Lemma Zpred'_succ' : (x:Z)(Zpred' (Zsucc' x))=x.
Proof.
Intro x; NewDestruct x; Simpl.
  Reflexivity.
NewDestruct p; Simpl; Try Rewrite double_moins_un_add_un_xI; Reflexivity.
NewDestruct p; Simpl; Try Rewrite is_double_moins_un; Reflexivity.
Qed.

Lemma Zsucc'_discr : (x:Z)x<>(Zsucc' x).
Proof.
Intro x; NewDestruct x; Simpl.
  Discriminate.
  Injection; Apply add_un_discr.
  NewDestruct p; Simpl.
    Discriminate.
    Intro H; Symmetry in H; Injection H; Apply double_moins_un_xO_discr.
    Discriminate.
Qed.

(**********************************************************************)
(** Other properties of binary integer numbers *)

Lemma ZL0 : (S (S O))=(plus (S O) (S O)).
Proof.
Reflexivity.
Qed.

(**********************************************************************)
(** Properties of the addition on integers *)

(** zero is left neutral for addition *)

Theorem Zero_left: (x:Z) (Zplus ZERO x) = x.
Proof.
Intro x; NewDestruct x; Reflexivity.
Qed.

(** zero is right neutral for addition *)

Theorem Zero_right: (x:Z) (Zplus x ZERO) = x.
Proof.
Intro x; NewDestruct x; Reflexivity.
Qed.

(** addition is commutative *)

Theorem Zplus_sym: (x,y:Z) (Zplus x y) = (Zplus y x).
Proof.
Intro x;NewInduction x as [|p|p];Intro y; NewDestruct y as [|q|q];Simpl;Try Reflexivity.
  Rewrite add_sym; Reflexivity.
  Rewrite ZC4; NewDestruct (compare q p EGAL); Reflexivity.
  Rewrite ZC4; NewDestruct (compare q p EGAL); Reflexivity.
  Rewrite add_sym; Reflexivity.
Qed.

(** opposite distributes over addition *)

Theorem Zopp_Zplus: 
  (x,y:Z) (Zopp (Zplus x y)) = (Zplus (Zopp x) (Zopp y)).
Proof.
Intro x; NewDestruct x as [|p|p]; Intro y; NewDestruct y as [|q|q]; Simpl;
  Reflexivity Orelse NewDestruct  (compare p q EGAL); Reflexivity.
Qed.

(** opposite is inverse for addition *)

Theorem Zplus_inverse_r: (x:Z) (Zplus x (Zopp x)) = ZERO.
Proof.
Intro x; NewDestruct x as [|p|p]; Simpl; [
  Reflexivity
| Rewrite (convert_compare_EGAL p); Reflexivity
| Rewrite (convert_compare_EGAL p); Reflexivity ].
Qed.

Theorem Zplus_inverse_l: (x:Z) (Zplus (Zopp x) x) = ZERO.
Proof.
Intro; Rewrite Zplus_sym; Apply Zplus_inverse_r.
Qed.

Hints Local Resolve Zero_left Zero_right.

(** addition is associative *)

Lemma weak_assoc :
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

Theorem Zplus_permute : (n,m,p:Z) (Zplus n (Zplus m p))=(Zplus m (Zplus n p)).
Proof.
Intros n m p;
Rewrite Zplus_sym;Rewrite <- Zplus_assoc; Rewrite (Zplus_sym p n); Trivial with arith.
Qed.

(** addition simplifies *)

Theorem Zsimpl_plus_l : (n,m,p:Z)(Zplus n m)=(Zplus n p)->m=p.
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

Theorem Zs_pred : (n:Z) n=(Zs (Zpred n)).
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

Lemma Zeq_S : (n,m:Z) n=m -> (Zs n)=(Zs m).
Proof.
Intros n m H; Rewrite H; Reflexivity.
Qed.

Lemma Znot_eq_S : (n,m:Z) ~(n=m) -> ~((Zs n)=(Zs m)).
Proof.
Unfold not ;Intros n m H1 H2;Apply H1;Apply Zeq_add_S; Assumption.
Qed.

(**********************************************************************)
(** Properties of subtraction on binary integer numbers *)

Lemma Zminus_0_r : (x:Z) (Zminus x ZERO)=x.
Proof.
Intro; Unfold Zminus; Simpl;Rewrite Zero_right; Trivial with arith.
Qed.

Lemma Zminus_n_O : (x:Z) x=(Zminus x ZERO).
Proof.
Intro; Symmetry; Apply Zminus_0_r.
Qed.

Lemma Zminus_diag : (n:Z)(Zminus n n)=ZERO.
Proof.
Intro; Unfold Zminus; Rewrite Zplus_inverse_r; Trivial with arith.
Qed.

Lemma Zminus_n_n : (n:Z)(ZERO=(Zminus n n)).
Proof.
Intro; Symmetry; Apply Zminus_diag.
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

Lemma Zminus_plus_simpl_l : 
  (x,y,z:Z)(Zminus (Zplus z x) (Zplus z y))=(Zminus x y).
Proof.
Intros n m p;Unfold Zminus; Rewrite Zopp_Zplus; Rewrite Zplus_assoc;
Rewrite (Zplus_sym p); Rewrite <- (Zplus_assoc n p); Rewrite Zplus_inverse_r;
Rewrite Zero_right; Trivial with arith.
Qed.

Lemma Zminus_plus_simpl : 
  (x,y,z:Z)((Zminus x y)=(Zminus (Zplus z x) (Zplus z y))).
Proof.
Intros; Symmetry; Apply Zminus_plus_simpl_l.
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

Theorem Zmult_1_n : (n:Z)(Zmult (POS xH) n)=n.
Proof.
Intro x; NewDestruct x; Reflexivity.
Qed.
V7only [Notation Zmult_one := Zmult_1_n.].

Theorem Zmult_n_1 : (n:Z)(Zmult n (POS xH))=n.
Proof.
Intro x; NewDestruct x; Simpl; Try Rewrite times_x_1; Reflexivity.
Qed.

(** Zero property of multiplication *)

Theorem Zero_mult_left: (x:Z) (Zmult ZERO x) = ZERO.
Proof.
Intro x; NewDestruct x; Reflexivity.
Qed.

Theorem Zero_mult_right: (x:Z) (Zmult x ZERO) = ZERO.
Proof.
Intro x; NewDestruct x; Reflexivity.
Qed.

Hints Local Resolve Zero_mult_left Zero_mult_right.

Lemma Zmult_n_O : (n:Z) ZERO=(Zmult n ZERO).
Proof.
Intro x; NewDestruct x; Reflexivity.
Qed.

(** Commutativity of multiplication *)

Theorem Zmult_sym : (x,y:Z) (Zmult x y) = (Zmult y x).
Proof.
Intros x y; NewDestruct x as [|p|p]; NewDestruct y as [|q|q]; Simpl; 
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

Theorem Zmult_zero : (x,y:Z)(Zmult x y)=ZERO -> x=ZERO \/ y=ZERO.
Proof.
Intros x y; NewDestruct x; NewDestruct y; Auto; Simpl; Intro H; Discriminate H.
Qed.

V7only [Unset Implicit Arguments.].

Lemma Zmult_1_inversion_l : 
 (x,y:Z) (Zmult x y)=(POS xH) -> x=(POS xH) \/ x=(NEG xH).
Proof.
Intros x y; NewDestruct x as [|p|p]; Intro; [ Discriminate | Left | Right ];
  (NewDestruct y as [|q|q]; Try Discriminate;
  Simpl in H; Injection H; Clear H; Intro H;
  Rewrite times_one_inversion_l with 1:=H; Reflexivity).
Qed.

(** Multiplication and Opposite *)

Theorem Zopp_Zmult_l : (x,y:Z)(Zopp (Zmult x y)) = (Zmult (Zopp x) y).
Proof.
Intros x y; NewDestruct x; NewDestruct y; Reflexivity.
Qed.

Theorem Zopp_Zmult_r : (x,y:Z)(Zopp (Zmult x y)) = (Zmult x (Zopp y)).
Intros x y; Rewrite (Zmult_sym x y); Rewrite Zopp_Zmult_l; Apply Zmult_sym.
Qed.

Lemma Zopp_Zmult: (x,y:Z) (Zmult (Zopp x) y) = (Zopp (Zmult x y)).
Proof.
Intros x y; Symmetry; Apply Zopp_Zmult_l.
Qed.

Theorem Zmult_Zopp_left :  (x,y:Z)(Zmult (Zopp x) y) = (Zmult x (Zopp y)).
Intros x y; Rewrite Zopp_Zmult; Rewrite Zopp_Zmult_r; Trivial with arith.
Qed.

Theorem Zmult_Zopp_Zopp: (x,y:Z) (Zmult (Zopp x) (Zopp y)) = (Zmult x y).
Proof.
Intros x y; NewDestruct x; NewDestruct y; Reflexivity.
Qed.

Theorem Zopp_one : (x:Z)(Zopp x)=(Zmult x (NEG xH)).
Intro x; NewInduction x; Intros; Rewrite Zmult_sym; Auto with arith.
Qed.

(** Distributivity of multiplication over addition *)

Lemma weak_Zmult_plus_distr_r:
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

Theorem Zmult_plus_distr_l : 
  (n,m,p:Z)((Zmult (Zplus n m) p)=(Zplus (Zmult n p) (Zmult m p))).
Proof.
Intros n m p;Rewrite Zmult_sym;Rewrite Zmult_plus_distr_r; 
Do 2 Rewrite -> (Zmult_sym p); Trivial with arith.
Qed.

(** Distributivity of multiplication over subtraction *)

Lemma Zmult_Zminus_distr_l :
  (x,y,z:Z)((Zmult (Zminus x y) z)=(Zminus (Zmult x z) (Zmult y z))).
Proof.
Intros x y z; Unfold Zminus.
Rewrite <- Zopp_Zmult.
Apply Zmult_plus_distr_l.
Qed.

V7only [Notation Zmult_minus_distr := Zmult_Zminus_distr_l.].
 
Lemma  Zmult_Zminus_distr_r :
  (x,y,z:Z)(Zmult z (Zminus x y)) = (Zminus (Zmult z x) (Zmult z y)).
Proof.
Intros x y z; Rewrite (Zmult_sym z (Zminus x y)).
Rewrite (Zmult_sym  z x).
Rewrite (Zmult_sym z y).
Apply Zmult_Zminus_distr_l.
Qed.

(** Simplification of multiplication for non-zero integers *)
V7only [Set Implicit Arguments.].

Lemma Zmult_reg_left : (x,y,z:Z) z<>ZERO -> (Zmult z x)=(Zmult z y) -> x=y.
Proof.
Intros x y z H H0.
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
V7only [Unset Implicit Arguments.].

(** Addition and multiplication by 2 *)

Lemma Zplus_Zmult_2 : (x:Z) (Zplus x x) = (Zmult x (POS (xO xH))).
Proof.
Intros x; Pattern 1 2 x ; Rewrite <- (Zmult_n_1 x);
Rewrite <- Zmult_plus_distr_r; Reflexivity.
Qed.

(** Multiplication and successor *)

Lemma Zmult_succ_r : (n,m:Z) (Zmult n (Zs m))=(Zplus (Zmult n m) n).
Proof.
Intros n m;Unfold Zs; Rewrite Zmult_plus_distr_r;
Rewrite (Zmult_sym n (POS xH));Rewrite Zmult_one; Trivial with arith.
Qed.

Lemma Zmult_n_Sm : (n,m:Z) (Zplus (Zmult n m) n)=(Zmult n (Zs m)).
Proof.
Intros; Symmetry; Apply Zmult_succ_r.
Qed.

Lemma Zmult_succ_l : (n,m:Z) (Zmult (Zs n) m)=(Zplus (Zmult n m) m).
Proof.
Intros n m; Unfold Zs; Rewrite Zmult_plus_distr_l; Rewrite Zmult_1_n;
Trivial with arith.
Qed.

Lemma Zmult_Sm_n : (n,m:Z) (Zplus (Zmult n m) m)=(Zmult (Zs n) m).
Proof.
Intros; Symmetry; Apply Zmult_succ_l.
Qed.

(** Misc redundant properties *)

Lemma Z_eq_mult:
  (x,y:Z)  y = ZERO -> (Zmult y x) = ZERO.
Intros x y H; Rewrite H; Auto with arith.
Qed.

(**********************************************************************)
(** Relating binary positive numbers and binary integers *)

Lemma POS_xI : (p:positive) (POS (xI p))=(Zplus (Zmult (POS (xO xH)) (POS p)) (POS xH)).
Proof.
Intro; Apply refl_equal.
Qed.

Lemma POS_xO : (p:positive) (POS (xO p))=(Zmult (POS (xO xH)) (POS p)).
Proof.
Intro; Apply refl_equal.
Qed.

Lemma NEG_xI : (p:positive) (NEG (xI p))=(Zminus (Zmult (POS (xO xH)) (NEG p)) (POS xH)).
Proof.
Intro; Apply refl_equal.
Qed.

Lemma NEG_xO : (p:positive) (NEG (xO p))=(Zmult (POS (xO xH)) (NEG p)).
Proof.
Reflexivity.
Qed.

Lemma POS_add : (p,p':positive)(POS (add p p'))=(Zplus (POS p) (POS p')).
Proof.
Intros p p'; NewDestruct p; NewDestruct p'; Reflexivity.
Qed.

Lemma NEG_add : (p,p':positive)(NEG (add p p'))=(Zplus (NEG p) (NEG p')).
Proof.
Intros p p'; NewDestruct p; NewDestruct p'; Reflexivity.
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
