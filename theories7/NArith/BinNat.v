(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require BinPos.

(**********************************************************************)
(** Binary natural numbers *)

Inductive entier: Set := Nul : entier | Pos : positive -> entier.

(** Declare binding key for scope positive_scope *)

Delimits Scope N_scope with N.

(** Automatically open scope N_scope for the constructors of N *)

Bind Scope N_scope with entier.
Arguments Scope Pos [ N_scope ].

Open Local Scope N_scope.

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

V8Infix "+" Nplus : N_scope.

(** Multiplication *)

Definition Nmult := [n,m]
  Cases n m of
  | Nul     _       => Nul
  | _       Nul     => Nul
  | (Pos p) (Pos q) => (Pos (times p q))
  end.

V8Infix "*" Nmult : N_scope.

(** Order *)

Definition Ncompare := [n,m]
  Cases n m of
  | Nul      Nul      => EGAL
  | Nul      (Pos m') => INFERIEUR
  | (Pos n') Nul      => SUPERIEUR
  | (Pos n') (Pos m') => (compare n' m' EGAL)
  end.

V8Infix "?=" Ncompare (at level 70, no associativity) : N_scope.

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

Theorem Nplus_assoc : 
  (n,m,p:entier)(Nplus n (Nplus m p))=(Nplus (Nplus n m) p).
Proof.
Intros.
NewDestruct n; Try Reflexivity.
NewDestruct m; Try Reflexivity.
NewDestruct p; Try Reflexivity.
Simpl; Rewrite add_assoc; Reflexivity.
Qed.

Theorem Nplus_succ : (n,m:entier)(Nplus (Nsucc n) m)=(Nsucc (Nplus n m)).
Proof.
NewDestruct n; NewDestruct m.
  Simpl; Reflexivity.
  Unfold Nsucc Nplus; Rewrite <- ZL12bis; Reflexivity.
  Simpl; Reflexivity.
  Simpl; Rewrite ZL14bis; Reflexivity.
Qed.

Theorem Nsucc_inj : (n,m:entier)(Nsucc n)=(Nsucc m)->n=m.
Proof.
NewDestruct n; NewDestruct m; Simpl; Intro H; 
  Reflexivity Orelse Injection H; Clear H; Intro H.
  Symmetry in H; Contradiction add_un_not_un with p.
  Contradiction add_un_not_un with p.
  Rewrite add_un_inj with 1:=H; Reflexivity.
Qed.

Theorem Nplus_reg_l : (n,m,p:entier)(Nplus n m)=(Nplus n p)->m=p.
Proof.
Intro n; Pattern n; Apply Nind; Clear n; Simpl.
  Trivial.
  Intros n IHn m p H0; Do 2 Rewrite Nplus_succ in H0.
  Apply IHn; Apply Nsucc_inj; Assumption.
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

Theorem Nmult_assoc : 
  (n,m,p:entier)(Nmult n (Nmult m p))=(Nmult (Nmult n m) p).
Proof.
Intros.
NewDestruct n; Try Reflexivity.
NewDestruct m; Try Reflexivity.
NewDestruct p; Try Reflexivity.
Simpl; Rewrite times_assoc; Reflexivity.
Qed.

Theorem Nmult_plus_distr_r :
  (n,m,p:entier)(Nmult (Nplus n m) p)=(Nplus (Nmult n p) (Nmult m p)).
Proof.
Intros.
NewDestruct n; Try Reflexivity.
NewDestruct m; NewDestruct p; Try Reflexivity.
Simpl; Rewrite times_add_distr_l; Reflexivity.
Qed.

Theorem Nmult_reg_r : (n,m,p:entier) ~p=Nul->(Nmult n p)=(Nmult m p) -> n=m.
Proof.
NewDestruct p; Intros Hp H.
Contradiction Hp; Reflexivity.
NewDestruct n; NewDestruct m; Reflexivity Orelse Try Discriminate H.
Injection H; Clear H; Intro H; Rewrite simpl_times_r with 1:=H; Reflexivity.
Qed. 

Theorem Nmult_0_l : (n:entier) (Nmult Nul n) = Nul.
Proof.
Reflexivity.
Qed.

(** Properties of comparison *)

Theorem Ncompare_Eq_eq : (n,m:entier) (Ncompare n m) = EGAL -> n = m.
Proof.
NewDestruct n as [|n]; NewDestruct m as [|m]; Simpl; Intro H;
  Reflexivity Orelse Try Discriminate H.
  Rewrite (compare_convert_EGAL n m H); Reflexivity.
Qed.

