(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i $Id$ i*)

(** Binary Integers (Pierre Crégut (CNET, Lannion, France) *)

Require Arith.
Require BinInt.
Require Zcompare.
Require Zorder.

Open Local Scope Z_scope.

(**********************************************************************)
(** Minimum on binary integer numbers *)

Definition Zmin := [n,m:Z]
 <Z>Cases (Zcompare n m) of
      EGAL      => n
    | INFERIEUR => n
    | SUPERIEUR => m
    end.

(** Properties of minimum on binary integer numbers *)

Lemma Zmin_SS : (n,m:Z)((Zs (Zmin n m))=(Zmin (Zs n) (Zs m))).
Proof.
Intros n m;Unfold Zmin; Rewrite (Zcompare_n_S n m);
(ElimCompare 'n 'm);Intros E;Rewrite E;Auto with arith.
Qed.

Lemma Zle_min_l : (n,m:Z)(Zle (Zmin n m) n).
Proof.
Intros n m;Unfold Zmin ; (ElimCompare 'n 'm);Intros E;Rewrite -> E;
  [ Apply Zle_n | Apply Zle_n | Apply Zlt_le_weak; Apply Zgt_lt;Exact E ].
Qed.

Lemma Zle_min_r : (n,m:Z)(Zle (Zmin n m) m).
Proof.
Intros n m;Unfold Zmin ; (ElimCompare 'n 'm);Intros E;Rewrite -> E;[
  Unfold Zle ;Rewrite -> E;Discriminate
| Unfold Zle ;Rewrite -> E;Discriminate
| Apply Zle_n ].
Qed.

Lemma Zmin_case : (n,m:Z)(P:Z->Set)(P n)->(P m)->(P (Zmin n m)).
Proof.
Intros n m P H1 H2; Unfold Zmin; Case (Zcompare n m);Auto with arith.
Qed.

Lemma Zmin_or : (n,m:Z)(Zmin n m)=n \/ (Zmin n m)=m.
Proof.
Unfold Zmin; Intros; Elim (Zcompare n m); Auto.
Qed.

Lemma Zmin_n_n : (n:Z) (Zmin n n)=n.
Proof.
Unfold Zmin; Intros; Elim (Zcompare n n); Auto.
Qed.

Lemma Zmin_plus :
 (x,y,n:Z)(Zmin (Zplus x n) (Zplus y n))=(Zplus (Zmin x y) n).
Proof.
Intros x y n; Unfold Zmin.
Rewrite (Zplus_sym x n);
Rewrite (Zplus_sym y n);
Rewrite (Zcompare_Zplus_compatible x y n).
Case (Zcompare x y); Apply Zplus_sym.
Qed.

(**********************************************************************)
(** Maximum of two binary integer numbers *)
V7only [ (* From Zdivides *) ].

Definition Zmax :=
   [a, b : ?]  Cases (Zcompare a b) of INFERIEUR => b | _ => a end.

(** Properties of maximum on binary integer numbers *)

Tactic Definition CaseEq name :=
Generalize (refl_equal ? name); Pattern -1 name; Case name.

Theorem Zmax1: (a, b : ?)  (Zle a (Zmax a b)).
Proof.
Intros a b; Unfold Zmax; (CaseEq '(Zcompare a b)); Simpl; Auto with zarith.
Unfold Zle; Intros H; Rewrite H; Red; Intros; Discriminate.
Qed.

Theorem Zmax2: (a, b : ?)  (Zle b (Zmax a b)).
Proof.
Intros a b; Unfold Zmax; (CaseEq '(Zcompare a b)); Simpl; Auto with zarith.
Intros H;
 (Case (Zle_or_lt b a); Auto; Unfold Zlt; Rewrite H; Intros; Discriminate).
Intros H;
 (Case (Zle_or_lt b a); Auto; Unfold Zlt; Rewrite H; Intros; Discriminate).
Qed.

