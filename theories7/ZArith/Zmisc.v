(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require BinInt.
Require Zcompare.
Require Zorder.
Require Zsyntax.
Require Bool.
V7only [Import Z_scope.].
Open Local Scope Z_scope.

(**********************************************************************)
(** Iterators *)

(** [n]th iteration of the function [f] *)
Fixpoint iter_nat[n:nat]  : (A:Set)(f:A->A)A->A :=
  [A:Set][f:A->A][x:A]
    Cases n of
      O => x
    | (S n') => (f (iter_nat n' A f x))
    end.

Fixpoint iter_pos[n:positive] : (A:Set)(f:A->A)A->A :=
  [A:Set][f:A->A][x:A]
    Cases n of
     	xH => (f x)
      | (xO n') => (iter_pos n' A f (iter_pos n' A f x))
      | (xI n') => (f (iter_pos n' A f (iter_pos n' A f x)))
    end.

Definition iter :=
  [n:Z][A:Set][f:A->A][x:A]Cases n of
    ZERO => x
  | (POS p) => (iter_pos p A f x)
  | (NEG p) => x
  end.

Theorem iter_nat_plus :
  (n,m:nat)(A:Set)(f:A->A)(x:A)
    (iter_nat (plus n m) A f x)=(iter_nat n A f (iter_nat m A f x)).
Proof.    
Induction n;
[ Simpl; Auto with arith
| Intros; Simpl; Apply f_equal with f:=f; Apply H
].  
Qed.

Theorem iter_convert : (n:positive)(A:Set)(f:A->A)(x:A)
  (iter_pos n A f x) = (iter_nat (convert n) A f x).
Proof.    
Intro n; NewInduction n as [p H|p H|];
[ Intros; Simpl; Rewrite -> (H A f x);
  Rewrite -> (H A f (iter_nat (convert p) A f x));
  Rewrite -> (ZL6 p); Symmetry; Apply f_equal with f:=f;
  Apply iter_nat_plus
| Intros; Unfold convert; Simpl; Rewrite -> (H A f x);
  Rewrite -> (H A f (iter_nat (convert p) A f x));
  Rewrite -> (ZL6 p); Symmetry;
  Apply iter_nat_plus
| Simpl; Auto with arith
].
Qed.

Theorem iter_pos_add :
  (n,m:positive)(A:Set)(f:A->A)(x:A)
    (iter_pos (add n m) A f x)=(iter_pos n A f (iter_pos m A f x)).
Proof.    
Intros n m; Intros.
Rewrite -> (iter_convert m A f x).
Rewrite -> (iter_convert n A f (iter_nat (convert m) A f x)).
Rewrite -> (iter_convert (add n m) A f x).
Rewrite -> (convert_add n m).
Apply iter_nat_plus.
Qed.

(** Preservation of invariants : if [f : A->A] preserves the invariant [Inv], 
    then the iterates of [f] also preserve it. *)

Theorem iter_nat_invariant :
  (n:nat)(A:Set)(f:A->A)(Inv:A->Prop)
  ((x:A)(Inv x)->(Inv (f x)))->(x:A)(Inv x)->(Inv (iter_nat n A f x)).
Proof.    
Induction n; Intros;
[ Trivial with arith
| Simpl; Apply H0 with x:=(iter_nat n0 A f x); Apply H; Trivial with arith].
Qed.

Theorem iter_pos_invariant :
  (n:positive)(A:Set)(f:A->A)(Inv:A->Prop)
  ((x:A)(Inv x)->(Inv (f x)))->(x:A)(Inv x)->(Inv (iter_pos n A f x)).
Proof.    
Intros; Rewrite iter_convert; Apply iter_nat_invariant; Trivial with arith.
Qed.

V7only [
(* Compatibility *)
Require Zbool.
Require Zeven.
Require Zabs.
Require Zmin.
Notation rename := rename.
Notation POS_xI := POS_xI.
Notation POS_xO := POS_xO.
Notation NEG_xI := NEG_xI.
Notation NEG_xO := NEG_xO.
Notation POS_add := POS_add.
Notation NEG_add := NEG_add.
Notation Zle_cases := Zle_cases.
Notation Zlt_cases := Zlt_cases.
Notation Zge_cases := Zge_cases.
Notation Zgt_cases := Zgt_cases.
Notation POS_gt_ZERO := POS_gt_ZERO.
Notation ZERO_le_POS := ZERO_le_POS.
Notation Zlt_ZERO_pred_le_ZERO := Zlt_ZERO_pred_le_ZERO.
Notation NEG_lt_ZERO := NEG_lt_ZERO.
Notation Zeven_not_Zodd := Zeven_not_Zodd.
Notation Zodd_not_Zeven := Zodd_not_Zeven.
Notation Zeven_Sn := Zeven_Sn.
Notation Zodd_Sn := Zodd_Sn.
Notation Zeven_pred := Zeven_pred.
Notation Zodd_pred := Zodd_pred.
Notation Zeven_div2 := Zeven_div2.
Notation Zodd_div2 := Zodd_div2.
Notation Zodd_div2_neg := Zodd_div2_neg.
Notation Z_modulo_2 := Z_modulo_2.
Notation Zsplit2 := Zsplit2.
Notation Zminus_Zplus_compatible := Zminus_Zplus_compatible.
Notation Zcompare_egal_dec := Zcompare_egal_dec.
Notation Zcompare_elim := Zcompare_elim.
Notation Zcompare_x_x := Zcompare_x_x.
Notation Zlt_not_eq := Zlt_not_eq.
Notation Zcompare_eq_case := Zcompare_eq_case.
Notation Zle_Zcompare := Zle_Zcompare.
Notation Zlt_Zcompare := Zlt_Zcompare.
Notation Zge_Zcompare := Zge_Zcompare.
Notation Zgt_Zcompare := Zgt_Zcompare.
Notation Zmin_plus := Zmin_plus.
Notation absolu_lt := absolu_lt.
Notation Zle_bool_imp_le := Zle_bool_imp_le.
Notation Zle_imp_le_bool := Zle_imp_le_bool.
Notation Zle_bool_refl := Zle_bool_refl.
Notation Zle_bool_antisym := Zle_bool_antisym.
Notation Zle_bool_trans := Zle_bool_trans.
Notation Zle_bool_plus_mono := Zle_bool_plus_mono.
Notation Zone_pos := Zone_pos.
Notation Zone_min_pos := Zone_min_pos.
Notation Zle_is_le_bool := Zle_is_le_bool.
Notation Zge_is_le_bool := Zge_is_le_bool.
Notation Zlt_is_le_bool := Zlt_is_le_bool.
Notation Zgt_is_le_bool := Zgt_is_le_bool.
Notation Zle_plus_swap := Zle_plus_swap.
Notation Zge_iff_le := Zge_iff_le.
Notation Zlt_plus_swap := Zlt_plus_swap.
Notation Zgt_iff_lt := Zgt_iff_lt.
Notation Zeq_plus_swap := Zeq_plus_swap.
(* Definitions *)
Notation entier_of_Z := entier_of_Z.
Notation Z_of_entier := Z_of_entier.
Notation Zle_bool := Zle_bool.
Notation Zge_bool := Zge_bool.
Notation Zlt_bool := Zlt_bool.
Notation Zgt_bool := Zgt_bool.
Notation Zeq_bool := Zeq_bool.
Notation Zneq_bool := Zneq_bool.
Notation Zeven := Zeven.
Notation Zodd := Zodd.
Notation Zeven_bool := Zeven_bool.
Notation Zodd_bool := Zodd_bool.
Notation Zeven_odd_dec := Zeven_odd_dec.
Notation Zeven_dec := Zeven_dec.
Notation Zodd_dec := Zodd_dec.
Notation Zdiv2_pos := Zdiv2_pos.
Notation Zdiv2 := Zdiv2.
Notation Zle_bool_total := Zle_bool_total.
Export Zbool.
Export Zeven.
Export Zabs.
Export Zmin.
Export Zorder.
Export Zcompare.
].
