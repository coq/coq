(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(****************************************************************************)
(*                            Bruno Barras                                  *)
(****************************************************************************)

Require Relation_Definitions.
Require Relation_Operators.


Section Properties.

  Variable A: Set.
  Variable R: (relation A).

  Local incl : (relation A)->(relation A)->Prop :=
      [R1,R2: (relation A)] (x,y:A) (R1 x y) -> (R2 x y).

Section Clos_Refl_Trans.

  Lemma clos_rt_is_preorder: (preorder A (clos_refl_trans A R)).
Apply Build_preorder.
Exact (rt_refl A R).

Exact (rt_trans A R).
Qed.



Lemma clos_rt_idempotent:
       (incl (clos_refl_trans A (clos_refl_trans A R))
                     (clos_refl_trans A R)).
Red.
NewInduction 1; Auto with sets.
Intros.
Apply rt_trans with y; Auto with sets.
Qed.

  Lemma  clos_refl_trans_ind_left: (A:Set)(R:A->A->Prop)(M:A)(P:A->Prop)
           (P M)
            ->((P0,N:A)
                (clos_refl_trans A R M P0)->(P P0)->(R P0 N)->(P N))
               ->(a:A)(clos_refl_trans A R M a)->(P a).
Intros.
Generalize H H0 .
Clear  H H0.
Elim H1; Intros; Auto with sets.
Apply H2 with x; Auto with sets.

Apply H3.
Apply H0; Auto with sets.

Intros.
Apply H5 with P0; Auto with sets.
Apply rt_trans with y; Auto with sets.
Qed.


End Clos_Refl_Trans.


Section Clos_Refl_Sym_Trans.

  Lemma clos_rt_clos_rst: (inclusion A (clos_refl_trans A R)
				        (clos_refl_sym_trans A R)).
Red.
NewInduction 1; Auto with sets.
Apply rst_trans with y; Auto with sets.
Qed.

  Lemma clos_rst_is_equiv: (equivalence A (clos_refl_sym_trans A R)).
Apply Build_equivalence.
Exact (rst_refl A R).

Exact (rst_trans A R).

Exact (rst_sym A R).
Qed.

  Lemma clos_rst_idempotent:
       (incl (clos_refl_sym_trans A (clos_refl_sym_trans A R))
                     (clos_refl_sym_trans A R)).
Red.
NewInduction 1; Auto with sets.
Apply rst_trans with y; Auto with sets.
Qed.

End Clos_Refl_Sym_Trans.

End Properties.
