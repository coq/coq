(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(* Definition mutuellement inductive et dependante *)

Require Export PolyList.

 Record signature : Type := {
    sort : Set;
    sort_beq : sort->sort->bool;
    sort_beq_refl : (f:sort)true=(sort_beq f f);
    sort_beq_eq : (f1,f2:sort)true=(sort_beq f1 f2)->f1=f2;
    fsym :> Set;
    fsym_type : fsym->(list sort)*sort;
    fsym_beq : fsym->fsym->bool;
    fsym_beq_refl : (f:fsym)true=(fsym_beq f f);
    fsym_beq_eq : (f1,f2:fsym)true=(fsym_beq f1 f2)->f1=f2
  }.

 
 Variable F : signature.

  Definition vsym := (sort F)*nat.

  Definition vsym_sort := (fst (sort F) nat).
  Definition vsym_nat := (snd (sort F) nat).
 

  Mutual Inductive term : (sort F)->Set :=
  	| term_var : (v:vsym)(term (vsym_sort v))
	| term_app : (f:F)(list_term (Fst (fsym_type F f)))
		->(term (Snd (fsym_type F f)))
  with list_term : (list (sort F)) -> Set :=
	| term_nil : (list_term (nil (sort F)))
	| term_cons : (s:(sort F);l:(list (sort F)))
	  (term s)->(list_term l)->(list_term (cons s l)).

