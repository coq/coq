(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(****************************************************************************)
(*                      Bruno Barras, Cristina Cornes                       *)
(*                                                                          *)
(*  Some of these definitons were taken from :                              *)
(*     Constructing Recursion Operators in Type Theory                      *)
(*     L. Paulson  JSC (1986) 2, 325-355                                    *)
(****************************************************************************)

Require Relation_Definitions.
Require PolyList.
Require PolyListSyntax.

(** Some operators to build relations *)

Section Transitive_Closure.
  Variable A: Set.
  Variable R: (relation A).

  Inductive clos_trans : A->A->Prop :=
     t_step: (x,y:A)(R x y)->(clos_trans x y)
   | t_trans: (x,y,z:A)(clos_trans x y)->(clos_trans y z)->(clos_trans x z).
End Transitive_Closure.


Section Reflexive_Transitive_Closure.
  Variable A: Set.
  Variable R: (relation A).

  Inductive clos_refl_trans: (relation A) :=
    rt_step: (x,y:A)(R x y)->(clos_refl_trans x y)
  | rt_refl: (x:A)(clos_refl_trans x x)
  | rt_trans: (x,y,z: A)(clos_refl_trans x y)->(clos_refl_trans y z)
                      ->(clos_refl_trans x z).
End Reflexive_Transitive_Closure.


Section Reflexive_Symetric_Transitive_Closure.
  Variable A: Set.
  Variable R: (relation A).

  Inductive clos_refl_sym_trans: (relation A) :=
    rst_step: (x,y:A)(R x y)->(clos_refl_sym_trans x y)
  | rst_refl: (x:A)(clos_refl_sym_trans x x)
  | rst_sym: (x,y:A)(clos_refl_sym_trans x y)->(clos_refl_sym_trans y x)
  | rst_trans: (x,y,z:A)(clos_refl_sym_trans x y)->(clos_refl_sym_trans y z)
                      ->(clos_refl_sym_trans x z).
End Reflexive_Symetric_Transitive_Closure.


Section Transposee.
  Variable A: Set.
  Variable R: (relation A).

  Definition transp := [x,y:A](R y x).
End Transposee.


Section Union.
  Variable A: Set.
  Variable R1,R2: (relation A).

  Definition union := [x,y:A](R1 x y)\/(R2 x y).
End Union.


Section Disjoint_Union.
Variable A,B:Set.
Variable leA: A->A->Prop.
Variable leB: B->B->Prop.

Inductive le_AsB : A+B->A+B->Prop :=
   le_aa: (x,y:A) (leA x y) -> (le_AsB (inl A B x) (inl A B y))
|  le_ab: (x:A)(y:B) (le_AsB (inl A B x) (inr A B y))
|  le_bb: (x,y:B)  (leB x y) -> (le_AsB (inr A B x) (inr A B y)).

End Disjoint_Union. 



Section Lexicographic_Product.
(* Lexicographic order on dependent pairs *)

Variable A:Set.
Variable B:A->Set.
Variable leA: A->A->Prop.
Variable leB: (x:A)(B x)->(B x)->Prop.

Inductive lexprod : (sigS A B) -> (sigS A B) ->Prop :=
  left_lex : (x,x':A)(y:(B x)) (y':(B x')) 
               (leA x x') ->(lexprod (existS A B x y) (existS A B x' y'))
| right_lex : (x:A) (y,y':(B x)) 
                (leB x y y') -> (lexprod (existS A B x y) (existS A B x y')).
End Lexicographic_Product.


Section Symmetric_Product.
  Variable A:Set.
  Variable B:Set.
  Variable leA: A->A->Prop.
  Variable leB: B->B->Prop.

  Inductive symprod : (A*B) -> (A*B) ->Prop :=
     left_sym : (x,x':A)(leA x x')->(y:B)(symprod (x,y) (x',y))
  | right_sym : (y,y':B)(leB y y')->(x:A)(symprod (x,y) (x,y')).

End Symmetric_Product.


Section Swap.
  Variable A:Set.
  Variable R:A->A->Prop.

  Inductive swapprod: (A*A)->(A*A)->Prop :=
     sp_noswap: (x,x':A*A)(symprod A A R R x x')->(swapprod x x')
   | sp_swap: (x,y:A)(p:A*A)(symprod A A R R (x,y) p)->(swapprod (y,x) p).
End Swap.


Section Lexicographic_Exponentiation.

Variable A : Set.
Variable leA : A->A->Prop.
Local Nil := (nil A).
Local List := (list A).

Inductive Ltl : List->List->Prop :=
  Lt_nil: (a:A)(x:List)(Ltl Nil (cons a x))
| Lt_hd : (a,b:A) (leA a b)-> (x,y:(list A))(Ltl (cons a x) (cons b y))
| Lt_tl : (a:A)(x,y:List)(Ltl x y) -> (Ltl (cons a x) (cons a y)).


Inductive Desc : List->Prop :=
   d_nil : (Desc Nil)
|  d_one : (x:A)(Desc (cons x Nil))
|  d_conc : (x,y:A)(l:List)(leA x y) 
              -> (Desc l^(cons y Nil))->(Desc (l^(cons y Nil))^(cons x Nil)).

Definition  Pow :Set := (sig List Desc).

Definition lex_exp : Pow -> Pow ->Prop := 
      [a,b:Pow](Ltl (proj1_sig List Desc a) (proj1_sig  List Desc b)).

End Lexicographic_Exponentiation.

Hints Unfold transp union : sets v62.
Hints Resolve t_step rt_step rt_refl rst_step rst_refl : sets v62.
Hints Immediate rst_sym : sets v62.
