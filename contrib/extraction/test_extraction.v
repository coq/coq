(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

Extraction nat.

Extraction [x:nat]x.

Inductive c [x:nat] : nat -> Set :=
    refl : (c x x)                  
  | trans : (y,z:nat)(c x y)->(le y z)->(c x z).
Extraction c.

Extraction [f:nat->nat][x:nat](f x).

Extraction [f:nat->Set->nat][x:nat](f x nat).

Extraction [f:(nat->nat)->nat][x:nat][g:nat->nat](f g).

Extraction (pair nat nat (S O) O).

Definition cf :=  [x:nat][_:(le x O)](S x).
Extraction (cf O (le_n O)).  

Extraction ([X:Set][x:X]x nat).

Definition d := [X:Type]X.

Extraction d.
Extraction (d Set).
Extraction [x:(d Set)]O.
Extraction (d nat).

Extraction ([x:(d Type)]O Type). 

Extraction ([x:(d Type)]x). 

Extraction ([X:Type][x:X]x Set nat).

Definition id' := [X:Type][x:X]x.      
Extraction id'.
Extraction (id' Set nat).

Extraction let t = nat in (id' Set t). 

Definition Ensemble := [U:Type]U->Prop.

Definition Empty_set := [U:Type][x:U]False.

Definition Add := [U:Type][A:(Ensemble U)][x:U][y:U](A y) \/ x==y.

Inductive Finite [U:Type] : (Ensemble U) -> Set :=
      Empty_is_finite: (Finite U (Empty_set U))
   |  Union_is_finite:
      (A: (Ensemble U)) (Finite U A) -> 
      (x: U) ~ (A x) -> (Finite U (Add U A x)).
Extraction Finite.

Extraction ([X:Type][x:X]O Type Type).

Extraction let n=O in let p=(S n) in (S p).

Extraction (x:(X:Type)X->X)(x Type Type).

Inductive tree : Set := 
   Node : nat -> forest -> tree
with forest : Set :=
 | Leaf : nat -> forest
 | Cons : tree -> forest -> forest .

Extraction tree.

Fixpoint tree_size [t:tree] : nat :=
         Cases t of (Node a f) => (S (forest_size f)) end
with forest_size [f:forest] : nat :=
         Cases f of 
	 | (Leaf b) => (S O)
         | (Cons t f') => (plus (tree_size t) (forest_size f'))
         end.

Extraction tree_size.

Extraction Cases (left True True I) of (left x)=>(S O) | (right x)=>O end.

Extraction sumbool_rec.

Definition horibilis := [b:bool]<[b:bool]if b then Type else nat>if b then Set else O.

Extraction horibilis.

Inductive predicate : Type := 
  | Atom : Prop -> predicate
  | And  : predicate -> predicate -> predicate.

Extraction predicate.

(* eta-expansions *)
Inductive titi : Set := tata : nat->nat->nat->nat->titi.
Extraction (tata O).
Extraction (tata O (S O)).

Inductive eta : Set := eta_c : nat->Prop->nat->Prop->eta.
Extraction eta_c.
Extraction (eta_c O).
Extraction (eta_c O True).
Extraction (eta_c O True O).

Inductive bidon [A:Prop;B:Type] : Set := tb : (x:A)(y:B)(bidon A B). 
Definition fbidon := [A,B:Type][f:A->B->(bidon True nat)][x:A][y:B](f x y).

Extraction bidon.
Extraction fbidon.
Extraction (fbidon True nat (tb True nat)).

(* mutual inductive on many sorts *)
Inductive 
  test0 : Prop := ctest0 : test0 
with 
  test1 : Set := ctest1 : test0-> test1.  
Extraction test0.

Extraction eq.
Extraction eq_rec.

(* mutual fixpoints on many sorts ? *)

  (* TODO *)

(* example with more arguments that given by the type *)

Extraction (nat_rec [n:nat]nat->nat [n:nat]O [n:nat][f:nat->nat]f O O).
