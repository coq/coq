(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

Extraction nat.
(* 
type nat = 
  |  O 
  | S of nat 
*)

Extraction [x:nat]x.
(* fun x -> x *)

Inductive c [x:nat] : nat -> Set :=
    refl : (c x x)                  
  | trans : (y,z:nat)(c x y)->(le y z)->(c x z).
Extraction c.
(* 
type c =
  | Refl
  | Trans of nat * nat * c
*)

Extraction [f:nat->nat][x:nat](f x).
(* fun f x -> f x *)

Extraction [f:nat->Set->nat][x:nat](f x nat).
(* fun f x -> f x () *)

Extraction [f:(nat->nat)->nat][x:nat][g:nat->nat](f g).
(* fun f x g -> f g *)

Extraction (pair ? ? (S O) O).
(* Pair ((S O), O) *)

Definition cf :=  [x:nat][_:(le x O)](S x).
Extraction (cf O (le_n O)).  
(* cf O *)

Extraction ([X:Set][x:X]x nat).
(* fun x -> x *)

Definition d := [X:Type]X.
Extraction d. (* type 'x d = 'x *)
Extraction (d Set). (* unit d *)
Extraction [x:(d Set)]O. (* fun _ -> O *)
Extraction (d nat). (* nat d *)

Extraction ([x:(d Type)]O Type).  (* O *)

Extraction ([x:(d Type)]x).  (* 'a1 *)

Extraction ([X:Type][x:X]x Set nat). (* nat *)

Definition id' := [X:Type][x:X]x.      
Extraction id'. (* let id' x = x *)
Extraction (id' Set nat). (* nat *)

Extraction let t = nat in (id' Set t).  (* nat *)

Definition Ensemble := [U:Type]U->Prop.
Definition Empty_set := [U:Type][x:U]False.
Definition Add := [U:Type][A:(Ensemble U)][x:U][y:U](A y) \/ x==y.

Inductive Finite [U:Type] : (Ensemble U) -> Set :=
      Empty_is_finite: (Finite U (Empty_set U))
   |  Union_is_finite:
      (A: (Ensemble U)) (Finite U A) -> 
      (x: U) ~ (A x) -> (Finite U (Add U A x)).
Extraction Finite.
(* 
type 'u finite =
  | Empty_is_finite
  | Union_is_finite of 'u finite * 'u
*)

Extraction ([X:Type][x:X]O Type Type). (* O *)

Extraction let n=O in let p=(S n) in (S p). (* S (S O) *)

Extraction (x:(X:Type)X->X)(x Type Type). 
(* (unit -> Obj.t -> Obj.t) -> Obj.t *)

(** Mutual Inductive *)

Inductive tree : Set := 
   Node : nat -> forest -> tree
with forest : Set :=
 | Leaf : nat -> forest
 | Cons : tree -> forest -> forest .

Extraction tree.
(* 
type tree =
  | Node of nat * forest
and forest =
  | Leaf of nat
  | Cons of tree * forest
*)

Fixpoint tree_size [t:tree] : nat :=
         Cases t of (Node a f) => (S (forest_size f)) end
with forest_size [f:forest] : nat :=
         Cases f of 
	 | (Leaf b) => (S O)
         | (Cons t f') => (plus (tree_size t) (forest_size f'))
         end.

Extraction tree_size.
(* 
let rec tree_size = function
  | Node (a, f) -> S (forest_size f)
and forest_size = function
  | Leaf b -> S O
  | Cons (t, f') -> plus (tree_size t) (forest_size f')
*)

Extraction Cases (left True True I) of (left x)=>(S O) | (right x)=>O end.
(* S O *)

Extraction sumbool_rect.
(* 
let sumbool_rect f0 f = function
  |  Left -> f0 ()
  | Right -> f ()
*)

Inductive predicate : Type := 
  | Atom : Prop -> predicate
  | EAnd  : predicate -> predicate -> predicate.
Extraction predicate.
(* 
type predicate =
  | Atom
  | EAnd of predicate * predicate
*)

(** Eta-expansions of inductive constructor *)

Inductive titi : Set := tata : nat->nat->nat->nat->titi.
Extraction (tata O).
(* fun x x0 x1 -> Tata (O, x, x0, x1) *)
Extraction (tata O (S O)).
(* fun x x0 -> Tata (O, (S O), x, x0) *)

Inductive eta : Set := eta_c : nat->Prop->nat->Prop->eta.
Extraction eta_c.
(* 
type eta =
  | Eta_c of nat * nat
*)
Extraction (eta_c O).
(* fun _ x _ -> Eta_c (O, x) *)
Extraction (eta_c O True).
(* fun x _ -> Eta_c (O, x) *)
Extraction (eta_c O True O).
(* fun _ -> Eta_c (O, O) *)


(** Example of singleton inductive type *)

Inductive bidon [A:Prop;B:Type] : Set := tb : (x:A)(y:B)(bidon A B). 
Definition fbidon := [A,B:Type][f:A->B->(bidon True nat)][x:A][y:B](f x y).
Extraction bidon.
(* type 'b bidon = 'b *)
Extraction tb.
(* tb : singleton inductive constructor *)
Extraction fbidon.
(* let fbidon f x y =
  f x y
*)
Extraction (fbidon True nat (tb True nat)).
(* fun x0 x -> fbidon (fun _ x1 -> x1) x0 x *)
Definition fbidon2 := (fbidon True nat (tb True nat)).
Extraction fbidon2. 
(* let fbidon2 x =
  x 
*)
(** NB: first argument of fbidon2 has type [True], so it disappears. *)

(** mutual inductive on many sorts *)

Inductive 
  test0 : Prop := ctest0 : test0 
with 
  test1 : Set := ctest1 : test0-> test1.  
Extraction test0.
(* test0 : logical inductive *)
Extraction test1. 
(* 
type test1 =
  | Ctest1
*)

(** logical singleton *)

Extraction eq.
(* eq : logical inductive *)
Extraction eq_rect.
(* let eq_rect x f y =
  f
*)

(** example with more arguments that given by the type *)

Extraction (nat_rec [n:nat]nat->nat [n:nat]O [n:nat][f:nat->nat]f O O).
(* nat_rec (fun n -> O) (fun n f -> f) O O *)


(** No more propagation of type parameters. Obj.t instead. *)

Inductive tp1 : Set := 
  T : (C:Set)(c:C)tp2 -> tp1 with tp2 : Set  := T' : tp1->tp2.
Extraction tp1.
(* 
type tp1 =
  | T of Obj.t * tp2
and tp2 =
  | T' of tp1
*) 

Inductive tp1bis : Set := 
  Tbis : tp2bis -> tp1bis 
with tp2bis : Set  := T'bis : (C:Set)(c:C)tp1bis->tp2bis.
Extraction tp1bis.
(* 
type tp1bis =
  | Tbis of tp2bis
and tp2bis =
  | T'bis of Obj.t * tp1bis
*)

(** casts *)

Extraction (True :: Type).
(* unit *)

(* examples needing Obj.magic *)
(* hybrids *)

Definition horibilis := [b:bool]<[b:bool]if b then Type else nat>if b then Set else O.
Extraction horibilis.
(* 
let horibilis = function
  | True -> ()
  | False -> O
*)

Definition PropSet := [b:bool]if b then Prop else Set.
Extraction PropSet. (* type propSet = Obj.t *)

Definition natbool := [b:bool]if b then nat else bool.
Extraction natbool. (* type natbool = Obj.t *)

Definition zerotrue := [b:bool]<natbool>if b then O else true.
Extraction zerotrue. 
(* 
let zerotrue = function
  | True -> O
  | False -> True
*)

Definition natProp := [b:bool]<[_:bool]Type>if b then nat else Prop.

Definition natTrue := [b:bool]<[_:bool]Type>if b then nat else True.

Definition zeroTrue := [b:bool]<natProp>if b then O else True.
Extraction zeroTrue.
(* 
let zeroTrue = function
  | True -> O
  | False -> ()
*)

Definition natTrue2 := [b:bool]<[_:bool]Type>if b then nat else True.

Definition zeroprop := [b:bool]<natTrue>if b then O else I.
Extraction zeroprop.
(* 
let zeroprop = function
  | True -> O
  | False -> ()
*)

(** instanciations Type -> Prop *)

(** polymorphic f applied several times *)

Extraction (pair ? ? (id' nat O) (id' bool true)).
(* Pair ((id' O), (id' True)) *)

(** ok *)

Extraction 
([i:(X:Type)X->X](pair ? ? (i nat O) (i bool true)) [X:Type][x:X]x).
(* let i = fun x -> x in Pair ((i O), (i True)) *)


(* still ok via optim beta -> let *)

Extraction [i:(X:Type)X->X](pair ? ? (i nat O) (i bool true)).
(* fun i -> Pair ((i () O), (i () True)) *)

(* problem: fun f -> (f 0, f true) not legal in ocaml *)
(* solution: fun f -> (f 0, Obj.magic f true) *)


Definition funPropSet:= 
 [b:bool]<[_:bool]Type>if b then (X:Prop)X->X else (X:Set)X->X.

(* Definition funPropSet2:=
 [b:bool](X:if b then Prop else Set)X->X. *)

Definition idpropset := 
 [b:bool]<funPropSet>if b then [X:Prop][x:X]x else [X:Set][x:X]x.

(* Definition proprop := [b:bool]((idpropset b) (natTrue b) (zeroprop b)). *)

Definition funProp := [b:bool][x:True]<natTrue>if b then O else x.

(*s prop and arity can be applied.... *)

Definition f : (X:Type)(nat->X)->(X->bool)->bool := 
 [X:Type;x:nat->X;y:X->bool](y (x O)).
Extraction f.
(* let f x y =
  y (x O)
*)

Definition f_prop := (f (O=O) [_](refl_equal ? O) [_]true).
Extraction NoInline f.
Extraction f_prop.
(* let f_prop =
  f () (fun _ -> True)
*)

Definition f_arity := (f Set [_:nat]nat [_:Set]true).
Extraction f_arity.
(* let f_arity =
  f () (fun _ -> True)
*)

Definition f_normal := (f nat [x]x [x](Cases x of O => true | _ => false end)).
Extraction f_normal.
(* let f_normal =
  f (fun x -> x) (fun x -> match x with
                             | O -> True
                             | S n -> False)
*)

Inductive Truc : Set->Set :=
       chose  : (A:Set)(Truc A)
     | machin : (A:Set)A->(Truc bool)->(Truc A).
Extraction Truc.
(*
type 'x truc =
  | Chose
  | Machin of 'x * bool truc
*)

(** False conversion of type: *)

Require PolyList.

Lemma oups : (H:(nat==(list nat)))nat -> nat.
Intros.
Generalize H0;Intros.
Rewrite H in H1.
Case H1.
Exact H0.
Intros.
Exact n.
Qed.
Extraction oups.
(* 
let oups h0 = match h0 with
  | Nil -> h0
  | Cons0 (n, l) -> n
*)




