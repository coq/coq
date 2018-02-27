(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Coq.extraction.Extraction.
Require Import Arith.
Require Import List.

(**** A few tests for the extraction mechanism ****)

(* Ideally, we should monitor the extracted output
   for changes, but this is painful. For the moment,
   we just check for failures of this script. *)

(*** STANDARD EXAMPLES *)

(** Functions. *)

Definition idnat (x:nat) := x.
Extraction idnat.
(* let idnat x = x *)

Definition id (X:Type) (x:X) := x.
Extraction id. (* let id x = x *)
Definition id' := id Set nat.
Extraction id'. (* type id' = nat *)

Definition test2 (f:nat -> nat) (x:nat) := f x.
Extraction test2.
(* let test2 f x = f x *)

Definition test3 (f:nat -> Set -> nat) (x:nat) := f x nat.
Extraction test3.
(* let test3 f x = f x __ *)

Definition test4 (f:(nat -> nat) -> nat) (x:nat) (g:nat -> nat) := f g.
Extraction test4.
(* let test4 f x g = f g *)

Definition test5 := (1, 0).
Extraction test5.
(* let test5 = Pair ((S O), O) *)

Definition cf (x:nat) (_:x <= 0) := S x.
Extraction NoInline cf.
Definition test6 := cf 0 (le_n 0).
Extraction test6.
(* let test6 = cf O *)

Definition test7 := (fun (X:Set) (x:X) => x) nat.
Extraction test7.
(* let test7 x = x *)

Definition d (X:Type) := X.
Extraction d. (* type 'x d = 'x *)
Definition d2 := d Set.
Extraction d2. (* type d2 = __ d *)
Definition d3 (x:d Set) := 0.
Extraction d3. (* let d3 _ = O *)
Definition d4 := d nat.
Extraction d4. (* type d4 = nat d *)
Definition d5 := (fun x:d Type => 0) Type.
Extraction d5.  (* let d5 = O *)
Definition d6 (x:d Type) := x.
Extraction d6.  (* type 'x d6 = 'x *)

Definition test8 := (fun (X:Type) (x:X) => x) Set nat.
Extraction test8. (* type test8 = nat *)

Definition test9 := let t := nat in id Set t.
Extraction test9.  (* type test9 = nat *)

Definition test10 := (fun (X:Type) (x:X) => 0) Type Type.
Extraction test10. (* let test10 = O *)

Definition test11 := let n := 0 in let p := S n in S p.
Extraction test11. (* let test11 = S (S O) *)

Definition test12 := forall x:forall X:Type, X -> X, x Type Type.
Extraction test12.
(* type test12 = (__ -> __ -> __) -> __ *)


Definition test13 := match @left True True I with
                     | left x => 1
                     | right x => 0
                     end.
Extraction test13. (* let test13 = S O *)


(** example with more arguments that given by the type *)

Definition test19 :=
  nat_rec (fun n:nat => nat -> nat) (fun n:nat => 0)
    (fun (n:nat) (f:nat -> nat) => f) 0 0.
Extraction test19.
(* let test19 =
  let rec f = function
    | O -> (fun n0 -> O)
    | S n0 -> f n0
  in f O O
*)


(** casts *)

Definition test20 := True:Type.
Extraction test20.
(* type test20 = __ *)


(** Simple inductive type and recursor. *)

Extraction nat.
(*
type nat =
  | O
  | S of nat
*)

Extraction sumbool_rect.
(*
let sumbool_rect f f0 = function
  |  Left -> f __
  | Right -> f0 __
*)

(** Less simple inductive type. *)

Inductive c (x:nat) : nat -> Set :=
  | refl : c x x
  | trans : forall y z:nat, c x y -> y <= z -> c x z.
Extraction c.
(*
type c =
  | Refl
  | Trans of nat * nat * c
*)

Definition Ensemble (U:Type) := U -> Prop.
Definition Empty_set (U:Type) (x:U) := False.
Definition Add (U:Type) (A:Ensemble U) (x y:U) := A y \/ x = y.

Inductive Finite (U:Type) : Ensemble U -> Type :=
  | Empty_is_finite : Finite U (Empty_set U)
  | Union_is_finite :
      forall A:Ensemble U,
        Finite U A -> forall x:U, ~ A x -> Finite U (Add U A x).
Extraction Finite.
(*
type 'u finite =
  | Empty_is_finite
  | Union_is_finite of 'u finite * 'u
*)


(** Mutual Inductive *)

Inductive tree : Set :=
    Node : nat -> forest -> tree
with forest : Set :=
  | Leaf : nat -> forest
  | Cons : tree -> forest -> forest.

Extraction tree.
(*
type tree =
  | Node of nat * forest
and forest =
  | Leaf of nat
  | Cons of tree * forest
*)

Fixpoint tree_size (t:tree) : nat :=
  match t with
  | Node a f => S (forest_size f)
  end

 with forest_size (f:forest) : nat :=
  match f with
  | Leaf b => 1
  | Cons t f' => tree_size t + forest_size f'
  end.

Extraction tree_size.
(*
let rec tree_size = function
  | Node (a, f) -> S (forest_size f)
and forest_size = function
  | Leaf b -> S O
  | Cons (t, f') -> plus (tree_size t) (forest_size f')
*)


(** Eta-expansions of inductive constructor *)

Inductive titi : Set :=
    tata : nat -> nat -> nat -> nat -> titi.
Definition test14 := tata 0.
Extraction test14.
(* let test14 x x0 x1 = Tata (O, x, x0, x1) *)
Definition test15 := tata 0 1.
Extraction test15.
(* let test15 x x0 = Tata (O, (S O), x, x0) *)

Inductive eta : Type :=
    eta_c : nat -> Prop -> nat -> Prop -> eta.
Extraction eta_c.
(*
type eta =
  | Eta_c of nat * nat
*)
Definition test16 := eta_c 0.
Extraction test16.
(* let test16 x = Eta_c (O, x) *)
Definition test17 := eta_c 0 True.
Extraction test17.
(* let test17 x = Eta_c (O, x) *)
Definition test18 := eta_c 0 True 0.
Extraction test18.
(* let test18 _ = Eta_c (O, O) *)


(** Example of singleton inductive type *)

Inductive bidon (A:Prop) (B:Type) : Type :=
    tb : forall (x:A) (y:B), bidon A B.
Definition fbidon (A B:Type) (f:A -> B -> bidon True nat)
  (x:A) (y:B) := f x y.
Extraction bidon.
(* type 'b bidon = 'b *)
Extraction tb.
(* tb : singleton inductive constructor *)
Extraction fbidon.
(* let fbidon f x y =
  f x y
*)

Definition fbidon2 := fbidon True nat (tb True nat).
Extraction fbidon2. (* let fbidon2 y = y *)
Extraction NoInline fbidon.
Extraction fbidon2.
(* let fbidon2 y = fbidon (fun _ x -> x) __ y *)

(* NB: first argument of fbidon2 has type [True], so it disappears. *)

(** mutual inductive on many sorts *)

Inductive test_0 : Prop :=
    ctest0 : test_0
with test_1 : Set :=
    ctest1 : test_0 -> test_1.
Extraction test_0.
(* test0 : logical inductive *)
Extraction test_1.
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

(** No more propagation of type parameters. Obj.t instead. *)

Inductive tp1 : Type :=
    T : forall (C:Set) (c:C), tp2 -> tp1
with tp2 : Type :=
    T' : tp1 -> tp2.
Extraction tp1.
(*
type tp1 =
  | T of __ * tp2
and tp2 =
  | T' of tp1
*)

Inductive tp1bis : Type :=
    Tbis : tp2bis -> tp1bis
with tp2bis : Type :=
    T'bis : forall (C:Set) (c:C), tp1bis -> tp2bis.
Extraction tp1bis.
(*
type tp1bis =
  | Tbis of tp2bis
and tp2bis =
  | T'bis of __ * tp1bis
*)


(** Strange inductive type. *)

Inductive Truc : Set -> Type :=
  | chose : forall A:Set, Truc A
  | machin : forall A:Set, A -> Truc bool -> Truc A.
Extraction Truc.
(*
type 'x truc =
  | Chose
  | Machin of 'x * bool truc
*)


(** Dependant type over Type *)

Definition test24 := sigT (fun a:Set => option a).
Extraction test24.
(* type test24 = (__, __ option) sigT *)


(** Coq term non strongly-normalizable after extraction *)

Require Import Gt.
Definition loop (Ax:Acc gt 0) :=
  (fix F (a:nat) (b:Acc gt a) {struct b} : nat :=
     F (S a) (Acc_inv b (S a) (gt_Sn_n a))) 0 Ax.
Extraction loop.
(* let loop _ =
  let rec f a =
    f (S a)
  in f O
*)

(*** EXAMPLES NEEDING OBJ.MAGIC *)

(** False conversion of type: *)

Lemma oups : forall H:nat = list nat, nat -> nat.
intros.
generalize H0; intros.
rewrite H in H1.
case H1.
exact H0.
intros.
exact n.
Defined.
Extraction oups.
(*
let oups h0 =
  match Obj.magic h0 with
    | Nil -> h0
    | Cons0 (n, l) -> n
*)


(** hybrids *)

Definition horibilis (b:bool) :=
  if b as b return (if b then Type else nat) then Set else 0.
Extraction horibilis.
(*
let horibilis = function
  | True -> Obj.magic __
  | False -> Obj.magic O
*)

Definition PropSet (b:bool) := if b then Prop else Set.
Extraction PropSet. (* type propSet = __ *)

Definition natbool (b:bool) := if b then nat else bool.
Extraction natbool. (* type natbool = __ *)

Definition zerotrue (b:bool) := if b as x return natbool x then 0 else true.
Extraction zerotrue.
(*
let zerotrue = function
  | True -> Obj.magic O
  | False -> Obj.magic True
*)

Definition natProp (b:bool) := if b return Type then nat else Prop.

Definition natTrue (b:bool) := if b return Type then nat else True.

Definition zeroTrue (b:bool) := if b as x return natProp x then 0 else True.
Extraction zeroTrue.
(*
let zeroTrue = function
  | True -> Obj.magic O
  | False -> Obj.magic __
*)

Definition natTrue2 (b:bool) := if b return Type then nat else True.

Definition zeroprop (b:bool) := if b as x return natTrue x then 0 else I.
Extraction zeroprop.
(*
let zeroprop = function
  | True -> Obj.magic O
  | False -> Obj.magic __
*)

(** polymorphic f applied several times *)

Definition test21 := (id nat 0, id bool true).
Extraction test21.
(* let test21 = Pair ((id O), (id True)) *)

(** ok *)

Definition test22 :=
  (fun f:forall X:Type, X -> X => (f nat 0, f bool true))
    (fun (X:Type) (x:X) => x).
Extraction test22.
(* let test22 =
  let f = fun x -> x in Pair ((f O), (f True)) *)

(* still ok via optim beta -> let *)

Definition test23 (f:forall X:Type, X -> X) := (f nat 0, f bool true).
Extraction test23.
(* let test23 f = Pair ((Obj.magic f __ O), (Obj.magic f __ True)) *)

(* problem: fun f -> (f 0, f true) not legal in ocaml *)
(* solution: magic ... *)


(** Dummy constant __ can be applied.... *)

Definition f (X:Type) (x:nat -> X) (y:X -> bool) : bool := y (x 0).
Extraction f.
(* let f x y =
  y (x O)
*)

Definition f_prop := f (0 = 0) (fun _ => refl_equal 0) (fun _ => true).
Extraction NoInline f.
Extraction f_prop.
(* let f_prop =
  f (Obj.magic __) (fun _ -> True)
*)

Definition f_arity := f Set (fun _:nat => nat) (fun _:Set => true).
Extraction f_arity.
(* let f_arity =
  f (Obj.magic __) (fun _ -> True)
*)

Definition f_normal :=
  f nat (fun x => x) (fun x => match x with
                               | O => true
                               | _ => false
                               end).
Extraction f_normal.
(* let f_normal =
  f (fun x -> x) (fun x -> match x with
                             | O -> True
                             | S n -> False)
*)


(* inductive with magic needed *)

Inductive Boite : Set :=
    boite : forall b:bool, (if b then nat else (nat * nat)%type) -> Boite.
Extraction Boite.
(*
type boite =
  | Boite of bool * __
*)


Definition boite1 := boite true 0.
Extraction boite1.
(* let boite1 = Boite (True, (Obj.magic O)) *)

Definition boite2 := boite false (0, 0).
Extraction boite2.
(* let boite2 = Boite (False, (Obj.magic (Pair (O, O)))) *)

Definition test_boite (B:Boite) :=
  match B return nat with
  | boite true n => n
  | boite false n => fst n + snd n
  end.
Extraction test_boite.
(*
let test_boite = function
  | Boite (b0, n) ->
      (match b0 with
         | True -> Obj.magic n
         | False -> plus (fst (Obj.magic n)) (snd (Obj.magic n)))
*)

(* singleton inductive with magic needed *)

Inductive Box : Type :=
    box : forall A:Set, A -> Box.
Extraction Box.
(* type box = __ *)

Definition box1 := box nat 0.
Extraction box1. (* let box1 = Obj.magic O *)

(* applied constant, magic needed *)

Definition idzarb (b:bool) (x:if b then nat else bool) := x.
Definition zarb := idzarb true 0.
Extraction NoInline idzarb.
Extraction zarb.
(* let zarb = Obj.magic idzarb True (Obj.magic O) *)

(** function of variable arity. *)
(** Fun n = nat -> nat -> ... -> nat *)

Fixpoint Fun (n:nat) : Set :=
  match n with
  | O => nat
  | S n => nat -> Fun n
  end.

Fixpoint Const (k n:nat) {struct n} : Fun n :=
  match n as x return Fun x with
  | O => k
  | S n => fun p:nat => Const k n
  end.

Fixpoint proj (k n:nat) {struct n} : Fun n :=
  match n as x return Fun x with
  | O => 0 (* ou assert false ....*)
  | S n =>
      match k with
      | O => fun x => Const x n
      | S k => fun x => proj k n
      end
  end.

Definition test_proj := proj 2 4 0 1 2 3.

Eval compute in test_proj.

Recursive Extraction test_proj.



(*** TO SUM UP: ***)

Module Everything.
 Definition idnat := idnat.
 Definition id := id.
 Definition id' := id'.
 Definition test2 := test2.
 Definition test3 := test3.
 Definition test4 := test4.
 Definition test5 := test5.
 Definition test6 := test6.
 Definition test7 := test7.
 Definition d := d.
 Definition d2 := d2.
 Definition d3 := d3.
 Definition d4 := d4.
 Definition d5 := d5.
 Definition d6 := d6.
 Definition test8 := test8.
 Definition test9 := test9.
 Definition test10 := test10.
 Definition test11 := test11.
 Definition test12 := test12.
 Definition test13 := test13.
 Definition test19 := test19.
 Definition test20 := test20.
 Definition nat := nat.
 Definition sumbool_rect := sumbool_rect.
 Definition c := c.
 Definition Finite := Finite.
 Definition tree := tree.
 Definition tree_size := tree_size.
 Definition test14 := test14.
 Definition test15 := test15.
 Definition eta_c := eta_c.
 Definition test16 := test16.
 Definition test17 := test17.
 Definition test18 := test18.
 Definition bidon := bidon.
 Definition tb := tb.
 Definition fbidon := fbidon.
 Definition fbidon2 := fbidon2.
 Definition test_0 := test_0.
 Definition test_1 := test_1.
 Definition eq_rect := eq_rect.
 Definition tp1 := tp1.
 Definition tp1bis := tp1bis.
 Definition Truc := Truc.
 Definition oups := oups.
 Definition test24 := test24.
 Definition loop := loop.
 Definition horibilis := horibilis.
 Definition PropSet := PropSet.
 Definition natbool := natbool.
 Definition zerotrue := zerotrue.
 Definition zeroTrue := zeroTrue.
 Definition zeroprop := zeroprop.
 Definition test21 := test21.
 Definition test22 := test22.
 Definition test23 := test23.
 Definition f := f.
 Definition f_prop := f_prop.
 Definition f_arity := f_arity.
 Definition f_normal := f_normal.
 Definition Boite := Boite.
 Definition boite1 := boite1.
 Definition boite2 := boite2.
 Definition test_boite := test_boite.
 Definition Box := Box.
 Definition box1 := box1.
 Definition zarb := zarb.
 Definition test_proj := test_proj.
End Everything.

(* Extraction "test_extraction.ml" Everything. *)
Recursive Extraction Everything.
(* Check that the previous OCaml code is compilable *)
Extraction TestCompile Everything.

Extraction Language Haskell.
(* Extraction "Test_extraction.hs" Everything. *)
Recursive Extraction Everything.

Extraction Language Scheme.
(* Extraction "test_extraction.scm" Everything. *)
Recursive Extraction Everything.


(*** Finally, a test more focused on everyday's life situations ***)

Require Import ZArith.

Extraction Language OCaml.
Recursive Extraction Z_modulo_2 Zdiv_eucl_exist.
Extraction TestCompile Z_modulo_2 Zdiv_eucl_exist.
