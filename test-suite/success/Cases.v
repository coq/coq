(****************************************************************************)
(* Pattern-matching when non inductive terms occur                          *)

(* Dependent form of annotation *)
Type match 0 as n, @eq return nat with
     | O, x => 0
     | S x, y => x
     end.
Type match 0, 0, @eq return nat with
     | O, x, y => 0
     | S x, y, z => x
     end.
Type match 0, @eq, 0 return _ with
     | O, x, y => 0
     | S x, y, z => x
     end.

(* Non dependent form of annotation *)
Type match 0, @eq return nat with
     | O, x => 0
     | S x, y => x
     end.

(* Combining dependencies and non inductive arguments *)
Type
  (fun (A : Set) (a : A) (H : 0 = 0) =>
   match H in (_ = x), a return (H = H) with
   | _, _ => refl_equal H
   end).

(* Interaction with coercions *)
Parameter bool2nat : bool -> nat.
Coercion bool2nat : bool >-> nat.
Definition foo : nat -> nat :=
  fun x => match x with
             | O => true
             | S _ => 0
           end.

(****************************************************************************)
(* All remaining examples come from Cristina Cornes' V6 TESTS/MultCases.v   *)

Inductive IFExpr : Set :=
  | Var : nat -> IFExpr
  | Tr : IFExpr
  | Fa : IFExpr
  | IfE : IFExpr -> IFExpr -> IFExpr -> IFExpr.

Inductive List (A : Set) : Set :=
  | Nil : List A
  | Cons : A -> List A -> List A.

Inductive listn : nat -> Set :=
  | niln : listn 0
  | consn : forall n : nat, nat -> listn n -> listn (S n).

Inductive Listn (A : Set) : nat -> Set :=
  | Niln : Listn A 0
  | Consn : forall n : nat, nat -> Listn A n -> Listn A (S n).

Inductive Le : nat -> nat -> Set :=
  | LeO : forall n : nat, Le 0 n
  | LeS : forall n m : nat, Le n m -> Le (S n) (S m).

Inductive LE (n : nat) : nat -> Set :=
  | LE_n : LE n n
  | LE_S : forall m : nat, LE n m -> LE n (S m).

Require Import Bool.



Inductive PropForm : Set :=
  | Fvar : nat -> PropForm
  | Or : PropForm -> PropForm -> PropForm.

Section testIFExpr.
Definition Assign := nat -> bool.
Parameter Prop_sem : Assign -> PropForm -> bool.

Type
  (fun (A : Assign) (F : PropForm) =>
   match F return bool with
   | Fvar n => A n
   | Or F G => Prop_sem A F || Prop_sem A G
   end).

Type
  (fun (A : Assign) (H : PropForm) =>
   match H return bool with
   | Fvar n => A n
   | Or F G => Prop_sem A F || Prop_sem A G
   end).
End testIFExpr.



Type (fun x : nat => match x return nat with
                     | O => 0
                     | x => x
                     end).

Module Type testlist.
Parameter A : Set.
Inductive list : Set :=
  | nil : list
  | cons : A -> list -> list.
Parameter inf : A -> A -> Prop.


Definition list_Lowert2 (a : A) (l : list) :=
  match l return Prop with
  | nil => True
  | cons b l => inf a b
  end.

Definition titi (a : A) (l : list) :=
  match l return list with
  | nil => l
  | cons b l => l
  end.
End testlist.


(* To test translation *)
(* ------------------- *)


Type match 0 return nat with
     | O => 0
     | _ => 0
     end.

Type match 0 return nat with
     | O as b => b
     | S O => 0
     | S (S x) => x
     end.

Type match 0 with
     | O as b => b
     | S O => 0
     | S (S x) => x
     end.


Type (fun x : nat => match x return nat with
                     | O as b => b
                     | S x => x
                     end).

Type (fun x : nat => match x with
                     | O as b => b
                     | S x => x
                     end).

Type match 0 return nat with
     | O as b => b
     | S x => x
     end.

Type match 0 return nat with
     | x => x
     end.

Type match 0 with
     | x => x
     end.

Type match 0 return nat with
     | O => 0
     | S x as b => b
     end.

Type (fun x : nat => match x return nat with
                     | O => 0
                     | S x as b => b
                     end).

Type (fun x : nat => match x with
                     | O => 0
                     | S x as b => b
                     end).


Type match 0 return nat with
     | O => 0
     | S x => 0
     end.


Type match 0 return (nat * nat) with
     | O => (0, 0)
     | S x => (x, 0)
     end.

Type match 0 with
     | O => (0, 0)
     | S x => (x, 0)
     end.

Type
  match 0 return (nat -> nat) with
  | O => fun n : nat => 0
  | S x => fun n : nat => 0
  end.

Type match 0 with
     | O => fun n : nat => 0
     | S x => fun n : nat => 0
     end.


Type
  match 0 return (nat -> nat) with
  | O => fun n : nat => 0
  | S x => fun n : nat => x + n
  end.

Type match 0 with
     | O => fun n : nat => 0
     | S x => fun n : nat => x + n
     end.


Type match 0 return nat with
     | O => 0
     | S x as b => b + x
     end.

Type match 0 return nat with
     | O => 0
     | S a as b => b + a
     end.
Type match 0 with
     | O => 0
     | S a as b => b + a
     end.


Type match 0 with
     | O => 0
     | _ => 0
     end.

Type match 0 return nat with
     | O => 0
     | x => x
     end.

Type match 0, 1 return nat with
     | x, y => x + y
     end.

Type match 0, 1 with
     | x, y => x + y
     end.

Type match 0, 1 return nat with
     | O, y => y
     | S x, y => x + y
     end.

Type match 0, 1 with
     | O, y => y
     | S x, y => x + y
     end.


Type match 0, 1 return nat with
     | O, x => x
     | S y, O => y
     | x, y => x + y
     end.




Type match 0, 1 with
     | O, x => x + 0
     | S y, O => y + 0
     | x, y => x + y
     end.

Type
  match 0, 1 return nat with
  | O, x => x + 0
  | S y, O => y + 0
  | x, y => x + y
  end.


Type
  match 0, 1 return nat with
  | O, x => x
  | S x as b, S y => b + x + y
  | x, y => x + y
  end.


Type
  match 0, 1 with
  | O, x => x
  | S x as b, S y => b + x + y
  | x, y => x + y
  end.


Type
  (fun l : List nat =>
   match l return (List nat) with
   | Nil _ => Nil nat
   | Cons _ a l => l
   end).

Type (fun l : List nat => match l with
                          | Nil _ => Nil nat
                          | Cons _ a l => l
                          end).

Type match Nil nat return nat with
     | Nil _ => 0
     | Cons _ a l => S a
     end.
Type match Nil nat with
     | Nil _ => 0
     | Cons _ a l => S a
     end.

Type match Nil nat return (List nat) with
     | Cons _ a l => l
     | x => x
     end.

Type match Nil nat with
     | Cons _ a l => l
     | x => x
     end.

Type
  match Nil nat return (List nat) with
  | Nil _ => Nil nat
  | Cons _ a l => l
  end.

Type match Nil nat with
     | Nil _ => Nil nat
     | Cons _ a l => l
     end.


Type
  match 0 return nat with
  | O => 0
  | S x => match Nil nat return nat with
           | Nil _ => x
           | Cons _ a l => x + a
           end
  end.

Type
  match 0 with
  | O => 0
  | S x => match Nil nat with
           | Nil _ => x
           | Cons _ a l => x + a
           end
  end.

Type
  (fun y : nat =>
   match y with
   | O => 0
   | S x => match Nil nat with
            | Nil _ => x
            | Cons _ a l => x + a
            end
   end).


Type
  match 0, Nil nat return nat with
  | O, x => 0
  | S x, Nil _ => x
  | S x, Cons _ a l => x + a
  end.



Type
  (fun (n : nat) (l : listn n) =>
   match l return nat with
   | niln => 0
   | x => 0
   end).

Type (fun (n : nat) (l : listn n) => match l with
                                     | niln => 0
                                     | x => 0
                                     end).


Type match niln return nat with
     | niln => 0
     | x => 0
     end.

Type match niln with
     | niln => 0
     | x => 0
     end.

Type match niln return nat with
     | niln => 0
     | consn n a l => a
     end.
Type match niln with
     | niln => 0
     | consn n a l => a
     end.


Type
  match niln in (listn n) return nat with
  | consn m _ niln => m
  | _ => 1
  end.



Type
  (fun (n x : nat) (l : listn n) =>
   match x, l return nat with
   | O, niln => 0
   | y, x => 0
   end).

Type match 0, niln return nat with
     | O, niln => 0
     | y, x => 0
     end.


Type match niln, 0 return nat with
     | niln, O => 0
     | y, x => 0
     end.

Type match niln, 0 with
     | niln, O => 0
     | y, x => 0
     end.

Type match niln, niln return nat with
     | niln, niln => 0
     | x, y => 0
     end.

Type match niln, niln with
     | niln, niln => 0
     | x, y => 0
     end.

Type
  match niln, niln, niln return nat with
  | niln, niln, niln => 0
  | x, y, z => 0
  end.


Type match niln, niln, niln with
     | niln, niln, niln => 0
     | x, y, z => 0
     end.



Type match niln return nat with
     | niln => 0
     | consn n a l => 0
     end.

Type match niln with
     | niln => 0
     | consn n a l => 0
     end.


Type
  match niln, niln return nat with
  | niln, niln => 0
  | niln, consn n a l => n
  | consn n a l, x => a
  end.


Type
  match niln, niln with
  | niln, niln => 0
  | niln, consn n a l => n
  | consn n a l, x => a
  end.


Type
  (fun (n : nat) (l : listn n) =>
   match l return nat with
   | niln => 0
   | x => 0
   end).

Type
  (fun (c : nat) (s : bool) =>
   match c, s return nat with
   | O, _ => 0
   | _, _ => c
   end).

Type
  (fun (c : nat) (s : bool) =>
   match c, s return nat with
   | O, _ => 0
   | S _, _ => c
   end).


(* Rows of pattern variables: some tricky cases *)
Axioms (P : nat -> Prop) (f : forall n : nat, P n).

Type
  (fun i : nat =>
   match true, i as n return (P n) with
   | true, k => f k
   | _, k => f k
   end).

Type
  (fun i : nat =>
   match i as n, true return (P n) with
   | k, true => f k
   | k, _ => f k
   end).

(* Nested Cases: the SYNTH of the Cases on n used to make Multcase believe
 * it has to synthesize the predicate on O (which he can't)
 *)
Type
  match 0 as n return match n with
                      | O => bool
                      | S _ => nat
                      end with
  | O => true
  | S _ => 0
  end.

Type (fun (n : nat) (l : listn n) => match l with
                                     | niln => 0
                                     | x => 0
                                     end).

Type
  (fun (n : nat) (l : listn n) =>
   match l return nat with
   | niln => 0
   | consn n a niln => 0
   | consn n a (consn m b l) => n + m
   end).


Type
  (fun (n : nat) (l : listn n) =>
   match l with
   | niln => 0
   | consn n a niln => 0
   | consn n a (consn m b l) => n + m
   end).



Type
  (fun (n : nat) (l : listn n) =>
   match l return nat with
   | niln => 0
   | consn n a niln => 0
   | consn n a (consn m b l) => n + m
   end).

Type
  (fun (n : nat) (l : listn n) =>
   match l with
   | niln => 0
   | consn n a niln => 0
   | consn n a (consn m b l) => n + m
   end).


Type
  (fun (A : Set) (n : nat) (l : Listn A n) =>
   match l return nat with
   | Niln _ => 0
   | Consn _ n a (Niln _) => 0
   | Consn _ n a (Consn _ m b l) => n + m
   end).

Type
  (fun (A : Set) (n : nat) (l : Listn A n) =>
   match l with
   | Niln _ => 0
   | Consn _ n a (Niln _) => 0
   | Consn _ n a (Consn _ m b l) => n + m
   end).

Type
  (fun (A:Set) (n:nat) (l:Listn A n) =>
    match l return Listn A O with
      | Niln _ as b => b
      | Consn _  n a (Niln _ as b) => (Niln A)
      | Consn _ n a (Consn _ m b l) => (Niln A)
    end).

(*
Type
  (fun (A:Set) (n:nat) (l:Listn A n) =>
    match l with
      | Niln _ as b => b
      | Consn _ n a (Niln _ as b) => (Niln A)
      | Consn _ n a (Consn _ m b l) => (Niln A)
    end).
*)

Type
  (fun (A:Set) (n:nat) (l:Listn A n) =>
    match l return Listn A (S 0) with
      | Niln _ as b => Consn A O O b
      | Consn _ n a (Niln _) as L => L
      | Consn _ n a _ => Consn A O O (Niln A)
    end).

Type
  (fun (A:Set) (n:nat) (l:Listn A n) =>
    match l return Listn A (S 0) with
      | Niln _ as b => Consn A O O b
      | Consn _ n a (Niln _) as L => L
      | Consn _ n a _ => Consn A O O (Niln A)
    end).

(* To test treatment of as-patterns in depth *)
Type
  (fun (A : Set) (l : List A) =>
   match l with
   | Nil _ as b => Nil A
   | Cons _ a (Nil _) as L => L
   | Cons _ a (Cons _ b m) as L => L
   end).


Type
  (fun (n : nat) (l : listn n) =>
   match l return (listn n) with
   | niln => l
   | consn n a c => l
   end).
Type
  (fun (n : nat) (l : listn n) =>
   match l with
   | niln => l
   | consn n a c => l
   end).


Type
  (fun (n : nat) (l : listn n) =>
   match l return (listn n) with
   | niln as b => l
   | _ => l
   end).


Type
  (fun (n : nat) (l : listn n) => match l with
                                  | niln as b => l
                                  | _ => l
                                  end).

Type
  (fun (n : nat) (l : listn n) =>
   match l return (listn n) with
   | niln as b => l
   | x => l
   end).


Type
  (fun (A : Set) (n : nat) (l : Listn A n) =>
   match l with
   | Niln _ as b => l
   | _ => l
   end).

Type
  (fun (A : Set) (n : nat) (l : Listn A n) =>
   match l return (Listn A n) with
   | Niln _ => l
   | Consn _ n a (Niln _) => l
   | Consn _ n a (Consn _ m b c) => l
   end).

Type
  (fun (A : Set) (n : nat) (l : Listn A n) =>
   match l with
   | Niln _ => l
   | Consn _ n a (Niln _) => l
   | Consn _ n a (Consn _ m b c) => l
   end).

Type
  (fun (A : Set) (n : nat) (l : Listn A n) =>
   match l return (Listn A n) with
   | Niln _ as b => l
   | Consn _ n a (Niln _ as b) => l
   | Consn _ n a (Consn _ m b _) => l
   end).

Type
  (fun (A : Set) (n : nat) (l : Listn A n) =>
   match l with
   | Niln _ as b => l
   | Consn _ n a (Niln _ as b) => l
   | Consn _ n a (Consn _ m b _) => l
   end).


Type
  match niln return nat with
  | niln => 0
  | consn n a niln => 0
  | consn n a (consn m b l) => n + m
  end.


Type
  match niln with
  | niln => 0
  | consn n a niln => 0
  | consn n a (consn m b l) => n + m
  end.

Type match LeO 0 return nat with
     | LeO x => x
     | LeS n m h => n + m
     end.


Type match LeO 0 with
     | LeO x => x
     | LeS n m h => n + m
     end.

Type
  (fun (n : nat) (l : Listn nat n) =>
   match l return nat with
   | Niln _ => 0
   | Consn _ n a l => 0
   end).


Type
  (fun (n : nat) (l : Listn nat n) =>
   match l with
   | Niln _ => 0
   | Consn _ n a l => 0
   end).


Type match Niln nat with
     | Niln _ => 0
     | Consn _ n a l => 0
     end.

Type match LE_n 0 return nat with
     | LE_n _ => 0
     | LE_S _ m h => 0
     end.


Type match LE_n 0 with
     | LE_n _ => 0
     | LE_S _ m h => 0
     end.



Type match LE_n 0 with
     | LE_n _ => 0
     | LE_S _ m h => 0
     end.



Type
  match niln return nat with
  | niln => 0
  | consn n a niln => n
  | consn n a (consn m b l) => n + m
  end.

Type
  match niln with
  | niln => 0
  | consn n a niln => n
  | consn n a (consn m b l) => n + m
  end.


Type
  match Niln nat return nat with
  | Niln _ => 0
  | Consn _ n a (Niln _
) => n
  | Consn _ n a (Consn _ m b l) => n + m
  end.

Type
  match Niln nat with
  | Niln _ => 0
  | Consn _ n a (Niln _) => n
  | Consn _ n a (Consn _ m b l) => n + m
  end.


Type
  match LeO 0 return nat with
  | LeO x => x
  | LeS n m (LeO x) => x + m
  | LeS n m (LeS x y h) => n + x
  end.


Type
  match LeO 0 with
  | LeO x => x
  | LeS n m (LeO x) => x + m
  | LeS n m (LeS x y h) => n + x
  end.


Type
  match LeO 0 return nat with
  | LeO x => x
  | LeS n m (LeO x) => x + m
  | LeS n m (LeS x y h) => m
  end.

Type
  match LeO 0 with
  | LeO x => x
  | LeS n m (LeO x) => x + m
  | LeS n m (LeS x y h) => m
  end.


Type
  (fun (n m : nat) (h : Le n m) =>
   match h return nat with
   | LeO x => x
   | x => 0
   end).

Type (fun (n m : nat) (h : Le n m) => match h with
                                      | LeO x => x
                                      | x => 0
                                      end).


Type
  (fun (n m : nat) (h : Le n m) =>
   match h return nat with
   | LeS n m h => n
   | x => 0
   end).


Type
  (fun (n m : nat) (h : Le n m) => match h with
                                   | LeS n m h => n
                                   | x => 0
                                   end).


Type
  (fun (n m : nat) (h : Le n m) =>
   match h return (nat * nat) with
   | LeO n => (0, n)
   | LeS n m _ => (S n, S m)
   end).


Type
  (fun (n m : nat) (h : Le n m) =>
   match h with
   | LeO n => (0, n)
   | LeS n m _ => (S n, S m)
   end).

Module Type F_v1.
Fixpoint F (n m : nat) (h : Le n m) {struct h} : Le n (S m) :=
  match h in (Le n m) return (Le n (S m)) with
  | LeO m' => LeO (S m')
  | LeS n' m' h' => LeS n' (S m') (F n' m' h')
  end.
End F_v1.

Module Type F_v2.
Fixpoint F (n m : nat) (h : Le n m) {struct h} : Le n (S m) :=
  match h in (Le n m) return (Le n (S m)) with
  | LeS n m h => LeS n (S m) (F n m h)
  | LeO m => LeO (S m)
  end.
End F_v2.

(* Rend la longueur de la liste *)

Module Type L1.
Definition length (n : nat) (l : listn n) :=
  match l return nat with
  | consn n _ (consn m _ _) => S (S m)
  | consn n _ _ => 1
  | _ => 0
  end.
End L1.

Module Type L1'.
Definition length (n : nat) (l : listn n) :=
  match l with
  | consn n _ (consn m _ _) => S (S m)
  | consn n _ _ => 1
  | _ => 0
  end.
End L1'.

Module Type L2.
Definition length (n : nat) (l : listn n) :=
  match l return nat with
  | consn n _ (consn m _ _) => S (S m)
  | consn n _ _ => S n
  | _ => 0
  end.
End L2.

Module Type L2'.
Definition length (n : nat) (l : listn n) :=
  match l with
  | consn n _ (consn m _ _) => S (S m)
  | consn n _ _ => S n
  | _ => 0
  end.
End L2'.

Module Type L3.
Definition length (n : nat) (l : listn n) :=
  match l return nat with
  | consn n _ (consn m _ l) => S n
  | consn n _ _ => 1
  | _ => 0
  end.
End L3.

Module Type L3'.
Definition length (n : nat) (l : listn n) :=
  match l with
  | consn n _ (consn m _ l) => S n
  | consn n _ _ => 1
  | _ => 0
  end.
End L3'.

Type match LeO 0 return nat with
     | LeS n m h => n + m
     | x => 0
     end.
Type match LeO 0 with
     | LeS n m h => n + m
     | x => 0
     end.

Type
  (fun (n m : nat) (h : Le n m) =>
   match h return nat with
   | LeO x => x
   | LeS n m (LeO x) => x + m
   | LeS n m (LeS x y h) => n + (m + (x + y))
   end).


Type
  (fun (n m : nat) (h : Le n m) =>
   match h with
   | LeO x => x
   | LeS n m (LeO x) => x + m
   | LeS n m (LeS x y h) => n + (m + (x + y))
   end).

Type
  match LeO 0 return nat with
  | LeO x => x
  | LeS n m (LeO x) => x + m
  | LeS n m (LeS x y h) => n + (m + (x + y))
  end.

Type
  match LeO 0 with
  | LeO x => x
  | LeS n m (LeO x) => x + m
  | LeS n m (LeS x y h) => n + (m + (x + y))
  end.


Type
  match LE_n 0 return nat with
  | LE_n _ => 0
  | LE_S _ m (LE_n _) => 0 + m
  | LE_S _ m (LE_S _ y h) => 0 + m
  end.


Type
  match LE_n 0 with
  | LE_n _ => 0
  | LE_S _ m (LE_n _) => 0 + m
  | LE_S _ m (LE_S _ y h) => 0 + m
  end.


Type (fun (n m : nat) (h : Le n m) => match h with
                                      | x => x
                                      end).

Type
  (fun (n m : nat) (h : Le n m) =>
   match h return nat with
   | LeO n => n
   | x => 0
   end).
Type (fun (n m : nat) (h : Le n m) => match h with
                                      | LeO n => n
                                      | x => 0
                                      end).


Type
  (fun n : nat =>
   match niln return (nat -> nat) with
   | niln => fun _ : nat => 0
   | consn n a niln => fun _ : nat => 0
   | consn n a (consn m b l) => fun _ : nat => n + m
   end).


Type
  (fun n : nat =>
   match niln with
   | niln => fun _ : nat => 0
   | consn n a niln => fun _ : nat => 0
   | consn n a (consn m b l) => fun _ : nat => n + m
   end).

Type
  (fun (A : Set) (n : nat) (l : Listn A n) =>
   match l return (nat -> nat) with
   | Niln _ => fun _ : nat => 0
   | Consn _ n a (Niln _) => fun _ : nat => n
   | Consn _ n a (Consn _ m b l) => fun _ : nat => n + m
   end).

Type
  (fun (A : Set) (n : nat) (l : Listn A n) =>
   match l with
   | Niln _ => fun _ : nat => 0
   | Consn _ n a (Niln _) => fun _ : nat => n
   | Consn _ n a (Consn _ m b l) => fun _ : nat => n + m
   end).

(* Also tests for multiple _ patterns *)
Type
  (fun (A : Set) (n : nat) (l : Listn A n) =>
   match l in (Listn _ n) return (Listn A n) with
   | Niln _ as b => b
   | Consn _ _ _ _ as b => b
   end).

(** This one was said to raised once an "Horrible error message!" *)

Type
  (fun (A:Set) (n:nat) (l:Listn A n) =>
   match l with
   | Niln _ as b => b
   | Consn _ _ _ _  as b =>  b
   end).

Type
  match niln in (listn n) return (listn n) with
  | niln as b => b
  | consn _ _ _ as b => b
  end.


Type
  match niln in (listn n) return (listn n) with
  | niln as b => b
  | x => x
  end.

Type
  (fun (n m : nat) (h : LE n m) =>
   match h return (nat -> nat) with
   | LE_n _ => fun _ : nat => n
   | LE_S _ m (LE_n _) => fun _ : nat => n + m
   | LE_S _ m (LE_S _ y h) => fun _ : nat => m + y
   end).
Type
  (fun (n m : nat) (h : LE n m) =>
   match h with
   | LE_n _ => fun _ : nat => n
   | LE_S _ m (LE_n _) => fun _ : nat => n + m
   | LE_S _ m (LE_S _ y h) => fun _ : nat => m + y
   end).


Type
  (fun (n m : nat) (h : LE n m) =>
   match h return nat with
   | LE_n _ => n
   | LE_S _ m (LE_n _) => n + m
   | LE_S _ m (LE_S _ y (LE_n _)) => n + m + y
   | LE_S _ m (LE_S _ y (LE_S _ y' h)) => n + m + (y + y')
   end).



Type
  (fun (n m : nat) (h : LE n m) =>
   match h with
   | LE_n _ => n
   | LE_S _ m (LE_n _) => n + m
   | LE_S _ m (LE_S _ y (LE_n _)) => n + m + y
   | LE_S _ m (LE_S _ y (LE_S _ y' h)) => n + m + (y + y')
   end).


Type
  (fun (n m : nat) (h : LE n m) =>
   match h return nat with
   | LE_n _ => n
   | LE_S _ m (LE_n _) => n + m
   | LE_S _ m (LE_S _ y h) => n + m + y
   end).


Type
  (fun (n m : nat) (h : LE n m) =>
   match h with
   | LE_n _ => n
   | LE_S _ m (LE_n _) => n + m
   | LE_S _ m (LE_S _ y h) => n + m + y
   end).

Type
  (fun n m : nat =>
   match LeO 0 return nat with
   | LeS n m h => n + m
   | x => 0
   end).

Type (fun n m : nat => match LeO 0 with
                       | LeS n m h => n + m
                       | x => 0
                       end).

Parameter test : forall n : nat, {0 <= n} + {False}.
Type (fun n : nat => match test n return nat with
                     | left _ => 0
                     | _ => 0
                     end).


Type (fun n : nat => match test n return nat with
                     | left _ => 0
                     | _ => 0
                     end).

Type (fun n : nat => match test n with
                     | left _ => 0
                     | _ => 0
                     end).

Parameter compare : forall n m : nat, {n < m} + {n = m} + {n > m}.
Type
  match compare 0 0 return nat with

      (* k<i *) | inleft (left _) => 0
   (* k=i *) | inleft _ => 0
   (* k>i *) | inright _ => 0
  end.

Type
  match compare 0 0 with

      (* k<i *) | inleft (left _) => 0
   (* k=i *) | inleft _ => 0
   (* k>i *) | inright _ => 0
  end.



CoInductive SStream (A : Set) : (nat -> A -> Prop) -> Type :=
    scons :
      forall (P : nat -> A -> Prop) (a : A),
      P 0 a -> SStream A (fun n : nat => P (S n)) -> SStream A P.
Parameter B : Set.

Type
  (fun (P : nat -> B -> Prop) (x : SStream B P) =>
   match x return B with
   | scons _ _ a _ _ => a
   end).


Type
  (fun (P : nat -> B -> Prop) (x : SStream B P) =>
   match x with
   | scons _ _ a _ _ => a
   end).

Type match (0, 0) return (nat * nat) with
     | (x, y) => (S x, S y)
     end.
Type match (0, 0) return (nat * nat) with
     | (b, y) => (S b, S y)
     end.
Type match (0, 0) return (nat * nat) with
     | (x, y) => (S x, S y)
     end.

Type match (0, 0) with
     | (x, y) => (S x, S y)
     end.
Type match (0, 0) with
     | (b, y) => (S b, S y)
     end.
Type match (0, 0) with
     | (x, y) => (S x, S y)
     end.

Module Type test_concat.

Parameter concat : forall A : Set, List A -> List A -> List A.

Type
  match Nil nat, Nil nat return (List nat) with
  | Nil _ as b, x => concat nat b x
  | Cons _ _ _ as d, Nil _ as c => concat nat d c
  | _, _ => Nil nat
  end.
Type
  match Nil nat, Nil nat with
  | Nil _ as b, x => concat nat b x
  | Cons _ _ _ as d, Nil _ as c => concat nat d c
  | _, _ => Nil nat
  end.

End test_concat.

Inductive redexes : Set :=
  | VAR : nat -> redexes
  | Fun : redexes -> redexes
  | Ap : bool -> redexes -> redexes -> redexes.

Fixpoint regular (U : redexes) : Prop :=
  match U return Prop with
  | VAR n => True
  | Fun V => regular V
  | Ap true (Fun _ as V) W => regular V /\ regular W
  | Ap true _ W => False
  | Ap false V W => regular V /\ regular W
  end.


Type (fun n : nat => match n with
                     | O => 0
                     | S (S n as V) => V
                     | _ => 0
                     end).

Parameter
  concat :
    forall n : nat, listn n -> forall m : nat, listn m -> listn (n + m).
Type
  (fun (n : nat) (l : listn n) (m : nat) (l' : listn m) =>
   match l in (listn n), l' return (listn (n + m)) with
   | niln, x => x
   | consn n a l'', x => consn (n + m) a (concat n l'' m x)
   end).

Type
  (fun (x y z : nat) (H : x = y) (H0 : y = z) =>
   match H return (x = z) with
   | refl_equal =>
       match H0 in (_ = n) return (x = n) with
       | refl_equal => H
       end
   end).

Type (fun h : False => match h return False with
                       end).

Type (fun h : False => match h return True with
                       end).

Definition is_zero (n : nat) := match n with
                                | O => True
                                | _ => False
                                end.

Type
  (fun (n : nat) (h : 0 = S n) =>
   match h in (_ = n) return (is_zero n) with
   | refl_equal => I
   end).

Definition disc (n : nat) (h : 0 = S n) : False :=
  match h in (_ = n) return (is_zero n) with
  | refl_equal => I
  end.

Definition nlength3 (n : nat) (l : listn n) :=
  match l with
  | niln => 0
  | consn O _ _ => 1
  | consn (S n) _ _ => S (S n)
  end.

(* == Testing strategy elimintation predicate  synthesis == *)
Section titi.
Variable h : False.
Type match 0 with
     | O => 0
     | _ => except h
     end.
End titi.

Type match niln with
     | consn _ a niln => a
     | consn n _ x => 0
     | niln => 0
     end.



Inductive wsort : Set :=
  | ws : wsort
  | wt : wsort.
Inductive TS : wsort -> Set :=
  | id : TS ws
  | lift : TS ws -> TS ws.

Type
  (fun (b : wsort) (M N : TS b) =>
   match M, N with
   | lift M1, id => False
   | _, _ => True
   end).



(* ===================================================================== *)
(* To test pattern matching over a non-dependent inductive type, but     *)
(* having constructors with some arguments that depend on others         *)
(* I.e. to test manipulation of elimination predicate                    *)
(* ===================================================================== *)

Module Type test_term.

Parameter LTERM : nat -> Set.
Inductive TERM : Type :=
  | var : TERM
  | oper : forall op : nat, LTERM op -> TERM.

Parameter t1 t2 : TERM.

Type
  match t1, t2 with
  | var, var => True
  | oper op1 l1, oper op2 l2 => False
  | _, _ => False
  end.

End test_term.



Require Import Peano_dec.
Parameter n : nat.
Definition eq_prf := exists m : _, n = m.
Parameter p : eq_prf.

Type
  match p with
  | ex_intro _ c eqc =>
      match eq_nat_dec c n with
      | right _ => refl_equal n
      | left y => (* c=n*)  refl_equal n
      end
  end.


Parameter ordre_total : nat -> nat -> Prop.

Parameter N_cla : forall N : nat, {N = 0} + {N = 1} + {N >= 2}.

Parameter
  exist_U2 :
    forall N : nat,
    N >= 2 ->
    {n : nat |
    forall m : nat, 0 < m /\ m <= N /\ ordre_total n m /\ 0 < n /\ n < N}.

Type
  (fun N : nat =>
   match N_cla N with
   | inright H => match exist_U2 N H with
                  | exist _ a b => a
                  end
   | _ => 0
   end).



(* ============================================== *)
(*     To test compilation of dependent case      *)
(*  Nested patterns                               *)
(* ============================================== *)

(* == To test that terms named with AS are correctly absolutized before
      substitution in rhs   == *)

Type
  (fun n : nat =>
   match n return nat with
   | O => 0
   | S O => 0
   | S (S n1) as N => N
   end).

(* ========= *)

Type
  match niln in (listn n) return Prop with
  | niln => True
  | consn (S O) _ _ => False
  | _ => True
  end.

Type
  match niln in (listn n) return Prop with
  | niln => True
  | consn (S (S O)) _ _ => False
  | _ => True
  end.


Type
  match LeO 0 as h in (Le n m) return nat with
  | LeO _ => 0
  | LeS (S x) _ _ => x
  | _ => 1
  end.

Type
  match LeO 0 as h in (Le n m) return nat with
  | LeO _ => 0
  | LeS (S x) (S y) _ => x
  | _ => 1
  end.

Type
  match LeO 0 as h in (Le n m) return nat with
  | LeO _ => 0
  | LeS (S x as b) (S y) _ => b
  | _ => 1
  end.


Module Type ff.

Parameter ff : forall n m : nat, n <> m -> S n <> S m.
Parameter discr_r : forall n : nat, 0 <> S n.
Parameter discr_l : forall n : nat, S n <> 0.

Type
  (fun n : nat =>
   match n return (n = 0 \/ n <> 0) with
   | O => or_introl (0 <> 0) (refl_equal 0)
   | S x => or_intror (S x = 0) (discr_l x)
   end).

Module Type eqdec.

Fixpoint eqdec (n m : nat) {struct n} : n = m \/ n <> m :=
  match n, m return (n = m \/ n <> m) with
  | O, O => or_introl (0 <> 0) (refl_equal 0)
  | O, S x => or_intror (0 = S x) (discr_r x)
  | S x, O => or_intror _ (discr_l x)
  | S x, S y =>
      match eqdec x y return (S x = S y \/ S x <> S y) with
      | or_introl h => or_introl (S x <> S y) (f_equal S h)
      | or_intror h => or_intror (S x = S y) (ff x y h)
      end
  end.

End eqdec.

Module Type eqdec'.

Fixpoint eqdec (n : nat) : forall m : nat, n = m \/ n <> m :=
  match n return (forall m : nat, n = m \/ n <> m) with
  | O =>
      fun m : nat =>
      match m return (0 = m \/ 0 <> m) with
      | O => or_introl (0 <> 0) (refl_equal 0)
      | S x => or_intror (0 = S x) (discr_r x)
      end
  | S x =>
      fun m : nat =>
      match m return (S x = m \/ S x <> m) with
      | O => or_intror (S x = 0) (discr_l x)
      | S y =>
          match eqdec x y return (S x = S y \/ S x <> S y) with
          | or_introl h => or_introl (S x <> S y) (f_equal S h)
          | or_intror h => or_intror (S x = S y) (ff x y h)
          end
      end
  end.

End eqdec'.

Inductive empty : forall n : nat, listn n -> Prop :=
    intro_empty : empty 0 niln.

Parameter
  inv_empty : forall (n a : nat) (l : listn n), ~ empty (S n) (consn n a l).

Type
  (fun (n : nat) (l : listn n) =>
   match l in (listn n) return (empty n l \/ ~ empty n l) with
   | niln => or_introl (~ empty 0 niln) intro_empty
   | consn n a y as b => or_intror (empty (S n) b) (inv_empty n a y)
   end).

End ff.

Module Type ff'.

Parameter ff : forall n m : nat, n <> m -> S n <> S m.
Parameter discr_r : forall n : nat, 0 <> S n.
Parameter discr_l : forall n : nat, S n <> 0.

Type
  (fun n : nat =>
   match n return (n = 0 \/ n <> 0) with
   | O => or_introl (0 <> 0) (refl_equal 0)
   | S x => or_intror (S x = 0) (discr_l x)
   end).

Module Type eqdec.

Fixpoint eqdec (n m : nat) {struct n} : n = m \/ n <> m :=
  match n, m return (n = m \/ n <> m) with
  | O, O => or_introl (0 <> 0) (refl_equal 0)
  | O, S x => or_intror (0 = S x) (discr_r x)
  | S x, O => or_intror _ (discr_l x)
  | S x, S y =>
      match eqdec x y return (S x = S y \/ S x <> S y) with
      | or_introl h => or_introl (S x <> S y) (f_equal S h)
      | or_intror h => or_intror (S x = S y) (ff x y h)
      end
  end.

End eqdec.

Module Type eqdec'.

Fixpoint eqdec (n : nat) : forall m : nat, n = m \/ n <> m :=
  match n return (forall m : nat, n = m \/ n <> m) with
  | O =>
      fun m : nat =>
      match m return (0 = m \/ 0 <> m) with
      | O => or_introl (0 <> 0) (refl_equal 0)
      | S x => or_intror (0 = S x) (discr_r x)
      end
  | S x =>
      fun m : nat =>
      match m return (S x = m \/ S x <> m) with
      | O => or_intror (S x = 0) (discr_l x)
      | S y =>
          match eqdec x y return (S x = S y \/ S x <> S y) with
          | or_introl h => or_introl (S x <> S y) (f_equal S h)
          | or_intror h => or_intror (S x = S y) (ff x y h)
          end
      end
  end.

End eqdec'.
End ff'.

(* ================================================== *)
(* Pour tester parametres                             *)
(* ================================================== *)


Inductive Empty (A : Set) : List A -> Prop :=
    intro_Empty : Empty A (Nil A).

Parameter
  inv_Empty : forall (A : Set) (a : A) (x : List A), ~ Empty A (Cons A a x).


Type
  match Nil nat as l return (Empty nat l \/ ~ Empty nat l) with
  | Nil _ => or_introl (~ Empty nat (Nil nat)) (intro_Empty nat)
  | Cons _ a y => or_intror (Empty nat (Cons nat a y)) (inv_Empty nat a y)
  end.


(* ================================================== *)
(* Sur les listes                                     *)
(* ================================================== *)


Inductive empty : forall n : nat, listn n -> Prop :=
    intro_empty : empty 0 niln.

Parameter
  inv_empty : forall (n a : nat) (l : listn n), ~ empty (S n) (consn n a l).

Type
  (fun (n : nat) (l : listn n) =>
   match l in (listn n) return (empty n l \/ ~ empty n l) with
   | niln => or_introl (~ empty 0 niln) intro_empty
   | consn n a y as b => or_intror (empty (S n) b) (inv_empty n a y)
   end).

(* ===================================== *)
(*   Test parametros:                    *)
(* ===================================== *)

Inductive eqlong : List nat -> List nat -> Prop :=
  | eql_cons :
      forall (n m : nat) (x y : List nat),
      eqlong x y -> eqlong (Cons nat n x) (Cons nat m y)
  | eql_nil : eqlong (Nil nat) (Nil nat).


Parameter V1 : eqlong (Nil nat) (Nil nat) \/ ~ eqlong (Nil nat) (Nil nat).
Parameter
  V2 :
    forall (a : nat) (x : List nat),
    eqlong (Nil nat) (Cons nat a x) \/ ~ eqlong (Nil nat) (Cons nat a x).
Parameter
  V3 :
    forall (a : nat) (x : List nat),
    eqlong (Cons nat a x) (Nil nat) \/ ~ eqlong (Cons nat a x) (Nil nat).
Parameter
  V4 :
    forall (a : nat) (x : List nat) (b : nat) (y : List nat),
    eqlong (Cons nat a x) (Cons nat b y) \/
    ~ eqlong (Cons nat a x) (Cons nat b y).

Type
  match Nil nat as x, Nil nat as y return (eqlong x y \/ ~ eqlong x y) with
  | Nil _, Nil _ => V1
  | Nil _, Cons _ a x => V2 a x
  | Cons _ a x, Nil _ => V3 a x
  | Cons _ a x, Cons _ b y => V4 a x b y
  end.


Type
  (fun x y : List nat =>
   match x, y return (eqlong x y \/ ~ eqlong x y) with
   | Nil _, Nil _ => V1
   | Nil _, Cons _ a x => V2 a x
   | Cons _ a x, Nil _ => V3 a x
   | Cons _ a x, Cons _ b y => V4 a x b y
   end).


(* ===================================== *)

Inductive Eqlong :
forall n : nat, listn n -> forall m : nat, listn m -> Prop :=
  | Eql_cons :
      forall (n m : nat) (x : listn n) (y : listn m) (a b : nat),
      Eqlong n x m y -> Eqlong (S n) (consn n a x) (S m) (consn m b y)
  | Eql_niln : Eqlong 0 niln 0 niln.


Parameter W1 : Eqlong 0 niln 0 niln \/ ~ Eqlong 0 niln 0 niln.
Parameter
  W2 :
    forall (n a : nat) (x : listn n),
    Eqlong 0 niln (S n) (consn n a x) \/ ~ Eqlong 0 niln (S n) (consn n a x).
Parameter
  W3 :
    forall (n a : nat) (x : listn n),
    Eqlong (S n) (consn n a x) 0 niln \/ ~ Eqlong (S n) (consn n a x) 0 niln.
Parameter
  W4 :
    forall (n a : nat) (x : listn n) (m b : nat) (y : listn m),
    Eqlong (S n) (consn n a x) (S m) (consn m b y) \/
    ~ Eqlong (S n) (consn n a x) (S m) (consn m b y).

Type
  match
    niln as x in (listn n), niln as y in (listn m)
    return (Eqlong n x m y \/ ~ Eqlong n x m y)
  with
  | niln, niln => W1
  | niln, consn n a x => W2 n a x
  | consn n a x, niln => W3 n a x
  | consn n a x, consn m b y => W4 n a x m b y
  end.


Type
  (fun (n m : nat) (x : listn n) (y : listn m) =>
   match
     x in (listn n), y in (listn m)
     return (Eqlong n x m y \/ ~ Eqlong n x m y)
   with
   | niln, niln => W1
   | niln, consn n a x => W2 n a x
   | consn n a x, niln => W3 n a x
   | consn n a x, consn m b y => W4 n a x m b y
   end).


Parameter
  Inv_r :
    forall (n a : nat) (x : listn n), ~ Eqlong 0 niln (S n) (consn n a x).
Parameter
  Inv_l :
    forall (n a : nat) (x : listn n), ~ Eqlong (S n) (consn n a x) 0 niln.
Parameter
  Nff :
    forall (n a : nat) (x : listn n) (m b : nat) (y : listn m),
    ~ Eqlong n x m y -> ~ Eqlong (S n) (consn n a x) (S m) (consn m b y).



Fixpoint Eqlongdec (n : nat) (x : listn n) (m : nat)
 (y : listn m) {struct x} : Eqlong n x m y \/ ~ Eqlong n x m y :=
  match
    x in (listn n), y in (listn m)
    return (Eqlong n x m y \/ ~ Eqlong n x m y)
  with
  | niln, niln => or_introl (~ Eqlong 0 niln 0 niln) Eql_niln
  | niln, consn n a x as L => or_intror (Eqlong 0 niln (S n) L) (Inv_r n a x)
  | consn n a x as L, niln => or_intror (Eqlong (S n) L 0 niln) (Inv_l n a x)
  | consn n a x as L1, consn m b y as L2 =>
      match
        Eqlongdec n x m y
        return (Eqlong (S n) L1 (S m) L2 \/ ~ Eqlong (S n) L1 (S m) L2)
      with
      | or_introl h =>
          or_introl (~ Eqlong (S n) L1 (S m) L2) (Eql_cons n m x y a b h)
      | or_intror h =>
          or_intror (Eqlong (S n) L1 (S m) L2) (Nff n a x m b y h)
      end
  end.

(* ============================================== *)
(*     To test compilation of dependent case      *)
(*      Multiple Patterns                         *)
(* ============================================== *)
Inductive skel : Type :=
  | PROP : skel
  | PROD : skel -> skel -> skel.

Parameter Can : skel -> Type.
Parameter default_can : forall s : skel, Can s.

Type
  (fun s1 s2 s1 s2 : skel =>
   match s1, s2 return (Can s1) with
   | PROP, PROP => default_can PROP
   | PROD x y, PROP => default_can (PROD x y)
   | PROD x y, _ => default_can (PROD x y)
   | PROP, _ => default_can PROP
   end).

(* to test bindings in nested Cases *)
(* ================================ *)
Inductive Pair : Set :=
  | pnil : Pair
  | pcons : Pair -> Pair -> Pair.

Type
  (fun p q : Pair =>
   match p with
   | pcons _ x => match q with
                  | pcons _ (pcons _ x) => True
                  | _ => False
                  end
   | _ => False
   end).


Type
  (fun p q : Pair =>
   match p with
   | pcons _ x =>
       match q with
       | pcons _ (pcons _ x) =>
           match q with
           | pcons _ (pcons _ (pcons _ x)) => x
           | _ => pnil
           end
       | _ => pnil
       end
   | _ => pnil
   end).

Type
  (fun (n : nat) (l : listn (S n)) =>
   match l in (listn z) return (listn (pred z)) with
   | niln => niln
   | consn n _ l =>
       match l in (listn m) return (listn m) with
       | niln => niln
       | b => b
       end
   end).



(* Test de la syntaxe avec nombres *)
Require Import Arith.
Type (fun n => match n with
               | S (S O) => true
               | _ => false
               end).

Require Import ZArith.
Type (fun n => match n with
               | Z0 => true
               | _ => false
               end).

(* Check that types with unknown sort, as A below, are not fatal to
   the pattern-matching compilation *)

Definition transport {A} (P : A->Type) {x y : A} (p : x=y) (u : P x) : P y :=
  match p with eq_refl => u end.

(* Check in-pattern clauses with constant constructors, which were
   previously interpreted as variables (before 8.5) *)

Check match eq_refl 0 in _=O return O=O with eq_refl => eq_refl end.

Check match niln in listn O return O=O with niln => eq_refl end.

(* A test about nested "as" clauses *)
(* (was failing up to May 2017) *)

Check fun x => match x with (y,z) as t as w => (y+z,t) = (0,w) end.
