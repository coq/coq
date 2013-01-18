Inductive List (A : Set) : Set :=
  | Nil : List A
  | Cons : A -> List A -> List A.

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

Parameter
  nff :
    forall (n m : nat) (x y : List nat),
    ~ eqlong x y -> ~ eqlong (Cons nat n x) (Cons nat m y).
Parameter
  inv_r : forall (n : nat) (x : List nat), ~ eqlong (Nil nat) (Cons nat n x).
Parameter
  inv_l : forall (n : nat) (x : List nat), ~ eqlong (Cons nat n x) (Nil nat).

Fixpoint eqlongdec (x y : List nat) {struct x} :
 eqlong x y \/ ~ eqlong x y :=
  match x, y return (eqlong x y \/ ~ eqlong x y) with
  | Nil _, Nil _ => or_introl (~ eqlong (Nil nat) (Nil nat)) eql_nil
  | Nil _, Cons _ a x as L => or_intror (eqlong (Nil nat) L) (inv_r a x)
  | Cons _ a x as L, Nil _ => or_intror (eqlong L (Nil nat)) (inv_l a x)
  | Cons _ a x as L1, Cons _ b y as L2 =>
      match eqlongdec x y return (eqlong L1 L2 \/ ~ eqlong L1 L2) with
      | or_introl h => or_introl (~ eqlong L1 L2) (eql_cons a b x y h)
      | or_intror h => or_intror (eqlong L1 L2) (nff a b x y h)
      end
  end.


Type
  match Nil nat as x, Nil nat as y return (eqlong x y \/ ~ eqlong x y) with
  | Nil _, Nil _ => or_introl (~ eqlong (Nil nat) (Nil nat)) eql_nil
  | Nil _, Cons _ a x as L => or_intror (eqlong (Nil nat) L) (inv_r a x)
  | Cons _ a x as L, Nil _ => or_intror (eqlong L (Nil nat)) (inv_l a x)
  | Cons _ a x as L1, Cons _ b y as L2 =>
      match eqlongdec x y return (eqlong L1 L2 \/ ~ eqlong L1 L2) with
      | or_introl h => or_introl (~ eqlong L1 L2) (eql_cons a b x y h)
      | or_intror h => or_intror (eqlong L1 L2) (nff a b x y h)
      end
  end.

