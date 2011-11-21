(*********************************************)
(* This has been a bug reported by Y. Bertot *)
Inductive expr : Set :=
  | b : expr -> expr -> expr
  | u : expr -> expr
  | a : expr
  | var : nat -> expr.

Fixpoint f (t : expr) : expr :=
  match t with
  | b t1 t2 => b (f t1) (f t2)
  | a => a
  | x => b t a
  end.

Fixpoint f2 (t : expr) : expr :=
  match t with
  | b t1 t2 => b (f2 t1) (f2 t2)
  | a => a
  | x => b x a
  end.

(*********************************************)
(* Test expansion of aliases                 *)
(* Originally taken from NMake_gen.v         *)

 Local Notation SizePlus n := (S (S (S (S (S (S n)))))).
 Local Notation Size := (SizePlus O).

 Parameter zn2z : Type -> Type.
 Parameter w0 : Type.
 Fixpoint word (w : Type) (n : nat) {struct n} : Type :=
  match n with
  | 0 => w
  | S n0 => zn2z (word w n0)
  end.

 Definition w1 := zn2z w0.
 Definition w2 := zn2z w1.
 Definition w3 := zn2z w2.
 Definition w4 := zn2z w3.
 Definition w5 := zn2z w4.
 Definition w6 := zn2z w5.

 Definition dom_t n := match n with
  | 0 => w0
  | 1 => w1
  | 2 => w2
  | 3 => w3
  | 4 => w4
  | 5 => w5
  | 6 => w6
  | SizePlus n => word w6 n
 end.
Parameter plus_t : forall n m : nat, word (dom_t n) m -> dom_t (m + n).

(* This used to fail because of a bug in expansion of SizePlus wrongly
   reusing n as an alias for the subpattern *)
Definition plus_t1 n : forall m, word (dom_t n) m -> dom_t (m+n) :=
   match n return (forall m, word (dom_t n) m -> dom_t (m+n)) with
     | SizePlus (S n') as n => plus_t n
     | _ as n =>
         fun m => match m return (word (dom_t n) m -> dom_t (m+n)) with
                    | SizePlus (S (S m')) as m => plus_t n m
                    | _ => fun x => x
                  end
   end.

(* Test (useless) intermediate alias *)
Definition plus_t2 n : forall m, word (dom_t n) m -> dom_t (m+n) :=
   match n return (forall m, word (dom_t n) m -> dom_t (m+n)) with
     | S (S (S (S (S (S (S n'))))) as n) as n'' => plus_t n''
     | _ as n =>
         fun m => match m return (word (dom_t n) m -> dom_t (m+n)) with
                    | SizePlus (S (S m')) as m => plus_t n m
                    | _ => fun x => x
                  end
   end.

(*****************************************************************************)
(* Check that alias expansion behaves consistently from versions to versions *)

Definition g m :=
  match pred m with
  | 0 => 0
  | n => n (* For compatibility, right-hand side should be (S n), not (pred m) *)
  end.

Goal forall m, g m = match pred m with 0 => 0 | S n => S n end.
intro; reflexivity.
Abort.
