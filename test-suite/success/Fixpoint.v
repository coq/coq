(* Playing with (co-)fixpoints with local definitions *)

Inductive listn : nat -> Set :=
  niln : listn 0
| consn : forall n:nat, nat -> listn n -> listn (S n).

Fixpoint f (n:nat) (m:=pred n) (l:listn m) (p:=S n) {struct l} : nat :=
   match n with O => p | _ =>
     match l with niln => p | consn q _ l => f (S q) l end
   end.

Eval compute in (f 2 (consn 0 0 niln)).

CoInductive Stream : nat -> Set :=
  Consn : forall n, nat -> Stream n -> Stream (S n).

CoFixpoint g (n:nat) (m:=pred n) (l:Stream m) (p:=S n) : Stream p :=
    match n return (let m:=pred n in forall l:Stream m, let p:=S n in Stream p)
    with
    | O => fun l:Stream 0 => Consn O 0 l
    | S n' =>
      fun l:Stream n' =>
      let l' :=
        match l in Stream q return Stream (pred q) with Consn _ _ l => l end
      in
      let a := match l with Consn _ a l => a end in
      Consn (S n') (S a) (g n' l')
   end l.

Eval compute in (fun l => match g 2 (Consn 0 6 l) with Consn _ a _ => a end).

(* Check inference of simple types in presence of non ambiguous
   dependencies (needs revision 10125) *)

Section folding.

Inductive vector (A:Type) : nat -> Type :=
  | Vnil : vector A 0
  | Vcons : forall (a:A) (n:nat), vector A n -> vector A (S n).

Variables (B C : Set) (g : B -> C -> C) (c : C).

Fixpoint foldrn n bs :=
  match bs with
  | Vnil => c
  | Vcons b _ tl => g b (foldrn _ tl)
  end.

End folding.

(* Check definition by tactics *)

Inductive even : nat -> Type :=
  | even_O : even 0
  | even_S : forall n, odd n -> even (S n)
with odd : nat -> Type :=
    odd_S : forall n, even n -> odd (S n).

Fixpoint even_div2 n (H:even n) : nat :=
  match H with
  | even_O => 0
  | even_S n H => S (odd_div2 n H)
  end
with odd_div2 n H : nat.
destruct H.
apply even_div2 with n.
assumption.
Qed.

Fixpoint even_div2' n (H:even n) : nat with odd_div2' n (H:odd n) : nat.
destruct H.
exact 0.
apply odd_div2' with n.
assumption.
destruct H.
apply even_div2' with n.
assumption.
Qed.

CoInductive Stream1 (A B:Type) := Cons1 : A -> Stream2 A B -> Stream1 A B
with Stream2 (A B:Type) := Cons2 : B -> Stream1 A B -> Stream2 A B.

CoFixpoint ex1 (n:nat) (b:bool) : Stream1 nat bool
with ex2 (n:nat) (b:bool) : Stream2 nat bool.
apply Cons1.
exact n.
apply (ex2 n b).
apply Cons2.
exact b.
apply (ex1 (S n) (negb b)).
Defined.
