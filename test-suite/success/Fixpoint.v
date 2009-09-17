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

