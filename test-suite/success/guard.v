(* Specific tests about guard condition *)

(* f must unfold to x, not F (de Bruijn mix-up!) *)
Check let x (f:nat->nat) k := f k in
      fun (y z:nat->nat) =>
      let f:=x in (* f := Rel 3 *)
      fix F (n:nat) : nat :=
        match n with
        | 0 => 0
        | S k => f F k (* here Rel 3 = F ! *)
        end.

(** Commutation of guard condition allows recursive calls on functional arguments,
    despite rewriting in their domain types.  *)
Inductive foo : Type -> Type :=
| End A : foo A
| Next A : (A -> foo A) -> foo A.

Definition nat : Type := nat.

Fixpoint bar (A : Type) (e : nat = A) (f : foo A) {struct f} : nat :=
match f with
| End _ => fun _ => O
| Next A g => fun e =>
    match e in (_ = B) return (B -> foo A) -> nat with
    | eq_refl => fun (g' : nat -> foo A) => bar A e (g' O)
    end g
end e.
