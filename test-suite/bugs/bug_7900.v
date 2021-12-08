Require Import Coq.Program.Program.
(* Set Universe Polymorphism. *)
Set Printing Universes.

Axiom ALL : forall {T:Prop}, T.

Inductive Expr : Set := E (a : Expr).

Parameter Value : Set.

Fixpoint eval (e: Expr): Value :=
  match e with
  | E a => eval a
  end.

Class Quote (n: Value) : Set :=
  { quote: Expr
    ; eval_quote: eval quote = n }.

Program Definition quote_mult n
        `{!Quote n} : Quote n :=
  {| quote := E (quote (n:=n)) |}.

Set Printing Universes.
Next Obligation.
Proof.
  Show Universes.
  destruct Quote0 as [q eq].
  Show Universes.
  rewrite <- eq.
  clear n eq.
  Show Universes.
  apply ALL.
  Show Universes.
Qed.
Print quote_mult_obligation_1.
(* quote_mult_obligation_1@{} =
let Top_internal_eq_rew_dep :=
  fun (A : Type@{Coq.Init.Logic.8}) (x : A) (P : forall a : A, x = a -> Type@{Top.5} (* <- XXX *))
    (f : P x eq_refl) (y : A) (e : x = y) =>
  match e as e0 in (_ = y0) return (P y0 e0) with
  | eq_refl => f
  end in
fun (n : Value) (Quote0 : Quote n) =>
match Quote0 as q return (eval quote = n) with
| {| quote := q; eval_quote := eq0 |} =>
    Top_internal_eq_rew_dep Value (eval q) (fun (n0 : Value) (eq1 : eval q = n0) => eval quote = n0)
      ALL n eq0
end
     : forall (n : Value) (Quote0 : Quote n), eval (E quote) = n

quote_mult_obligation_1 is universe polymorphic
*)
