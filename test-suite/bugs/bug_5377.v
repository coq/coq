Goal ((forall (t : Type) (x y : t),
          True ->
          x = y)) -> False.
Proof.
  intro HG.
  let P := lazymatch goal with
  | [ H : forall t x y, True -> @?P t x y
                        |- _ ]
    => P
  end in
  pose (f := P).
  unify f (fun (t : Type) (x y : t) => x = y).
Abort.

Goal True.
Proof.
let c := lazymatch constr:(fun (T : nat -> Type) (y : nat) (_ : T y) => y) with
         | fun _ y _ => @?C y => C
         end in
pose (f := c).
unify f (fun n : nat => n).
Abort.

Goal (forall x : nat, x = x -> x = x \/ x = x) -> True.
Proof.
intro.
let P := lazymatch goal with
| [ H : forall y, @?P y -> @?P y \/ _ |- _ ]
  => P
end in
pose (f := P).
unify f (fun x : nat => x = x).
Abort.

Goal (forall x : nat, x = x -> x = x \/ x = x) -> True.
Proof.
intro.
lazymatch goal with
| [ H : forall y, @?P y -> @?Q y \/ _ |- _ ]
  => idtac
end.
Abort.

Axiom eq : forall {T} (_ : T), Prop.

Goal forall _ : (forall t (_ : eq t) (x : t), eq x), Prop.
Proof.
intro.
let P := lazymatch goal with
| [ H : forall t _ x, @?P t x |- _ ]
  => P
end in
pose (f := P).
Abort.
