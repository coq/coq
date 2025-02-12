
Notation "g 'o' f" := ((fun g0 f0 x => g0 (f0 x)) g f) (at level 40, left associativity) : function_scope.

Polymorphic Definition eq_sym {A} {x y : A} (p:x = y) : y = x := match p with eq_refl => eq_refl end.

Polymorphic Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y
  := match p with eq_refl => u end.

Polymorphic Definition transport_arrow'@{a b | } {A : Type@{a}} {B:A->Type@{b}} {C : A -> Type@{b}}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C x1)
  : transport (fun x => B x -> C x) p f = transport _ p o f o transport _ (eq_sym p).
Proof.
  destruct p; auto.
Defined.
(* Universe constraints are not implied by the ones declared: b <= eq.u0 *)
