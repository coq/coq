Notation pr1 := (@projT1 _ _).
Notation compose := (fun g' f' x => g' (f' x)).
Notation "g 'o' f" := (compose g f) (at level 40, left associativity) :
function_scope.
Open Scope function_scope.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y := match p
with eq_refl => eq_refl end.
Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x) := forall x:A,
f x = g x.
Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) :
type_scope.
Theorem Univalence_implies_FunextNondep (A B : Type)
: forall f g : A -> B, f == g -> f = g.
Proof.
  intros f g p.
  pose (d := fun x : A => existT (fun xy => fst xy = snd xy) (f x, f x)
(eq_refl (f x))).
  pose (e := fun x : A => existT (fun xy => fst xy = snd xy) (f x, g x) (p x)).
  change f with ((snd o pr1) o d).
  change g with ((snd o pr1) o e).
  apply (ap (fun g => snd o pr1 o g)).
(* Used to raise a not Found due to a "typo" in solve_evar_evar *)
