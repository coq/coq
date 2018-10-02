(* -*- coq-prog-args: ("-nois") -*- *)
Delimit Scope type_scope with type.
Delimit Scope function_scope with function.

Bind Scope type_scope with Sortclass.
Bind Scope function_scope with Funclass.

Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Notation "A -> B" := (forall (_ : A), B) : type_scope.

Definition compose {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Notation " g ∘ f " := (compose g f)
  (at level 40, left associativity) : function_scope.

Fail Check (fun x => x) ∘ (fun x => x). (* this [Check] should fail, as [function_scope] is not opened *)
Check compose ((fun x => x) ∘ (fun x => x)) (fun x => x). (* this check should succeed, as [function_scope] should be automatically bound in the arugments to [compose] *)
