

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).
  (* type this in emacs in agda-input method with \lambda *)

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.
(* written \to or \r- in Agda input method *)
(* the level comes from sub/coq/theories/Unicode/Utf8_core.v *)


Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Definition UU := Type.

Identity Coercion fromUUtoType : UU >-> Sortclass.

Record total2 { T: UU } ( P: T -> UU ) := tpair { pr1 : T; pr2 : P pr1 }.

Arguments tpair {_} _ _ _.
Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

Notation "'∑'  x .. y , P" := (total2 (λ x, .. (total2 (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.
  (* type this in emacs in agda-input method with \sum *)

Section Test.
  Variables (A : UU) (P: (A → UU) → UU).

  Fail Check ∑ (F : A → UU), P(F).
End Test.
