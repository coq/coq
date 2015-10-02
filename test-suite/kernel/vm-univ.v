(* Basic tests *)
Polymorphic Definition pid {T : Type} (x : T) : T := x.
(*
Definition _1 : pid true = true :=
  @eq_refl _ true <: pid true = true.

Polymorphic Definition a_type := Type.

Definition _2 : a_type@{i} = Type@{i} :=
  @eq_refl _ Type@{i} <: a_type@{i} = Type@{i}.

Polymorphic Definition FORALL (T : Type) (P : T -> Prop) : Prop :=
  forall x : T, P x.

Polymorphic Axiom todo : forall {T:Type}, T -> T.

Polymorphic Definition todo' (T : Type) := @todo T.

Definition _3 : @todo'@{Set} = @todo@{Set} :=
  @eq_refl _ (@todo@{Set}) <: @todo'@{Set} = @todo@{Set}.
*)

(* Inductive Types *)
Inductive sumbool (A B : Prop) : Set :=
| left : A -> sumbool A B
| right : B -> sumbool A B.

Definition x : sumbool True False := left _ _ I.

Definition sumbool_copy {A B : Prop} (H : sumbool A B) : sumbool A B :=
  match H with
  | left _ _ x => left _ _ x
  | right _ _ x => right _ _ x
  end.

Definition _4 : sumbool_copy x = x :=
  @eq_refl _ x <: sumbool_copy x = x.

(* Polymorphic Inductive Types *)
Polymorphic Inductive poption (T : Type@{i}) : Type@{i} :=
| PSome : T -> poption@{i} T
| PNone : poption@{i} T.

Polymorphic Definition poption_default {T : Type@{i}} (p : poption@{i} T) (x : T) : T :=
  match p with
  | @PSome _ y => y
  | @PNone _ => x
  end.

Polymorphic Inductive plist (T : Type@{i}) : Type@{i} :=
| pnil
| pcons : T -> plist@{i} T -> plist@{i} T.

Arguments pnil {_}.
Arguments pcons {_} _ _.

Section pmap.
  Context {T : Type@{i}} {U : Type@{j}} (f : T -> U).

  Polymorphic Fixpoint pmap (ls : plist@{i} T) : plist@{j} U :=
    match ls with
    | @pnil _ => @pnil _
    | @pcons _ l ls => @pcons@{j} U (f l) (pmap@{i j} ls)
    end.
End pmap.

Universe Ubool.
Inductive tbool : Type@{Ubool} := ttrue | tfalse.


Eval vm_compute in pmap pid (pcons true (pcons false pnil)).
Eval vm_compute in pmap (fun x => match x with
                                  | pnil => true
                                  | pcons _ _ => false
                                  end) (pcons pnil (pcons (pcons false pnil) pnil)).
Eval vm_compute in pmap (fun x => x -> Type) (pcons tbool (pcons (plist tbool) pnil)).

Polymorphic Inductive Tree (T : Type@{i}) : Type@{i} :=
| Empty
| Branch : plist@{i} (Tree@{i} T) -> Tree@{i} T.

Section pfold.
  Context {T : Type@{i}} {U : Type@{u}} (f : T -> U -> U).

  Polymorphic Fixpoint pfold (acc : U) (ls : plist@{i} T) : U :=
    match ls with
    | pnil => acc
    | pcons a b => pfold (f a acc) b
    end.
End pfold.

Polymorphic Inductive nat : Type@{i} :=
| O
| S : nat -> nat.

Fixpoint nat_max (a b : nat) : nat :=
  match a , b with
  | O , b => b
  | a , O => a
  | S a , S b => S (nat_max a b)
  end.

Polymorphic Fixpoint height {T : Type@{i}} (t : Tree@{i} T) : nat :=
  match t with
  | Empty _ => O
  | Branch _ ls => S (pfold nat_max O (pmap height ls))
  end.

Polymorphic Fixpoint repeat {T : Type@{i}} (n : nat) (v : T) : plist@{i} T :=
  match n with
  | O => pnil
  | S n => pcons v (repeat n v)
  end.

Polymorphic Fixpoint big_tree (n : nat) : Tree@{i} nat :=
  match n with
  | O => @Empty nat
  | S n' => Branch _ (repeat n' (big_tree n'))
  end.

Eval compute in height (big_tree (S (S (S O)))).

Let big := S (S (S (S (S O)))).
Polymorphic Definition really_big := (S@{i} (S (S (S (S (S (S (S (S (S O)))))))))).

Time Definition _5 : height (@Empty nat) = O :=
  @eq_refl nat O <: height (@Empty nat) = O.

Time Definition _6 : height@{Set} (@Branch nat pnil) = S O :=
  @eq_refl nat@{Set} (S@{Set} O@{Set}) <: height@{Set} (@Branch nat pnil) = S O.

Time Definition _7 : height (big_tree big) = big :=
  @eq_refl nat big <: height (big_tree big) = big.

Time Definition _8 : height (big_tree really_big) = really_big :=
 @eq_refl nat@{Set} (S@{Set}
        (S@{Set}
           (S@{Set}
              (S@{Set}
                 (S@{Set}
                    (S@{Set} (S@{Set} (S@{Set} (S@{Set} (S@{Set} O@{Set}))))))))))
 <:
 @eq nat@{Set}
   (@height nat@{Set} (big_tree really_big@{Set}))
   really_big@{Set}.
