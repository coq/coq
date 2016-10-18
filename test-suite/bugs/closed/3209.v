(* Avoiding some occur-check *)

(* 1. Original example *)

Inductive eqT {A} (x : A) : A -> Type :=
  reflT : eqT x x.
Definition Bi_inv (A B : Type) (f : (A -> B)) :=
  sigT (fun (g : B -> A) =>
          sigT (fun (h : B -> A) =>
                  sigT (fun (α : forall b : B, eqT (f (g b)) b) =>
                          forall a : A, eqT (h (f a)) a))).
Definition TEquiv (A B : Type) := sigT (fun (f : A -> B) => Bi_inv _ _ f).

Axiom UA : forall (A B : Type), TEquiv (TEquiv A B) (eqT A B).
Definition idtoeqv {A B} (e : eqT A B) : TEquiv A B :=
  sigT_rect (fun _ => TEquiv A B)
            (fun (f : TEquiv A B -> eqT A B) H =>
               sigT_rect _ (* (fun _ => TEquiv A B) *)
                         (fun g _ => g e)
                         H)
            (UA A B).

(* 2. Alternative example by Guillaume *)

Inductive foo (A : Prop) : Prop := Foo : foo A.
Axiom bar : forall (A : Prop) (P : foo A -> Prop), (A -> P (Foo A)) -> Prop.

(* This used to fail with a Not_found, we fail more graciously but a
   heuristic could be implemented, e.g. in some smart occur-check
   function, to find a solution of then form ?P := fun _ => ?P' *)

Fail Check (fun e : ?[T] => bar ?[A] ?[P] (fun g : ?[A'] => g e)).

(* This works and tells which solution we could have inferred *)

Check (fun e : ?[T] => bar ?[A] (fun _ => ?[P]) (fun g : ?[A'] => g e)).

(* For the record, here is the trace in the failing example:

In (fun e : ?T => bar ?[A] ?[P] (fun g : ?A' => g e)), we have the existential variables

e:?T |- ?A : Prop
e:?T |- ?P : foo ?A -> Prop
e:?T |- ?A' : Type

with constraints

?A' == ?A
?A' == ?T -> ?P (Foo ?A)

To type (g e), unification first defines

?A := forall x:?B, ?P'{e:=e,x:=x}
with ?T <= ?B
and ?P'@{e:=e,x:=e} <= ?P@{e:=e} (Foo (forall x:?B, ?P'{e:=e,x:=x}))

Then, since ?P'@{e:=e,x:=e} may use "e" in two different ways, it is
not a pattern and we define a new

e:?T x:?B|- ?P'' : foo (?B' -> ?P''') -> Prop

for some ?B' and ?P''', together with

?P'@{e,x} := ?P''{e:=e,x:=e} (Foo (?B -> ?P')
?P@{e} := ?P''{e:=e,x:=e}

Moreover, ?B' and ?P''' have to satisfy

?B'@{e:=e,x:=e} == ?B@{e:=e}
?P'''@{e:=e,x:=e} == ?P'@{e:=e,x:=x}

and this leads to define ?P' which was the initial existential
variable to define.
*)

