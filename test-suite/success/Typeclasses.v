Generalizable All Variables.

Module mon.

Reserved Notation "'return' t" (at level 0).
Reserved Notation "x >>= y" (at level 65, left associativity).



Record Monad {m : Type -> Type} := {
  unit : Π {α}, α -> m α where "'return' t" := (unit t) ;
  bind : Π {α β}, m α -> (α -> m β) -> m β where "x >>= y" := (bind x y) ;
  bind_unit_left : Π {α β} (a : α) (f : α -> m β), return a >>= f = f a }.

Print Visibility.
Print unit.
Implicit Arguments unit [[m] [m0] [α]].
Implicit Arguments Monad [].
Notation "'return' t" := (unit t).

(* Test correct handling of existentials and defined fields. *)

Class A `(e: T) := { a := True }.
Class B `(e_: T) := { e := e_; sg_ass :> A e }.

Goal forall `{B T}, a.
  intros. exact I.
Defined.

Class B' `(e_: T) := { e' := e_; sg_ass' :> A e_ }.

Goal forall `{B' T}, a.
  intros. exact I.
Defined.

End mon.

(* Correct treatment of dependent goals *) 

(* First some preliminaries: *)

Section sec.
  Context {N: Type}.
  Class C (f: N->N) := {}.
  Class E := { e: N -> N }.
  Context
    (g: N -> N) `(E) `(C e)
    `(forall (f: N -> N), C f -> C (fun x => f x))
    (U: forall f: N -> N, C f -> False).

(* Now consider the following: *)

  Let foo := U (fun x => e x).
  Check foo _.

(* This type checks fine, so far so good. But now
 let's try to get rid of the intermediate constant foo.
 Surely we can just expand it inline, right? Wrong!: *)
 Check U (fun x => e x) _.
End sec.