
Set Universe Polymorphism.
Set Printing Relevance Marks.

Definition foo (A:Type) (a:A) := a.
Definition foo' (A:Prop) (a:A) := a.
Definition bar (A:SProp) (a:A) := a.
Definition baz@{s|u|} (A:Type@{s|u}) (a:A) := a.

Definition hide@{s|u|} {A:Type@{s|u}} := A.
Definition boz@{s s'|u|} (A:Type@{s|u}) (B:Type@{s'|u}) (a:@hide A) (b:@hide B) := a.

Print foo.
Print foo'.
Print bar.
Print baz.

(* arguments a and b are printed separately because they have different relevances
   even though the types are printed the same (difference hidden by implicit arguments) *)
Print boz.

Inductive sFalse : SProp := .

Goal True.
  Unset Printing Notations. (* arrow notation has no binder so relevance isn't printed *)
  pose (f:=fun A (a:A) => A).
  Show.
  let _ := constr:(f nat) in idtac.
  Show.
Abort.
Set Printing Notations.

(* TODO print relevance of letin *)
Check let x := 0 in x.

(* TODO print relevance of fixpoints (should be fix f (* Relevant *) ...) *)
Check fix f (n:nat) := 0.


(* TODO print case relevance *)
Check match 0 with 0 | _ => 0 end.

(* TODO print primitive projection relevance *)
Set Primitive Projections.
Record R := { p : nat }.
Check fun v => v.(p).
