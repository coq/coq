(* File reduced by coq-bug-finder from original input, then from 2809 lines to 39 lines *)
Set Primitive Projections.
Set Implicit Arguments. 
Module Export foo.
  Record prod (A B : Type) := pair { fst : A ; snd : B }.
End foo.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Arguments idpath {A a} , [A] a.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y := match p with idpath => idpath end.
Axiom path_prod : forall {A B : Type} (z z' : prod A B), (fst z = fst z') -> (snd z = snd z') -> (z = z').
Notation fst := (@fst _ _).
Notation snd := (@snd _ _).
Definition ap_fst_path_prod {A B : Type} {z z' : prod A B} (p : @paths A (fst z) (fst z')) (q : snd z = snd z')
: ap fst (path_prod z z' p q) = p.
Abort.

Notation fstp x := (x.(foo.fst)).
Notation fstap x := (foo.fst x).

Definition ap_fst_path_prod' {A B : Type} {z z' : prod A B} (p : @paths A (fst z) (fst z')) (q : snd z = snd z')
: ap (fun x => fstap x) (path_prod z z' p q) = p.

Abort.

(* Toplevel input, characters 137-138:
Error:
In environment
A : Type
B : Type
z : prod A B
z' : prod A B
p : @paths A (foo.fst ?11 ?14 z) (foo.fst ?26 ?29 z')
q : @paths ?54 (foo.snd ?42 ?45 z) (foo.snd ?57 ?60 z')
The term "p" has type "@paths A (foo.fst ?11 ?14 z) (foo.fst ?26 ?29 z')"
while it is expected to have type "@paths A (foo.fst z) (foo.fst z')". *)
