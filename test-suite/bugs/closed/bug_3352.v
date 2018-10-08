Unset Strict Universe Declaration.

(*
I'm not sure what the general rule should be; intuitively, I want [IsHProp (* Set *) Foo] to mean [IsHProp (* U >= Set *) Foo].  (I think this worked in HoTT/coq, too.)  Morally, [IsHProp] has no universe level associated with it distinct from that of its argument, you should never get a universe inconsistency from unifying [IsHProp A] with [IsHProp A].  (The issue is tricker when IsHProp uses [A] elsewhere, as in:
*)

(* File reduced by coq-bug-finder from original input, then from 7725 lines to 78 lines, then from 51 lines to 13 lines *)
Set Universe Polymorphism.
Inductive Empty : Set := .
Record IsHProp (A : Type) := { foo : True }.
Definition hprop_Empty : IsHProp@{i} Empty := {| foo := I |}.
Goal let U := Type in let gt := Set : U in IsHProp (Empty : U).
simpl.
Set Printing Universes.
exact @hprop_Empty. (* Toplevel input, characters 21-32:
Error:
The term "hprop_Empty" has type "IsHProp (* Set *) Empty"
while it is expected to have type "IsHProp (* Top.17 *) Empty"
(Universe inconsistency: Cannot enforce Top.17 = Set because Set < Top.17)). *)
Defined.

Module B.
(* -*- coq-prog-args: ("-indices-matter") -*- *)
(* File reduced by coq-bug-finder from original input, then from 7725 lines to 78 lines, then from 51 lines to 13 lines *)
Set Universe Polymorphism.
Inductive paths {A} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Record Contr (A : Type) := { center : A }.
Monomorphic Record IsHProp (A : Type) := { foo : forall x y : A, Contr (x = y) }.
Definition hprop_Empty : IsHProp Empty := {| foo x y := match x : Empty with end |}.
Goal let U := Type in let gt := Set : U in IsHProp (Empty : U).
simpl.
Set Printing Universes.
exact hprop_Empty.
Defined.
End B.
