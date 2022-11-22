Local Set Universe Polymorphism.
Set Printing Universes.
Cumulative Inductive TM@{t} : Type@{t} -> Type :=
(* Monadic operations *)
| tmReturn {A:Type@{t}}
  : A -> TM A
| tmBind {A B : Type@{t}}
  : TM A -> (A -> TM B) -> TM B
.

Definition lift@{a u1 u2 | a <= u1, u1 <= u2} {A : Type@{a}} : TM@{u1} A -> TM@{u2} _ := fun x => x.

Definition tmFix_body'@{a b f1 f2 fx fr}
           {A : Type@{a}} {B : Type@{b}} (f : (A -> TM@{f1} B) -> (A -> TM@{f2} B))
           (tmFix : unit -> A -> TM@{fx} B)
  : A -> TM@{fr} B
  := f (fun a => tmBind@{fr} (tmReturn@{fr} tmFix) (fun tmFix =>       (tmFix tt a))).
