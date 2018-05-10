(* About typing of with bindings *)

Record r : Type := mk_r { type : Type; cond : type -> Prop }.

Inductive p : Prop := consp : forall (e : r) (x : type e), cond e x -> p.

Goal p.
Fail apply consp with (fun _ : bool => mk_r unit (fun x => True)) nil.
Abort.
 
(* A simplification of an example from coquelicot, which was failing
   at some time after a fix #4782 was committed. *)

Record T := { dom : Type }.
Definition pairT A B := {| dom := (dom A * dom B)%type |}.
Class C (A:Type).
Parameter B:T.
Instance c (A:T) : C (dom A).
Instance cn : C (dom B).
Parameter F : forall A:T, C (dom A) -> forall x:dom A, x=x -> A = A.
Set Typeclasses Debug.
Goal forall (A:T) (x:dom A), pairT A A = pairT A A.
intros.
apply (F _ _)  with (x,x).
Abort.
  
