Set Implicit Arguments.

(* Suggested by Pierre Casteran (bug #169) *)
(* Argument 3 is needed to typecheck and should be printed *)
Definition compose := [A,B,C:Set; f : A-> B ; g : B->C ; x : A] (g (f x)).
Check (compose 3!nat S).

(* Better to explicitly display the arguments inferable from a
   position that could disappear after reduction *)
Inductive ex [A:Set;P:A->Prop] : Prop
    := ex_intro : (x:A)(P x)->(ex P).
Check (ex_intro 2![_]True 3!O I).

