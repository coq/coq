(* Treat "match" on a "cofix" like "match" on a constructor in guard condition *)

Module CofixRedex.

CoInductive Stream := {hd : nat; tl : Stream}.
Definition zeros := cofix zeros := {|hd := 0; tl := zeros|}.

Fixpoint f n :=
  match n with
  | 0 => 0
  | S n =>
    match zeros with
    | {|hd:=_|} => fun f => f n
    end f
  end.

End CofixRedex.

Module CofixRedexPrimProj.

Set Primitive Projections.
CoInductive Stream A := {hd : A; tl : Stream A}.
Arguments hd {A} s.

Fixpoint f n :=
  match n with
  | 0 => 0
  | S n => (cofix cst := {|hd := (fun f => f n); tl := cst|}).(hd) f
  end.

End CofixRedexPrimProj.

(* Stack was missing when unfolding primitive projection in guard condition *)

Module ProjectionStack.

Set Primitive Projections.

Record T := { a : nat -> nat }.

Check fix f (b:bool) n : nat :=
  match n with
  | 0 => 0
  | S n => (if b then {| a := f b |}.(a) else f b) n
  end.

End ProjectionStack.
