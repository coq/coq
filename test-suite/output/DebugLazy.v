Unset Lazy Time Profiling. (* not reproducible enough for testing *)

Module SimpleFib.

Fixpoint fib n :=
  match n with
  | 0 => 1
  | S k =>
      match k with
      | 0 => 1
      | S p => fib k + fib p
      end
  end.

Fixpoint div2 n :=
  match n with
  | 0 | 1 => 0
  | S (S k) => S (div2 k)
  end.

(* example from the haskell profiling doc:
   costs are mostly in [fib] (for us actually in addition because unary integers)
   but we can tell that it's more the fib in [f] than the one in [g] *)

Definition f n := fib n.
Definition g n := fib (div2 n).

Definition main n := (f n, g n).

Set Lazy Profiling.

Eval lazy in main 15.

Set Debug "lazy-trace".
Eval lazy in main 2.

End SimpleFib.

Require ListDef.

Module Bug1.
Import ListDef.

(* example from lexical profiling theory and practice *)

Definition f {A} (x:A) l := match l with nil => x::nil | y::tl => x::y::tl end.

Fixpoint append {A} (l:list A) l' := match l with nil => l' | x::tl => x :: append tl l' end.

Fixpoint rev {A} (l:list A) := match l with nil => nil | y::tl => append (rev tl) (y::nil) end.

Fixpoint fold_right {A B} (f:A->B->B) (l:list A) acc :=
  match l with
  | nil => acc
  | x::tl => f x (fold_right f tl acc)
  end.

Definition head l := match l with nil => 0 | x::l => x end.

Definition myhead l := head (fold_right f l nil).

Definition mylast l := head (rev (fold_right f l nil)).

Fixpoint eat n := match n with 0 => tt | S n => eat n end.

Set Lazy Profiling.

Eval lazy in
  match eat (myhead (seq 1 1000)) with
    tt => eat (mylast (seq 1001 10))
  end.
(* 1000 beta/iota steps in "f in myhead"
   with kernel term sharing on, because "f" in myhead is actually "@f nat"
   we need to update the context in zupdate
   otherwise the steps are assigned to myhead *)

End Bug1.
