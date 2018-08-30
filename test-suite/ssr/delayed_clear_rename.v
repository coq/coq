Require Import ssreflect.
Example foo (t t1 t2 : True) : True /\ True -> True -> True.
Proof.
move=>[{t1 t2 t} t1 t2] t.
Abort.
