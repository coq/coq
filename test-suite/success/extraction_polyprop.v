(* Inserting coercions in the presence of sort polymorphism *)

Require Coq.extraction.Extraction.

Definition f {X} (p : (nat -> X) * True) : X * nat :=
  (fst p 0, 0).
Definition f_prop := f ((fun _ => I),I).
Extraction f_prop.

Definition h (x : nat * nat) := match x with (y,z) => (I,I) end.
Extraction h.

Module A.
Definition foo (P : Prop) (p : P) (f : P -> nat) := f p.
Definition bar A B (f : A -> nat) (p : A * B) := f (fst p).
Definition baz1 := foo (True * True) ((I, I) : True * True : Prop) (bar True True (fun _ => 0)).
Definition baz2 := foo (True * True) ((I, I) : True * True : Prop) (fun x => bar True True (fun _ => 0) x).
End A.
Recursive Extraction A.baz1.
Extraction TestCompile A.baz1.
Recursive Extraction A.baz2.
Extraction TestCompile A.baz2.

Module B.
Definition foo (P Q : Prop) (p : P) (f : P -> Q * nat) := f p.
Definition bar A B (f : A -> (True * True) * nat) (p : A * B) := f (fst p).
Definition baz1 := foo (True * True) (True * True) ((I, I) : True * True : Prop) (bar True True (fun x => ((x,x),0))).
Definition baz2 := foo (True * True) (True * True) ((I, I) : True * True : Prop) (fun x => bar True True (fun x => ((x,x),0)) x).
End B.
Recursive Extraction B.baz1.
Extraction TestCompile B.baz1.
Recursive Extraction B.baz2.
Extraction TestCompile B.baz2.

Module C.
Definition foo (P Q : Prop) (p : P) (f : P -> Q * nat) := f p.
Definition bar A B (f : A -> True *  nat) (p : A * B) := f (fst p).
Definition baz1 := foo (True * True) True ((I, I) : True * True : Prop) (bar True True (fun x => (x,0))).
Definition baz2 := foo (True * True) True ((I, I) : True * True : Prop) (fun x => bar True True (fun x => (x,0)) x).
End C.
Recursive Extraction C.baz1.
Extraction TestCompile C.baz1.
Recursive Extraction C.baz2.
Extraction TestCompile C.baz2.

Module E.
Definition foo (P : Prop) (p : P) (f : P -> nat) := f p.
Definition bar A B (p : A * B) := let x := fst p in 0.
Definition baz1 := foo (True * True) (I, I) (bar True True).
Definition baz2 := foo (True * True) (I, I) (fun x => bar True True x).
End E.
Recursive Extraction E.baz1.
Extraction TestCompile E.baz1.
Recursive Extraction E.baz2.
Extraction TestCompile E.baz2.

(** Example with a constructor already partially in Prop *)
Module F.
Definition foo (P : Prop) (p : P) (f : P -> nat) := f p.
Definition bar A B (f : A->nat) (p : {a:A | B}) := f (proj1_sig p).
Definition baz1 := foo {a:True | True} (exist _ I I) (bar True True (fun _ => 0)).
Definition baz2 := foo {a:True | True} (exist _ I I) (fun x => bar True True (fun _ => 0) x).
End F.
Recursive Extraction F.baz1.
Extraction TestCompile F.baz1.
Recursive Extraction F.baz2.
Extraction TestCompile F.baz2.

(** Examples with nested sort-polymorphic types *)
Module G.
Definition foo (P : Prop) (p : P) (f : P -> nat) := f p.
Definition bar A B C (f : B -> nat) (p : A * B * C) := f (snd (fst p)).
Definition baz1 := foo (True * True * True) ((I, I, I) : True * True * True : Prop) (bar True True True (fun _ => 0)).
Definition baz2 := foo (True * True * True) ((I, I, I) : True * True * True : Prop) (fun x => bar True True True (fun _ => 0) x).
End G.
Recursive Extraction G.baz1.
Extraction TestCompile G.baz1.
Recursive Extraction G.baz2.
Extraction TestCompile G.baz2.

(** Examples with universe subtyping *)
Module H.
Definition map (X Y:Type) (f : X -> Y) (g : Y -> bool) (x:X) := g (f x).
Definition use1 := map True True (fun x => x) (fun _ => true) I.
Definition use2 := map (True*True) True (fun x => fst x) (fun _ => true) (I,I).
End H.
Recursive Extraction H.use1.
Extraction TestCompile H.use1.
Recursive Extraction H.use2.
Extraction TestCompile H.use2.
