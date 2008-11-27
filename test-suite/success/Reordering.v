(* Testing the reordering of hypothesis required by pattern, fold and change. *)
Goal forall (A:Set) (x:A) (A':=A), True.
intros.
fold A' in x. (* suceeds: x is moved after A' *)
Undo.
pattern A' in x.
Undo.
change A' in x.
Abort.

(* p and m should be moved before H *)
Goal forall n:nat, n=n -> forall m:nat, let p := (m,n) in True.
intros.
change n with (snd p) in H.
Abort.
