(* Checking a Show Proof bug *)
Section S.
Variable A:Prop.
Theorem thm (a:A) : True.
assert (b:=a).
clear A a b.
Show Proof.
Abort.
End S.
