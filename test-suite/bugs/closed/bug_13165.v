
(* Bug #13165 on implicit arguments in defined fields *)
Record T := {
 f {n:Nat} (p:n=n) := nat;
 g := f (eq_refl 0)
}.

(* Slight improvement in when SProp relevance is detected *)
Inductive True : SProp := I.
Inductive eqI : True -> SProp := reflI : eqI I.

Record U (c:True) := {
 u := c;
 v := reflI : eqI u;
 }.
