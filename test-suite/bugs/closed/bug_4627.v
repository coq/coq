Class sa (A:Type) := { }.

Record predicate A (sa:sa A) :=
  { pred_fun: A->Prop }.
Record ABC : Type :=
  { abc: Type }.
Record T :=
  { T_abc: ABC }.


(*
sa: forall _ : Type@{Top.179}, Prop
predicate: forall (A : Type@{Top.205}) (_ : sa A), Type@{max(Set+1, Top.205)}
T: Type@{Top.208+1}
ABC: Type@{Top.208+1}
abc: forall _ : ABC, Type@{Top.208}

Top.205 <= Top.179   predicate <= sa.A
Set < Top.208        Set < abc
Set < Top.205        Set < predicate
*)

Definition foo : predicate T (Build_sa T) :=
    {| pred_fun:= fun w => True |}.
(* *)
(* Top.208 < Top.205   <--- added by foo *)
(* *)

Check predicate nat (Build_sa nat).
(*

The issue is that the template polymorphic universe of [predicate], Top.205, does not get replaced with the universe of [nat] in the above line.
  -Jason Gross

8.5          -- predicate nat (Build_sa nat): Type@{max(Set+1, Top.205)}
8.5 EXPECTED -- predicate nat (Build_sa nat): Type@{Set+1}
8.4pl4       -- predicate nat {| |}: Type (* max(Set, (Set)+1) *)
*)

(* This works in 8.4pl4 and SHOULD work in 8.5 *)
Definition bar : ABC :=
  {| abc:= predicate nat (Build_sa nat) |}.
(*
The term "predicate nat (Build_sa nat)" has type
 "Type@{max(Set+1, Top.205)}"
while it is expected to have type "Type@{Top.208}"
(universe inconsistency: Cannot enforce Top.205 <=
Top.208 because Top.208 < Top.205).
*)
