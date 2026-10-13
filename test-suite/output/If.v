Check if true then 1 else 0.  (* boolean if *)

Check if 4 then 1 else 0.  (* non boolean if, printed as if _ is *)

Check if 4 is S n then n else 0.
Check if 4 is S n then 1 else 0.
Check if 4 is O then 1 else 0.

Variant T := A | B | C.
Check match A with A => 0 | _ => 1 end.  (* printed as match, not if *)
Check if B is C then 1 else 0.  (* printed as if *)
Set Printing All.
Check if B is C then 1 else 0.  (* printed as match *)
Unset Printing All.
Check if B is C then 1 else 0.  (* printed as if *)
Set Printing Regular Matches.
Check if B is C then 1 else 0.  (* printed as match *)
Unset Printing Regular Matches.
Check if B is C then 1 else 0.  (* printed as if *)

Variant T2 := A1 | A2.
Check match A1 with A2 => 0 | _ => 1 end.  (* printed as match, not if *)
Check if A1 is A1 then 1 else 0.  (* printed as if *)
Check if A1 is A2 then 1 else 0.  (* printed as if *)

Inductive natr := Sr of natr | Or.

Check if Or is Sr _ then 1 else 0.
Check if Or is Or then 1 else 0.

Lemma test : sumbool True True -> True.
Proof.
  refine (fun x : sumbool True True => if x is left _ then _ else _);assumption.
Defined.
Print test.  (* printed as match (cannot use if) *)

(* There are historic uses of the if syntax with sumbool, so don't warn for now *)
Check if @left True False I then 1 else 0.
Check if @inleft nat False 3 then 1 else 0.

(* Coercions to bool are automatically introduced: *)
Coercion is_S n := if n is S _ then true else false.
Check if 4 then 1 else 0.
Set Printing Coercions.
Check if 4 then 1 else 0.
