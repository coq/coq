Fail Notation "( x , y , .. , z )" := ltac:(let r := constr:(prod .. (prod x y) .. z) in r).
(* The command has indeed failed with message:
=> Error: Special token .. is for use in the Notation command. *)
