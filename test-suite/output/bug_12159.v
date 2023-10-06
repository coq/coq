Declare Scope A.
Declare Scope B.
Delimit Scope A with A.
Delimit Scope B with B.
Definition to_unit (v : Number.uint) : option unit
  := match Nat.of_num_uint v with O => Some tt | _ => None end.
Definition of_unit (v : unit) : Number.uint := Nat.to_num_uint 0.
Definition of_unit' (v : unit) : Number.uint := Nat.to_num_uint 1.
Number Notation unit to_unit of_unit : A.
Number Notation unit to_unit of_unit' : B.
Definition f x : unit := x.
Check f tt.
Arguments f x%_A.
Check f tt.
Check tt.
Open Scope A.
Check tt.
Close Scope A.
Check tt.
Open Scope B.
Check tt.
Undelimit Scope B.
Check tt.
Open Scope A.
Check tt.
Close Scope A.
Check tt.
Close Scope B.
Check tt.
Open Scope B.
Check tt.
Notation "1" := true.
Check tt.
Open Scope A.
Check tt.
Declare Scope C.
Notation "0" := false : C.
Open Scope C.
Check tt.  (* gives 0 but should now be 0%A *)
