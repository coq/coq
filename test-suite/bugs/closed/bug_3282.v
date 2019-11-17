(* Check let-ins in fix and Fixpoint *)

Definition foo := fix f (m : nat) (o := true) (n : nat) {struct n} :=
  match n with 0 => 0 | S n' => f 0 n' end.

Fixpoint f (m : nat) (o := true) (n : nat) {struct n} :=
  match n with 0 => 0 | S n' => f 0 n' end.

Definition foo' := fix f {m : nat} (o := true) (n : nat) {struct n} :=
  match n with 0 => 0 | S n' => f (m:=0) n' end.
Check foo' (m:=0) 0.

Fixpoint f' {m : nat} (o := true) (n : nat) {struct n} :=
  match n with 0 => 0 | S n' => f' (m:=0) n' end.
Check f' (m:=0) 0.

CoInductive Stream := { hd : nat; tl : Stream }.

Definition cofoo := cofix f (o := true) {m} := {| hd := 0; tl := f (m:=0) |}.
Check cofoo (m:=0).

CoFixpoint cof (o := true) {m} := {| hd := 0; tl := cof (m:=0) |}.
Check cof (m:=0).

Definition cofoo' := cofix f {m} (o := true) := {| hd := 0; tl := f (m:=0) |}.
Check cofoo' (m:=0).

CoFixpoint cof' {m} (o := true) := {| hd := 0; tl := cof' (m:=0) |}.
Check cof' (m:=0).
