(* coq-prog-args: ("-top" "ArgumentsScope") *)
(* A few tests to check Global Argument Scope command *)

Section A.
Variable a : bool -> bool.
Definition negb' := negb.
Section B.
Variable b : bool -> bool.
Definition negb'' := negb.
About a.
About b.
About negb''.
About negb'.
About negb.
Global Arguments negb'' _ : clear scopes.
Global Arguments negb' _ : clear scopes.
Global Arguments negb _ : clear scopes.
Global Arguments a _ : clear scopes.
Global Arguments b _ : clear scopes.
About a.
About b.
About negb.
About negb'.
About negb''.
End B.
About a.
End A.
About negb.
About negb'.
About negb''.

(* Check multiple scopes *)

Declare Scope A_scope.
Delimit Scope A_scope with A.
Declare Scope B_scope.
Delimit Scope B_scope with B.
Notation "'tt'" := true : A_scope.
Notation "'tt'" := false : B_scope.

Definition f (x : bool) := x.

Arguments f x%A%B.
About f.

Check f tt.
Set Printing All.
Check f tt.
Unset Printing All.

Arguments f x%B%A.
About f.

Check f tt.
Set Printing All.
Check f tt.
Unset Printing All.

(* Check binding scope inside/outside *)

Bind Scope A_scope with bool.
#[add_bottom] Bind Scope B_scope with bool.

Definition g (x : bool) := x.

About g.

Bind Scope A_scope with nat.
#[add_top] Bind Scope B_scope with nat.

Definition g' (x : nat) := x.

About g'.

Bind Scope A_scope with unit.
Bind Scope B_scope with unit.  (* default: reset *)

Definition g'' (x : unit) := x.

About g''.
