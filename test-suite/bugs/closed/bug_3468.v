(* Checking that unrelated terms requiring some scope do not affect
   the interpretation of tactic-in-term. The "Check" was failing with:
   The term "Set" has type "Type" while it is expected to have type
   "nat". *)

Notation bar2 a b := (let __ := ltac:(exact I) in (a + b)%type) (only parsing).
Check bar2 (Set + Set) Set.

(* Taking into account scopes in notations containing tactic-in-term *)

Declare Scope foo_scope.
Delimit Scope foo_scope with foo.
Notation "x ~~" := (x) (at level 0, only parsing) : foo_scope.
Notation bar x := (x%foo) (only parsing).
Notation baz x := ltac:(exact x%foo) (only parsing).
Check bar (O ~~).
Check baz (O ~~). (* Was failing *)

(* This was reported as bug #8706 *)

Declare Scope my_scope.
Notation "@ a" := a%nat (at level 100, only parsing) : my_scope.
Delimit Scope my_scope with my.

Notation "& b" := ltac:(exact (b)%my) (at level 100, only parsing): my_scope.
Definition test := (& (@4))%my.

(* Check inconsistent scopes *)
Fail Notation bar3 a := (let __ := ltac:(exact a%nat) in a%bool) (only parsing).
