Record test := build { field : nat }.
Record test_r := build_r { field_r : nat }.
Record test_c := build_c { field_c : nat }.

Add Printing Constructor test_c.
Add Printing Record test_r.

Set Printing Records.

Check build 5.
Check {| field := 5 |}.

Check build_r 5.
Check build_c 5.

Unset Printing Records.

Check build 5.
Check {| field := 5 |}.
Check build_r 5.
Check build_c 5.

Set Printing Records.

Record N := C { T : Type; _ : True }.
Check fun x:N => let 'C _ p := x in p.
Check fun x:N => let 'C T _ := x in T.
Check fun x:N => let 'C T p := x in (T,p).

Record M := D { U : Type; a := 0; q : True }.
Check fun x:M => let 'D T _ p := x in p.
Check fun x:M => let 'D T _ p := x in T.
Check fun x:M => let 'D T p := x in (T,p).
Check fun x:M => let 'D T a p := x in (T,p,a).
Check fun x:M => let '{|U:=T;a:=a;q:=p|} := x in (T,p,a).

Module FormattingIssue13142.

Record T {A B} := {a:A;b:B}.

Module LongModuleName.
  Record test := { long_field_name0 : nat;
                  long_field_name1 : nat;
                  long_field_name2 : nat;
                  long_field_name3 : nat }.
End LongModuleName.

Definition c :=
      {| LongModuleName.long_field_name0 := 0;
         LongModuleName.long_field_name1 := 1;
         LongModuleName.long_field_name2 := 2;
         LongModuleName.long_field_name3 := 3 |}.

Definition d :=
 fun '{| LongModuleName.long_field_name0 := a;
         LongModuleName.long_field_name1 := b;
         LongModuleName.long_field_name2 := c;
         LongModuleName.long_field_name3 := d |} => (a,b,c,d).

Check {|a:=0;b:=0|}.
Check fun '{| LongModuleName.long_field_name0:=_ |} => 0.
Eval compute in {|a:=c;b:=d|}.
Import LongModuleName.
Eval compute in {|a:=c;b:=d|}.

End FormattingIssue13142.

Module ProjectionPrinting.

Notation "a +++ b" := (a * b) (at level 40, format "'[v' a '/' +++ '/' b ']'").

Record R := { field : nat -> nat }.
Set Printing Projections.
Check fun x => 0 +++ x.(field) 0.

End ProjectionPrinting.

Module RecordImplicitParameters.

(* Check that implicit parameters are treated independently of extra
   implicit arguments (at some time they did not and it was failing at
   typing time) *)

Record R A := { f : A -> A }.
Fail Check fun x => x.(f).

End RecordImplicitParameters.

Module WhyNotPrim.

  Set Primitive Projections.

  Record squashed : Prop := { x : nat }.

  Record noprojs := { y := 0 }.

  Record norelevantprojs (A:SProp) := { z : A }.

  Record anonproj := { _ : nat }.

End WhyNotPrim.
