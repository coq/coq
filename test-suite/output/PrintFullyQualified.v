(* Test file for Printing Fully Qualified option *)

Module Foo.
  Axiom ax : False.
End Foo.

Module Bar.
  Axiom ax : False.
End Bar.

Definition use_foo := Foo.ax.
Definition use_bar := Bar.ax.

(* Test with nested modules *)
Module Outer.
  Module Inner.
    Definition def := 0.
  End Inner.
End Outer.

Definition use_nested := Outer.Inner.def.

(* Search with name-only output - default (shortest names) *)
Set Search Output Name Only.
Search "use_foo".
Search "use_bar".
Search "use_nested".

(* Search with name-only output - fully qualified *)
Set Printing Fully Qualified.
Search "use_foo".
Search "use_bar".
Search "use_nested".

Fail Check .ax.
Fail Check .Foo.ax.
Check .PrintFullyQualified.Foo.ax.

Unset Printing Fully Qualified.
