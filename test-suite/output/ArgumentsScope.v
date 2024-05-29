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

Arguments f x%_A%_B.
About f.

Check f tt.
Set Printing All.
Check f tt.
Unset Printing All.

Arguments f x%_B%_A.
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

Module SectionTest1.

  Inductive A :=.
  Inductive B :=.
  Declare Scope X.
  Section S.
    Declare Scope Y.
    Bind Scope X with A.
    Bind Scope Y with B.
    Definition f : A -> B -> A := fun x _ => x.
    About f.
  End S.
  (* In section, Bind Scope do not survive the section nor have a persistent effect:
     outside the section, f does not know any more about X and Y, even thoug X exists outside the section *)
  About f.

End SectionTest1.

Module SectionTest2.

  Inductive A :=.
  Module M.
    Declare Scope X.
    Bind Scope X with A.
  End M.
  Module N.
    Import M.
    Section S.
      Axiom f : A -> A.
    End S.
  End N.
  (* In modules, Bind Scope has a persistent effect even if not imported:
     f knows about X even if M not imported *)
  About N.f.
  Axiom g : A -> A.
  (* Without the Import, Bind Scope has however no effect on declarations not
     already aware of this binding *)
  About g.

End SectionTest2.
