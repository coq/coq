Class C := {}.

Global Declare Instance I0 : C.
Local Declare Instance I1 : C.
Global Polymorphic Declare Instance I3 : C.
Polymorphic Global Declare Instance I4 : C.
Local Polymorphic Declare Instance I5 : C.
Polymorphic Local Declare Instance I6 : C.

Global Program Instance I7 : C := {}.
Local Program Instance I8 : C := {}.
Program Global Instance I9 : C := {}.
Program Local Instance I10 : C := {}.

Polymorphic Program Global Instance I11 : C := {}.
Polymorphic Program Local Instance I12 : C := {}.
Program Global Polymorphic Instance I13 : C := {}.
Program Local Polymorphic Instance I14 : C := {}.
Global Program Polymorphic Instance I15 : C := {}.
Local Program Polymorphic Instance I16 : C := {}.

Global Notation x0 := 0.
Local Notation x1 := 0.

Global Definition x2 := 0.
Local Definition x3 := 0.
Polymorphic Definition x4 := 0.
Polymorphic Global Definition x5 := 0.
Polymorphic Local Definition x6 := 0.
Global Polymorphic Definition x7 := 0.
Local Polymorphic Definition x8 := 0.

Polymorphic Inductive y0 := z0.
Polymorphic Variant y1 := z1.

Local Obligation Tactic := auto.
Global Obligation Tactic := auto.

Global Typeclasses Opaque I7.
Local Typeclasses Opaque I8.

Global Hint Extern 10 (_ <= _) => auto : arith.
Local Hint Extern 10 (_ <= _) => auto : arith.

Global Ltac lt0 := auto.
Local Ltac lt1 := auto.

Require Corelib.Program.Tactics.

Global Program Definition x9 := 0.
Local Program Definition x10 := 0.
Program Global Definition x11 := 0.
Program Local Definition x12 := 0.

Polymorphic Program Global Definition x13 := 0.
Polymorphic Program Local Definition x14 := 0.
Program Global Polymorphic Definition x15 := 0.
Program Local Polymorphic Definition x16 := 0.
Global Program Polymorphic Definition x17 := 0.
Local Program Polymorphic Definition x18 := 0.
