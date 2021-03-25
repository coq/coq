Record Atype : Type :=
  { t1 : forall (a : Type), a
  ; t2 : Type
  ; t3 : t2 }.
About t1.
About t3.

Record Btype : Type :=
  { u1 : forall (b : Type) (b0 : Type), b * b0
  ; u2 : Type
  ; u3 : u2 }.
About u1.
About u3.

Record Ctype : Type :=
  { v1 : forall (c0 : Type), c0
  ; v2 : Type
  ; v3 : v2
  }.
About v1.
About v3.
