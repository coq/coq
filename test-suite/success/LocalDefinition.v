(* Test consistent behavior of Local Definition (#8722) *)

(* Test consistent behavior of Local Definition wrt Admitted *)

Module TestAdmittedVisibility.
  Module A.
    Let a1 : nat. Admitted. (* Suppose to behave like a "Local Definition" *)
    Local Definition b1 : nat. Admitted. (* Told to be a "Local Definition" *)
    Local Definition c1 := 0.
    Local Parameter d1 : nat.
    Section S.
      Let a2 : nat. Admitted. (* Told to be turned into a toplevel assumption *)
      Local Definition b2 : nat. Admitted. (* Told to be a "Local Definition" *)
      Local Definition c2 := 0.
      Local Parameter d2 : nat.
    End S.
  End A.
  Import A.
  Fail Check a1. (* used to be accepted *)
  Fail Check b1. (* used to be accepted *)
  Fail Check c1.
  Fail Check d1.
  Fail Check a2. (* used to be accepted *)
  Fail Check b2. (* used to be accepted *)
  Fail Check c2.
  Fail Check d2.
End TestAdmittedVisibility.

(* Test consistent behavior of Local Definition wrt automatic declaration of instances *)

Module TestVariableAsInstances.
  Module Test1.
    Set Typeclasses Axioms Are Instances.
    Class U.
    Local Parameter b : U.
    Definition testU := _ : U. (* _ resolved *)

    Class T.
    Variable a : T.  (* warned to be the same as "Local Parameter" *)
    Definition testT := _ : T. (* _ resolved *)
  End Test1.

  Module Test2.
    Unset Typeclasses Axioms Are Instances.
    Class U.
    Local Parameter b : U.
    Fail Definition testU := _ : U. (* _ unresolved *)

    Class T.
    Variable a : T.  (* warned to be the same as "Local Parameter" thus should not be an instance *)
    Fail Definition testT := _ : T. (* used to succeed *)
  End Test2.
End TestVariableAsInstances.
