Module Type Intf1.
Parameter T : Type.
Inductive a := A.
End Intf1.

Module Impl1 <: Intf1.
Definition T := unit.
Inductive a := A.
End Impl1.

Module Type Intf2
  (Impl1 : Intf1).
Parameter x : Impl1.A=Impl1.A -> Impl1.T.
End Intf2.

Module Type Intf3
  (Impl1 : Intf1)
  (Impl2 : Intf2(Impl1)).
End Intf3.

Fail Module Toto
  (Impl1' : Intf1)
  (Impl2 : Intf2(Impl1'))
  (Impl3 : Intf3(Impl1)(Impl2)).
(* A UserError is expected here, not an uncaught Not_found *)

(* NB : the Inductive above and the A=A weren't in the initial test,
   they are here only to force an access to the environment
   (cf [Printer.qualid_of_global]) and check that this env is ok. *)
