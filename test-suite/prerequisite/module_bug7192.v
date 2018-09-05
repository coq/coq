(* Variant of #7192 to be tested in a file requiring this file *)
(* #7192 is about Print Assumptions not entering implementation of submodules *)

Definition a := True.
Module Type B. Axiom f : Prop. End B.
Module Type C. Declare Module D : B. End C.
Module M7192: C.
  Module D <: B. Definition f := a. End D.
End M7192.
