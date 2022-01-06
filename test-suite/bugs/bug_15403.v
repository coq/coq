Module Type EqType.
   Parameter Inline t : Type.
   Parameter eq : t -> t -> Prop.
End EqType.

Module NAT.
   Definition t := nat.
   Definition eq := @eq nat.
End NAT.

Module F (E:EqType) :=
  E.

Module Import NAT' := F NAT.

(* NAT'.eq should declared arguments in nat_scope *)
Notation "1" := true.
Check NAT'.eq 1 1.
