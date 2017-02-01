(* Revealed a missing re-consideration of postponed problems *)

Module A.
Inductive flat_type := Unit | Prod (A B : flat_type).
Inductive exprf (op : flat_type -> flat_type -> Type) {var : Type} : flat_type 
-> Type :=
| Op {t1 tR} (opc : op t1 tR) (args : exprf op t1) : exprf op tR.
Inductive op : flat_type -> flat_type -> Type := .
Arguments Op {_ _ _ _} _ _.
Definition bound_op {var}
           {src2 dst2}
           (opc2 : op src2 dst2)
  : forall (args2 : exprf op (var:=var) src2), Op opc2 args2 = Op opc2 args2
  := match opc2 return (forall args2, Op opc2 args2 = Op opc2 args2) with end.
End A.

(* A shorter variant *)
Module B.
Inductive exprf (op : unit -> Type) : Type :=
| A : exprf op
| Op tR (opc : op tR) (args : exprf op) : exprf op.
Inductive op : unit -> Type := .
Definition bound_op (dst2 : unit) (opc2 : op dst2)
  : forall (args2 : exprf op), Op op dst2 opc2 args2 = A op
  := match opc2 in op h return (forall args2 : exprf ?[U], Op ?[V] ?[I] opc2 args2 = A op) with end.
End B.
