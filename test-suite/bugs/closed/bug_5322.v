(* Regression in computing types of branches in "match" *)
Inductive flat_type := Unit | Prod (A B : flat_type).
Inductive exprf (op : flat_type -> flat_type -> Type) {var : Type} : flat_type
-> Type :=
| Op {t1 tR} (opc : op t1 tR) (args : exprf op t1) : exprf op tR.
Inductive op : flat_type -> flat_type -> Type := a : op Unit Unit.
Arguments Op {_ _ _ _} _ _.
Definition bound_op {var}
           {src2 dst2}
           (opc2 : op src2 dst2)
  : forall (args2 : exprf op (var:=var) src2), Op opc2 args2 = Op opc2 args2.
  refine match opc2 return (forall args2, Op opc2 args2 = Op opc2 args2) with
         | _ => _
         end.
