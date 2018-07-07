Goal Set -> Prop.
intro x.
Fail let r := constr:(@ eq Set x x) in
clear x;
exact r.
Abort.

Goal False.
Proof.
Fail set (x := True);
let y := constr: (I : x) in
clear x; set (x := False);
exact y.
Abort.
