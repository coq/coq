Class A := { n : nat }.

Record Rn := { rn : A }.

Class Cn := { cn : A }.

Record Rc := { rc :> A }.

Record Ri := { ri :: A }.

Class Ci := { ci :: A }.

Record Ric := { ric ::> A }.

Class Cic := { cic ::> A }.

Print Graph.

Print Instances A.
