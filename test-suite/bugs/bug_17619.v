Goal True.
let t := open_constr:(_) in
let c := open_constr:(fun x (f:t x) => f x) in
let _ := type of c in
idtac.
Abort.

Axiom ST : SProp.
Axiom s : ST.

Goal ST.
let t := open_constr:(_) in
let c := open_constr:(fun x (f:t x) => f x) in
let c := eval simpl in c in
let c := constr:(c s (fun x => x)) in
exact c.
Qed.
