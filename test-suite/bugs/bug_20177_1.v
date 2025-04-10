Goal False.
let e := open_constr:(_) in
assert (True -> e).
exfalso.
Abort.
