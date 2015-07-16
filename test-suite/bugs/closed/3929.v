Goal True.
evar (T:Type).
pose (Z:=nat).
let Tv:=eval cbv [T] in T in
pose (x:=Tv).
revert x.
refine (_ : let x:=Z in True).
let Zv:=eval cbv [Z] in Z in
let Tv:=eval cbv [T] in T in
constr_eq Zv Tv.
Abort.

