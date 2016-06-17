Universes i j.
Set Printing Universes.
Set Printing All.
Polymorphic Definition lt@{x y} : Type@{y} := Type@{x}.
Goal True.
evar (T:Type@{i}).
set (Z := nat : Type@{j}). simpl in Z.
let Tv:=eval cbv [T] in T in
pose (x:=Tv).
revert x.
refine (_ : let x:=Z in True).
(** This enforces i <= j *)
Fail pose (lt@{i j}).
let Zv:=eval cbv [Z] in Z in
let Tv:=eval cbv [T] in T in
constr_eq Zv Tv.
exact I. 
Defined.

Goal True.
evar (T:nat).
pose (Z:=0).
let Tv:=eval cbv [T] in T in
pose (x:=Tv).
revert x.
refine (_ : let x:=Z in True).
let Zv:=eval cbv [Z] in Z in
let Tv:=eval cbv [T] in T in
constr_eq Zv Tv.
Abort.

Goal True.
evar (T:Set).
pose (Z:=nat).
let Tv:=eval cbv [T] in T in
pose (x:=Tv).
revert x.
refine (_ : let x:=Z in True).
let Zv:=eval cbv [Z] in Z in
let Tv:=eval cbv [T] in T in
constr_eq Zv Tv.
Abort.

Goal forall (A:Type)(a:A), True.
intros A a.
evar (T:A).
pose (Z:=a).
let Tv:=eval cbv delta [T] in T in
pose (x:=Tv).
revert x.
refine (_ : let x:=Z in True).
let Zv:=eval cbv [Z] in Z in
let Tv:=eval cbv [T] in T in
constr_eq Zv Tv.
Abort.

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
