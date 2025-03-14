From Ltac2 Require Import Ltac2.
Notation "'silly' i1 .. i_ => x"
  := (let v := match (fun i1 => .. (fun i_ => x) ..) return _ with
               | y => y
               end in
      let _ := ltac2:(let _ := x in ()) in
      v)
       (at level 10, i1 binder, i_ binder, only parsing).

Fail Check silly a b c => (a, b, c).
