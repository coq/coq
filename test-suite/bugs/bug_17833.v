From Ltac2 Require Import Ltac2.
Notation "'silly' i1 .. i_ => x"
  := (let v := match (fun i1 => .. (fun i_ => x) ..) return _ with
               | y => y
               end in
      let _ := ltac2:(()) in
      v)
       (at level 10, i1 binder, i_ binder, only parsing).

Fail #[warnings="+ltac2-missing-notation-var"] Check silly a b c => (a, b, c).
(* Error: Missing notation term for variables i1 i_ x, probably an ill-typed expression *)

Check silly a b c => (a, b, c).
