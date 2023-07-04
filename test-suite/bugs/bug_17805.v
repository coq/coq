Inductive baz :=
  K : (let foo2 := Type@{_} in
  let foo3 := Type@{_} in
  let set_le_foo3 := (fun y : Set => (fun x : foo3 => x) y) in
  let foo3_le_foo2 := (fun y : foo3 => (fun x : foo2 => x) y) in
  let set_eq_foo2 := (fun y : foo2 => (fun x : Set => x) y) in
  nat) -> baz.


(* a bit more transitive constraints *)
Inductive baz' :=
  K' : (let foo2 := Type@{_} in
       let foo3 := Type@{_} in
       let foo4 := Type@{_} in
  let set_le_foo3 := (fun y : Set => (fun x : foo3 => x) y) in
  let foo3_le_foo2 := (fun y : foo3 => (fun x : foo2 => x) y) in
  let foo2_le_foo4 := (fun y : foo2 => (fun x : foo4 => x) y) in
  let set_eq_foo4 := (fun y : foo4 => (fun x : Set => x) y) in
  nat) -> baz'.
