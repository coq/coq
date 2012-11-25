(* Checking that let-in's hiding evars are expanded when enforcing
   "occur-check" *)

Require Import List.

Definition foo x y :=
let xy := (x, y) in
let bar xys  :=
      match xys with
      | nil => xy :: nil
      | xy' :: xys' => xy' :: xys'
      end in bar (nil : list (nat * nat)).
