(* Checking that let-in's hiding evars are expanded when enforcing
   "occur-check" *)

Definition foo x y :=
let xy := (x, y) in
let bar xys  :=
      match xys with
      | nil => cons xy nil
      | cons xy' xys' => cons xy' xys'
      end in bar (nil : list (nat * nat)).
