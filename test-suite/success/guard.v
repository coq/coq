(* Specific tests about guard condition *)

(* f must unfold to x, not F (de Bruijn mix-up!) *)
Check let x (f:nat->nat) k := f k in
      fun (y z:nat->nat) =>
      let f:=x in (* f := Rel 3 *)
      fix F (n:nat) : nat :=
        match n with
        | 0 => 0
        | S k => f F k (* here Rel 3 = F ! *)
        end.
