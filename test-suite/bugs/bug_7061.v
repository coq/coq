(* A few examples of non strongly normalizing fixpoints *)

Fail Fixpoint beta_erase (v:bool) := (fun x y => x) 0 (beta_erase v).

Fail Fixpoint zeta_erase (v:bool) := let _ := zeta_erase v in 0.

Fail Fixpoint iota_case_erase (v:bool) :=
  match true with
  | true => 0
  | false => iota_case_erase v
  end.

Fail Fixpoint iota_fix_erase (v:bool) :=
  let g1 := fix g1 (x : nat) := x
            with g2 (x : nat) := iota_fix_erase v
            for g1
  in
  g1 0.

Fail Fixpoint f (x : bool) :=
  let y := f x in
  match true with
  | true => true
  | false => y
  end.
