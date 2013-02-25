(* Check that types are not uselessly unfolded *)

(* Check here that P returns something of type "option L" and not
   "option (list nat)" *)

Definition L := list nat.

Definition P (e:option L) :=
  match e with
  | None => None
  | Some cl => Some cl
  end.

Print P.

(* Check that plus is folded even if reduction is involved *)
Check (fun m n p (H : S m <= (S n) + p) => le_S_n _ _ H).
