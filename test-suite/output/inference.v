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
