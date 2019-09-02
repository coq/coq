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

(* Check that the heuristic to solve constraints is not artificially
   dependent on the presence of a let-in, and in particular that the
   second [_] below is not inferred to be n, as if obtained by
   first-order unification with [T n] of the conclusion [T _] of the
   type of the first [_]. *)

(* Note: exact numbers of evars are not important... *)

Inductive T (n:nat) : Type := A : T n.
Check fun n (y:=A n:T n) => _ _ : T n.
Check fun n => _ _ : T n.
