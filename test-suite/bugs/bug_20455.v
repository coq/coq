Definition not_zero n := match n with 0 => False | S _ => True end.
Definition not_one n := match n with 0 => False | S n => not_zero n end.

(* Written as clear as I can make it. #[refine] is not needed.  *)
Fixpoint issue (n : nat) {struct n} : not_zero n -> False.
  refine
  match n with
  | 0 => fun h => h
  | S subn => fun h =>
    let f (b : bool) (e : b = true) (x : nat) (Hx : not_one x) :=
      let arg := (match (if b then x else subn) with 0 => subn | S subsubn => subsubn end) in
      issue arg _
    in
    f true eq_refl 5 I
  end.
  subst b.
  destruct x; cbn in Hx.
  - now exfalso.
  - assumption.
Fail Defined.
Abort.
