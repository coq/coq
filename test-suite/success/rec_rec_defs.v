Notation "'∑' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Unset Guard Checking.
Print Typing Flags.
Definition test :=
  fix f (n : nat) : Type :=
    match n with
    | 0 => unit
    | S n => ∑ (a : f n), (g n a = 0)
    end
  (* We must give the strucutral argument, Coq still checks it comes
    before any recursive call and we will need at least that for [f n] to
    be considered an ok recursive call.by guard checking. *)
  with g (n : nat) (x : f n) {struct n} : nat :=
    match n return f n -> nat with
    | 0 => fun _ => 0
    | S n => fun p => 0
    end x
  for f.

Eval compute in (test 2).
