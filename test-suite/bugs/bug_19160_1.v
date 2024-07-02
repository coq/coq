Inductive trip := Z | L (_:trip) (_:trip) | R (_:trip).

Type fun x:bool =>
  fix foo (n:trip) : x = x := eq_refl
  with bar (n:trip) : x = x :=
  match n with
  | Z => eq_refl
  | L k _ => bar k
  | R k => foo k
  end
for foo.
(* Error: In pattern-matching on term "n" the branch for constructor "R" has type
 "fun _ : trip => _UNBOUND_REL_6 = _UNBOUND_REL_6" which should be "fun _ : trip => x = x".
*)
