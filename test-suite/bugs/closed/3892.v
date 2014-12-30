(* Check that notation variables do not capture names hidden behind
   another notation. *)
Notation "A <-> B" := ((A -> B) * (B -> A))%type : type_scope.
Notation compose := (fun g f x => g (f x)).
Notation "g 'o' f" := (compose g f) (at level 40, left associativity).
Definition iff_compose {A B C : Type} (g : B <-> C) (f : A <-> B) : A <-> C :=
  (fst g o fst f , snd f o snd g).
(* Used to fail with: This expression should be a name. *)
