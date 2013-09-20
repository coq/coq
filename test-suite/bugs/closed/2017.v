(* Some check of Miller's pattern inference - used to fail in 8.2 due
   first to the presence of aliases, secondly due to the absence of
   restriction of the potential interesting variables to the subset of
   variables effectively occurring in the term to instantiate *)

Set Implicit Arguments.

Variable choose : forall(P : bool -> Prop)(H : exists x, P x), bool.

Variable H : exists x : bool, True.

Definition coef :=
match Some true	with
  Some _ => @choose _ H |_ => true
end .
