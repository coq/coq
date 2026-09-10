Goal True.
  eassert ?[T].
  Fail progress (eassert ?[T'] as H; [|let _ := constr:(eq_refl _ :> ?T = ?T') in exact H]).
  Fail progress (eassert ?[T'] as H; [|instantiate (T := ?T'); exact H]).
Abort.
