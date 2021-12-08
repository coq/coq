Goal exists x, x = true.
Proof.
  evar (a : bool).
  exists a.
  (* Up to 8.5, this used to leave a constraint causing later tactics to fail *)
  (* From 8.5, it failed with an unsolvable constraint *)
  refine (unit_rec (fun s => unit_rec _ _ s = _) _ tt).
  reflexivity.
Qed.

Goal forall y : sumbool True True, exists x, x = sumbool_rect (fun _ => bool) (fun _ => true) (fun _ => true) y.
  eexists.
  let x := match goal with |- ?x = _ => constr:(x) end in
  let k := fresh in
  set (k := x);
    match goal with
      | [ |- _ = sumbool_rect ?T (fun b => _) (fun c => _) ?v ]
        => refine (_ : sumbool_rect T (fun b => _) (fun c => _) v = _)
    end;
    match goal with
      | [ |- _ = sumbool_rect ?T (fun b => _) (fun c => _) ?v ]
        => refine (sumbool_rect
                     (fun sb => sumbool_rect T _ _ sb = sumbool_rect T _ _ sb)
                     _
                     _
                     v);
          try intro; simpl sumbool_rect
      | [ |- bool ] => idtac
    end.
  reflexivity.
  reflexivity.
Qed.
