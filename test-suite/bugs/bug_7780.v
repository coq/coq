(* A lift was missing in expanding aliases under binders for unification *)

(* Below, the lift was missing while expanding the reference to
   [mkcons] in [?N] which was under binder [arg] *)

Goal forall T (t : T) (P P0 : T -> Set), option (option (list (P0 t)) -> option (list (P t))).
  intros ????.
  refine (Some
            (fun rls
             => let mkcons := ?[M] in
                let default arg := ?[N] in
                match rls as rls (* 2 *) return option (list (P ?[O])) with
                | Some _ => None
                | None => None
                end)).
Abort.
