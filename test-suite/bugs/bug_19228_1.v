Axiom invert_Some : forall {A} (x : option A),
    match x with
    | Some _ => A
    | None => unit
    end.
(* A gets elaborated to Type on master but Set on this PR. *)
Check @invert_Some Type.
