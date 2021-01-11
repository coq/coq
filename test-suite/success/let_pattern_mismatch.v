(* Weird corner case accepted by the pattern-matching algorithm. Destructuring
   let-bindings in patterns can actually be shorter than the case they match. *)

Inductive ascii : Set :=
| Ascii : bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> ascii.

Definition dummy (a : ascii) : unit :=
  let (a0,a1,a2,a3,a4,a5,a6,a7) := a in tt.

Goal forall (a : ascii) (H : tt = dummy a), True.
Proof.
intros a H.
unfold dummy in *.
(* Two bound variables in the pattern, eight in the term. *)
match goal with
| H:context [ let (x, y) := ?X in _ ] |- _ => destruct X eqn:?
end.
Abort.
