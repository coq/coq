(* Check that problems with several solutions are solved in 8.4 as in 8.2 and 8.3 *)

Inductive Fin: nat -> Set :=
| first k : Fin (S k)
| succ k: Fin k -> Fin (S k).

Lemma match_sym_eq_eq: forall (n1 n2: nat)(f: Fin n1)(e: n1 = n2),
f = match sym_eq e in (_ = l) return (Fin l) with refl_equal =>
    match e in (_ = l) return (Fin l) with refl_equal => f end end.
Proof.
  intros n1 n2 f e.
  (* Next line has a dependent and a non dependent solution *)
  (* 8.2 and 8.3 used to choose the dependent one which is the one to make *)
  (* the goal progress *)
  refine (match e return _ with refl_equal => _ end).
  reflexivity.
  Undo 2.
  (** Check insensitivity to alphabetic order *)
  refine (match e as a in _ = b return _ with refl_equal => _ end).
  reflexivity.
  Undo 2.
  (** Check insensitivity to alphabetic order *)
  refine (match e as z in _ = y return _ with refl_equal => _ end).
  reflexivity.
  Undo 2.
  (* Next line similarly has a dependent and a non dependent solution *)
  refine (match e with refl_equal => _ end).
  reflexivity.
Qed.
