(* Two types that differ only in a cast at the head of an application, which
   the traversal reads (it visits the type of the cast) and a comparison that
   flattens applications and looks through casts does not.

   The second query of each pair replays what the first recorded. A replay
   folds the references of a root in the order of [GlobRef.Set_env], which is
   hash order (it sorts by name only among references with one hash), so the
   types of the axioms are folded in an order that is neither source order nor
   name order. A wrongly merged pair loses the references of the type folded
   second, so a section shows the bug in either order only when each of its
   two types has a reference the other lacks (sections 2 and 3). Section 1
   compares a plain type with a cast of it, whose references include the plain
   type's, so it shows the bug only when the plain type is folded first.

   Each section is independent of the others. *)

Definition add (a b : nat) : nat := b.

(* ---- 1 ---- A plain type ([zz]) and a cast ([aa]): merged, the replay loses
   [ax0], which only the cast mentions, if it folds [zz] before [aa]. It does
   with the current hash order of these two names, and a rename could change
   that, which is why sections 2 and 3 do not depend on it. *)
Axiom ax0 : nat.
Definition X : Set := (fun _ : nat => nat) ax0.
Axiom zz : (fun _ : nat => nat) (add 0 0).
Axiom aa : (fun _ : nat => nat) ((add 0 <: X -> nat) 0).
Definition r1 : nat := (fun _ _ : nat => 0) aa zz.
Print Assumptions r1.
Print Assumptions r1.

(* ---- 2 ---- Two casts, each naming a reference the other lacks ([A0] and
   [A1]), with the axiom naming the larger reference first in the source and
   then the smaller. Merged, the type folded second loses its reference
   whichever it is. *)
Definition Y := nat.
Definition f (n : nat) : Y -> nat := fun _ => n.
Definition g (p : f 0 0 = 0) : True := I.
Axiom A0 : Prop.
Axiom A1 : Prop.
Axiom b0 : (f 0 <: (((fun _ : Prop => Y) A0) -> nat)) 0 = 0.
Axiom b1 : (f 0 <: (((fun _ : Prop => Y) A1) -> nat)) 0 = 0.
Definition R : True := let _ := g b0 in let _ := g b1 in I.
Print Assumptions R.
Print Assumptions R.

(* The same with the axioms named in the opposite order: [c0] names [B1] and
   [c1] names [B0]. *)
Axiom B0 : Prop.
Axiom B1 : Prop.
Axiom c0 : (f 0 <: (((fun _ : Prop => Y) B1) -> nat)) 0 = 0.
Axiom c1 : (f 0 <: (((fun _ : Prop => Y) B0) -> nat)) 0 = 0.
Definition R' : True := let _ := g c0 in let _ := g c1 in I.
Print Assumptions R'.
Print Assumptions R'.

(* ---- 3 ---- The same under Print All Dependencies, in both naming orders. *)
Axiom C0 : Prop.
Axiom C1 : Prop.
Axiom d0 : (f 0 <: (((fun _ : Prop => Y) C0) -> nat)) 0 = 0.
Axiom d1 : (f 0 <: (((fun _ : Prop => Y) C1) -> nat)) 0 = 0.
Definition S : True := let _ := g d0 in let _ := g d1 in I.
Print All Dependencies S.
Print All Dependencies S.

Axiom D0 : Prop.
Axiom D1 : Prop.
Axiom e0 : (f 0 <: (((fun _ : Prop => Y) D1) -> nat)) 0 = 0.
Axiom e1 : (f 0 <: (((fun _ : Prop => Y) D0) -> nat)) 0 = 0.
Definition S' : True := let _ := g e0 in let _ := g e1 in I.
Print All Dependencies S'.
Print All Dependencies S'.
