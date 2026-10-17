(* Test for the Kernel Unfold Height Heuristic flag. *)

(* Disable dependency heuristic, as it overrides the height heuristic. *)
Unset Kernel Conversion Dep Heuristic.

Unset Kernel Conversion Height Heuristic.

(* Tests for the Heuristic *)

Fixpoint fact (n : nat) :=
match n with
| O => 1
| S k => n * fact k
end.

(* [fact100'] depends on [fact100], so the definitional height of the former
   is greater than that of the latter.
*)
Definition fact100 := fact 100.
Definition fact100' := fact100.

Print Height fact100. (* fact100 : 4*)
Print Height fact100'. (* fact100' : 5*)

(* Case 1a: This is fast because the right side is unfolded first by default
   when both constants have the same strategy. So the equality is found
   after one unfolding step. *)
Timeout 1 Check eq_refl : fact100 = fact100'.

(* Case 1b: This times out because [fact100] is unfolded and reduced first,
   and so a costly computation is performed before [fact100'] is unfolded
   even once. *)
Fail Timeout 1 Check eq_refl : fact100' = fact100.


(* With the Heuristic.
   When both constants have the same strategy, the one with greatest definitional
   height is unfolded first. This heuristic over-approximates dependencies.
*)
Set Kernel Conversion Height Heuristic.

(* Case 2a: This is still fast. *)
Timeout 1 Check eq_refl : fact100 = fact100'.
(* Case 2b: Even though [fact100'] appears on the left, conversion
   unfolds it first guided by its strategy level. *)
Timeout 1 Check eq_refl : fact100' = fact100.


(* Additional Sanity Checks
   Interactive definitions also profit from the heuristic.
   When they are ended transparently (w/ [Defined.] or [Defined ident.],
   their heights are computed and stored.)
*)

Definition ifact100 : nat.
Proof. exact (fact 100). Defined.

Print Height ifact100. (* ifact100 : 4 *)

#[refine]
Definition ifact100' : nat := _.
Proof. exact ifact100. Defined.

Print Height ifact100'. (* ifact100' : 5 *)

Timeout 1 Check eq_refl : ifact100 = ifact100'.
Timeout 1 Check eq_refl : ifact100' = ifact100.
