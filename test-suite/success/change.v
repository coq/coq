(* A few tests of the syntax of clauses and of the interpretation of change *)

Goal let a := 0+0 in a=a.
intro.
change 0 in (value of a).
change ((fun A:Type => A) nat) in (type of a).
Abort.

Goal forall x, 2 + S x = 1 + S x.
intro. 
change (?u + S x) with (S (u + x)). 
Abort.

(* Check the combination of at, with and in (see bug #2146) *)

Goal 3=3 -> 3=3. intro H.
change 3 at 2 with (1+2) in |- *.
change 3 at 2 with (1+2) in H |-.
change 3 with (1+2) in H at 1 |- * at 1.
(* Now check that there are no more 3's *)
change 3 with (1+2) in * || reflexivity.
Qed.

(* Note: the following is invalid and must fail
change 3 at 1 with (1+2) at 3.
change 3 at 1 with (1+2) in *.
change 3 at 1 with (1+2) in H at 2 |-.
change 3 at 1 with (1+2) in |- * at 3.
change 3 at 1 with (1+2) in H |- *.
change 3 at 1 with (1+2) in H, H|-.
change 3 in |- * at 1.
 *)

(* Test that pretyping checks allowed elimination sorts *)

Goal True.
Fail change True with (let (x,a) := ex_intro _ True (eq_refl True) in x).
Fail change True with
        match ex_intro _ True (eq_refl True) with ex_intro x _ => x end.
Abort.
