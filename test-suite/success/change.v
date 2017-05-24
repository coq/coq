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
change 3 at 2 with (1+2).
change 3 at 2 with (1+2) in H |-.
change 3 with (1+2) in H at 1 |- * at 1.
(* Now check that there are no more 3's *)
change 3 with (1+2) in * || reflexivity.
Qed.

(* Note: the following is invalid and must fail
change 3 at 1 with (1+2) at 3.
change 3 at 1 with (1+2) in *.
change 3 at 1 with (1+2) in H at 2 |-.
change 3 at 1 with (1+2) at 3.
change 3 at 1 with (1+2) in H |- *.
change 3 at 1 with (1+2) in H, H|-.
change 3 at 1.
 *)

(* Test that pretyping checks allowed elimination sorts *)

Goal True.
Fail change True with (let (x,a) := ex_intro _ True (eq_refl True) in x).
Fail change True with
        match ex_intro _ True (eq_refl True) with ex_intro x _ => x end.
Abort.

(* Check absence of loop in identity substitution (was failing up to
   Sep 2014, see #3641) *)

Goal True.
change ?x with x.
Abort.

(* Check typability after change of type subterms *)
Goal nat = nat :> Set.
Fail change nat with (@id Type nat). (* would otherwise be ill-typed *)
Abort.

(* Check typing env for rhs is the correct one *)

Goal forall n, let x := n in id (fun n => n + x) 0 = 0.
intros.
unfold x.
(* check that n in 0+n is not interpreted as the n from "fun n" *)
change n with (0+n).
Abort.

(* Check non-collision of non-normalized defined evars with pattern variables *)

Goal exists x, 1=1 -> x=1/\x=1.
eexists ?[n]; intros; split.
eassumption.
match goal with |- ?x=1 => change (x=1) with (0+x=1) end.
match goal with |- 0+1=1 => trivial end.
Qed.
