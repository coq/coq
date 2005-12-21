(* The tactic language *)

(* Submitted by Pierre Crégut *)
(* Checks substitution of x *)
Ltac f x := unfold x in |- *; idtac.
 
Lemma lem1 : 0 + 0 = 0.
f plus.
reflexivity.
Qed.

(* Submitted by Pierre Crégut *)
(* Check syntactic correctness *)
Ltac F x := idtac; G x
 with G y := idtac; F y.

(* Check that Match Context keeps a closure *)
Ltac U := let a := constr:I in
          match goal with
          |  |- _ => apply a
          end.

Lemma lem2 : True.
U.
Qed.

(* Check that Match giving non-tactic arguments are evaluated at Let-time *)
 
Ltac B := let y := (match goal with
                    | z:_ |- _ => z
                    end) in
          (intro H1; exact y).

Lemma lem3 : True -> False -> True -> False.
intros H H0.
B.  (* y is H0 if at let-time, H1 otherwise *)
Qed.

(* Checks the matching order of hypotheses *)
Ltac Y := match goal with
          | x:_,y:_ |- _ => apply x
          end.
Ltac Z := match goal with
          | y:_,x:_ |- _ => apply x
          end.

Lemma lem4 : (True -> False) -> (False -> False) -> False.
intros H H0.
Z. (* Apply H0 *)
Y. (* Apply H *)
exact I.
Qed.

(* Check backtracking *)
Lemma back1 : 0 = 1 -> 0 = 0 -> 1 = 1 -> 0 = 0.
intros;
 match goal with
 | _:(0 = ?X1),_:(1 = 1) |- _ => exact (refl_equal X1)
 end.
Qed.

Lemma back2 : 0 = 0 -> 0 = 1 -> 1 = 1 -> 0 = 0.
intros;
 match goal with
 | _:(0 = ?X1),_:(1 = 1) |- _ => exact (refl_equal X1)
 end.
Qed.

Lemma back3 : 0 = 0 -> 1 = 1 -> 0 = 1 -> 0 = 0.
intros;
 match goal with
 | _:(0 = ?X1),_:(1 = 1) |- _ => exact (refl_equal X1)
 end.
Qed.

(* Check context binding *)
Ltac sym t :=
  match constr:t with
  | context C[(?X1 = ?X2)] => context C [X1 = X2]
  end.

Lemma sym : 0 <> 1 -> 1 <> 0.
intro H.
let t := sym type of H in
assert t.
exact H.
intro H1.
apply H.
symmetry  in |- *.
assumption.
Qed.

(* Check context binding in match goal *)
(* This wasn't working in V8.0pl1, as the list of matched hyps wasn't empty *)
Ltac sym' :=
  match goal with
  | _:True |- context C[(?X1 = ?X2)] =>
      let t := context C [X2 = X1] in
      assert t
  end.

Lemma sym' : True -> 0 <> 1 -> 1 <> 0.
intros Ht H.
sym'.
exact H.
intro H1.
apply H.
symmetry  in |- *.
assumption.
Qed.

(* Check that fails abort the current match context *)
Lemma decide : True \/ False.
match goal with
| _ => fail 1
| _ => right
end || left.
exact I.
Qed.

(* Check that "match c with" backtracks on subterms *)
Lemma refl : 1 = 1.
let t :=
 (match constr:(1 = 2) with
  | context [(S ?X1)] => constr:(refl_equal X1:1 = 1)
  end) in
assert (H := t).
assumption.
Qed.

(* Note that backtracking in "match c with" is only on type-checking not on
evaluation of tactics. E.g., this does not work

Lemma refl : (1)=(1).
Match (1)=(2) With
  [[(S ?1)]] -> Apply (refl_equal nat ?1).
Qed.
*)


(* Check the precedences of rel context, ltac context and vars context *)
(* (was wrong in V8.0) *)

Ltac check_binding y := cut ((fun y => y) = S).
Goal True.
check_binding true.
Abort.
