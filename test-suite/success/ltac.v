(* The tactic language *)

(* Submitted by Pierre Crégut *)
(* Checks substitution of x *)
Tactic Definition f x := Unfold x; Idtac.
 
Lemma lem1 : (plus O O) = O.
f plus.
Reflexivity.
Qed.

(* Submitted by Pierre Crégut *)
(* Check syntactic correctness *)
Recursive Tactic Definition F x := Idtac; (G x)
And G y := Idtac; (F y).

(* Check that Match Context keeps a closure *)
Tactic Definition U := Let a = 'I In Match Context With [ |- ? ] -> Apply a.

Lemma lem2 : True.
U.
Qed.

(* Check that Match giving non-tactic arguments are evaluated at Let-time *)
 
Tactic Definition B :=
 Let y = (Match Context With [ z:? |- ? ] -> z) In 
 Intro H1; Exact y.

Lemma lem3 : True -> False -> True -> False.
Intros H H0.
B.  (* y is H0 if at let-time, H1 otherwise *)
Qed.

(* Checks the matching order of hypotheses *)
Tactic Definition Y := Match Context With [ x:?; y:? |- ? ] -> Apply x.
Tactic Definition Z := Match Context With [ y:?; x:? |- ? ] -> Apply x.

Lemma lem4 : (True->False) -> (False->False) -> False.
Intros H H0.
Z. (* Apply H0 *)
Y. (* Apply H *)
Exact I.
Qed.

(* Check backtracking *)
Lemma back1 : (0)=(1)->(0)=(0)->(1)=(1)->(0)=(0).
Intros; Match Context With [_:(O)=?1;_:(1)=(1)|-? ] -> Exact (refl_equal ? ?1).
Qed.

Lemma back2 : (0)=(0)->(0)=(1)->(1)=(1)->(0)=(0).
Intros; Match Context With [_:(O)=?1;_:(1)=(1)|-? ] -> Exact (refl_equal ? ?1).
Qed.

Lemma back3 : (0)=(0)->(1)=(1)->(0)=(1)->(0)=(0).
Intros; Match Context With [_:(O)=?1;_:(1)=(1)|-? ] -> Exact (refl_equal ? ?1).
Qed.

(* Check context binding *)
Tactic Definition sym t := Match t With [C[?1=?2]] -> Inst C[?1=?2].

Lemma sym : ~(0)=(1)->~(1)=(0).
Intro H.
Let t = (sym (Check H)) In Assert t.
Exact H.
Intro H1.
Apply H.
Symmetry.
Assumption.
Qed.

(* Check context binding in match goal *)
(* This wasn't working in V8.0pl1, as the list of matched hyps wasn't empty *)
Tactic Definition sym' := 
  Match Context With [_:True|-C[?1=?2]] -> Let t = Inst C[?2=?1] In Assert t.

Lemma sym' : True->~(0)=(1)->~(1)=(0).
Intros Ht H.
sym'.
Exact H.
Intro H1.
Apply H.
Symmetry.
Assumption.
Qed.

(* Check that fails abort the current match context *)
Lemma decide : True \/ False.
(Match Context With
| _ -> Fail 1
| _ -> Right) Orelse Left.
Exact I.
Qed.

(* Check that "match c with" backtracks on subterms *)
Lemma refl : (1)=(1).
Let t = (Match (1)=(2) With
  [[(S ?1)]] -> '((refl_equal nat ?1) :: (1)=(1)))
In Assert H:=t.
Assumption.
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

Tactic Definition check_binding y := Cut (([y]y) = S).
Goal True.
check_binding true.
Abort.
