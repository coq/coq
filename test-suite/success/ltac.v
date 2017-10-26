(* The tactic language *)

(* Submitted by Pierre Crégut *)
(* Checks substitution of x *)
Ltac f x := unfold x; idtac.

Lemma lem1 : 0 + 0 = 0.
f plus.
reflexivity.
Qed.

(* Submitted by Pierre Crégut *)
(* Check syntactic correctness *)
Ltac F x := idtac; G x
 with G y := idtac; F y.

(* Check that Match Context keeps a closure *)
Ltac U := let a := constr:(I) in
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
  match constr:(t) with
  | context C[(?X1 = ?X2)] => context C [X1 = X2]
  end.

Lemma sym : 0 <> 1 -> 1 <> 0.
intro H.
let t := sym type of H in
assert t.
exact H.
intro H1.
apply H.
symmetry .
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
symmetry .
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
check_binding ipattern:(H).
Abort.

(* Check that variables explicitly parsed as ltac variables are not
   seen as intro pattern or constr (BZ#984) *)

Ltac afi tac := intros; tac.
Goal 1 = 2.
afi ltac:(auto).
Abort.

(* Tactic Notation avec listes *)

Tactic Notation "pat" hyp(id) "occs" integer_list(l) := pattern id at l.

Goal forall x, x=0 -> x=x.
intro x.
pat x occs 1 3.
Abort.

Tactic Notation "revert" ne_hyp_list(l) := generalize l; clear l.

Goal forall a b c, a=0 -> b=c+a.
intros.
revert a b c H.
Abort.

(* Used to fail until revision 9280 because of a parasitic App node with
   empty args *)

Goal True.
match constr:(@None) with @None => exact I end.
Abort.

(* Check second-order pattern unification *)

Ltac to_exist :=
  match goal with
  |- forall x y, @?P x y =>
    let Q := eval lazy beta in (exists x, forall y, P x y) in
    assert (Q->Q)
  end.

Goal forall x y : nat, x = y.
to_exist. exact (fun H => H).
Abort.

(* Used to fail in V8.1 *)

Tactic Notation "test" constr(t) integer(n) :=
   set (k := t) at n.

Goal forall x : nat, x = 1 -> x + x + x = 3.
intros x H.
test x 2.
Abort.

(* Utilisation de let rec sans arguments *)

Ltac is :=
  let rec i := match goal with |- ?A -> ?B => intro; i | _ => idtac end in
  i.

Goal True -> True -> True.
is.
exact I.
Abort.

(* Interférence entre espaces des noms *)

Ltac O := intro.
Ltac Z1 t := set (x:=t).
Ltac Z2 t := t.
Goal True -> True.
Z1 O.
Z2 ltac:(O).
exact I.
Qed.

(* Illegal application used to make Ltac loop. *)

Section LtacLoopTest.
  Ltac f x := idtac.
  Goal True.
  Timeout 1 try f()().
  Abort.
End LtacLoopTest.

(* Test binding of open terms *)

Ltac test_open_match z :=
  match z with
    (forall y x, ?h = 0) => assert (forall x y, h = x + y)
  end.

Goal True.
test_open_match (forall z y, y + z  = 0).
reflexivity.
apply I.
Qed.

(* Test binding of open terms with non linear matching *)

Ltac f_non_linear t :=
  match t with
    (forall x y, ?u = 0) -> (forall y x, ?u = 0) =>
       assert (forall x y:nat, u = u)
  end.

Goal True.
f_non_linear ((forall x y, x+y = 0) -> (forall x y, y+x = 0)).
reflexivity.
f_non_linear ((forall a b, a+b = 0) -> (forall a b, b+a = 0)).
reflexivity.
f_non_linear ((forall a b, a+b = 0) -> (forall x y, y+x = 0)).
reflexivity.
f_non_linear ((forall x y, x+y = 0) -> (forall a b, b+a = 0)).
reflexivity.
f_non_linear ((forall x y, x+y = 0) -> (forall y x, x+y = 0)).
reflexivity.
f_non_linear ((forall x y, x+y = 0) -> (forall y x, y+x = 0)) (* should fail *)
|| exact I.
Qed.

(* Test regular failure when clear/intro breaks soundness of the
   interpretation of terms in current environment *)

Ltac g y := clear y; assert (y=y).
Goal forall x:nat, True.
intro x.
Fail g x.
Abort.

Ltac h y := assert (y=y).
Goal forall x:nat, True.
intro x.
Fail clear x; f x.
Abort.

(* Do not consider evars as unification holes in Ltac matching (and at
   least not as holes unrelated to the original evars)
   [Example adapted from Ynot code]
 *)

Ltac not_eq e1 e2 :=
  match e1 with
    | e2 => fail 1
    | _ => idtac
  end.

Goal True.
evar(foo:nat).
let evval := eval compute in foo in not_eq evval 1.
let evval := eval compute in foo in not_eq 1 evval.
Abort.

(* Check instantiation of binders using ltac names *)

Goal True.
let x := ipattern:(y) in assert (forall x y, x = y + 0).
intro.
destruct y. (* Check that the name is y here *)
Abort.

(* An example suggested by Jason (see #4317) showing the intended semantics *)
(* Order of binders is reverted because y is just told to depend on x *)

Goal 1=1.
let T := constr:(fun a b : nat => a) in
  lazymatch T with
  | (fun x z => ?y) => pose ((fun x x => y) 2 1)
  end.
exact (eq_refl n).
Qed.

(* A variant of #2602 which was wrongly succeeding because "a", bound to
   "?m", was then internally turned into a "_" in the second matching *)

Goal exists m, S m > 0.
eexists.
Fail match goal with
 | |- context [ S ?a ] =>
     match goal with
       | |- S a > a => idtac
     end
end.
Abort.

(* Test evar syntax *)

Goal True.
evar (0=0).
Abort.

(* Test location of hypothesis in "symmetry in H". This was broken in
   8.6 where H, when the oldest hyp, was moved at the place of most
   recent hypothesis *)

Goal 0=1 -> True -> True.
intros H H0.
symmetry in H.
(* H should be the first hypothesis *)
match goal with h:_ |- _ => assert (h=h) end. (* h should be H0 *)
exact (eq_refl H0).
Abort.
