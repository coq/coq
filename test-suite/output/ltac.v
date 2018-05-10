(* This used to refer to b instead of z sometimes between 8.4 and 8.5beta3 *)
Goal True.
Fail let T := constr:((fun a b : nat => a+b) 1 1) in
  lazymatch T with
  | (fun x z => ?y) 1 1
    => pose ((fun x _ => y) 1 1)
  end.
Abort.

(* This should not raise a warning (see #4317) *)
Goal True.
assert (H:= eq_refl ((fun x => x) 1)).
let HT := type of H in
lazymatch goal with
| H1 : HT |- _ => idtac
end.
Abort.

Ltac f x y z :=
  symmetry in x, y;
  auto with z;
  auto;
  intros;
  clearbody x;
  generalize dependent z.

Print Ltac f.

(* Error messages *)

Ltac g1 x := refine x.
Tactic Notation "g2" constr(x) := g1 x.
Tactic Notation "f1" constr(x) := refine x.
Ltac f2 x := f1 x.
Goal False.
Fail g1 I.
Fail f1 I.
Fail g2 I.
Fail f2 I.
Abort.

Ltac h x := injection x.
Goal True -> False.
Fail h I.
intro H.
Fail h H.
Abort.

(* Check printing of the "var" argument "Hx" *)
Ltac m H := idtac H; exact H.
Goal True.
let a:=constr:(let Hx := 0 in ltac:(m Hx)) in idtac.
Abort.

(* Check consistency of interpretation scopes (#4398) *)

Goal nat*(0*0=0) -> nat*(0*0=0). intro.
match goal with H: ?x*?y |- _ => idtac x end.
match goal with |- ?x*?y => idtac x end.
match goal with H: context [?x*?y] |- _ => idtac x end.
match goal with |- context [?x*?y] => idtac x end.
Abort.

(* Check printing of let in Ltac and Tactic Notation *)

Ltac foo :=
  let x := intros in
  let y := intros -> in
  let v := constr:(@ nil True) in
  let w := () in
  let z := 1 in
  pose v.
Print Ltac foo.
