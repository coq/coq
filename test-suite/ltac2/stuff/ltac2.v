Require Import Ltac2.Ltac2.

Ltac2 foo (_ : int) :=
  let f (x : int) := x in
  let _ := f 0 in
  f 1.

Print Ltac2 foo.

Import Control.

Ltac2 exact x := refine (fun () => x).

Print Ltac2 refine.
Print Ltac2 exact.

Ltac2 foo' () := ident:(bla).

Print Ltac2 foo'.

Ltac2 bar x h := match x with
| None => constr:(fun H => ltac2:(exact (hyp ident:(H))) -> nat)
| Some x => x
end.

Print Ltac2 bar.

Ltac2 qux := Some 0.

Print Ltac2 qux.

Ltac2 Type foo := [ Foo (int) ].

Fail Ltac2 qux0 := Foo None.

Ltac2 Type 'a ref := { mutable contents : 'a }.

Fail Ltac2 qux0 := { contents := None }.
Ltac2 foo0 () := { contents := None }.

Print Ltac2 foo0.

Ltac2 qux0 x := x.(contents).
Ltac2 qux1 x := x.(contents) := x.(contents).

Ltac2 qux2 := ([1;2], true).

Print Ltac2 qux0.
Print Ltac2 qux1.
Print Ltac2 qux2.

Import Control.

Ltac2 qux3 x := constr:(nat -> ltac2:(refine (fun () => hyp x))).

Print Ltac2 qux3.

Ltac2 Type rec nat := [ O | S (nat) ].

Ltac2 message_of_nat n :=
let rec aux n :=
match n with
| O => Message.of_string "O"
| S n => Message.concat (Message.of_string "S") (aux n)
end in aux n.

Print Ltac2 message_of_nat.

Ltac2 numgoals () :=
  let r := { contents := O } in
  enter (fun () => r.(contents) := S (r.(contents)));
  r.(contents).

Print Ltac2 numgoals.

Goal True /\ False.
Proof.
let n := numgoals () in Message.print (message_of_nat n).
refine (fun () => open_constr:((fun x => conj _ _) 0)); ().
let n := numgoals () in Message.print (message_of_nat n).

Fail (hyp ident:(x)).
Fail (enter (fun () => hyp ident:(There_is_no_spoon); ())).

enter (fun () => Message.print (Message.of_string "foo")).

enter (fun () => Message.print (Message.of_constr (goal ()))).
Fail enter (fun () => Message.print (Message.of_constr (qux3 ident:(x)))).
enter (fun () => plus (fun () => constr:(_); ()) (fun _ => ())).
plus
  (fun () => enter (fun () => let x := ident:(foo) in let _ := hyp x in ())) (fun _ => Message.print (Message.of_string "failed")).
let x := { contents := 0 } in
let x := x.(contents) := x.(contents) in x.
Abort.

Ltac2 Type exn ::= [ Foo ].

Goal True.
Proof.
plus (fun () => zero Foo) (fun _ => ()).
Abort.

Ltac2 Type exn ::= [ Bar (string) ].

Goal True.
Proof.
Fail zero (Bar "lol").
Abort.

Ltac2 Notation "refine!" c(thunk(constr)) := refine c.

Goal True.
Proof.
refine! I.
Abort.

Goal True.
Proof.
let x () := plus (fun () => 0) (fun _ => 1) in
match case x with
| Val x =>
  match x with
  | (x, k) => Message.print (Message.of_int (k Not_found))
  end
| Err x => Message.print (Message.of_string "Err")
end.
Abort.

Goal (forall n : nat, n = 0 -> False) -> True.
Proof.
refine (fun () => '(fun H => _)).
Std.case true (hyp @H, Std.ExplicitBindings [Std.NamedHyp @n, '0]).
refine (fun () => 'eq_refl).
Qed.

Goal forall x, 1 + x = x + 1.
Proof.
refine (fun () => '(fun x => _)).
Std.cbv {
  Std.rBeta := true; Std.rMatch := true; Std.rFix := true; Std.rCofix := true;
  Std.rZeta := true; Std.rDelta := true; Std.rConst := [];
} { Std.on_hyps := None; Std.on_concl := Std.AllOccurrences }.
Abort.
