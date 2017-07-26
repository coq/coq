Require Import Ltac2.Ltac2.

Ltac2 foo (_ : int) :=
  let f (x : int) := x in
  let _ := f 0 in
  f 1.

Print Ltac2 foo.

Import Control.

Ltac2 exact x := refine (fun _ => x).

Print Ltac2 refine.
Print Ltac2 exact.

Ltac2 foo' _ := ident:(bla).

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
Ltac2 foo0 _ := { contents := None }.

Print Ltac2 foo0.

Ltac2 qux0 x := x.(contents).
Ltac2 qux1 x := x.(contents) := x.(contents).

Ltac2 qux2 := ([1;2], true).

Print Ltac2 qux0.
Print Ltac2 qux1.
Print Ltac2 qux2.

Import Control.

Ltac2 qux3 x := constr:(nat -> ltac2:(refine (fun _ => hyp x))).

Print Ltac2 qux3.

Ltac2 qux4 f x := x, (f x, x).

Print Ltac2 qux4.

Ltac2 Type rec nat := [ O | S (nat) ].

Ltac2 message_of_nat n :=
let rec aux n :=
match n with
| O => Message.of_string "O"
| S n => Message.concat (Message.of_string "S") (aux n)
end in aux n.

Print Ltac2 message_of_nat.

Ltac2 numgoals (_ : unit) :=
  let r := { contents := O } in
  enter (fun _ => r.(contents) := S (r.(contents)));
  r.(contents).

Print Ltac2 numgoals.

Goal True /\ False.
Proof.
let n := numgoals () in Message.print (message_of_nat n).
refine (fun _ => open_constr:((fun x => conj _ _) 0)); ().
let n := numgoals () in Message.print (message_of_nat n).

Fail (hyp ident:(x)).
Fail (enter (fun _ => hyp ident:(There_is_no_spoon); ())).

enter (fun _ => Message.print (Message.of_string "foo")).

enter (fun _ => Message.print (Message.of_constr (goal ()))).
Fail enter (fun _ => Message.print (Message.of_constr (qux3 ident:(x)))).
enter (fun _ => plus (fun _ => constr:(_); ()) (fun _ => ())).
plus
  (fun _ => enter (fun _ => let x := ident:(foo) in let _ := hyp x in ())) (fun _ => Message.print (Message.of_string "failed")).
let x := { contents := 0 } in
let x := x.(contents) := x.(contents) in x.
Abort.

Ltac2 Type exn ::= [ Foo ].

Goal True.
Proof.
plus (fun _ => zero Foo) (fun _ => ()).
Abort.

Ltac2 Type exn ::= [ Bar (string) ].

Goal True.
Proof.
Fail zero (Bar "lol").
Abort.

Ltac2 Notation "refine!" c(constr) := refine c.

Goal True.
Proof.
refine! I.
Abort.

Goal True.
Proof.
let x _ := plus (fun _ => 0) (fun _ => 1) in
match case x with
| Val x =>
  match x with
  | (x, k) => Message.print (Message.of_int (k Not_found))
  end
| Err x => Message.print (Message.of_string "Err")
end.
Abort.
