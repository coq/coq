Require Import Ltac2.Ltac2 Ltac2.Notations.

Ltac2 Type exn ::= [ Nope ].

Ltac2 check_id id id' := match Ident.equal id id' with
| true => ()
| false => Control.throw Nope
end.

Goal True -> False.
Proof.
Fail
let b := { contents := true } in
let f c :=
  match b.(contents) with
  | true => Message.print (Message.of_constr c); b.(contents) := false; fail
  | false => ()
  end
in
(** This fails because the matching is not allowed to backtrack once
    it commits to a branch*)
lazy_match! '(nat -> bool) with context [?a] => f a end.
lazy_match! Control.goal () with ?a -> ?b => Message.print (Message.of_constr b) end.

(** This one works by taking the second match context, i.e. ?a := nat *)
let b := { contents := true } in
let f c :=
  match b.(contents) with
  | true => b.(contents) := false; fail
  | false => Message.print (Message.of_constr c)
  end
in
match! '(nat -> bool) with context [?a] => f a end.
Abort.

Goal forall (i j : unit) (x y : nat) (b : bool), True.
Proof.
Fail match! goal with
| [ h : ?t, h' : ?t |- _ ] => ()
end.
intros i j x y b.
match! goal with
| [ h : ?t, h' : ?t |- _ ] =>
  check_id h @x;
  check_id h' @y
end.
match! reverse goal with
| [ h : ?t, h' : ?t |- _ ] =>
  check_id h @j;
  check_id h' @i
end.
Abort.

(* Check #79 *)
Goal 2 = 3.
  Control.plus
    (fun ()
     => lazy_match! goal with
    | [ |- 2 = 3 ] => Control.zero (Tactic_failure None)
    | [ |- 2 = _ ] => Control.zero (Tactic_failure (Some (Message.of_string "should not be printed")))
     end)
    (fun e
     => match e with
        | Tactic_failure c
          => match c with
             | None => ()
             | _ => Control.zero e
             end
        | e => Control.zero e
        end).
Abort.
