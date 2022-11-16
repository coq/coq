Require Import Ltac2.Ltac2 Ltac2.Notations.

Ltac2 Type exn ::= [ Nope ].

Ltac2 check_constr x y := match Constr.equal x y with
| true => ()
| false => Control.throw Nope
end.

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

pose (def1 := 0 + 0).
pose (def2 := true).
match! goal with
| [ h := _ |- _ ] => check_id h @def2
end.
match! reverse goal with
| [ h := _ |- _ ] => check_id h @def1
end.
match! goal with
| [ h := _ : nat |- _ ] => check_id h @def1
end.
match! goal with
| [ h : nat |- _ ] => check_id h @def1
end.
match! reverse goal with
| [ h : nat |- _ ] => check_id h @x
end.
match! goal with
| [ h := ?v |- _ ] => check_constr v constr:(true)
end.
match! goal with
| [ h := context c [ 0 ] |- _ ] => check_constr (Pattern.instantiate c constr:(3)) constr:(3 + 0)
end.
match! goal with
| [ h1 : context [ unit ] , h2 := context [ 0 ] , h3 : context [ bool ] |- _ ] => ()
end.
match! goal with
| [ h1 : unit , h2 := context [ 0 ] , h3 : context [ bool ] |- _ ] => ()
end.
lazy_match! goal with
| [ h1 : context c1 [ ?t1 ] , h2 := context c2 [ Nat.add ?v2 ] , h3 : context c3 [ ?t2 ] |- _ ] =>
    check_constr t1 'bool;
    check_constr v2 '0;
    check_constr t2 'bool;
    check_constr (Pattern.instantiate c1 'Empty_set) 'Empty_set;
    check_constr (Pattern.instantiate c2 '(Nat.add 1)) '(1 + 0);
    check_constr (Pattern.instantiate c3 'unit) 'unit
end.
match! goal with
| [ h1 : unit , h2 := context c2 [ Nat.add ?v2 ] , h3 : context c3 [ ?t2 ] |- _ ] =>
    check_constr v2 '0;
    check_constr t2 'bool;
    check_constr (Pattern.instantiate c2 '(Nat.add 1)) '(1 + 0);
    check_constr (Pattern.instantiate c3 'unit) 'unit
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

Fail Ltac2 Eval fun x => match x with (x,x) => x end.
Ltac2 Eval fun x => match x with (x,y) => x end.

Module StupidTuple.
  Ltac2 foo x :=
    match x with
    | ((a,b),c) => b
    end .

  Fail Ltac2 Eval foo (1,2).
End StupidTuple.

Module Empty.
  Ltac2 Type empty := [].
  Ltac2 bar (x:empty) := match x with end.
End Empty.

Module DeepType.
  Ltac2 Type rec mylist := [ Nil | One (unit option) | Cons (unit option, mylist) ].

  Fail Ltac2 test x :=
    match x with
    | Nil, _ => ()
    | _, Nil => ()
    | One None, _ => ()
    | _, One None => ()
    end.

  Fail Ltac2 test x :=
    match x with
    | Nil, _ => ()
    | _, Nil => ()
    | One None, _ => ()
    | _, One None => ()
    | Cons _ _, Cons _ _ => ()
    end.

  Succeed Ltac2 test x :=
    match x with
    | Nil, _ => ()
    | _, Nil => ()
    | One None, _ => ()
    | _, One None => ()
    | _, _ => ()
    end.

  Succeed Ltac2 test x :=
    match x with
    | Nil, _ => ()
    | _, Nil => ()
    | One _, _ => ()
    | _, One _ => ()
    | Cons _ _, _ => ()
    | _, Cons _ _ => ()
    end.
End DeepType.

Module As.
  Ltac2 option_flat x :=
    match x with
    | Some (Some _ as v) => v
    | Some None | None => None
    end.

  (* this checks that we didn't parse the pattern as "Some (Some (_ as v))" *)
  Ltac2 Eval option_flat (Some (Some 0)).
End As.

Module Record.

  Ltac2 bang x := match x with { contents := v } => v end.

  Ltac2 Type exn ::= [ Regression_Test_Failure ].

  Ltac2 check_eq_int a b :=
    if Int.equal a b then () else Control.throw Regression_Test_Failure .

  Print Ltac2 bang.

  Ltac2 Eval
        let r := { contents := 0 } in
        r.(contents) := 1;
        check_eq_int (bang r) 1.

  Fail Ltac2 Eval
       let r := { contents := 0 } in
       r.(contents) := 1;
       check_eq_int (bang r) 0.

  Ltac2 Type foo := { a : int; b : int }.

  Ltac2 bar x := match x with { a := a } => a end.

End Record.

Module Atom.

  Fail Ltac2 mix_atoms x :=
    match x with
    | 0 | "" => false
    | _ => true
    end.

  Ltac2 match_int x :=
    match x with
    | 0 => false
    | _ => true
    end.
  Fail Ltac2 dummy : (int * int) -> _ := match_int.

  Ltac2 match_str x :=
    match x with
    | "" => false
    | _ => true
    end.
  Fail Ltac2 dummy : int -> _ := match_str.

End Atom.
