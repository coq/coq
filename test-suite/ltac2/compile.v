Require Import Ltac2.Ltac2.
Import Ltac2.Printf.

Module ThunkSet.
  (* checks that "r.(contents) := 1" gets thunked appropriately
     together with the access to the value *)

  Ltac2 foo () :=
    let r := { contents := 0 } in
    let r := (); r.(contents) with _ := r.(contents) := 1 in
    r.

  Ltac2 foo' () :=
    let r := { contents := 0 } in
    let r := r.(contents) with _ := r.(contents) := 1 in
    r.

  Ltac2 bar () :=
    let r := { contents := 0 } in
    let _ := r.(contents) := 1 with r := r.(contents) in
    r.

  Ltac2 Eval if Int.equal (foo ()) 0 then () else Control.throw Assertion_failure.
  Ltac2 Eval if Int.equal (foo' ()) 0 then () else Control.throw Assertion_failure.
  Ltac2 Eval if Int.equal (bar ()) 1 then () else Control.throw Assertion_failure.

  Ltac2 Compile foo foo' bar.

  Ltac2 Eval if Int.equal (foo ()) 0 then () else Control.throw Assertion_failure.
  Ltac2 Eval if Int.equal (foo' ()) 0 then () else Control.throw Assertion_failure.
  Ltac2 Eval if Int.equal (bar ()) 1 then () else Control.throw Assertion_failure.
End ThunkSet.

Module StringPat.

  Ltac2 foo1 x :=
    match x with
    | ("s", _) | (_, "s") => true
    | _ => false
    end.

  Ltac2 foo2 x :=
    match x with
    | ("s", "") | (_, "s") => true
    | _ => false
    end.

  Ltac2 foo3 x :=
    match x with
    | ("s", "s") => true
    | _ => false
    end.

  Ltac2 foo4 x :=
    match x with
    | ("s", "s") | ("", "s") | ("s", "") => true
    | _ => false
    end.

  Ltac2 foo5 x :=
    match x with
    | ("s", "s") | ("", "s") | ("s", "x") => true
    | _ => false
    end.

  Ltac2 foo6 x :=
    match x with
    | (("s" | "x"), ("x" | "s")) => true
    | _ => false
    end.

  Import Bool.BoolNotations.

  Ltac2 check_true fn f x y :=
    if f (x, y) then ()
    else Control.throw (Tactic_failure (Some (fprintf "%s (""%s"", ""%s"") = false!" fn x y))).

  Ltac2 check_false fn f x y :=
    if f (x, y) then Control.throw (Tactic_failure (Some (fprintf "%s (""%s"", ""%s"") = true!" fn x y)))
    else ().

  Ltac2 check (fn,f,(b,x,y)) := if b then check_true fn f x y else check_false fn f x y.

  Ltac2 check_foo1 () :=
    List.iter check
    (List.map (fun x => ("foo1", foo1, x))
       [(true, "s", ""); (true, "", "s"); (true, "s", "s"); (false, "", "")]).

  Ltac2 check_foo2 () :=
    List.iter check
    (List.map (fun x => ("foo2", foo2, x))
       [(true, "s", ""); (true, "", "s"); (true, "x", "s");
        (false, "s", "x"); (false, "", "")]).

  Ltac2 check_foo3 () :=
    List.iter check
    (List.map (fun x => ("foo3", foo3, x))
       [(true, "s", "s"); (false, "", ""); (false, "s", ""); (false, "", "s"); (false, "ss", "ss")]).

  Ltac2 check_foo4 () :=
    List.iter check
    (List.map (fun x => ("foo4", foo4, x))
       [(true, "s", "s"); (true, "", "s"); (true, "s", "");
        (false, "", ""); (false, "x", "x"); (false, "s", "x")]).

  Ltac2 check_foo5 () :=
    List.iter check
    (List.map (fun x => ("foo5", foo5, x))
       [(true, "s", "s"); (true, "", "s"); (true, "s", "x");
        (false, "", ""); (false, "x", "s"); (false, "s", ""); (false, "x", "x")]).

  Ltac2 check_foo6 () :=
    List.iter check
    (List.map (fun x => ("foo6", foo6, x))
       [(true, "s", "x"); (true, "x", "s"); (true, "x", "x"); (true, "s", "s");
        (false, "", "s"); (false, "ss", "x"); (false, "", "")]).

  Ltac2 check_all () :=
    check_foo1 (); check_foo2 (); check_foo3 ();
    check_foo4 (); check_foo5 (); check_foo6 ().

  Ltac2 Eval check_all().

  Ltac2 Compile foo1 foo2 foo3 foo4 foo5 foo6.

  Ltac2 Eval check_all().

End StringPat.

Module Constr.

  Ltac2 foo x y z :=
    let a := constr:($x + ltac:(exact $y)) in
    constr:($a + ltac2:(let y := z in exact $y)).

  Ltac2 Compile foo.

  Ltac2 Eval
    if Constr.equal
         (foo constr:(0) constr:(1) constr:(2))
         constr:(0 + 1 + 2)
    then ()
    else Control.throw Assertion_failure.

End Constr.

Module Open.

  Ltac2 foo e :=
    match e with
    | Not_found => Control.throw Assertion_failure
    | Invalid_argument x => Control.zero (Invalid_argument x)
    | _ => ()
    end.

  Ltac2 Compile foo.

  Ltac2 Eval foo Assertion_failure.

  Fail Ltac2 Eval foo Not_found.

  Ltac2 Eval Control.plus (fun () => foo (Invalid_argument None))
    (fun e =>
       match e with
       | Invalid_argument None => ()
       | _ => Control.throw Assertion_failure
       end).

End Open.

Module MatchGoal.
  (* match goal exercises a variety of functionalities *)

  Ltac2 Type exn ::= [ Nope ].

  Ltac2 check_constr x y :=
    match Constr.equal x y with
    | true => ()
    | false => Control.throw Nope
    end.

  Ltac2 check_id id id' :=
    match Ident.equal id id' with
    | true => ()
    | false => Control.throw Nope
    end.

  Ltac2 check () :=
    lazy_match! goal with
    | [ h1 : context c1 [ ?t1 ] , h2 := context c2 [ Nat.add ?v2 ] , h3 : context c3 [ ?t2 ] |- _ ] =>
        check_constr t1 'bool;
        check_constr v2 '0;
        check_constr t2 'bool;
        check_constr (Pattern.instantiate c1 'Empty_set) 'Empty_set;
        check_constr (Pattern.instantiate c2 '(Nat.add 1)) '(1 + 0);
        check_constr (Pattern.instantiate c3 'unit) 'unit
    end.

  Ltac2 Compile check.

  Goal forall (i j : unit) (x y : nat) (b : bool), True.
  Proof.
    intros i j x y b.
    pose (def1 := 0 + 0).
    pose (def2 := true).
    check().
  Abort.

End MatchGoal.
