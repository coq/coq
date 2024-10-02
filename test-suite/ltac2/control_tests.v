Require Import Ltac2.Ltac2.

(** Basic tests for external APIs from Ltac2.Control *)

Import Ltac2.Control.
Import Ltac2.Ref.

Ltac2 Type exn ::= [ Error ].

Fail Ltac2 Eval throw Error.
Fail Ltac2 Eval plus_bt (fun _ => zero Error) throw_bt.
Fail Ltac2 Eval plus_bt (fun _ => zero Error) zero_bt.
Ltac2 Eval plus_bt (fun _ => ()) throw_bt.
Ltac2 Eval plus_bt (fun _ => ()) zero_bt.

Fail Ltac2 Eval zero Error.

Fail Ltac2 Eval plus (fun () => throw Error) (fun _ => ()).

Ltac2 Eval plus (fun () => zero Error) (fun _ => ()).
Ltac2 Eval plus_bt (fun () => zero Error) (fun _ _ => ()).

Fail Ltac2 Eval case (fun () => throw Error).

Ltac2 Eval match case (fun () => zero Error) with
  | Val _ => throw Error
  | Err Error => ()
  | Err _ => throw Error
  end.

Ltac2 Eval
  let n := plus (fun () => 1) (fun _ => 2) in
  if Int.equal n 1 then zero Error else ().

Fail Ltac2 Eval
  match case (fun () => plus (fun () => 1) (fun _ => 2)) with
  | Val (n,k) =>
      if Int.equal n 1 then zero Error else ()
  | Err _ => throw Error
  end.

Ltac2 Eval
  match case (fun () => plus (fun () => 1) (fun _ => 2)) with
  | Val (n,k) =>
      if Int.equal n 1 then k Error else throw Error
  | Err _ => throw Error
  end.

Ltac2 Eval once (fun () => 1).

Fail Ltac2 Eval
  let n := once (fun () => plus (fun () => 1) (fun _ => 2)) in
  if Int.equal n 1 then zero Error else ().

Ltac2 Eval
  if Int.equal (numgoals()) 0 then () else throw Error.

Goal True /\ True.
  if Int.equal (numgoals()) 1 then () else throw Error.
  split.
  if Int.equal (numgoals()) 1 then () else throw Error.
  all:if Int.equal (numgoals()) 2 then () else throw Error.
  all:shelve ().
  all:if Int.equal (numgoals()) 0 then () else throw Error.
Abort.

Goal tt = tt /\ 2 = 2 /\ True /\ True /\ true = true.
  repeat (match! goal with [ |- _ /\ _ ] => split end).

  Fail all: dispatch [].
  Fail all: dispatch [fun _ => ()].
  1,2: dispatch [(fun _ => ()); (fun _ => exact (eq_refl 2))].
  all: extend [fun _ => exact (eq_refl tt)] (fun _ => exact I) [fun _ => ()].

  exact (eq_refl true).

  all: if Int.equal (numgoals()) 0 then () else throw Error.

  all: extend [] (fun _ => ()) [].
  Fail all: extend [fun _ => ()] (fun _ => ()) [].
Qed.

Goal True /\ False.
  split.
  let r := ref 0 in
  enter (fun () =>
           if Int.equal (get r) 0 then incr r; exact I
           else ()).
  all: if Int.equal (numgoals()) 1 then () else throw Error.
Abort.

Goal 1 = 1 /\ 2 = 2 /\ 3 = 3.
  repeat (match! goal with [ |- _ /\ _ ] => split end).
  all:focus 2 3 (fun () => enter (fun () => plus (fun () => exact (eq_refl 2)) (fun _ => exact (eq_refl 3)))).
  Fail focus 2 3 (fun _ => ()).

  shelve ().
  all: if Int.equal (numgoals()) 0 then () else throw Error.
Abort.

Goal exists n, n = 0.
  shelve_unifiable ().
  Notations.unshelve eexists.
  all:shelve_unifiable ().
  all: if Int.equal (numgoals()) 1 then () else throw Error.
  exact (eq_refl 0).
Qed.

Goal True.
  let c := '(_ :> nat) in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Evar ev _ => new_goal ev
  | _ => throw Error
  end.
  exact I.
  exact 0.
Qed.

Goal True.
  Fail progress (fun () => ()).
  progress (fun () => exact I).
Abort.

Goal 3 = 3 -> 1 = 1 /\ 2 = 2.
  intros H.
  split.
  Fail all: let _ := goal () in ().
  Fail all: let _ := hyps () in ().
  Fail all: let _ := hyp @H in ().

  reflexivity.

  if Constr.equal (goal()) '(2 = 2) then () else throw Error.
  if Constr.equal (hyp @H) '&H then () else throw Error.
  Fail let _ := hyp @X in ().
  pose (X := 2).
  if Constr.equal (hyp @X) '&X then () else throw Error.

  if Option.equal Constr.equal (hyp_value @H) None then () else throw Error.
  if Option.equal Constr.equal (hyp_value @X) (Some '2) then () else throw Error.

  Ltac2 Eval hyps().
  match hyps () with
  | [ (h, None, hty); (x, Some xbdy, xty) ] =>
      if Ident.equal h @H then () else throw Error;
      if Constr.equal hty '(3 = 3) then () else throw Error;
      if Ident.equal x @X then () else throw Error;
      if Constr.equal xbdy '2 then () else throw Error;
      if Constr.equal xty 'nat then () else throw Error
  | _ => throw Error
  end.

  refine (fun () => '(eq_refl &X)).
Qed.

Goal True.
  with_holes (fun _ => ()) (fun () => ()).
  Fail with_holes (fun _ => '_) (fun _ => ()).
  with_holes (fun _ => '_) (fun c => unify $c I).
Abort.

Ltac2 Eval time (Some "time") (fun () => ()).

Goal True.
  abstract (Some @subproof) (fun () => exact I).
Qed.

Ltac2 Eval check_interrupt ().

Ltac2 Eval
  match case (fun () => '(1 + tt)) with
  | Err (Internal e) =>
      let _ := clear_err_info e in ()
  | _ => throw Error
  end.

Ltac2 Eval timeout 1 (fun () => ()).

(* I don't think we can currently get values of type float
   without going through constr primitive floats (no ltac2 parsing for float literals)
   so skipping testing for timeoutf *)
