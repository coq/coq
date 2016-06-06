Ltac force_clear :=
  clear;
  repeat match goal with
         | [ H : _ |- _ ] => clear H
         | [ H := _ |- _ ] => clearbody H
         end.

Class abstract_term {T} (x : T) := by_abstract_term : T.
Hint Extern 0 (@abstract_term ?T ?x) => force_clear; change T; abstract (exact x) : typeclass_instances.

Goal True.
(* These work: *)
  let term := constr:(I) in
  let T := type of term in
  let x := constr:((_ : abstract_term term) : T) in
  pose x.
  let term := constr:(I) in
  let T := type of term in
  let x := constr:((_ : abstract_term term) : T) in
  let x := (eval cbv iota in (let v : T := x in v)) in
  pose x.
  let term := constr:(I) in
  let T := type of term in
  let x := constr:((_ : abstract_term term) : T) in
  let x := match constr:(Set) with ?y => constr:(y) end in
  pose x.
(* This fails with an error: *)
  Fail let term := constr:(I) in
  let T := type of term in
  let x := constr:((_ : abstract_term term) : T) in
  let x := match constr:(x) with ?y => constr:(y) end in
  pose x. (* The command has indeed failed with message:
Error: Variable y should be bound to a term. *)
(* And the rest fail with Anomaly: Uncaught exception Not_found. Please report. *)
  Fail let term := constr:(I) in
  let T := type of term in
  let x := constr:((_ : abstract_term term) : T) in
  let x := match constr:(x) with ?y => y end in
  pose x.
  Fail let term := constr:(I) in
  let T := type of term in
  let x := constr:((_ : abstract_term term) : T) in
  let x := (eval cbv iota in x) in
  pose x.
  Fail let term := constr:(I) in
  let T := type of term in
  let x := constr:((_ : abstract_term term) : T) in
  let x := type of x in
  pose x. (* should succeed *)
  Fail let term := constr:(I) in
  let T := type of term in
  let x := constr:(_ : abstract_term term) in
  let x := type of x in
  pose x. (* should succeed *)

(*Apparently what [cbv iota] doesn't see can't hurt it, and [pose] is perfectly happy with abstracted lemmas only some of the time.

Even stranger, consider:*)
  let term := constr:(I) in
  let T := type of term in
  let x := constr:((_ : abstract_term term) : T) in
  let y := (eval cbv iota in (let v : T := x in v)) in
  pose y;
    let x' := fresh "x'" in
    pose x as x'.
      let x := (eval cbv delta [x'] in x') in
      pose x;
      let z := (eval cbv iota in x) in
      pose z.

(*This works fine.  But if I change the period to a semicolon, I get:*)

      Fail let term := constr:(I) in
  let T := type of term in
  let x := constr:((_ : abstract_term term) : T) in
  let y := (eval cbv iota in (let v : T := x in v)) in
  pose y;
    let x' := fresh "x'" in
    pose x as x';
      let x := (eval cbv delta [x'] in x') in
      pose x. (* Anomaly: Uncaught exception Not_found. Please report. *)
 (* should succeed *)
(*and if I use the second one instead of [pose x] (note that using [idtac] works fine), I get:*)

 Fail  let term := constr:(I) in
  let T := type of term in
  let x := constr:((_ : abstract_term term) : T) in
  let y := (eval cbv iota in (let v : T := x in v)) in
  pose y;
    let x' := fresh "x'" in
    pose x as x';
      let x := (eval cbv delta [x'] in x') in
      let z := (eval cbv iota in x) in (* Error: Variable x should be bound to a term. *)
      idtac. (* should succeed *)
