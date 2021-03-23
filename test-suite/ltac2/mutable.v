Require Import Ltac2.Ltac2.

Ltac2 mutable foo () := 0.

Ltac2 Eval
  Set foo := (fun () => 42);
  if Int.equal (foo ()) 42 then () else Control.throw Not_found.

(* Check that the effect does not persist *)
Ltac2 Eval
  if Int.equal (foo ()) 0 then () else Control.throw Not_found.

(* Closures capturing a mutable definition return the last bound value *)
Ltac2 Eval
  Set foo := (fun () => 42);
  let bar () := foo () in
  Set foo := (fun () => 18);
  if Int.equal (bar ()) 18 then () else Control.throw Not_found.

(* Replacement is syntax-directed *)

Fail Ltac2 qux () :=
  let bar := foo in
  Set bar := (fun () => 0).

Fail Ltac2 qux () :=
  let bar () := foo () in
  Set bar := (fun () => 0).

Ltac2 foo' () := 0.

Fail Ltac2 qux () := Set foo' := (fun () => 0).

(* Polymorphic replacement not supported yet. *)
Ltac2 mutable bar x := x.
Fail Ltac2 qux () := Set bar := (fun () => 42).
