(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Ltac2.Init.
Require Ltac2.Control Ltac2.Std.

Ltac2 Notation "intros" p(intropatterns) := Std.intros p.

Ltac2 Notation "eintros" p(intropatterns) := Std.eintros p.

Ltac2 Notation "split" bnd(thunk(bindings)) :=
  Control.with_holes bnd (fun bnd => Std.split bnd).

Ltac2 Notation "esplit" bnd(bindings) := Std.esplit bnd.

Ltac2 Notation "left" bnd(thunk(bindings)) :=
  Control.with_holes bnd (fun bnd => Std.left bnd).

Ltac2 Notation "eleft" bnd(bindings) := Std.eleft bnd.

Ltac2 Notation "right" bnd(thunk(bindings)) :=
  Control.with_holes bnd (fun bnd => Std.right bnd).

Ltac2 Notation "eright" bnd(bindings) := Std.eright bnd.

Ltac2 Notation "constructor" := Std.constructor ().
Ltac2 Notation "constructor" n(tactic) bnd(thunk(bindings)) :=
  Control.with_holes bnd (fun bnd => Std.constructor_n n bnd).

Ltac2 Notation "econstructor" := Std.econstructor ().
Ltac2 Notation "econstructor" n(tactic) bnd(bindings) :=
  Std.econstructor_n n bnd.

Ltac2 eelim c bnd use :=
    let use := match use with
    | None => None
    | Some u =>
      let ((_, c, wth)) := u in Some (c, wth)
    end in
  Std.eelim (c, bnd) use.

Ltac2 elim c bnd use :=
  Control.with_holes
    (fun () => c (), bnd (), use ())
    (fun ((c, bnd, use)) =>
      let use := match use with
      | None => None
      | Some u =>
        let ((_, c, wth)) := u in Some (c, wth)
      end in
    Std.elim (c, bnd) use).

Ltac2 Notation "elim" c(thunk(constr)) bnd(thunk(bindings))
  use(thunk(opt(seq("using", constr, bindings)))) := elim c bnd use.

Ltac2 Notation "eelim" c(constr) bnd(bindings)
  use(opt(seq("using", constr, bindings))) :=
  eelim c bnd use.
