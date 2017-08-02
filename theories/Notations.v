(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Ltac2.Init.
Require Ltac2.Control Ltac2.Std.

Ltac2 Notation "intros" p(intropatterns) := Std.intros false p.

Ltac2 Notation "eintros" p(intropatterns) := Std.intros true p.

Ltac2 Notation "split" bnd(thunk(bindings)) :=
  Control.with_holes bnd (fun bnd => Std.split false bnd).

Ltac2 Notation "esplit" bnd(bindings) := Std.split true bnd.

Ltac2 Notation "left" bnd(thunk(bindings)) :=
  Control.with_holes bnd (fun bnd => Std.left false bnd).

Ltac2 Notation "eleft" bnd(bindings) := Std.left true bnd.

Ltac2 Notation "right" bnd(thunk(bindings)) :=
  Control.with_holes bnd (fun bnd => Std.right false bnd).

Ltac2 Notation "eright" bnd(bindings) := Std.right true bnd.

Ltac2 Notation "constructor" := Std.constructor false.
Ltac2 Notation "constructor" n(tactic) bnd(thunk(bindings)) :=
  Control.with_holes bnd (fun bnd => Std.constructor_n false n bnd).

Ltac2 Notation "econstructor" := Std.constructor true.
Ltac2 Notation "econstructor" n(tactic) bnd(bindings) :=
  Std.constructor_n true n bnd.

Ltac2 elim0 ev c bnd use :=
  let use := match use with
  | None => None
  | Some u =>
    let ((_, c, wth)) := u in Some (c, wth)
  end in
  Std.elim ev (c, bnd) use.

Ltac2 Notation "elim" c(thunk(constr)) bnd(thunk(bindings))
  use(thunk(opt(seq("using", constr, bindings)))) :=
  Control.with_holes
    (fun () => c (), bnd (), use ())
    (fun ((c, bnd, use)) => elim0 false c bnd use).

Ltac2 Notation "eelim" c(constr) bnd(bindings)
  use(opt(seq("using", constr, bindings))) :=
  elim0 true c bnd use.

Ltac2 apply0 adv ev cb cl :=
  let cl := match cl with
  | None => None
  | Some p =>
    let ((_, id, ipat)) := p in
    let p := match ipat with
    | None => None
    | Some p =>
      let ((_, ipat)) := p in
      Some ipat
    end in
    Some (id, p)
  end in
  Std.apply adv ev cb cl.

Ltac2 Notation "eapply"
  cb(list1(thunk(seq(constr, bindings)), ","))
  cl(opt(seq(keyword("in"), ident, opt(seq(keyword("as"), intropattern))))) :=
  apply0 true true cb cl.

Ltac2 Notation "apply"
  cb(list1(thunk(seq(constr, bindings)), ","))
  cl(opt(seq(keyword("in"), ident, opt(seq(keyword("as"), intropattern))))) :=
  apply0 true false cb cl.
