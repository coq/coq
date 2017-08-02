(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Ltac2.Init.
Require Ltac2.Control Ltac2.Std.

(** Enter and check evar resolution *)
Ltac2 enter_h ev f arg :=
match ev with
| true => Control.enter (fun () => f ev (arg ()))
| false =>
  Control.enter (fun () =>
    Control.with_holes arg (fun x => f ev x))
end.

Ltac2 intros0 ev p :=
  Control.enter (fun () => Std.intros false p).

Ltac2 Notation "intros" p(intropatterns) := intros0 false p.

Ltac2 Notation "eintros" p(intropatterns) := intros0 true p.

Ltac2 split0 ev bnd :=
  enter_h ev Std.split bnd.

Ltac2 Notation "split" bnd(thunk(bindings)) := split0 false bnd.

Ltac2 Notation "esplit" bnd(thunk(bindings)) := split0 true bnd.

Ltac2 left0 ev bnd := enter_h ev Std.left bnd.

Ltac2 Notation "left" bnd(thunk(bindings)) := left0 false bnd.

Ltac2 Notation "eleft" bnd(thunk(bindings)) := left0 true bnd.

Ltac2 right0 ev bnd := enter_h ev Std.right bnd.

Ltac2 Notation "right" bnd(thunk(bindings)) := right0 false bnd.

Ltac2 Notation "eright" bnd(thunk(bindings)) := right0 true bnd.

Ltac2 constructor0 ev n bnd :=
  enter_h ev (fun ev bnd => Std.constructor_n ev n bnd) bnd.

Ltac2 Notation "constructor" := Control.enter (fun () => Std.constructor false).
Ltac2 Notation "constructor" n(tactic) bnd(thunk(bindings)) := constructor0 false n bnd.

Ltac2 Notation "econstructor" := Control.enter (fun () => Std.constructor true).
Ltac2 Notation "econstructor" n(tactic) bnd(thunk(bindings)) := constructor0 true n bnd.

Ltac2 elim0 ev c bnd use :=
  let f ev ((c, bnd, use)) :=
    let use := match use with
    | None => None
    | Some u =>
      let ((_, c, wth)) := u in Some (c, wth)
    end in
    Std.elim ev (c, bnd) use
  in
  enter_h ev f (fun () => c (), bnd (), use ()).

Ltac2 Notation "elim" c(thunk(constr)) bnd(thunk(bindings))
  use(thunk(opt(seq("using", constr, bindings)))) :=
  elim0 false c bnd use.

Ltac2 Notation "eelim" c(thunk(constr)) bnd(thunk(bindings))
  use(thunk(opt(seq("using", constr, bindings)))) :=
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
