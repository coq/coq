(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Ltac2.Init.
Require Ltac2.Control Ltac2.Int Ltac2.Std.

(** Tacticals *)

Ltac2 orelse t f :=
match Control.case t with
| Err e => f e
| Val ans =>
  let ((x, k)) := ans in
  Control.plus (fun _ => x) k
end.

Ltac2 ifcatch t s f :=
match Control.case t with
| Err e => f e
| Val ans =>
  let ((x, k)) := ans in
  Control.plus (fun _ => s x) (fun e => s (k e))
end.

Ltac2 fail0 (_ : unit) := Control.zero Tactic_failure.

Ltac2 Notation fail := fail0 ().

Ltac2 try0 t := Control.enter (fun _ => orelse t (fun _ => ())).

Ltac2 Notation try := try0.

Ltac2 rec repeat0 (t : unit -> unit) :=
  Control.enter (fun () =>
    ifcatch (fun _ => Control.progress t)
      (fun _ => Control.check_interrupt (); repeat0 t) (fun _ => ())).

Ltac2 Notation repeat := repeat0.

Ltac2 dispatch0 t ((head, tail)) :=
  match tail with
  | None => Control.enter (fun _ => t (); Control.dispatch head)
  | Some tacs =>
    let ((def, rem)) := tacs in
    Control.enter (fun _ => t (); Control.extend head def rem)
  end.

Ltac2 Notation t(thunk(self)) ">" "[" l(dispatch) "]" : 4 := dispatch0 t l.

Ltac2 do0 n t :=
  let rec aux n t := match Int.equal n 0 with
  | true => ()
  | false => t (); aux (Int.sub n 1) t
  end in
  aux (n ()) t.

Ltac2 Notation do := do0.

Ltac2 Notation once := Control.once.

Ltac2 progress0 tac := Control.enter (fun _ => Control.progress tac).

Ltac2 Notation progress := progress0.

Ltac2 rec first0 tacs :=
match tacs with
| [] => Control.zero Tactic_failure
| tac :: tacs => Control.enter (fun _ => orelse tac (fun _ => first0 tacs))
end.

Ltac2 Notation "first" "[" tacs(list0(thunk(tactic(6)), "|")) "]" := first0 tacs.

Ltac2 complete tac :=
  let ans := tac () in
  Control.enter (fun () => Control.zero Tactic_failure);
  ans.

Ltac2 rec solve0 tacs :=
match tacs with
| [] => Control.zero Tactic_failure
| tac :: tacs =>
  Control.enter (fun _ => orelse (fun _ => complete tac) (fun _ => first0 tacs))
end.

Ltac2 Notation "solve" "[" tacs(list0(thunk(tactic(6)), "|")) "]" := solve0 tacs.

Ltac2 time0 tac := Control.time None tac.

Ltac2 Notation time := time0.

Ltac2 abstract0 tac := Control.abstract None tac.

Ltac2 Notation abstract := abstract0.

(** Base tactics *)

(** Note that we redeclare notations that can be parsed as mere identifiers
    as abbreviations, so that it allows to parse them as function arguments
    without having to write them within parentheses. *)

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
Ltac2 Notation intros := intros.

Ltac2 Notation "eintros" p(intropatterns) := intros0 true p.
Ltac2 Notation eintros := eintros.

Ltac2 split0 ev bnd :=
  enter_h ev Std.split bnd.

Ltac2 Notation "split" bnd(thunk(bindings)) := split0 false bnd.
Ltac2 Notation split := split.

Ltac2 Notation "esplit" bnd(thunk(bindings)) := split0 true bnd.
Ltac2 Notation esplit := esplit.

Ltac2 left0 ev bnd := enter_h ev Std.left bnd.

Ltac2 Notation "left" bnd(thunk(bindings)) := left0 false bnd.
Ltac2 Notation left := left.

Ltac2 Notation "eleft" bnd(thunk(bindings)) := left0 true bnd.
Ltac2 Notation eleft := eleft.

Ltac2 right0 ev bnd := enter_h ev Std.right bnd.

Ltac2 Notation "right" bnd(thunk(bindings)) := right0 false bnd.
Ltac2 Notation right := right.

Ltac2 Notation "eright" bnd(thunk(bindings)) := right0 true bnd.
Ltac2 Notation eright := eright.

Ltac2 constructor0 ev n bnd :=
  enter_h ev (fun ev bnd => Std.constructor_n ev n bnd) bnd.

Ltac2 Notation "constructor" := Control.enter (fun () => Std.constructor false).
Ltac2 Notation constructor := constructor.
Ltac2 Notation "constructor" n(tactic) bnd(thunk(bindings)) := constructor0 false n bnd.

Ltac2 Notation "econstructor" := Control.enter (fun () => Std.constructor true).
Ltac2 Notation econstructor := econstructor.
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

Ltac2 induction0 ev ic use :=
  let f ev use :=
    let use := match use with
    | None => None
    | Some u =>
      let ((_, c, wth)) := u in Some (c, wth)
    end in
    Std.induction ev ic use
  in
  enter_h ev f use.

Ltac2 Notation "induction"
  ic(list1(induction_clause, ","))
  use(thunk(opt(seq("using", constr, bindings)))) :=
  induction0 false ic use.

Ltac2 Notation "einduction"
  ic(list1(induction_clause, ","))
  use(thunk(opt(seq("using", constr, bindings)))) :=
  induction0 true ic use.

Ltac2 destruct0 ev ic use :=
  let f ev use :=
    let use := match use with
    | None => None
    | Some u =>
      let ((_, c, wth)) := u in Some (c, wth)
    end in
    Std.destruct ev ic use
  in
  enter_h ev f use.

Ltac2 Notation "destruct"
  ic(list1(induction_clause, ","))
  use(thunk(opt(seq("using", constr, bindings)))) :=
  destruct0 false ic use.

Ltac2 Notation "edestruct"
  ic(list1(induction_clause, ","))
  use(thunk(opt(seq("using", constr, bindings)))) :=
  destruct0 true ic use.

Ltac2 default_on_concl cl :=
match cl with
| None => { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences }
| Some cl => cl
end.

Ltac2 Notation "red" cl(opt(clause)) :=
  Std.red (default_on_concl cl).
Ltac2 Notation red := red.

Ltac2 Notation "hnf" cl(opt(clause)) :=
  Std.hnf (default_on_concl cl).
Ltac2 Notation hnf := hnf.

Ltac2 Notation "vm_compute" pl(opt(seq(pattern, occurrences))) cl(opt(clause)) :=
  Std.vm pl (default_on_concl cl).
Ltac2 Notation vm_compute := vm_compute.

Ltac2 Notation "native_compute" pl(opt(seq(pattern, occurrences))) cl(opt(clause)) :=
  Std.native pl (default_on_concl cl).
Ltac2 Notation native_compute := native_compute.

Ltac2 fold0 pl cl :=
  let cl := default_on_concl cl in
  Control.enter (fun () => Control.with_holes pl (fun pl => Std.fold pl cl)).

Ltac2 Notation "fold" pl(thunk(list1(open_constr))) cl(opt(clause)) :=
  fold0 pl cl.

Ltac2 Notation "pattern" pl(list1(seq(constr, occurrences), ",")) cl(opt(clause)) :=
  Std.pattern pl (default_on_concl cl).

Ltac2 rewrite0 ev rw cl tac :=
  let tac := match tac with
  | None => None
  | Some p =>
    let ((_, tac)) := p in
    Some tac
  end in
  let cl := default_on_concl cl in
  Std.rewrite ev rw cl tac.

Ltac2 Notation "rewrite"
  rw(list1(rewriting, ","))
  cl(opt(clause))
  tac(opt(seq("by", thunk(tactic)))) :=
  rewrite0 false rw cl tac.

Ltac2 Notation "erewrite"
  rw(list1(rewriting, ","))
  cl(opt(clause))
  tac(opt(seq("by", thunk(tactic)))) :=
  rewrite0 true rw cl tac.

(** Other base tactics *)

Ltac2 Notation reflexivity := Std.reflexivity ().

Ltac2 Notation assumption := Std.assumption ().

Ltac2 Notation etransitivity := Std.etransitivity ().

Ltac2 Notation admit := Std.admit ().

Ltac2 Notation clear := Std.keep [].

Ltac2 Notation refine := Control.refine.
