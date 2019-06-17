(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.
Require Ltac2.Control Ltac2.Pattern Ltac2.Array Ltac2.Int Ltac2.Std.

(** Constr matching *)

Ltac2 Notation "lazy_match!" t(tactic(6)) "with" m(constr_matching) "end" :=
  Pattern.lazy_match0 t m.

Ltac2 Notation "multi_match!" t(tactic(6)) "with" m(constr_matching) "end" :=
  Pattern.multi_match0 t m.

Ltac2 Notation "match!" t(tactic(6)) "with" m(constr_matching) "end" :=
  Pattern.one_match0 t m.

(** Goal matching *)

Ltac2 Notation "lazy_match!" "goal" "with" m(goal_matching) "end" :=
  Pattern.lazy_goal_match0 false m.

Ltac2 Notation "multi_match!" "goal" "with" m(goal_matching) "end" :=
  Pattern.multi_goal_match0 false m.

Ltac2 Notation "match!" "goal" "with" m(goal_matching) "end" :=
  Pattern.one_goal_match0 false m.

Ltac2 Notation "lazy_match!" "reverse" "goal" "with" m(goal_matching) "end" :=
  Pattern.lazy_goal_match0 true m.

Ltac2 Notation "multi_match!" "reverse" "goal" "with" m(goal_matching) "end" :=
  Pattern.multi_goal_match0 true m.

Ltac2 Notation "match!" "reverse" "goal" "with" m(goal_matching) "end" :=
  Pattern.one_goal_match0 true m.

(** Tacticals *)

Ltac2 orelse t f :=
match Control.case t with
| Err e => f e
| Val ans =>
  let (x, k) := ans in
  Control.plus (fun _ => x) k
end.

Ltac2 ifcatch t s f :=
match Control.case t with
| Err e => f e
| Val ans =>
  let (x, k) := ans in
  Control.plus (fun _ => s x) (fun e => s (k e))
end.

Ltac2 fail0 (_ : unit) := Control.enter (fun _ => Control.zero (Tactic_failure None)).

Ltac2 Notation fail := fail0 ().

Ltac2 try0 t := Control.enter (fun _ => orelse t (fun _ => ())).

Ltac2 Notation try := try0.

Ltac2 rec repeat0 (t : unit -> unit) :=
  Control.enter (fun () =>
    ifcatch (fun _ => Control.progress t)
      (fun _ => Control.check_interrupt (); repeat0 t) (fun _ => ())).

Ltac2 Notation repeat := repeat0.

Ltac2 dispatch0 t (head, tail) :=
  match tail with
  | None => Control.enter (fun _ => t (); Control.dispatch head)
  | Some tacs =>
    let (def, rem) := tacs in
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
| [] => Control.zero (Tactic_failure None)
| tac :: tacs => Control.enter (fun _ => orelse tac (fun _ => first0 tacs))
end.

Ltac2 Notation "first" "[" tacs(list0(thunk(tactic(6)), "|")) "]" := first0 tacs.

Ltac2 complete tac :=
  let ans := tac () in
  Control.enter (fun () => Control.zero (Tactic_failure None));
  ans.

Ltac2 rec solve0 tacs :=
match tacs with
| [] => Control.zero (Tactic_failure None)
| tac :: tacs =>
  Control.enter (fun _ => orelse (fun _ => complete tac) (fun _ => solve0 tacs))
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

Ltac2 Notation "split" bnd(thunk(with_bindings)) := split0 false bnd.
Ltac2 Notation split := split.

Ltac2 Notation "esplit" bnd(thunk(with_bindings)) := split0 true bnd.
Ltac2 Notation esplit := esplit.

Ltac2 exists0 ev bnds := match bnds with
| [] => split0 ev (fun () => Std.NoBindings)
| _ =>
  let rec aux bnds := match bnds with
  | [] => ()
  | bnd :: bnds => split0 ev bnd; aux bnds
  end in
  aux bnds
end.

Ltac2 Notation "exists" bnd(list0(thunk(bindings), ",")) := exists0 false bnd.
(* Ltac2 Notation exists := exists. *)

Ltac2 Notation "eexists" bnd(list0(thunk(bindings), ",")) := exists0 true bnd.
Ltac2 Notation eexists := eexists.

Ltac2 left0 ev bnd := enter_h ev Std.left bnd.

Ltac2 Notation "left" bnd(thunk(with_bindings)) := left0 false bnd.
Ltac2 Notation left := left.

Ltac2 Notation "eleft" bnd(thunk(with_bindings)) := left0 true bnd.
Ltac2 Notation eleft := eleft.

Ltac2 right0 ev bnd := enter_h ev Std.right bnd.

Ltac2 Notation "right" bnd(thunk(with_bindings)) := right0 false bnd.
Ltac2 Notation right := right.

Ltac2 Notation "eright" bnd(thunk(with_bindings)) := right0 true bnd.
Ltac2 Notation eright := eright.

Ltac2 constructor0 ev n bnd :=
  enter_h ev (fun ev bnd => Std.constructor_n ev n bnd) bnd.

Ltac2 Notation "constructor" := Control.enter (fun () => Std.constructor false).
Ltac2 Notation constructor := constructor.
Ltac2 Notation "constructor" n(tactic) bnd(thunk(with_bindings)) := constructor0 false n bnd.

Ltac2 Notation "econstructor" := Control.enter (fun () => Std.constructor true).
Ltac2 Notation econstructor := econstructor.
Ltac2 Notation "econstructor" n(tactic) bnd(thunk(with_bindings)) := constructor0 true n bnd.

Ltac2 specialize0 c pat :=
  enter_h false (fun _ c => Std.specialize c pat) c.

Ltac2 Notation "specialize" c(thunk(seq(constr, with_bindings))) ipat(opt(seq("as", intropattern))) :=
  specialize0 c ipat.

Ltac2 elim0 ev c bnd use :=
  let f ev (c, bnd, use) := Std.elim ev (c, bnd) use in
  enter_h ev f (fun () => c (), bnd (), use ()).

Ltac2 Notation "elim" c(thunk(constr)) bnd(thunk(with_bindings))
  use(thunk(opt(seq("using", constr, with_bindings)))) :=
  elim0 false c bnd use.

Ltac2 Notation "eelim" c(thunk(constr)) bnd(thunk(with_bindings))
  use(thunk(opt(seq("using", constr, with_bindings)))) :=
  elim0 true c bnd use.

Ltac2 apply0 adv ev cb cl :=
  Std.apply adv ev cb cl.

Ltac2 Notation "eapply"
  cb(list1(thunk(seq(constr, with_bindings)), ","))
  cl(opt(seq("in", ident, opt(seq("as", intropattern))))) :=
  apply0 true true cb cl.

Ltac2 Notation "apply"
  cb(list1(thunk(seq(constr, with_bindings)), ","))
  cl(opt(seq("in", ident, opt(seq("as", intropattern))))) :=
  apply0 true false cb cl.

Ltac2 default_on_concl cl :=
match cl with
| None => { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences }
| Some cl => cl
end.

Ltac2 pose0 ev p :=
  enter_h ev (fun ev (na, p) => Std.pose na p) p.

Ltac2 Notation "pose" p(thunk(pose)) :=
  pose0 false p.

Ltac2 Notation "epose" p(thunk(pose)) :=
  pose0 true p.

Ltac2 Notation "set" p(thunk(pose)) cl(opt(clause)) :=
  Std.set false p (default_on_concl cl).

Ltac2 Notation "eset" p(thunk(pose)) cl(opt(clause)) :=
  Std.set true p (default_on_concl cl).

Ltac2 assert0 ev ast :=
  enter_h ev (fun _ ast => Std.assert ast) ast.

Ltac2 Notation "assert" ast(thunk(assert)) := assert0 false ast.

Ltac2 Notation "eassert" ast(thunk(assert)) := assert0 true ast.

Ltac2 default_everywhere cl :=
match cl with
| None => { Std.on_hyps := None; Std.on_concl := Std.AllOccurrences }
| Some cl => cl
end.

Ltac2 Notation "remember"
  c(thunk(open_constr))
  na(opt(seq("as", ident)))
  pat(opt(seq("eqn", ":", intropattern)))
  cl(opt(clause)) :=
  Std.remember false na c pat (default_everywhere cl).

Ltac2 Notation "eremember"
  c(thunk(open_constr))
  na(opt(seq("as", ident)))
  pat(opt(seq("eqn", ":", intropattern)))
  cl(opt(clause)) :=
  Std.remember true na c pat (default_everywhere cl).

Ltac2 induction0 ev ic use :=
  let f ev use := Std.induction ev ic use in
  enter_h ev f use.

Ltac2 Notation "induction"
  ic(list1(induction_clause, ","))
  use(thunk(opt(seq("using", constr, with_bindings)))) :=
  induction0 false ic use.

Ltac2 Notation "einduction"
  ic(list1(induction_clause, ","))
  use(thunk(opt(seq("using", constr, with_bindings)))) :=
  induction0 true ic use.

Ltac2 generalize0 gen :=
  enter_h false (fun _ gen => Std.generalize gen) gen.

Ltac2 Notation "generalize"
  gen(thunk(list1(seq (open_constr, occurrences, opt(seq("as", ident))), ","))) :=
  generalize0 gen.

Ltac2 destruct0 ev ic use :=
  let f ev use := Std.destruct ev ic use in
  enter_h ev f use.

Ltac2 Notation "destruct"
  ic(list1(induction_clause, ","))
  use(thunk(opt(seq("using", constr, with_bindings)))) :=
  destruct0 false ic use.

Ltac2 Notation "edestruct"
  ic(list1(induction_clause, ","))
  use(thunk(opt(seq("using", constr, with_bindings)))) :=
  destruct0 true ic use.

Ltac2 Notation "simple" "inversion"
  arg(destruction_arg)
  pat(opt(seq("as", intropattern)))
  ids(opt(seq("in", list1(ident)))) :=
  Std.inversion Std.SimpleInversion arg pat ids.

Ltac2 Notation "inversion"
  arg(destruction_arg)
  pat(opt(seq("as", intropattern)))
  ids(opt(seq("in", list1(ident)))) :=
  Std.inversion Std.FullInversion arg pat ids.

Ltac2 Notation "inversion_clear"
  arg(destruction_arg)
  pat(opt(seq("as", intropattern)))
  ids(opt(seq("in", list1(ident)))) :=
  Std.inversion Std.FullInversionClear arg pat ids.

Ltac2 Notation "red" cl(opt(clause)) :=
  Std.red (default_on_concl cl).
Ltac2 Notation red := red.

Ltac2 Notation "hnf" cl(opt(clause)) :=
  Std.hnf (default_on_concl cl).
Ltac2 Notation hnf := hnf.

Ltac2 Notation "simpl" s(strategy) pl(opt(seq(pattern, occurrences))) cl(opt(clause)) :=
  Std.simpl s pl (default_on_concl cl).
Ltac2 Notation simpl := simpl.

Ltac2 Notation "cbv" s(strategy) cl(opt(clause)) :=
  Std.cbv s (default_on_concl cl).
Ltac2 Notation cbv := cbv.

Ltac2 Notation "cbn" s(strategy) cl(opt(clause)) :=
  Std.cbn s (default_on_concl cl).
Ltac2 Notation cbn := cbn.

Ltac2 Notation "lazy" s(strategy) cl(opt(clause)) :=
  Std.lazy s (default_on_concl cl).
Ltac2 Notation lazy := lazy.

Ltac2 Notation "unfold" pl(list1(seq(reference, occurrences), ",")) cl(opt(clause)) :=
  Std.unfold pl (default_on_concl cl).

Ltac2 fold0 pl cl :=
  let cl := default_on_concl cl in
  Control.enter (fun () => Control.with_holes pl (fun pl => Std.fold pl cl)).

Ltac2 Notation "fold" pl(thunk(list1(open_constr))) cl(opt(clause)) :=
  fold0 pl cl.

Ltac2 Notation "pattern" pl(list1(seq(constr, occurrences), ",")) cl(opt(clause)) :=
  Std.pattern pl (default_on_concl cl).

Ltac2 Notation "vm_compute" pl(opt(seq(pattern, occurrences))) cl(opt(clause)) :=
  Std.vm pl (default_on_concl cl).
Ltac2 Notation vm_compute := vm_compute.

Ltac2 Notation "native_compute" pl(opt(seq(pattern, occurrences))) cl(opt(clause)) :=
  Std.native pl (default_on_concl cl).
Ltac2 Notation native_compute := native_compute.

Ltac2 change0 p cl :=
  let (pat, c) := p in
  Std.change pat c (default_on_concl cl).

Ltac2 Notation "change" c(conversion) cl(opt(clause)) := change0 c cl.

Ltac2 rewrite0 ev rw cl tac :=
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

(** coretactics *)

Ltac2 exact0 ev c :=
  Control.enter (fun _ =>
    match ev with
    | true =>
      let c := c () in
      Control.refine (fun _ => c)
    | false =>
      Control.with_holes c (fun c => Control.refine (fun _ => c))
    end
  ).

Ltac2 Notation "exact" c(thunk(open_constr)) := exact0 false c.
Ltac2 Notation "eexact" c(thunk(open_constr)) := exact0 true c.

Ltac2 Notation "intro" id(opt(ident)) mv(opt(move_location)) := Std.intro id mv.
Ltac2 Notation intro := intro.

Ltac2 Notation "move" id(ident) mv(move_location) := Std.move id mv.

Ltac2 Notation reflexivity := Std.reflexivity ().

Ltac2 symmetry0 cl :=
  Std.symmetry (default_on_concl cl).

Ltac2 Notation "symmetry" cl(opt(clause)) := symmetry0 cl.
Ltac2 Notation symmetry := symmetry.

Ltac2 Notation "revert" ids(list1(ident)) := Std.revert ids.

Ltac2 Notation assumption := Std.assumption ().

Ltac2 Notation etransitivity := Std.etransitivity ().

Ltac2 Notation admit := Std.admit ().

Ltac2 clear0 ids := match ids with
| [] => Std.keep []
| _ => Std.clear ids
end.

Ltac2 Notation "clear" ids(list0(ident)) := clear0 ids.
Ltac2 Notation "clear" "-" ids(list1(ident)) := Std.keep ids.
Ltac2 Notation clear := clear.

Ltac2 Notation refine := Control.refine.

(** extratactics *)

Ltac2 absurd0 c := Control.enter (fun _ => Std.absurd (c ())).

Ltac2 Notation "absurd" c(thunk(open_constr)) := absurd0 c.

Ltac2 subst0 ids := match ids with
| [] => Std.subst_all ()
| _ => Std.subst ids
end.

Ltac2 Notation "subst" ids(list0(ident)) := subst0 ids.
Ltac2 Notation subst := subst.

Ltac2 Notation "discriminate" arg(opt(destruction_arg)) :=
  Std.discriminate false arg.
Ltac2 Notation discriminate := discriminate.

Ltac2 Notation "ediscriminate" arg(opt(destruction_arg)) :=
  Std.discriminate true arg.
Ltac2 Notation ediscriminate := ediscriminate.

Ltac2 Notation "injection" arg(opt(destruction_arg)) ipat(opt(seq("as", intropatterns))):=
  Std.injection false ipat arg.

Ltac2 Notation "einjection" arg(opt(destruction_arg)) ipat(opt(seq("as", intropatterns))):=
  Std.injection true ipat arg.

(** Auto *)

Ltac2 default_db dbs := match dbs with
| None => Some []
| Some dbs =>
  match dbs with
  | None => None
  | Some l => Some l
  end
end.

Ltac2 default_list use := match use with
| None => []
| Some use => use
end.

Ltac2 trivial0 use dbs :=
  let dbs := default_db dbs in
  let use := default_list use in
  Std.trivial Std.Off use dbs.

Ltac2 Notation "trivial"
  use(opt(seq("using", list1(thunk(constr), ","))))
  dbs(opt(seq("with", hintdb))) := trivial0 use dbs.

Ltac2 Notation trivial := trivial.

Ltac2 auto0 n use dbs :=
  let dbs := default_db dbs in
  let use := default_list use in
  Std.auto Std.Off n use dbs.

Ltac2 Notation "auto" n(opt(tactic(0)))
  use(opt(seq("using", list1(thunk(constr), ","))))
  dbs(opt(seq("with", hintdb))) := auto0 n use dbs.

Ltac2 Notation auto := auto.

Ltac2 new_eauto0 n use dbs :=
  let dbs := default_db dbs in
  let use := default_list use in
  Std.new_auto Std.Off n use dbs.

Ltac2 Notation "new" "auto" n(opt(tactic(0)))
  use(opt(seq("using", list1(thunk(constr), ","))))
  dbs(opt(seq("with", hintdb))) := new_eauto0 n use dbs.

Ltac2 eauto0 n p use dbs :=
  let dbs := default_db dbs in
  let use := default_list use in
  Std.eauto Std.Off n p use dbs.

Ltac2 Notation "eauto" n(opt(tactic(0))) p(opt(tactic(0)))
  use(opt(seq("using", list1(thunk(constr), ","))))
  dbs(opt(seq("with", hintdb))) := eauto0 n p use dbs.

Ltac2 Notation eauto := eauto.

Ltac2 Notation "typeclasses_eauto" n(opt(tactic(0)))
  dbs(opt(seq("with", list1(ident)))) := Std.typeclasses_eauto None n dbs.

Ltac2 Notation "typeclasses_eauto" "bfs" n(opt(tactic(0)))
  dbs(opt(seq("with", list1(ident)))) := Std.typeclasses_eauto (Some Std.BFS) n dbs.

Ltac2 Notation typeclasses_eauto := typeclasses_eauto.

(** Congruence *)

Ltac2 f_equal0 () := ltac1:(f_equal).
Ltac2 Notation f_equal := f_equal0 ().

(** now *)

Ltac2 now0 t := t (); ltac1:(easy).
Ltac2 Notation "now" t(thunk(self)) := now0 t.
