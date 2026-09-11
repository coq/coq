(* Regression test for #21733: universe constraints dropped by abstract
when proof term references hypotheses via Var nodes whose types
contain universe levels not directly present in the body/type. *)
(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-native-compiler" "ondemand" "-R" "iso-checker" "IsomorphismChecker" "-top" "bug_pretype_12") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 116 lines to 87 lines, then from 101 lines to 1979 lines, then from 1981 lines to 90 lines, then from 104 lines to 2723 lines, then from 2726 lines to 101 lines, then from 115 lines to 268 lines, then from 275 lines to 118 lines, then from 133 lines to 120 lines, then from 135 lines to 108 lines, then from 123 lines to 108 lines *)
(* coqc version 9.1.0 compiled with OCaml 4.14.2
coqtop version 9.1.0
Expected coqc runtime on this file: 0.924 sec
Expected coqc peak memory usage on this file: 491884.0 kb *)
Require Ltac2.Ltac2.
Module Minimal.
(* #21733: cbv beta's convert_concl ~cast:true + CUMUL pretyping drops universe constraints *)
Export Ltac2.Notations.
Axiom Iso : Type -> Type -> Prop.
Axiom rel : forall {A B : Type}, Iso A B -> A -> B -> Prop.
Record W (G : Type -> Type) := { p : forall A, G A -> Type }.
Axiom P_iso : forall F G : Type -> Type, Iso (W F) (W G).
Axiom ax : forall (F G : Type -> Type) (h : forall a b : Type, Iso a b -> Iso (F a) (G b))
  (w1 : W F) (w2 : W G) (_ : rel (P_iso F G) w1 w2) (a b : Type) (hab : Iso a b)
  (v1 : F a) (v2 : G b) (_ : rel (h a b hab) v1 v2), Iso (@p _ w1 a v1) (@p _ w2 b v2).
Ltac2 refine gc h := let fl := Constr.Pretype.Flags.open_constr_flags_no_tc in
  let c := if gc then Constr.Pretype.pretype fl (Constr.Pretype.expected_oftype (Control.goal ())) h
  else (let c := Constr.Pretype.pretype fl Constr.Pretype.expected_without_type_constraint h in
    let ty := Constr.type c in let gl := Control.goal () in unify $ty $gl; c) in exact $c.
Ltac2 nested gc := let (_,l) := Constr.decompose_app_list
    (lazy_match! goal with | [ |- Iso ?f _ ] => f end) in let a := List.nth l 0 in
  let h := match! goal with
    | [ h : forall (_ _ : Type), Iso _ _ -> Iso _ _ |- _ ] => Control.hyp h end in
  refine gc preterm:($h $a ltac2:(intros; cbv beta) ltac2:(intros; cbv beta;
    match! goal with | [ h : Iso _ _ |- _ ] => let v := Control.hyp h in exact $v end)).
Ltac2 go gc := let (_,l) := Constr.decompose_app_list
    (lazy_match! goal with | [ |- Iso ?f _ ] => f end) in
  let a := List.nth l 0 in let b := List.nth l 1 in
  let c := List.nth l 2 in let d := List.nth l 3 in
  refine gc preterm:(@ax $a ltac2:(intros; cbv beta) ltac2:(intros; cbv beta; nested gc)
    $b ltac2:(intros; cbv beta) ltac2:(intros; cbv beta;
      match! goal with | [ h : rel _ _ _ |- _ ] => let v := Control.hyp h in exact $v end)
    $c ltac2:(intros; cbv beta) ltac2:(intros; cbv beta;
      match! goal with | [ h : Iso _ _ |- _ ] => let v := Control.hyp h in exact $v end)
    $d ltac2:(intros; cbv beta) ltac2:(intros; cbv beta;
      match! goal with | [ h : rel _ _ _ |- _ ] => let v := Control.hyp h in exact $v end)).
(* Default: both flags off, bug reproduces *)
Unset Unification Recheck Casts.
Unset Unification Full Retyping.
Definition bug_default : { f : forall (A : Type) (G : Type -> Type), W G -> G A -> Type &
  forall (a b : Type) (h : Iso a b) (F G : Type -> Type) (hF : forall x y : Type,
  Iso x y -> Iso (F x) (G y)) (w1 : W F) (w2 : W G) (_ : rel (P_iso F G) w1 w2)
  (v1 : F a) (v2 : G b) (_ : rel (hF a b h) v1 v2), Iso (@p _ w1 a v1) (f b G w2 v2) }.
Proof. eexists; intros. ltac2:(go Ltac2.Init.true). Fail Qed. Abort.

(* Recheck Casts alone fixes it *)
Set Unification Recheck Casts.
Unset Unification Full Retyping.
Definition bug_recheck : { f : forall (A : Type) (G : Type -> Type), W G -> G A -> Type &
  forall (a b : Type) (h : Iso a b) (F G : Type -> Type) (hF : forall x y : Type,
  Iso x y -> Iso (F x) (G y)) (w1 : W F) (w2 : W G) (_ : rel (P_iso F G) w1 w2)
  (v1 : F a) (v2 : G b) (_ : rel (hF a b h) v1 v2), Iso (@p _ w1 a v1) (f b G w2 v2) }.
Proof. eexists; intros. ltac2:(go Ltac2.Init.true). Qed.
Unset Unification Recheck Casts.

(* Full Retyping alone fixes it *)
Unset Unification Recheck Casts.
Set Unification Full Retyping.
Definition bug_full_retype : { f : forall (A : Type) (G : Type -> Type), W G -> G A -> Type &
  forall (a b : Type) (h : Iso a b) (F G : Type -> Type) (hF : forall x y : Type,
  Iso x y -> Iso (F x) (G y)) (w1 : W F) (w2 : W G) (_ : rel (P_iso F G) w1 w2)
  (v1 : F a) (v2 : G b) (_ : rel (hF a b h) v1 v2), Iso (@p _ w1 a v1) (f b G w2 v2) }.
Proof. eexists; intros. ltac2:(go Ltac2.Init.true). Qed.
Unset Unification Full Retyping.

(* Both flags on fixes it *)
Set Unification Recheck Casts.
Set Unification Full Retyping.
Definition bug_both : { f : forall (A : Type) (G : Type -> Type), W G -> G A -> Type &
  forall (a b : Type) (h : Iso a b) (F G : Type -> Type) (hF : forall x y : Type,
  Iso x y -> Iso (F x) (G y)) (w1 : W F) (w2 : W G) (_ : rel (P_iso F G) w1 w2)
  (v1 : F a) (v2 : G b) (_ : rel (hF a b h) v1 v2), Iso (@p _ w1 a v1) (f b G w2 v2) }.
Proof. eexists; intros. ltac2:(go Ltac2.Init.true). Qed.
Unset Unification Recheck Casts.
Unset Unification Full Retyping.

(* CONV path always works regardless of flags *)
Definition ok : { f : forall (A : Type) (G : Type -> Type), W G -> G A -> Type &
  forall (a b : Type) (h : Iso a b) (F G : Type -> Type) (hF : forall x y : Type,
  Iso x y -> Iso (F x) (G y)) (w1 : W F) (w2 : W G) (_ : rel (P_iso F G) w1 w2)
  (v1 : F a) (v2 : G b) (_ : rel (hF a b h) v1 v2), Iso (@p _ w1 a v1) (f b G w2 v2) }.
Proof. eexists; intros. ltac2:(go Ltac2.Init.false). Qed.
End Minimal.
Module BugFromIssue.
Set Unification Recheck Casts.
#[export]
Set Universe Polymorphism.
Inductive eq@{s|u|} {α:Type@{s|u}} (a:α) : α -> SProp
  := eq_refl : eq a a.

#[local] Notation "x = y" := (eq x y) : type_scope.
#[export]
Set Implicit Arguments.
Record Iso@{s s'|u u'|} (A : Type@{s|u}) (B : Type@{s'|u'}) := {
    to :> A -> B;
    from : B -> A;
    to_from : forall x, to (from x) = x;
    from_to : forall x, from (to x) = x;
}.
Record > rel_iso@{s s'|u u'|} {A B} (i : Iso@{s s'|u u'} A B) (x : A) (y : B) : SProp := { proj_rel_iso :> i.(to) x = y }.
Module Export Control.

  Ltac2 solve_constraints () := ltac1:(solve_constraints).
End Control.
Module Export Std.
  Ltac2 mutable force_use_goal_constraint_flag := 0.
  Ltac2 mutable force_do_unify := 1.
  Export Ltac2.Notations.
End Std.
Module Export PolymorphicSpecif.
  Polymorphic Cumulative Record sigT@{ua ub} {A : Type@{ua}} {B : A -> Type@{ub}} := existT { projT1 : A; projT2 : B projT1 }.
End PolymorphicSpecif.
Record Producer (G : Type -> Type) := { semProdSize : forall (A : Type), G A -> SProp }.

Ltac2 refine_preterm use_gc do_unify h :=
  let fl := Constr.Pretype.Flags.open_constr_flags_no_tc in
  unshelve (
    let c :=
      if use_gc then
        Constr.Pretype.pretype fl (Constr.Pretype.expected_oftype (Control.goal ())) h
      else
        Constr.Pretype.pretype fl Constr.Pretype.expected_without_type_constraint h
    in
    (if do_unify then
       let ty := Constr.type c in
       let gl := Control.goal () in
       unify $ty $gl
     else ());
    cbv beta iota zeta in *;
    let c := eval cbv beta iota zeta in $c in
    eexact $c);
  Control.shelve_unifiable ();
  Control.solve_constraints ();
  cbv beta zeta in *.

Ltac2 resolve_iso_assumption () :=
  match! goal with
  | [ h : Iso _ _ |- _ ] => let hv := Control.hyp h in exact $hv
  | [ h : rel_iso _ _ _ |- _ ] => let hv := Control.hyp h in exact $hv
  end.

Ltac2 resolve_rel_iso () :=
  match! goal with
  | [ h : rel_iso _ _ _ |- _ ] => let hv := Control.hyp h in exact $hv
  end.

Ltac2 resolve_functor_iso () :=
  let f := lazy_match! goal with | [ |- Iso ?f _ ] => f end in
  let (_head, args) := Constr.decompose_app_list f in
  let arg := List.nth args 0 in
  let iso_proof :=
    match! goal with
    | [ h : forall (_ _ : Type), Iso _ _ -> Iso _ _ |- _ ] => Control.hyp h
    end in
  let hyp := preterm:($iso_proof
    $arg ltac2:(intros; cbv beta) ltac2:(intros; cbv beta; resolve_iso_assumption ())) in
  let use_gc := Int.gt Std.force_use_goal_constraint_flag 0 in
  let use_unify := Int.gt Std.force_do_unify 0 in
  refine_preterm use_gc use_unify hyp.

Ltac2 inlined_resolve_known_isos use_gc use_unify iso_proof :=

  let f := lazy_match! goal with | [ |- Iso ?f _ ] => f end in
  let (_h, args) := Constr.decompose_app_list f in
  let arg1 := List.nth args 0 in
  let arg2 := List.nth args 1 in
  let arg3 := List.nth args 2 in
  let arg4 := List.nth args 3 in

  let hyp := preterm:($iso_proof
    $arg1 ltac2:(intros; cbv beta) ltac2:(intros; cbv beta; resolve_functor_iso ())
    $arg2 ltac2:(intros; cbv beta) ltac2:(intros; cbv beta; resolve_rel_iso ())
    $arg3 ltac2:(intros; cbv beta) ltac2:(intros; cbv beta; resolve_iso_assumption ())
    $arg4 ltac2:(intros; cbv beta) ltac2:(intros; cbv beta; resolve_rel_iso ())) in

  refine_preterm use_gc use_unify hyp.
Parameter Producer_iso : forall x1 x2 : Type -> Type, @Iso (Producer x1) (Producer x2).
Parameter semProdSize_iso : forall (x1 x2 : Type -> Type) (hx : forall x3 x4 : Type, @Iso x3 x4 -> @Iso (x1 x3) (x2 x4)) (x3 : Producer x1) (x4 : Producer x2), @rel_iso (Producer x1) (Producer x2) (Producer_iso x1 x2) x3 x4 -> forall (x5 x6 : Type) (hx1 : @Iso x5 x6) (x7 : x1 x5) (x8 : x2 x6), @rel_iso (x1 x5) (x2 x6) (hx x5 x6 hx1) x7 x8 -> @Iso (@semProdSize x1 x3 x5 x7) (@semProdSize x2 x4 x6 x8).
(* Test with abstract (uses build_constant_by_tactic) *)
Definition buggy_packaged :
  @PolymorphicSpecif.sigT
    (forall (x : Type) (x0 : Type -> Type) (_ : Producer x0) (_ : x0 x), SProp)
    (fun imported : forall (x : Type) (x0 : Type -> Type) (_ : Producer x0) (_ : x0 x), SProp =>
    forall (x1 x2 : Type) (hx : @Iso x1 x2) (x3 x4 : Type -> Type)
      (hx0 : forall (x5 x6 : Type) (_ : @Iso x5 x6), @Iso (x3 x5) (x4 x6))
      (x5 : Producer x3) (x6 : Producer x4)
      (_ : @rel_iso (Producer x3) (Producer x4) (Producer_iso x3 x4) x5 x6)
      (x7 : x3 x1) (x8 : x4 x2)
      (_ : @rel_iso (x3 x1) (x4 x2) (hx0 x1 x2 hx) x7 x8),
    @Iso (@semProdSize x3 x5 x1 x7) (imported x2 x4 x6 x8)).
Proof.
  eexists.
  intros.
  Fail Fail abstract (ltac2:(inlined_resolve_known_isos Ltac2.Init.false Ltac2.Init.false constr:(semProdSize_iso))). (* this always succeeded *)
  Fail Fail abstract (ltac2:(inlined_resolve_known_isos Ltac2.Init.false Ltac2.Init.true constr:(semProdSize_iso))). (* this always succeeded *)
  Fail Fail abstract (ltac2:(inlined_resolve_known_isos Ltac2.Init.true Ltac2.Init.true constr:(semProdSize_iso))). (* this always succeeded *)
  abstract (ltac2:(inlined_resolve_known_isos Ltac2.Init.true Ltac2.Init.false constr:(semProdSize_iso))).
Qed.

(* Test without abstract (Qed, no build_constant_by_tactic) *)
Definition buggy_packaged2 :
  @PolymorphicSpecif.sigT
    (forall (x : Type) (x0 : Type -> Type) (_ : Producer x0) (_ : x0 x), SProp)
    (fun imported : forall (x : Type) (x0 : Type -> Type) (_ : Producer x0) (_ : x0 x), SProp =>
    forall (x1 x2 : Type) (hx : @Iso x1 x2) (x3 x4 : Type -> Type)
      (hx0 : forall (x5 x6 : Type) (_ : @Iso x5 x6), @Iso (x3 x5) (x4 x6))
      (x5 : Producer x3) (x6 : Producer x4)
      (_ : @rel_iso (Producer x3) (Producer x4) (Producer_iso x3 x4) x5 x6)
      (x7 : x3 x1) (x8 : x4 x2)
      (_ : @rel_iso (x3 x1) (x4 x2) (hx0 x1 x2 hx) x7 x8),
    @Iso (@semProdSize x3 x5 x1 x7) (imported x2 x4 x6 x8)).
Proof.
  eexists.
  intros.
  ltac2:(inlined_resolve_known_isos Ltac2.Init.true Ltac2.Init.false constr:(semProdSize_iso)).
Qed.
End BugFromIssue.
