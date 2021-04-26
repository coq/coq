Section inversion_sigma.
  Local Unset Implicit Arguments.
  Context A (B B' : A -> Prop) (C C' : forall a, B a -> Prop)
          (D : forall a b, C a b -> Prop) (E : forall a b c, D a b c -> Prop).
  Context (AP : Prop) (BP BP' : AP -> Prop) (CP CP' : forall a, BP a -> Prop)
          (DP : forall a b, CP a b -> Prop) (EP : forall a b c, DP a b c -> Prop).

  (* Require that, after destructing sigma types and inverting
     equalities, we can subst equalities of variables only, and reduce
     down to [eq_refl = eq_refl]. *)
  Local Ltac destr_sigma :=
    repeat match goal with
           | [ H : ex _ |- _ ] => destruct H
           | [ H : sig _ |- _ ] => destruct H
           | [ H : sigT _ |- _ ] => destruct H
           | [ H : ex2 _ _ |- _ ] => destruct H
           | [ H : sig2 _ _ |- _ ] => destruct H
           | [ H : sigT2 _ _ |- _ ] => destruct H
           end; simpl in *.
  Local Ltac fin_test_inversion_sigma :=
    match goal with
    | [ |- eq_refl = eq_refl ] => reflexivity
    end.
  Local Ltac test_inversion_sigma :=
    intros;
    destr_sigma;
    inversion_sigma;
    repeat match goal with
           | [ H : ?x = ?y |- _ ] => is_var x; is_var y; subst x; simpl in *
           end;
    fin_test_inversion_sigma.

  Local Ltac test_inversion_sigma_in_H :=
    intros;
    destr_sigma;
    repeat match goal with H : _ = _ |- _ => inversion_sigma H end;
    repeat match goal with
           | [ H : ?x = ?y |- _ ] => is_var x; is_var y; subst x; simpl in *
           end;
    fin_test_inversion_sigma.

  Goal forall (x y : { a : A & { b : { b : B a & C a b } & { d : D a (projT1 b) (projT2 b) & E _ _ _ d } } })
              (p : x = y), p = p.
  Proof.
    intros x y p; destr_sigma.
    inversion_sigma p as [-> p]; cbn [eq_rect] in *.
    lazymatch type of p with
    | existT _ (existT _ ?a ?b) (existT _ ?c ?d) = existT _ (existT _ ?e ?f) (existT _ ?g ?h)
      => is_var a; is_var b; is_var c; is_var d; is_var e; is_var f; is_var g; is_var h
    end.
    inversion_sigma p as [p1 p2].
    lazymatch type of p1 with existT _ ?a ?b = existT _ ?c ?d => is_var a; is_var b; is_var c; is_var d end.
    inversion_sigma p1 as [-> <-]; cbn [eq_rect eq_existT_uncurried eq_sigT eq_existT_curried eq_sigT_uncurried] in * |- .
    lazymatch type of p2 with existT _ ?a ?b = existT _ ?c ?d => is_var a; is_var b; is_var c; is_var d end.
    inversion_sigma p2 as [-> <-].
    cbn.
    fin_test_inversion_sigma.
  Qed.

  Goal forall (x y : { a : A | { b : { b : B a | C a b } | { d : D a (proj1_sig b) (proj2_sig b) | E _ _ _ d } } })
              (p : x = y), p = p.
  Proof.
    intros x y p; destr_sigma.
    inversion_sigma p as [-> p]; cbn [eq_rect] in *.
    lazymatch type of p with
    | exist _ (exist _ ?a ?b) (exist _ ?c ?d) = exist _ (exist _ ?e ?f) (exist _ ?g ?h)
      => is_var a; is_var b; is_var c; is_var d; is_var e; is_var f; is_var g; is_var h
    end.
    inversion_sigma p as [p1 p2].
    lazymatch type of p1 with exist _ ?a ?b = exist _ ?c ?d => is_var a; is_var b; is_var c; is_var d end.
    inversion_sigma p1 as [-> <-]; cbn [eq_rect eq_exist_uncurried eq_sig eq_exist_curried eq_sig_uncurried] in * |- .
    lazymatch type of p2 with exist _ ?a ?b = exist _ ?c ?d => is_var a; is_var b; is_var c; is_var d end.
    inversion_sigma p2 as [-> <-].
    cbn.
    fin_test_inversion_sigma.
  Qed.

  Goal forall (x y : exists a : AP, exists b : exists b : BP a, CP a b, exists d : DP a (ex_proj1 b) (ex_proj2 b), EP _ _ _ d)
              (p : x = y), p = p.
  Proof.
    intros x y p; destr_sigma.
    inversion_sigma p as [-> p]; cbn [eq_rect] in *.
    lazymatch type of p with
    | ex_intro _ (ex_intro _ ?a ?b) (ex_intro _ ?c ?d) = ex_intro _ (ex_intro _ ?e ?f) (ex_intro _ ?g ?h)
      => is_var a; is_var b; is_var c; is_var d; is_var e; is_var f; is_var g; is_var h
    end.
    inversion_sigma p as [p1 p2].
    lazymatch type of p1 with ex_intro _ ?a ?b = ex_intro _ ?c ?d => is_var a; is_var b; is_var c; is_var d end.
    inversion_sigma p1 as [-> <-]; cbn [eq_rect eq_ex_intro_uncurried eq_ex_intro eq_ex eq_ex_uncurried] in * |- .
    lazymatch type of p2 with ex_intro _ ?a ?b = ex_intro _ ?c ?d => is_var a; is_var b; is_var c; is_var d end.
    inversion_sigma p2 as [-> <-].
    cbn.
    fin_test_inversion_sigma.
  Qed.

  Goal forall (x y : { a : { a : A & B a } & C _ (projT2 a) & C' _ (projT2 a) })
              (p : x = y), p = p.
  Proof.
    intros x y p; destr_sigma.
    inversion_sigma p as [p <- <-]; cbn [eq_rect] in *.
    lazymatch type of p with existT _ ?a ?b = existT _ ?c ?d => is_var a; is_var b; is_var c; is_var d end.
    inversion_sigma p as [-> <-].
    cbn.
    fin_test_inversion_sigma.
  Qed.

  Goal forall (x y : { a : { a : A & B a } | C _ (projT2 a) & C' _ (projT2 a) })
              (p : x = y), p = p.
  Proof.
    intros x y p; destr_sigma.
    inversion_sigma p as [p <- <-]; cbn [eq_rect] in *.
    lazymatch type of p with existT _ ?a ?b = existT _ ?c ?d => is_var a; is_var b; is_var c; is_var d end.
    inversion_sigma p as [-> <-].
    cbn.
    fin_test_inversion_sigma.
  Qed.

  Goal forall (x y : exists2 a : exists a : AP, BP a, CP _ (ex_proj2 a) & CP' _ (ex_proj2 a))
              (p : x = y), p = p.
  Proof.
    intros x y p; destr_sigma.
    inversion_sigma p as [p <- <-]; cbn [eq_rect] in *.
    lazymatch type of p with ex_intro _ ?a ?b = ex_intro _ ?c ?d => is_var a; is_var b; is_var c; is_var d end.
    inversion_sigma p as [-> <-].
    cbn.
    fin_test_inversion_sigma.
  Qed.

  Goal forall (x y : { a : { a : A & B a & B' a } & C _ (projT2 (sigT_of_sigT2 a)) & C' _ (projT2 (sigT_of_sigT2 a)) })
              (p : x = y), p = p.
  Proof.
    intros x y p; destr_sigma.
    inversion_sigma p as [p <- <-]; cbn [eq_rect] in *.
    lazymatch type of p with existT2 _ _ ?a ?b ?c = existT2 _ _ ?d ?e ?f => is_var a; is_var b; is_var c; is_var d; is_var e; is_var f end.
    inversion_sigma p as [-> <- <-].
    cbn.
    fin_test_inversion_sigma.
  Qed.

  Goal forall (x y : { a : { a : A & B a & B' a } | C _ (projT2 (sigT_of_sigT2 a)) & C' _ (projT2 (sigT_of_sigT2 a)) })
              (p : x = y), p = p.
  Proof.
    intros x y p; destr_sigma.
    inversion_sigma p as [p <- <-]; cbn [eq_rect] in *.
    lazymatch type of p with existT2 _ _ ?a ?b ?c = existT2 _ _ ?d ?e ?f => is_var a; is_var b; is_var c; is_var d; is_var e; is_var f end.
    inversion_sigma p as [-> <- <-].
    cbn.
    fin_test_inversion_sigma.
  Qed.

  Goal forall (x y : exists2 a : exists2 a : AP, BP a & BP' a, CP _ (ex_proj2 (ex_of_ex2 a)) & CP' _ (ex_proj2 (ex_of_ex2 a)))
              (p : x = y), p = p.
  Proof.
    intros x y p; destr_sigma.
    inversion_sigma p as [p <- <-]; cbn [eq_rect] in *.
    lazymatch type of p with ex_intro2 _ _ ?a ?b ?c = ex_intro2 _ _ ?d ?e ?f => is_var a; is_var b; is_var c; is_var d; is_var e; is_var f end.
    inversion_sigma p as [-> <- <-].
    cbn.
    fin_test_inversion_sigma.
  Qed.

  Goal forall (x y : { a : A & { b : { b : B a & C a b } & { d : D a (projT1 b) (projT2 b) & E _ _ _ d } } })
              (p : x = y), p = p.
  Proof. test_inversion_sigma. Qed.

  Goal forall (x y : { a : A | { b : { b : B a | C a b } | { d : D a (proj1_sig b) (proj2_sig b) | E _ _ _ d } } })
              (p : x = y), p = p.
  Proof. test_inversion_sigma. Qed.

  Goal forall (x y : exists a : AP, exists b : exists b : BP a, CP a b, exists d : DP a (ex_proj1 b) (ex_proj2 b), EP _ _ _ d)
              (p : x = y), p = p.
  Proof. test_inversion_sigma. Qed.

  Goal forall (x y : { a : { a : A & B a } & C _ (projT2 a) & C' _ (projT2 a) })
              (p : x = y), p = p.
  Proof. test_inversion_sigma. Qed.

  Goal forall (x y : { a : { a : A & B a } | C _ (projT2 a) & C' _ (projT2 a) })
              (p : x = y), p = p.
  Proof. test_inversion_sigma. Qed.

  Goal forall (x y : { a : { a : A & B a & B' a } | C _ (projT2 (sigT_of_sigT2 a)) & C' _ (projT2 (sigT_of_sigT2 a)) })
              (p : x = y), p = p.
  Proof. test_inversion_sigma. Qed.

  Goal forall (x y : { a : { a : A & B a & B' a } | C _ (projT2 (sigT_of_sigT2 a)) & C' _ (projT2 (sigT_of_sigT2 a)) })
              (p : x = y), p = p.
  Proof. test_inversion_sigma. Qed.

  Goal forall (x y : exists2 a : exists2 a : AP, BP a & BP' a, CP _ (ex_proj2 (ex_of_ex2 a)) & CP' _ (ex_proj2 (ex_of_ex2 a)))
              (p : x = y), p = p.
  Proof. test_inversion_sigma. Qed.


  Goal forall (x y : { a : A & { b : { b : B a & C a b } & { d : D a (projT1 b) (projT2 b) & E _ _ _ d } } })
              (p : x = y), p = p.
  Proof. test_inversion_sigma_in_H. Qed.

  Goal forall (x y : { a : A | { b : { b : B a | C a b } | { d : D a (proj1_sig b) (proj2_sig b) | E _ _ _ d } } })
              (p : x = y), p = p.
  Proof. test_inversion_sigma_in_H. Qed.

  Goal forall (x y : exists a : AP, exists b : exists b : BP a, CP a b, exists d : DP a (ex_proj1 b) (ex_proj2 b), EP _ _ _ d)
              (p : x = y), p = p.
  Proof. test_inversion_sigma_in_H. Qed.

  Goal forall (x y : { a : { a : A & B a } & C _ (projT2 a) & C' _ (projT2 a) })
              (p : x = y), p = p.
  Proof. test_inversion_sigma_in_H. Qed.

  Goal forall (x y : { a : { a : A & B a } | C _ (projT2 a) & C' _ (projT2 a) })
              (p : x = y), p = p.
  Proof. test_inversion_sigma_in_H. Qed.

  Goal forall (x y : { a : { a : A & B a & B' a } | C _ (projT2 (sigT_of_sigT2 a)) & C' _ (projT2 (sigT_of_sigT2 a)) })
              (p : x = y), p = p.
  Proof. test_inversion_sigma_in_H. Qed.

  Goal forall (x y : { a : { a : A & B a & B' a } | C _ (projT2 (sigT_of_sigT2 a)) & C' _ (projT2 (sigT_of_sigT2 a)) })
              (p : x = y), p = p.
  Proof. test_inversion_sigma_in_H. Qed.

  Goal forall (x y : exists2 a : exists2 a : AP, BP a & BP' a, CP _ (ex_proj2 (ex_of_ex2 a)) & CP' _ (ex_proj2 (ex_of_ex2 a)))
              (p : x = y), p = p.
  Proof. test_inversion_sigma_in_H. Qed.
End inversion_sigma.
