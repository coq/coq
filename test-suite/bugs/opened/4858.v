(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "src" "Crypto" "-R" "Bedrock" "Bedrock" "-top" "CompleteWeierstrassCurveTheorems") -*- *)
(* File reduced by coq-bug-finder from original input, then from 375 lines to 15 lines, then from 128 lines to 19 lines, then from 759 lines to 236 lines, then from 253 lines to 236 lines, then from 412 lines to 351 lines, then from 356 lines to 329 lines, then from 343 lines to 329 lines, then from 324 lines to 264 lines, then from 278 lines to 264 lines *)
(* coqc version 8.5pl1 (June 2016) compiled on Jun 21 2016 11:33:29 with OCaml 4.01.0
   coqtop version 8.5pl1 (June 2016) *)
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Require Coq.nsatz.Nsatz.

Import Coq.Lists.List.
Lemma cring_sub_diag_iff {R zero eq sub} `{cring:Cring.Cring (R:=R) (ring0:=zero) (ring_eq:=eq) (sub:=sub)}
  : forall x y, eq (sub x y) zero <-> eq x y.
  admit.
Defined.

Ltac get_goal := lazymatch goal with |- ?g => g end.

Ltac nsatz_equation_implications_to_list eq zero g :=
  lazymatch g with
  | eq ?p zero => constr:(p::nil)
  | eq ?p zero -> ?g => let l := nsatz_equation_implications_to_list eq zero g in constr:(p::l)
  end.

Ltac nsatz_reify_equations eq zero :=
  let g := get_goal in
  let lb := nsatz_equation_implications_to_list eq zero g in
  lazymatch (eval red in (Ncring_tac.list_reifyl (lterm:=lb))) with
    (?variables, ?le) =>
    lazymatch (eval compute in (List.rev le)) with
    | ?reified_goal::?reified_givens => constr:((variables, reified_givens, reified_goal))
    end
  end.

Ltac nsatz_get_free_variables reified_package :=
  lazymatch reified_package with (?fv, _, _) => fv end.

Ltac nsatz_get_reified_givens reified_package :=
  lazymatch reified_package with (_, ?givens, _) => givens end.

Ltac nsatz_get_reified_goal reified_package :=
  lazymatch reified_package with (_, _, ?goal) => goal end.
Import Coq.nsatz.Nsatz.

Ltac nsatz_compute_to_goal sugar nparams reified_goal power reified_givens :=
  nsatz_compute (PEc sugar :: PEc nparams :: PEpow reified_goal power :: reified_givens).

Ltac nsatz_compute_get_leading_coefficient :=
  lazymatch goal with
    |- Logic.eq ((?a :: _ :: ?b) :: ?c) _ -> _ => a
  end.

Ltac nsatz_compute_get_certificate :=
  lazymatch goal with
    |- Logic.eq ((?a :: _ :: ?b) :: ?c) _ -> _ => constr:((c,b))
  end.

Ltac nsatz_rewrite_and_revert domain :=
  lazymatch type of domain with
  | @Integral_domain.Integral_domain ?F ?zero _ _ _ _ _ ?eq ?Fops ?FRing ?FCring =>
    lazymatch goal with
    | |- eq _ zero => idtac
    | |- eq _ _ => rewrite <-(cring_sub_diag_iff (cring:=FCring))
    end;
    repeat match goal with
           | [H : eq _ zero |- _ ] => revert H
           | [H : eq _ _ |- _ ] => rewrite <-(cring_sub_diag_iff (cring:=FCring)) in H; revert H
           end
  end.

Ltac nsatz_clear_duplicates_for_bug_4851 domain :=
  lazymatch type of domain with
  | @Integral_domain.Integral_domain _ _ _ _ _ _ _ ?eq _ _ _ =>
    repeat match goal with
           | [ H : eq ?x ?y, H' : eq ?x ?y |- _ ] => clear H'
           end
  end.

Ltac nsatz_nonzero :=
  try solve [apply Integral_domain.integral_domain_one_zero
            |apply Integral_domain.integral_domain_minus_one_zero
            |trivial
            |assumption].

Ltac nsatz_domain_sugar_power domain sugar power :=
  let nparams := constr:(BinInt.Zneg BinPos.xH) in
  lazymatch type of domain with
  | @Integral_domain.Integral_domain ?F ?zero _ _ _ _ _ ?eq ?Fops ?FRing ?FCring =>
    nsatz_clear_duplicates_for_bug_4851 domain;
    nsatz_rewrite_and_revert domain;
    let reified_package := nsatz_reify_equations eq zero in
    let fv := nsatz_get_free_variables reified_package in
    let interp := constr:(@Nsatz.PEevalR _ _ _ _ _ _ _ _ Fops fv) in
    let reified_givens := nsatz_get_reified_givens reified_package in
    let reified_goal := nsatz_get_reified_goal reified_package in
    nsatz_compute_to_goal sugar nparams reified_goal power reified_givens;
    let a := nsatz_compute_get_leading_coefficient in
    let crt := nsatz_compute_get_certificate in
    intros _ ; intros;
    apply (fun Haa refl cond => @Integral_domain.Rintegral_domain_pow _ _ _ _ _ _ _ _ _ _ _ domain (interp a) _ (BinNat.N.to_nat power) Haa (@Nsatz.check_correct _ _ _ _ _ _ _ _ _ _ FCring fv reified_givens (PEmul a (PEpow reified_goal power)) crt refl cond));
    [ nsatz_nonzero; cbv iota beta delta [Nsatz.PEevalR PEeval InitialRing.gen_phiZ InitialRing.gen_phiPOS]
    | solve [vm_compute; exact (eq_refl true)]
    | solve [repeat (split; [assumption|]); exact I] ]
  end.

Ltac nsatz_guess_domain :=
  match goal with
  | |- ?eq _ _ => constr:(_:Integral_domain.Integral_domain (ring_eq:=eq))
  | |- not (?eq _ _) =>  constr:(_:Integral_domain.Integral_domain (ring_eq:=eq))
  | [H: ?eq _ _ |- _ ] =>  constr:(_:Integral_domain.Integral_domain (ring_eq:=eq))
  | [H: not (?eq _ _) |- _] =>  constr:(_:Integral_domain.Integral_domain (ring_eq:=eq))
  end.

Ltac nsatz_sugar_power sugar power :=
  let domain := nsatz_guess_domain in
  nsatz_domain_sugar_power domain sugar power.

Tactic Notation "nsatz" constr(n) :=
  let nn := (eval compute in (BinNat.N.of_nat n)) in
  nsatz_sugar_power BinInt.Z0 nn.

Tactic Notation "nsatz" := nsatz 1%nat || nsatz 2%nat || nsatz 3%nat || nsatz 4%nat || nsatz 5%nat.

Section Algebra.
  Context {T:Type} {eq:T->T->Prop}.

  Class is_eq_dec := { eq_dec : forall x y : T, {x=y} + {x<>y} }.

  Section SingleOperation.
    Context {op:T->T->T}.

    Class is_associative := { associative : forall x y z, op x (op y z) = op (op x y) z }.

    Context {id:T}.

    Class is_left_identity := { left_identity : forall x, op id x = x }.
    Class is_right_identity := { right_identity : forall x, op x id = x }.

    Class monoid :=
      {
        monoid_is_associative : is_associative;
        monoid_is_left_identity : is_left_identity;
        monoid_is_right_identity : is_right_identity;

        monoid_op_Proper: Proper (respectful eq (respectful eq eq)) op;
        monoid_Equivalence : Equivalence eq;
        monoid_is_eq_dec : is_eq_dec
      }.

    Context {inv:T->T}.
    Class is_left_inverse := { left_inverse : forall x, op (inv x) x = id }.
    Class is_right_inverse := { right_inverse : forall x, op x (inv x) = id }.

    Class group :=
      {
        group_monoid : monoid;
        group_is_left_inverse : is_left_inverse;
        group_is_right_inverse : is_right_inverse;

        group_inv_Proper: Proper (respectful eq eq) inv
      }.

    Class is_commutative := { commutative : forall x y, op x y = op y x }.

    Record abelian_group :=
      {
        abelian_group_group : group;
        abelian_group_is_commutative : is_commutative
      }.
  End SingleOperation.

  Section AddMul.
    Context {zero one:T}.
    Local Notation "0" := zero.
    Local Notation "1" := one.
    Context {opp:T->T}.
    Context {add:T->T->T} {sub:T->T->T} {mul:T->T->T}.
    Local Infix "+" := add.
    Local Infix "-" := sub.
    Local Infix "*" := mul.

    Class is_left_distributive := { left_distributive : forall a b c, a * (b + c) =  a * b + a * c }.
    Class is_right_distributive := { right_distributive : forall a b c, (b + c) * a = b * a + c * a }.

    Class ring :=
      {
        ring_abelian_group_add : abelian_group (op:=add) (id:=zero) (inv:=opp);
        ring_monoid_mul : monoid (op:=mul) (id:=one);
        ring_is_left_distributive : is_left_distributive;
        ring_is_right_distributive : is_right_distributive;

        ring_sub_definition : forall x y, x - y = x + opp y;

        ring_mul_Proper : Proper (respectful eq (respectful eq eq)) mul;
        ring_sub_Proper : Proper(respectful eq (respectful eq eq)) sub
      }.

    Class commutative_ring :=
      {
        commutative_ring_ring : ring;
        commutative_ring_is_commutative : is_commutative (op:=mul)
      }.
    Global Existing Instance commutative_ring_ring.

    Class is_mul_nonzero_nonzero := { mul_nonzero_nonzero : forall x y, x<>0 -> y<>0 -> x*y<>0 }.

    Class is_zero_neq_one := { zero_neq_one : zero <> one }.

    Class integral_domain :=
      {
        integral_domain_commutative_ring : commutative_ring;
        integral_domain_is_mul_nonzero_nonzero : is_mul_nonzero_nonzero;
        integral_domain_is_zero_neq_one : is_zero_neq_one
      }.
    Global Existing Instance integral_domain_commutative_ring.

    Context {inv:T->T} {div:T->T->T}.
    Class is_left_multiplicative_inverse := { left_multiplicative_inverse : forall x, x<>0 -> (inv x) * x = 1 }.

    Class field :=
      {
        field_commutative_ring : commutative_ring;
        field_is_left_multiplicative_inverse : is_left_multiplicative_inverse;
        field_domain_is_zero_neq_one : is_zero_neq_one;

        field_div_definition : forall x y , div x y = x * inv y;

        field_inv_Proper : Proper (respectful eq eq) inv;
        field_div_Proper : Proper (respectful eq (respectful eq eq)) div
      }.
  End AddMul.
End Algebra.

Module Export Ring.

  Global Instance Ncring_Ring_ops {T eq zero one opp add sub mul} `{@ring T eq zero one opp add sub mul} : @Ncring.Ring_ops T zero one add mul sub opp eq.
  Global Instance Ncring_Ring {T eq zero one opp add sub mul} `{@ring T eq zero one opp add sub mul} : @Ncring.Ring T zero one add mul sub opp eq Ncring_Ring_ops.
  admit.
  Defined.

  Section TacticSupportCommutative.
    Context {T eq zero one opp add sub mul} `{@commutative_ring T eq zero one opp add sub mul}.

    Global Instance Cring_Cring_commutative_ring :
      @Cring.Cring T zero one add mul sub opp eq Ring.Ncring_Ring_ops Ring.Ncring_Ring.
    admit.
    Defined.
  End TacticSupportCommutative.
  Section IntegralDomain.
    Context {T eq zero one opp add sub mul} `{@integral_domain T eq zero one opp add sub mul}.

    Global Instance Integral_domain :
      @Integral_domain.Integral_domain T zero one add mul sub opp eq Ring.Ncring_Ring_ops
                                       Ring.Ncring_Ring Ring.Cring_Cring_commutative_ring.
    admit.
    Defined.
  End IntegralDomain.
  Global Instance integral_domain {T eq zero one opp add mul sub inv div} `{@field T eq zero one opp add sub mul inv div} : @integral_domain T eq zero one opp add sub mul.
  admit.
  Defined.
  Section CompleteWeierstrassCurveTheorems.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}.
    Local Infix "=" := Feq : type_scope.

    Goal forall xx f10 f9 : F, xx = xx -> f9 = f10.
      intros.
      try nsatz. (* Anomaly: Uncaught exception Failure("hd"). Please report. *)
