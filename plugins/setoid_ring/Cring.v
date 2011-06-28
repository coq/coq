(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import List.
Require Import Setoid.
Require Import BinPos.
Require Import BinList.
Require Import Znumtheory.
Require Export Morphisms Setoid Bool.
Require Import ZArith.
Require Export Algebra_syntax.
Require Export Ring2.
Require Export Ring2_initial.
Require Export Ring2_tac.

Class Cring {R:Type}`{Rr:Ring R} := 
 cring_mul_comm: forall x y:R, x * y == y * x.

Ltac reify_goal lvar lexpr lterm:=
  (*idtac lvar; idtac lexpr; idtac lterm;*)
  match lexpr with
     nil => idtac
   | ?e1::?e2::_ =>  
        match goal with
          |- (?op ?u1 ?u2) =>
           change (op 
             (@Ring_polynom.PEeval
               _ zero _+_ _*_ _-_ -_ Z gen_phiZ N (fun n:N => n)
               (@Ring_theory.pow_N _ 1 multiplication) lvar e1)
             (@Ring_polynom.PEeval
               _ zero _+_ _*_ _-_ -_ Z gen_phiZ N (fun n:N => n)
               (@Ring_theory.pow_N _ 1 multiplication) lvar e2))
        end
  end.

Section cring.
Context {R:Type}`{Rr:Cring R}.

Lemma cring_eq_ext: ring_eq_ext _+_ _*_ -_ _==_.
intros. apply mk_reqe;intros. 
rewrite H. rewrite H0. reflexivity.
rewrite H. rewrite H0. reflexivity.
 rewrite H. reflexivity. Defined.

Lemma cring_almost_ring_theory:
   almost_ring_theory (R:=R) zero one _+_ _*_ _-_ -_ _==_.
intros. apply mk_art ;intros. 
rewrite ring_add_0_l; reflexivity. 
rewrite ring_add_comm; reflexivity. 
rewrite ring_add_assoc; reflexivity. 
rewrite ring_mul_1_l; reflexivity. 
apply ring_mul_0_l.
rewrite cring_mul_comm; reflexivity. 
rewrite ring_mul_assoc; reflexivity. 
rewrite ring_distr_l; reflexivity. 
rewrite ring_opp_mul_l; reflexivity. 
apply ring_opp_add.
rewrite ring_sub_def ; reflexivity. Defined.

Lemma cring_morph:
  ring_morph  zero one _+_ _*_ _-_ -_ _==_
             0%Z 1%Z Zplus Zmult Zminus Zopp Zeq_bool
             gen_phiZ.
intros. apply mkmorph ; intros; simpl; try reflexivity.
rewrite gen_phiZ_add; reflexivity.
rewrite ring_sub_def. unfold Zminus. rewrite gen_phiZ_add.
rewrite gen_phiZ_opp; reflexivity.
rewrite gen_phiZ_mul; reflexivity.
rewrite gen_phiZ_opp; reflexivity.
rewrite (Zeqb_ok x y H). reflexivity. Defined.

Lemma cring_power_theory : 
  @Ring_theory.power_theory R one _*_ _==_ N (fun n:N => n)
  (@Ring_theory.pow_N _  1 multiplication).
intros; apply Ring_theory.mkpow_th. reflexivity. Defined.

Lemma cring_div_theory: 
  div_theory _==_ Zplus Zmult gen_phiZ Z.quotrem.
intros. apply InitialRing.Ztriv_div_th. unfold Setoid_Theory.
simpl.   apply ring_setoid. Defined.
End cring.

Ltac cring_gen :=
  match goal with
    |- ?g => let lterm := lterm_goal g in (* les variables *)
        match eval red in (list_reifyl (lterm:=lterm)) with
          | (?fv, ?lexpr) => 
           (*idtac "variables:";idtac fv;
           idtac "terms:"; idtac lterm;
           idtac "reifications:"; idtac lexpr; *)
           reify_goal fv lexpr lterm;
           match goal with 
             |- ?g => 
               generalize
                 (@Ring_polynom.ring_correct _ 0 1 _+_ _*_ _-_ -_ _==_
                        ring_setoid
                        cring_eq_ext
                        cring_almost_ring_theory
                        Z 0%Z 1%Z Zplus Zmult Zminus Zopp Zeq_bool
                        gen_phiZ
                        cring_morph
                        N
                        (fun n:N => n)
                        (@Ring_theory.pow_N _  1 multiplication)
                        cring_power_theory
                        Z.quotrem
                        cring_div_theory
                        O fv nil);
                 let rc := fresh "rc"in
                   intro rc; apply rc
           end
        end
  end.

Ltac cring_compute:= vm_compute; reflexivity.

Ltac cring:= 
  intros;
  cring_gen;
  cring_compute.

