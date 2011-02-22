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
Require Import Zdiv_def.
Require Export Morphisms Setoid Bool.
Require Import ZArith.
Require Import Algebra_syntax.
Require Import Ring_polynom.
Require Export Cring.
Require Import Cring_initial.


Set Implicit Arguments.

Class is_closed_list T (l:list T) := {}.
Instance Iclosed_nil T 
 : is_closed_list (T:=T) nil.
Instance Iclosed_cons T t l 
 `{is_closed_list (T:=T) l} 
 : is_closed_list (T:=T) (t::l).

Class is_in_list_at (R:Type) (t:R) (l:list R) (i:nat) := {}.
Instance  Ifind0 (R:Type) (t:R) l
 : is_in_list_at t (t::l) 0.
Instance  IfindS (R:Type) (t2 t1:R) l i 
 `{is_in_list_at R t1 l i} 
 : is_in_list_at t1 (t2::l) (S i) | 1.

Class reifyPE (R:Type) (e:PExpr Z) (lvar:list R) (t:R) := {}.
Instance  reify_zero (R:Type) (RR:Cring R) lvar 
 : reifyPE (PEc 0%Z) lvar cring0.
Instance  reify_one (R:Type) (RR:Cring R) lvar 
 : reifyPE (PEc 1%Z) lvar cring1.
Instance  reify_plus (R:Type)  (RR:Cring R)
  e1 lvar t1 e2 t2 
 `{reifyPE R e1 lvar t1} 
 `{reifyPE R e2 lvar t2} 
 : reifyPE (PEadd e1 e2) lvar (cring_plus t1 t2).
Instance  reify_mult (R:Type)  (RR:Cring R)
  e1 lvar t1 e2 t2 
 `{reifyPE R e1 lvar t1} 
 `{reifyPE R e2 lvar t2}
 : reifyPE (PEmul e1 e2) lvar (cring_mult t1 t2).
Instance  reify_sub (R:Type) (RR:Cring R) 
 e1 lvar t1 e2 t2 
 `{reifyPE R e1 lvar t1} 
 `{reifyPE R e2 lvar t2}
 : reifyPE (PEsub e1 e2) lvar (cring_sub t1 t2).
Instance  reify_opp (R:Type) (RR:Cring R) 
 e1 lvar t1 
 `{reifyPE R e1 lvar t1}
 : reifyPE (PEopp e1) lvar (cring_opp t1).
Instance  reify_pow (R:Type) (RR:Cring R) 
 e1 lvar t1 n 
 `{reifyPE R e1 lvar t1}
 : reifyPE (PEpow e1 n) lvar (@Ring_theory.pow_N _ cring1 cring_mult t1 n).
Instance  reify_var (R:Type) t lvar i 
 `{is_in_list_at R t lvar i}
 : reifyPE (PEX Z (P_of_succ_nat i)) lvar t 
 | 100.

Class reifyPElist (R:Type) (lexpr:list (PExpr Z)) (lvar:list R) 
  (lterm:list R) := {}.
Instance reifyPE_nil (R:Type) lvar 
 : @reifyPElist R nil lvar (@nil R).
Instance reifyPE_cons (R:Type) e1 lvar t1 lexpr2 lterm2
 `{reifyPE R e1 lvar t1} `{reifyPElist R lexpr2 lvar lterm2} 
 : reifyPElist (e1::lexpr2) lvar (t1::lterm2).

Definition list_reifyl (R:Type) lexpr lvar lterm 
 `{reifyPElist R lexpr lvar lterm}
 `{is_closed_list (T:=R) lvar} := (lvar,lexpr).

Unset Implicit Arguments.

Instance multiplication_phi_cring{R:Type}{Rr:Cring R} : Multiplication  :=
  {multiplication x y := cring_mult
    (@gen_phiZ R Rr x) y}.

(*
Print HintDb typeclass_instances.
*)
(* Reification *)

Ltac lterm_goal g :=
  match g with
  cring_eq ?t1 ?t2 => constr:(t1::t2::nil)
  | cring_eq ?t1 ?t2 -> ?g => let lvar := lterm_goal g in constr:(t1::t2::lvar)     
  end.

Ltac reify_goal lvar lexpr lterm:=
(*  idtac lvar; idtac lexpr; idtac lterm;*)
  match lexpr with
     nil => idtac
   | ?e::?lexpr1 =>  
        match lterm with
         ?t::?lterm1 => (* idtac "t="; idtac t;*)
           let x := fresh "T" in
           set (x:= t);
           change x with 
             (@PEeval _ 0 addition multiplication subtraction opposite  Z
               (@gen_phiZ _ _)
               N (fun n:N => n) (@Ring_theory.pow_N _ 1 multiplication) lvar e); 
           clear x;
           reify_goal lvar lexpr1 lterm1
        end
  end.

Existing Instance gen_phiZ_morph.
Existing Instance Zr.

Lemma Zeqb_ok: forall x y : Z, Zeq_bool x y = true -> x == y.
 intros x y H. rewrite (Zeq_bool_eq x y H). rrefl. Qed. 


Lemma cring_eq_ext: forall (R:Type)(Rr:Cring R),
  ring_eq_ext addition multiplication opposite cring_eq.
intros. apply mk_reqe; set_cring_notations;intros. 
cring_rewrite H0. cring_rewrite H. rrefl.
cring_rewrite H0. cring_rewrite H. rrefl.
 cring_rewrite H. rrefl. Defined.

Lemma cring_almost_ring_theory: forall (R:Type)(Rr:Cring R),
   almost_ring_theory 0 1 addition multiplication subtraction opposite cring_eq.
intros. apply mk_art ; set_cring_notations;intros.
cring_rewrite cring_add_0_l; rrefl. 
cring_rewrite cring_add_comm; rrefl. 
cring_rewrite cring_add_assoc; rrefl. 
cring_rewrite cring_mul_1_l; rrefl. 
apply cring_mul_0_l.
cring_rewrite cring_mul_comm; rrefl. 
cring_rewrite cring_mul_assoc; rrefl. 
cring_rewrite cring_distr_l; rrefl. 
cring_rewrite cring_opp_mul_l; rrefl. 
apply cring_opp_add.
cring_rewrite cring_sub_def ; rrefl. Defined.

Lemma cring_morph:  forall (R:Type)(Rr:Cring R),
  ring_morph  0 1 addition multiplication subtraction opposite cring_eq
             0%Z 1%Z Zplus Zmult Zminus Zopp Zeq_bool
             (@gen_phiZ _ _).
intros. apply mkmorph ; intros; simpl; try rrefl; set_cring_notations.
cring_rewrite gen_phiZ_add; rrefl.
cring_rewrite cring_sub_def. unfold Zminus. cring_rewrite gen_phiZ_add.
cring_rewrite gen_phiZ_opp; rrefl.
cring_rewrite gen_phiZ_mul; rrefl.
cring_rewrite gen_phiZ_opp; rrefl.
rewrite (Zeqb_ok x y H). rrefl. Defined.

Lemma cring_power_theory :  forall (R:Type)(Rr:Cring R),
  power_theory 1 (@multiplication _ _ (@multiplication_cring R Rr)) cring_eq (fun n:N => n)
  (@Ring_theory.pow_N _  1 multiplication).
intros; apply mkpow_th; set_cring_notations. rrefl. Defined.

Lemma cring_div_theory: forall (R:Type)(Rr:Cring R),
  div_theory cring_eq Zplus Zmult (gen_phiZ Rr) Zquotrem.
intros. apply InitialRing.Ztriv_div_th. unfold Setoid_Theory.
simpl.   apply (@cring_setoid R Rr). Defined.

Ltac cring_gen :=
  match goal with
    |- ?g => let lterm := lterm_goal g in (* les variables *)
        match eval red in (list_reifyl (lterm:=lterm)) with
          | (?fv, ?lexpr) => 
(*         idtac "variables:";idtac fv;
           idtac "terms:"; idtac lterm;
           idtac "reifications:"; idtac lexpr; 
           *)
            let lv := fresh "lvar" in
              set (lv := fv);
                reify_goal lv lexpr lterm;
                match goal with 
                  |- ?g => 
                    set_cring_notations ; unfold lv;
                      generalize (@ring_correct _ 0 1 addition multiplication subtraction opposite 
                        cring_eq
                        cring_setoid (@cring_eq_ext _ _) (@cring_almost_ring_theory _ _)
                        Z 0%Z 1%Z Zplus Zmult Zminus Zopp Zeq_bool
                        (@gen_phiZ _ _) (@cring_morph _ _) N (fun n:N => n)
                        (@Ring_theory.pow_N _  1 multiplication)
                        (@cring_power_theory _ _) Zquotrem (@cring_div_theory _ _) O fv nil);
                      set_cring_notations;
                      let rc := fresh "rc"in
                        intro rc; apply rc
                end
        end
  end.

Ltac cring_compute:= vm_compute; reflexivity.

Ltac cring:= 
  unset_cring_notations; intros;
  unfold multiplication_phi_cring; simpl gen_phiZ;
  match goal with
    |- (@cring_eq ?r ?rd _ _ ) =>
          cring_gen; cring_compute
  end.

(* Tests *)

Variable R: Type.
Variable Rr: Cring R.
Existing Instance Rr.

(* reification: 0,7s
sinon, le reste de la tactique donne le même temps que ring 
*)
Goal forall x y z  t u :R, (x + y + z + t + u)^13%N == (u + t + z + y + x) ^13%N.
Time cring. (*Finished transaction in 0. secs (0.410938u,0.s)*)
Qed.
(*
Goal forall x y z  t u :R, (x + y + z + t + u)^16%N == (u + t + z + y + x) ^16%N.
Time cring.(*Finished transaction in 1. secs (0.968852u,0.001s)*)
Qed.
*)
(*
Require Export Ring.
Open Scope Z_scope.
Goal forall x y z  t u :Z, (x + y + z + t + u)^13 = (u + t + z + y + x) ^13.
intros.
Time ring.(*Finished transaction in 0. secs (0.371944u,0.s)*)
Qed.

Goal forall x y z  t u :Z, (x + y + z + t + u)^16 = (u + t + z + y + x) ^16.
intros.
Time ring.(*Finished transaction in 1. secs (0.914861u,0.s)*)
Qed.
*)

(*
Goal forall x y z:R, x + y  == y + x + 0 .
cring.
Qed.

Goal forall x y z:R, x * y * z == x * (y * z).
cring.
Qed.

Goal forall x y z:R, 3%Z * x * (2%Z * y * z) == 6%Z * (x * y) * z.
cring.
Qed.

Goal forall x y z:R, x ^ 2%N == x * x.
cring.
Qed.
*)

