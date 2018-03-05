(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export List.
Require Import Setoid.
Require Import BinPos.
Require Import BinList.
Require Import Znumtheory.
Require Export Morphisms Setoid Bool.
Require Import ZArith_base.
Require Export Algebra_syntax.
Require Export Ncring.
Require Export Ncring_initial.
Require Export Ncring_tac.

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
               _ zero one _+_ _*_ _-_ -_ Z Ncring_initial.gen_phiZ N (fun n:N => n)
               (@Ring_theory.pow_N _ 1 multiplication) lvar e1)
             (@Ring_polynom.PEeval
               _ zero one _+_ _*_ _-_ -_ Z Ncring_initial.gen_phiZ N (fun n:N => n)
               (@Ring_theory.pow_N _ 1 multiplication) lvar e2))
        end
  end.

Section cring.
Context {R:Type}`{Rr:Cring R}.

Lemma cring_eq_ext: ring_eq_ext _+_ _*_ -_ _==_.
Proof.
intros. apply mk_reqe; solve_proper.
Defined.

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
             0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zeq_bool
             Ncring_initial.gen_phiZ.
intros. apply mkmorph ; intros; simpl; try reflexivity.
rewrite Ncring_initial.gen_phiZ_add; reflexivity.
rewrite ring_sub_def. unfold Z.sub. rewrite Ncring_initial.gen_phiZ_add.
rewrite Ncring_initial.gen_phiZ_opp; reflexivity.
rewrite Ncring_initial.gen_phiZ_mul; reflexivity.
rewrite Ncring_initial.gen_phiZ_opp; reflexivity.
rewrite (Zeqb_ok x y H). reflexivity. Defined.

Lemma cring_power_theory : 
  @Ring_theory.power_theory R one _*_ _==_ N (fun n:N => n)
  (@Ring_theory.pow_N _  1 multiplication).
intros; apply Ring_theory.mkpow_th. reflexivity. Defined.

Lemma cring_div_theory: 
  div_theory _==_ Z.add Z.mul Ncring_initial.gen_phiZ Z.quotrem.
intros. apply InitialRing.Ztriv_div_th. unfold Setoid_Theory.
simpl.   apply ring_setoid. Defined.

End cring.

Ltac cring_gen :=
  match goal with
    |- ?g => let lterm := lterm_goal g in
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
                        Z 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zeq_bool
                        Ncring_initial.gen_phiZ
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

Instance Zcri: (Cring (Rr:=Zr)).
red. exact Z.mul_comm. Defined.

(* Cring_simplify *)

Ltac cring_simplify_aux lterm fv lexpr hyp :=
    match lterm with
      | ?t0::?lterm =>
    match lexpr with
      | ?e::?le =>
        let t := constr:(@Ring_polynom.norm_subst
          Z 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zeq_bool Z.quotrem O nil e) in
        let te := 
          constr:(@Ring_polynom.Pphi_dev
            _ 0 1 _+_ _*_ _-_ -_ 
            
            Z 0%Z 1%Z Zeq_bool
            Ncring_initial.gen_phiZ
            get_signZ fv t) in
        let eq1 := fresh "ring" in
        let nft := eval vm_compute in t in
        let t':= fresh "t" in
        pose (t' := nft);
        assert (eq1 : t = t');
        [vm_cast_no_check (eq_refl t')|
        let eq2 := fresh "ring" in
        assert (eq2:(@Ring_polynom.PEeval
          _ zero _+_ _*_ _-_ -_ Z Ncring_initial.gen_phiZ N (fun n:N => n)
          (@Ring_theory.pow_N _ 1 multiplication) fv e) == te);
        [let eq3 := fresh "ring" in
          generalize (@ring_rw_correct _ 0 1 _+_ _*_ _-_ -_ _==_
            ring_setoid
            cring_eq_ext
            cring_almost_ring_theory
            Z 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zeq_bool
            Ncring_initial.gen_phiZ
            cring_morph
            N
            (fun n:N => n)
            (@Ring_theory.pow_N _ 1 multiplication)
            cring_power_theory
            Z.quotrem
            cring_div_theory
            get_signZ get_signZ_th
            O nil fv I nil (eq_refl nil) );
          intro eq3; apply eq3; reflexivity|
              match hyp with
                | 1%nat => rewrite eq2
                | ?H => try rewrite eq2 in H
              end];
        let P:= fresh "P" in
        match hyp with
          | 1%nat => 
            rewrite eq1;
            pattern (@Ring_polynom.Pphi_dev
            _ 0 1 _+_ _*_ _-_ -_ 
            
            Z 0%Z 1%Z Zeq_bool
            Ncring_initial.gen_phiZ
            get_signZ fv t');
            match goal with
              |- (?p ?t) => set (P:=p)
            end;
              unfold t' in *; clear t' eq1 eq2;
              unfold Pphi_dev, Pphi_avoid; simpl;
                repeat (unfold mkmult1, mkmultm1, mkmult_c_pos, mkmult_c,
                  mkadd_mult, mkmult_c_pos, mkmult_pow, mkadd_mult,
                  mkpow;simpl)
          | ?H =>
               rewrite eq1 in H;
               pattern (@Ring_polynom.Pphi_dev
            _ 0 1 _+_ _*_ _-_ -_ 
            
            Z 0%Z 1%Z Zeq_bool
            Ncring_initial.gen_phiZ
            get_signZ fv t') in H; 
               match type of H with
                  | (?p ?t)  => set (P:=p) in H
               end;
               unfold t' in *; clear t' eq1 eq2;
               unfold Pphi_dev, Pphi_avoid in H; simpl in H;
                repeat (unfold mkmult1, mkmultm1, mkmult_c_pos, mkmult_c,
                  mkadd_mult, mkmult_c_pos, mkmult_pow, mkadd_mult,
                  mkpow in H;simpl in H)
        end; unfold P in *; clear P
        ]; cring_simplify_aux lterm fv le hyp
      | nil => idtac
    end
    | nil => idtac
    end.

Ltac set_variables fv :=
  match fv with
    | nil => idtac
    | ?t::?fv =>
        let v := fresh "X" in
        set (v:=t) in *; set_variables fv
  end.

Ltac deset n:=
   match n with
    | 0%nat => idtac
    | S ?n1 =>
      match goal with
        | h:= ?v : ?t |- ?g => unfold h in *; clear h; deset n1
      end
   end.

(* a est soit un terme de l'anneau, soit une liste de termes.
J'ai pas réussi à un décomposer les Vlists obtenues avec ne_constr_list
 dans Tactic Notation *)

Ltac cring_simplify_gen a hyp :=
  let lterm :=
    match a with
      | _::_ => a
      | _ => constr:(a::nil)
    end in
    match eval red in (list_reifyl (lterm:=lterm)) with
      | (?fv, ?lexpr) => idtac lterm; idtac fv; idtac lexpr;
      let n := eval compute in (length fv) in
      idtac n;
      let lt:=fresh "lt" in
      set (lt:= lterm);
      let lv:=fresh "fv" in
      set (lv:= fv);
      (* les termes de fv sont remplacés par des variables 
         pour pouvoir utiliser simpl ensuite sans risquer
         des simplifications indésirables *)
      set_variables fv;
      let lterm1 := eval unfold lt in lt in
      let lv1 := eval unfold lv in lv in
        idtac lterm1; idtac lv1;
      cring_simplify_aux lterm1 lv1 lexpr hyp;
      clear lt lv;
      (* on remet les termes de fv *)
      deset n
    end.

Tactic Notation "cring_simplify" constr(lterm):=
 cring_simplify_gen lterm 1%nat.

Tactic Notation "cring_simplify" constr(lterm) "in" ident(H):=
 cring_simplify_gen lterm H.

