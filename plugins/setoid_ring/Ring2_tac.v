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
Open Scope Z_scope.
Require Import Algebra_syntax.
Require Export Ring2.
Require Import Ring2_polynom.
Require Import Ring2_initial.


Set Implicit Arguments.

(* Reification with Type Classes, inspired from B.Grégoire and A.Spiewack *)

Class is_in_list_at (R:Type) (t:R) (l:list R) (i:nat) := {}.
Instance  Ifind0 (R:Type) (t:R) l
 : is_in_list_at t (t::l) 0.
Instance  IfindS (R:Type) (t2 t1:R) l i 
 `{is_in_list_at R t1 l i} 
 : is_in_list_at t1 (t2::l) (S i) | 1.

Class reifyPE (R:Type) (e:PExpr Z) (lvar:list R) (t:R) := {}.
Instance  reify_zero (R:Type) (RR:Ring R) lvar 
 : reifyPE (PEc 0%Z) lvar ring0.
Instance  reify_one (R:Type) (RR:Ring R) lvar 
 : reifyPE (PEc 1%Z) lvar ring1.
Instance  reify_plus (R:Type)  (RR:Ring R)
  e1 lvar t1 e2 t2 
 `{reifyPE R e1 lvar t1} 
 `{reifyPE R e2 lvar t2} 
 : reifyPE (PEadd e1 e2) lvar (ring_plus t1 t2).
Instance  reify_mult (R:Type)  (RR:Ring R)
  e1 lvar t1 e2 t2 
 `{reifyPE R e1 lvar t1} 
 `{reifyPE R e2 lvar t2}
 : reifyPE (PEmul e1 e2) lvar (ring_mult t1 t2).
Instance  reify_sub (R:Type) (RR:Ring R) 
 e1 lvar t1 e2 t2 
 `{reifyPE R e1 lvar t1} 
 `{reifyPE R e2 lvar t2}
 : reifyPE (PEsub e1 e2) lvar (ring_sub t1 t2).
Instance  reify_opp (R:Type) (RR:Ring R) 
 e1 lvar t1 
 `{reifyPE R e1 lvar t1}
 : reifyPE (PEopp e1) lvar (ring_opp t1).
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

Class is_closed_list T (l:list T) := {}.
Instance Iclosed_nil T 
 : is_closed_list (T:=T) nil.
Instance Iclosed_cons T t l 
 `{is_closed_list (T:=T) l} 
 : is_closed_list (T:=T) (t::l).

Definition list_reifyl (R:Type) lexpr lvar lterm 
 `{reifyPElist R lexpr lvar lterm}
 `{is_closed_list (T:=R) lvar} := (lvar,lexpr).

Unset Implicit Arguments.

Instance multiplication_phi_ring{R:Type}{Rr:Ring R} : Multiplication  :=
  {multiplication x y := ring_mult (gen_phiZ Rr x) y}.

(*
Print HintDb typeclass_instances.
*)
(* Reification *)

Ltac lterm_goal g :=
  match g with
  ring_eq ?t1 ?t2 => constr:(t1::t2::nil)
  | ring_eq ?t1 ?t2 -> ?g => let lvar :=
    lterm_goal g in constr:(t1::t2::lvar)     
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
             (@PEeval Z Zr _ _ (@gen_phiZ_morph _ _) N
                      (fun n:N => n) (@Ring_theory.pow_N _ ring1 ring_mult)
                      lvar e); 
           clear x;
           reify_goal lvar lexpr1 lterm1
        end
  end.

Existing Instance gen_phiZ_morph.
Existing Instance Zr.

Lemma comm: forall (R:Type)(Rr:Ring R)(c : Z) (x : R),
  x * [c] == [c] * x.
induction c. intros. ring_simpl. gen_ring_rewrite. simpl. intros.
ring_rewrite_rev same_gen.
induction p. simpl.  gen_ring_rewrite. ring_rewrite IHp. rrefl.
simpl.  gen_ring_rewrite. ring_rewrite IHp. rrefl.
simpl.  gen_ring_rewrite. 
simpl. intros. ring_rewrite_rev same_gen.
induction p. simpl. generalize IHp. clear IHp.
gen_ring_rewrite. intro IHp.  ring_rewrite IHp. rrefl.
simpl. generalize IHp. clear IHp.
gen_ring_rewrite. intro IHp.  ring_rewrite IHp. rrefl.
simpl.  gen_ring_rewrite. Qed.

Lemma Zeqb_ok: forall x y : Z, Zeq_bool x y = true -> x == y.
 intros x y H. rewrite (Zeq_bool_eq x y H). rrefl. Qed. 


 Ltac ring_gen :=
   match goal with
     |- ?g => let lterm := lterm_goal g in (* les variables *)
       match eval red in (list_reifyl (lterm:=lterm)) with
         | (?fv, ?lexpr) => 
(*         idtac "variables:";idtac fv;
           idtac "terms:"; idtac lterm;
           idtac "reifications:"; idtac lexpr; 
*)
           reify_goal fv lexpr lterm;
           match goal with 
             |- ?g => 
               set_ring_notations;
               apply (@ring_correct Z Zr _ _ (@gen_phiZ_morph _ _)
                 (@comm _ _) Zeq_bool Zeqb_ok N (fun n:N => n)
                 (@Ring_theory.pow_N _  1 multiplication));
               [apply mkpow_th; rrefl
                 |vm_compute; reflexivity]
           end
       end
   end.
 
Ltac ring2:= 
  unset_ring_notations; intros;
  match goal with
    |- (@ring_eq ?r ?rd _ _ ) =>
          simpl; ring_gen
  end.
Variable R: Type.
Variable Rr: Ring R.
Existing Instance Rr.

Goal forall x y z:R, x  == x .
ring2. 
Qed.

Goal forall x y z:R, x * y * z == x * (y * z).
ring2.
Qed.

Goal forall x y z:R, [3]* x *([2]* y * z) == [6] * (x * y) * z.
ring2.
Qed.

Goal forall x y z:R, 3 * x * (2 * y * z) == 6 * (x * y) * z.
ring2.
Qed.


(* Fails with Multiplication: A -> B -> C.
Goal forall x:R,    2%Z * (x * x) == 3%Z * x.
Admitted.
*)