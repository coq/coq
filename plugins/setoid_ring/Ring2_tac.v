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
Require Import Algebra_syntax.
Require Export Ring2.
Require Import Ring2_polynom.
Require Import Ring2_initial.


Set Implicit Arguments.

Class nth (R:Type) (t:R) (l:list R) (i:nat).

Instance  Ifind0 (R:Type) (t:R) l
 : nth t(t::l) 0.

Instance  IfindS (R:Type) (t2 t1:R) l i 
 {_:nth t1 l i} 
 : nth t1 (t2::l) (S i) | 1.

Class closed (T:Type) (l:list T).

Instance Iclosed_nil T 
 : closed (T:=T) nil.

Instance Iclosed_cons T t (l:list T) 
 {_:closed l} 
 : closed (t::l).

Class reify (R:Type)`{Rr:Ring (T:=R)} (e:PExpr Z) (lvar:list R) (t:R).

Instance  reify_zero (R:Type)  lvar op
 `{Ring (T:=R)(ring0:=op)}
 : reify (ring0:=op)(PEc 0%Z) lvar op.

Instance  reify_one (R:Type)  lvar op
 `{Ring (T:=R)(ring1:=op)}
 : reify (ring1:=op) (PEc 1%Z) lvar op.

Instance  reify_add (R:Type)
  e1 lvar t1 e2 t2 op 
 `{Ring (T:=R)(add:=op)}
 {_:reify (add:=op) e1 lvar t1}
 {_:reify (add:=op) e2 lvar t2}
 : reify (add:=op) (PEadd e1 e2) lvar (op t1 t2).

Instance  reify_mul (R:Type) 
  e1 lvar t1 e2 t2 op 
 `{Ring (T:=R)(mul:=op)}
 {_:reify (mul:=op) e1 lvar t1}
 {_:reify (mul:=op) e2 lvar t2}
 : reify (mul:=op) (PEmul e1 e2) lvar (op t1 t2).

Instance  reify_mul_ext (R:Type) `{Ring R}
  lvar z e2 t2 
 `{Ring (T:=R)}
 {_:reify e2 lvar t2}
 : reify (PEmul (PEc z) e2) lvar
      (@multiplication Z _ _  z t2)|9.

Instance  reify_sub (R:Type)
 e1 lvar t1 e2 t2 op
 `{Ring (T:=R)(sub:=op)}
 {_:reify (sub:=op) e1 lvar t1}
 {_:reify (sub:=op) e2 lvar t2}
 : reify (sub:=op) (PEsub e1 e2) lvar (op t1 t2).

Instance  reify_opp (R:Type)
 e1 lvar t1  op
 `{Ring (T:=R)(opp:=op)}
 {_:reify (opp:=op) e1 lvar t1}
 : reify (opp:=op) (PEopp e1) lvar (op t1).

Instance  reify_pow (R:Type) `{Ring R}
 e1 lvar t1 n 
 `{Ring (T:=R)}
 {_:reify e1 lvar t1}
 : reify (PEpow e1 n) lvar (pow_N t1 n)|1.

Instance  reify_var (R:Type) t lvar i 
 `{nth R t lvar i}
 `{Rr: Ring (T:=R)}
 : reify (Rr:= Rr) (PEX Z (P_of_succ_nat i))lvar t 
 | 100.

Class reifylist (R:Type)`{Rr:Ring (T:=R)} (lexpr:list (PExpr Z)) (lvar:list R) 
  (lterm:list R).

Instance reify_nil (R:Type) lvar 
 `{Rr: Ring (T:=R)}
 : reifylist (Rr:= Rr) nil lvar (@nil R).

Instance reify_cons (R:Type) e1 lvar t1 lexpr2 lterm2
 `{Rr: Ring (T:=R)}
 {_:reify (Rr:= Rr) e1 lvar t1}
 {_:reifylist (Rr:= Rr) lexpr2 lvar lterm2} 
 : reifylist (Rr:= Rr) (e1::lexpr2) lvar (t1::lterm2).

Definition list_reifyl (R:Type) lexpr lvar lterm 
 `{Rr: Ring (T:=R)}
 {_:reifylist (Rr:= Rr) lexpr lvar lterm}
 `{closed (T:=R) lvar}  := (lvar,lexpr).

Unset Implicit Arguments.


Ltac lterm_goal g :=
  match g with
  | ?t1 == ?t2 => constr:(t1::t2::nil)
  | ?t1 = ?t2 => constr:(t1::t2::nil)
  end.

Lemma Zeqb_ok: forall x y : Z, Zeq_bool x y = true -> x == y.
 intros x y H. rewrite (Zeq_bool_eq x y H). reflexivity. Qed. 

Ltac reify_goal lvar lexpr lterm:=
  (*idtac lvar; idtac lexpr; idtac lterm;*)
  match lexpr with
     nil => idtac
   | ?e1::?e2::_ =>  
        match goal with
          |- (?op ?u1 ?u2) =>
           change (op 
             (@PEeval Z _ _ _ _ _ _ _ _ _ (@gen_phiZ _ _ _ _ _ _ _ _ _) N
                      (fun n:N => n) (@pow_N _ _ _ _ _ _ _ _ _)
                      lvar e1)
             (@PEeval Z _ _ _ _ _ _ _ _ _ (@gen_phiZ _ _ _ _ _ _ _ _ _) N
                      (fun n:N => n) (@pow_N _ _ _ _ _ _ _ _ _)
                      lvar e2))
        end
  end.

Lemma comm: forall (R:Type)`{Ring R}(c : Z) (x : R),
  x * (gen_phiZ c) == (gen_phiZ c) * x.
induction c. intros. simpl. gen_rewrite. simpl. intros.
rewrite <- same_gen.
induction p. simpl.  gen_rewrite. rewrite IHp. reflexivity.
simpl.  gen_rewrite. rewrite IHp. reflexivity.
simpl.  gen_rewrite. 
simpl. intros. rewrite <- same_gen.
induction p. simpl. generalize IHp. clear IHp.
gen_rewrite. intro IHp.  rewrite IHp. reflexivity.
simpl. generalize IHp. clear IHp.
gen_rewrite. intro IHp.  rewrite IHp. reflexivity.
simpl.  gen_rewrite. Qed.

Ltac ring_gen :=
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
               apply (@ring_correct Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                       (@gen_phiZ _ _ _ _ _ _ _ _ _) _
                 (@comm _ _ _ _ _ _ _ _ _ _) Zeq_bool Zeqb_ok N (fun n:N => n)
                 (@pow_N _ _ _ _ _ _ _ _ _));
               [apply mkpow_th; reflexivity
                 |vm_compute; reflexivity]
           end
       end
   end.

Ltac ring2:= 
  intros;
  ring_gen.

