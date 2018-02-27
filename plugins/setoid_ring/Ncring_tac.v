(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import List.
Require Import Setoid.
Require Import BinPos.
Require Import BinList.
Require Import Znumtheory.
Require Export Morphisms Setoid Bool.
Require Import ZArith.
Require Import Algebra_syntax.
Require Export Ncring.
Require Import Ncring_polynom.
Require Import Ncring_initial.


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

Instance  reifyZ0 (R:Type)  lvar 
 `{Ring (T:=R)}
 : reify (PEc Z0) lvar Z0|11.

Instance  reifyZpos (R:Type)  lvar (p:positive)
 `{Ring (T:=R)}
 : reify (PEc (Zpos p)) lvar (Zpos p)|11.

Instance  reifyZneg (R:Type)  lvar (p:positive)
 `{Ring (T:=R)}
 : reify (PEc (Zneg p)) lvar (Zneg p)|11.

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
 : reify (mul:=op) (PEmul e1 e2) lvar (op t1 t2)|10.

Instance  reify_mul_ext (R:Type) `{Ring R}
  lvar (z:Z) e2 t2 
 `{Ring (T:=R)}
 {_:reify e2 lvar t2}
 : reify (PEmul (PEc z) e2) lvar
      (@multiplication Z _ _ z t2)|9.

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
 : reify (Rr:= Rr) (PEX Z (Pos.of_succ_nat i))lvar t
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
  | (_ ?t1 ?t2) => constr:(t1::t2::nil)
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

Ltac non_commutative_ring:= 
  intros;
  ring_gen.

(* simplification *)

Ltac ring_simplify_aux lterm fv lexpr hyp :=
    match lterm with
      | ?t0::?lterm =>
    match lexpr with
      | ?e::?le => (* e:PExpr Z est la réification de t0:R *)
        let t := constr:(@Ncring_polynom.norm_subst
          Z 0%Z 1%Z Z.add Z.mul Z.sub Z.opp (@eq Z) Zops Zeq_bool e) in
        (* t:Pol Z *)
        let te := 
          constr:(@Ncring_polynom.Pphi Z 
            _ 0 1 _+_ _*_ _-_ -_ _==_ _ Ncring_initial.gen_phiZ fv t) in
        let eq1 := fresh "ring" in
        let nft := eval vm_compute in t in
        let t':= fresh "t" in
        pose (t' := nft);
        assert (eq1 : t = t');
        [vm_cast_no_check (eq_refl t')|
        let eq2 := fresh "ring" in
        assert (eq2:(@Ncring_polynom.PEeval Z
          _ 0 1 _+_ _*_ _-_ -_ _==_ _ Ncring_initial.gen_phiZ N (fun n:N => n) 
          (@Ring_theory.pow_N _ 1 multiplication) fv e) == te);
        [apply (@Ncring_polynom.norm_subst_ok
          Z _ 0%Z 1%Z Z.add Z.mul Z.sub Z.opp (@eq Z)
          _ _ 0 1 _+_ _*_ _-_ -_ _==_ _ _ Ncring_initial.gen_phiZ _
          (@comm _ 0 1 _+_ _*_ _-_ -_ _==_ _ _) _ Zeqb_ok);
           apply mkpow_th; reflexivity
          | match hyp with
                | 1%nat => rewrite eq2
                | ?H => try rewrite eq2 in H
              end];
        let P:= fresh "P" in
        match hyp with
          | 1%nat => idtac "ok";
            rewrite eq1;
            pattern (@Ncring_polynom.Pphi Z _ 0 1 _+_ _*_ _-_ -_ _==_
              _ Ncring_initial.gen_phiZ fv t');
            match goal with
              |- (?p ?t) => set (P:=p)
            end;
              unfold t' in *; clear t' eq1 eq2; simpl
          | ?H =>
               rewrite eq1 in H;
               pattern (@Ncring_polynom.Pphi Z _ 0 1 _+_ _*_ _-_ -_ _==_
                  _ Ncring_initial.gen_phiZ fv t') in H; 
               match type of H with
                  | (?p ?t)  => set (P:=p) in H
               end;
               unfold t' in *; clear t' eq1 eq2; simpl in H
        end; unfold P in *; clear P
        ]; ring_simplify_aux lterm fv le hyp
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

Ltac ring_simplify_gen a hyp :=
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
      ring_simplify_aux lterm1 lv1 lexpr hyp;
      clear lt lv;
      (* on remet les termes de fv *)
      deset n
    end.

Tactic Notation "non_commutative_ring_simplify" constr(lterm):=
 ring_simplify_gen lterm 1%nat.

Tactic Notation "non_commutative_ring_simplify" constr(lterm) "in" ident(H):=
 ring_simplify_gen lterm H.


