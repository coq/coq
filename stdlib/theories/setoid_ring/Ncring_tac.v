(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

Ltac reify_as_var_aux n lvar term :=
  lazymatch lvar with
  | @cons _ ?t0 ?tl =>
      let conv :=
        match goal with
        | _ => let _ := match goal with _ => convert term t0 end in open_constr:(true)
        | _ => open_constr:(false)
        end
      in
      lazymatch conv with
      | true => n
      | false => reify_as_var_aux open_constr:(S n) tl term
      end
  | _ =>
      let _ := open_constr:(eq_refl : lvar = @cons _ term _) in
      n
  end.

Ltac reify_as_var lvar term := reify_as_var_aux Datatypes.O lvar term.

Ltac close_varlist lvar :=
  lazymatch lvar with
  | @nil _ => idtac
  | @cons _ _ ?tl => close_varlist tl
  | _ => let _ := constr:(eq_refl : lvar = @nil _) in idtac
  end.

(* extensibility: override to add ways to reify a term.
   Return [tt] for terms which aren't handled (tt doesn't have type PExpr so is unambiguous) *)
Ltac extra_reify term := open_constr:(tt).

Ltac reify_term R ring0 ring1 add mul sub opp lvar term :=
  let reify_term x := reify_term R ring0 ring1 add mul sub opp lvar x in
  match term with
  (* int literals *)
  | Z0 => open_constr:(PEc 0%Z)
  | Zpos ?p => open_constr:(PEc (Zpos p))
  | Zneg ?p => open_constr:(PEc (Zneg p))

  (* ring constants *)
  | _ =>
    let _ := lazymatch goal with _ => convert ring0 term end in
    open_constr:(PEc 0%Z)
  | _ =>
    let _ := lazymatch goal with _ => convert ring1 term end in
    open_constr:(PEc 1%Z)

  (* binary operators *)
  | ?op ?t1 ?t2 =>
    (* quick(?) check op is of the right type? TODO try without this check *)
    let _ := open_constr:(t1 : R) in
    let _ := open_constr:(t2 : R) in
    match tt with
    | _ =>
      let _ := lazymatch goal with _ => convert add op end in
      (* NB: don't reify before we recognize the operator in case we can't recognire it *)
      let et1 := reify_term t1 in
      let et2 := reify_term t2 in
      open_constr:(PEadd et1 et2)
    | _ =>
      let _ := lazymatch goal with _ => convert mul op end in
      let et1 := reify_term t1 in
      let et2 := reify_term t2 in
      open_constr:(PEmul et1 et2)
    | _ =>
      let _ := lazymatch goal with _ => convert sub op end in
      let et1 := reify_term t1 in
      let et2 := reify_term t2 in
      open_constr:(PEsub et1 et2)
    end

  (* unary operator (opposite) *)
  | ?op ?t =>
    let _ := lazymatch goal with _ => convert opp op end in
    let et := reify_term t in
    open_constr:(PEopp et)

  (* special cases (XXX can/should we be less syntactic?) *)
  | @multiplication Z _ _ ?z ?t =>
    let et := reify_term t in
    open_constr:(PEmul (PEc z) et)
  | pow_N ?t ?n =>
    let et := reify_term t in
    open_constr:(PEpow et n)
  | @power _ _ power_ring ?t ?n =>
    let et := reify_term t in
    open_constr:(PEpow et (ZN n))

  (* extensibility and variable case *)
  | _ =>
    let extra := extra_reify term in
    lazymatch extra with
    | tt =>
      let n := reify_as_var lvar term in
      open_constr:(PEX Z (Pos.of_succ_nat n))
    | ?v => v
    end
  end.

Ltac list_reifyl_core Tring lvar lterm :=
  lazymatch lterm with
  | @nil _ => open_constr:(@nil (PExpr Z))
  | @cons _ ?t ?tl =>
      lazymatch Tring with
      | Ring (T:=?R) (ring0:=?ring0) (ring1:=?ring1)
          (add:=?add) (mul:=?mul) (sub:=?sub) (opp:=?opp) =>
        let et := reify_term R ring0 ring1 add mul sub opp lvar t in
        let etl := list_reifyl_core Tring lvar tl in
        open_constr:(@cons (PExpr Z) et etl)
      end
  end.

Ltac list_reifyl lvar lterm :=
  lazymatch lterm with
  | @cons ?R _ _ =>
      let R_ring := constr:(_ :> Ring (T:=R)) in
      let Tring := type of R_ring in
      let lexpr := list_reifyl_core Tring lvar lterm in
      let _ := lazymatch goal with _ => close_varlist lvar end in
      constr:((lvar,lexpr))
  end.

Ltac list_reifyl0 lterm :=
  lazymatch lterm with
  | @cons ?R _ _ =>
      let lvar := open_constr:(_ :> list R) in
      list_reifyl lvar lterm
  end.

Class ReifyL {R:Type} (lvar lterm : list R) := list_reifyl : (list R * list (PExpr Z)).
Arguments list_reifyl {R lvar lterm _}.

Global Hint Extern 0 (ReifyL ?lvar ?lterm) => let reif := list_reifyl lvar lterm in exact reif : typeclass_instances.

Unset Implicit Arguments.

Ltac lterm_goal g :=
  match g with
  | ?t1 == ?t2 => constr:(t1::t2::nil)
  | ?t1 = ?t2 => constr:(t1::t2::nil)
  | (_ ?t1 ?t2) => constr:(t1::t2::nil)
  end.

Lemma Private_Zeqb_ok: forall x y : Z, Z.eqb x y = true -> x == y.
Proof. intros x y ->%Z.eqb_eq. reflexivity. Qed.

#[deprecated(use=Z.eqb_eq, since="9.0")]
Notation Zeqb_ok := Private_Zeqb_ok (only parsing).


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
  induction c.
  - intros. simpl. gen_rewrite.
  - simpl. intros.
    rewrite <- same_gen.
    induction p.
    + simpl.  gen_rewrite. rewrite IHp. reflexivity.
    + simpl.  gen_rewrite. rewrite IHp. reflexivity.
    + simpl.  gen_rewrite.
  - simpl. intros. rewrite <- same_gen.
    induction p.
    + simpl. generalize IHp. clear IHp.
      gen_rewrite. intro IHp.  rewrite IHp. reflexivity.
    + simpl. generalize IHp. clear IHp.
      gen_rewrite. intro IHp.  rewrite IHp. reflexivity.
    + simpl.  gen_rewrite.
Qed.

Ltac ring_gen :=
   match goal with
     |- ?g =>
       let lterm := lterm_goal g in
       let reif := list_reifyl0 lterm in
       match reif with
         | (?fv, ?lexpr) =>
           (*idtac "variables:";idtac fv;
           idtac "terms:"; idtac lterm;
           idtac "reifications:"; idtac lexpr; *)
           reify_goal fv lexpr lterm;
           match goal with
             |- ?g =>
               apply (@ring_correct Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                       (@gen_phiZ _ _ _ _ _ _ _ _ _) _
                 (@comm _ _ _ _ _ _ _ _ _ _) Z.eqb Private_Zeqb_ok N (fun n:N => n)
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
          Z 0%Z 1%Z Z.add Z.mul Z.sub Z.opp (@eq Z) Zops Z.eqb e) in
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
          (@comm _ 0 1 _+_ _*_ _-_ -_ _==_ _ _) _ Private_Zeqb_ok);
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
   let reif := list_reifyl0 lterm in
    match reif with
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
