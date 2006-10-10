(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Ring_tac BinList Ring_polynom InitialRing.
Require Export Field_theory.

 (* syntaxification *)
 Ltac mkFieldexpr C Cst radd rmul rsub ropp rdiv rinv t fv := 
 let rec mkP t :=
    match Cst t with
    | Ring_tac.NotConstant =>
        match t with 
        | (radd ?t1 ?t2) => 
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(FEadd e1 e2)
        | (rmul ?t1 ?t2) => 
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(FEmul e1 e2)
        | (rsub ?t1 ?t2) => 
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(FEsub e1 e2)
        | (ropp ?t1) =>
          let e1 := mkP t1 in constr:(FEopp e1)
        | (rdiv ?t1 ?t2) => 
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(FEdiv e1 e2)
        | (rinv ?t1) =>
          let e1 := mkP t1 in constr:(FEinv e1)
        | _ =>
          let p := Find_at t fv in constr:(@FEX C p)
        end
    | ?c => constr:(FEc c)
    end
 in mkP t.

Ltac FFV Cst add mul sub opp div inv t fv :=
 let rec TFV t fv :=
  match Cst t with
  | Ring_tac.NotConstant =>
      match t with
      | (add ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (mul ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (sub ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (opp ?t1) => TFV t1 fv
      | (div ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (inv ?t1) => TFV t1 fv
      | _ => AddFvTail t fv
      end
  | _ => fv
  end 
 in TFV t fv.

(* simplifying the non-zero condition... *)

Ltac fold_field_cond req rO :=
  let rec fold_concl t :=
    match t with
      ?x /\ ?y =>
        let fx := fold_concl x in let fy := fold_concl y in constr:(fx/\fy)
    | req ?x rO -> False => constr:(~ req x rO)
    | _ => t
    end in
  match goal with
    |- ?t => let ft := fold_concl t in change ft
  end.

Ltac simpl_PCond req rO :=
  protect_fv "field_cond";
  try (exact I);
  fold_field_cond req rO.

(* Rewriting (field_simplify) *)
Ltac Make_field_simplify_tac lemma Cond_lemma req Cst_tac :=
  let Make_tac :=
    match type of lemma with
    | forall l fe nfe,
      _ = nfe -> 
      PCond _ _ _ _ _ _ _ _ _ ->
      req (FEeval ?rO ?radd ?rmul ?rsub ?ropp ?rdiv ?rinv (C:=?C) ?phi l fe)
        _ =>
        let mkFV := FFV Cst_tac radd rmul rsub ropp rdiv rinv in
        let mkFE := mkFieldexpr C Cst_tac radd rmul rsub ropp rdiv rinv in
        let simpl_field H := protect_fv "field" in H in
(*unfold Pphi_dev in H;simpl in H in *)
        (fun f rl => (f mkFV mkFE simpl_field lemma req rl;
                      try (apply Cond_lemma; simpl_PCond req rO)))
    | _ => fail 1 "field anomaly: bad correctness lemma (rewr)"
    end in
  Make_tac ReflexiveRewriteTactic.
(* Pb: second rewrite are applied to non-zero condition of first rewrite... *)


(* Generic form of field tactics *)
Ltac Field_Scheme FV_tac SYN_tac SIMPL_tac lemma Cond_lemma req :=
  let ParseLemma :=
    match type of lemma with
    | forall l fe1 fe2 nfe1 nfe2, _ = nfe1 -> _ = nfe2 -> _ -> 
      PCond _ _ _ _ _ _ _ _ _ ->
      req (@FEeval ?R ?rO _ _ _ _ _ _ _ _ l fe1) _ =>
        (fun f => f R rO)
    | _ => fail 1 "field anomaly: bad correctness lemma (scheme)" 
    end in
  let ParseExpr2 ilemma :=
    match type of ilemma with
      forall nfe1 nfe2, ?fe1 = nfe1 -> ?fe2 = nfe2 -> _ => (fun f => f fe1 fe2)
    | _ => fail 1 "field anomaly: cannot find norm expression"
    end in
  let Main r1 r2 R rO :=
    let fv := FV_tac r1 (@List.nil R) in
    let fv := FV_tac r2 fv in
    let fe1 := SYN_tac r1 fv in
    let fe2 := SYN_tac r2 fv in
    let nfrac1 := fresh "frac1" in 
    let norm_hyp1 := fresh "norm_frac1" in
    let nfrac2 := fresh "frac2" in 
    let norm_hyp2 := fresh "norm_frac2" in
    ParseExpr2 (lemma fv fe1 fe2)
    ltac:(fun nfrac_val1 nfrac_val2 =>
          (compute_assertion norm_hyp1 nfrac1 nfrac_val1;
           compute_assertion norm_hyp2 nfrac2 nfrac_val2;
           (apply (lemma fv fe1 fe2 nfrac1 nfrac2 norm_hyp1 norm_hyp2)
            || fail "field anomaly: failed in applying lemma");
           [ SIMPL_tac | apply Cond_lemma; simpl_PCond req rO];
           try clear nfrac1 nfrac2 norm_hyp1 norm_hyp2)) in
  ParseLemma ltac:(OnEquation req Main).


Ltac ParseFieldComponents lemma req :=
  match type of lemma with
  | forall l fe1 fe2 nfe1 nfe2,
    _ = nfe1 -> _ = nfe2 -> _ -> PCond _ _ _ _ _ _ _ _ _ ->
    req (@FEeval ?R ?rO ?add ?mul ?sub ?opp ?div ?inv ?C ?phi l fe1) _ =>
      (fun f => f add mul sub opp div inv C)
  | _ => fail 1 "field anomaly: bad correctness lemma (parse)"
  end.

(* solve completely a field equation, leaving non-zero conditions to be
   proved (field) *)
Ltac Make_field_tac lemma Cond_lemma req Cst_tac :=
  let Main radd rmul rsub ropp rdiv rinv C :=
    let mkFV := FFV Cst_tac radd rmul rsub ropp rdiv rinv in
    let mkFE := mkFieldexpr C Cst_tac radd rmul rsub ropp rdiv rinv in
    let Simpl :=
      vm_compute; (reflexivity || fail "not a valid field equation") in
    Field_Scheme mkFV mkFE Simpl lemma Cond_lemma req in
  ParseFieldComponents lemma req Main.

(* transforms a field equation to an equivalent (simplified) ring equation,
   and leaves non-zero conditions to be proved (field_simplify_eq) *)
Ltac Make_field_simplify_eq_tac lemma Cond_lemma req Cst_tac :=
  let Main radd rmul rsub ropp rdiv rinv C :=
    let mkFV := FFV Cst_tac radd rmul rsub ropp rdiv rinv in
    let mkFE := mkFieldexpr C Cst_tac radd rmul rsub ropp rdiv rinv in
    let Simpl := (protect_fv "field") in
    Field_Scheme mkFV mkFE Simpl lemma Cond_lemma req in
  ParseFieldComponents lemma req Main.
