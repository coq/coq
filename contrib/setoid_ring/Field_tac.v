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

Ltac ParseFieldComponents lemma :=
  match type of lemma with
  | context [@FEeval ?R ?rO ?add ?mul ?sub ?opp ?div ?inv ?C ?phi _ _] =>
      (fun f => f add mul sub opp div inv C)
  | _ => fail 1 "field anomaly: bad correctness lemma (parse)"
  end.

(* simplifying the non-zero condition... *)

Ltac fold_field_cond req :=
  let rec fold_concl t :=
    match t with
      ?x /\ ?y =>
        let fx := fold_concl x in let fy := fold_concl y in constr:(fx/\fy)
    | req ?x ?y -> False => constr:(~ req x y)
    | _ => t
    end in
  match goal with
    |- ?t => let ft := fold_concl t in change ft
  end.

Ltac simpl_PCond req :=
  protect_fv "field_cond";
  try (exact I);
  fold_field_cond req.

(* Rewriting (field_simplify) *)
Ltac Field_simplify lemma Cond_lemma req Cst_tac :=
  let Make_tac :=
    match type of lemma with
    | forall l fe nfe,
      _ = nfe -> 
      PCond _ _ _ _ _ _ _ _ _ ->
      req (FEeval ?rO ?radd ?rmul ?rsub ?ropp ?rdiv ?rinv (C:=?C) ?phi l fe)
        _ =>
        let mkFV := FFV Cst_tac radd rmul rsub ropp rdiv rinv in
        let mkFE := mkFieldexpr C Cst_tac radd rmul rsub ropp rdiv rinv in
        let field_rw H := (protect_fv "field" in H; rewrite H) in
        fun f rl => f mkFV mkFE field_rw lemma req rl;
                    try (apply Cond_lemma; simpl_PCond req)
    | _ => fail 1 "field anomaly: bad correctness lemma (rewr)"
    end in
  Make_tac ReflexiveNormTactic.
(* Pb: second rewrite are applied to non-zero condition of first rewrite... *)

Tactic Notation (at level 0) "field_simplify" constr_list(rl) :=
  field_lookup
    (fun req cst_tac _ _ field_simplify_ok cond_ok pre post rl =>
       pre(); Field_simplify field_simplify_ok cond_ok req cst_tac rl; post()).


(* Generic form of field tactics *)
Ltac Field_Scheme FV_tac SYN_tac SIMPL_tac lemma Cond_lemma req :=
  let R := match type of req with ?R -> _ => R end in
  let rec ParseExpr ilemma :=
    match type of ilemma with
      forall nfe, ?fe = nfe -> _ =>
        (fun t => 
           let x := fresh "fld_expr" in 
           let H := fresh "norm_fld_expr" in
           compute_assertion H x fe;
           ParseExpr (ilemma x H) t;
           try clear x H)
    | _ => (fun t => t ilemma)
    end in
  let Main r1 r2 :=
    let fv := FV_tac r1 (@List.nil R) in
    let fv := FV_tac r2 fv in
    let fe1 := SYN_tac r1 fv in
    let fe2 := SYN_tac r2 fv in
    ParseExpr (lemma fv fe1 fe2)
    ltac:(fun ilemma =>
           apply ilemma || fail "field anomaly: failed in applying lemma";
            [ SIMPL_tac | apply Cond_lemma; simpl_PCond req]) in
  OnEquation req Main.

(* solve completely a field equation, leaving non-zero conditions to be
   proved (field) *)
Ltac Field lemma Cond_lemma req Cst_tac :=
  let Main radd rmul rsub ropp rdiv rinv C :=
    let mkFV := FFV Cst_tac radd rmul rsub ropp rdiv rinv in
    let mkFE := mkFieldexpr C Cst_tac radd rmul rsub ropp rdiv rinv in
    let Simpl :=
      vm_compute; reflexivity || fail "not a valid field equation" in
    Field_Scheme mkFV mkFE Simpl lemma Cond_lemma req in
  ParseFieldComponents lemma Main.

Tactic Notation (at level 0) "field" :=
  field_lookup
    (fun req cst_tac field_ok _ _ cond_ok pre post rl =>
       pre(); Field field_ok cond_ok req cst_tac; post()).

(* transforms a field equation to an equivalent (simplified) ring equation,
   and leaves non-zero conditions to be proved (field_simplify_eq) *)
Ltac Field_simplify_eq lemma Cond_lemma req Cst_tac :=
  let Main radd rmul rsub ropp rdiv rinv C :=
    let mkFV := FFV Cst_tac radd rmul rsub ropp rdiv rinv in
    let mkFE := mkFieldexpr C Cst_tac radd rmul rsub ropp rdiv rinv in
    let Simpl := (protect_fv "field") in
    Field_Scheme mkFV mkFE Simpl lemma Cond_lemma req in
  ParseFieldComponents lemma Main.

Tactic Notation (at level 0) "field_simplify_eq" :=
  field_lookup
    (fun req cst_tac _ field_simplify_eq_ok _ cond_ok pre post rl =>
       pre(); Field_simplify_eq field_simplify_eq_ok cond_ok req cst_tac;
       post()).

(* Adding a new field *)

Ltac ring_of_field f :=
  match type of f with
  | almost_field_theory _ _ _ _ _ _ _ _ _ => constr:(AF_AR f)
  | field_theory _ _ _ _ _ _ _ _ _ => constr:(F_R f)
  | semi_field_theory _ _ _ _ _ _ _ => constr:(SF_SR f)
  end.

Ltac coerce_to_almost_field set ext f :=
  match type of f with
  | almost_field_theory _ _ _ _ _ _ _ _ _ => f
  | field_theory _ _ _ _ _ _ _ _ _ => constr:(F2AF set ext f)
  | semi_field_theory _ _ _ _ _ _ _ => constr:(SF2AF set f)
  end.

Ltac field_elements set ext fspec rk :=
  let afth := coerce_to_almost_field set ext fspec in
  let rspec := ring_of_field fspec in
  ring_elements set ext rspec rk
  ltac:(fun arth ext_r morph f => f afth ext_r morph).


Ltac field_lemmas set ext inv_m fspec rk :=
  field_elements set ext fspec rk
  ltac:(fun afth ext_r morph =>
    let field_ok := constr:(Field_correct set ext_r inv_m afth morph) in
    let field_simpl_ok :=
      constr:(Pphi_dev_div_ok set ext_r inv_m afth morph) in
    let field_simpl_eq_ok :=
      constr:(Field_simplify_eq_correct set ext_r inv_m afth morph) in
    let cond1_ok := constr:(Pcond_simpl_gen set ext_r afth morph) in
    let cond2_ok := constr:(Pcond_simpl_complete set ext_r afth morph) in
    (fun f => f afth ext_r morph field_ok field_simpl_ok field_simpl_eq_ok
                cond1_ok cond2_ok)).
