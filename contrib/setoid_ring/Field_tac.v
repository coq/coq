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
 Ltac mkFieldexpr C Cst CstPow radd rmul rsub ropp rdiv rinv rpow t fv := 
 let rec mkP t :=
    match Cst t with
    | InitialRing.NotConstant =>
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
        | (rpow ?t1 ?n) =>
          match CstPow n with
          | InitialRing.NotConstant => 
            let p := Find_at t fv in constr:(@FEX C p)
          | ?c => let e1 := mkP t1 in constr:(FEpow e1 c)
          end
  
        | _ =>
          let p := Find_at t fv in constr:(@FEX C p)
        end
    | ?c => constr:(FEc c)
    end
 in mkP t.

Ltac FFV Cst CstPow add mul sub opp div inv pow t fv :=
 let rec TFV t fv :=
  match Cst t with
  | InitialRing.NotConstant =>
      match t with
      | (add ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (mul ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (sub ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (opp ?t1) => TFV t1 fv
      | (div ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (inv ?t1) => TFV t1 fv
      | (pow ?t1 ?n) =>
        match CstPow n with
        | InitialRing.NotConstant => AddFvTail t fv
        | _ => TFV t1 fv
        end
      | _ => AddFvTail t fv
      end
  | _ => fv
  end 
 in TFV t fv.

Ltac ParseFieldComponents lemma req :=
  match type of lemma with
  | context [
     (*   PCond _ _ _  _ _ _ _  _ _  _ _ -> *)
        req (@FEeval ?R ?rO ?radd ?rmul ?rsub ?ropp ?rdiv ?rinv 
                          ?C ?phi ?Cpow ?Cp_phi ?rpow _ _) _ ] =>
      (fun f => f radd rmul rsub ropp rdiv rinv rpow C)
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
  (try exact I);
  fold_field_cond req.

Ltac simpl_PCond_BEURK req :=
  protect_fv "field_cond";
  fold_field_cond req.

(* Rewriting (field_simplify) *)
Ltac Field_norm_gen f Cst_tac Pow_tac lemma Cond_lemma req n lH rl :=
  let Main radd rmul rsub ropp rdiv rinv rpow C :=
    let mkFV := FV Cst_tac Pow_tac radd rmul rsub ropp rpow in
    let mkPol := mkPolexpr C Cst_tac Pow_tac radd rmul rsub ropp rpow in
    let mkFFV := FFV Cst_tac Pow_tac radd rmul rsub ropp rdiv rinv rpow in
    let mkFE := 
       mkFieldexpr C Cst_tac Pow_tac radd rmul rsub ropp rdiv rinv rpow in
    let fv := FV_hypo_tac mkFV req lH in
    let simpl_field H := (protect_fv "field" in H;f H) in
    let lemma_tac fv RW_tac :=
      let rr_lemma := fresh "f_rw_lemma" in
      let lpe := mkHyp_tac C req ltac:(fun t => mkPol t fv) lH in
      let vlpe := fresh "list_hyp" in
      let vlmp := fresh "list_hyp_norm" in
      let vlmp_eq := fresh "list_hyp_norm_eq" in
      let prh := proofHyp_tac lH in
      pose (vlpe := lpe);
      match type of lemma with
      | context [mk_monpol_list ?cO ?cI ?cadd ?cmul ?csub ?copp ?ceqb _] =>
        compute_assertion vlmp_eq vlmp 
            (mk_monpol_list cO cI cadd cmul csub copp ceqb vlpe);
         (assert (rr_lemma := lemma n vlpe fv prh vlmp vlmp_eq)
          || fail "type error when build the rewriting lemma");
         RW_tac rr_lemma;
        try clear rr_lemma vlmp_eq vlmp vlpe
      | _ => fail 1 "field_simplify anomaly: bad correctness lemma"
      end in
    ReflexiveRewriteTactic mkFFV mkFE simpl_field lemma_tac fv rl;
    try (apply Cond_lemma; simpl_PCond req) in
  ParseFieldComponents lemma req Main.

Ltac Field_simplify_gen f := 
     fun req cst_tac pow_tac _ _ field_simplify_ok _ cond_ok pre post lH rl =>
       pre(); 
       Field_norm_gen f cst_tac pow_tac field_simplify_ok cond_ok req 
                  ring_subst_niter lH rl; 
      post().

Ltac Field_simplify := Field_simplify_gen ltac:(fun H => rewrite H).

Tactic Notation (at level 0) 
  "field_simplify" constr_list(rl) :=
  match goal with [|- ?G] => field_lookup Field_simplify [] rl [G] end.

Tactic Notation (at level 0) 
  "field_simplify" "[" constr_list(lH) "]" constr_list(rl) :=
  match goal with [|- ?G] => field_lookup Field_simplify [lH] rl [G] end.

Tactic Notation "field_simplify" constr_list(rl) "in" hyp(H):=   
 match goal with 
 | [|- ?G] =>
   let t := type of H in   
   let g := fresh "goal" in
   set (g:= G);
   generalize H;clear H;
   field_lookup Field_simplify [] rl [t];
   intro H;
   unfold g;clear g
 end.

Tactic Notation "field_simplify" "["constr_list(lH) "]" constr_list(rl) "in" hyp(H):=   
 match goal with 
 | [|- ?G] =>
   let t := type of H in   
   let g := fresh "goal" in
   set (g:= G);
   generalize H;clear H;
   field_lookup Field_simplify [lH] rl [t];
   intro H;
   unfold g;clear g
 end.

(*
Ltac Field_simplify_in hyp:= 
   Field_simplify_gen ltac:(fun H => rewrite H in hyp).

Tactic Notation (at level 0) 
  "field_simplify" constr_list(rl) "in" hyp(h) :=
  let t := type of h in
  field_lookup (Field_simplify_in h) [] rl [t].

Tactic Notation (at level 0) 
  "field_simplify" "[" constr_list(lH) "]" constr_list(rl) "in" hyp(h) :=
  let t := type of h in
  field_lookup (Field_simplify_in h) [lH] rl [t].
*)

(** Generic tactic for solving equations *)

Ltac Field_Scheme Simpl_tac Cst_tac Pow_tac lemma Cond_lemma req n lH :=
  let Main radd rmul rsub ropp rdiv rinv rpow C :=
    let mkFV := FV Cst_tac Pow_tac radd rmul rsub ropp rpow in
    let mkPol := mkPolexpr C Cst_tac Pow_tac radd rmul rsub ropp rpow in
    let mkFFV := FFV Cst_tac Pow_tac radd rmul rsub ropp rdiv rinv rpow in
    let mkFE := 
       mkFieldexpr C Cst_tac Pow_tac radd rmul rsub ropp rdiv rinv rpow in
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
    let Main_eq t1 t2 :=
      let fv := FV_hypo_tac mkFV req lH in
      let fv := mkFFV t1 fv in
      let fv := mkFFV t2 fv in
      let lpe := mkHyp_tac C req ltac:(fun t => mkPol t fv) lH in
      let prh := proofHyp_tac lH in
      let vlpe := fresh "list_hyp" in
      let fe1 := mkFE t1 fv in
      let fe2 := mkFE t2 fv in
      pose (vlpe := lpe);
      let nlemma := fresh "field_lemma" in
      (assert (nlemma := lemma n fv vlpe fe1 fe2 prh)
       || fail "field anomaly:failed to build lemma"); 
      ParseExpr nlemma
         ltac:(fun ilemma =>
                  apply ilemma 
                  || fail "field anomaly: failed in applying lemma";
                  [ Simpl_tac | apply Cond_lemma; simpl_PCond req]);
      clear vlpe nlemma in
    OnEquation req Main_eq in
  ParseFieldComponents lemma req Main.

(* solve completely a field equation, leaving non-zero conditions to be
   proved (field) *)

Ltac FIELD :=
   let Simpl := vm_compute; reflexivity || fail "not a valid field equation" in
   fun req cst_tac pow_tac field_ok _ _ _ cond_ok pre post lH rl =>
       pre(); 
       Field_Scheme Simpl cst_tac pow_tac field_ok cond_ok req 
         Ring_tac.ring_subst_niter lH;
       try exact I;
       post().
 
Tactic Notation (at level 0) "field" :=
  match goal with [|- ?G] => field_lookup FIELD [] [G] end.

Tactic Notation (at level 0) "field" "[" constr_list(lH) "]" :=
  match goal with [|- ?G] => field_lookup FIELD [lH] [G] end.

(* transforms a field equation to an equivalent (simplified) ring equation,
   and leaves non-zero conditions to be proved (field_simplify_eq) *)
Ltac FIELD_SIMPL  :=
  let Simpl := (protect_fv "field") in
  fun req cst_tac pow_tac _ field_simplify_eq_ok _ _ cond_ok pre post lH rl =>
       pre(); 
       Field_Scheme Simpl cst_tac pow_tac field_simplify_eq_ok cond_ok 
          req Ring_tac.ring_subst_niter lH;
       post().

Tactic Notation (at level 0) "field_simplify_eq" :=  
  match goal with [|- ?G] => field_lookup FIELD_SIMPL [] [G] end.

Tactic Notation (at level 0) "field_simplify_eq" "[" constr_list(lH) "]" :=  
  match goal with [|- ?G] => field_lookup FIELD_SIMPL [lH] [G] end.

(* Same as FIELD_SIMPL but in hypothesis *)

Ltac Field_simplify_eq Cst_tac Pow_tac lemma Cond_lemma req n lH :=
   let Main radd rmul rsub ropp rdiv rinv rpow C :=
    let hyp := fresh "hyp" in
    intro hyp;
    match type of hyp with
    | req ?t1 ?t2 =>
      let mkFV := FV Cst_tac Pow_tac radd rmul rsub ropp rpow in
      let mkPol := mkPolexpr C Cst_tac Pow_tac radd rmul rsub ropp rpow in
      let mkFFV := FFV Cst_tac Pow_tac radd rmul rsub ropp rdiv rinv rpow in
      let mkFE := 
        mkFieldexpr C Cst_tac Pow_tac radd rmul rsub ropp rdiv rinv rpow in
      let rec ParseExpr ilemma :=
        match type of ilemma with
        |  forall nfe, ?fe = nfe -> _ =>
          (fun t => 
            let x := fresh "fld_expr" in 
            let H := fresh "norm_fld_expr" in
            compute_assertion H x fe;
            ParseExpr (ilemma x H) t;
            try clear H x)
        | _ => (fun t => t ilemma)
        end in
      let fv := FV_hypo_tac mkFV req lH in
      let fv := mkFFV t1 fv in
      let fv := mkFFV t2 fv in
      let lpe := mkHyp_tac C req ltac:(fun t => mkPol t fv) lH in
      let prh := proofHyp_tac lH in
      let fe1 := mkFE t1 fv in
      let fe2 := mkFE t2 fv in
      let vlpe := fresh "vlpe" in
      ParseExpr (lemma n fv lpe fe1 fe2 prh)
         ltac:(fun ilemma =>
             match type of ilemma with
             | req _ _ ->  _ -> ?EQ => 
               let tmp := fresh "tmp" in
               assert (tmp : EQ);
               [ apply ilemma; 
                 [ exact hyp | apply Cond_lemma; simpl_PCond_BEURK req]
               | protect_fv "field" in tmp;
                 generalize tmp;clear tmp ];
               clear hyp  
             end)
     end in
  ParseFieldComponents lemma req Main.

Ltac FIELD_SIMPL_EQ :=
 fun req cst_tac pow_tac _ _ _ lemma cond_ok pre post lH rl =>
       pre(); 
       Field_simplify_eq cst_tac pow_tac lemma cond_ok req
         Ring_tac.ring_subst_niter lH;
       post().

Tactic Notation (at level 0) "field_simplify_eq" "in" hyp(H) :=
  let t := type of H in
  generalize H;
  field_lookup FIELD_SIMPL_EQ [] [t];
  [ try exact I
  | clear H;intro H].


Tactic Notation (at level 0) 
  "field_simplify_eq" "[" constr_list(lH) "]"  "in" hyp(H) :=  
  let t := type of H in
  generalize H;
  field_lookup FIELD_SIMPL_EQ [lH] [t];
  [ try exact I
  |clear H;intro H].
 
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

Ltac field_elements set ext fspec pspec sspec rk :=
  let afth := coerce_to_almost_field set ext fspec in
  let rspec := ring_of_field fspec in
  ring_elements set ext rspec pspec sspec rk
  ltac:(fun arth ext_r morph p_spec s_spec f => f afth ext_r morph p_spec s_spec).

Ltac field_lemmas set ext inv_m fspec pspec sspec rk :=
  let simpl_eq_lemma := 
     match pspec with
     | None => constr:(Field_simplify_eq_correct)
     | Some _ => constr:(Field_simplify_eq_pow_correct)
     end in
  let simpl_eq_in_lemma :=
     match pspec with
     | None => constr:(Field_simplify_eq_in_correct)
     | Some _ => constr:(Field_simplify_eq_pow_in_correct)
     end in
  let rw_lemma :=
     match pspec with
     | None => constr:(Field_rw_correct)
     | Some _ => constr:(Field_rw_pow_correct)
     end in
  field_elements set ext fspec pspec sspec rk
   ltac:(fun afth ext_r morph p_spec s_spec =>
     match p_spec with
     | mkhypo ?pp_spec => match s_spec with
     | mkhypo ?ss_spec =>
       let field_simpl_eq_ok :=
         constr:(simpl_eq_lemma _ _ _  _ _ _  _ _ _ _ 
                   set ext_r inv_m afth 
                   _ _ _  _ _ _  _ _ _ morph 
                   _ _ _ pp_spec _ ss_spec) in 
       let field_simpl_ok :=
         constr:(rw_lemma _ _ _  _ _ _  _ _ _ _
                   set ext_r inv_m afth 
                   _ _ _  _ _ _  _ _ _ morph 
                   _ _ _ pp_spec _ ss_spec) in
       let field_simpl_eq_in :=
         constr:(simpl_eq_in_lemma _ _ _  _ _ _  _ _ _ _
                   set ext_r inv_m afth 
                   _ _ _  _ _ _  _ _ _ morph 
                   _ _ _ pp_spec _ ss_spec) in
       let field_ok := 
         constr:(Field_correct set ext_r inv_m afth morph pp_spec ss_spec) in
       let cond1_ok := 
         constr:(Pcond_simpl_gen set ext_r afth morph pp_spec) in
       let cond2_ok := 
         constr:(Pcond_simpl_complete set ext_r afth morph pp_spec) in
       (fun f => 
         f afth ext_r morph field_ok field_simpl_ok field_simpl_eq_ok field_simpl_eq_in
                cond1_ok cond2_ok)
     | _ => fail 2 "bad sign specification"
     end 
     | _ => fail 1 "bad power specification" 
     end).

