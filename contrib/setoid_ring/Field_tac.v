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
    let f :=
    match Cst t with
    | InitialRing.NotConstant =>
        match t with 
        | (radd ?t1 ?t2) => 
          fun _ =>
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(FEadd e1 e2)
        | (rmul ?t1 ?t2) => 
          fun _ =>
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(FEmul e1 e2)
        | (rsub ?t1 ?t2) => 
          fun _ => 
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(FEsub e1 e2)
        | (ropp ?t1) =>
          fun _ => let e1 := mkP t1 in constr:(FEopp e1)
        | (rdiv ?t1 ?t2) => 
          fun _ =>
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(FEdiv e1 e2)
        | (rinv ?t1) =>
          fun _ => let e1 := mkP t1 in constr:(FEinv e1)
        | (rpow ?t1 ?n) =>
          match CstPow n with
          | InitialRing.NotConstant => 
            fun _ =>
            let p := Find_at t fv in
            constr:(@FEX C p)
          | ?c => fun _ => let e1 := mkP t1 in constr:(FEpow e1 c)
          end
        | _ =>
          fun _ =>
          let p := Find_at t fv in
          constr:(@FEX C p)
        end
    | ?c => fun _ => constr:(FEc c)
    end in
    f ()
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
        | InitialRing.NotConstant =>
            AddFvTail t fv
        | _ => TFV t1 fv
        end
      | _ => AddFvTail t fv
      end
  | _ => fv
  end 
 in TFV t fv.

(* packaging the field structure *)

(* TODO: inline PackField into field_lookup *)
Ltac PackField F req Cst_tac Pow_tac L1 L2 L3 L4 cond_ok pre post :=
  let FLD :=
    match type of L1 with
    | context [req (@FEeval ?R ?rO ?radd ?rmul ?rsub ?ropp ?rdiv ?rinv 
                                      ?C ?phi ?Cpow ?Cp_phi ?rpow _ _) _ ] =>
        (fun proj =>
           proj Cst_tac Pow_tac pre post
             req radd rmul rsub ropp rdiv rinv rpow C L1 L2 L3 L4 cond_ok)
    | _ => fail 1 "field anomaly: bad correctness lemma (parse)"
    end in
  F FLD.

Ltac get_FldPre FLD :=
  FLD ltac:
      (fun Cst_tac Pow_tac pre post req radd rmul rsub ropp rdiv rinv rpow C
           L1 L2 L3 L4 cond_ok =>
       pre).

Ltac get_FldPost FLD :=
  FLD ltac:
      (fun Cst_tac Pow_tac pre post req radd rmul rsub ropp rdiv rinv rpow C
           L1 L2 L3 L4 cond_ok =>
       post).

Ltac get_L1 FLD :=
  FLD ltac:
      (fun Cst_tac Pow_tac pre post req radd rmul rsub ropp rdiv rinv rpow C
           L1 L2 L3 L4 cond_ok =>
       L1).

Ltac get_SimplifyEqLemma FLD :=
  FLD ltac:
      (fun Cst_tac Pow_tac pre post req radd rmul rsub ropp rdiv rinv rpow C
           L1 L2 L3 L4 cond_ok =>
       L2).

Ltac get_SimplifyLemma FLD :=
  FLD ltac:
      (fun Cst_tac Pow_tac pre post req radd rmul rsub ropp rdiv rinv rpow C
           L1 L2 L3 L4 cond_ok =>
       L3).

Ltac get_L4 FLD :=
  FLD ltac:
      (fun Cst_tac Pow_tac pre post req radd rmul rsub ropp rdiv rinv rpow C
           L1 L2 L3 L4 cond_ok =>
       L4).

Ltac get_CondLemma FLD :=
  FLD ltac:
      (fun Cst_tac Pow_tac pre post req radd rmul rsub ropp rdiv rinv rpow C
           L1 L2 L3 L4 cond_ok =>
       cond_ok).

Ltac get_FldEq FLD :=
  FLD ltac:
      (fun Cst_tac Pow_tac pre post req radd rmul rsub ropp rdiv rinv rpow C
           L1 L2 L3 L4 cond_ok =>
       req).

Ltac get_FldCarrier FLD :=
  let req := get_FldEq FLD in
  relation_carrier req.

Ltac get_RingFV FLD :=
  FLD ltac:
      (fun Cst_tac Pow_tac pre post req radd rmul rsub ropp rdiv rinv rpow C
           L1 L2 L3 L4 cond_ok =>
       FV Cst_tac Pow_tac radd rmul rsub ropp rpow).

Ltac get_FFV FLD :=
  FLD ltac:
      (fun Cst_tac Pow_tac pre post req radd rmul rsub ropp rdiv rinv rpow C
           L1 L2 L3 L4 cond_ok =>
       FFV Cst_tac Pow_tac radd rmul rsub ropp rdiv rinv rpow).

Ltac get_RingMeta FLD :=
  FLD ltac:
      (fun Cst_tac Pow_tac pre post req radd rmul rsub ropp rdiv rinv rpow C
           L1 L2 L3 L4 cond_ok =>
       mkPolexpr C Cst_tac Pow_tac radd rmul rsub ropp rpow).

Ltac get_Meta FLD :=
  FLD ltac:
      (fun Cst_tac Pow_tac pre post req radd rmul rsub ropp rdiv rinv rpow C
           L1 L2 L3 L4 cond_ok =>
       mkFieldexpr C Cst_tac Pow_tac radd rmul rsub ropp rdiv rinv rpow).

Ltac get_Hyp_tac FLD :=
  FLD ltac:
      (fun Cst_tac Pow_tac pre post req radd rmul rsub ropp rdiv rinv rpow C
           L1 L2 L3 L4 cond_ok =>
       let mkPol := mkPolexpr C Cst_tac Pow_tac radd rmul rsub ropp rpow in
       fun fv lH => mkHyp_tac C req ltac:(fun t => mkPol t fv) lH).

Ltac get_FEeval FLD :=
  let L1 := get_L1 FLD in
  match type of L1 with
  | context
    [(@FEeval
      ?R ?r0 ?add ?mul ?sub ?opp ?div ?inv ?C ?phi ?Cpow ?powphi ?pow _ _)] =>
       constr:(@FEeval R r0 add mul sub opp div inv C phi Cpow powphi pow)
  | _ => fail 1 "field anomaly: bad correctness lemma (get_FEeval)"
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
  let ft := fold_concl Get_goal in
  change ft.

Ltac simpl_PCond FLD :=
  let req := get_FldEq FLD in
  let lemma := get_CondLemma FLD in
  try apply lemma;
  protect_fv "field_cond";
  fold_field_cond req;
  try exact I.

Ltac simpl_PCond_BEURK FLD :=
  let req := get_FldEq FLD in
  let lemma := get_CondLemma FLD in
  apply lemma;
  protect_fv "field_cond";
  fold_field_cond req.

(* Rewriting (field_simplify) *)
Ltac Field_norm_gen f n FLD lH rl :=
  let mkFV := get_RingFV FLD in
  let mkFFV := get_FFV FLD in
  let mkFE :=  get_Meta FLD in
  let fv0 := FV_hypo_tac mkFV ltac:(get_FldEq FLD) lH in
  let lemma_tac fv kont :=
    let lemma := get_SimplifyLemma FLD in
    (* reify equations of the context *)
    let lpe := get_Hyp_tac FLD fv lH in
    let vlpe := fresh "hyps" in
    pose (vlpe := lpe);
    let prh := proofHyp_tac lH in
    (* compute the normal form of the reified hyps *)
    let vlmp := fresh "hyps'" in
    let vlmp_eq := fresh "hyps_eq" in
    let mk_monpol := get_MonPol lemma in
    compute_assertion vlmp_eq vlmp (mk_monpol vlpe);
    (* partially instantiate the lemma *)
    let lem := fresh "f_rw_lemma" in
    (assert (lem := lemma n vlpe fv prh vlmp vlmp_eq)
     || fail "type error when building the rewriting lemma");
    (* continuation will call main_tac for all reified terms *)
    kont lem;
    (* at the end, cleanup *)
    (clear lem vlmp_eq vlmp vlpe||idtac"Field_norm_gen:cleanup failed") in
  (* each instance of the lemma is simplified then passed to f *)
  let main_tac H := protect_fv "field" in H; f H in
  (* generate and use equations for each expression *)
  ReflexiveRewriteTactic mkFFV mkFE lemma_tac main_tac fv0 rl;
  (* simplifying the denominator condition *)
  try simpl_PCond FLD.

Ltac Field_simplify_gen f FLD lH rl := 
  get_FldPre FLD ();
  Field_norm_gen f ring_subst_niter FLD lH rl; 
  get_FldPost FLD ().

Ltac Field_simplify := Field_simplify_gen ltac:(fun H => rewrite H).

Tactic Notation (at level 0) "field_simplify" constr_list(rl) :=
  let G := Get_goal in
  field_lookup (PackField Field_simplify) [] rl G.

Tactic Notation (at level 0) 
  "field_simplify" "[" constr_list(lH) "]" constr_list(rl) :=
  let G := Get_goal in
  field_lookup (PackField Field_simplify) [lH] rl G.

Tactic Notation "field_simplify" constr_list(rl) "in" hyp(H):=   
  let G := Get_goal in
  let t := type of H in   
  let g := fresh "goal" in
  set (g:= G);
  generalize H;clear H;
  field_lookup (PackField Field_simplify) [] rl t;
  intro H;
  unfold g;clear g.

Tactic Notation "field_simplify" 
    "["constr_list(lH) "]" constr_list(rl) "in" hyp(H):=   
  let G := Get_goal in
  let t := type of H in   
  let g := fresh "goal" in
  set (g:= G);
  generalize H;clear H;
  field_lookup (PackField Field_simplify) [lH] rl t;
  intro H;
  unfold g;clear g.

(*
Ltac Field_simplify_in hyp:= 
   Field_simplify_gen ltac:(fun H => rewrite H in hyp).

Tactic Notation (at level 0) 
  "field_simplify" constr_list(rl) "in" hyp(h) :=
  let t := type of h in
  field_lookup (Field_simplify_in h) [] rl t.

Tactic Notation (at level 0) 
  "field_simplify" "[" constr_list(lH) "]" constr_list(rl) "in" hyp(h) :=
  let t := type of h in
  field_lookup (Field_simplify_in h) [lH] rl t.
*)

(** Generic tactic for solving equations *)

Ltac Field_Scheme Simpl_tac n lemma FLD lH :=
  let req := get_FldEq FLD in
  let mkFV := get_RingFV FLD in
  let mkFFV := get_FFV FLD in
  let mkFE := get_Meta FLD in
  let Main_eq t1 t2 :=
    let fv := FV_hypo_tac mkFV req lH in
    let fv := mkFFV t1 fv in
    let fv := mkFFV t2 fv in
    let lpe := get_Hyp_tac FLD fv lH in
    let prh := proofHyp_tac lH in
    let vlpe := fresh "list_hyp" in
    let fe1 := mkFE t1 fv in
    let fe2 := mkFE t2 fv in
    pose (vlpe := lpe);
    let nlemma := fresh "field_lemma" in
    (assert (nlemma := lemma n fv vlpe fe1 fe2 prh)
     || fail "field anomaly:failed to build lemma"); 
    ProveLemmaHyps nlemma
      ltac:(fun ilemma =>
              apply ilemma 
               || fail "field anomaly: failed in applying lemma";
              [ Simpl_tac | simpl_PCond FLD]);
    clear vlpe nlemma in
  OnEquation req Main_eq.

(* solve completely a field equation, leaving non-zero conditions to be
   proved (field) *)

Ltac FIELD FLD lH rl :=
  let Simpl := vm_compute; reflexivity || fail "not a valid field equation" in
  let lemma := get_L1 FLD in
  get_FldPre FLD (); 
  Field_Scheme Simpl Ring_tac.ring_subst_niter lemma FLD lH;
  try exact I;
  get_FldPost FLD().
 
Tactic Notation (at level 0) "field" :=
  let G := Get_goal in
  field_lookup (PackField FIELD) [] G.

Tactic Notation (at level 0) "field" "[" constr_list(lH) "]" :=
  let G := Get_goal in
  field_lookup (PackField FIELD) [lH] G.

(* transforms a field equation to an equivalent (simplified) ring equation,
   and leaves non-zero conditions to be proved (field_simplify_eq) *)
Ltac FIELD_SIMPL FLD lH rl :=
  let Simpl := (protect_fv "field") in
  let lemma := get_SimplifyEqLemma FLD in
  get_FldPre FLD (); 
  Field_Scheme Simpl Ring_tac.ring_subst_niter lemma FLD lH;
  get_FldPost FLD ().

Tactic Notation (at level 0) "field_simplify_eq" :=  
  let G := Get_goal in
  field_lookup (PackField FIELD_SIMPL) [] G.

Tactic Notation (at level 0) "field_simplify_eq" "[" constr_list(lH) "]" :=  
  let G := Get_goal in
  field_lookup FIELD_SIMPL [lH] G.

(* Same as FIELD_SIMPL but in hypothesis *)

Ltac Field_simplify_eq n FLD lH :=
  let req := get_FldEq FLD in
  let mkFV := get_RingFV FLD in
  let mkFFV := get_FFV FLD in
  let mkFE := get_Meta FLD in
  let lemma := get_L4 FLD in
  let hyp := fresh "hyp" in
  intro hyp;   
  OnEquationHyp req hyp ltac:(fun t1 t2 =>
      let fv := FV_hypo_tac mkFV req lH in
      let fv := mkFFV t1 fv in
      let fv := mkFFV t2 fv in
      let lpe := get_Hyp_tac FLD fv lH in
      let prh := proofHyp_tac lH in
      let fe1 := mkFE t1 fv in
      let fe2 := mkFE t2 fv in
      let vlpe := fresh "vlpe" in
      ProveLemmaHyps (lemma n fv lpe fe1 fe2 prh)
         ltac:(fun ilemma =>
             match type of ilemma with
             | req _ _ ->  _ -> ?EQ => 
               let tmp := fresh "tmp" in
               assert (tmp : EQ);
               [ apply ilemma; [ exact hyp | simpl_PCond_BEURK FLD]
               | protect_fv "field" in tmp; revert tmp ];
               clear hyp  
             end)).

Ltac FIELD_SIMPL_EQ FLD lH rl :=
  get_FldPre FLD (); 
  Field_simplify_eq Ring_tac.ring_subst_niter FLD lH;
  get_FldPost().

Tactic Notation (at level 0) "field_simplify_eq" "in" hyp(H) :=
  let t := type of H in
  generalize H;
  field_lookup (PackField FIELD_SIMPL_EQ) [] t;
  [ try exact I
  | clear H;intro H].


Tactic Notation (at level 0) 
  "field_simplify_eq" "[" constr_list(lH) "]"  "in" hyp(H) :=  
  let t := type of H in
  generalize H;
  field_lookup (PackField FIELD_SIMPL_EQ) [lH] t;
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

Ltac field_elements set ext fspec pspec sspec dspec rk :=
  let afth := coerce_to_almost_field set ext fspec in
  let rspec := ring_of_field fspec in
  ring_elements set ext rspec pspec sspec dspec rk
  ltac:(fun arth ext_r morph p_spec s_spec d_spec f => f afth ext_r morph p_spec s_spec d_spec).

Ltac field_lemmas set ext inv_m fspec pspec sspec dspec rk :=
  let get_lemma :=
    match pspec with None => fun x y => x | _ => fun x y => y end in
  let simpl_eq_lemma := get_lemma 
       Field_simplify_eq_correct       Field_simplify_eq_pow_correct in
  let simpl_eq_in_lemma := get_lemma
       Field_simplify_eq_in_correct   Field_simplify_eq_pow_in_correct in
  let rw_lemma := get_lemma
       Field_rw_correct                    Field_rw_pow_correct in
  field_elements set ext fspec pspec sspec dspec rk
   ltac:(fun afth ext_r morph p_spec s_spec d_spec =>
     match morph with
     | _ =>
       let field_ok1 := constr:(Field_correct set ext_r inv_m afth morph) in
       match p_spec with
       | mkhypo ?pp_spec =>  
         let field_ok2 := constr:(field_ok1 _ _ _ pp_spec) in
         match s_spec with
         | mkhypo ?ss_spec => 
           let field_ok3 := constr:(field_ok2 _ ss_spec) in
           match d_spec with
           | mkhypo ?dd_spec => 
             let field_ok := constr:(field_ok3 _ dd_spec) in
             let mk_lemma lemma :=     
              constr:(lemma _ _ _  _ _ _  _ _ _ _ 
                   set ext_r inv_m afth 
                   _ _ _  _ _ _  _ _ _ morph 
                   _ _ _ pp_spec _ ss_spec _ dd_spec) in 
             let field_simpl_eq_ok := mk_lemma simpl_eq_lemma  in
             let field_simpl_ok := mk_lemma rw_lemma in
             let field_simpl_eq_in := mk_lemma simpl_eq_in_lemma in
             let cond1_ok := 
                constr:(Pcond_simpl_gen set ext_r afth morph pp_spec dd_spec) in
             let cond2_ok := 
               constr:(Pcond_simpl_complete set ext_r afth morph pp_spec dd_spec) in
             (fun f => 
               f afth ext_r morph field_ok field_simpl_ok field_simpl_eq_ok field_simpl_eq_in
                  cond1_ok cond2_ok)
           | _ => fail 4 "field: bad coefficiant division specification"
           end
         | _ => fail 3 "field: bad sign specification"
         end
       | _ => fail 2 "field: bad power specification"
       end  
     | _ => fail 1 "field internal error : field_lemmas, please report"
     end).
