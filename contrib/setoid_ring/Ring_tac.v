Set Implicit Arguments.
Require Import Setoid.
Require Import BinPos.
Require Import Ring_polynom.
Require Import BinList.
Require Import InitialRing.
Declare ML Module "newring".
  

(* adds a definition id' on the normal form of t and an hypothesis id
   stating that t = id' (tries to produces a proof as small as possible) *)
Ltac compute_assertion id  id' t :=
  let t' := eval vm_compute in t in
  pose (id' := t');
  assert (id : t = id');
  [vm_cast_no_check (refl_equal id')|idtac].
(* [exact_no_check (refl_equal id'<: t = id')|idtac]). *)

(********************************************************************)
(* Tacticals to build reflexive tactics *)

Ltac OnEquation req :=
  match goal with
  | |- req ?lhs ?rhs => (fun f => f lhs rhs)
  | _ => fail 1 "Goal is not an equation (of expected equality)"
  end.

Ltac OnMainSubgoal H ty :=
  match ty with
  | _ -> ?ty' =>
     let subtac := OnMainSubgoal H ty' in
     fun tac => lapply H; [clear H; intro H; subtac tac | idtac]
  | _ => (fun tac => tac)
  end.

Ltac ApplyLemmaThen lemma expr tac :=
  let nexpr := fresh "expr_nf" in
  let H := fresh "eq_nf" in
  let Heq := fresh "thm" in
  let nf_spec :=
    match type of (lemma expr) with
      forall x, ?nf_spec = x -> _ => nf_spec
    | _ => fail 1 "ApplyLemmaThen: cannot find norm expression"
    end in
  compute_assertion H nexpr nf_spec;
  assert (Heq:=lemma _ _ H) || fail "anomaly: failed to apply lemma";
  clear H;
  OnMainSubgoal Heq ltac:(type of Heq) ltac:(tac Heq; clear Heq nexpr).

Ltac ApplyLemmaThenAndCont lemma expr tac CONT_tac cont_arg :=
  let npe := fresh "expr_nf" in
  let H := fresh "eq_nf" in
  let Heq := fresh "thm" in
  let npe_spec :=
    match type of (lemma expr) with
      forall npe, ?npe_spec = npe -> _ => npe_spec
    | _ => fail 1 "ApplyLemmaThenAndCont: cannot find norm expression"
    end in
  (compute_assertion H npe npe_spec;
   (assert (Heq:=lemma _ _ H) || fail "anomaly: failed to apply lemma");
   clear H;
   OnMainSubgoal Heq ltac:(type of Heq)
     ltac:(try tac Heq; clear Heq npe;CONT_tac cont_arg)).

(* General scheme of reflexive tactics using of correctness lemma
   that involves normalisation of one expression *)

Ltac ReflexiveRewriteTactic FV_tac SYN_tac MAIN_tac LEMMA_tac fv terms :=
  (* extend the atom list *)
  let fv := list_fold_left FV_tac fv terms in
  let RW_tac lemma := 
     let fcons term CONT_tac cont_arg := 
      let expr := SYN_tac term fv in
      (ApplyLemmaThenAndCont lemma expr MAIN_tac CONT_tac cont_arg) in
     (* rewrite steps *)
     lazy_list_fold_right fcons ltac:(idtac) terms in
  LEMMA_tac fv RW_tac.

(********************************************************)


(* Building the atom list of a ring expression *)
Ltac FV Cst CstPow add mul sub opp pow t fv :=
 let rec TFV t fv :=
  match Cst t with
  | NotConstant =>
      match t with
      | (add ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (mul ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (sub ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (opp ?t1) => TFV t1 fv
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

 (* syntaxification of ring expressions *)
Ltac mkPolexpr C Cst CstPow radd rmul rsub ropp rpow t fv := 
 let rec mkP t :=
    let f :=
    match Cst t with
    | InitialRing.NotConstant =>
        match t with 
        | (radd ?t1 ?t2) => 
          fun _ =>
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(PEadd e1 e2)
        | (rmul ?t1 ?t2) => 
          fun _ =>
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(PEmul e1 e2)
        | (rsub ?t1 ?t2) => 
          fun _ => 
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(PEsub e1 e2)
        | (ropp ?t1) =>
          fun _ =>
          let e1 := mkP t1 in constr:(PEopp e1)
        | (rpow ?t1 ?n) =>
          match CstPow n with
          | InitialRing.NotConstant => 
            fun _ => let p := Find_at t fv in constr:(PEX C p)
          | ?c => fun _ => let e1 := mkP t1 in constr:(PEpow e1 c)
          end
        | _ =>
          fun _ => let p := Find_at t fv in constr:(PEX C p)
        end
    | ?c => fun _ => constr:(@PEc C c)
    end in
    f ()
 in mkP t.

Ltac ParseRingComponents lemma :=
  match type of lemma with
  | context [@PEeval ?R ?rO ?add ?mul ?sub ?opp ?C ?phi ?Cpow ?powphi ?pow _ _] =>
      (fun f => f R add mul sub opp pow C)
  | _ => fail 1 "ring anomaly: bad correctness lemma (parse)"
  end.

(* ring tactics *)

Ltac relation_carrier req :=
  let ty := type of req in
  match eval hnf in ty with
   ?R -> _ => R
  | _ => fail 1000 "Equality has no relation type"
  end.

Ltac FV_hypo_tac mkFV req lH :=
  let R := relation_carrier req in
  let FV_hypo_l_tac h :=
    match h with @mkhypo (req ?pe _) _ => mkFV pe end in
  let FV_hypo_r_tac h :=
    match h with @mkhypo (req _ ?pe) _ => mkFV pe end in
  let fv := list_fold_right FV_hypo_l_tac (@nil R) lH in
  list_fold_right FV_hypo_r_tac fv lH.

Ltac mkHyp_tac C req mkPE lH :=
  let mkHyp h res := 
   match h with 
   | @mkhypo (req ?r1 ?r2) _ =>
     let pe1 := mkPE r1 in
     let pe2 := mkPE r2 in
     constr:(cons (pe1,pe2) res)
   | _ => fail 1 "hypothesis is not a ring equality"
   end in
  list_fold_right mkHyp (@nil (PExpr C * PExpr C)) lH.
     
Ltac proofHyp_tac lH :=
  let get_proof h :=
    match h with
    | @mkhypo _ ?p => p
    end in
  let rec bh l :=
    match l with
    | nil => constr:(I)
    | cons ?h nil => get_proof h
    | cons ?h ?tl => 
      let l := get_proof h in
      let r := bh tl in  
      constr:(conj l r)
    end in
  bh lH.

Definition ring_subst_niter := (10*10*10)%nat.
 
Ltac Ring Cst_tac CstPow_tac lemma1 req n lH :=
  let Main lhs rhs R radd rmul rsub ropp rpow C :=
    let mkFV := FV Cst_tac CstPow_tac radd rmul rsub ropp rpow in
    let mkPol := mkPolexpr C Cst_tac CstPow_tac radd rmul rsub ropp rpow in
    let fv := FV_hypo_tac mkFV req lH in
    let fv := mkFV lhs fv in
    let fv := mkFV rhs fv in
    check_fv fv;
    let pe1 := mkPol lhs fv in
    let pe2 := mkPol rhs fv in
    let lpe := mkHyp_tac C req ltac:(fun t => mkPol t fv) lH in
    let vlpe := fresh "hyp_list" in
    let vfv := fresh "fv_list" in
    pose (vlpe := lpe);
    pose (vfv := fv);
    (apply (lemma1 n vfv vlpe pe1 pe2)
      || fail "typing error while applying ring");
    [ ((let prh := proofHyp_tac lH in exact prh)
        || idtac "can not automatically proof hypothesis : maybe a left member of a hypothesis is not a monomial") 
    | vm_compute;
      (exact (refl_equal true) || fail "not a valid ring equation")] in
  ParseRingComponents lemma1 ltac:(OnEquation req Main).

Ltac Ring_norm_gen f Cst_tac CstPow_tac lemma2 req n lH rl :=
  let Main R add mul sub opp pow C :=
    let mkFV := FV Cst_tac CstPow_tac add mul sub opp pow in
    let mkPol := mkPolexpr C Cst_tac CstPow_tac add mul sub opp pow in
    let fv := FV_hypo_tac mkFV req lH in
    let simpl_ring H := (protect_fv "ring" in H; f H) in
    let lemma_tac fv RW_tac := 
      let rr_lemma := fresh "r_rw_lemma" in
      let lpe := mkHyp_tac C req ltac:(fun t => mkPol t fv) lH in
      let vlpe := fresh "list_hyp" in
      let vlmp := fresh "list_hyp_norm" in
      let vlmp_eq := fresh "list_hyp_norm_eq" in
      let prh := proofHyp_tac lH in
      pose (vlpe := lpe);
      match type of lemma2 with
      | context [mk_monpol_list ?cO ?cI ?cadd ?cmul ?csub ?copp ?cdiv ?ceqb _]
            =>
        compute_assertion vlmp_eq vlmp 
            (mk_monpol_list cO cI cadd cmul csub copp cdiv ceqb vlpe);
         (assert (rr_lemma := lemma2 n vlpe fv prh vlmp vlmp_eq)
          || fail 1 "type error when build the rewriting lemma");   
         RW_tac rr_lemma;
         try clear rr_lemma vlmp_eq vlmp vlpe
      | _ => fail 1 "ring_simplify anomaly: bad correctness lemma"
      end in
    ReflexiveRewriteTactic mkFV mkPol simpl_ring lemma_tac fv rl in
  ParseRingComponents lemma2 Main.


Ltac Ring_gen
  req sth ext morph arth cst_tac pow_tac lemma1 lemma2 pre post lH rl :=
  pre();Ring cst_tac pow_tac lemma1 req ring_subst_niter lH.

Ltac Get_goal := match goal with [|- ?G] => G end.

Tactic Notation (at level 0) "ring" :=
  let G := Get_goal in
  ring_lookup Ring_gen [] G.

Tactic Notation (at level 0) "ring" "[" constr_list(lH) "]" :=
  let G := Get_goal in
  ring_lookup Ring_gen [lH] G.

(* Simplification *)

Ltac Ring_simplify_gen f :=
  fun req sth ext morph arth cst_tac pow_tac lemma1 lemma2 pre post lH rl =>
     let l := fresh "to_rewrite" in
     pose (l:= rl);
     generalize (refl_equal l);
     unfold l at 2;
     pre(); 
     let Tac RL :=
       let Heq := fresh "Heq" in
       intros Heq;clear Heq l;
       Ring_norm_gen f cst_tac pow_tac lemma2 req ring_subst_niter lH RL; 
       post() in
     let Main :=
       match goal with
       | [|- l = ?RL -> _ ] => (fun f => f RL)
       | _ => fail 1 "ring_simplify anomaly: bad goal after pre"
       end in
     Main Tac.

Ltac Ring_simplify := Ring_simplify_gen ltac:(fun H => rewrite H).

Tactic Notation (at level 0) "ring_simplify" constr_list(rl) := 
  let G := Get_goal in
  ring_lookup Ring_simplify [] rl G.

Tactic Notation (at level 0) 
  "ring_simplify" "[" constr_list(lH) "]" constr_list(rl) :=
  let G := Get_goal in
  ring_lookup Ring_simplify [lH] rl G.

(* MON DIEU QUE C'EST MOCHE !!!!!!!!!!!!! *)

Tactic Notation "ring_simplify" constr_list(rl) "in" hyp(H):=   
  let G := Get_goal in
  let t := type of H in   
  let g := fresh "goal" in
  set (g:= G);
  generalize H;clear H;
  ring_lookup Ring_simplify [] rl t;
  intro H;
  unfold g;clear g.

Tactic Notation 
  "ring_simplify" "["constr_list(lH)"]" constr_list(rl) "in" hyp(H):=   
  let G := Get_goal in
  let t := type of H in   
  let g := fresh "goal" in
  set (g:= G);
  generalize H;clear H;
  ring_lookup Ring_simplify [lH] rl t;
  intro H;
  unfold g;clear g.



(*     LE RESTE MARCHE PAS DOMMAGE  .....  *)















(*








Ltac Ring_simplify_in hyp:= Ring_simplify_gen ltac:(fun H => rewrite H in hyp).


Tactic Notation (at level 0) 
  "ring_simplify" "[" constr_list(lH) "]" constr_list(rl) := 
  match goal with [|- ?G] => ring_lookup Ring_simplify [lH] rl G end.

Tactic Notation (at level 0) 
  "ring_simplify" constr_list(rl) := 
  match goal with [|- ?G] => ring_lookup Ring_simplify [] rl G end.

Tactic Notation (at level 0) 
  "ring_simplify" "[" constr_list(lH) "]" constr_list(rl) "in" hyp(h):= 
  let t := type of h in
  ring_lookup 
   (fun req sth ext morph arth cst_tac pow_tac lemma1 lemma2 pre post lH rl =>
     pre(); 
     Ring_norm_gen ltac:(fun EQ => rewrite EQ in h) cst_tac pow_tac lemma2 req ring_subst_niter lH rl; 
     post()) 
  [lH] rl t. 
(*  ring_lookup ltac:(Ring_simplify_in h) [lH] rl [t]. NE MARCHE PAS ??? *)

Ltac Ring_simpl_in hyp := Ring_norm_gen ltac:(fun H => rewrite H in hyp).

Tactic Notation (at level 0) 
  "ring_simplify" constr_list(rl) "in" constr(h):= 
  let t := type of h in
  ring_lookup   
   (fun req sth ext morph arth cst_tac pow_tac lemma1 lemma2 pre post lH rl =>
     pre(); 
     Ring_simpl_in h cst_tac pow_tac lemma2 req ring_subst_niter lH rl; 
     post())
 [] rl t.

Ltac rw_in H Heq := rewrite Heq in H.

Ltac simpl_in H := 
  let t := type of H in
   ring_lookup 
   (fun req sth ext morph arth cst_tac pow_tac lemma1 lemma2 pre post lH rl =>
     pre(); 
     Ring_norm_gen ltac:(fun Heq => rewrite Heq in H) cst_tac pow_tac lemma2 req ring_subst_niter lH rl; 
     post()) 
   [] t.


*)
