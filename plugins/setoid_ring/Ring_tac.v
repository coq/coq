(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Set Implicit Arguments.
Require Import Setoid.
Require Import BinPos.
Require Import Ring_polynom.
Require Import BinList.
Require Export ListTactics.
Require Import InitialRing.
Require Import Quote.
Declare ML Module "newring_plugin".


(* adds a definition t' on the normal form of t and an hypothesis id
   stating that t = t' (tries to produces a proof as small as possible) *)
Ltac compute_assertion eqn t' t :=
  let nft := eval vm_compute in t in
  pose (t' := nft);
  assert (eqn : t = t');
  [vm_cast_no_check (eq_refl t')|idtac].

Ltac relation_carrier req :=
  let ty := type of req in
  match eval hnf in ty with
   ?R -> _ => R
  | _ => fail 1000 "Equality has no relation type"
  end.

Ltac Get_goal := match goal with [|- ?G] => G end.

(********************************************************************)
(* Tacticals to build reflexive tactics *)

Ltac OnEquation req :=
  match goal with
  | |- req ?lhs ?rhs => (fun f => f lhs rhs)
  | _ => (fun _ => fail "Goal is not an equation (of expected equality)")
  end.

Ltac OnEquationHyp req h :=
  match type of h with
  | req ?lhs ?rhs => fun f => f lhs rhs
  | _ => (fun _ => fail "Hypothesis is not an equation (of expected equality)")
  end.

(* Note: auxiliary subgoals in reverse order *)
Ltac OnMainSubgoal H ty :=
  match ty with
  | _ -> ?ty' =>
     let subtac := OnMainSubgoal H ty' in
     fun kont => lapply H; [clear H; intro H; subtac kont | idtac]
  | _ => (fun kont => kont())
  end.

(* A generic pattern to have reflexive tactics do some computation:
   lemmas of the form [forall x', x=x' -> P(x')] are understood as:
   compute the normal form of x, instantiate x' with it, prove
   hypothesis x=x' with vm_compute and reflexivity, and pass the
   instantiated lemma to the continuation.
 *)
Ltac ProveLemmaHyp lemma :=
  match type of lemma with
    forall x', ?x = x' -> _ =>
      (fun kont =>
        let x' := fresh "res" in
        let H := fresh "res_eq" in
        compute_assertion H x' x;
        let lemma' := constr:(lemma x' H) in
        kont lemma';
        (clear H||idtac"ProveLemmaHyp: cleanup failed");
        subst x')
  | _ => (fun _ => fail "ProveLemmaHyp: lemma not of the expected form")
  end.

Ltac ProveLemmaHyps lemma :=
  match type of lemma with
    forall x', ?x = x' -> _ =>
      (fun kont =>
        let x' := fresh "res" in
        let H := fresh "res_eq" in
        compute_assertion H x' x;
        let lemma' := constr:(lemma x' H) in
        ProveLemmaHyps lemma' kont;
        (clear H||idtac"ProveLemmaHyps: cleanup failed");
        subst x')
  | _ => (fun kont => kont lemma)
  end.

(*
Ltac ProveLemmaHyps lemma := (* expects a continuation *)
  let try_step := ProveLemmaHyp lemma in
  (fun kont =>
    try_step ltac:(fun lemma' => ProveLemmaHyps lemma' kont) ||
    kont lemma).
*)
Ltac ApplyLemmaThen lemma expr kont :=
  let lem := constr:(lemma expr) in
  ProveLemmaHyp lem ltac:(fun lem' =>
    let Heq := fresh "thm" in
    assert (Heq:=lem');
    OnMainSubgoal Heq ltac:(type of Heq) ltac:(fun _ => kont Heq);
    (clear Heq||idtac"ApplyLemmaThen: cleanup failed")).
(*
Ltac ApplyLemmaThenAndCont lemma expr tac CONT_tac cont_arg :=
  let pe :=
    match type of (lemma expr) with
      forall pe', ?pe = pe' -> _ => pe
    | _ => fail 1 "ApplyLemmaThenAndCont: cannot find norm expression"
    end in
  let pe' := fresh "expr_nf" in
  let nf_pe := fresh "pe_eq" in
  compute_assertion nf_pe pe' pe;
  let Heq := fresh "thm" in
  (assert (Heq:=lemma pe pe' H) || fail "anomaly: failed to apply lemma");
  clear nf_pe;
  OnMainSubgoal Heq ltac:(type of Heq)
    ltac:(try tac Heq; clear Heq pe';CONT_tac cont_arg)).
*)
Ltac ApplyLemmaThenAndCont lemma expr tac CONT_tac :=
  ApplyLemmaThen lemma expr
    ltac:(fun lemma' => try tac lemma'; CONT_tac()).

(* General scheme of reflexive tactics using of correctness lemma
   that involves normalisation of one expression
   - [FV_tac term fv] is a tactic that adds the atomic expressions
       of [term] into [fv]
   - [SYN_tac term fv] reifies [term] given the list of atomic expressions
   - [LEMMA_tac fv kont] computes the correctness lemma and passes it to
       continuation kont
   - [MAIN_tac H] process H which is the conclusion of the correctness lemma
       instantiated with each reified term
   - [fv] is the initial value of atomic expressions (to be completed by
       the reification of the terms
   - [terms] the list (a constr of type list) of terms to reify and process.
 *)
Ltac ReflexiveRewriteTactic
     FV_tac SYN_tac LEMMA_tac MAIN_tac fv terms :=
  (* extend the atom list *)
  let fv := list_fold_left FV_tac fv terms in
  let RW_tac lemma :=
     let fcons term CONT_tac :=
      let expr := SYN_tac term fv in
      let main H :=
        match type of H with
        | (?req _ ?rhs) => change (req term rhs) in H
        end;
        MAIN_tac H in
      (ApplyLemmaThenAndCont lemma expr main CONT_tac) in
     (* rewrite steps *)
     lazy_list_fold_right fcons ltac:(fun _=>idtac) terms in
  LEMMA_tac fv RW_tac.

(********************************************************)

Ltac FV_hypo_tac mkFV req lH :=
  let R := relation_carrier req in
  let FV_hypo_l_tac h :=
    match h with @mkhypo (req ?pe _) _ => mkFV pe end in
  let FV_hypo_r_tac h :=
    match h with @mkhypo (req _ ?pe) _ => mkFV pe end in
  let fv := list_fold_right FV_hypo_l_tac (@nil R) lH in
  list_fold_right FV_hypo_r_tac fv lH.

Ltac mkHyp_tac C req Reify lH :=
  let mkHyp h res :=
   match h with
   | @mkhypo (req ?r1 ?r2) _ =>
     let pe1 := Reify r1 in
     let pe2 := Reify r2 in
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

Ltac get_MonPol lemma :=
  match type of lemma with
  | context [(mk_monpol_list ?cO ?cI ?cadd ?cmul ?csub ?copp ?cdiv ?ceqb _)] =>
      constr:(mk_monpol_list cO cI cadd cmul csub copp cdiv ceqb)
  | _ => fail 1 "ring/field anomaly: bad correctness lemma (get_MonPol)"
  end.

(********************************************************)

(* Building the atom list of a ring expression *)
(* We do not assume that Cst recognizes the rO and rI terms as constants, as *)
(* the tactic could be used to discriminate occurrences of an opaque *)
(* constant phi, with (phi 0) not convertible to 0 for instance *)
Ltac FV Cst CstPow rO rI add mul sub opp pow t fv :=
 let rec TFV t fv :=
  let f :=
  match Cst t with
  | NotConstant =>
      match t with
      | rO =>  fun _ => fv
      | rI =>  fun _ => fv
      | (add ?t1 ?t2) => fun _ => TFV t2 ltac:(TFV t1 fv)
      | (mul ?t1 ?t2) => fun _ => TFV t2 ltac:(TFV t1 fv)
      | (sub ?t1 ?t2) => fun _ => TFV t2 ltac:(TFV t1 fv)
      | (opp ?t1) => fun _ => TFV t1 fv
      | (pow ?t1 ?n) =>
        match CstPow n with
        | InitialRing.NotConstant => fun _ => AddFvTail t fv
        | _ => fun _ => TFV t1 fv
        end
      | _ => fun _ => AddFvTail t fv
      end
  | _ => fun _ => fv
  end in
  f()
 in TFV t fv.

 (* syntaxification of ring expressions *)
 (* We do not assume that Cst recognizes the rO and rI terms as constants, as *)
 (* the tactic could be used to discriminate occurrences of an opaque *)
 (* constant phi, with (phi 0) not convertible to 0 for instance *)
Ltac mkPolexpr C Cst CstPow rO rI radd rmul rsub ropp rpow t fv :=
 let rec mkP t :=
    let f :=
    match Cst t with
    | InitialRing.NotConstant =>
        match t with
        | rO => 
          fun _ => constr:(@PEO C)
        | rI => 
          fun _ => constr:(@PEI C)
        | (radd ?t1 ?t2) =>
          fun _ =>
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(@PEadd C e1 e2)
        | (rmul ?t1 ?t2) =>
          fun _ =>
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(@PEmul C e1 e2)
        | (rsub ?t1 ?t2) =>
          fun _ =>
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(@PEsub C e1 e2)
        | (ropp ?t1) =>
          fun _ =>
          let e1 := mkP t1 in constr:(@PEopp C e1)
        | (rpow ?t1 ?n) =>
          match CstPow n with
          | InitialRing.NotConstant =>
            fun _ => let p := Find_at t fv in constr:(PEX C p)
          | ?c => fun _ => let e1 := mkP t1 in constr:(@PEpow C e1 c)
          end
        | _ =>
          fun _ => let p := Find_at t fv in constr:(PEX C p)
        end
    | ?c => fun _ => constr:(@PEc C c)
    end in
    f ()
 in mkP t.

(* packaging the ring structure *)

Ltac PackRing F req sth ext morph arth cst_tac pow_tac lemma1 lemma2 pre post :=
  let RNG :=
    match type of lemma1 with
    | context
       [@PEeval ?R ?r0 ?r1 ?add ?mul ?sub ?opp ?C ?phi ?Cpow ?powphi ?pow _ _] =>
        (fun proj => proj
             cst_tac pow_tac pre post
             R req r0 r1 add mul sub opp C Cpow powphi pow lemma1 lemma2)
    | _ => fail 1 "field anomaly: bad correctness lemma (parse)"
    end in
  F RNG.

Ltac get_Carrier RNG :=
  RNG ltac:(fun cst_tac pow_tac pre post
             R req r0 r1 add mul sub opp C Cpow powphi pow lemma1 lemma2 =>
            R).

Ltac get_Eq RNG :=
  RNG ltac:(fun cst_tac pow_tac pre post
             R req r0 r1 add mul sub opp C Cpow powphi pow lemma1 lemma2 =>
            req).

Ltac get_Pre RNG :=
  RNG ltac:(fun cst_tac pow_tac pre post
             R req r0 r1 add mul sub opp C Cpow powphi pow lemma1 lemma2 =>
            pre).

Ltac get_Post RNG :=
  RNG ltac:(fun cst_tac pow_tac pre post
             R req r0 r1 add mul sub opp C Cpow powphi pow lemma1 lemma2 =>
            post).

Ltac get_NormLemma RNG :=
  RNG ltac:(fun cst_tac pow_tac pre post
             R req r0 r1 add mul sub opp C Cpow powphi pow lemma1 lemma2 =>
            lemma1).

Ltac get_SimplifyLemma RNG :=
  RNG ltac:(fun cst_tac pow_tac pre post
             R req r0 r1 add mul sub opp C Cpow powphi pow lemma1 lemma2 =>
            lemma2).

Ltac get_RingFV RNG :=
  RNG ltac:(fun cst_tac pow_tac pre post
             R req r0 r1 add mul sub opp C Cpow powphi pow lemma1 lemma2 =>
            FV cst_tac pow_tac r0 r1 add mul sub opp pow).

Ltac get_RingMeta RNG :=
  RNG ltac:(fun cst_tac pow_tac pre post
             R req r0 r1 add mul sub opp C Cpow powphi pow lemma1 lemma2 =>
            mkPolexpr C cst_tac pow_tac r0 r1 add mul sub opp pow).

Ltac get_RingHypTac RNG :=
  RNG ltac:(fun cst_tac pow_tac pre post
             R req r0 r1 add mul sub opp C Cpow powphi pow lemma1 lemma2 =>
       let mkPol := mkPolexpr C cst_tac pow_tac r0 r1 add mul sub opp pow in
       fun fv lH => mkHyp_tac C req ltac:(fun t => mkPol t fv) lH).

(* ring tactics *)

Definition ring_subst_niter := (10*10*10)%nat.

Ltac Ring RNG lemma lH :=
  let req := get_Eq RNG in
  OnEquation req ltac:(fun lhs rhs =>
    let mkFV := get_RingFV RNG in
    let mkPol := get_RingMeta RNG in
    let mkHyp := get_RingHypTac RNG in
    let fv := FV_hypo_tac mkFV ltac:(get_Eq RNG) lH in
    let fv := mkFV lhs fv in
    let fv := mkFV rhs fv in
    check_fv fv;
    let pe1 := mkPol lhs fv in
    let pe2 := mkPol rhs fv in
    let lpe := mkHyp fv lH in
    let vlpe := fresh "hyp_list" in
    let vfv := fresh "fv_list" in
    pose (vlpe := lpe);
    pose (vfv := fv);
    (apply (lemma vfv vlpe pe1 pe2)
      || fail "typing error while applying ring");
    [ ((let prh := proofHyp_tac lH in exact prh)
        || idtac "can not automatically prove hypothesis :";
           [> idtac " maybe a left member of a hypothesis is not a monomial"..])
    | vm_compute;
      (exact (eq_refl true) || fail "not a valid ring equation")]).

Ltac Ring_norm_gen f RNG lemma lH rl :=
  let mkFV := get_RingFV RNG in
  let mkPol := get_RingMeta RNG in
  let mkHyp := get_RingHypTac RNG in
  let mk_monpol := get_MonPol lemma in
  let fv := FV_hypo_tac mkFV ltac:(get_Eq RNG) lH in
  let lemma_tac fv kont :=
    let lpe := mkHyp fv lH in
    let vlpe := fresh "list_hyp" in
    let vlmp := fresh "list_hyp_norm" in
    let vlmp_eq := fresh "list_hyp_norm_eq" in
    let prh := proofHyp_tac lH in
    pose (vlpe := lpe);
    compute_assertion vlmp_eq vlmp (mk_monpol vlpe);
    let H := fresh "ring_lemma" in
    (assert (H := lemma vlpe fv prh vlmp vlmp_eq)
      || fail "type error when build the rewriting lemma");
    clear vlmp_eq;
    kont H;
    (clear H||idtac"Ring_norm_gen: cleanup failed");
    subst vlpe vlmp in
  let simpl_ring H := (protect_fv "ring" in H; f H) in
  ReflexiveRewriteTactic mkFV mkPol lemma_tac simpl_ring fv rl.

Ltac Ring_gen RNG lH rl :=
  let lemma := get_NormLemma RNG in
  get_Pre RNG ();
  Ring RNG (lemma ring_subst_niter) lH.

Tactic Notation (at level 0) "ring" :=
  let G := Get_goal in
  ring_lookup (PackRing Ring_gen) [] G.

Tactic Notation (at level 0) "ring" "[" constr_list(lH) "]" :=
  let G := Get_goal in
  ring_lookup (PackRing Ring_gen) [lH] G.

(* Simplification *)

Ltac Ring_simplify_gen f RNG lH rl :=
  let lemma := get_SimplifyLemma RNG in
  let l := fresh "to_rewrite" in
  pose (l:= rl);
  generalize (eq_refl l);
  unfold l at 2;
  get_Pre RNG ();
  let rl :=
    match goal with
    | [|- l = ?RL -> _ ] => RL
    | _ => fail 1 "ring_simplify anomaly: bad goal after pre"
    end in
  let Heq := fresh "Heq" in
  intros Heq;clear Heq l;
  Ring_norm_gen f RNG (lemma ring_subst_niter) lH rl;
  get_Post RNG ().

Ltac Ring_simplify := Ring_simplify_gen ltac:(fun H => rewrite H).

Tactic Notation (at level 0) "ring_simplify" constr_list(rl) :=
  let G := Get_goal in
  ring_lookup (PackRing Ring_simplify) [] rl G.

Tactic Notation (at level 0)
  "ring_simplify" "[" constr_list(lH) "]" constr_list(rl) :=
  let G := Get_goal in
  ring_lookup (PackRing Ring_simplify) [lH] rl G.

Tactic Notation "ring_simplify" constr_list(rl) "in" hyp(H):=
  let G := Get_goal in
  let t := type of H in
  let g := fresh "goal" in
  set (g:= G);
  generalize H;
  ring_lookup (PackRing Ring_simplify) [] rl t;
  (* 
     Correction of bug 1859:
     we want to leave H at its initial position
     this is obtained by adding a copy of H (H'), 
     move it just after H, remove H and finally 
     rename H into H'
   *)
  let H' := fresh "H" in
  intro H';
  move H' after H;
  clear H;rename H' into H;
  unfold g;clear g.

Tactic Notation "ring_simplify" "["constr_list(lH)"]" constr_list(rl) "in" hyp(H):=
  let G := Get_goal in
  let t := type of H in
  let g := fresh "goal" in
  set (g:= G);
  generalize H;
  ring_lookup (PackRing Ring_simplify) [lH] rl t;
  (* 
     Correction of bug 1859:
     we want to leave H at its initial position
     this is obtained by adding a copy of H (H'), 
     move it just after H, remove H and finally 
     rename H into H'
   *)
  let H' := fresh "H" in
  intro H';
  move H' after H;
  clear H;rename H' into H;
  unfold g;clear g.
