Set Implicit Arguments.
Require Import Setoid.
Require Import BinPos.
Require Import Ring_polynom.
Require Import BinList.
Declare ML Module "newring".


(* adds a definition id' on the normal form of t and an hypothesis id
   stating that t = id' (tries to produces a proof as small as possible) *)
Ltac compute_assertion id  id' t :=
  let t' := eval vm_compute in t in
  (pose (id' := t');
   assert (id : t = id');
   [exact_no_check (refl_equal id')|idtac]).

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
     (fun tac => (lapply H; [clear H; intro H; subtac tac | idtac]))
  | _ => (fun tac => tac)
  end.

Ltac ApplyLemmaAndSimpl tac lemma pe:=
  let npe := fresh "ast_nf" in
  let H := fresh "eq_nf" in
  let Heq := fresh "thm" in
  let npe_spec :=
    match type of (lemma pe) with
      forall npe, ?npe_spec = npe -> _ => npe_spec
    | _ => fail 1 "ApplyLemmaAndSimpl: cannot find norm expression"
    end in
  (compute_assertion H npe npe_spec;
   (assert (Heq:=lemma _ _ H) || fail "anomaly: failed to apply lemma");
   clear H;
   OnMainSubgoal Heq ltac:(type of Heq)
     ltac:(tac Heq; rewrite Heq; clear Heq npe)).

(* General scheme of reflexive tactics using of correctness lemma
   that involves normalisation of one expression *)
Ltac ReflexiveRewriteTactic FV_tac SYN_tac SIMPL_tac lemma2 req rl :=
  let R := match type of req with ?R -> _ => R end in
  (* build the atom list *)
  let fv := list_fold_left FV_tac (@List.nil R) rl in
  (* some type-checking to avoid late errors *)
  (check_fv fv;
   (* rewrite steps *)
   list_iter
     ltac:(fun r =>
       let ast := SYN_tac r fv in
       (try ApplyLemmaAndSimpl SIMPL_tac (lemma2 fv) ast))
     rl).

(********************************************************)

(* An object to return when an expression is not recognized as a constant *)
Definition NotConstant := false.
		      
(* Building the atom list of a ring expression *)
Ltac FV Cst add mul sub opp t fv :=
 let rec TFV t fv :=
  match Cst t with
  | NotConstant =>
      match t with
      | (add ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (mul ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (sub ?t1 ?t2) => TFV t2 ltac:(TFV t1 fv)
      | (opp ?t1) => TFV t1 fv
      | _ => AddFvTail t fv
      end
  | _ => fv
  end
 in TFV t fv.

 (* syntaxification of ring expressions *)
 Ltac mkPolexpr C Cst radd rmul rsub ropp t fv := 
 let rec mkP t :=
    match Cst t with
    | NotConstant =>
        match t with 
        | (radd ?t1 ?t2) => 
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(PEadd e1 e2)
        | (rmul ?t1 ?t2) => 
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(PEmul e1 e2)
        | (rsub ?t1 ?t2) => 
          let e1 := mkP t1 in
          let e2 := mkP t2 in constr:(PEsub e1 e2)
        | (ropp ?t1) =>
          let e1 := mkP t1 in constr:(PEopp e1)
        | _ =>
          let p := Find_at t fv in constr:(PEX C p)
        end
    | ?c => constr:(PEc c)
    end
 in mkP t.

(* ring tactics *)

 Ltac Ring Cst_tac lemma1 req :=
  let Make_tac :=
    match type of lemma1 with
    | forall (l:list ?R) (pe1 pe2:PExpr ?C),
      _ = true ->
      req (PEeval ?rO ?add ?mul ?sub ?opp ?phi l pe1) _ =>
        let mkFV := FV Cst_tac add mul sub opp in
        let mkPol := mkPolexpr C Cst_tac add mul sub opp in
        (fun f => f R mkFV mkPol)
    | _ => fail 1 "ring anomaly: bad correctness lemma"
    end in
  let Main r1 r2 R mkFV mkPol :=
    let fv := mkFV r1 (@List.nil R) in
    let fv := mkFV r2 fv in
    (check_fv fv;
     let pe1 := mkPol r1 fv in
     let pe2 := mkPol r2 fv in
     (apply (lemma1 fv pe1 pe2) || fail "typing error while applying ring");
     vm_compute;
     (exact (refl_equal true) || fail "not a valid ring equation")) in
  Make_tac ltac:(OnEquation req Main).

Ltac Ring_simplify Cst_tac lemma2 req rl :=
  let Make_tac :=
    match type of lemma2 with 
      forall (l:list ?R) (pe:PExpr ?C) (npe:Pol ?C),
      _ = npe ->
      req (PEeval ?rO ?add ?mul ?sub ?opp ?phi l pe) _ =>
      let mkFV := FV Cst_tac add mul sub opp in
      let mkPol := mkPolexpr C Cst_tac add mul sub opp in
      let simpl_ring H := protect_fv "ring" in H in
      (fun tac => tac mkFV mkPol simpl_ring lemma2 req rl)
    | _ => fail 1 "ring anomaly: bad correctness lemma"
    end in
  Make_tac ReflexiveRewriteTactic.


Tactic Notation (at level 0) "ring" :=
  ring_lookup
    (fun req sth ext morph arth cst_tac lemma1 lemma2 pre post rl =>
       (pre(); Ring cst_tac lemma1 req)).

Tactic Notation (at level 0) "ring_simplify" constr_list(rl) :=
  ring_lookup
    (fun req sth ext morph arth cst_tac lemma1 lemma2 pre post rl =>
       (pre(); Ring_simplify cst_tac lemma2 req rl; post())) rl.

(* A simple macro tactic to be prefered to ring_simplify *)
Ltac ring_replace t1 t2 := replace t1 with t2 by ring.
