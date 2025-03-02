(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(*                              EqDecide                               *)
(*   A tactic for deciding propositional equality on inductive types   *)
(*                           by Eduardo Gimenez                        *)
(************************************************************************)

open Util
open Names
open Namegen
open Constr
open Context
open EConstr
open Declarations
open Tactics
open Tacticals
open Auto
open Constr_matching
open Hipattern
open Proofview.Notations
open Tacmach
open Tactypes

(* This file contains the implementation of the tactics ``Decide
   Equality'' and ``Compare''. They can be used to decide the
   propositional equality of two objects that belongs to a small
   inductive datatype --i.e., an inductive set such that all the
   arguments of its constructors are non-functional sets.

   The procedure for proving (x,y:R){x=y}+{~x=y} can be scketched as
   follows:
   1. Eliminate x and then y.
   2. Try discrimination to solve those goals where x and y has
      been introduced by different constructors.
   3. If x and y have been introduced by the same constructor,
      then analyse one by one the corresponding pairs of arguments.
      If they are equal, rewrite one into the other. If they are
      not, derive a contradiction from the injectiveness of the
      constructor.
   4. Once all the arguments have been rewritten, solve the remaining half
      of the disjunction by reflexivity.

   Eduardo Gimenez (30/3/98).
*)

let clear_last =
  Proofview.tclEVARMAP >>= fun sigma ->
  (onLastHyp (fun c -> (clear [destVar sigma c])))

let choose_eq eqonleft =
  if eqonleft then
    left_with_bindings false NoBindings
  else
    right_with_bindings false NoBindings
let choose_noteq eqonleft =
  if eqonleft then
    right_with_bindings false NoBindings
  else
    left_with_bindings false NoBindings

(* A surgical generalize which selects the right occurrences by hand *)
(* This prevents issues where c2 is also a subterm of c1 (see e.g. #5449) *)

type dectype = {
  eqonleft : bool;
  op : EConstr.t;
  eq1 : EConstr.t;
  eq2 : EConstr.t;
  noteq : EConstr.t;
}

let mk_dectype { eqonleft; op; eq1; eq2; noteq } t x y =
  let eq = mkApp (eq1,[|t;x;y|]) in
  let neq = mkApp (noteq,[|mkApp (eq2,[|t;x;y|])|]) in
  if eqonleft then mkApp (op,[|eq;neq|]) else mkApp (op,[|neq;eq|])

let generalize_right dty typ c1 c2 =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
  Refine.refine_with_principal ~typecheck:false begin fun sigma ->
    let na = Name (next_name_away_with_default "x" Anonymous (Termops.vars_of_env env)) in
    let r = Retyping.relevance_of_type env sigma typ in
    let newconcl = mkProd (make_annot na r, typ, mk_dectype dty typ c1 (mkRel 1)) in
    let (sigma, x) = Evarutil.new_evar env sigma newconcl in
    (sigma, mkApp (x, [|c2|]), Some (fst @@ destEvar sigma x))
  end
  end

let mkBranches (dty, c1, c2, typ) =
  tclTHENLIST
    [generalize_right dty typ c1 c2;
     Simple.elim c1;
     intros;
     onLastHyp Simple.case;
     clear_last;
     intros]

let inj_flags = Some {
    Equality.keep_proof_equalities = true; (* necessary *)
    Equality.injection_pattern_l2r_order = true; (* does not matter here *)
  }

let discrHyp id =
  let c env sigma = (sigma, (mkVar id, NoBindings)) in
  let tac c = Equality.discr_tac false (Some (None, ElimOnConstr c)) in
  Tacticals.tclDELAYEDWITHHOLES false c tac

let solveNoteqBranch side =
  tclTHEN (choose_noteq side)
    (tclTHEN introf
      (onLastHypId (fun id -> discrHyp id)))

(* Constructs the type {c1=c2}+{~c1=c2} *)

let mkDecideEqGoal eqonleft (op,eq,neg) rectype c1 c2 =
  let equality    = mkApp(eq, [|rectype; c1; c2|]) in
  let disequality = mkApp(neg, [|equality|]) in
  if eqonleft then mkApp(op, [|equality; disequality |])
  else mkApp(op, [|disequality; equality |])


(* Constructs the type (x1,x2:R){x1=x2}+{~x1=x2} *)

let idx = Id.of_string "x"
let idy = Id.of_string "y"

let mkGenDecideEqGoal rectype ops g =
  let sigma = Proofview.Goal.sigma g in
  let hypnames = pf_ids_set_of_hyps g in
  let xname    = next_ident_away idx hypnames in
  let yname    = next_ident_away idy (Id.Set.add xname hypnames) in
  (mkNamedProd sigma (make_annot xname ERelevance.relevant) rectype
     (mkNamedProd sigma (make_annot yname ERelevance.relevant) rectype
        (mkDecideEqGoal true ops
          rectype (mkVar xname) (mkVar yname))))

let rec rewrite_and_clear hyps = match hyps with
| [] -> Proofview.tclUNIT ()
| id :: hyps ->
  tclTHENLIST [
    Equality.rewriteLR (mkVar id);
    clear [id];
    rewrite_and_clear hyps;
  ]

let eqCase tac =
  tclTHEN intro (onLastHypId tac)

let injHyp id =
  let c env sigma = (sigma, (mkVar id, NoBindings)) in
  let tac c = Equality.injClause inj_flags None false (Some (None, ElimOnConstr c)) in
  Tacticals.tclDELAYEDWITHHOLES false c tac

let diseqCase hyps eqonleft =
  let diseq  = Id.of_string "diseq" in
  let absurd = Id.of_string "absurd" in
  (intro_using_then diseq (fun diseq ->
  tclTHEN (choose_noteq eqonleft)
  (tclTHEN (rewrite_and_clear (List.rev hyps))
  (tclTHEN  (red_in_concl)
  (intro_using_then absurd (fun absurd ->
  tclTHEN  (Simple.apply (mkVar diseq))
  (tclTHEN  (injHyp absurd)
            (Auto.gen_trivial [] None))))))))

open Proofview.Notations

(* spiwack: a PatternMatchingFailure wrapper around [Hipattern]. *)

let match_eqdec env sigma c =
  try
    let (eqonleft,_,c1,c2,ty) = match_eqdec env sigma c in
    let (op,eq1,noteq,eq2) =
      match EConstr.kind sigma c with
      | App (op,[|ty1;ty2|]) ->
         let ty1, ty2 = if eqonleft then ty1, ty2 else ty2, ty1 in
         (match EConstr.kind sigma ty1, EConstr.kind sigma ty2 with
         | App (eq1,_), App (noteq,[|neq|]) ->
            (match EConstr.kind sigma neq with
             | App (eq2,_) -> op,eq1,noteq,eq2
             | _ -> assert false)
         | _ -> assert false)
      | _ -> assert false in
    let dty = { eqonleft; op; eq1; eq2; noteq } in
    Proofview.tclUNIT (dty, c1, c2, ty)
  with PatternMatchingFailure as exn ->
    let _, info = Exninfo.capture exn in
    Proofview.tclZERO ~info PatternMatchingFailure

(* /spiwack *)

let elim_type dty rectype a1 a2 =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let (ind, _) = Tacred.reduce_to_atomic_ind env sigma dty.op in
  let s = Tacticals.elimination_sort_of_goal gl in
  let elimc = Indrec.lookup_eliminator env (fst ind) s in
  (* Eliminator type is expected to have (potentially non-dependent) shape
      [forall A B (P : I A B -> Type), P _ -> P _ -> forall (s : I A B), P s ] *)
  let sigma, elimc = EConstr.fresh_global env sigma elimc in
  let elimc =
    let { eqonleft; eq1; eq2; noteq } = dty in
    let eq = mkApp (eq1,[|rectype;a1;a2|]) in
    let neq = mkApp (noteq,[|mkApp (eq2,[|rectype;a1;a2|])|]) in
    if eqonleft then mkApp (elimc, [|eq; neq|]) else mkApp (elimc, [|neq; eq|])
  in
  let elimt = Retyping.get_type_of env sigma elimc in
  let clause = Clenv.mk_clenv_from env sigma (elimc, elimt) in
  Proofview.Unsafe.tclEVARS sigma <*> Clenv.res_pf clause ~with_evars:false
  end

let rec solveArg hyps dty largs rargs = match largs, rargs with
| [], [] ->
  tclTHENLIST [
    choose_eq dty.eqonleft;
    rewrite_and_clear (List.rev hyps);
    intros_reflexivity;
  ]
| a1 :: largs, a2 :: rargs ->
  Proofview.Goal.enter begin fun gl ->
  let sigma, rectype = pf_type_of gl a1 in
  let tac hyp = solveArg (hyp :: hyps) dty largs rargs in
  let subtacs =
    if dty.eqonleft then [eqCase tac;diseqCase hyps dty.eqonleft;default_auto]
    else [diseqCase hyps dty.eqonleft;eqCase tac;default_auto] in
  tclTHEN (Proofview.Unsafe.tclEVARS sigma) (tclTHENS (elim_type dty rectype a1 a2) subtacs)
  end
| _ -> invalid_arg "List.fold_right2"

let solveEqBranch rectype =
  Proofview.tclORELSE
    begin
      Proofview.Goal.enter begin fun gl ->
        let concl = pf_concl gl in
        let env = Proofview.Goal.env gl in
        let sigma = project gl in
        match_eqdec env sigma concl >>= fun (dty, lhs, rhs,_) ->
          let (mib,mip) = Inductive.lookup_mind_specif env rectype in
          let nparams   = mib.mind_nparams in
          let getargs l = List.skipn nparams (snd (decompose_app_list sigma l)) in
          let rargs   = getargs rhs
          and largs   = getargs lhs in

          solveArg [] dty largs rargs
      end
    end
    begin function (e, info) -> match e with
      | PatternMatchingFailure -> Tacticals.tclZEROMSG (Pp.str"Unexpected conclusion!")
      | e -> Proofview.tclZERO ~info e
    end

(* The tactic Decide Equality *)

let hd_app sigma c = match EConstr.kind sigma c with
  | App (h,_) -> h
  | _ -> c

let decideGralEquality =
  Proofview.tclORELSE
    begin
      Proofview.Goal.enter begin fun gl ->
        let concl = pf_concl gl in
        let env = Proofview.Goal.env gl in
        let sigma = project gl in
        match_eqdec env sigma concl >>= fun (dty, c1, c2, typ as data) ->
        let headtyp = hd_app sigma (pf_whd_compute gl typ) in
        begin match EConstr.kind sigma headtyp with
        | Ind (mi,_) -> Proofview.tclUNIT mi
        | _ -> tclZEROMSG (Pp.str"This decision procedure only works for inductive objects.")
        end >>= fun rectype ->
          (tclTHEN
             (mkBranches data)
             (tclORELSE (solveNoteqBranch dty.eqonleft) (solveEqBranch rectype)))
      end
    end
    begin function (e, info) -> match e with
      | PatternMatchingFailure ->
          Tacticals.tclZEROMSG (Pp.str"The goal must be of the form {x<>y}+{x=y} or {x=y}+{x<>y}.")
      | e -> Proofview.tclZERO ~info e
    end

let decideEqualityGoal = tclTHEN intros decideGralEquality

let decideEquality rectype ops =
  Proofview.Goal.enter begin fun gl ->
  let decide = mkGenDecideEqGoal rectype ops gl in
  (tclTHENS (cut decide) [default_auto;decideEqualityGoal])
  end


(* The tactic Compare *)

let compare c1 c2 =
  let open Rocqlib in
  pf_constr_of_global (lib_ref "core.sumbool.type") >>= fun opc ->
  pf_constr_of_global (lib_ref "core.eq.type") >>= fun eqc ->
  pf_constr_of_global (lib_ref "core.not.type") >>= fun notc ->
  Proofview.Goal.enter begin fun gl ->
  let sigma, rectype = pf_type_of gl c1 in
  let ops = (opc,eqc,notc) in
  let decide = mkDecideEqGoal true ops rectype c1 c2 in
  tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (tclTHENS (cut decide)
       [(tclTHEN  intro
           (tclTHEN (onLastHyp simplest_case) clear_last));
        decideEquality rectype ops])
  end
