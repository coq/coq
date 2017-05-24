(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(*                              EqDecide                               *)
(*   A tactic for deciding propositional equality on inductive types   *)
(*                           by Eduardo Gimenez                        *)
(************************************************************************)

open Util
open Names
open Namegen
open Term
open EConstr
open Declarations
open Tactics
open Tacticals.New
open Auto
open Constr_matching
open Misctypes
open Tactypes
open Hipattern
open Proofview.Notations
open Tacmach.New
open Coqlib

(* This file containts the implementation of the tactics ``Decide
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
    left_with_bindings false Misctypes.NoBindings
  else
    right_with_bindings false Misctypes.NoBindings
let choose_noteq eqonleft =
  if eqonleft then
    right_with_bindings false Misctypes.NoBindings
  else
    left_with_bindings false Misctypes.NoBindings

open Sigma.Notations

(* A surgical generalize which selects the right occurrences by hand *)
(* This prevents issues where c2 is also a subterm of c1 (see e.g. #5449) *)

let generalize_right mk typ c1 c2 =
  Proofview.Goal.enter { Proofview.Goal.enter = begin fun gl ->
    let env = Proofview.Goal.env gl in
    let store = Proofview.Goal.extra gl in
  Refine.refine ~unsafe:true { Sigma.run = begin fun sigma ->
    let na = Name (next_name_away_with_default "x" Anonymous (Termops.ids_of_context env)) in
    let newconcl = mkProd (na, typ, mk typ c1 (mkRel 1)) in
    let Sigma (x, sigma, p) = Evarutil.new_evar env sigma ~principal:true ~store newconcl in
    Sigma (mkApp (x, [|c2|]), sigma, p)
  end }
  end }

let mkBranches (eqonleft,mk,c1,c2,typ) =
  tclTHENLIST
    [generalize_right mk typ c1 c2;
     Simple.elim c1;
     intros;
     onLastHyp Simple.case;
     clear_last;
     intros]

let discrHyp id =
  let c = { delayed = fun env sigma -> Sigma.here (mkVar id, NoBindings) sigma } in
  let tac c = Equality.discr_tac false (Some (None, ElimOnConstr c)) in
  Tacticals.New.tclDELAYEDWITHHOLES false c tac

let solveNoteqBranch side =
  tclTHEN (choose_noteq side)
    (tclTHEN introf
      (onLastHypId (fun id -> discrHyp id)))

(* Constructs the type {c1=c2}+{~c1=c2} *)

let make_eq () =
(*FIXME*) EConstr.of_constr (Universes.constr_of_global (Coqlib.build_coq_eq ()))
let build_coq_not () = EConstr.of_constr (build_coq_not ())
let build_coq_sumbool () = EConstr.of_constr (build_coq_sumbool ())

let mkDecideEqGoal eqonleft op rectype c1 c2 =
  let equality    = mkApp(make_eq(), [|rectype; c1; c2|]) in
  let disequality = mkApp(build_coq_not (), [|equality|]) in
  if eqonleft then mkApp(op, [|equality; disequality |])
  else mkApp(op, [|disequality; equality |])


(* Constructs the type (x1,x2:R){x1=x2}+{~x1=x2} *)

let idx = Id.of_string "x"
let idy = Id.of_string "y"

let mkGenDecideEqGoal rectype g =
  let hypnames = pf_ids_of_hyps g in
  let xname    = next_ident_away idx hypnames
  and yname    = next_ident_away idy hypnames in
  (mkNamedProd xname rectype
     (mkNamedProd yname rectype
        (mkDecideEqGoal true (build_coq_sumbool ())
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
  let c = { delayed = fun env sigma -> Sigma.here (mkVar id, NoBindings) sigma } in
  let tac c = Equality.injClause None false (Some (None, ElimOnConstr c)) in
  Tacticals.New.tclDELAYEDWITHHOLES false c tac

let diseqCase hyps eqonleft =
  let diseq  = Id.of_string "diseq" in
  let absurd = Id.of_string "absurd" in
  (tclTHEN (intro_using diseq)
  (tclTHEN (choose_noteq eqonleft)
  (tclTHEN (rewrite_and_clear (List.rev hyps))
  (tclTHEN  (red_in_concl)
  (tclTHEN  (intro_using absurd)
  (tclTHEN  (Simple.apply (mkVar diseq))
  (tclTHEN  (injHyp absurd)
            (full_trivial []))))))))

open Proofview.Notations

(* spiwack: a PatternMatchingFailure wrapper around [Hipattern]. *)

let match_eqdec sigma c =
  try
    let (eqonleft,_,c1,c2,ty) = match_eqdec sigma c in
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
    let mk t x y =
      let eq = mkApp (eq1,[|t;x;y|]) in
      let neq = mkApp (noteq,[|mkApp (eq2,[|t;x;y|])|]) in
      if eqonleft then mkApp (op,[|eq;neq|]) else mkApp (op,[|neq;eq|]) in
    Proofview.tclUNIT (eqonleft,mk,c1,c2,ty)
  with PatternMatchingFailure -> Proofview.tclZERO PatternMatchingFailure

(* /spiwack *)

let rec solveArg hyps eqonleft mk largs rargs = match largs, rargs with
| [], [] ->
  tclTHENLIST [
    choose_eq eqonleft;
    rewrite_and_clear (List.rev hyps);
    intros_reflexivity;
  ]
| a1 :: largs, a2 :: rargs ->
  Proofview.Goal.enter { enter = begin fun gl ->
  let rectype = pf_unsafe_type_of gl a1 in
  let decide = mk rectype a1 a2 in
  let tac hyp = solveArg (hyp :: hyps) eqonleft mk largs rargs in
  let subtacs =
    if eqonleft then [eqCase tac;diseqCase hyps eqonleft;default_auto]
    else [diseqCase hyps eqonleft;eqCase tac;default_auto] in
  (tclTHENS (elim_type decide) subtacs)
  end }
| _ -> invalid_arg "List.fold_right2"

let solveEqBranch rectype =
  Proofview.tclORELSE
    begin
      Proofview.Goal.enter { enter = begin fun gl ->
        let concl = pf_concl gl in
        let sigma = project gl in
        match_eqdec sigma concl >>= fun (eqonleft,mk,lhs,rhs,_) ->
          let (mib,mip) = Global.lookup_inductive rectype in
          let nparams   = mib.mind_nparams in
          let getargs l = List.skipn nparams (snd (decompose_app sigma l)) in
          let rargs   = getargs rhs
          and largs   = getargs lhs in
          solveArg [] eqonleft mk largs rargs
      end }
    end
    begin function (e, info) -> match e with
      | PatternMatchingFailure -> Tacticals.New.tclZEROMSG (Pp.str"Unexpected conclusion!")
      | e -> Proofview.tclZERO ~info e
    end

(* The tactic Decide Equality *)

let hd_app sigma c = match EConstr.kind sigma c with
  | App (h,_) -> h
  | _ -> c

let decideGralEquality =
  Proofview.tclORELSE
    begin
      Proofview.Goal.enter { enter = begin fun gl ->
        let concl = pf_concl gl in
        let sigma = project gl in
        match_eqdec sigma concl >>= fun (eqonleft,mk,c1,c2,typ as data) ->
        let headtyp = hd_app sigma (pf_compute gl typ) in
        begin match EConstr.kind sigma headtyp with
        | Ind (mi,_) -> Proofview.tclUNIT mi
        | _ -> tclZEROMSG (Pp.str"This decision procedure only works for inductive objects.")
        end >>= fun rectype ->
          (tclTHEN
             (mkBranches data)
             (tclORELSE (solveNoteqBranch eqonleft) (solveEqBranch rectype)))
      end }
    end
    begin function (e, info) -> match e with
      | PatternMatchingFailure ->
          Tacticals.New.tclZEROMSG (Pp.str"The goal must be of the form {x<>y}+{x=y} or {x=y}+{x<>y}.")
      | e -> Proofview.tclZERO ~info e
    end

let decideEqualityGoal = tclTHEN intros decideGralEquality

let decideEquality rectype =
  Proofview.Goal.enter { enter = begin fun gl ->
  let decide = mkGenDecideEqGoal rectype gl in
  (tclTHENS (cut decide) [default_auto;decideEqualityGoal])
  end }


(* The tactic Compare *)

let compare c1 c2 =
  Proofview.Goal.enter { enter = begin fun gl ->
  let rectype = pf_unsafe_type_of gl c1 in
  let decide = mkDecideEqGoal true (build_coq_sumbool ()) rectype c1 c2 in
  (tclTHENS (cut decide)
            [(tclTHEN  intro
             (tclTHEN (onLastHyp simplest_case) clear_last));
             decideEquality rectype])
  end }
