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
open Declarations
open Tactics
open Tacticals.New
open Auto
open Constr_matching
open Misctypes
open Tactypes
open Hipattern
open Pretyping
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

let clear_last = (onLastHyp (fun c -> (clear [destVar c])))

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

let mkBranches c1 c2 =
  tclTHENLIST
    [generalize [c2];
     Simple.elim c1;
     intros;
     onLastHyp Simple.case;
     clear_last;
     intros]

let discrHyp id =
  let c = { delayed = fun env sigma -> Sigma.here (Term.mkVar id, NoBindings) sigma } in
  let tac c = Equality.discr_tac false (Some (None, ElimOnConstr c)) in
  Tacticals.New.tclDELAYEDWITHHOLES false c tac

let solveNoteqBranch side =
  tclTHEN (choose_noteq side)
    (tclTHEN introf
      (onLastHypId (fun id -> discrHyp id)))

(* Constructs the type {c1=c2}+{~c1=c2} *)

let make_eq () =
(*FIXME*) Universes.constr_of_global (Coqlib.build_coq_eq ())

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
  let c = { delayed = fun env sigma -> Sigma.here (Term.mkVar id, NoBindings) sigma } in
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

(* spiwack: a small wrapper around [Hipattern]. *)

let match_eqdec c =
  try Proofview.tclUNIT (match_eqdec c)
  with PatternMatchingFailure -> Proofview.tclZERO PatternMatchingFailure

(* /spiwack *)

let rec solveArg hyps eqonleft op largs rargs = match largs, rargs with
| [], [] ->
  tclTHENLIST [
    choose_eq eqonleft;
    rewrite_and_clear (List.rev hyps);
    intros_reflexivity;
  ]
| a1 :: largs, a2 :: rargs ->
  Proofview.Goal.enter { enter = begin fun gl ->
  let rectype = pf_unsafe_type_of gl a1 in
  let decide = mkDecideEqGoal eqonleft op rectype a1 a2 in
  let tac hyp = solveArg (hyp :: hyps) eqonleft op largs rargs in
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
        let concl = pf_nf_concl gl in
        match_eqdec concl >>= fun (eqonleft,op,lhs,rhs,_) ->
          let (mib,mip) = Global.lookup_inductive rectype in
          let nparams   = mib.mind_nparams in
          let getargs l = List.skipn nparams (snd (decompose_app l)) in
          let rargs   = getargs rhs
          and largs   = getargs lhs in
          solveArg [] eqonleft op largs rargs
      end }
    end
    begin function (e, info) -> match e with
      | PatternMatchingFailure -> Tacticals.New.tclZEROMSG (Pp.str"Unexpected conclusion!")
      | e -> Proofview.tclZERO ~info e
    end

(* The tactic Decide Equality *)

let hd_app c = match kind_of_term c with
  | App (h,_) -> h
  | _ -> c

let decideGralEquality =
  Proofview.tclORELSE
    begin
      Proofview.Goal.enter { enter = begin fun gl ->
        let concl = pf_nf_concl gl in
        match_eqdec concl >>= fun (eqonleft,_,c1,c2,typ) ->
        let headtyp = hd_app (pf_compute gl typ) in
        begin match kind_of_term headtyp with
        | Ind (mi,_) -> Proofview.tclUNIT mi
        | _ -> tclZEROMSG (Pp.str"This decision procedure only works for inductive objects.")
        end >>= fun rectype ->
          (tclTHEN
             (mkBranches c1 c2)
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
