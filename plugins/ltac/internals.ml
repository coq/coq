(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open EConstr
open EConstr.Vars
open Names
open Tacexpr
open CErrors
open Util
open Termops
open Tactypes
open Tactics
open Proofview.Notations

let assert_succeeds tac =
  let open Proofview in
  let exception Succeeded in
  tclORELSE (tclONCE tac <*> tclZERO Succeeded) (function
      | Succeeded, _ -> tclUNIT ()
      | exn, info -> tclZERO ~info exn)

let mytclWithHoles tac with_evars c =
  Proofview.Goal.enter begin fun gl ->
    let env = Tacmach.pf_env gl in
    let sigma = Tacmach.project gl in
    let sigma',c = Tactics.force_destruction_arg with_evars env sigma c in
    Tacticals.tclWITHHOLES with_evars (tac with_evars (Some c)) sigma'
  end

(**********************************************************************)
(* replace, discriminate, injection, simplify_eq                      *)
(* dependent rewrite                                      *)

let with_delayed_uconstr ist c tac =
  let flags = Pretyping.{
    use_coercions = true;
    use_typeclasses = NoUseTC;
    solve_unification_constraints = true;
    fail_evar = false;
    expand_evars = true;
    program_mode = false;
    polymorphic = false;
    undeclared_evars_patvars = false;
    patvars_abstract = false;
    unconstrained_sorts = false;
 } in
  let c = Tacinterp.type_uconstr ~flags ist c in
  Tacticals.tclDELAYEDWITHHOLES false c tac

let replace_in_clause_maybe_by ist dir_opt c1 c2 cl tac =
  with_delayed_uconstr ist c1
  (fun c1 -> Equality.replace_in_clause_maybe_by dir_opt c1 c2 cl (Option.map (Tacinterp.tactic_of_value ist) tac))

let replace_term ist dir_opt c cl =
  with_delayed_uconstr ist c (fun c -> Equality.replace_term dir_opt c cl)

let elimOnConstrWithHoles tac with_evars c =
  Tacticals.tclDELAYEDWITHHOLES with_evars c
    (fun c -> tac with_evars (Some (None,ElimOnConstr c)))

let discr_main c = elimOnConstrWithHoles Equality.discr_tac false c

let discrHyp id =
  Proofview.tclEVARMAP >>= fun sigma ->
  discr_main (fun env sigma -> (sigma, (EConstr.mkVar id, NoBindings)))

let injection_main with_evars c =
 elimOnConstrWithHoles (Equality.injClause None None) with_evars c

let injHyp id =
  Proofview.tclEVARMAP >>= fun sigma ->
  injection_main false (fun env sigma -> (sigma, (EConstr.mkVar id, NoBindings)))

let constr_flags () = Pretyping.{
  use_coercions = true;
  use_typeclasses = UseTC;
  solve_unification_constraints = Proof.use_unification_heuristics ();
  fail_evar = false;
  expand_evars = true;
  program_mode = false;
  polymorphic = false;
  undeclared_evars_patvars = false;
  patvars_abstract = false;
  unconstrained_sorts = false;
}

let refine_tac ist ~simple ~with_classes c =
  let with_classes = if with_classes then Pretyping.UseTC else Pretyping.NoUseTC in
  Proofview.Goal.enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let env = Proofview.Goal.env gl in
    let flags =
      { (constr_flags ()) with Pretyping.use_typeclasses = with_classes } in
    let expected_type = Pretyping.OfType concl in
    let c = Tacinterp.type_uconstr ~flags ~expected_type ist c in
    let update = begin fun sigma ->
      c env sigma
    end in
    let refine = Refine.refine ~typecheck:false update in
    if simple then refine
    else refine <*>
           Tactics.reduce_after_refine <*>
           Proofview.shelve_unifiable
  end

(**********************************************************************)

(**********************************************************************)
(* A tactic that reduces one match t with ... by doing destruct t.    *)
(* if t is not a variable, the tactic does                            *)
(* case_eq t;intros ... heq;rewrite heq in *|-. (but heq itself is    *)
(* preserved).                                                        *)
(* Contributed by Julien Forest and Pierre Courtieu (july 2010)       *)
(**********************************************************************)

let induction_arg_of_quantified_hyp = function
  | AnonHyp n -> None,ElimOnAnonHyp n
  | NamedHyp id -> None,ElimOnIdent id

exception Found of unit Proofview.tactic

let rewrite_except h =
  Proofview.Goal.enter begin fun gl ->
  let hyps = Tacmach.pf_ids_of_hyps gl in
  Tacticals.tclMAP (fun id -> if Id.equal id h then Proofview.tclUNIT () else
      Tacticals.tclTRY (Equality.general_rewrite ~where:(Some id) ~l2r:true Locus.AllOccurrences ~freeze:true ~dep:true ~with_evars:false (mkVar h, NoBindings)))
    hyps
  end


let refl_equal () = Rocqlib.lib_ref "core.eq.type"

(* This is simply an implementation of the case_eq tactic.  this code
  should be replaced by a call to the tactic but I don't know how to
  call it before it is defined. *)
let  mkCaseEq a  : unit Proofview.tactic =
  Proofview.Goal.enter begin fun gl ->
    let type_of_a = Tacmach.pf_get_type_of gl a in
    Tacticals.pf_constr_of_global (delayed_force refl_equal) >>= fun req ->
    Tacticals.tclTHENLIST
         [Generalize.generalize [(mkApp(req, [| type_of_a; a|]))];
          Proofview.Goal.enter begin fun gl ->
            let concl = Proofview.Goal.concl gl in
            let env = Proofview.Goal.env gl in
            (* FIXME: this looks really wrong. Does anybody really use
               this tactic? *)
            let ans = Tacred.pattern_occs [Locus.OnlyOccurrences [1], a] env (Evd.from_env env) concl in
            match ans with
            | NoChange -> Proofview.tclUNIT ()
            | Changed (_, c) -> change_concl c
          end;
          simplest_case a]
  end


let case_eq_intros_rewrite x =
  Proofview.Goal.enter begin fun gl ->
  let n = nb_prod (Tacmach.project gl) (Proofview.Goal.concl gl) in
  (* Pp.msgnl (Printer.pr_lconstr x); *)
  Tacticals.tclTHENLIST [
      mkCaseEq x;
    Proofview.Goal.enter begin fun gl ->
      let concl = Proofview.Goal.concl gl in
      let hyps = Tacmach.pf_ids_set_of_hyps gl in
      let n' = nb_prod (Tacmach.project gl) concl in
      let h = fresh_id_in_env hyps (Id.of_string "heq") (Proofview.Goal.env gl)  in
      Tacticals.tclTHENLIST [
                    Tacticals.tclDO (n'-n-1) intro;
                    introduction h;
                    rewrite_except h]
    end
  ]
  end

let rec find_a_destructable_match sigma t =
  let cl = induction_arg_of_quantified_hyp (NamedHyp (CAst.make @@ Id.of_string "x")) in
  let cl = [cl, (None, None), None], None in
  let dest = CAst.make @@ TacAtom (TacInductionDestruct(false, false, cl)) in
  match EConstr.kind sigma t with
    | Case (_,_,_,_,_,x,_) when closed0 sigma x ->
        if isVar sigma x then
          (* TODO check there is no rel n. *)
          raise (Found (Tacinterp.eval_tactic dest))
        else
          (* let _ = Pp.msgnl (Printer.pr_lconstr x)  in *)
          raise (Found (case_eq_intros_rewrite x))
    | _ -> EConstr.iter sigma (fun c -> find_a_destructable_match sigma c) t


let destauto0 t =
  Proofview.tclEVARMAP >>= fun sigma ->
  try find_a_destructable_match sigma t;
    Tacticals.tclZEROMSG (Pp.str "No destructable match found")
  with Found tac -> tac

let destauto =
  Proofview.Goal.enter begin fun gl -> destauto0 (Proofview.Goal.concl gl) end

let destauto_in id =
  Proofview.Goal.enter begin fun gl ->
  let ctype = Tacmach.pf_get_type_of gl (mkVar id) in
(*  Pp.msgnl (Printer.pr_lconstr (mkVar id)); *)
(*  Pp.msgnl (Printer.pr_lconstr (ctype)); *)
  destauto0 ctype
  end

(** Term introspection *)

let is_evar x =
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma x with
    | Evar _ -> Proofview.tclUNIT ()
    | _ -> Tacticals.tclFAIL (Pp.str "Not an evar")

let has_evar x =
  Proofview.tclEVARMAP >>= fun sigma ->
  if Evarutil.has_undefined_evars sigma x
  then Proofview.tclUNIT ()
  else Tacticals.tclFAIL (Pp.str "No evars")

let is_var x =
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma x with
    | Var _ ->  Proofview.tclUNIT ()
    | _ -> Tacticals.tclFAIL (Pp.str "Not a variable or hypothesis")

let is_fix x =
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma x with
    | Fix _ -> Proofview.tclUNIT ()
    | _ -> Tacticals.tclFAIL (Pp.str "not a fix definition")

let is_cofix x =
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma x with
    | CoFix _ -> Proofview.tclUNIT ()
    | _ -> Tacticals.tclFAIL (Pp.str "not a cofix definition")

let is_ind x =
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma x with
    | Ind _ -> Proofview.tclUNIT ()
    | _ -> Tacticals.tclFAIL (Pp.str "not an (co)inductive datatype")

let is_constructor x =
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma x with
    | Construct _ -> Proofview.tclUNIT ()
    | _ -> Tacticals.tclFAIL (Pp.str "not a constructor")

let is_proj x =
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma x with
    | Proj _ -> Proofview.tclUNIT ()
    | _ -> Tacticals.tclFAIL (Pp.str "not a primitive projection")

let is_const x =
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma x with
    | Const _ -> Proofview.tclUNIT ()
    | _ -> Tacticals.tclFAIL (Pp.str "not a constant")

let unshelve ist t =
  Proofview.with_shelf (Tacinterp.tactic_of_value ist t) >>= fun (gls, ()) ->
  let gls = List.map Proofview.with_empty_state gls in
  Proofview.Unsafe.tclGETGOALS >>= fun ogls ->
  Proofview.Unsafe.tclSETGOALS (gls @ ogls)

(** tactic analogous to "OPTIMIZE HEAP" *)

let tclOPTIMIZE_HEAP =
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> Gc.compact ()))

let onSomeWithHoles tac = function
  | None -> tac None
  | Some c -> Tacticals.tclDELAYEDWITHHOLES false c (fun c -> tac (Some c))

let decompose l c =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Tacmach.project gl in
    let to_ind c =
      if isInd sigma c then fst (destInd sigma c)
      else user_err Pp.(str "not an inductive type")
    in
    let l = List.map to_ind l in
    Elim.h_decompose l c
  end

let exact ist (c : Ltac_pretype.closed_glob_constr) =
  let open Tacmach in
  Proofview.Goal.enter begin fun gl ->
  let expected_type = Pretyping.OfType (pf_concl gl) in
  let sigma, c = Tacinterp.type_uconstr ~expected_type ist c (pf_env gl) (project gl) in
  Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma) (Tactics.exact_no_check c)
  end

(** ProofGeneral specific command *)

(* Execute tac, show the names of new hypothesis names created by tac
   in the "as" format and then forget everything. From the logical
   point of view [infoH tac] is therefore equivalent to idtac,
   except that it takes the time and memory of tac and prints "as"
   information. The resulting (unchanged) goals are printed *after*
   the as-expression, which forces pg to some gymnastic.
   TODO: Have something similar (better?) in the xml protocol.
   NOTE: some tactics delete hypothesis and reuse names (induction,
   destruct), this is not detected by this tactical. *)
let infoH ~pstate (tac : raw_tactic_expr) : unit =
  let (_, oldhyps) = Declare.Proof.get_current_goal_context pstate in
  let oldhyps = List.map Context.Named.Declaration.get_id @@ Environ.named_context oldhyps in
  let tac = Tacinterp.interp tac in
  let tac =
    let open Proofview.Notations in
    tac <*>
    Proofview.Unsafe.tclGETGOALS >>= fun gls ->
    Proofview.tclEVARMAP >>= fun sigma ->
    let map gl =
      let gl = Proofview_monad.drop_state gl in
      let hyps = Evd.evar_filtered_context (Evd.find_undefined sigma gl) in
      List.map Context.Named.Declaration.get_id @@ hyps
    in
    let hyps = List.map map gls in
    let newhyps = List.map (fun hypl -> List.subtract Names.Id.equal hypl oldhyps) hyps in
    let s =
      let frst = ref true in
      List.fold_left
      (fun acc lh -> acc ^ (if !frst then (frst:=false;"") else " | ")
        ^ (List.fold_left
            (fun acc d -> (Names.Id.to_string d) ^ " " ^ acc)
            "" lh))
      "" newhyps in
    let () = Feedback.msg_notice
      Pp.(str "<infoH>"
        ++  (hov 0 (str s))
        ++  (str "</infoH>")) in
    Proofview.tclUNIT ()
  in
  ignore (Declare.Proof.by tac pstate)

let declare_equivalent_keys c c' =
  let get_key c =
    let env = Global.env () in
    let evd = Evd.from_env env in
    let (evd, c) = Constrintern.interp_open_constr env evd c in
    let kind c = EConstr.kind evd c in
    Keys.constr_key env kind c
  in
  let k1 = get_key c in
  let k2 = get_key c' in
    match k1, k2 with
    | Some k1, Some k2 -> Keys.declare_equiv_keys k1 k2
    | _ -> ()
