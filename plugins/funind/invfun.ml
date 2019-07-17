(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Constr
open EConstr
open Pp
open Tacticals
open Tactics
open Indfun_common
open Tacmach
open Tactypes

let thin ids gl = Proofview.V82.of_tactic (Tactics.clear ids) gl

(* (\* [id_to_constr id] finds the term associated to [id] in the global environment *\) *)
(* let id_to_constr id = *)
(*   try *)
(*     Constrintern.global_reference id *)
(*   with Not_found -> *)
(*     raise (UserError ("",str "Cannot find " ++ Ppconstr.pr_id id)) *)


let make_eq () =
  try
    EConstr.of_constr (UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref "core.eq.type"))
  with _ -> assert false

(***********************************************)

(* [revert_graph kn post_tac hid] transforme an hypothesis [hid] having type Ind(kn,num) t1 ... tn res
   when [kn] denotes a graph block  into
   f_num t1... tn = res (by applying [f_complete] to the first type) before apply post_tac on the result

   if the type of hypothesis has not this form or if we cannot find the completeness lemma then we do nothing
*)
let revert_graph kn post_tac hid g =
    let sigma = project g in
    let typ = pf_unsafe_type_of g (mkVar hid) in
    match EConstr.kind sigma typ with
      | App(i,args) when isInd sigma i ->
          let ((kn',num) as ind'),u = destInd sigma i in
          if MutInd.equal kn kn'
          then (* We have generated a graph hypothesis so that we must change it if we can *)
            let info =
              try find_Function_of_graph ind'
              with Not_found -> (* The graphs are mutually recursive but we cannot find one of them !*)
                anomaly (Pp.str "Cannot retrieve infos about a mutual block.")
            in
            (* if we can find a completeness lemma for this function
               then we can come back to the functional form. If not, we do nothing
            *)
            match info.completeness_lemma with
              | None -> tclIDTAC g
              | Some f_complete ->
                  let f_args,res = Array.chop (Array.length args - 1) args in
                  tclTHENLIST
                    [
                      Proofview.V82.of_tactic (generalize [applist(mkConst f_complete,(Array.to_list f_args)@[res.(0);mkVar hid])]);
                      thin [hid];
                      Proofview.V82.of_tactic (Simple.intro hid);
                      post_tac hid
                    ]
                    g

          else tclIDTAC g
      | _ -> tclIDTAC g


(*
   [functional_inversion hid fconst f_correct ] is the functional version of [inversion]

   [hid] is the hypothesis to invert, [fconst] is the function to invert and  [f_correct]
   is the correctness lemma for [fconst].

   The sketch is the following~:
   \begin{enumerate}
   \item Transforms the hypothesis [hid] such that its type is now $res\ =\ f\ t_1 \ldots t_n$
   (fails if it is not possible)
   \item replace [hid] with $R\_f t_1 \ldots t_n res$ using [f_correct]
   \item apply [inversion] on [hid]
   \item finally in each branch, replace each  hypothesis [R\_f ..]  by [f ...] using [f_complete] (whenever
   such a lemma exists)
   \end{enumerate}
*)

let functional_inversion kn hid fconst f_correct : Tacmach.tactic =
  fun g ->
    let old_ids = List.fold_right Id.Set.add  (pf_ids_of_hyps g) Id.Set.empty in
    let sigma = project g in
    let type_of_h = pf_unsafe_type_of g (mkVar hid) in
    match EConstr.kind sigma type_of_h with
      | App(eq,args) when EConstr.eq_constr sigma eq (make_eq ())  ->
          let pre_tac,f_args,res =
            match EConstr.kind sigma args.(1),EConstr.kind sigma args.(2) with
              | App(f,f_args),_ when EConstr.eq_constr sigma f fconst ->
                  ((fun hid -> Proofview.V82.of_tactic (intros_symmetry (Locusops.onHyp hid))),f_args,args.(2))
              |_,App(f,f_args) when EConstr.eq_constr sigma f fconst ->
                 ((fun hid -> tclIDTAC),f_args,args.(1))
              | _ -> (fun hid -> tclFAIL 1 (mt ())),[||],args.(2)
          in
          tclTHENLIST [
            pre_tac hid;
            Proofview.V82.of_tactic (generalize [applist(f_correct,(Array.to_list f_args)@[res;mkVar hid])]);
            thin [hid];
            Proofview.V82.of_tactic (Simple.intro hid);
            Proofview.V82.of_tactic (Inv.inv Inv.FullInversion None (NamedHyp hid));
            (fun g ->
               let new_ids = List.filter (fun id -> not (Id.Set.mem id old_ids)) (pf_ids_of_hyps g) in
               tclMAP (revert_graph kn pre_tac)  (hid::new_ids)  g
            );
          ] g
      | _ -> tclFAIL 1 (mt ()) g


let error msg = user_err Pp.(str msg)

let invfun qhyp f  =
  let f =
    match f with
      | GlobRef.ConstRef f -> f
      | _ -> raise (CErrors.UserError(None,str "Not a function"))
  in
  try
    let finfos = find_Function_infos f in
    let f_correct = mkConst(Option.get finfos.correctness_lemma)
    and kn = fst finfos.graph_ind
    in
    Proofview.V82.of_tactic (
      Tactics.try_intros_until (fun hid -> Proofview.V82.tactic (functional_inversion kn hid (mkConst f)  f_correct)) qhyp
    )
  with
    | Not_found ->  error "No graph found"
    | Option.IsNone  -> error "Cannot use equivalence with graph!"

exception NoFunction

let invfun qhyp f g =
  match f with
    | Some f -> invfun qhyp f g
    | None ->
       Proofview.V82.of_tactic begin
        Tactics.try_intros_until
          (fun hid -> Proofview.V82.tactic begin fun g ->
            let sigma = project g in
             let hyp_typ = pf_unsafe_type_of g (mkVar hid)  in
             match EConstr.kind sigma hyp_typ with
               | App(eq,args) when EConstr.eq_constr sigma eq (make_eq ()) ->
                   begin
                     let f1,_ = decompose_app sigma args.(1) in
                     try
                       if not (isConst sigma f1) then raise NoFunction;
                       let finfos = find_Function_infos (fst (destConst sigma f1)) in
                       let f_correct = mkConst(Option.get finfos.correctness_lemma)
                       and kn = fst finfos.graph_ind
                       in
                       functional_inversion kn hid f1 f_correct g
                     with | NoFunction | Option.IsNone | Not_found ->
                       try
                         let f2,_ = decompose_app sigma args.(2) in
                         if not (isConst sigma f2) then raise NoFunction;
                         let finfos = find_Function_infos (fst (destConst sigma f2)) in
                         let f_correct = mkConst(Option.get finfos.correctness_lemma)
                         and kn = fst finfos.graph_ind
                         in
                         functional_inversion kn hid  f2 f_correct g
                       with
                         | NoFunction ->
                             user_err  (str "Hypothesis " ++ Ppconstr.pr_id hid ++ str " must contain at least one Function")
                         | Option.IsNone  ->
                             if do_observe ()
                             then
                               error "Cannot use equivalence with graph for any side of the equality"
                             else user_err  (str "Cannot find inversion information for hypothesis " ++ Ppconstr.pr_id hid)
                         | Not_found ->
                             if do_observe ()
                             then
                               error "No graph found for any side of equality"
                             else user_err  (str "Cannot find inversion information for hypothesis " ++ Ppconstr.pr_id hid)
                   end
               | _ -> user_err  (Ppconstr.pr_id hid ++ str " must be an equality ")
          end)
          qhyp
          end
          g
