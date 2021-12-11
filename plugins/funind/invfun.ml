(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Constr
open EConstr
open Tacmach
open Tactics
open Tacticals
open Indfun_common

(***********************************************)

(* [revert_graph kn post_tac hid] transforme an hypothesis [hid] having type Ind(kn,num) t1 ... tn res
   when [kn] denotes a graph block  into
   f_num t1... tn = res (by applying [f_complete] to the first type) before apply post_tac on the result

   if the type of hypothesis has not this form or if we cannot find the completeness lemma then we do nothing
*)
let revert_graph kn post_tac hid =
  Proofview.Goal.enter (fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = project gl in
      let typ = pf_get_hyp_typ hid gl in
      match EConstr.kind sigma typ with
      | App (i, args) when isInd sigma i ->
        let ((kn', num) as ind'), u = destInd sigma i in
        if Environ.QMutInd.equal env kn kn' then
          (* We have generated a graph hypothesis so that we must change it if we can *)
          let info =
            match find_Function_of_graph ind' with
            | Some info -> info
            | None ->
              (* The graphs are mutually recursive but we cannot find one of them !*)
              CErrors.anomaly
                (Pp.str "Cannot retrieve infos about a mutual block.")
          in
          (* if we can find a completeness lemma for this function
             then we can come back to the functional form. If not, we do nothing
          *)
          match info.completeness_lemma with
          | None -> tclIDTAC
          | Some f_complete ->
            let f_args, res = Array.chop (Array.length args - 1) args in
            tclTHENLIST
              [ generalize
                  [ applist
                      ( mkConst f_complete
                      , Array.to_list f_args @ [res.(0); mkVar hid] ) ]
              ; clear [hid]
              ; Simple.intro hid
              ; post_tac hid ]
        else tclIDTAC
      | _ -> tclIDTAC)

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

let functional_inversion kn hid fconst f_correct =
  Proofview.Goal.enter (fun gl ->
      let old_ids =
        List.fold_right Id.Set.add (pf_ids_of_hyps gl) Id.Set.empty
      in
      let sigma = project gl in
      let type_of_h = pf_get_hyp_typ hid gl in
      match EConstr.kind sigma type_of_h with
      | App (eq, args) when EConstr.eq_constr sigma eq (make_eq ()) ->
        let pre_tac, f_args, res =
          match (EConstr.kind sigma args.(1), EConstr.kind sigma args.(2)) with
          | App (f, f_args), _ when EConstr.eq_constr sigma f fconst ->
            ((fun hid -> intros_symmetry (Locusops.onHyp hid)), f_args, args.(2))
          | _, App (f, f_args) when EConstr.eq_constr sigma f fconst ->
            ((fun hid -> tclIDTAC), f_args, args.(1))
          | _ -> ((fun hid -> tclFAILn 1 Pp.(mt ())), [||], args.(2))
        in
        tclTHENLIST
          [ pre_tac hid
          ; generalize
              [applist (f_correct, Array.to_list f_args @ [res; mkVar hid])]
          ; clear [hid]
          ; Simple.intro hid
          ; Inv.inv Inv.FullInversion None (Tactypes.NamedHyp (CAst.make hid))
          ; Proofview.Goal.enter (fun gl ->
                let new_ids =
                  List.filter
                    (fun id -> not (Id.Set.mem id old_ids))
                    (pf_ids_of_hyps gl)
                in
                tclMAP (revert_graph kn pre_tac) (hid :: new_ids)) ]
      | _ -> tclFAILn 1 Pp.(mt ()))

let invfun qhyp f =
  let f =
    match f with
    | GlobRef.ConstRef f -> f
    | _ -> CErrors.user_err Pp.(str "Not a function")
  in
  match find_Function_infos f with
  | None -> CErrors.user_err (Pp.str "No graph found")
  | Some finfos -> (
    match finfos.correctness_lemma with
    | None -> CErrors.user_err (Pp.str "Cannot use equivalence with graph!")
    | Some f_correct ->
      let f_correct = mkConst f_correct and kn = fst finfos.graph_ind in
      Tactics.try_intros_until
        (fun hid -> functional_inversion kn hid (mkConst f) f_correct)
        qhyp )

let invfun qhyp f =
  let exception NoFunction in
  match f with
  | Some f -> invfun qhyp f
  | None ->
    let tac_action hid gl =
      let sigma = project gl in
      let hyp_typ = pf_get_hyp_typ hid gl in
      match EConstr.kind sigma hyp_typ with
      | App (eq, args) when EConstr.eq_constr sigma eq (make_eq ()) -> (
        let f1, _ = decompose_app sigma args.(1) in
        try
          if not (isConst sigma f1) then raise NoFunction;
          let finfos =
            Option.get (find_Function_infos (fst (destConst sigma f1)))
          in
          let f_correct = mkConst (Option.get finfos.correctness_lemma)
          and kn = fst finfos.graph_ind in
          functional_inversion kn hid f1 f_correct
        with NoFunction | Option.IsNone ->
          let f2, _ = decompose_app sigma args.(2) in
          if isConst sigma f2 then
            match find_Function_infos (fst (destConst sigma f2)) with
            | None ->
              if do_observe () then
                CErrors.user_err
                  (Pp.str "No graph found for any side of equality")
              else
                CErrors.user_err
                  Pp.(
                    str "Cannot find inversion information for hypothesis "
                    ++ Ppconstr.pr_id hid)
            | Some finfos -> (
              match finfos.correctness_lemma with
              | None ->
                if do_observe () then
                  CErrors.user_err
                    (Pp.str
                       "Cannot use equivalence with graph for any side of the \
                        equality")
                else
                  CErrors.user_err
                    Pp.(
                      str "Cannot find inversion information for hypothesis "
                      ++ Ppconstr.pr_id hid)
              | Some f_correct ->
                let f_correct = mkConst f_correct
                and kn = fst finfos.graph_ind in
                functional_inversion kn hid f2 f_correct )
          else
            (* NoFunction *)
            CErrors.user_err
              Pp.(
                str "Hypothesis " ++ Ppconstr.pr_id hid
                ++ str " must contain at least one Function") )
      | _ ->
        CErrors.user_err Pp.(Ppconstr.pr_id hid ++ str " must be an equality ")
    in
    try_intros_until (tac_action %> Proofview.Goal.enter) qhyp
