(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open CErrors
open Names
open Constr
open EConstr
open Tacticals
open Tactics
open Induction
open Indfun_common
module RelDecl = Context.Rel.Declaration

let is_rec_info sigma scheme_info =
  let test_branche min acc decl =
    acc
    ||
    let new_branche =
      it_mkProd_or_LetIn dummy
        (fst (decompose_prod_decls sigma (RelDecl.get_type decl)))
    in
    let free_rels_in_br = Termops.free_rels sigma new_branche in
    let max = min + scheme_info.npredicates in
    Int.Set.exists (fun i -> i >= min && i < max) free_rels_in_br
  in
  List.fold_left_i test_branche 1 false (List.rev scheme_info.branches)

let choose_dest_or_ind scheme_info args =
  Proofview.tclBIND Proofview.tclEVARMAP (fun sigma ->
      Induction.induction_destruct (is_rec_info sigma scheme_info) false args)

let functional_induction with_clean c princl pat =
  let open Proofview.Notations in
  Proofview.Goal.enter_one (fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let concl = Proofview.Goal.concl gl in
      let f, args = decompose_app_list sigma c in
      match princl with
      | None -> (
        (* No principle is given let's find the good one *)
        match EConstr.kind sigma f with
        | Const (c', u) ->
          let princ_option =
            let finfo =
              (* we first try to find out a graph on f *)
              match find_Function_infos c' with
              | Some finfo -> finfo
              | None ->
                user_err
                  ( str "Cannot find induction information on "
                  ++ Termops.pr_global_env env (ConstRef c') )
            in
            match Retyping.get_sort_quality_or_set_of env sigma concl with
            | Qual (QConstant QSProp) -> finfo.sprop_lemma
            | Qual (QConstant QProp) -> finfo.prop_lemma
            | Set -> finfo.rec_lemma
            | Qual (QConstant QType | QVar _) -> finfo.rect_lemma
            | Qual (QGlobal _) -> CErrors.user_err Pp.(str "Cannot handle global sort.")
          in
          let sigma, princ =
            (* then we get the principle *)
            match princ_option with
            | Some princ ->
              Evd.fresh_global env sigma (GlobRef.ConstRef princ)
            | None ->
              (*i If there is not default lemma defined then,
                      we cross our finger and try to find a lemma named f_ind
                      (or f_rec, f_rect) i*)
              let princ_name =
                Elimschemes.make_elimination_ident
                  (Constant.label c')
                  (Retyping.get_sort_quality_or_set_of env sigma concl)
              in
              let princ_ref =
                match
                  Constrintern.locate_reference
                    (Libnames.qualid_of_ident princ_name)
                with
                | Some r -> r
                | None ->
                  user_err
                    ( str "Cannot find induction principle for "
                    ++ Termops.pr_global_env env (ConstRef c') )
              in
              Evd.fresh_global env sigma princ_ref
          in
          let princt = Retyping.get_type_of env sigma princ in
          Proofview.Unsafe.tclEVARS sigma
          <*> Proofview.tclUNIT (princ, Tactypes.NoBindings, princt, args)
        | _ ->
          CErrors.user_err
            (str "functional induction must be used with a function") )
      | Some (princ, binding) ->
        let sigma, princt = Typing.type_of env sigma princ in
        Proofview.Unsafe.tclEVARS sigma
        <*> Proofview.tclUNIT (princ, binding, princt, args))
  >>= fun (princ, bindings, princ_type, args) ->
  Proofview.Goal.enter (fun gl ->
      let sigma = Proofview.Goal.sigma gl in
      let princ_infos = compute_elim_sig sigma princ_type in
      let args_as_induction_constr =
        let c_list = if princ_infos.farg_in_concl then [c] else [] in
        if List.length args + List.length c_list = 0 then
          user_err Pp.(str "Cannot recognize a valid functional scheme");
        let encoded_pat_as_patlist =
          List.make (List.length args + List.length c_list - 1) None @ [pat]
        in
        List.map2
          (fun c pat ->
            ( ( None
              , ElimOnConstr
                  (fun env sigma -> (sigma, (c, Tactypes.NoBindings))) )
            , (None, pat)
            , None ))
          (args @ c_list) encoded_pat_as_patlist
      in
      let princ' = Some (princ, bindings) in
      let princ_vars =
        List.fold_right
          (fun a acc ->
            try Id.Set.add (destVar sigma a) acc with DestKO -> acc)
          args Id.Set.empty
      in
      let old_idl =
        List.fold_right Id.Set.add (Tacmach.pf_ids_of_hyps gl) Id.Set.empty
      in
      let old_idl = Id.Set.diff old_idl princ_vars in
      let subst_and_reduce gl =
        if with_clean then
          let idl =
            List.filter
              (fun id -> not (Id.Set.mem id old_idl))
              (Tacmach.pf_ids_of_hyps gl)
          in
          let flag =
            Genredexpr.Cbv {Redops.all_flags with Genredexpr.rDelta = false}
          in
          tclTHEN
            (tclMAP
               (fun id ->
                 tclTRY (Equality.subst_gen (do_rewrite_dependent ()) [id]))
               idl)
            (reduce flag Locusops.allHypsAndConcl)
        else tclIDTAC
      in
      tclTHEN
        (choose_dest_or_ind princ_infos (args_as_induction_constr, princ'))
        (Proofview.Goal.enter subst_and_reduce))
