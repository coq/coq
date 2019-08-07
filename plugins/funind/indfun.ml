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
open Sorts
open Util
open Names
open Constr
open EConstr
open Pp
open Indfun_common
open Tactypes

module RelDecl = Context.Rel.Declaration

let is_rec_info sigma scheme_info =
  let test_branche min acc decl =
    acc || (
      let new_branche =
        it_mkProd_or_LetIn mkProp (fst (decompose_prod_assum sigma (RelDecl.get_type decl))) in
      let free_rels_in_br = Termops.free_rels sigma new_branche in
      let max = min + scheme_info.Tactics.npredicates in
      Int.Set.exists (fun i -> i >= min && i< max) free_rels_in_br
    )
  in
  List.fold_left_i test_branche 1 false (List.rev scheme_info.Tactics.branches)

let choose_dest_or_ind scheme_info args =
  Proofview.tclBIND Proofview.tclEVARMAP (fun sigma ->
  Tactics.induction_destruct (is_rec_info sigma scheme_info) false args)

let functional_induction with_clean c princl pat =
  let res =
    fun g ->
    let sigma = Tacmach.project g in
    let f,args = decompose_app sigma c in
    let princ,bindings, princ_type,g' =
      match princl with
      | None -> (* No principle is given let's find the good one *)
         begin
           match EConstr.kind sigma f with
           | Const (c',u) ->
              let princ_option =
                let finfo = (* we first try to find out a graph on f *)
                  try find_Function_infos c'
                  with Not_found ->
                    user_err  (str "Cannot find induction information on "++
                                       Printer.pr_leconstr_env (Tacmach.pf_env g) sigma (mkConst c') )
                in
                match Tacticals.elimination_sort_of_goal g with
                | InSProp -> finfo.sprop_lemma
                | InProp -> finfo.prop_lemma
                | InSet -> finfo.rec_lemma
                | InType -> finfo.rect_lemma
              in
              let princ,g' =  (* then we get the principle *)
                try
                  let g',princ =
                    Tacmach.pf_eapply (Evd.fresh_global) g  (GlobRef.ConstRef (Option.get princ_option )) in
                  princ,g'
                with Option.IsNone ->
                  (*i If there is not default lemma defined then,
                          we cross our finger and try to find a lemma named f_ind
                          (or f_rec, f_rect) i*)
                  let princ_name =
                    Indrec.make_elimination_ident
                      (Label.to_id (Constant.label c'))
                      (Tacticals.elimination_sort_of_goal g)
                  in
                  try
                    let princ_ref = const_of_id princ_name in
                    let (a,b) = Tacmach.pf_eapply (Evd.fresh_global) g princ_ref in
                    (b,a)
                    (* mkConst(const_of_id princ_name ),g (\* FIXME *\) *)
                  with Not_found -> (* This one is neither defined ! *)
                    user_err  (str "Cannot find induction principle for "
                                     ++ Printer.pr_leconstr_env (Tacmach.pf_env g) sigma (mkConst c') )
              in
              (princ,NoBindings,Tacmach.pf_unsafe_type_of g' princ,g')
           | _ -> raise (UserError(None,str "functional induction must be used with a function" ))
         end
      | Some ((princ,binding)) ->
         princ,binding,Tacmach.pf_unsafe_type_of g princ,g
    in
    let sigma = Tacmach.project g' in
    let princ_infos = Tactics.compute_elim_sig (Tacmach.project g') princ_type in
    let args_as_induction_constr =
      let c_list =
        if princ_infos.Tactics.farg_in_concl
        then [c] else []
      in
      if List.length args + List.length c_list = 0
      then user_err Pp.(str "Cannot recognize a valid functional scheme" );
      let encoded_pat_as_patlist =
        List.make (List.length args + List.length c_list - 1) None @ [pat]
      in
      List.map2
        (fun c pat ->
          ((None,
            Tactics.ElimOnConstr (fun env sigma -> (sigma,(c,NoBindings)))),
           (None,pat),
           None))
        (args@c_list)
        encoded_pat_as_patlist
    in
    let princ' = Some (princ,bindings) in
    let princ_vars =
      List.fold_right
        (fun a acc -> try Id.Set.add (destVar sigma a) acc with DestKO -> acc)
        args
        Id.Set.empty
    in
    let old_idl = List.fold_right Id.Set.add (Tacmach.pf_ids_of_hyps g) Id.Set.empty in
    let old_idl = Id.Set.diff old_idl princ_vars in
    let subst_and_reduce g =
      if with_clean
      then
        let idl =
          List.filter (fun id -> not (Id.Set.mem id old_idl))
            (Tacmach.pf_ids_of_hyps g)
        in
        let flag =
          Genredexpr.Cbv
            {Redops.all_flags
             with Genredexpr.rDelta = false;
            }
        in
        Tacticals.tclTHEN
          (Tacticals.tclMAP (fun id -> Tacticals.tclTRY (Proofview.V82.of_tactic (Equality.subst_gen (do_rewrite_dependent ()) [id]))) idl )
          (Proofview.V82.of_tactic (Tactics.reduce flag Locusops.allHypsAndConcl))
          g
      else Tacticals.tclIDTAC g
    in
    Tacticals.tclTHEN
      (Proofview.V82.of_tactic (choose_dest_or_ind
         princ_infos
         (args_as_induction_constr,princ')))
      subst_and_reduce
      g'
  in res
