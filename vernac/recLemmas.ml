(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Constr
open Declarations

module RelDecl = Context.Rel.Declaration

let find_mutually_recursive_statements sigma ctxs ccls =
    let inds = List.map2 (fun ctx ccl ->
      let (hyps,ccl) = EConstr.decompose_prod_decls sigma ccl in
      let hyps = hyps @ ctx in
      let whnf_hyp_hds = EConstr.map_rel_context_in_env
        (fun env c -> fst (Reductionops.whd_all_stack env sigma c))
        (Global.env()) hyps in
      let ind_hyps =
        List.flatten (List.map_i (fun i decl ->
          let t = RelDecl.get_type decl in
          match EConstr.kind sigma t with
          | Ind ((kn,_ as ind),u) when
                let mind = Global.lookup_mind kn in
                mind.mind_finite <> Declarations.CoFinite ->
              [ind,i]
          | _ ->
              []) 0 (List.rev (List.filter Context.Rel.Declaration.is_local_assum whnf_hyp_hds))) in
      let ind_ccl =
        let cclenv = EConstr.push_rel_context hyps (Global.env()) in
        let whnf_ccl,_ = Reductionops.whd_all_stack cclenv sigma ccl in
        match EConstr.kind sigma whnf_ccl with
        | Ind ((kn,_ as ind),u) when (Global.lookup_mind kn).mind_finite == Declarations.CoFinite ->
            [ind,0]
        | _ ->
            [] in
      ind_hyps,ind_ccl) ctxs ccls in
    let inds_hyps,ind_ccls = List.split inds in
    let of_same_mutind ((kn,_),_) = function ((kn',_),_) -> Environ.QMutInd.equal (Global.env ()) kn kn' in
    (* Check if all conclusions are coinductive in the same type *)
    (* (degenerated cartesian product since there is at most one coind ccl) *)
    let same_indccl =
      List.cartesians_filter (fun hyp oks ->
        if List.for_all (of_same_mutind hyp) oks
        then Some (hyp::oks) else None) [] ind_ccls in
    let common_same_indhyp =
      List.cartesians_filter (fun hyp oks ->
        if List.for_all (of_same_mutind hyp) oks
        then Some (hyp::oks) else None) [] inds_hyps in
    let possibly_cofix = not (List.is_empty same_indccl) in (* all conclusions are coinductive *)
    let possible_fix_indices =
      match common_same_indhyp with
      | [] -> []
      | _::_ ->
        (* assume the largest indices as possible *)
        List.map (List.map snd) inds_hyps in
    if not possibly_cofix && List.is_empty possible_fix_indices then
      CErrors.user_err Pp.(str
         ("Cannot find common (mutual) inductive premises or coinductive" ^
          " conclusions in the statements."));
    Pretyping.{possibly_cofix; possible_fix_indices}
