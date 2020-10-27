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
open Constr
open Declarations

module RelDecl = Context.Rel.Declaration

let find_mutually_recursive_statements sigma thms =
    let n = List.length thms in
    let inds = List.map (fun x ->
      let typ = Declare.CInfo.get_typ x in
      let (hyps,ccl) = EConstr.decompose_prod_assum sigma typ in
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
              [ind,x,i]
          | _ ->
              []) 0 (List.rev (List.filter Context.Rel.Declaration.is_local_assum whnf_hyp_hds))) in
      let ind_ccl =
        let cclenv = EConstr.push_rel_context hyps (Global.env()) in
        let whnf_ccl,_ = Reductionops.whd_all_stack cclenv Evd.empty ccl in
        match EConstr.kind sigma whnf_ccl with
        | Ind ((kn,_ as ind),u) when
              let mind = Global.lookup_mind kn in
              Int.equal mind.mind_ntypes n && mind.mind_finite == Declarations.CoFinite ->
            [ind,x,0]
        | _ ->
            [] in
      ind_hyps,ind_ccl) thms in
    let inds_hyps,ind_ccls = List.split inds in
    let of_same_mutind ((kn,_),_,_) = function ((kn',_),_,_) -> Environ.QMutInd.equal (Global.env ()) kn kn' in
    (* Check if all conclusions are coinductive in the same type *)
    (* (degenerated cartesian product since there is at most one coind ccl) *)
    let same_indccl =
      List.cartesians_filter (fun hyp oks ->
        if List.for_all (of_same_mutind hyp) oks
        then Some (hyp::oks) else None) [] ind_ccls in
    let ordered_same_indccl =
      List.filter (List.for_all_i (fun i ((kn,j),_,_) -> Int.equal i j) 0) same_indccl in
    (* Check if some hypotheses are inductive in the same type *)
    let common_same_indhyp =
      List.cartesians_filter (fun hyp oks ->
        if List.for_all (of_same_mutind hyp) oks
        then Some (hyp::oks) else None) [] inds_hyps in
    let ordered_inds,finite,guard =
      match ordered_same_indccl, common_same_indhyp with
      | indccl::rest, _ ->
          assert (List.is_empty rest);
          (* One occ. of common coind ccls and no common inductive hyps *)
          if not (List.is_empty common_same_indhyp) then
            Flags.if_verbose Feedback.msg_info (Pp.str "Assuming mutual coinductive statements.");
          flush_all ();
          indccl, true, []
      | [], _::_ ->
          let () = match same_indccl with
          | ind :: _ ->
            if List.distinct_f Names.Ind.CanOrd.compare (List.map pi1 ind)
            then
              Flags.if_verbose Feedback.msg_info
                (Pp.strbrk
                   ("Coinductive statements do not follow the order of "^
                    "definition, assuming the proof to be by induction."));
            flush_all ()
          | _ -> ()
          in
          let possible_guards = List.map (List.map pi3) inds_hyps in
          (* assume the largest indices as possible *)
          List.last common_same_indhyp, false, possible_guards
      | _, [] ->
        CErrors.user_err Pp.(str
            ("Cannot find common (mutual) inductive premises or coinductive" ^
             " conclusions in the statements."))
    in
    (finite,guard,None), ordered_inds

type mutual_info =
  | NonMutual of EConstr.t Declare.CInfo.t
  | Mutual of
      { mutual_info : Declare.Proof.mutual_info
      ; cinfo : EConstr.t Declare.CInfo.t list
      ; possible_guards : int list
      }

let look_for_possibly_mutual_statements sigma thms : mutual_info =
  match thms with
  | [thm] ->
      (* One non recursively proved theorem *)
    NonMutual thm
  | _::_ as thms ->
    (* More than one statement and/or an explicit decreasing mark: *)
    (* we look for a common inductive hyp or a common coinductive conclusion *)
    let recguard,ordered_inds = find_mutually_recursive_statements sigma thms in
    let cinfo = List.map pi2 ordered_inds in
    Mutual { mutual_info = recguard; cinfo; possible_guards = List.map (fun (_,_,i) -> succ i) ordered_inds }
  | [] -> CErrors.anomaly (Pp.str "Empty list of theorems.")
