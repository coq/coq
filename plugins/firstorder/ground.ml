(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Formula
open Sequent
open Rules
open Instances
open Tacmach
open Tacticals

let get_flags () =
  let open TransparentState in
  let f accu coe = match coe.Coercionops.coe_value with
    | Names.GlobRef.ConstRef kn -> { accu with tr_cst = Names.Cpred.remove kn accu.tr_cst }
    | _ -> accu
  in
  let flags = List.fold_left f TransparentState.full (Coercionops.coercions ()) in
  { Formula.reds = RedFlags.red_add_transparent RedFlags.all flags }

let get_id hd = match hd.id with FormulaId id -> id

let ground_tac ~flags solver startseq =
  Proofview.Goal.enter begin fun gl ->
  let rec toptac skipped seq =
    Proofview.Goal.enter begin fun gl ->
    tclORELSE (axiom_tac seq)
      begin
        try
          let (hd, seq1) = take_formula (pf_env gl) (project gl) seq
          and re_add s=re_add_formula_list (project gl) skipped s in
          let continue=toptac []
          and backtrack =toptac (hd::skipped) seq1 in
          let AnyFormula hd = hd in
            match hd.pat with
                RightPattern rpat->
                  begin
                    match rpat with
                        Rand->
                          and_tac ~flags backtrack continue (re_add seq1)
                      | Rforall->
                          let backtrack1=
                            tclFAIL (Pp.str "reversible in 1st order mode")
                          in
                            forall_tac ~flags backtrack1 continue (re_add seq1)
                      | Rarrow->
                          arrow_tac ~flags backtrack continue (re_add seq1)
                      | Ror->
                          or_tac ~flags backtrack continue (re_add seq1)
                      | Rfalse->backtrack
                      | Rexists(i,dom,triv)->
                          let (lfp, seq2) = collect_quantified (pf_env gl) (project gl) seq in
                          let backtrack2=toptac (lfp@skipped) seq2 in
                            if Sequent.has_fuel seq then
                              quantified_tac ~flags lfp backtrack2
                                continue (re_add seq)
                            else
                              backtrack2 (* need special backtracking *)
                  end
              | LeftPattern lpat->
                  begin
                    match lpat with
                        Lfalse->
                          left_false_tac (get_id hd)
                      | Land ind->
                          left_and_tac ~flags ind backtrack
                          (get_id hd) continue (re_add seq1)
                      | Lor ind->
                          left_or_tac ~flags ind backtrack
                          (get_id hd) continue (re_add seq1)
                      | Lforall (_,_,_)->
                          let (lfp, seq2) = collect_quantified (pf_env gl) (project gl) seq in
                          let backtrack2=toptac (lfp@skipped) seq2 in
                            if Sequent.has_fuel seq then
                              quantified_tac ~flags lfp backtrack2
                                continue (re_add seq)
                            else
                              backtrack2 (* need special backtracking *)
                      | Lexists ind ->
                          left_exists_tac ~flags ind backtrack (get_id hd)
                            continue (re_add seq1)
                      | LA (typ,lap)->
                          let la_tac=
                            begin
                              match lap with
                                  LLatom -> backtrack
                                | LLand (ind,largs) | LLor(ind,largs)
                                | LLfalse (ind,largs)->
                                    (ll_ind_tac ~flags ind largs backtrack
                                       (get_id hd) continue (re_add seq1))
                                | LLforall p ->
                                    if Sequent.has_fuel seq then
                                      (ll_forall_tac ~flags p backtrack
                                         (get_id hd) continue (re_add seq1))
                                    else backtrack
                                | LLexists (ind,l) ->
                                    ll_ind_tac ~flags ind l backtrack
                                      (get_id hd) continue (re_add seq1)
                                | LLarrow (a,b,c) ->
                                    (ll_arrow_tac ~flags a b c backtrack
                                       (get_id hd) continue (re_add seq1))
                            end in
                            ll_atom_tac ~flags typ la_tac (get_id hd) continue (re_add seq1)
                  end
            with Heap.EmptyHeap->solver
      end
    end in
    let n = List.length (Proofview.Goal.hyps gl) in
    startseq (fun seq -> wrap ~flags n true (toptac []) seq)
  end
