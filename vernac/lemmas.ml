(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Hugo Herbelin from contents related to lemma proofs in
   file command.ml, Aug 2009 *)

open Util

(************************************************************************)
(* Creating a lemma-like constant                                       *)
(************************************************************************)

(* Starting a goal *)
let start_lemma ~name ~poly
    ?(udecl=UState.default_univ_decl)
    ?(info=Declare.Info.make ()) ?(impargs=[]) sigma c =
  Declare.start_proof sigma ~name ~udecl ~poly ~impargs ~info c

(* Note that proofs opened by start_dependent lemma cannot be closed
   by the regular terminators, thus we don't need to update the [thms]
   field. We will capture this invariant by typing in the future *)
let start_dependent_lemma ~name ~poly
    ?(udecl=UState.default_univ_decl)
    ?(info=Declare.Info.make ()) telescope =
  Declare.start_dependent_proof ~name ~udecl ~poly ~info telescope

let rec_tac_initializer finite guard thms snl =
  if finite then
    match List.map (fun { Declare.Recthm.name; typ } -> name, (EConstr.of_constr typ)) thms with
    | (id,_)::l -> Tactics.mutual_cofix id l 0
    | _ -> assert false
  else
    (* nl is dummy: it will be recomputed at Qed-time *)
    let nl = match snl with
     | None -> List.map succ (List.map List.last guard)
     | Some nl -> nl
    in match List.map2 (fun { Declare.Recthm.name; typ } n -> (name, n, (EConstr.of_constr typ))) thms nl with
       | (id,n,_)::l -> Tactics.mutual_fix id n l 0
       | _ -> assert false

let start_lemma_with_initialization ?hook ~poly ~scope ~kind ~udecl sigma recguard thms snl =
  let intro_tac { Declare.Recthm.args; _ } = Tactics.auto_intros_tac args in
  let init_tac, compute_guard = match recguard with
  | Some (finite,guard,init_terms) ->
    let rec_tac = rec_tac_initializer finite guard thms snl in
    let term_tac =
      match init_terms with
      | None ->
        List.map intro_tac thms
      | Some init_terms ->
        (* This is the case for hybrid proof mode / definition
           fixpoint, where terms for some constants are given with := *)
        let tacl = List.map (Option.cata (EConstr.of_constr %> Tactics.exact_no_check) Tacticals.New.tclIDTAC) init_terms in
        List.map2 (fun tac thm -> Tacticals.New.tclTHEN tac (intro_tac thm)) tacl thms
    in
    Tacticals.New.tclTHENS rec_tac term_tac, guard
  | None ->
    let () = match thms with [_] -> () | _ -> assert false in
    intro_tac (List.hd thms), [] in
  match thms with
  | [] -> CErrors.anomaly (Pp.str "No proof to start.")
  | { Declare.Recthm.name; typ; impargs; _} :: thms ->
    let info = Declare.Info.make ?hook ~scope ~kind ~compute_guard ~thms () in
    (* start_lemma has the responsibility to add (name, impargs, typ)
       to thms, once Info.t is more refined this won't be necessary *)
    let lemma = start_lemma ~name ~impargs ~poly ~udecl ~info sigma (EConstr.of_constr typ) in
    Declare.Proof.map ~f:(fun p ->
        pi1 @@ Proof.run_tactic Global.(env ()) init_tac p) lemma
