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

module NamedDecl = Context.Named.Declaration

(* Support for terminators and proofs with an associated constant
   [that can be saved] *)

type lemma_possible_guards = int list list

module Proof_ending = Declare.Proof_ending
module Info = Declare.Info

(* Proofs with a save constant function *)
type t =
  { proof : Declare.Proof.t
  ; info : Info.t
  }

let pf_map f pf = { pf with proof = f pf.proof }
let pf_fold f pf = f pf.proof

let set_endline_tactic t = pf_map (Declare.Proof.set_endline_tactic t)

(* To be removed *)
module Internal = struct

  (** Gets the current terminator without checking that the proof has
      been completed. Useful for the likes of [Admitted]. *)
  let get_info ps = ps.info

end

let by tac pf =
  let proof, res = Declare.by tac pf.proof in
  { pf with proof }, res

(************************************************************************)
(* Creating a lemma-like constant                                       *)
(************************************************************************)

let initialize_named_context_for_proof () =
  let sign = Global.named_context () in
  List.fold_right
    (fun d signv ->
      let id = NamedDecl.get_id d in
      let d = if Decls.variable_opacity id then NamedDecl.drop_body d else d in
      Environ.push_named_context_val d signv) sign Environ.empty_named_context_val

(* Starting a goal *)
let start_lemma ~name ~poly
    ?(udecl=UState.default_univ_decl)
    ?(info=Info.make ()) ?(impargs=[]) sigma c =
  (* We remove the bodies of variables in the named context marked
     "opaque", this is a hack tho, see #10446 *)
  let sign = initialize_named_context_for_proof () in
  let goals = [ Global.env_of_context sign , c ] in
  let proof = Declare.start_proof sigma ~name ~udecl ~poly goals in
  let info = Declare.Info.add_first_thm ~info ~name ~typ:c ~impargs in
  { proof; info }

(* Note that proofs opened by start_dependent lemma cannot be closed
   by the regular terminators, thus we don't need to update the [thms]
   field. We will capture this invariant by typing in the future *)
let start_dependent_lemma ~name ~poly
    ?(udecl=UState.default_univ_decl)
    ?(info=Info.make ()) telescope =
  let proof = Declare.start_dependent_proof ~name ~udecl ~poly telescope in
  { proof; info }

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
    let info = Info.make ?hook ~scope ~kind ~compute_guard ~thms () in
    (* start_lemma has the responsibility to add (name, impargs, typ)
       to thms, once Info.t is more refined this won't be necessary *)
    let lemma = start_lemma ~name ~impargs ~poly ~udecl ~info sigma (EConstr.of_constr typ) in
    pf_map (Declare.Proof.map_proof (fun p ->
        pi1 @@ Proof.run_tactic Global.(env ()) init_tac p)) lemma

let save_lemma_admitted ~lemma =
  Declare.save_lemma_admitted ~proof:lemma.proof ~info:lemma.info

let save_lemma_proved ~lemma ~opaque ~idopt =
  Declare.save_lemma_proved ~proof:lemma.proof ~info:lemma.info ~opaque ~idopt
