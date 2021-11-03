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
open Tacexpr

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
      let hyps = Evd.evar_filtered_context (Evd.find sigma gl) in
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
