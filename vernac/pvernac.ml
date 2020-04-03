(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pcoq

let uvernac = create_universe "vernac"

type proof_mode = string

(* Tactic parsing modes *)
let register_proof_mode, find_proof_mode, lookup_proof_mode =
  let proof_mode : (string, Vernacexpr.vernac_expr Entry.t) Hashtbl.t =
    Hashtbl.create 19 in
  let register_proof_mode ename e = Hashtbl.add proof_mode ename e; ename in
  let find_proof_mode ename =
    try Hashtbl.find proof_mode ename
    with Not_found ->
      CErrors.anomaly Pp.(str "proof mode not found: " ++ str ename) in
  let lookup_proof_mode name =
    if Hashtbl.mem proof_mode name then Some name
    else None
  in
  register_proof_mode, find_proof_mode, lookup_proof_mode

let proof_mode_to_string name = name

let command_entry_ref = ref None

module Vernac_ =
  struct
    let gec_vernac s = Entry.create ("vernac:" ^ s)

    (* The different kinds of vernacular commands *)
    let gallina = gec_vernac "gallina"
    let gallina_ext = gec_vernac "gallina_ext"
    let command = gec_vernac "command"
    let syntax = gec_vernac "syntax_command"
    let vernac_control = gec_vernac "Vernac.vernac_control"
    let rec_definition = gec_vernac "Vernac.rec_definition"
    let hint_info = gec_vernac "hint_info"
    (* Reduction expressions *)
    let pattern_occ = new_entry utactic "pattern_occ"
    let occs = new_entry utactic "occs"
    let occs_nums = new_entry utactic "occs_nums"
    let red_expr = new_entry utactic "red_expr"
    (* Main vernac entry *)
    let main_entry = Entry.create "vernac"
    let noedit_mode = gec_vernac "noedit_command"

    let () =
      let act_vernac v loc = Some v in
      let act_eoi _ loc = None in
      let rule = [
        Pcoq.(Production.make (Rule.next Rule.stop (Symbol.token Tok.PEOI)) act_eoi);
        Pcoq.(Production.make (Rule.next Rule.stop (Symbol.nterm vernac_control)) act_vernac);
      ] in
      Pcoq.(grammar_extend main_entry {pos=None; data=[None, None, rule]})

    let select_tactic_entry spec =
      match spec with
      | None -> noedit_mode
      | Some ename -> find_proof_mode ename

    let command_entry =
      Pcoq.Entry.of_parser "command_entry"
        (fun _ strm -> Pcoq.Entry.parse_token_stream (select_tactic_entry !command_entry_ref) strm)

  end

module Unsafe = struct
  let set_tactic_entry oname = command_entry_ref := oname
end

let main_entry proof_mode =
  Unsafe.set_tactic_entry proof_mode;
  Vernac_.main_entry

let () =
  register_grammar Genredexpr.wit_red_expr (Vernac_.red_expr);
