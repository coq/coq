(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Procq

type proof_mode = string

(* Tactic parsing modes *)
let register_proof_mode, find_proof_mode, lookup_proof_mode, list_proof_modes =
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
  let list_proof_modes () =
    Hashtbl.fold CString.Map.add proof_mode CString.Map.empty
  in
  register_proof_mode, find_proof_mode, lookup_proof_mode, list_proof_modes

let proof_mode_to_string name = name

let command_entry_ref = ref None

module Vernac_ =
  struct
    (* The different kinds of vernacular commands *)
    let gallina = Entry.make "gallina"
    let gallina_ext = Entry.make "gallina_ext"
    let command = Entry.make "command"
    let syntax = Entry.make "syntax_command"
    let vernac_control = Entry.make "vernac_control"
    let inductive_or_record_definition = Entry.make "inductive_or_record_definition"
    let fix_definition = Entry.make "fix_definition"
    let red_expr = Entry.make "red_expr"
    let hint_info = Entry.make "hint_info"
    (* Main vernac entry *)
    let main_entry = Entry.make "vernac"
    let noedit_mode = Entry.make "noedit_command"

    let () =
      let act_vernac v loc = Some v in
      let act_eoi _ loc = None in
      let rule = [
        Procq.(Production.make (Rule.next Rule.stop (Symbol.token Tok.PEOI)) act_eoi);
        Procq.(Production.make (Rule.next Rule.stop (Symbol.nterm vernac_control)) act_vernac);
      ] in
      Procq.(grammar_extend main_entry (Fresh (Gramlib.Gramext.First, [None, None, rule])))

    let select_tactic_entry spec =
      match spec with
      | None -> noedit_mode
      | Some ename -> find_proof_mode ename

    let command_entry =
      Procq.Entry.(of_parser "command_entry"
        { parser_fun = (fun _kwstate strm -> Procq.Entry.parse_token_stream (select_tactic_entry !command_entry_ref) strm) })

  end

module Unsafe = struct
  let set_tactic_entry oname = command_entry_ref := oname
end

let main_entry proof_mode =
  Unsafe.set_tactic_entry proof_mode;
  Vernac_.main_entry

let () =
  register_grammar Redexpr.wit_red_expr (Vernac_.red_expr);
