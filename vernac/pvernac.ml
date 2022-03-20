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
    (* The different kinds of vernacular commands *)
    let gallina = Entry.create "gallina"
    let gallina_ext = Entry.create "gallina_ext"
    let command = Entry.create "command"
    let syntax = Entry.create "syntax_command"
    let vernac_control = Entry.create "Vernac.vernac_control"
    let inductive_or_record_definition = Entry.create "Vernac.inductive_or_record_definition"
    let fix_definition = Entry.create "Vernac.fix_definition"
    let red_expr = Entry.create "red_expr"
    let hint_info = Entry.create "hint_info"
    (* Main vernac entry *)
    let main_entry = Entry.create "vernac"
    let noedit_mode = Entry.create "noedit_command"

    let () =
      let act_vernac v loc = Some v in
      let act_eoi _ loc = None in
      let rule = [
        Pcoq.(Production.make (Rule.next Rule.stop (Symbol.token Tok.PEOI)) act_eoi);
        Pcoq.(Production.make (Rule.next Rule.stop (Symbol.nterm vernac_control)) act_vernac);
      ] in
      Pcoq.(grammar_extend main_entry (Fresh (Gramlib.Gramext.First, [None, None, rule])))

    let select_tactic_entry spec =
      match spec with
      | None -> noedit_mode
      | Some ename -> find_proof_mode ename

    let command_entry =
      Pcoq.Entry.(of_parser "command_entry"
        { parser_fun = (fun strm -> Pcoq.Entry.parse_token_stream (select_tactic_entry !command_entry_ref) strm) })

  end

module Unsafe = struct
  let set_tactic_entry oname = command_entry_ref := oname
end

let main_entry proof_mode =
  Unsafe.set_tactic_entry proof_mode;
  Vernac_.main_entry

let () =
  register_grammar Genredexpr.wit_red_expr (Vernac_.red_expr);
