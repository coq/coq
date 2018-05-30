(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pcoq

let uncurry f (x,y) = f x y

let uvernac = create_universe "vernac"

module Vernac_ =
  struct
    let gec_vernac s = Gram.entry_create ("vernac:" ^ s)

    (* The different kinds of vernacular commands *)
    let gallina = gec_vernac "gallina"
    let gallina_ext = gec_vernac "gallina_ext"
    let command = gec_vernac "command"
    let syntax = gec_vernac "syntax_command"
    let vernac_control = gec_vernac "Vernac.vernac_control"
    let rec_definition = gec_vernac "Vernac.rec_definition"
    let red_expr = new_entry utactic "red_expr"
    let hint_info = gec_vernac "hint_info"
    (* Main vernac entry *)
    let main_entry = Gram.entry_create "vernac"
    let noedit_mode = gec_vernac "noedit_command"

    let () =
      let act_vernac = Gram.action (fun v loc -> Some (to_coqloc loc, v)) in
      let act_eoi = Gram.action (fun _ loc -> None) in
      let rule = [
        ([ Symbols.stoken Tok.EOI ], act_eoi);
        ([ Symbols.snterm (Gram.Entry.obj vernac_control) ], act_vernac );
      ] in
      uncurry (Gram.extend main_entry) (None, [None, None, rule])

    let command_entry_ref = ref noedit_mode
    let command_entry =
      Gram.Entry.of_parser "command_entry"
        (fun strm -> Gram.parse_tokens_after_filter !command_entry_ref strm)

  end

let main_entry = Vernac_.main_entry

let set_command_entry e = Vernac_.command_entry_ref := e
let get_command_entry () = !Vernac_.command_entry_ref

let () =
  register_grammar Stdarg.wit_red_expr (Vernac_.red_expr);
