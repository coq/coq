(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp
open CErrors

type deprecation = { since : string option ; note : string option }

let mk_deprecation ?(since=None) ?(note=None) () =
  { since ; note }

type atts = {
  loc : Loc.t option;
  locality : bool option;
  polymorphic : bool;
  program : bool;
  deprecated : deprecation option;
}

let mk_atts ?(loc=None) ?(locality=None) ?(polymorphic=false) ?(program=false) ?(deprecated=None) () : atts =
  { loc ; locality ; polymorphic ; program ; deprecated }

type 'a vernac_command = 'a -> atts:atts -> st:Vernacstate.t -> Vernacstate.t

type plugin_args = Genarg.raw_generic_argument list

(* Table of vernac entries *)
let vernac_tab =
  (Hashtbl.create 211 :
    (Vernacexpr.extend_name, bool * plugin_args vernac_command) Hashtbl.t)

let vinterp_add depr s f =
  try
    Hashtbl.add vernac_tab s (depr, f)
  with Failure _ ->
    user_err ~hdr:"vinterp_add"
      (str"Cannot add the vernac command " ++ str (fst s) ++ str" twice.")

let overwriting_vinterp_add s f =
  begin
    try
      let _ = Hashtbl.find vernac_tab s in Hashtbl.remove vernac_tab s
    with Not_found -> ()
  end;
  Hashtbl.add vernac_tab s (false, f)

let vinterp_map s =
  try
    Hashtbl.find vernac_tab s
  with Failure _ | Not_found ->
    user_err ~hdr:"Vernac Interpreter"
      (str"Cannot find vernac command " ++ str (fst s) ++ str".")

let vinterp_init () = Hashtbl.clear vernac_tab

let warn_deprecated_command =
  let open CWarnings in
  create ~name:"deprecated-command" ~category:"deprecated"
         (fun pr -> str "Deprecated vernacular command: " ++ pr)

(* Interpretation of a vernac command *)

let call opn converted_args ~atts ~st =
  let phase = ref "Looking up command" in
  try
    let depr, callback = vinterp_map opn in
    let () = if depr then
      let rules = Egramml.get_extend_vernac_rule opn in
      let pr_gram = function
      | Egramml.GramTerminal s -> str s
      | Egramml.GramNonTerminal _ -> str "_"
      in
      let pr = pr_sequence pr_gram rules in
      warn_deprecated_command pr;
    in
    phase := "Checking arguments";
    let hunk = callback converted_args in
    phase := "Executing command";
    hunk ~atts ~st
  with
    | reraise ->
        let reraise = CErrors.push reraise in
        if !Flags.debug then
	  Feedback.msg_debug (str"Vernac Interpreter " ++ str !phase);
        iraise reraise
