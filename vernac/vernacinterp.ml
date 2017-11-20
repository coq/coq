(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open CErrors

type deprecation = bool
type vernac_command = Genarg.raw_generic_argument list -> Loc.t option ->
  Vernacstate.t -> Vernacstate.t

(* Table of vernac entries *)
let vernac_tab =
  (Hashtbl.create 211 :
    (Vernacexpr.extend_name, deprecation * vernac_command) Hashtbl.t)

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

let call ?locality ?loc (opn,converted_args) =
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
    Locality.LocalityFixme.set locality;
    let res = hunk loc in
    Locality.LocalityFixme.assert_consumed ();
    res
  with
    | Drop -> raise Drop
    | reraise ->
        let reraise = CErrors.push reraise in
        if !Flags.debug then
	  Feedback.msg_debug (str"Vernac Interpreter " ++ str !phase);
        iraise reraise
