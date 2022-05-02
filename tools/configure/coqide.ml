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
open CmdArgs
open CmdArgs.Prefs

let (/) = Filename.concat

(** * lablgtk3 and CoqIDE *)

(** Detect and/or verify the Lablgtk3 location *)

let get_lablgtkdir ocamlfind =
  tryrun ocamlfind ["query";"lablgtk3-sourceview3"]

(** Detect and/or verify the Lablgtk2 version *)

let check_lablgtk_version ocamlfind =
  let v, _ = tryrun ocamlfind ["query"; "-format"; "%v"; "lablgtk3"] in
  try
    let vn = generic_version_nums ~name:"lablgtk3" v in
    if vn < [3; 1; 2] then
      (false, v)
    else
      (true, v)
  with _ -> (false, v)

let pr_ide = function No -> "no" | Byte -> "only bytecode" | Opt -> "native"

exception Ide of ide

(** If the user asks an impossible coqide, we abort the configuration *)

let set_ide prefs ide msg = match ide, prefs.coqide with
  | No, Some (Byte|Opt)
  | Byte, Some Opt -> die (msg^":\n=> cannot build requested CoqIDE")
  | _ ->
    cprintf prefs "%s:\n=> %s CoqIDE will be built." msg (pr_ide ide);
    raise (Ide ide)

(* XXX *)
let lablgtkdir = ref ""

(** Which CoqIDE is possible ? Which one is requested ?
    This function also sets the lablgtkdir reference in case of success. *)

let check_coqide ocamlfind prefs best_compiler camllib =
  if prefs.coqide = Some No then set_ide prefs No "CoqIde manually disabled";
  let dir, via = get_lablgtkdir ocamlfind in
  if dir = ""
  then set_ide prefs No "LablGtk3 or LablGtkSourceView3 not found"
  else
    let (ok, version) = check_lablgtk_version ocamlfind in
    let found = Format.sprintf "LablGtk3 and LablGtkSourceView3 found (%s)" version in
    if not ok then set_ide prefs No (found^", but too old (required >= 3.1.2, found " ^ version ^ ")");
    (* We're now sure to produce at least one kind of coqide *)
    lablgtkdir := dir;
    if prefs.coqide = Some Byte then set_ide prefs Byte (found^", bytecode requested");
    if best_compiler <> "opt" then set_ide prefs Byte (found^", but no native compiler");
    if not (Sys.file_exists (camllib/"threads"/"threads.cmxa")) then
      set_ide prefs Byte (found^", but no native threads");
    set_ide prefs Opt (found^", with native threads")

let coqide ocamlfind prefs best_compiler camllib =
  (try check_coqide ocamlfind prefs best_compiler camllib
   with Ide Opt -> "opt" | Ide Byte -> "byte" | Ide No -> "no"), !lablgtkdir

(** System-specific CoqIDE flags *)

let idearchdef ocamlfind prefs coqide arch =
  match coqide, arch with
    | "opt", "Darwin" when prefs.macintegration ->
      let osxdir,_ = tryrun ocamlfind ["query";"lablgtkosx"] in
      if osxdir <> "" then "QUARTZ" else "X11"
    | "opt", "win32" ->
      "WIN32"
    | _, "win32" ->
      "WIN32"
    | _ -> "X11"
