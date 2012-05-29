(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Managing locality *)

let locality_flag = ref None

let local_of_bool = function
  | true -> Decl_kinds.Local
  | false -> Decl_kinds.Global

let check_locality () =
  match !locality_flag with
  | Some (loc,b) ->
    let s = if b then "Local" else "Global" in
    Errors.user_err_loc
      (loc,"",Pp.str ("This command does not support the \""^s^"\" prefix."))
  | None -> ()

(** Extracting the locality flag *)

(* Commands which supported an inlined Local flag *)

let enforce_locality_full local =
  let local =
    match !locality_flag with
    | Some (_,false) when local ->
	Errors.error "Cannot be simultaneously Local and Global."
    | Some (_,true) when local ->
	Errors.error "Use only prefix \"Local\"."
    | None ->
	if local then begin
	  Flags.if_warn
	   Pp.msg_warning (Pp.str"Obsolete syntax: use \"Local\" as a prefix.");
	  Some true
	end else
	None
    | Some (_,b) -> Some b in
  locality_flag := None;
  local

(* Commands which did not supported an inlined Local flag (synonym of
   [enforce_locality_full false]) *)

let use_locality_full () =
  let r = Option.map snd !locality_flag in
  locality_flag := None;
   r

(** Positioning locality for commands supporting discharging and export
     outside of modules *)

(* For commands whose default is to discharge and export:
   Global is the default and is neutral;
   Local in a section deactivates discharge,
   Local not in a section deactivates export *)

let make_locality = function Some true -> true | _ -> false

let use_locality () = make_locality (use_locality_full ())

let use_locality_exp () = local_of_bool (use_locality ())

let enforce_locality local = make_locality (enforce_locality_full local)

let enforce_locality_exp local = local_of_bool (enforce_locality local)

(* For commands whose default is not to discharge and not to export:
   Global forces discharge and export;
   Local is the default and is neutral *)

let use_non_locality () =
  match use_locality_full () with Some false -> false | _ -> true

(* For commands whose default is to not discharge but to export:
   Global in sections forces discharge, Global not in section is the default;
   Local in sections is the default, Local not in section forces non-export *)

let make_section_locality =
  function Some b -> b | None -> Lib.sections_are_opened ()

let use_section_locality () =
  make_section_locality (use_locality_full ())

let enforce_section_locality local =
  make_section_locality (enforce_locality_full local)

(** Positioning locality for commands supporting export but not discharge *)

(* For commands whose default is to export (if not in section):
   Global in sections is forbidden, Global not in section is neutral;
   Local in sections is the default, Local not in section forces non-export *)

let make_module_locality = function
  | Some false ->
      if Lib.sections_are_opened () then
	Errors.error
	  "This command does not support the Global option in sections.";
      false
  | Some true -> true
  | None -> false

let use_module_locality () =
  make_module_locality (use_locality_full ())

let enforce_module_locality local =
  make_module_locality (enforce_locality_full local)
