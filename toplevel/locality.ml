(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Managing locality *)

let local_of_bool = function
  | true -> Decl_kinds.Local
  | false -> Decl_kinds.Global

let check_locality locality_flag =
  match locality_flag with
  | Some b ->
    let s = if b then "Local" else "Global" in
    Errors.error ("This command does not support the \""^s^"\" prefix.")
  | None -> ()

(** Extracting the locality flag *)

(* Commands which supported an inlined Local flag *)

let enforce_locality_full locality_flag local =
  let local =
    match locality_flag with
    | Some false when local ->
	Errors.error "Cannot be simultaneously Local and Global."
    | Some true when local ->
	Errors.error "Use only prefix \"Local\"."
    | None ->
	if local then begin
          Pp.msg_warning (Pp.str "Obsolete syntax: use \"Local\" as a prefix.");
	  Some true
	end else
	None
    | Some b -> Some b in
  local

(** Positioning locality for commands supporting discharging and export
     outside of modules *)

(* For commands whose default is to discharge and export:
   Global is the default and is neutral;
   Local in a section deactivates discharge,
   Local not in a section deactivates export *)
let make_non_locality = function Some false -> false | _ -> true

let make_locality = function Some true -> true | _ -> false

let enforce_locality locality_flag local =
   make_locality (enforce_locality_full locality_flag local)

let enforce_locality_exp locality_flag local =
  match locality_flag, local with
  | None, Some local -> local
  | Some b, None -> local_of_bool b
  | None, None -> Decl_kinds.Global
  | Some _, Some _ -> Errors.error "Local non allowed in this case"

(* For commands whose default is to not discharge but to export:
   Global in sections forces discharge, Global not in section is the default;
   Local in sections is the default, Local not in section forces non-export *)

let make_section_locality =
  function Some b -> b | None -> Lib.sections_are_opened ()

let enforce_section_locality locality_flag local =
  make_section_locality (enforce_locality_full locality_flag local)

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

let enforce_module_locality locality_flag local =
  make_module_locality (enforce_locality_full locality_flag local)

module LocalityFixme = struct
  let locality = ref None
  let set l = locality := l
  let consume () =
    let l = !locality in
    locality := None;
    l
  let assert_consumed () = check_locality !locality
end
