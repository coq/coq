(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Managing locality *)

let importability_of_bool = function
  | true -> Declare.ImportNeedQualified
  | false -> Declare.ImportDefaultBehavior

(** Positioning locality for commands supporting discharging and export
     outside of modules *)

(* For commands whose default is to discharge and export:
   Global is the default and is neutral;
   Local in a section deactivates discharge,
   Local not in a section deactivates export *)
let make_non_locality = function Some false -> false | _ -> true

let make_locality = function Some true -> true | _ -> false

let warn_local_declaration =
  CWarnings.create ~name:"local-declaration" ~category:"scope"
    Pp.(fun () ->
        Pp.strbrk "Interpreting this declaration as if " ++
        strbrk "a global declaration prefixed by \"Local\", " ++
        strbrk "i.e. as a global declaration which shall not be " ++
        strbrk "available without qualification when imported.")

let enforce_locality_exp locality_flag discharge =
  let open DeclareDef in
  let open Vernacexpr in
  match locality_flag, discharge with
  | Some b, NoDischarge -> Global (importability_of_bool b)
  | None, NoDischarge -> Global Declare.ImportDefaultBehavior
  | None, DoDischarge when not (Lib.sections_are_opened ()) ->
     (* If a Let/Variable is defined outside a section, then we consider it as a local definition *)
     warn_local_declaration ();
     Global Declare.ImportNeedQualified
  | None, DoDischarge -> Discharge
  | Some true, DoDischarge -> CErrors.user_err Pp.(str "Local not allowed in this case")
  | Some false, DoDischarge -> CErrors.user_err Pp.(str "Global not allowed in this case")

let enforce_locality locality_flag =
   make_locality locality_flag

(* For commands whose default is to not discharge but to export:
   Global in sections forces discharge, Global not in section is the default;
   Local in sections is the default, Local not in section forces non-export *)

let make_section_locality =
  function Some b -> b | None -> Lib.sections_are_opened ()

let enforce_section_locality locality_flag =
  make_section_locality locality_flag

(** Positioning locality for commands supporting export but not discharge *)

(* For commands whose default is to export (if not in section):
   Global in sections is forbidden, Global not in section is neutral;
   Local in sections is the default, Local not in section forces non-export *)

let make_module_locality = function
  | Some false ->
      if Lib.sections_are_opened () then
	CErrors.user_err Pp.(str
	  "This command does not support the Global option in sections.");
      false
  | Some true -> true
  | None -> false

let enforce_module_locality locality_flag =
  make_module_locality locality_flag
