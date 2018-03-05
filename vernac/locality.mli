(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Managing locality *)

(** * Positioning locality for commands supporting discharging and export
    outside of modules *)

(** For commands whose default is to discharge and export:
    Global is the default and is neutral;
    Local in a section deactivates discharge,
    Local not in a section deactivates export *)

val make_locality : bool option -> bool
val make_non_locality : bool option -> bool
val enforce_locality_exp : bool option -> Decl_kinds.discharge -> Decl_kinds.locality
val enforce_locality : bool option -> bool

(** For commands whose default is to not discharge but to export:
    Global in sections forces discharge, Global not in section is the default;
    Local in sections is the default, Local not in section forces non-export *)

val make_section_locality : bool option -> bool
val enforce_section_locality : bool option -> bool

(** * Positioning locality for commands supporting export but not discharge *)

(** For commands whose default is to export (if not in section):
    Global in sections is forbidden, Global not in section is neutral;
    Local in sections is the default, Local not in section forces non-export *)

val make_module_locality : bool option -> bool
val enforce_module_locality : bool option -> bool
