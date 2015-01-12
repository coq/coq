(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Managing locality *)

(** Commands which supported an inlined Local flag *)

val enforce_locality_full : bool option -> bool -> bool option

(** * Positioning locality for commands supporting discharging and export
    outside of modules *)

(** For commands whose default is to discharge and export:
    Global is the default and is neutral;
    Local in a section deactivates discharge,
    Local not in a section deactivates export *)

val make_locality : bool option -> bool
val make_non_locality : bool option -> bool
val enforce_locality : bool option -> bool -> bool
val enforce_locality_exp :
  bool option -> Decl_kinds.locality option -> Decl_kinds.locality

(** For commands whose default is to not discharge but to export:
    Global in sections forces discharge, Global not in section is the default;
    Local in sections is the default, Local not in section forces non-export *)

val make_section_locality : bool option -> bool
val enforce_section_locality : bool option -> bool -> bool

(** * Positioning locality for commands supporting export but not discharge *)

(** For commands whose default is to export (if not in section):
    Global in sections is forbidden, Global not in section is neutral;
    Local in sections is the default, Local not in section forces non-export *)

val make_module_locality : bool option -> bool
val enforce_module_locality : bool option -> bool -> bool

(* This is the old imperative interface that is still used for
 * VernacExtend vernaculars.  Time permitting this could be trashed too *)
module LocalityFixme : sig
  val set : bool option -> unit
  val consume : unit -> bool option
  val assert_consumed : unit -> unit
end
