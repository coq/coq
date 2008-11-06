(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Names
open Libnames
open Miniml
open Mlutil
open Pp

val fnl2 : unit -> std_ppcmds
val space_if : bool -> std_ppcmds
val sec_space_if : bool -> std_ppcmds

val pp_par : bool -> std_ppcmds -> std_ppcmds
val pp_apply : std_ppcmds -> bool -> std_ppcmds list -> std_ppcmds
val pr_binding : identifier list -> std_ppcmds

val rename_id : identifier -> Idset.t -> identifier

type env = identifier list * Idset.t
val empty_env : unit -> env

val rename_vars: Idset.t -> identifier list -> env
val rename_tvars: Idset.t -> identifier list -> identifier list
val push_vars : identifier list -> env -> identifier list * env
val get_db_name : int -> env -> identifier

type phase = Pre | Impl | Intf

val set_phase : phase -> unit
val get_phase : unit -> phase

val opened_libraries : unit -> module_path list

type kind = Term | Type | Cons | Mod

val pp_global : kind -> global_reference -> string
val pp_module : module_path -> string

val top_visible_mp : unit -> module_path
val push_visible : module_path -> mod_self_id option -> unit
val pop_visible : unit -> unit

val check_duplicate : module_path -> label -> string

type reset_kind = AllButExternal | Everything

val reset_renaming_tables : reset_kind -> unit

val set_keywords : Idset.t -> unit
