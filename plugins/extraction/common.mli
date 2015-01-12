(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Globnames
open Miniml
open Pp

(** By default, in module Format, you can do horizontal placing of blocks
    even if they include newlines, as long as the number of chars in the
    blocks are less that a line length. To avoid this awkward situation,
    we attach a big virtual size to [fnl] newlines. *)

val fnl : unit -> std_ppcmds
val fnl2 : unit -> std_ppcmds
val space_if : bool -> std_ppcmds

val pp_par : bool -> std_ppcmds -> std_ppcmds

(** [pp_apply] : a head part applied to arguments, possibly with parenthesis *)
val pp_apply : std_ppcmds -> bool -> std_ppcmds list -> std_ppcmds

(** Same as [pp_apply], but with also protection of the head by parenthesis *)
val pp_apply2 : std_ppcmds -> bool -> std_ppcmds list -> std_ppcmds

val pp_tuple_light : (bool -> 'a -> std_ppcmds) -> 'a list -> std_ppcmds
val pp_tuple : ('a -> std_ppcmds) -> 'a list -> std_ppcmds
val pp_boxed_tuple : ('a -> std_ppcmds) -> 'a list -> std_ppcmds

val pr_binding : Id.t list -> std_ppcmds

val rename_id : Id.t -> Id.Set.t -> Id.t

type env = Id.t list * Id.Set.t
val empty_env : unit -> env

val rename_vars: Id.Set.t -> Id.t list -> env
val rename_tvars: Id.Set.t -> Id.t list -> Id.t list
val push_vars : Id.t list -> env -> Id.t list * env
val get_db_name : int -> env -> Id.t

type phase = Pre | Impl | Intf

val set_phase : phase -> unit
val get_phase : unit -> phase

val opened_libraries : unit -> module_path list

type kind = Term | Type | Cons | Mod

val pp_global : kind -> global_reference -> string
val pp_module : module_path -> string

val top_visible_mp : unit -> module_path
(* In [push_visible], the [module_path list] corresponds to
   module parameters, the innermost one coming first in the list *)
val push_visible : module_path -> module_path list -> unit
val pop_visible : unit -> unit

val check_duplicate : module_path -> Label.t -> string

type reset_kind = AllButExternal | Everything

val reset_renaming_tables : reset_kind -> unit

val set_keywords : Id.Set.t -> unit

(** For instance: [mk_ind "Coq.Init.Datatypes" "nat"] *)

val mk_ind : string -> string -> mutual_inductive

(** Special hack for constants of type Ascii.ascii : if an
    [Extract Inductive ascii => char] has been declared, then
    the constants are directly turned into chars *)

val is_native_char : ml_ast -> bool
val get_native_char : ml_ast -> char
val pp_native_char : ml_ast -> std_ppcmds
