(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Miniml

(** By default, in module Format, you can do horizontal placing of blocks
    even if they include newlines, as long as the number of chars in the
    blocks are less that a line length. To avoid this awkward situation,
    we attach a big virtual size to [fnl] newlines. *)

val fnl : unit -> Pp.t
val fnl2 : unit -> Pp.t
val space_if : bool -> Pp.t

val pp_par : bool -> Pp.t -> Pp.t

(** [pp_apply] : a head part applied to arguments, possibly with parenthesis *)
val pp_apply : Pp.t -> bool -> Pp.t list -> Pp.t

(** Same as [pp_apply], but with also protection of the head by parenthesis *)
val pp_apply2 : Pp.t -> bool -> Pp.t list -> Pp.t

val pp_tuple_light : (bool -> 'a -> Pp.t) -> 'a list -> Pp.t
val pp_tuple : ('a -> Pp.t) -> 'a list -> Pp.t
val pp_boxed_tuple : ('a -> Pp.t) -> 'a list -> Pp.t

val pr_binding : Id.t list -> Pp.t

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

val opened_libraries : unit -> ModPath.t list

type kind = Term | Type | Cons | Mod

val pp_global : kind -> GlobRef.t -> string
val pp_module : ModPath.t -> string

val top_visible_mp : unit -> ModPath.t
(* In [push_visible], the [module_path list] corresponds to
   module parameters, the innermost one coming first in the list *)
val push_visible : ModPath.t -> ModPath.t list -> unit
val pop_visible : unit -> unit

val get_duplicate : ModPath.t -> Label.t -> string option

type reset_kind = AllButExternal | Everything

val reset_renaming_tables : reset_kind -> unit

val set_keywords : Id.Set.t -> unit

(** For instance: [mk_ind "Coq.Init.Datatypes" "nat"] *)

val mk_ind : string -> string -> MutInd.t

(** Special hack for constants of type Ascii.ascii : if an
    [Extract Inductive ascii => char] has been declared, then
    the constants are directly turned into chars *)

val is_native_char : ml_ast -> bool
val get_native_char : ml_ast -> char
val pp_native_char : ml_ast -> Pp.t
