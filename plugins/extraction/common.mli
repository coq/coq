(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

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
val pp_array : ('a -> Pp.t) -> 'a list -> Pp.t
val pp_boxed_tuple : ('a -> Pp.t) -> 'a list -> Pp.t

val pr_binding : Names.Id.t list -> Pp.t

val rename_id : Names.Id.t -> Names.Id.Set.t -> Names.Id.t

type env = Names.Id.t list * Names.Id.Set.t
val empty_env : unit -> env

val rename_vars: Names.Id.Set.t -> Names.Id.t list -> env
val rename_tvars: Names.Id.Set.t -> Names.Id.t list -> Names.Id.t list
val push_vars : Names.Id.t list -> env -> Names.Id.t list * env
val get_db_name : int -> env -> Names.Id.t

type phase = Pre | Impl | Intf

val set_phase : phase -> unit
val get_phase : unit -> phase

val opened_libraries : unit -> Names.ModPath.t list

type kind = Term | Type | Cons | Mod

val pp_global : kind -> Names.GlobRef.t -> string
val pp_global_name : kind -> Names.GlobRef.t -> string
val pp_module : Names.ModPath.t -> string

val top_visible_mp : unit -> Names.ModPath.t
(* In [push_visible], the [module_path list] corresponds to
   module parameters, the innermost one coming first in the list *)
val push_visible : Names.ModPath.t -> Names.ModPath.t list -> unit
val pop_visible : unit -> unit

val get_duplicate : Names.ModPath.t -> Names.Label.t -> string option

type reset_kind = AllButExternal | Everything

val reset_renaming_tables : reset_kind -> unit

val set_keywords : Names.Id.Set.t -> unit

(** Special hack for constants of type Ascii.ascii : if an
    [Extract Inductive ascii => char] has been declared, then
    the constants are directly turned into chars *)

val is_native_char : Miniml.ml_ast -> bool
val get_native_char : Miniml.ml_ast -> char
val pp_native_char : Miniml.ml_ast -> Pp.t

(** Special hack for constants of type String.string : if an
    [Extract Inductive string => string] has been declared, then
    the constants are directly turned into string literals *)

val is_native_string : Miniml.ml_ast -> bool
val get_native_string : Miniml.ml_ast -> string
val pp_native_string : Miniml.ml_ast -> Pp.t

(* Registered sig type *)
val sig_type_ref : unit -> Names.GlobRef.t
