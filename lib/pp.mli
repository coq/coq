(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Coq document type. *)

(** Pretty printing guidelines ******************************************)
(*                                                                      *)
(* `Pp.t` is the main pretty printing document type                     *)
(* in the Coq system. Documents are composed laying out boxes, and      *)
(* users can add arbitrary tag metadata that backends are free          *)
(* to interpret.                                                        *)
(*                                                                      *)
(* The datatype has a public view to allow serialization or advanced    *)
(* uses, however regular users are _strongly_ warned againt its use,    *)
(* they should instead rely on the available functions below.           *)
(*                                                                      *)
(* Box order and number is indeed an important factor. Try to create    *)
(* a proper amount of boxes. The `++` operator provides "efficient"     *)
(* concatenation, but using the list constructors is usually preferred. *)
(*                                                                      *)
(* That is to say, this:                                                *)
(*                                                                      *)
(* `hov [str "Term"; hov (pr_term t); str "is defined"]`                *)
(*                                                                      *)
(* is preferred to:                                                     *)
(*                                                                      *)
(* `hov (str "Term" ++ hov (pr_term t) ++ str "is defined")`            *)
(*                                                                      *)
(************************************************************************)

(* XXX: Improve and add attributes *)
type pp_tag = string

(* Following discussion on #390, we play on the safe side and make the
   internal representation opaque here. *)
type t

type std_ppcmds = t
[@@ocaml.deprecated "alias of Pp.t"]

type block_type =
  | Pp_hbox   of int
  | Pp_vbox   of int
  | Pp_hvbox  of int
  | Pp_hovbox of int

type doc_view =
  | Ppcmd_empty
  | Ppcmd_string of string
  | Ppcmd_glue of t list
  | Ppcmd_box  of block_type * t
  | Ppcmd_tag  of pp_tag * t
  (* Are those redundant? *)
  | Ppcmd_print_break of int * int
  | Ppcmd_force_newline
  | Ppcmd_comment of string list

val repr   : t -> doc_view
val unrepr : doc_view -> t

(** {6 Formatting commands} *)

val str   : string -> t
val brk   : int * int -> t
val fnl   : unit -> t
val ws    : int -> t
val mt    : unit -> t
val ismt  : t -> bool

val comment  : string list -> t

(** {6 Manipulation commands} *)

val app : t -> t -> t
(** Concatenation. *)

val seq : t list -> t
(** Multi-Concatenation. *)

val (++) : t -> t -> t
(** Infix alias for [app]. *)

(** {6 Derived commands} *)

val spc : unit -> t
val cut : unit -> t
val align : unit -> t
val int : int -> t
val real : float -> t
val bool : bool -> t
val qstring : string -> t
val qs : string -> t
val quote : t -> t
val strbrk : string -> t

(** {6 Boxing commands} *)

val h : int -> t -> t
val v : int -> t -> t
val hv : int -> t -> t
val hov : int -> t -> t

(** {6 Tagging} *)

val tag : pp_tag -> t -> t

(** {6 Printing combinators} *)

val pr_comma : unit -> t
(** Well-spaced comma. *)

val pr_semicolon : unit -> t
(** Well-spaced semicolon. *)

val pr_bar : unit -> t
(** Well-spaced pipe bar. *)

val pr_spcbar : unit -> t
(** Pipe bar with space before and after. *)

val pr_arg : ('a -> t) -> 'a -> t
(** Adds a space in front of its argument. *)

val pr_non_empty_arg : ('a -> t) -> 'a -> t
(** Adds a space in front of its argument if non empty. *)

val pr_opt : ('a -> t) -> 'a option -> t
(** Inner object preceded with a space if [Some], nothing otherwise. *)

val pr_opt_no_spc : ('a -> t) -> 'a option -> t
(** Same as [pr_opt] but without the leading space. *)

val pr_nth : int -> t
(** Ordinal number with the correct suffix (i.e. "st", "nd", "th", etc.). *)

val prlist : ('a -> t) -> 'a list -> t
(** Concatenation of the list contents, without any separator.

    Unlike all other functions below, [prlist] works lazily. If a strict
    behavior is needed, use [prlist_strict] instead. *)

val prlist_strict :  ('a -> t) -> 'a list -> t
(** Same as [prlist], but strict. *)

val prlist_with_sep :
   (unit -> t) -> ('a -> t) -> 'a list -> t
(** [prlist_with_sep sep pr [a ; ... ; c]] outputs
    [pr a ++ sep () ++ ... ++ sep () ++ pr c]. 
    where the thunk sep is memoized, rather than being called each place 
     its result is used.
*)

val prvect : ('a -> t) -> 'a array -> t
(** As [prlist], but on arrays. *)

val prvecti : (int -> 'a -> t) -> 'a array -> t
(** Indexed version of [prvect]. *)

val prvect_with_sep :
   (unit -> t) -> ('a -> t) -> 'a array -> t
(** As [prlist_with_sep], but on arrays. *)

val prvecti_with_sep :
   (unit -> t) -> (int -> 'a -> t) -> 'a array -> t
(** Indexed version of [prvect_with_sep]. *)

val pr_enum : ('a -> t) -> 'a list -> t
(** [pr_enum pr [a ; b ; ... ; c]] outputs
    [pr a ++ str "," ++ pr b ++ str "," ++ ... ++ str "and" ++ pr c]. *)

val pr_sequence : ('a -> t) -> 'a list -> t
(** Sequence of objects separated by space (unless an element is empty). *)

val surround : t -> t
(** Surround with parenthesis. *)

val pr_vertical_list : ('b -> t) -> 'b list -> t

(** {6 Main renderers, to formatter and to string } *)

(** [pp_with fmt pp] Print [pp] to [fmt] and don't flush [fmt]  *)
val pp_with          : Format.formatter -> t -> unit

val string_of_ppcmds : t -> string


(** Tag prefix to start a multi-token diff span *)
val start_pfx : string

(** Tag prefix to end a multi-token diff span *)
val end_pfx : string

(** Split a tag into prefix and base tag *)
val split_tag : string -> string * string

(** Print the Pp in tree form for debugging *)
val db_print_pp : Format.formatter -> t -> unit

(** Print the Pp in tree form for debugging, return as a string *)
val db_string_of_pp : t -> string

(** Combine nested Ppcmd_glues *)
val flatten : t -> t
