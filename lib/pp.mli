(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Modify pretty printing functions behavior for emacs ouput (special
   chars inserted at some places). This function should called once in
   module [Options], that's all. *)
val make_pp_emacs:unit -> unit
val make_pp_nonemacs:unit -> unit

(** Pretty-printers. *)

type std_ppcmds

(** {6 Formatting commands} *)

val str  : string -> std_ppcmds
val stras : int * string -> std_ppcmds
val brk : int * int -> std_ppcmds
val tbrk : int * int -> std_ppcmds
val tab : unit -> std_ppcmds
val fnl : unit -> std_ppcmds
val pifb : unit -> std_ppcmds
val ws : int -> std_ppcmds
val mt : unit -> std_ppcmds
val ismt : std_ppcmds -> bool

val comment : int -> std_ppcmds
val comments : ((int * int) * string) list ref

(** {6 Manipulation commands} *)

val app : std_ppcmds -> std_ppcmds -> std_ppcmds
(** Concatenation. *)

val (++) : std_ppcmds -> std_ppcmds -> std_ppcmds
(** Infix alias for [app]. *)

val eval_ppcmds : std_ppcmds -> std_ppcmds
(** Force computation. *)

val is_empty : std_ppcmds -> bool
(** Test emptyness. *)

(** {6 Derived commands} *)

val spc : unit -> std_ppcmds
val cut : unit -> std_ppcmds
val align : unit -> std_ppcmds
val int : int -> std_ppcmds
val real : float -> std_ppcmds
val bool : bool -> std_ppcmds
val qstring : string -> std_ppcmds
val qs : string -> std_ppcmds
val quote : std_ppcmds -> std_ppcmds
val strbrk : string -> std_ppcmds

(** {6 Boxing commands} *)

val h : int -> std_ppcmds -> std_ppcmds
val v : int -> std_ppcmds -> std_ppcmds
val hv : int -> std_ppcmds -> std_ppcmds
val hov : int -> std_ppcmds -> std_ppcmds
val t : std_ppcmds -> std_ppcmds

(** {6 Opening and closing of boxes} *)

val hb : int -> std_ppcmds
val vb : int -> std_ppcmds
val hvb : int -> std_ppcmds
val hovb : int -> std_ppcmds
val tb : unit -> std_ppcmds
val close : unit -> std_ppcmds
val tclose : unit -> std_ppcmds

(** {6 Sending messages to the user} *)
type message_level = Feedback.message_level =
  | Debug of string
  | Info
  | Notice
  | Warning
  | Error

type message = Feedback.message = {
  message_level : message_level;
  message_content : string;
}

type logger = message_level -> std_ppcmds -> unit

val msg_info : std_ppcmds -> unit
(** Message that displays information, usually in verbose mode, such as [Foobar
    is defined] *)

val msg_notice : std_ppcmds -> unit
(** Message that should be displayed, such as [Print Foo] or [Show Bar]. *)

val msg_warning : std_ppcmds -> unit
(** Message indicating that something went wrong, but without serious 
    consequences. *)

val msg_error : std_ppcmds -> unit
(** Message indicating that something went really wrong, though still 
    recoverable; otherwise an exception would have been raised. *)

val msg_debug : std_ppcmds -> unit
(** For debugging purposes *)

val std_logger : logger
(** Standard logging function *)

val set_logger : logger -> unit

val log_via_feedback : unit -> unit

val of_message : message -> Xml_datatype.xml
val to_message : Xml_datatype.xml -> message
val is_message : Xml_datatype.xml -> bool


(** {6 Feedback sent, even asynchronously, to the user interface} *)

(* This stuff should be available to most of the system, line msg_* above.
 * But I'm unsure this is the right place, especially for the global edit_id.
 *
 * Morally the parser gets a string and an edit_id, and gives back an AST.
 * Feedbacks during the parsing phase are attached to this edit_id.
 * The interpreter assignes an exec_id to the ast, and feedbacks happening
 * during interpretation are attached to the exec_id (still unimplemented,
 * since the two phases are performed sequentially) *)

val feedback :
  ?state_id:Feedback.state_id -> Feedback.feedback_content -> unit

val set_id_for_feedback : Feedback.edit_or_state_id -> unit
val set_feeder : (Feedback.feedback -> unit) -> unit

(** {6 Utilities} *)

val string_of_ppcmds : std_ppcmds -> string

(** {6 Printing combinators} *)

val pr_comma : unit -> std_ppcmds
(** Well-spaced comma. *)

val pr_semicolon : unit -> std_ppcmds
(** Well-spaced semicolon. *)

val pr_bar : unit -> std_ppcmds
(** Well-spaced pipe bar. *)

val pr_arg : ('a -> std_ppcmds) -> 'a -> std_ppcmds
(** Adds a space in front of its argument. *)

val pr_opt : ('a -> std_ppcmds) -> 'a option -> std_ppcmds
(** Inner object preceded with a space if [Some], nothing otherwise. *)

val pr_opt_no_spc : ('a -> std_ppcmds) -> 'a option -> std_ppcmds
(** Same as [pr_opt] but without the leading space. *)

val pr_nth : int -> std_ppcmds
(** Ordinal number with the correct suffix (i.e. "st", "nd", "th", etc.). *)

val prlist : ('a -> std_ppcmds) -> 'a list -> std_ppcmds
(** Concatenation of the list contents, without any separator.

    Unlike all other functions below, [prlist] works lazily. If a strict 
    behavior is needed, use [prlist_strict] instead. *)

val prlist_strict :  ('a -> std_ppcmds) -> 'a list -> std_ppcmds
(** Same as [prlist], but strict. *)

val prlist_with_sep :
   (unit -> std_ppcmds) -> ('a -> std_ppcmds) -> 'a list -> std_ppcmds
(** [prlist_with_sep sep pr [a ; ... ; c]] outputs
    [pr a ++ sep() ++ ... ++ sep() ++ pr c]. *)

val prvect : ('a -> std_ppcmds) -> 'a array -> std_ppcmds
(** As [prlist], but on arrays. *)

val prvecti : (int -> 'a -> std_ppcmds) -> 'a array -> std_ppcmds
(** Indexed version of [prvect]. *)

val prvect_with_sep :
   (unit -> std_ppcmds) -> ('a -> std_ppcmds) -> 'a array -> std_ppcmds
(** As [prlist_with_sep], but on arrays. *)

val prvecti_with_sep :
   (unit -> std_ppcmds) -> (int -> 'a -> std_ppcmds) -> 'a array -> std_ppcmds
(** Indexed version of [prvect_with_sep]. *)

val pr_enum : ('a -> std_ppcmds) -> 'a list -> std_ppcmds
(** [pr_enum pr [a ; b ; ... ; c]] outputs
    [pr a ++ str "," ++ pr b ++ str "," ++ ... ++ str "and" ++ pr c]. *)

val pr_sequence : ('a -> std_ppcmds) -> 'a list -> std_ppcmds
(** Sequence of objects separated by space (unless an element is empty). *)

val surround : std_ppcmds -> std_ppcmds
(** Surround with parenthesis. *)

val pr_vertical_list : ('b -> std_ppcmds) -> 'b list -> std_ppcmds

(** {6 Low-level pretty-printing functions {% \emph{%}without flush{% }%}. } *)

val pp_with : Format.formatter -> std_ppcmds -> unit
val ppnl_with : Format.formatter -> std_ppcmds -> unit
val pp_flush_with : Format.formatter -> unit -> unit

(** {6 Pretty-printing functions {% \emph{%}without flush{% }%} on [stdout] and [stderr]. } *)

(** These functions are low-level interface to printing and should not be used
    in usual code. Consider using the [msg_*] function family instead. *)

val pp : std_ppcmds -> unit
val ppnl : std_ppcmds -> unit
val pperr : std_ppcmds -> unit
val pperrnl : std_ppcmds -> unit
val pperr_flush : unit -> unit
val pp_flush : unit -> unit
val flush_all: unit -> unit

(** {6 Deprecated functions} *)

(** DEPRECATED. Do not use in newly written code. *)

val msg_with : Format.formatter -> std_ppcmds -> unit

val msg : std_ppcmds -> unit
val msgnl : std_ppcmds -> unit
val msgerr : std_ppcmds -> unit
val msgerrnl : std_ppcmds -> unit
val message : string -> unit       (** = pPNL *)
