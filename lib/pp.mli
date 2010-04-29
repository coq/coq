(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

open Pp_control

(** Modify pretty printing functions behavior for emacs ouput (special
   chars inserted at some places). This function should called once in
   module [Options], that's all. *)
val make_pp_emacs:unit -> unit
val make_pp_nonemacs:unit -> unit

(** Pretty-printers. *)

type ppcmd

type std_ppcmds = ppcmd Stream.t

(** {6 Formatting commands. } *)

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

(** {6 Concatenation. } *)

val (++) : std_ppcmds -> std_ppcmds -> std_ppcmds

(** {6 Derived commands. } *)

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

val xmlescape : ppcmd -> ppcmd

(** {6 Boxing commands. } *)

val h : int -> std_ppcmds -> std_ppcmds
val v : int -> std_ppcmds -> std_ppcmds
val hv : int -> std_ppcmds -> std_ppcmds
val hov : int -> std_ppcmds -> std_ppcmds
val t : std_ppcmds -> std_ppcmds

(** {6 Opening and closing of boxes. } *)

val hb : int -> std_ppcmds
val vb : int -> std_ppcmds
val hvb : int -> std_ppcmds
val hovb : int -> std_ppcmds
val tb : unit -> std_ppcmds
val close : unit -> std_ppcmds
val tclose : unit -> std_ppcmds

(** {6 Pretty-printing functions {% \emph{%}without flush{% }%}. } *)

val pp_with : Format.formatter -> std_ppcmds -> unit
val ppnl_with : Format.formatter -> std_ppcmds -> unit
val warning_with : Format.formatter -> string -> unit
val warn_with : Format.formatter -> std_ppcmds -> unit
val pp_flush_with : Format.formatter -> unit -> unit

val set_warning_function : (Format.formatter -> std_ppcmds -> unit) -> unit

(** {6 Pretty-printing functions {% \emph{%}with flush{% }%}. } *)

val msg_with : Format.formatter -> std_ppcmds -> unit
val msgnl_with : Format.formatter -> std_ppcmds -> unit


(** {6 Sect } *)
(** The following functions are instances of the previous ones on
  [std_ft] and [err_ft]. *)

(** {6 Pretty-printing functions {% \emph{%}without flush{% }%} on [stdout] and [stderr]. } *)

val pp : std_ppcmds -> unit
val ppnl : std_ppcmds -> unit
val pperr : std_ppcmds -> unit
val pperrnl : std_ppcmds -> unit
val message : string -> unit       (** = pPNL *)
val warning : string -> unit
val warn : std_ppcmds -> unit
val pp_flush : unit -> unit
val flush_all: unit -> unit

(** {6 Pretty-printing functions {% \emph{%}with flush{% }%} on [stdout] and [stderr]. } *)

val msg : std_ppcmds -> unit
val msgnl : std_ppcmds -> unit
val msgerr : std_ppcmds -> unit
val msgerrnl : std_ppcmds -> unit
val msg_warning : std_ppcmds -> unit
