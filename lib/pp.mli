
(* $Id$ *)

(*i*)
open Pp_control
(*i*)

(* Pretty-printers. *)

type 'a ppcmd_token

type std_ppcmds = (int*string) ppcmd_token Stream.t

(*s Formatting commands. *)

val sTR  : string -> (int*string) ppcmd_token
val sTRas : int * string -> (int*string) ppcmd_token
val bRK : int * int -> 'a ppcmd_token
val tBRK : int * int -> 'a ppcmd_token
val tAB : 'a ppcmd_token
val fNL : 'a ppcmd_token
val pifB : 'a ppcmd_token
val wS : int -> 'a ppcmd_token

(*s Derived commands. *)

val sPC : 'a ppcmd_token
val cUT : 'a ppcmd_token
val aLIGN : 'a ppcmd_token
val iNT : int -> (int*string) ppcmd_token
val rEAL : float -> (int * string) ppcmd_token
val bOOL : bool -> (int * string) ppcmd_token
val qSTRING : string -> (int * string) ppcmd_token
val qS : string -> (int * string) ppcmd_token

(*s Boxing commands. *)

val h : int -> std_ppcmds -> std_ppcmds
val v : int -> std_ppcmds -> std_ppcmds
val hV : int -> std_ppcmds -> std_ppcmds
val hOV : int -> std_ppcmds -> std_ppcmds
val t : std_ppcmds -> std_ppcmds

(*s Opening and closing of boxes. *)

val hB : int -> 'a ppcmd_token
val vB : int -> 'a ppcmd_token
val hVB : int -> 'a ppcmd_token
val hOVB : int -> 'a ppcmd_token
val tB : 'a ppcmd_token
val cLOSE : 'a ppcmd_token
val tCLOSE : 'a ppcmd_token

(*s Pretty-printing functions WITHOUT FLUSH. *)

val pP_with : Format.formatter -> std_ppcmds -> unit
val pPNL_with : Format.formatter -> std_ppcmds -> unit
val warning_with : Format.formatter -> string -> unit
val wARN_with : Format.formatter -> std_ppcmds -> unit
val pp_flush_with : Format.formatter -> unit -> unit

(*s Pretty-printing functions WITH FLUSH. *)

val mSG_with : Format.formatter -> std_ppcmds -> unit
val mSGNL_with : Format.formatter -> std_ppcmds -> unit


(*s The following functions are instances of the previous ones on
  [std_ft] and [err_ft]. *)

(*s Pretty-printing functions WITHOUT FLUSH on [stdout] and [stderr]. *)

val pP : std_ppcmds -> unit
val pPNL : std_ppcmds -> unit
val pPERR : std_ppcmds -> unit
val pPERRNL : std_ppcmds -> unit
val message : string -> unit       (* = pPNL *)
val warning : string -> unit
val wARN : std_ppcmds -> unit
val pp_flush : unit -> unit
val flush_all: unit -> unit

(*s Pretty-printing functions WITH FLUSH on [stdout] and [stderr]. *)

val mSG : std_ppcmds -> unit
val mSGNL : std_ppcmds -> unit
val mSGERR : std_ppcmds -> unit
val mSGERRNL : std_ppcmds -> unit
val wARNING : std_ppcmds -> unit

