
(* $Id$ *)

open Pp_control

type 'a ppcmd_token

type std_ppcmds = (int*string) ppcmd_token Stream.t

(* formatting commands *)
val sTR  : string -> (int*string) ppcmd_token (* string *)
val sTRas : int * string -> (int*string) ppcmd_token
                                              (* string with length *)
val bRK  : int * int -> 'a ppcmd_token        (* break *)
val tBRK : int * int -> 'a ppcmd_token        (* go to tabulation *)
val tAB  : 'a ppcmd_token                     (* set tabulation *)
val fNL  : 'a ppcmd_token                     (* force newline *)
val pifB : 'a ppcmd_token                     (* print if broken *)
val wS   : int -> 'a ppcmd_token              (* white space *)

(* derived commands *)
val sPC     : 'a ppcmd_token                        (* space *)
val cUT     : 'a ppcmd_token                        (* cut *)
val aLIGN   : 'a ppcmd_token                        (* go to tab *)
val iNT     : int -> (int*string) ppcmd_token       (* int *)
val rEAL    : float -> (int * string) ppcmd_token   (* real *)
val bOOL    : bool -> (int * string) ppcmd_token    (* bool *)
val qSTRING : string -> (int * string) ppcmd_token  (* quoted string *)
val qS      : string -> (int * string) ppcmd_token  (*   "       "   *)

(* boxing commands *)
val h   : int -> std_ppcmds -> std_ppcmds (* H box   *) 
val v   : int -> std_ppcmds -> std_ppcmds (* V box   *)
val hV  : int -> std_ppcmds -> std_ppcmds (* HV box  *)  
val hOV : int -> std_ppcmds -> std_ppcmds (* HOV box *)
val t   : std_ppcmds -> std_ppcmds        (* TAB box *)

(* Opening and closing of boxes *)
val hB    : int -> 'a ppcmd_token  (* open hbox *)
val vB    : int -> 'a ppcmd_token  (* open vbox *)
val hVB   : int -> 'a ppcmd_token  (* open hvbox *)
val hOVB  : int -> 'a ppcmd_token  (* open hovbox *)
val tB    : 'a ppcmd_token         (* open tbox *)
val cLOSE : 'a ppcmd_token         (* close box *)
val tCLOSE: 'a ppcmd_token         (* close tbox *)


(* pretty printing functions WITHOUT FLUSH *)
val pP_with       : Format.formatter -> std_ppcmds -> unit
val pPNL_with     : Format.formatter -> std_ppcmds -> unit
val warning_with  : Format.formatter -> string -> unit
val wARN_with     : Format.formatter -> std_ppcmds -> unit
val pp_flush_with : Format.formatter -> unit -> unit

(* pretty printing functions WITH FLUSH *)
val mSG_with      : Format.formatter -> std_ppcmds -> unit
val mSGNL_with    : Format.formatter -> std_ppcmds -> unit


(* These are instances of the previous ones on std_ft and err_ft *)

(* pretty printing functions WITHOUT FLUSH on stdout and stderr *)
val pP       : std_ppcmds -> unit
val pPNL     : std_ppcmds -> unit
val pPERR    : std_ppcmds -> unit
val pPERRNL  : std_ppcmds -> unit
val message  : string -> unit       (* = pPNL *)
val warning  : string -> unit
val wARN     : std_ppcmds -> unit
val pp_flush : unit -> unit
val flush_all: unit -> unit

(* pretty printing functions WITH FLUSH on stdout and stderr *)
val mSG      : std_ppcmds -> unit
val mSGNL    : std_ppcmds -> unit
val mSGERR   : std_ppcmds -> unit
val mSGERRNL : std_ppcmds -> unit
val wARNING  : std_ppcmds -> unit

