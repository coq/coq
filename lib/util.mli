
(* $Id$ *)

open Pp

(* Errors *)

exception Anomaly of string * std_ppcmds  (* System errors *)
val anomaly : string -> 'a
val anomalylabstrm : string -> std_ppcmds -> 'a

exception UserError of string * std_ppcmds (* User errors *)
val error : string -> 'a
val errorlabstrm : string -> std_ppcmds -> 'a

(* Strings *)

val explode : string -> string list
val implode : string list -> string

val parse_section_path : string -> string list * string * string

(* Lists *)

val intersect : 'a list -> 'a list -> 'a list
val subtract : 'a list -> 'a list -> 'a list

(* Pretty-printing *)

val pr_spc : unit -> std_ppcmds
val pr_fnl : unit -> std_ppcmds
val pr_int : int -> std_ppcmds
val pr_str : string -> std_ppcmds
val pr_coma : unit -> std_ppcmds

val prlist : ('a -> 'b Stream.t) -> 'a list -> 'b Stream.t
val prlist_with_sep :
   (unit -> 'a Stream.t) -> ('b -> 'a Stream.t) -> 'b list -> 'a Stream.t
val prvect_with_sep :
   (unit -> 'a Stream.t) -> ('b -> 'a Stream.t) -> 'b array -> 'a Stream.t
