
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
val list_chop  : int -> 'a list -> 'a list * 'a list

(* Arrays *)

val array_exists : ('a -> bool) -> 'a array -> bool
val array_for_all : ('a -> bool) -> 'a array -> bool
val array_for_all2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool
val array_hd : 'a array -> 'a
val array_tl : 'a array -> 'a array
val array_last : 'a array -> 'a
val array_cons : 'a -> 'a array -> 'a array
val array_fold_left_from : int -> ('a -> 'b -> 'a) -> 'a -> 'b array -> 'a
val array_fold_right_from : int -> ('a -> 'b -> 'b) -> 'a array -> 'b -> 'b
val array_app_tl : 'a array -> 'a list -> 'a list
val array_list_of_tl : 'a array -> 'a list
val array_map_to_list : ('a -> 'b) -> 'a array ->'b list
val array_chop : int -> 'a array -> 'a array * 'a array

(* Functions *)

val compose : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val iterate : ('a -> 'a) -> int -> 'a -> 'a

(* Misc *)

type ('a,'b) union = Inl of 'a | Inr of 'b

module Intset : Set.S with type elt = int

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
