
(* $Id$ *)

(*i*)
open Pp
(*i*)

(* Errors. [Anomaly] is used for system errors and [UserError] for the
   user's ones. *)

exception Anomaly of string * std_ppcmds
val anomaly : string -> 'a
val anomalylabstrm : string -> std_ppcmds -> 'a

exception UserError of string * std_ppcmds
val error : string -> 'a
val errorlabstrm : string -> std_ppcmds -> 'a

(*s Strings. *)

val explode : string -> string list
val implode : string list -> string

val parse_section_path : string -> string list * string * string

module Stringmap : Map.S with type key = string

(*s Lists. *)

val list_intersect : 'a list -> 'a list -> 'a list
val list_unionq : 'a list -> 'a list -> 'a list
val list_subtract : 'a list -> 'a list -> 'a list
val list_subtractq : 'a list -> 'a list -> 'a list
val list_chop : int -> 'a list -> 'a list * 'a list
val list_tabulate : (int -> 'a) -> int -> 'a list
val list_assign : 'a list -> int -> 'a -> 'a list
val list_distinct : 'a list -> bool
val list_map_i : (int -> 'a -> 'b) -> int -> 'a list -> 'b list
val list_index : 'a -> 'a list -> int
val list_fold_left_i :  (int -> 'a -> 'b -> 'a) -> int -> 'a -> 'b list -> 'a
val list_for_all_i : (int -> 'a -> bool) -> int -> 'a list -> bool

(*s Arrays. *)

val array_exists : ('a -> bool) -> 'a array -> bool
val array_for_all : ('a -> bool) -> 'a array -> bool
val array_for_all2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool
val array_hd : 'a array -> 'a
val array_tl : 'a array -> 'a array
val array_last : 'a array -> 'a
val array_cons : 'a -> 'a array -> 'a array
val array_fold_left2 : 
  ('a -> 'b -> 'c -> 'a) -> 'a -> 'b array -> 'c array -> 'a
val array_fold_left2_i : 
  (int -> 'a -> 'b -> 'c -> 'a) -> 'a -> 'b array -> 'c array -> 'a
val array_fold_left_from : int -> ('a -> 'b -> 'a) -> 'a -> 'b array -> 'a
val array_fold_right_from : int -> ('a -> 'b -> 'b) -> 'a array -> 'b -> 'b
val array_app_tl : 'a array -> 'a list -> 'a list
val array_list_of_tl : 'a array -> 'a list
val array_map_to_list : ('a -> 'b) -> 'a array ->'b list
val array_chop : int -> 'a array -> 'a array * 'a array
val array_map2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array

(*s Functions. *)

val compose : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val iterate : ('a -> 'a) -> int -> 'a -> 'a

(*s Misc. *)

type ('a,'b) union = Inl of 'a | Inr of 'b

module Intset : Set.S with type elt = int

val option_app : ('a -> 'b) -> 'a option -> 'b option

(*s Time stamps. *)

type time_stamp

val get_time_stamp : unit -> time_stamp
val compare_time_stamps : time_stamp -> time_stamp -> int

(*s Pretty-printing. *)

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
