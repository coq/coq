
(* $Id$ *)

(*i*)
open Pp
(*i*)

(* This module contains numerous utility functions on strings, lists,
   arrays, etc. *)

(*s Errors. [Anomaly] is used for system errors and [UserError] for the
   user's ones. *)

exception Anomaly of string * std_ppcmds
val anomaly : string -> 'a
val anomalylabstrm : string -> std_ppcmds -> 'a

exception UserError of string * std_ppcmds
val error : string -> 'a
val errorlabstrm : string -> std_ppcmds -> 'a

type loc = int * int

val anomaly_loc : loc * string * std_ppcmds -> 'a
val user_err_loc : loc * string * std_ppcmds -> 'a
val invalid_arg_loc : loc * string -> 'a

(*s Strings. *)

val explode : string -> string list
val implode : string list -> string

val parse_loadpath : string -> string list

module Stringset : Set.S with type elt = string

module Stringmap : Map.S with type key = string

val stringmap_to_list : 'a Stringmap.t -> (string * 'a) list 
val stringmap_dom : 'a Stringmap.t -> string list

(*s Lists. *)

val list_add_set : 'a -> 'a list -> 'a list
val list_intersect : 'a list -> 'a list -> 'a list
val list_union : 'a list -> 'a list -> 'a list
val list_unionq : 'a list -> 'a list -> 'a list
val list_subtract : 'a list -> 'a list -> 'a list
val list_subtractq : 'a list -> 'a list -> 'a list
val list_chop : int -> 'a list -> 'a list * 'a list
(* [list_tabulate f n] builds [[f 0; ...; f (n-1)]] *)
val list_tabulate : (int -> 'a) -> int -> 'a list
val list_assign : 'a list -> int -> 'a -> 'a list
val list_distinct : 'a list -> bool
val list_map_i : (int -> 'a -> 'b) -> int -> 'a list -> 'b list
val list_map2_i : 
  (int -> 'a -> 'b -> 'c) -> int -> 'a list -> 'b list -> 'c list
val list_index : 'a -> 'a list -> int
val list_iter_i :  (int -> 'a -> unit) -> 'a list -> unit
val list_fold_left_i :  (int -> 'a -> 'b -> 'a) -> int -> 'a -> 'b list -> 'a
val list_fold_right_and_left :
    ('a -> 'b -> 'b list -> 'a) -> 'b list -> 'a -> 'a
val list_for_all_i : (int -> 'a -> bool) -> int -> 'a list -> bool
val list_except : 'a -> 'a list -> 'a list
val list_for_all2eq : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
val list_sep_last : 'a list -> 'a * 'a list
val list_try_find_i : (int -> 'a -> 'b) -> int -> 'a list -> 'b
val list_uniquize : 'a list -> 'a list
val list_subset : 'a list -> 'a list -> bool
val list_splitby : ('a -> bool) -> 'a list -> 'a list * 'a list
val list_firstn : int -> 'a list -> 'a list
val list_last : 'a list -> 'a
val list_lastn : int -> 'a list -> 'a list
val list_prefix_of : 'a list -> 'a list -> bool
(* [map_append f [x1; ...; xn]] returns [(f x1)@(f x2)@...@(f xn)] *)
val list_map_append : ('a -> 'b list) -> 'a list -> 'b list
(* raises [Invalid_argument] if the two lists don't have the same length *)
val list_map_append2 : ('a -> 'b -> 'c list) -> 'a list -> 'b list -> 'c list
val list_share_tails : 'a list -> 'a list -> 'a list * 'a list * 'a list
val list_join_map : ('a -> 'b list) -> 'a list -> 'b list
val list_try_find : ('a -> 'b) -> 'a list -> 'b

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
val array_map_to_list : ('a -> 'b) -> 'a array -> 'b list
val array_chop : int -> 'a array -> 'a array * 'a array
val array_map2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
val array_map2_i : (int -> 'a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
val array_map3 : 
  ('a -> 'b -> 'c -> 'd) -> 'a array -> 'b array -> 'c array -> 'd array

(*s Matrices *)

val matrix_transpose : 'a list list -> 'a list list

(*s Functions. *)

val compose : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val iterate : ('a -> 'a) -> int -> 'a -> 'a
val repeat : int -> ('a -> unit) -> 'a -> unit

(*s Misc. *)

type ('a,'b) union = Inl of 'a | Inr of 'b

module Intset : Set.S with type elt = int

val intset_exists : (int -> bool) -> Intset.t -> bool

module Intmap : Map.S with type key = int

val intmap_in_dom : int -> 'a Intmap.t -> bool
val intmap_to_list : 'a Intmap.t -> (int * 'a) list
val intmap_inv : 'a Intmap.t -> 'a -> int list

val interval : int -> int -> int list

val in_some : 'a -> 'a option
val out_some : 'a option -> 'a
val option_app : ('a -> 'b) -> 'a option -> 'b option

(* In [map_succeed f l] an element [a] is removed if [f a] raises *)
(* [Failure _] otherwise behaves as [List.map f l] *)

val map_succeed : ('a -> 'b) -> 'a list -> 'b list

(*s Pretty-printing. *)

val pr_spc : unit -> std_ppcmds
val pr_fnl : unit -> std_ppcmds
val pr_int : int -> std_ppcmds
val pr_str : string -> std_ppcmds
val pr_coma : unit -> std_ppcmds

val prlist : ('a -> 'b Stream.t) -> 'a list -> 'b Stream.t
val prvecti : (int -> 'a -> 'b Stream.t) -> 'a array -> 'b Stream.t
val prlist_with_sep :
   (unit -> 'a Stream.t) -> ('b -> 'a Stream.t) -> 'b list -> 'a Stream.t
val prvect_with_sep :
   (unit -> 'a Stream.t) -> ('b -> 'a Stream.t) -> 'b array -> 'a Stream.t
