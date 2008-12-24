(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

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

(* [todo] is for running of an incomplete code its implementation is
   "do nothing" (or print a message), but this function should not be
   used in a released code *)

val todo : string -> unit

type loc = Compat.loc

type 'a located = loc * 'a

val unloc : loc -> int * int
val make_loc : int * int -> loc
val dummy_loc : loc
val anomaly_loc : loc * string * std_ppcmds -> 'a
val user_err_loc : loc * string * std_ppcmds -> 'a
val invalid_arg_loc : loc * string -> 'a
val join_loc : loc -> loc -> loc
val located_fold_left : ('a -> 'b -> 'a) -> 'a -> 'b located -> 'a
val located_iter2 : ('a -> 'b -> unit) -> 'a located -> 'b located -> unit

(* Like [Exc_located], but specifies the outermost file read, the
   input buffer associated to the location of the error (or the module name
   if boolean is true), and the error itself. *)

exception Error_in_file of string * (bool * string * loc) * exn

(* Mapping under pairs *)

val on_fst : ('a -> 'b) -> 'a * 'c -> 'b * 'c
val on_snd : ('a -> 'b) -> 'c * 'a -> 'c * 'b

(*s Projections from triplets *)

val pi1 : 'a * 'b * 'c -> 'a
val pi2 : 'a * 'b * 'c -> 'b
val pi3 : 'a * 'b * 'c -> 'c

(*s Chars. *)

val is_letter : char -> bool
val is_digit : char -> bool
val is_ident_tail : char -> bool

(*s Strings. *)

val explode : string -> string list
val implode : string list -> string
val string_index_from : string -> int -> string -> int
val string_string_contains : where:string -> what:string -> bool
val plural : int -> string -> string
val ordinal : int -> string

val parse_loadpath : string -> string list

module Stringset : Set.S with type elt = string
module Stringmap : Map.S with type key = string

type utf8_status = UnicodeLetter | UnicodeIdentPart | UnicodeSymbol

exception UnsupportedUtf8

val classify_unicode : int -> utf8_status
val check_ident : string -> unit
val check_ident_soft : string -> unit
val lowercase_first_char_utf8 : string -> string

(*s Lists. *)

val list_add_set : 'a -> 'a list -> 'a list
val list_eq_set : 'a list -> 'a list -> bool
val list_intersect : 'a list -> 'a list -> 'a list
val list_union : 'a list -> 'a list -> 'a list
val list_unionq : 'a list -> 'a list -> 'a list
val list_subtract : 'a list -> 'a list -> 'a list
val list_subtractq : 'a list -> 'a list -> 'a list
val list_chop : int -> 'a list -> 'a list * 'a list
(* [list_tabulate f n] builds [[f 0; ...; f (n-1)]] *)
val list_tabulate : (int -> 'a) -> int -> 'a list
val list_make : int -> 'a -> 'a list
val list_assign : 'a list -> int -> 'a -> 'a list
val list_distinct : 'a list -> bool
val list_duplicates : 'a list -> 'a list
val list_filter2 : ('a -> 'b -> bool) -> 'a list * 'b list -> 'a list * 'b list
val list_map_filter : ('a -> 'b option) -> 'a list -> 'b list
(* [list_smartmap f [a1...an] = List.map f [a1...an]] but if for all i
   [ f ai == ai], then [list_smartmap f l==l] *)
val list_smartmap : ('a -> 'a) -> 'a list -> 'a list
val list_map_left : ('a -> 'b) -> 'a list -> 'b list
val list_map_i : (int -> 'a -> 'b) -> int -> 'a list -> 'b list
val list_map2_i : 
  (int -> 'a -> 'b -> 'c) -> int -> 'a list -> 'b list -> 'c list
val list_map3 :
  ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list
val list_map4 :
  ('a -> 'b -> 'c -> 'd -> 'e) -> 'a list -> 'b list -> 'c list -> 'd list -> 'e list
(* [list_index] returns the 1st index of an element in a list (counting from 1) *)
val list_index : 'a -> 'a list -> int
(* [list_unique_index x l] returns [Not_found] if [x] doesn't occur exactly once *)
val list_unique_index : 'a -> 'a list -> int 
(* [list_index0] behaves as [list_index] except that it starts counting at 0 *)
val list_index0 : 'a -> 'a list -> int
val list_iter3 : ('a -> 'b -> 'c -> unit) -> 'a list -> 'b list -> 'c list -> unit
val list_iter_i :  (int -> 'a -> unit) -> 'a list -> unit
val list_fold_right_i :  (int -> 'a -> 'b -> 'b) -> int -> 'a list -> 'b -> 'b
val list_fold_left_i :  (int -> 'a -> 'b -> 'a) -> int -> 'a -> 'b list -> 'a
val list_fold_right_and_left :
    ('a -> 'b -> 'b list -> 'a) -> 'b list -> 'a -> 'a
val list_fold_left3 : ('a -> 'b -> 'c -> 'd -> 'a) -> 'a -> 'b list -> 'c list -> 'd list -> 'a
val list_for_all_i : (int -> 'a -> bool) -> int -> 'a list -> bool
val list_except : 'a -> 'a list -> 'a list
val list_remove : 'a -> 'a list -> 'a list
val list_remove_first : 'a -> 'a list -> 'a list
val list_remove_assoc_in_triple : 'a -> ('a * 'b * 'c) list -> ('a * 'b * 'c) list
val list_for_all2eq : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
val list_sep_last : 'a list -> 'a * 'a list
val list_try_find_i : (int -> 'a -> 'b) -> int -> 'a list -> 'b
val list_try_find : ('a -> 'b) -> 'a list -> 'b
val list_uniquize : 'a list -> 'a list
(* merges two sorted lists and preserves the uniqueness property: *)
val list_merge_uniq : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list
val list_subset : 'a list -> 'a list -> bool
val list_split_at : ('a -> bool) -> 'a list -> 'a list * 'a list
val list_split_by : ('a -> bool) -> 'a list -> 'a list * 'a list
val list_split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
val list_partition_by : ('a -> 'a -> bool) -> 'a list -> 'a list list
val list_firstn : int -> 'a list -> 'a list
val list_last : 'a list -> 'a
val list_lastn : int -> 'a list -> 'a list
val list_skipn : int -> 'a list -> 'a list 
val list_addn : int -> 'a -> 'a list -> 'a list
val list_prefix_of : 'a list -> 'a list -> bool
val list_drop_prefix : 'a list -> 'a list -> 'a list
val list_drop_last : 'a list -> 'a list
(* [map_append f [x1; ...; xn]] returns [(f x1)@(f x2)@...@(f xn)] *)
val list_map_append : ('a -> 'b list) -> 'a list -> 'b list
val list_join_map : ('a -> 'b list) -> 'a list -> 'b list
(* raises [Invalid_argument] if the two lists don't have the same length *)
val list_map_append2 : ('a -> 'b -> 'c list) -> 'a list -> 'b list -> 'c list
val list_share_tails : 'a list -> 'a list -> 'a list * 'a list * 'a list
(* [list_fold_map f e_0 [l_1...l_n] = e_n,[k_1...k_n]]
   where [(e_i,k_i)=f e_{i-1} l_i] *)
val list_fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
val list_fold_map' : ('b -> 'a -> 'c * 'a) -> 'b list -> 'a -> 'c list * 'a
val list_map_assoc : ('a -> 'b) -> ('c * 'a) list -> ('c * 'b) list
(* A generic cartesian product: for any operator (**), 
   [list_cartesian (**) [x1;x2] [y1;y2] = [x1**y1; x1**y2; x2**y1; x2**y1]], 
   and so on if there are more elements in the lists. *)
val list_cartesian : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
(* [list_cartesians] is an n-ary cartesian product: it iterates 
   [list_cartesian] over a list of lists.  *)
val list_cartesians : ('a -> 'b -> 'b) -> 'b -> 'a list list -> 'b list
(* list_combinations [[a;b];[c;d]] returns [[a;c];[a;d];[b;c];[b;d]] *)
val list_combinations : 'a list list -> 'a list list
(* Keep only those products that do not return None *)
val list_cartesian_filter :
  ('a -> 'b -> 'c option) -> 'a list -> 'b list -> 'c list
val list_cartesians_filter :
  ('a -> 'b -> 'b option) -> 'b -> 'a list list -> 'b list

val list_union_map : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b

(*s Arrays. *)

val array_exists : ('a -> bool) -> 'a array -> bool
val array_for_all : ('a -> bool) -> 'a array -> bool
val array_for_all2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool
val array_for_all3 : ('a -> 'b -> 'c -> bool) ->
  'a array -> 'b array -> 'c array -> bool
val array_for_all4 : ('a -> 'b -> 'c -> 'd -> bool) ->
  'a array -> 'b array -> 'c array -> 'd array -> bool
val array_hd : 'a array -> 'a
val array_tl : 'a array -> 'a array
val array_last : 'a array -> 'a
val array_cons : 'a -> 'a array -> 'a array
val array_rev : 'a array -> unit
val array_fold_right_i : 
  (int -> 'b -> 'a -> 'a) -> 'b array -> 'a -> 'a
val array_fold_left_i : (int -> 'a -> 'b -> 'a) -> 'a -> 'b array -> 'a
val array_fold_right2 :
  ('a -> 'b -> 'c -> 'c) -> 'a array -> 'b array -> 'c -> 'c
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
val array_smartmap : ('a -> 'a) -> 'a array -> 'a array
val array_map2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
val array_map2_i : (int -> 'a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
val array_map3 : 
  ('a -> 'b -> 'c -> 'd) -> 'a array -> 'b array -> 'c array -> 'd array
val array_map_left : ('a -> 'b) -> 'a array -> 'b array
val array_map_left_pair : ('a -> 'b) -> 'a array -> ('c -> 'd) -> 'c array ->
  'b array * 'd array
val array_iter2 : ('a -> 'b -> unit) -> 'a array -> 'b array -> unit
val array_fold_map' : ('a -> 'c -> 'b * 'c) -> 'a array -> 'c -> 'b array * 'c
val array_fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b array -> 'a * 'c array
val array_fold_map2' :
  ('a -> 'b -> 'c -> 'd * 'c) -> 'a array -> 'b array -> 'c -> 'd array * 'c
val array_distinct : 'a array -> bool
val array_union_map : ('a -> 'b -> 'b) -> 'a array -> 'b -> 'b

(*s Matrices *)

val matrix_transpose : 'a list list -> 'a list list

(*s Functions. *)

val identity : 'a -> 'a
val compose : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val iterate : ('a -> 'a) -> int -> 'a -> 'a
val repeat : int -> ('a -> unit) -> 'a -> unit
val iterate_for : int -> int -> (int -> 'a -> 'a) -> 'a -> 'a

(*s Misc. *)

type ('a,'b) union = Inl of 'a | Inr of 'b

module Intset : Set.S with type elt = int

module Intmap : Map.S with type key = int

val intmap_in_dom : int -> 'a Intmap.t -> bool
val intmap_to_list : 'a Intmap.t -> (int * 'a) list
val intmap_inv : 'a Intmap.t -> 'a -> int list

val interval : int -> int -> int list


(* In [map_succeed f l] an element [a] is removed if [f a] raises *)
(* [Failure _] otherwise behaves as [List.map f l] *)

val map_succeed : ('a -> 'b) -> 'a list -> 'b list

(*s Pretty-printing. *)

val pr_spc : unit -> std_ppcmds
val pr_fnl : unit -> std_ppcmds
val pr_int : int -> std_ppcmds
val pr_str : string -> std_ppcmds
val pr_coma : unit -> std_ppcmds
val pr_semicolon : unit -> std_ppcmds
val pr_bar : unit -> std_ppcmds
val pr_arg : ('a -> std_ppcmds) -> 'a -> std_ppcmds
val pr_opt : ('a -> std_ppcmds) -> 'a option -> std_ppcmds
val pr_opt_no_spc : ('a -> std_ppcmds) -> 'a option -> std_ppcmds
val nth : int -> std_ppcmds

val prlist : ('a -> std_ppcmds) -> 'a list -> std_ppcmds
(* unlike all other functions below, [prlist] works lazily.
   if a strict behavior is needed, use [prlist_strict] instead. *)
val prlist_strict :  ('a -> std_ppcmds) -> 'a list -> std_ppcmds
val prlist_with_sep :
   (unit -> std_ppcmds) -> ('b -> std_ppcmds) -> 'b list -> std_ppcmds
val prvect : ('a -> std_ppcmds) -> 'a array -> std_ppcmds
val prvecti : (int -> 'a -> std_ppcmds) -> 'a array -> std_ppcmds
val prvect_with_sep :
   (unit -> std_ppcmds) -> ('b -> std_ppcmds) -> 'b array -> std_ppcmds
val pr_vertical_list : ('b -> std_ppcmds) -> 'b list -> std_ppcmds
val pr_enum : ('a -> std_ppcmds) -> 'a list -> std_ppcmds
val pr_located : ('a -> std_ppcmds) -> 'a located -> std_ppcmds
val pr_sequence : ('a -> std_ppcmds) -> 'a list -> std_ppcmds
val surround : std_ppcmds -> std_ppcmds


(*s Size of an ocaml value (in words, bytes and kilobytes). *)

val size_w : 'a -> int
val size_b : 'a -> int
val size_kb : 'a -> int

(*s Total size of the allocated ocaml heap. *)

val heap_size : unit -> int
val heap_size_kb : unit -> int

(*s Coq interruption: set the following boolean reference to interrupt Coq
    (it eventually raises [Break], simulating a Ctrl-C) *)

val interrupt : bool ref
val check_for_interrupt : unit -> unit
