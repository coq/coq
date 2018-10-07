(* camlp5r *)
(* fstream.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* Module [Fstream]: functional streams *)

(* This module implement functional streams and parsers together with
   backtracking parsers. To be used with syntax [pa_fstream.cmo]. The
   syntax is:
   For functional streams:
-     stream: [fstream [: ... :]]
   For functional parsers:
-     parser: [fparser [ [: ... :] -> ... | ... ]]
   For backtracking parsers:
-     parser: [bparser [ [: ... :] -> ... | ... ]]

   Functional parsers are of type:
     [Fstream.t 'a -> option ('b * Fstream.t 'a)]
   Backtracking parsers are of type:
     [Fstream.t 'a -> option ('b * Fstream.t 'a * Fstream.kont 'a 'b)]

   Functional parsers have limited backtrack, i.e if a rule fails, the
   next rule is tested with the initial stream; limited because when
   in case of a rule with two consecutive symbols [a] and [b], if [b]
   fails, the rule fails: there is no try with the next rule of [a].

   Backtracking parsers have full backtrack. If a rule fails, the next
   case of the previous rule is tested.
*)

exception Cut

(** Functional streams *)

type 'a t
    (* The type of 'a functional streams *)
val from : (int -> 'a option) -> 'a t
    (* [Fstream.from f] returns a stream built from the function [f].
       To create a new stream element, the function [f] is called with
       the current stream count. The user function [f] must return either
       [Some <value>] for a value or [None] to specify the end of the
       stream. *)

val of_list : 'a list -> 'a t
    (* Return the stream holding the elements of the list in the same
       order. *)
val of_string : string -> char t
    (* Return the stream of the characters of the string parameter. *)
val of_channel : in_channel -> char t
    (* Return the stream of the characters read from the input channel. *)

val iter : ('a -> unit) -> 'a t -> unit
    (* [Fstream.iter f s] scans the whole stream s, applying function [f]
       in turn to each stream element encountered. *)

val next : 'a t -> ('a * 'a t) option
    (* Return [Some (a, s)] where [a] is the first element of the stream
       and [s] the remaining stream, or [None] if the stream is empty. *)
val empty : 'a t -> (unit * 'a t) option
    (* Return [Some ((), s)] if the stream is empty where [s] is itself,
       else [None] *)
val count : 'a t -> int
    (* Return the current count of the stream elements, i.e. the number
       of the stream elements discarded. *)
val count_unfrozen : 'a t -> int
    (* Return the number of unfrozen elements in the beginning of the
       stream; useful to determine the position of a parsing error (longuest
       path). *)

(** Backtracking parsers *)

type ('a, 'b) kont =
    K of (unit -> ('b * 'a t * ('a, 'b) kont) option)
    (* The type of continuation of a backtracking parser. *)
type ('a, 'b) bp = 'a t -> ('b * 'a t * ('a, 'b) kont) option
    (* The type of a backtracking parser. *)

val bcontinue : ('a, 'b) kont -> ('b * 'a t * ('a, 'b) kont) option
   (* [bcontinue k] return the next solution of a backtracking parser. *)

val bparse_all : ('a, 'b) bp -> 'a t -> 'b list
    (* [bparse_all p strm] return the list of all solutions of a
       backtracking parser applied to a functional stream. *)

(*--*)

val nil : 'a t
type 'a data
val cons : 'a -> 'a t -> 'a data
val app : 'a t -> 'a t -> 'a data
val flazy : (unit -> 'a data) -> 'a t

val b_seq : ('a, 'b) bp -> ('b -> ('a, 'c) bp) -> ('a, 'c) bp
val b_or : ('a, 'b) bp -> ('a, 'b) bp -> ('a, 'b) bp
val b_term : ('a -> 'b option) -> ('a, 'b) bp
val b_act : 'b -> ('a, 'b) bp
