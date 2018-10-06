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

exception Cut;

(** Functional streams *)

type t 'a = 'x;
    (* The type of 'a functional streams *)
value from : (int -> option 'a) -> t 'a;
    (* [Fstream.from f] returns a stream built from the function [f].
       To create a new stream element, the function [f] is called with
       the current stream count. The user function [f] must return either
       [Some <value>] for a value or [None] to specify the end of the
       stream. *)

value of_list : list 'a -> t 'a;
    (* Return the stream holding the elements of the list in the same
       order. *)
value of_string : string -> t char;
    (* Return the stream of the characters of the string parameter. *)
value of_channel : in_channel -> t char;
    (* Return the stream of the characters read from the input channel. *)

value iter : ('a -> unit) -> t 'a -> unit;
    (* [Fstream.iter f s] scans the whole stream s, applying function [f]
       in turn to each stream element encountered. *)

value next : t 'a -> option ('a * t 'a);
    (* Return [Some (a, s)] where [a] is the first element of the stream
       and [s] the remaining stream, or [None] if the stream is empty. *)
value empty : t 'a -> option (unit * t 'a);
    (* Return [Some ((), s)] if the stream is empty where [s] is itself,
       else [None] *)
value count : t 'a -> int;
    (* Return the current count of the stream elements, i.e. the number
       of the stream elements discarded. *)
value count_unfrozen : t 'a -> int;
    (* Return the number of unfrozen elements in the beginning of the
       stream; useful to determine the position of a parsing error (longuest
       path). *)

(** Backtracking parsers *)

type kont 'a 'b = [ K of unit -> option ('b * t 'a * kont 'a 'b) ];
    (* The type of continuation of a backtracking parser. *)
type bp 'a 'b = t 'a -> option ('b * t 'a * kont 'a 'b);
    (* The type of a backtracking parser. *)

value bcontinue : kont 'a 'b -> option ('b * t 'a * kont 'a 'b);
   (* [bcontinue k] return the next solution of a backtracking parser. *)

value bparse_all : bp 'a 'b -> t 'a -> list 'b;
    (* [bparse_all p strm] return the list of all solutions of a
       backtracking parser applied to a functional stream. *)

(*--*)

value nil : t 'a;
type data 'a = 'x;
value cons : 'a -> t 'a -> data 'a;
value app : t 'a -> t 'a -> data 'a;
value flazy : (unit -> data 'a) -> t 'a;

value b_seq : bp 'a 'b -> ('b -> bp 'a 'c) -> bp 'a 'c;
value b_or : bp 'a 'b -> bp 'a 'b -> bp 'a 'b;
value b_term : ('a -> option 'b) -> bp 'a 'b;
value b_act : 'b -> bp 'a 'b;
