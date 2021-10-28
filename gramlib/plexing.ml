(* camlp5r *)
(* plexing.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

type 'te lexer_func = ?loc:Loc.t -> char Stream.t -> 'te LStream.t

module type S = sig
  type te
  type 'c pattern
  val tok_pattern_eq : 'a pattern -> 'b pattern -> ('a, 'b) Util.eq option
  val tok_pattern_strings : 'c pattern -> string * string option
  val tok_func : te lexer_func
  val tok_using : 'c pattern -> unit
  val tok_removing : 'c pattern -> unit
  val tok_match : 'c pattern -> te -> 'c
  val tok_text : 'c pattern -> string

  (* State for the comments, at some point we should make it functional *)
  module State : sig
    type t
    val init : unit -> t
    val set : t -> unit
    val get : unit -> t
    val drop : unit -> unit
    val get_comments : t -> ((int * int) * string) list
  end

end
