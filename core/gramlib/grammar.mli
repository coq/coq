(* camlp5r *)
(* grammar.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Extensible grammars.

    This module implements the Camlp5 extensible grammars system.
    Grammars entries can be extended using the [EXTEND] statement,
    added by loading the Camlp5 [pa_extend.cmo] file. *)

(** {6 Functorial interface} *)

   (** Alternative for grammars use. Grammars are no more Ocaml values:
       there is no type for them. Modules generated preserve the
       rule "an entry cannot call an entry of another grammar" by
       normal OCaml typing. *)

(** The input signature for the functor [Grammar.GMake]: [te] is the
       type of the tokens. *)

type norec
type mayrec

module type S = sig
  type te
  type 'c pattern
  type ty_pattern = TPattern : 'a pattern -> ty_pattern

  module Parsable : sig
    type t
    val make : ?loc:Loc.t -> char Stream.t -> t
    val comments : t -> ((int * int) * string) list
  end

  module Entry : sig
    type 'a t
    val make : string -> 'a t
    val create : string -> 'a t (* compat *)
    val parse : 'a t -> Parsable.t -> 'a
    val name : 'a t -> string
    type 'a parser_fun = { parser_fun : te LStream.t -> 'a }
    val of_parser : string -> 'a parser_fun -> 'a t
    val parse_token_stream : 'a t -> te LStream.t -> 'a
    val print : Format.formatter -> 'a t -> unit
    val is_empty : 'a t -> bool
  end

  module rec Symbol : sig

    type ('self, 'trec, 'a) t
    val nterm : 'a Entry.t -> ('self, norec, 'a) t
    val nterml : 'a Entry.t -> string -> ('self, norec, 'a) t
    val list0 : ('self, 'trec, 'a) t -> ('self, 'trec, 'a list) t
    val list0sep :
      ('self, 'trec, 'a) t -> ('self, norec, unit) t -> bool ->
      ('self, 'trec, 'a list) t
    val list1 : ('self, 'trec, 'a) t -> ('self, 'trec, 'a list) t
    val list1sep :
      ('self, 'trec, 'a) t -> ('self, norec, unit) t -> bool ->
      ('self, 'trec, 'a list) t
    val opt : ('self, 'trec, 'a) t -> ('self, 'trec, 'a option) t
    val self : ('self, mayrec, 'self) t
    val next : ('self, mayrec, 'self) t
    val token : 'c pattern -> ('self, norec, 'c) t
    val tokens : ty_pattern list -> ('self, norec, unit) t
    val rules : 'a Rules.t list -> ('self, norec, 'a) t

  end and Rule : sig

    type ('self, 'trec, 'f, 'r) t

    val stop : ('self, norec, 'r, 'r) t
    val next :
      ('self, _, 'a, 'r) t -> ('self, _, 'b) Symbol.t ->
      ('self, mayrec, 'b -> 'a, 'r) t
    val next_norec :
      ('self, norec, 'a, 'r) Rule.t -> ('self, norec, 'b) Symbol.t ->
      ('self, norec, 'b -> 'a, 'r) t

  end and Rules : sig

    type 'a t
    val make : (_, norec, 'f, Loc.t -> 'a) Rule.t -> 'f -> 'a t

  end

  module Production : sig
    type 'a t
    val make : ('a, _, 'f, Loc.t -> 'a) Rule.t -> 'f -> 'a t
  end

  type 'a single_extend_statement =
    string option * Gramext.g_assoc option * 'a Production.t list

  type 'a extend_statement =
  | Reuse of string option * 'a Production.t list
    (** Extend an existing level by its optional given name. If None, picks the topmost level. *)
  | Fresh of Gramext.position * 'a single_extend_statement list
    (** Create a level at the given position. *)

  val generalize_symbol : ('a, 'tr, 'c) Symbol.t -> ('a, norec, 'c) Symbol.t option

  (* Used in custom entries, should tweak? *)
  val level_of_nonterm : ('a, norec, 'c) Symbol.t -> string option

end

(* Interface private to clients  *)
module type ExtS = sig

  include S

  val safe_extend : 'a Entry.t -> 'a extend_statement -> unit
  val safe_delete_rule : 'a Entry.t -> 'a Production.t -> unit

  module Unsafe : sig
    val clear_entry : 'a Entry.t -> unit
  end

end

(** Signature type of the functor [Grammar.GMake]. The types and
    functions are almost the same than in generic interface, but:
    -      Grammars are not values. Functions holding a grammar as parameter
      do not have this parameter yet.
    -      The type [parsable] is used in function [parse] instead of
      the char stream, avoiding the possible loss of tokens.
    -      The type of tokens (expressions and patterns) can be any
      type (instead of (string * string)); the module parameter
      must specify a way to show them as (string * string) *)

module GMake (L : Plexing.S) : ExtS with type te = L.te and type 'c pattern = 'c L.pattern
