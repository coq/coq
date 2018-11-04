(* camlp5r *)
(* grammar.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Extensible grammars.

    This module implements the Camlp5 extensible grammars system.
    Grammars entries can be extended using the [EXTEND] statement,
    added by loading the Camlp5 [pa_extend.cmo] file. *)

type g
   (** The type for grammars, holding entries. *)
type token = string * string

type parsable
val parsable : g -> char Stream.t -> parsable
   (** Type and value allowing to keep the same token stream between
       several calls of entries of the same grammar, to prevent possible
       loss of tokens. To be used with [Entry.parse_parsable] below *)

module Entry :
  sig
    type 'a e
    val create : g -> string -> 'a e
    val parse : 'a e -> char Stream.t -> 'a
    val parse_all : 'a e -> char Stream.t -> 'a list
    val parse_parsable : 'a e -> parsable -> 'a
    val name : 'a e -> string
    val of_parser : g -> string -> (token Stream.t -> 'a) -> 'a e
    val parse_token_stream : 'a e -> token Stream.t -> 'a
    val print : Format.formatter -> 'a e -> unit
    val find : 'a e -> string -> Obj.t e
    external obj : 'a e -> token Gramext.g_entry = "%identity"
    val parse_token : 'a e -> token Stream.t -> 'a
  end
   (** Module to handle entries.
-      [Entry.e] is the type for entries returning values of type ['a].
-      [Entry.create g n] creates a new entry named [n] in the grammar [g].
-      [Entry.parse e] returns the stream parser of the entry [e].
-      [Entry.parse_all e] returns the stream parser returning all possible
          values while parsing with the entry [e]: may return more than one
          value when the parsing algorithm is [Backtracking]
-      [Entry.parse_all e] returns the parser returning all possible values.
-      [Entry.parse_parsable e] returns the parsable parser of the entry [e].
-      [Entry.name e] returns the name of the entry [e].
-      [Entry.of_parser g n p] makes an entry from a token stream parser.
-      [Entry.parse_token_stream e] returns the token stream parser of the
          entry [e].
-      [Entry.print e] displays the entry [e] using [Format].
-      [Entry.find e s] finds the entry named [s] in the rules of [e].
-      [Entry.obj e] converts an entry into a [Gramext.g_entry] allowing
          to see what it holds.
-      [Entry.parse_token]: deprecated since 2017-06-16; old name for
          [Entry.parse_token_stream] *)

type ('self, 'a) ty_symbol
(** Type of grammar symbols. A type-safe wrapper around Gramext.symbol. The
    first type argument is the type of the ambient entry, the second one is the
    type of the produced value. *)

type ('self, 'f, 'r) ty_rule

type 'a ty_production

(** {6 Clearing grammars and entries} *)

module Unsafe :
  sig
    val gram_reinit : g -> token Plexing.lexer -> unit
    val clear_entry : 'a Entry.e -> unit
  end
   (** Module for clearing grammars and entries. To be manipulated with
       care, because: 1) reinitializing a grammar destroys all tokens
       and there may have problems with the associated lexer if there
       are keywords; 2) clearing an entry does not destroy the tokens
       used only by itself.
-      [Unsafe.reinit_gram g lex] removes the tokens of the grammar
-      and sets [lex] as a new lexer for [g]. Warning: the lexer
-      itself is not reinitialized.
-      [Unsafe.clear_entry e] removes all rules of the entry [e]. *)

(** {6 Functorial interface} *)

   (** Alternative for grammars use. Grammars are no more Ocaml values:
       there is no type for them. Modules generated preserve the
       rule "an entry cannot call an entry of another grammar" by
       normal OCaml typing. *)

module type GLexerType = sig type te val lexer : te Plexing.lexer end
   (** The input signature for the functor [Grammar.GMake]: [te] is the
       type of the tokens. *)

module type S =
  sig
    type te
    type parsable
    val parsable : char Stream.t -> parsable
    val tokens : string -> (string * int) list
    val glexer : te Plexing.lexer
    module Entry :
      sig
        type 'a e
        val create : string -> 'a e
        val parse : 'a e -> parsable -> 'a
        val name : 'a e -> string
        val of_parser : string -> (te Stream.t -> 'a) -> 'a e
        val parse_token_stream : 'a e -> te Stream.t -> 'a
        val print : Format.formatter -> 'a e -> unit
        external obj : 'a e -> te Gramext.g_entry = "%identity"
        val parse_token : 'a e -> te Stream.t -> 'a
      end
    type ('self, 'a) ty_symbol
    type ('self, 'f, 'r) ty_rule
    type 'a ty_production
    val s_nterm : 'a Entry.e -> ('self, 'a) ty_symbol
    val s_nterml : 'a Entry.e -> string -> ('self, 'a) ty_symbol
    val s_list0 : ('self, 'a) ty_symbol -> ('self, 'a list) ty_symbol
    val s_list0sep :
      ('self, 'a) ty_symbol -> ('self, 'b) ty_symbol -> bool ->
        ('self, 'a list) ty_symbol
    val s_list1 : ('self, 'a) ty_symbol -> ('self, 'a list) ty_symbol
    val s_list1sep :
      ('self, 'a) ty_symbol -> ('self, 'b) ty_symbol -> bool ->
        ('self, 'a list) ty_symbol
    val s_opt : ('self, 'a) ty_symbol -> ('self, 'a option) ty_symbol
    val s_flag : ('self, 'a) ty_symbol -> ('self, bool) ty_symbol
    val s_self : ('self, 'self) ty_symbol
    val s_next : ('self, 'self) ty_symbol
    val s_token : Plexing.pattern -> ('self, string) ty_symbol
    val s_rules : 'a ty_production list -> ('self, 'a) ty_symbol
    val r_stop : ('self, 'r, 'r) ty_rule
    val r_next :
      ('self, 'a, 'r) ty_rule -> ('self, 'b) ty_symbol ->
        ('self, 'b -> 'a, 'r) ty_rule
    val r_cut : ('self, 'a, 'r) ty_rule -> ('self, 'a, 'r) ty_rule
    val production : ('a, 'f, Ploc.t -> 'a) ty_rule * 'f -> 'a ty_production

    module Unsafe :
      sig
        val gram_reinit : te Plexing.lexer -> unit
        val clear_entry : 'a Entry.e -> unit
      end
    val extend :
      'a Entry.e -> Gramext.position option ->
        (string option * Gramext.g_assoc option *
           (te Gramext.g_symbol list * Gramext.g_action) list)
          list ->
        unit
    val safe_extend :
      'a Entry.e -> Gramext.position option ->
        (string option * Gramext.g_assoc option * 'a ty_production list)
          list ->
        unit
    val delete_rule : 'a Entry.e -> te Gramext.g_symbol list -> unit
    val safe_delete_rule : 'a Entry.e -> ('a, 'f, 'r) ty_rule -> unit
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

module GMake (L : GLexerType) : S with type te = L.te
