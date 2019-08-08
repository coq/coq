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

module type GLexerType = Plexing.Lexer
   (** The input signature for the functor [Grammar.GMake]: [te] is the
       type of the tokens. *)

module type S =
  sig
    type te
    type 'c pattern
    type parsable
    val parsable : ?loc:Loc.t -> char Stream.t -> parsable
    val tokens : string -> (string option * int) list
    module Entry :
      sig
        type 'a e
        val create : string -> 'a e
        val parse : 'a e -> parsable -> 'a
        val name : 'a e -> string
        val of_parser : string -> (Plexing.location_function -> te Stream.t -> 'a) -> 'a e
        val parse_token_stream : 'a e -> te Stream.t -> 'a
        val print : Format.formatter -> 'a e -> unit
      end
    type ty_norec = TyNoRec
    type ty_mayrec = TyMayRec
    type ('self, 'trec, 'a) ty_symbol
    type ('self, 'trec, 'f, 'r) ty_rule
    type 'a ty_rules
    type 'a ty_production
    val s_nterm : 'a Entry.e -> ('self, ty_norec, 'a) ty_symbol
    val s_nterml : 'a Entry.e -> string -> ('self, ty_norec, 'a) ty_symbol
    val s_list0 : ('self, 'trec, 'a) ty_symbol -> ('self, 'trec, 'a list) ty_symbol
    val s_list0sep :
      ('self, 'trec, 'a) ty_symbol -> ('self, ty_norec, 'b) ty_symbol -> bool ->
        ('self, 'trec, 'a list) ty_symbol
    val s_list1 : ('self, 'trec, 'a) ty_symbol -> ('self, 'trec, 'a list) ty_symbol
    val s_list1sep :
      ('self, 'trec, 'a) ty_symbol -> ('self, ty_norec, 'b) ty_symbol -> bool ->
        ('self, 'trec, 'a list) ty_symbol
    val s_opt : ('self, 'trec, 'a) ty_symbol -> ('self, 'trec, 'a option) ty_symbol
    val s_self : ('self, ty_mayrec, 'self) ty_symbol
    val s_next : ('self, ty_mayrec, 'self) ty_symbol
    val s_token : 'c pattern -> ('self, ty_norec, 'c) ty_symbol
    val s_rules : warning:(string -> unit) option -> 'a ty_rules list -> ('self, ty_norec, 'a) ty_symbol

    val r_stop : ('self, ty_norec, 'r, 'r) ty_rule
    val r_next :
      ('self, _, 'a, 'r) ty_rule -> ('self, _, 'b) ty_symbol ->
        ('self, ty_mayrec, 'b -> 'a, 'r) ty_rule
    val r_next_norec :
      ('self, ty_norec, 'a, 'r) ty_rule -> ('self, ty_norec, 'b) ty_symbol ->
        ('self, ty_norec, 'b -> 'a, 'r) ty_rule
    val rules : (_, ty_norec, 'f, Loc.t -> 'a) ty_rule * 'f -> 'a ty_rules
    val production : ('a, _, 'f, Loc.t -> 'a) ty_rule * 'f -> 'a ty_production

    module Unsafe :
      sig
        val clear_entry : 'a Entry.e -> unit
      end
    val safe_extend : warning:(string -> unit) option ->
      'a Entry.e -> Gramext.position option ->
        (string option * Gramext.g_assoc option * 'a ty_production list)
          list ->
        unit
    val safe_delete_rule : 'a Entry.e -> ('a, _, 'f, 'r) ty_rule -> unit
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

module GMake (L : GLexerType) :
  S with type te = L.te and type 'c pattern = 'c L.pattern
