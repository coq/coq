(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Compatibility file depending on ocaml/camlp4 version *)

(** Locations *)

IFDEF CAMLP5 THEN

module CompatLoc = struct
  include Ploc
  let ghost = dummy
  let merge = encl
end

exception Exc_located = Ploc.Exc

let to_coqloc loc =
  Loc.create (Ploc.file_name loc) (Ploc.line_nb loc)
    (Ploc.bol_pos loc) (Ploc.first_pos loc, Ploc.last_pos loc)

let make_loc = Ploc.make_unlined

ELSE

module CompatLoc = Camlp4.PreCast.Loc

exception Exc_located = CompatLoc.Exc_located

let to_coqloc loc =
  Loc.create (CompatLoc.file_name loc) (CompatLoc.start_line loc)
    (CompatLoc.start_bol loc) (CompatLoc.start_off loc, CompatLoc.stop_off loc)

let make_loc (start, stop) =
  CompatLoc.of_tuple ("", 0, 0, start, 0, 0, stop, false)

END

let (!@) = to_coqloc

(** Misc module emulation *)

IFDEF CAMLP5 THEN

module PcamlSig = struct end
module Token = Token
module CompatGramext = struct include Gramext type assoc = g_assoc end

ELSE

module PcamlSig = Camlp4.Sig
module Ast = Camlp4.PreCast.Ast
module Pcaml = Camlp4.PreCast.Syntax
module MLast = Ast
module Token = struct exception Error of string end
module CompatGramext = Camlp4.Sig.Grammar

END

(** Signature of CLexer *)

IFDEF CAMLP5 THEN

module type LexerSig = sig
  include Grammar.GLexerType with type te = Tok.t
  module Error : sig
    type t
    exception E of t
    val to_string : t -> string
  end
end

ELSE

module type LexerSig =
  Camlp4.Sig.Lexer with module Loc = CompatLoc and type Token.t = Tok.t

END

(** Signature and implementation of grammars *)

IFDEF CAMLP5 THEN

module type GrammarSig = sig
  include Grammar.S with type te = Tok.t
  type 'a entry = 'a Entry.e
  type internal_entry = Tok.t Gramext.g_entry
  type symbol = Tok.t Gramext.g_symbol
  type action = Gramext.g_action
  type production_rule = symbol list * action
  type single_extend_statment =
      string option * Gramext.g_assoc option * production_rule list
  type extend_statment =
      Gramext.position option * single_extend_statment list
  val action : 'a -> action
  val entry_create : string -> 'a entry
  val entry_parse : 'a entry -> parsable -> 'a
  val entry_print : Format.formatter -> 'a entry -> unit
  val srules' : production_rule list -> symbol
  val parse_tokens_after_filter : 'a entry -> Tok.t Stream.t -> 'a
end

module GrammarMake (L:LexerSig) : GrammarSig = struct
  include Grammar.GMake (L)
  type 'a entry = 'a Entry.e
  type internal_entry = Tok.t Gramext.g_entry
  type symbol = Tok.t Gramext.g_symbol
  type action = Gramext.g_action
  type production_rule = symbol list * action
  type single_extend_statment =
      string option * Gramext.g_assoc option * production_rule list
  type extend_statment =
      Gramext.position option * single_extend_statment list
  let action = Gramext.action
  let entry_create = Entry.create
  let entry_parse e p =
    try Entry.parse e p
    with Exc_located (loc,e) ->
      let loc' = Loc.get_loc (Exninfo.info e) in
      let loc = match loc' with None -> to_coqloc loc | Some loc -> loc in
      Loc.raise loc e

  let entry_print ft x = Entry.print ft x
  let srules' = Gramext.srules
  let parse_tokens_after_filter = Entry.parse_token
end

ELSE

module type GrammarSig = sig
  include Camlp4.Sig.Grammar.Static
    with module Loc = CompatLoc and type Token.t = Tok.t
  type 'a entry = 'a Entry.t
  type action = Action.t
  type parsable
  val parsable : char Stream.t -> parsable
  val action : 'a -> action
  val entry_create : string -> 'a entry
  val entry_parse : 'a entry -> parsable -> 'a
  val entry_print : Format.formatter -> 'a entry -> unit
  val srules' : production_rule list -> symbol
end

module GrammarMake (L:LexerSig) : GrammarSig = struct
  (* We need to refer to Coq's module Loc before it is hidden by include *)
  let raise_coq_loc loc e = Loc.raise (to_coqloc loc) e
  include Camlp4.Struct.Grammar.Static.Make (L)
  type 'a entry = 'a Entry.t
  type action = Action.t
  type parsable = char Stream.t
  let parsable s = s
  let action = Action.mk
  let entry_create = Entry.mk
  let entry_parse e s =
    try parse e (*FIXME*)CompatLoc.ghost s
    with Exc_located (loc,e) -> raise_coq_loc loc e
  let entry_print ft x = Entry.print ft x
  let srules' = srules (entry_create "dummy")
end

END

(** Some definitions are grammar-specific in Camlp4, so we use a functor to
    depend on it while taking a dummy argument in Camlp5. *)

module GramextMake (G : GrammarSig) :
sig
  val stoken : Tok.t -> G.symbol
  val sself : G.symbol
  val snext : G.symbol
  val slist0 : G.symbol -> G.symbol
  val slist0sep : G.symbol * G.symbol -> G.symbol
  val slist1 : G.symbol -> G.symbol
  val slist1sep : G.symbol * G.symbol -> G.symbol
  val sopt : G.symbol -> G.symbol
  val snterml : G.internal_entry * string -> G.symbol
  val snterm : G.internal_entry -> G.symbol
  val snterml_level : G.symbol -> string
end =
struct

IFDEF CAMLP5 THEN
  let stoken tok =
    let pattern = match tok with
    | Tok.KEYWORD s -> "", s
    | Tok.IDENT s -> "IDENT", s
    | Tok.PATTERNIDENT s -> "PATTERNIDENT", s
    | Tok.FIELD s -> "FIELD", s
    | Tok.INT s -> "INT", s
    | Tok.INDEX s -> "INDEX", s
    | Tok.STRING s -> "STRING", s
    | Tok.LEFTQMARK -> "LEFTQMARK", ""
    | Tok.BULLET s -> "BULLET", s
    | Tok.EOI -> "EOI", ""
    in
    Gramext.Stoken pattern
ELSE
  module Gramext = G
  let stoken tok = match tok with
  | Tok.KEYWORD s -> Gramext.Skeyword s
  | tok -> Gramext.Stoken (Tok.equal tok, G.Token.to_string tok)
END

  let slist0sep (x, y) = Gramext.Slist0sep (x, y, false)
  let slist1sep (x, y) = Gramext.Slist1sep (x, y, false)

  let snterml (x, y) = Gramext.Snterml (x, y)
  let snterm x = Gramext.Snterm x
  let sself = Gramext.Sself
  let snext = Gramext.Snext
  let slist0 x = Gramext.Slist0 x
  let slist1 x = Gramext.Slist1 x
  let sopt x = Gramext.Sopt x

  let snterml_level = function
  | Gramext.Snterml (_, l) -> l
  | _ -> failwith "snterml_level"

end


(** Misc functional adjustments *)

(** - The lexer produces streams made of pairs in camlp4 *)

let get_tok = IFDEF CAMLP5 THEN fun x -> x ELSE fst END

(** - Gram.extend is more currified in camlp5 than in camlp4 *)

IFDEF CAMLP5 THEN
let maybe_curry f x y = f (x,y)
let maybe_uncurry f (x,y) = f x y
ELSE
let maybe_curry f = f
let maybe_uncurry f = f
END

(** Compatibility with camlp5 strict mode *)
IFDEF CAMLP5 THEN
  IFDEF STRICT THEN
    let vala x = Ploc.VaVal x
  ELSE
    let vala x = x
  END
ELSE
  let vala x = x
END

(** Fix a quotation difference in [str_item] *)

let declare_str_items loc l =
IFDEF CAMLP5 THEN
  MLast.StDcl (loc, vala l) (* correspond to <:str_item< declare $list:l'$ end >> *)
ELSE
  Ast.stSem_of_list l
END

(** Quotation difference for match clauses *)

let default_patt loc =
  (<:patt< _ >>, vala None, <:expr< failwith "Extension: cannot occur" >>)

IFDEF CAMLP5 THEN

let make_fun loc cl =
  let l = cl @ [default_patt loc] in
  MLast.ExFun (loc, vala l)  (* correspond to <:expr< fun [ $list:l$ ] >> *)

ELSE

let make_fun loc cl =
  let mk_when = function
    | Some w -> w
    | None -> Ast.ExNil loc
  in
  let mk_clause (patt,optwhen,expr) =
    (* correspond to <:match_case< ... when ... -> ... >> *)
    Ast.McArr (loc, patt, mk_when optwhen, expr) in
  let init = mk_clause (default_patt loc) in
  let add_clause x acc = Ast.McOr (loc, mk_clause x, acc) in
  let l = List.fold_right add_clause cl init in
  Ast.ExFun (loc,l) (* correspond to <:expr< fun [ $l$ ] >> *)

END

IFDEF CAMLP5 THEN
let warning_verbose = Gramext.warning_verbose
ELSE
(* TODO: this is a workaround, since there isn't such
   [warning_verbose] in new camlp4. *)
let warning_verbose = ref true
END
