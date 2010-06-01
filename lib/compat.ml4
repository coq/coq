(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Compatibility file depending on ocaml/camlp4 version *)

(** Locations *)

IFDEF CAMLP5 THEN

module Loc = struct
  include Ploc
  exception Exc_located = Exc
  let ghost = dummy
  let merge = encl
end

let make_loc = Loc.make_unlined
let unloc loc = (Loc.first_pos loc, Loc.last_pos loc)

ELSE

module Loc = Camlp4.PreCast.Loc

let make_loc (start,stop) =
  Loc.of_tuple ("", 0, 0, start, 0, 0, stop, false)
let unloc loc = (Loc.start_off loc, Loc.stop_off loc)

END

(** Misc module emulation *)

IFDEF CAMLP5 THEN

module PcamlSig = struct end

ELSE

module PcamlSig = Camlp4.Sig
module Ast = Camlp4.PreCast.Ast
module Pcaml = Camlp4.PreCast.Syntax
module MLast = Ast
module Token = struct exception Error of string end

END


(** Grammar auxiliary types *)

IFDEF CAMLP5 THEN
type gram_assoc = Gramext.g_assoc = NonA | RightA | LeftA
type gram_position = Gramext.position =
  | First
  | Last
  | Before of string
  | After of string
  | Like of string (** dont use it, not in camlp4 *)
  | Level of string
ELSE
type gram_assoc = PcamlSig.Grammar.assoc = NonA | RightA | LeftA
type gram_position = PcamlSig.Grammar.position =
  | First
  | Last
  | Before of string
  | After of string
  | Level of string
END


(** Signature of Lexer *)

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
  Camlp4.Sig.Lexer with module Loc = Loc and type Token.t = Tok.t

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
      string option * gram_assoc option * production_rule list
  type extend_statment =
      gram_position option * single_extend_statment list
  val action : 'a -> action
  val entry_create : string -> 'a entry
  val entry_parse : 'a entry -> parsable -> 'a
  val entry_print : 'a entry -> unit
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
      string option * gram_assoc option * production_rule list
  type extend_statment =
      gram_position option * single_extend_statment list
  let action = Gramext.action
  let entry_create = Entry.create
  let entry_parse = Entry.parse
  let entry_print = Entry.print
  let srules' = Gramext.srules
  let parse_tokens_after_filter = Entry.parse_token
end

ELSE

module type GrammarSig = sig
  include Camlp4.Sig.Grammar.Static
    with module Loc = Loc and type Token.t = Tok.t
  type 'a entry = 'a Entry.t
  type action = Action.t
  type parsable
  val parsable : char Stream.t -> parsable
  val action : 'a -> action
  val entry_create : string -> 'a entry
  val entry_parse : 'a entry -> parsable -> 'a
  val entry_print : 'a entry -> unit
  val srules' : production_rule list -> symbol
end

module GrammarMake (L:LexerSig) : GrammarSig = struct
  include Camlp4.Struct.Grammar.Static.Make (L)
  type 'a entry = 'a Entry.t
  type action = Action.t
  type parsable = char Stream.t
  let parsable s = s
  let action = Action.mk
  let entry_create = Entry.mk
  let entry_parse e s = parse e (*FIXME*)Loc.ghost s
  let entry_print x = Entry.print Format.std_formatter x
  let srules' = srules (entry_create "dummy")
end

END


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


(** Fix a quotation difference in [str_item] *)

let declare_str_items loc l =
  let l' = <:str_item< open Pcoq >> :: <:str_item< open Extrawit >> :: l in
IFDEF CAMLP5 THEN
  MLast.StDcl (loc,l') (* correspond to <:str_item< declare $list:l'$ end >> *)
ELSE
  Ast.stSem_of_list l'
END

(** Quotation difference for match clauses *)

let default_patt loc =
  (<:patt< _ >>, None, <:expr< failwith "Extension: cannot occur" >>)

IFDEF CAMLP5 THEN

let make_fun loc cl =
  let l = cl @ [default_patt loc] in
  MLast.ExFun (loc,l)  (* correspond to <:expr< fun [ $list:l$ ] >> *)

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

(** Explicit antiquotation $anti:... $ *)

IFDEF CAMLP5 THEN
let expl_anti loc e = <:expr< $anti:e$ >>
ELSE
let expl_anti _loc e = e (* FIXME: understand someday if we can do better *)
END
