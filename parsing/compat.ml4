(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

IFDEF CAMLP5_6_00 THEN
let ploc_make_loc fname lnb pos bpep = Ploc.make_loc fname lnb pos bpep ""
let ploc_file_name = Ploc.file_name
ELSE
let ploc_make_loc fname lnb pos bpep = Ploc.make lnb pos bpep
let ploc_file_name _ = ""
END

let of_coqloc loc =
  let (fname, lnb, pos, bp, ep) = Loc.represent loc in
  ploc_make_loc fname lnb pos (bp,ep)

let to_coqloc loc =
  Loc.create (ploc_file_name loc) (Ploc.line_nb loc)
    (Ploc.bol_pos loc) (Ploc.first_pos loc, Ploc.last_pos loc)

let make_loc = Ploc.make_unlined

ELSE

module CompatLoc = Camlp4.PreCast.Loc

exception Exc_located = CompatLoc.Exc_located

let of_coqloc loc =
  let (fname, lnb, pos, bp, ep) = Loc.represent loc in
  CompatLoc.of_tuple (fname, 0, 0, bp, 0, 0, ep, false)

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

ELSE

module PcamlSig = Camlp4.Sig
module Ast = Camlp4.PreCast.Ast
module Pcaml = Camlp4.PreCast.Syntax
module MLast = Ast
module Token = struct exception Error of string end

END


(** Grammar auxiliary types *)

IFDEF CAMLP5 THEN

let to_coq_assoc = function
| Gramext.RightA -> Extend.RightA
| Gramext.LeftA -> Extend.LeftA
| Gramext.NonA -> Extend.NonA

let of_coq_assoc = function
| Extend.RightA -> Gramext.RightA
| Extend.LeftA -> Gramext.LeftA
| Extend.NonA -> Gramext.NonA

let of_coq_position = function
| Extend.First -> Gramext.First
| Extend.Last -> Gramext.Last
| Extend.Before s -> Gramext.Before s
| Extend.After s -> Gramext.After s
| Extend.Level s -> Gramext.Level s

let to_coq_position = function
| Gramext.First -> Extend.First
| Gramext.Last -> Extend.Last
| Gramext.Before s -> Extend.Before s
| Gramext.After s -> Extend.After s
| Gramext.Level s -> Extend.Level s
| Gramext.Like _ -> assert false (** dont use it, not in camlp4 *)

ELSE

let to_coq_assoc = function
| PcamlSig.Grammar.RightA -> Extend.RightA
| PcamlSig.Grammar.LeftA -> Extend.LeftA
| PcamlSig.Grammar.NonA -> Extend.NonA

let of_coq_assoc = function
| Extend.RightA -> PcamlSig.Grammar.RightA
| Extend.LeftA -> PcamlSig.Grammar.LeftA
| Extend.NonA -> PcamlSig.Grammar.NonA

let of_coq_position = function
| Extend.First -> PcamlSig.Grammar.First
| Extend.Last -> PcamlSig.Grammar.Last
| Extend.Before s -> PcamlSig.Grammar.Before s
| Extend.After s -> PcamlSig.Grammar.After s
| Extend.Level s -> PcamlSig.Grammar.Level s

let to_coq_position = function
| PcamlSig.Grammar.First -> Extend.First
| PcamlSig.Grammar.Last -> Extend.Last
| PcamlSig.Grammar.Before s -> Extend.Before s
| PcamlSig.Grammar.After s -> Extend.After s
| PcamlSig.Grammar.Level s -> Extend.Level s

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
    with Exc_located (loc,e) -> Loc.raise (to_coqloc loc) e
IFDEF CAMLP5_6_02_1 THEN
  let entry_print ft x = Entry.print ft x
ELSE
  let entry_print _ x = Entry.print x
END
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

(** Explicit antiquotation $anti:... $ *)

IFDEF CAMLP5 THEN
let expl_anti loc e = <:expr< $anti:e$ >>
ELSE
let expl_anti _loc e = e (* FIXME: understand someday if we can do better *)
END

(** Qualified names in OCaml *)

IFDEF CAMLP5 THEN
let qualified_name loc path name =
  let fold dir accu = <:expr< $uid:dir$.$accu$ >> in
  List.fold_right fold path <:expr< $lid:name$ >>
ELSE
let qualified_name loc path name =
  let fold dir accu = Ast.IdAcc (loc, Ast.IdUid (loc, dir), accu) in
  let path = List.fold_right fold path (Ast.IdLid (loc, name)) in
  Ast.ExId (loc, path)
END
