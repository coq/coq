(* camlp5r *)
(* grammar.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Gramext
open Format
open Util

exception ParseError of string
(** Raised by parsers when the first component of a stream pattern is
   accepted, but one of the following components is rejected. *)

(* Functorial interface *)

type norec = private [ `norec ]
type mayrec = private [ `mayrec ]

module type S = sig
  type keyword_state
  type te
  type 'c pattern
  type ty_pattern = TPattern : 'a pattern -> ty_pattern

  type peek_error = unit

  type 'a parser_v = ('a, peek_error) result

  (** Type combinators to factor the module type between explicit
      state passing in Grammar and global state in Procq *)

  type 'a with_gstate
  (** Reader of grammar state *)

  type 'a with_kwstate
  (** Read keyword state *)

  type 'a with_estate
  (** Read entry state *)

  type 'a mod_estate
  (** Read/write entry state *)

  module Parsable : sig
    type t
    (** [Parsable.t] Stream tokenizers with Rocq-specific functionality *)

    val make : ?loc:Loc.t -> (unit,char) Stream.t -> t
    (** [make ?loc strm] Build a parsable from stream [strm], resuming
       at position [?loc] *)

    val comments : t -> ((int * int) * string) list

    val drop_comments : t -> unit

    val loc : t -> Loc.t
    (** [loc pa] Return parsing position for [pa] *)

    val consume : t -> int -> unit with_kwstate
    (** [consume pa n] Discard [n] tokens from [pa], updating the
       parsing position *)

  end

  module Entry : sig
    type 'a t
    val make : string -> 'a t mod_estate
    val parse : 'a t -> Parsable.t -> 'a with_gstate
    val name : 'a t -> string
    type 'a parser_fun = { parser_fun : keyword_state -> (keyword_state,te) LStream.t -> 'a parser_v }
    val of_parser : string -> 'a parser_fun -> 'a t mod_estate
    val parse_token_stream : 'a t -> (keyword_state,te) LStream.t -> 'a parser_v with_gstate
    val print : flatten:bool -> Format.formatter -> 'a t -> unit with_kwstate with_estate
    val is_empty : 'a t -> bool with_estate
    type any_t = Any : 'a t -> any_t
    val accumulate_in : any_t list -> any_t list CString.Map.t with_estate
    val all_in : unit -> any_t list CString.Map.t with_estate
  end

  module rec Symbol : sig

    type ('self, 'trec, 'a) t
    val nterm : 'a Entry.t -> ('self, norec, 'a) t
    val nterml : 'a Entry.t -> string -> ('self, norec, 'a) t
    val list0 : ('self, 'trec, 'a) t -> ('self, 'trec, 'a list) t
    val list0sep :
      ('self, 'trec, 'a) t -> ('self, norec, unit) t ->
      ('self, 'trec, 'a list) t
    val list1 : ('self, 'trec, 'a) t -> ('self, 'trec, 'a list) t
    val list1sep :
      ('self, 'trec, 'a) t -> ('self, norec, unit) t ->
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
  | Fresh of Gramext.position * 'a single_extend_statement list

  val generalize_symbol : ('a, 'tr, 'c) Symbol.t -> ('b, norec, 'c) Symbol.t option

  (* Used in custom entries, should tweak? *)
  val level_of_nonterm : _ Symbol.t -> string option

end

module type ExtS = sig

  type keyword_state

  module EState : sig
    type t
    val empty : t
  end
  module GState : sig
    type t = {
      estate : EState.t;
      kwstate : keyword_state;
      recover : bool;
      has_non_assoc : bool;
    }
  end

  include S
    with type keyword_state := keyword_state
     and type 'a with_gstate := GState.t -> 'a
     and type 'a with_kwstate := keyword_state -> 'a
     and type 'a with_estate := EState.t -> 'a
     and type 'a mod_estate := EState.t -> EState.t * 'a

  val safe_extend : EState.t -> 'a Entry.t -> 'a extend_statement -> EState.t

  type 's add_kw = { add_kw : 'c. 's -> 'c pattern -> 's }

  val add_extend_kws : 's add_kw -> 's -> _ extend_statement -> 's

  module Unsafe : sig
    val existing_entry : EState.t -> 'a Entry.t -> EState.t
    val existing_of_parser : EState.t -> 'a Entry.t -> 'a Entry.parser_fun -> EState.t
  end

end

(* Implementation *)
module GMake (L : Plexing.S) : ExtS
  with type keyword_state := L.keyword_state
   and type te := L.te
   and type 'c pattern := 'c L.pattern
= struct

type te = L.te
type 'c pattern = 'c L.pattern
type ty_pattern = TPattern : 'a pattern -> ty_pattern

type peek_error = unit

type 'a parser_v = ('a, peek_error) result

type 'a parser_t = (L.keyword_state,L.te) LStream.t -> 'a parser_v

let (let*) : 'a parser_v -> ('a -> 'b parser_v) -> 'b parser_v = Result.bind
let (let+) : 'a parser_v -> ('a ->' b) -> 'b parser_v = fun x f -> Result.map f x

let (<+>) (x: 'a parser_v) (y:unit -> 'a parser_v) : 'a parser_v =
  match x with
  | Ok _ -> x
  | Error () -> y ()

(** Used to propagate possible presence of SELF/NEXT in a rule (binary and) *)
type ('a, 'b, 'c) ty_and_rec =
| NoRec2 : (norec, norec, norec) ty_and_rec
| MayRec2 : ('a, 'b, mayrec) ty_and_rec

(** Used to propagate possible presence of SELF/NEXT in a tree (ternary and) *)
type ('a, 'b, 'c, 'd) ty_and_rec3 =
| NoRec3 : (norec, norec, norec, norec) ty_and_rec3
| MayRec3 : ('a, 'b, 'c, mayrec) ty_and_rec3

type _ tag = ..
module DMap = PolyMap.Make (struct type nonrec 'a tag = 'a tag = .. end)

type 'a ty_entry = {
  ename : string;
  etag : 'a DMap.onetag;
}

type ('self, 'trec, 'a) ty_symbol =
| Stoken : 'c pattern -> ('self, norec, 'c) ty_symbol
| Stokens : ty_pattern list -> ('self, norec, unit) ty_symbol
| Slist1 : ('self, 'trec, 'a) ty_symbol -> ('self, 'trec, 'a list) ty_symbol
| Slist1sep : ('self, 'trec, 'a) ty_symbol * ('self, norec, unit) ty_symbol -> ('self, 'trec, 'a list) ty_symbol
| Slist0 : ('self, 'trec, 'a) ty_symbol -> ('self, 'trec, 'a list) ty_symbol
| Slist0sep : ('self, 'trec, 'a) ty_symbol * ('self, norec, unit) ty_symbol -> ('self, 'trec, 'a list) ty_symbol
| Sopt : ('self, 'trec, 'a) ty_symbol -> ('self, 'trec, 'a option) ty_symbol
| Sself : ('self, mayrec, 'self) ty_symbol
| Snext : ('self, mayrec, 'self) ty_symbol
| Snterm : 'a ty_entry -> ('self, norec, 'a) ty_symbol
    (* norec but the entry can nevertheless introduce a loop with the current entry*)
| Snterml : 'a ty_entry * string -> ('self, norec, 'a) ty_symbol
| Stree : ('self, 'trec, Loc.t -> 'a) ty_tree -> ('self, 'trec, 'a) ty_symbol

and ('self, 'trec, 'a) ty_tree =
| Node : ('trn, 'trs, 'trb, 'tr) ty_and_rec3 * ('self, 'trn, 'trs, 'trb, 'b, 'a) ty_node -> ('self, 'tr, 'a) ty_tree
| LocAct : 'k -> ('self, norec, 'k) ty_tree
| DeadEnd : ('self, norec, 'k) ty_tree

and ('self, 'trec, 'trecs, 'trecb, 'a, 'r) ty_node = {
  node : ('self, 'trec, 'a) ty_symbol;
  son : ('self, 'trecs, 'a -> 'r) ty_tree;
  brother : ('self, 'trecb, 'r) ty_tree;
}

type ('self, _, _, 'r) ty_rule =
| TStop : ('self, norec, 'r, 'r) ty_rule
| TNext : ('trr, 'trs, 'tr) ty_and_rec * ('self, 'trr, 'a, 'r) ty_rule * ('self, 'trs, 'b) ty_symbol -> ('self, 'tr, 'b -> 'a, 'r) ty_rule

type ('trecs, 'trecp, 'a) ty_rec_level = {
  assoc : g_assoc;
  lname : string option;
  lsuffix : ('a, 'trecs, 'a -> Loc.t -> 'a) ty_tree;
  lprefix : ('a, 'trecp, Loc.t -> 'a) ty_tree;
}

type 'a ty_level = Level : (_, _, 'a) ty_rec_level -> 'a ty_level

type 'a ty_desc =
| Dlevels of 'a ty_level list
| Dparser of (L.keyword_state -> 'a parser_t)

type position = LStream.position

(** The closures are built by partially applying the parsing functions
    to [edesc] but without depending on the state (so when we update
    an entry we don't need to update closures in unrelated entries).
    This is an important optimisation, see eg https://gitlab.com/coq/coq/-/jobs/3585529623
    (+40% on mathcomp-ssreflect, +15% on stdlib without this,
     significant slowdowns on most developments)
*)
type ('t,'a) entry_data = {
  eentry : 'a ty_entry;
  edesc : 'a ty_desc;
  estart : 't -> int -> 'a parser_t;
  econtinue : 't -> int option -> int -> position -> 'a -> 'a parser_t;
}

module rec EState : DMap.MapS
  with type 'a value := (GState.t, 'a) entry_data
  = DMap.Map(struct type 'a t = (GState.t, 'a) entry_data end)

and GState : sig
  type t = {
    estate : EState.t;
    kwstate : L.keyword_state;
    recover : bool;
    has_non_assoc : bool;
  }
end = struct
  type t = {
    estate : EState.t;
    kwstate : L.keyword_state;
    recover : bool;
    has_non_assoc : bool;
  }
end
open GState

let get_entry estate e = try EState.find (DMap.tag_of_onetag e.etag) estate
  with Not_found -> assert false

type 'a ty_rules =
| TRules : (_, norec, 'act, Loc.t -> 'a) ty_rule * 'act -> 'a ty_rules

type 'a ty_production =
| TProd : ('a, _, 'act, Loc.t -> 'a) ty_rule * 'act -> 'a ty_production

let rec derive_eps : type s r a. (s, r, a) ty_symbol -> bool =
  function
    Slist0 _ -> true
  | Slist0sep (_, _) -> true
  | Sopt _ -> true
  | Stree t -> tree_derive_eps t
  | Slist1 _ -> false
  | Slist1sep (_, _) -> false
  | Snterm _ -> false | Snterml (_, _) -> false
  | Snext -> false
  | Sself -> false
  | Stoken _ -> false
  | Stokens _ -> false
and tree_derive_eps : type s tr a. (s, tr, a) ty_tree -> bool =
  function
    LocAct _ -> true
  | Node (_, {node = s; brother = bro; son = son}) ->
      derive_eps s && tree_derive_eps son || tree_derive_eps bro
  | DeadEnd -> false

let eq_entry : type a1 a2. a1 ty_entry -> a2 ty_entry -> (a1, a2) eq option = fun e1 e2 ->
  DMap.eq_onetag e1.etag (DMap.tag_of_onetag e2.etag)

let tok_pattern_eq_list pl1 pl2 =
  let f (TPattern p1) (TPattern p2) = Option.has_some (L.tok_pattern_eq p1 p2) in
  if List.for_all2eq f pl1 pl2 then Some Refl else None

let rec eq_symbol : type s r1 r2 a1 a2. (s, r1, a1) ty_symbol -> (s, r2, a2) ty_symbol -> (a1, a2) eq option = fun s1 s2 ->
  match s1, s2 with
    Snterm e1, Snterm e2 -> eq_entry e1 e2
  | Snterml (e1, l1), Snterml (e2, l2) ->
    if String.equal l1 l2 then eq_entry e1 e2 else None
  | Slist0 s1, Slist0 s2 ->
    begin match eq_symbol s1 s2 with None -> None | Some Refl -> Some Refl end
  | Slist0sep (s1, sep1), Slist0sep (s2, sep2) ->
    begin match eq_symbol s1 s2 with
    | None -> None
    | Some Refl ->
      match eq_symbol sep1 sep2 with
      | None -> None
      | Some Refl -> Some Refl
    end
  | Slist1 s1, Slist1 s2 ->
    begin match eq_symbol s1 s2 with None -> None | Some Refl -> Some Refl end
  | Slist1sep (s1, sep1), Slist1sep (s2, sep2) ->
    begin match eq_symbol s1 s2 with
    | None -> None
    | Some Refl ->
      match eq_symbol sep1 sep2 with
      | None -> None
      | Some Refl -> Some Refl
    end
  | Sopt s1, Sopt s2 ->
    begin match eq_symbol s1 s2 with None -> None | Some Refl -> Some Refl end
  | Stree _, Stree _ -> None
  | Sself, Sself -> Some Refl
  | Snext, Snext -> Some Refl
  | Stoken p1, Stoken p2 -> L.tok_pattern_eq p1 p2
  | Stokens pl1, Stokens pl2 -> tok_pattern_eq_list pl1 pl2
  | _ -> None

let is_before : type s1 s2 r1 r2 a1 a2. (s1, r1, a1) ty_symbol -> (s2, r2, a2) ty_symbol -> bool = fun s1 s2 ->
  match s1, s2 with
  | Stoken p1, Stoken p2 ->
     L.tok_pattern_exact p1
     && not (L.tok_pattern_exact p2)
  | Stoken _, _ -> true
  | _ -> false

(** Ancillary datatypes *)

type 'a ty_rec = MayRec : mayrec ty_rec | NoRec : norec ty_rec

type ('a, 'b, 'c) ty_and_ex =
| NR00 : (mayrec, mayrec, mayrec) ty_and_ex
| NR01 : (mayrec, norec, mayrec) ty_and_ex
| NR10 : (norec, mayrec, mayrec) ty_and_ex
| NR11 : (norec, norec, norec) ty_and_ex

type ('a, 'b) ty_mayrec_and_ex =
| MayRecNR : ('a, 'b, _) ty_and_ex -> ('a, 'b) ty_mayrec_and_ex

type ('s, 'a) ty_mayrec_symbol =
| MayRecSymbol : ('s, _, 'a) ty_symbol -> ('s, 'a) ty_mayrec_symbol

type ('s, 'a) ty_mayrec_tree =
| MayRecTree : ('s, 'tr, 'a) ty_tree -> ('s, 'a) ty_mayrec_tree

type ('s, 'a, 'r) ty_mayrec_rule =
| MayRecRule : ('s, _, 'a, 'r) ty_rule -> ('s, 'a, 'r) ty_mayrec_rule

type ('self, 'trec, _) ty_symbols =
| TNil : ('self, norec, unit) ty_symbols
| TCns : ('trh, 'trt, 'tr) ty_and_rec * ('self, 'trh, 'a) ty_symbol * ('self, 'trt, 'b) ty_symbols -> ('self, 'tr, 'a * 'b) ty_symbols

(** ('i, 'p, 'f, 'r) rel_prod0 ~
  ∃ α₁ ... αₙ.
    p ≡ αₙ * ... α₁ * 'i ∧
    f ≡ α₁ -> ... -> αₙ -> 'r
*)
type ('i, _, 'f, _) rel_prod0 =
| Rel0 : ('i, 'i, 'f, 'f) rel_prod0
| RelS : ('i, 'p, 'f, 'a -> 'r) rel_prod0 -> ('i, 'a * 'p, 'f, 'r) rel_prod0

type ('p, 'k, 'r) rel_prod = (unit, 'p, 'k, 'r) rel_prod0

type ('s, 'tr, 'i, 'k, 'r) any_symbols =
| AnyS : ('s, 'tr, 'p) ty_symbols * ('i, 'p, 'k, 'r) rel_prod0 -> ('s, 'tr, 'i, 'k, 'r) any_symbols

type ('s, 'tr, 'k, 'r) ty_belast_rule =
| Belast : ('trr, 'trs, 'tr) ty_and_rec * ('s, 'trr, 'k, 'a -> 'r) ty_rule * ('s, 'trs, 'a) ty_symbol -> ('s, 'tr, 'k, 'r) ty_belast_rule

(* unfortunately, this is quadratic, but ty_rules aren't too long
 * (99% of the time of length less or equal 10 and maximum is 22
 * when compiling Rocq and its standard library) *)
let rec get_symbols : type s trec k r. (s, trec, k, r) ty_rule -> (s, trec, unit, k, r) any_symbols =
  let rec belast_rule : type s trr trs tr a k r. (trr, trs, tr) ty_and_rec -> (s, trr, k, r) ty_rule -> (s, trs, a) ty_symbol -> (s, tr, a -> k, r) ty_belast_rule =
    fun ar r s -> match ar, r with
    | NoRec2, TStop -> Belast (NoRec2, TStop, s)
    | MayRec2, TStop -> Belast (MayRec2, TStop, s)
    | NoRec2, TNext (NoRec2, r, s') ->
       let Belast (NoRec2, r, s') = belast_rule NoRec2 r s' in
       Belast (NoRec2, TNext (NoRec2, r, s), s')
    | MayRec2, TNext (_, r, s') ->
       let Belast (_, r, s') = belast_rule MayRec2 r s' in
       Belast (MayRec2, TNext (MayRec2, r, s), s') in
  function
  | TStop -> AnyS (TNil, Rel0)
  | TNext (MayRec2, r, s) ->
     let Belast (MayRec2, r, s) = belast_rule MayRec2 r s in
     let AnyS (r, pf) = get_symbols r in
     AnyS (TCns (MayRec2, s, r), RelS pf)
  | TNext (NoRec2, r, s) ->
     let Belast (NoRec2, r, s) = belast_rule NoRec2 r s in
     let AnyS (r, pf) = get_symbols r in
     AnyS (TCns (NoRec2, s, r), RelS pf)

let get_rec_symbols (type s tr p) (s : (s, tr, p) ty_symbols) : tr ty_rec =
  match s with TCns (MayRec2, _, _) -> MayRec
  | TCns (NoRec2, _, _) -> NoRec | TNil -> NoRec

let get_rec_tree (type s tr f) (s : (s, tr, f) ty_tree) : tr ty_rec =
  match s with Node (MayRec3, _) -> MayRec
  | Node (NoRec3, _) -> NoRec | LocAct _ -> NoRec | DeadEnd -> NoRec

let and_symbols_tree (type s trs trt p f) (s : (s, trs, p) ty_symbols) (t : (s, trt, f) ty_tree) : (trs, trt) ty_mayrec_and_ex =
  match get_rec_symbols s, get_rec_tree t with
  | MayRec, MayRec -> MayRecNR NR00 | MayRec, NoRec -> MayRecNR NR01
  | NoRec, MayRec -> MayRecNR NR10 | NoRec, NoRec -> MayRecNR NR11

let and_and_tree (type s tr' trt tr trn trs trb f) (ar : (tr', trt, tr) ty_and_rec) (arn : (trn, trs, trb, trt) ty_and_rec3) (t : (s, trb, f) ty_tree) : (tr', trb, tr) ty_and_rec =
  match ar, arn, get_rec_tree t with
  | MayRec2, _, MayRec -> MayRec2 | MayRec2, _, NoRec -> MayRec2
  | NoRec2, NoRec3, NoRec -> NoRec2

let insert_tree (type s trs trt tr p k a) entry_name (ar : (trs, trt, tr) ty_and_ex) (gsymbols : (s, trs, p) ty_symbols) (pf : (p, k, a) rel_prod) (action : k) (tree : (s, trt, a) ty_tree) : (s, tr, a) ty_tree =
  let rec insert : type trs trt tr p f k. (trs, trt, tr) ty_and_ex -> (s, trs, p) ty_symbols -> (p, k, f) rel_prod -> (s, trt, f) ty_tree -> k -> (s, tr, f) ty_tree  =
    fun ar symbols pf tree action ->
    match symbols, pf with
      TCns (ars, s, sl), RelS pf ->
        (* descent in tree at symbol [s] *)
        insert_in_tree ar ars s sl pf tree action
    | TNil, Rel0 ->
        (* insert the action *)
        let node (type tb) ({node = s; son = son; brother = bro} : (_, _, _, tb, _, _) ty_node) =
          let ar : (norec, tb, tb) ty_and_ex =
            match get_rec_tree bro with MayRec -> NR10 | NoRec -> NR11 in
          {node = s; son = son; brother = insert ar TNil Rel0 bro action} in
        match ar, tree with
        | NR10, Node (_, n) -> Node (MayRec3, node n)
        | NR11, Node (NoRec3, n) -> Node (NoRec3, node n)
        | NR11, LocAct old_action ->
          (* What to do about this warning? For now it is disabled *)
          if false then
            begin
              let msg =
                "<W> Grammar extension: " ^
                (if entry_name = "" then "" else "in ["^entry_name^"%s], ") ^
                "some rule has been masked" in
              Feedback.msg_warning (Pp.str msg)
            end;
          LocAct action
        | NR11, DeadEnd -> LocAct action
  and insert_in_tree : type trs trs' trs'' trt tr a p f k. (trs'', trt, tr) ty_and_ex -> (trs, trs', trs'') ty_and_rec -> (s, trs, a) ty_symbol -> (s, trs', p) ty_symbols -> (p, k, a -> f) rel_prod -> (s, trt, f) ty_tree -> k -> (s, tr, f) ty_tree =
    fun ar ars s sl pf tree action ->
    let ar : (trs'', trt, tr) ty_and_rec = match ar with NR11 -> NoRec2
      | NR00 -> MayRec2 | NR01 -> MayRec2 | NR10 -> MayRec2 in
    match try_insert ar ars s sl pf tree action with
      Some t -> t
    | None ->
       let node ar =
         {node = s; son = insert ar sl pf DeadEnd action; brother = tree} in
       match ar, ars, get_rec_symbols sl with
       | MayRec2, MayRec2, MayRec -> Node (MayRec3, node NR01)
       | MayRec2, _, NoRec -> Node (MayRec3, node NR11)
       | NoRec2, NoRec2, NoRec -> Node (NoRec3, node NR11)
  and try_insert : type trs trs' trs'' trt tr a p f k. (trs'', trt, tr) ty_and_rec -> (trs, trs', trs'') ty_and_rec -> (s, trs, a) ty_symbol -> (s, trs', p) ty_symbols -> (p, k, a -> f) rel_prod -> (s, trt, f) ty_tree -> k -> (s, tr, f) ty_tree option =
    fun ar ars symb symbl pf tree action ->
    match tree with
      Node (arn, {node = symb1; son = son; brother = bro}) ->
        (* merging rule [symb; symbl -> action] in tree [symb1; son | bro] *)
        begin match eq_symbol symb symb1 with
        | Some Refl ->
          (* reducing merge of [symb; symbl -> action] with [symb1; son] to merge of [symbl -> action] with [son] *)
          let MayRecNR arss = and_symbols_tree symbl son in
          let son = insert arss symbl pf son action in
          let node = {node = symb1; son = son; brother = bro} in
          (* propagate presence of SELF/NEXT *)
          begin match ar, ars, arn, arss with
          | MayRec2, _, _, _ -> Some (Node (MayRec3, node))
          | NoRec2, NoRec2, NoRec3, NR11 -> Some (Node (NoRec3, node)) end
        | None ->
        let ar' = and_and_tree ar arn bro in
        if is_before symb1 symb || derive_eps symb && not (derive_eps symb1) then
          (* inserting new rule after current rule, i.e. in [bro] *)
          let bro =
            match try_insert ar' ars symb symbl pf bro action with
              Some bro ->
                (* could insert in [bro] *)
                bro
            | None ->
                (* not ok to insert in [bro] or after; we insert now *)
                let MayRecNR arss = and_symbols_tree symbl DeadEnd in
                let son = insert arss symbl pf DeadEnd action in
                let node = {node = symb; son = son; brother = bro} in
                (* propagate presence of SELF/NEXT *)
                match ar, ars, arn, arss with
                | MayRec2, _, _, _ -> Node (MayRec3, node)
                | NoRec2, NoRec2, NoRec3, NR11 -> Node (NoRec3, node)
          in
          let node = {node = symb1; son = son; brother = bro} in
          (* propagate presence of SELF/NEXT *)
          match ar, arn with
            | MayRec2, _ -> Some (Node (MayRec3, node))
            | NoRec2, NoRec3 -> Some (Node (NoRec3, node))
        else
          (* should insert in [bro] or before the tree [symb1; son | bro] *)
          match try_insert ar' ars symb symbl pf bro action with
            Some bro ->
             (* could insert in [bro] *)
              let node = {node = symb1; son = son; brother = bro} in
              begin match ar, arn with
                | MayRec2, _ -> Some (Node (MayRec3, node))
                | NoRec2, NoRec3 -> Some (Node (NoRec3, node)) end
          | None ->
             (* should insert before [symb1; son | bro] *)
             None
        end
    | LocAct _ -> None | DeadEnd -> None
  in
  insert ar gsymbols pf tree action

let insert_tree_norec (type s p k a) entry_name (gsymbols : (s, norec, p) ty_symbols) (pf : (p, k, a) rel_prod) (action : k) (tree : (s, norec, a) ty_tree) : (s, norec, a) ty_tree =
  insert_tree entry_name NR11 gsymbols pf action tree

let insert_tree (type s trs trt p k a) entry_name (gsymbols : (s, trs, p) ty_symbols) (pf : (p, k, a) rel_prod) (action : k) (tree : (s, trt, a) ty_tree) : (s, a) ty_mayrec_tree =
  let MayRecNR ar = and_symbols_tree gsymbols tree in
  MayRecTree (insert_tree entry_name ar gsymbols pf action tree)

let srules (type self a) (rl : a ty_rules list) : (self, norec, a) ty_symbol =
  let rec retype_tree : type s a. (s, norec, a) ty_tree -> (self, norec, a) ty_tree =
    function
    | Node (NoRec3, {node = s; son = son; brother = bro}) ->
      Node (NoRec3, {node = retype_symbol s; son = retype_tree son; brother = retype_tree bro})
    | LocAct k -> LocAct k
    | DeadEnd -> DeadEnd
  and retype_symbol : type s a. (s, norec, a) ty_symbol -> (self, norec, a) ty_symbol =
    function
    | Stoken p -> Stoken p
    | Stokens l -> Stokens l
    | Slist1 s -> Slist1 (retype_symbol s)
    | Slist1sep (s, sep) -> Slist1sep (retype_symbol s, retype_symbol sep)
    | Slist0 s -> Slist0 (retype_symbol s)
    | Slist0sep (s, sep) -> Slist0sep (retype_symbol s, retype_symbol sep)
    | Sopt s -> Sopt (retype_symbol s)
    | Snterm e -> Snterm e
    | Snterml (e, l) -> Snterml (e, l)
    | Stree t -> Stree (retype_tree t) in
  let rec retype_rule : type s k r. (s, norec, k, r) ty_rule -> (self, norec, k, r) ty_rule =
    function
    | TStop -> TStop
    | TNext (NoRec2, r, s) -> TNext (NoRec2, retype_rule r, retype_symbol s) in
  let t =
    List.fold_left
      (fun tree (TRules (symbols, action)) ->
        let symbols = retype_rule symbols in
        let AnyS (symbols, pf) = get_symbols symbols in
        insert_tree_norec "" symbols pf action tree)
      DeadEnd rl
  in
  Stree t

let is_level_labelled n (Level lev) =
  match lev.lname with
    Some n1 -> n = n1
  | None -> false

let insert_level (type s tr p k) entry_name (symbols : (s, tr, p) ty_symbols) (pf : (p, k, Loc.t -> s) rel_prod) (action : k) (slev : s ty_level) : s ty_level =
  match symbols with
  | TCns (_, Sself, symbols) ->
      (* Insert a rule of the form "SELF; ...." *)
      let Level slev = slev in
      let RelS pf = pf in
      let MayRecTree lsuffix = insert_tree entry_name symbols pf action slev.lsuffix in
      Level
      {assoc = slev.assoc; lname = slev.lname;
       lsuffix = lsuffix;
       lprefix = slev.lprefix}
  | _ ->
      (* Insert a rule not starting with SELF *)
      let Level slev = slev in
      let MayRecTree lprefix = insert_tree entry_name symbols pf action slev.lprefix in
      Level
      {assoc = slev.assoc; lname = slev.lname; lsuffix = slev.lsuffix;
       lprefix = lprefix}

let empty_lev lname assoc =
  let assoc =
    match assoc with
      Some a -> a
    | None -> LeftA
  in
  Level
  {assoc = assoc; lname = lname; lsuffix = DeadEnd; lprefix = DeadEnd}

let err_no_level lev e =
  let msg = sprintf "Grammar.extend: No level labelled \"%s\" in entry \"%s\"" lev e in
  failwith msg

let get_position entry position levs =
  match position with
    First -> [], levs
  | Last -> levs, []
  | Before n ->
      let rec get =
        function
          [] -> err_no_level n entry.ename
        | lev :: levs ->
            if is_level_labelled n lev then [], lev :: levs
            else
              let (levs1, levs2) = get levs in lev :: levs1, levs2
      in
      get levs
  | After n ->
      let rec get =
        function
          [] -> err_no_level n entry.ename
        | lev :: levs ->
            if is_level_labelled n lev then [lev], levs
            else
              let (levs1, levs2) = get levs in lev :: levs1, levs2
      in
      get levs

let get_level entry name levs = match name with
  | Some n ->
      let rec get =
        function
          [] -> err_no_level n entry.ename
        | lev :: levs ->
            if is_level_labelled n lev then [], lev, levs
            else
              let (levs1, rlev, levs2) = get levs in lev :: levs1, rlev, levs2
      in
      get levs
  | None ->
    begin match levs with
        lev :: levs -> [], lev, levs
      | [] ->
        let msg = sprintf "Grammar.extend: No top level in entry \"%s\"" entry.ename in
        failwith msg
    end

let change_to_self0 (type s) (type trec) (type a) (entry : s ty_entry) : (s, trec, a) ty_symbol -> (s, a) ty_mayrec_symbol =
  function
  | Snterm e ->
      begin match eq_entry e entry with
      | None -> MayRecSymbol (Snterm e)
      | Some Refl -> MayRecSymbol (Sself)
      end
  | x -> MayRecSymbol x

let rec change_to_self : type s trec a r. s ty_entry -> (s, trec, a, r) ty_rule -> (s, a, r) ty_mayrec_rule = fun e r -> match r with
| TStop -> MayRecRule TStop
| TNext (_, r, t) ->
  let MayRecRule r = change_to_self e r in
  let MayRecSymbol t = change_to_self0 e t in
  MayRecRule (TNext (MayRec2, r, t))

type 'a single_extend_statement =
  string option * Gramext.g_assoc option * 'a ty_production list

type 'a extend_statement =
| Reuse of string option * 'a ty_production list
| Fresh of Gramext.position * 'a single_extend_statement list

type 's add_kw = { add_kw : 'c. 's -> 'c pattern -> 's }

let rec add_symbol_kws : type s trec a. _ -> _ -> (s, trec, a) ty_symbol -> _ =
  fun add_kw lstate -> function
  | Slist0 s -> add_symbol_kws add_kw lstate s
  | Slist1 s -> add_symbol_kws add_kw lstate s
  | Slist0sep (s, t) -> let lstate = add_symbol_kws add_kw lstate s in add_symbol_kws add_kw lstate t
  | Slist1sep (s, t) -> let lstate = add_symbol_kws add_kw lstate s in add_symbol_kws add_kw lstate t
  | Sopt s -> add_symbol_kws add_kw lstate s
  | Stree t -> add_tree_kws add_kw lstate t
  | Stoken tok -> add_kw.add_kw lstate tok
  | Stokens (TPattern tok::_) ->
    (* Only the first token is liable to trigger a keyword effect *)
    add_kw.add_kw lstate tok
  | Stokens [] -> assert false
  | Snterm _
  | Snterml _
  | Snext
  | Sself -> lstate

and add_tree_kws : type s tr a. _ -> _ -> (s, tr, a) ty_tree -> _ =
  fun add_kw lstate -> function
  | Node (_, {node = s; brother = bro; son = son}) ->
    let lstate = add_symbol_kws add_kw lstate s in
    let lstate = add_tree_kws add_kw lstate bro in
    add_tree_kws add_kw lstate son
  | LocAct _ | DeadEnd -> lstate

let rec add_rule_kws : type s trr k r. _ -> _ -> (s, trr, k, r) ty_rule -> _ =
  fun add_kw lstate -> function
  | TStop -> lstate
  | TNext (_, r, s) ->
    let lstate = add_symbol_kws add_kw lstate s in
    add_rule_kws add_kw lstate r

let add_production_kws add_kw lstate (TProd (r, _)) = add_rule_kws add_kw lstate r

let add_extend_kws add_kw lstate ext =
  let add_ps lstate ps =
    List.fold_left (fun lstate p -> add_production_kws add_kw lstate p) lstate ps
  in
  match ext with
  | Reuse (_, ps) -> add_ps lstate ps
  | Fresh (_, ps) -> List.fold_left (fun lstate (_, _, ps) -> add_ps lstate ps) lstate ps

let add_prod entry lev (TProd (symbols, action)) =
  let MayRecRule symbols = change_to_self entry symbols in
  let AnyS (symbols, pf) = get_symbols symbols in
  insert_level entry.ename symbols pf action lev

let levels_of_rules entry edata st =
  let elev =
    match edata.edesc with
      Dlevels elev -> elev
    | Dparser _ ->
        let msg = sprintf "Grammar.extend: entry not extensible: \"%s\"" entry.ename in
        failwith msg
  in
  match st with
  | Reuse (name, []) -> elev
  | Reuse (name, prods) ->
    let (levs1, lev, levs2) = get_level entry name elev in
    let lev = List.fold_left (fun lev prod -> add_prod entry lev prod) lev prods in
    levs1 @ [lev] @ levs2
  | Fresh (position, rules) ->
    let (levs1, levs2) = get_position entry position elev in
    let fold levs (lname, assoc, prods) =
      let lev = empty_lev lname assoc in
      let lev = List.fold_left (fun lev prod -> add_prod entry lev prod) lev prods in
      lev :: levs
    in
    let levs = List.fold_left fold [] rules in
    levs1 @ List.rev levs @ levs2

(* used for printing and iteration *)
type ex_symbols =
  | ExNil
  | ExCns : _ ty_symbol * ex_symbols list -> ex_symbols

let exCns ~flatten n s =
  if flatten then
    List.map (fun s -> ExCns (n, [s])) s
  else [ExCns (n, s)]

let rec ex_tree : type s tr a. flatten:bool -> (s, tr, a) ty_tree -> ex_symbols list =
  fun ~flatten -> function
    DeadEnd -> []
  | LocAct _ -> [ExNil]
  | Node (_, {node = n; brother = b; son = s}) ->
    let s = ex_tree ~flatten s in
    exCns ~flatten n s @ ex_tree ~flatten b

let utf8_string_escaped s =
  let b = Buffer.create (String.length s) in
  let rec loop i =
    if i = String.length s then Buffer.contents b
    else
      begin
        begin match s.[i] with
          '"' -> Buffer.add_string b "\\\""
        | '\\' -> Buffer.add_string b "\\\\"
        | '\n' -> Buffer.add_string b "\\n"
        | '\t' -> Buffer.add_string b "\\t"
        | '\r' -> Buffer.add_string b "\\r"
        | '\b' -> Buffer.add_string b "\\b"
        | c -> Buffer.add_char b c
        end;
        loop (i + 1)
      end
  in
  loop 0

let string_escaped s = utf8_string_escaped s

let print_str ppf s = fprintf ppf "\"%s\"" (string_escaped s)

let print_token kwstate b ppf p =
  match L.tok_pattern_strings kwstate p with
  | "", Some s -> print_str ppf s
  | con, Some prm -> if b then fprintf ppf "%s@ %a" con print_str prm else fprintf ppf "(%s@ %a)" con print_str prm
  | con, None -> fprintf ppf "%s" con

let print_tokens kwstate ppf = function
  | [] -> assert false
  | TPattern p :: pl ->
    fprintf ppf "[%a%a]"
    (print_token kwstate true) p
    (fun ppf -> List.iter (function TPattern p -> fprintf ppf ";@ "; print_token kwstate true ppf p))
    pl

let print_level ~flatten =
  let rec print_symbol : type s tr r. _ -> formatter -> (s, tr, r) ty_symbol -> unit =
    fun kwstate ppf ->
    function
    | Slist0 s -> fprintf ppf "LIST0 %a" (print_symbol1 kwstate) s
    | Slist0sep (s, t) ->
      fprintf ppf "LIST0 %a SEP %a" (print_symbol1 kwstate) s (print_symbol1 kwstate) t
    | Slist1 s -> fprintf ppf "LIST1 %a" (print_symbol1 kwstate) s
    | Slist1sep (s, t) ->
      fprintf ppf "LIST1 %a SEP %a" (print_symbol1 kwstate) s (print_symbol1 kwstate) t
    | Sopt s -> fprintf ppf "OPT %a" (print_symbol1 kwstate) s
    | Stoken p -> print_token kwstate true ppf p
    | Stokens [TPattern p] -> print_token kwstate true ppf p
    | Stokens pl -> print_tokens kwstate ppf pl
    | Snterml (e, l) ->
      fprintf ppf "%s LEVEL %a" e.ename print_str l
    | s -> (print_symbol1 kwstate) ppf s
  and print_symbol1 : type s tr r. _ -> formatter -> (s, tr, r) ty_symbol -> unit =
    fun kwstate ppf ->
    function
    | Snterm e -> fprintf ppf "%s%s" e.ename ""
    | Sself -> pp_print_string ppf "SELF"
    | Snext -> pp_print_string ppf "NEXT"
    | Stoken p -> print_token kwstate false ppf p
    | Stokens [TPattern p] -> print_token kwstate false ppf p
    | Stokens pl -> print_tokens kwstate ppf pl
    | Stree t -> print_level kwstate ppf pp_print_space (ex_tree ~flatten t)
    | s ->
      fprintf ppf "(%a)" (print_symbol kwstate) s
  and print_rule : _ -> formatter -> ex_symbols -> unit =
    fun kwstate ppf symbols ->
    fprintf ppf "@[<hov 0>";
    let rec fold : _ -> ex_symbols -> unit =
      fun sep symbols ->
      match symbols with
      | ExNil -> ()
      | ExCns (symbol, symbols) ->
        fprintf ppf "%t%a" sep (print_symbol kwstate) symbol;
        match symbols with
        | [symbols] ->
          fold (fun ppf -> fprintf ppf ";@ ") symbols
        | _ -> fprintf ppf ";@ "; print_level kwstate ppf pp_force_newline symbols
    in
    let () = fold (fun ppf -> ()) symbols in
    fprintf ppf "@]"
  and print_level : _ -> _ -> _ -> ex_symbols list -> _ =
    fun kwstate ppf pp_print_space rules ->
    fprintf ppf "@[<hov 0>[ ";
    let () =
      Format.pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "%a| " pp_print_space ())
        (fun ppf rule -> print_rule kwstate ppf rule)
        ppf rules
    in
    fprintf ppf " ]@]"
  in
  print_level

let ex_level ~flatten lev =
  let suff = ex_tree ~flatten lev.lsuffix in
  let lrec = if List.is_empty suff then [] else exCns ~flatten Sself suff in
  lrec @ ex_tree ~flatten lev.lprefix

let print_levels ~flatten kwstate ppf elev =
  Format.pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@,| ")
    (fun ppf (Level lev) ->
       let rules = ex_level ~flatten lev in
       fprintf ppf "@[<hov 2>";
       begin match lev.lname with
           Some n -> fprintf ppf "%a@;<1 2>" print_str n
         | None -> ()
       end;
       begin match lev.assoc with
           BothA -> fprintf ppf "BOTHA"
         | LeftA -> fprintf ppf "LEFTA"
         | RightA -> fprintf ppf "RIGHTA"
         | NonA -> fprintf ppf "NONA"
       end;
       fprintf ppf "@]@;<1 2>";
       print_level ~flatten kwstate ppf pp_force_newline rules)
    ppf elev

let print_entry ~flatten estate kwstate ppf e =
  fprintf ppf "@[<v 0>[ ";
  begin match (get_entry estate e).edesc with
    Dlevels elev -> print_levels ~flatten kwstate ppf elev
  | Dparser _ -> fprintf ppf "<parser>"
  end;
  fprintf ppf " ]@]"

let name_of_symbol : type s tr a. s ty_entry -> (s, tr, a) ty_symbol -> string =
  fun entry ->
  function
    Snterm e -> "[" ^ e.ename ^ "]"
  | Snterml (e, l) -> "[" ^ e.ename ^ " level " ^ l ^ "]"
  | Sself -> "[" ^ entry.ename ^ "]"
  | Snext -> "[" ^ entry.ename ^ "]"
  | Stoken tok -> L.tok_text tok
  | Stokens tokl -> String.concat " " (List.map (function TPattern tok -> L.tok_text tok) tokl)
  | Slist0 _ -> assert false
  | Slist1sep _ -> assert false
  | Slist1 _ -> assert false
  | Slist0sep _ -> assert false
  | Sopt _ -> assert false
  | Stree _ -> assert false

type ('r, 'f) tok_list =
| TokNil : ('f, 'f) tok_list
| TokCns : 'a pattern * ('r, 'f) tok_list -> ('a -> 'r, 'f) tok_list

type ('s, 'f) tok_tree = TokTree : 'a pattern * ('s, _, 'a -> 'r) ty_tree * ('r, 'f) tok_list -> ('s, 'f) tok_tree

let rec get_token_list : type s tr a r f.
  s ty_entry -> a pattern -> (r, f) tok_list -> (s, tr, a -> r) ty_tree -> (s, f) tok_tree option =
  fun entry last_tok rev_tokl tree ->
  match tree with
    Node (_, {node = Stoken tok; son = son; brother = DeadEnd}) ->
      get_token_list entry tok (TokCns (last_tok, rev_tokl)) son
  | _ ->
     match rev_tokl with
     | TokNil -> None
     | _ -> Some (TokTree (last_tok, tree, rev_tokl))

let rec name_of_symbol_failed : type s tr a. s ty_entry -> (s, tr, a) ty_symbol -> _ =
  fun entry ->
  function
  | Slist0 s -> name_of_symbol_failed entry s
  | Slist0sep (s, _) -> name_of_symbol_failed entry s
  | Slist1 s -> name_of_symbol_failed entry s
  | Slist1sep (s, _) -> name_of_symbol_failed entry s
  | Sopt s -> name_of_symbol_failed entry s
  | Stree t -> name_of_tree_failed entry t
  | s -> name_of_symbol entry s
and name_of_tree_failed : type s tr a. s ty_entry -> (s, tr, a) ty_tree -> _ =
  fun entry ->
  function
    Node (_, {node = s; son = son; brother = bro}) ->
      let tokl =
        match s with
          Stoken tok -> get_token_list entry tok TokNil son
        | _ -> None
      in
      let txt =
        match tokl with
        | None ->
          let txt = name_of_symbol_failed entry s in
          let txt =
            match s, son with
              Sopt _, Node _ -> txt ^ " or " ^ name_of_tree_failed entry son
            | _ -> txt
          in
          txt
        | Some (TokTree (last_tok, _, rev_tokl)) ->
          let rec build_str : type a b. string -> (a, b) tok_list -> string =
           fun s -> function
           | TokNil -> s
           | TokCns (tok, t) -> build_str (L.tok_text tok ^ " " ^ s) t in
          build_str (L.tok_text last_tok) rev_tokl
      in
      begin match bro with
      | DeadEnd -> txt
      | LocAct _ -> "nothing else"
      | Node _ -> txt ^ " or " ^ name_of_tree_failed entry bro
      end
  | DeadEnd -> "???" | LocAct _ -> "nothing else"

let tree_failed (type s tr a) (entry : s ty_entry) (prev_symb_result : a) (prev_symb : (s, tr, a) ty_symbol) tree =
  let txt = name_of_tree_failed entry tree in
  let txt =
    match prev_symb with
      Slist0 s ->
        let txt1 = name_of_symbol_failed entry s in
        txt1 ^ " or " ^ txt ^ " expected"
    | Slist1 s ->
        let txt1 = name_of_symbol_failed entry s in
        txt1 ^ " or " ^ txt ^ " expected"
    | Slist0sep (s, sep) ->
        begin match prev_symb_result with
          [] ->
            let txt1 = name_of_symbol_failed entry s in
            txt1 ^ " or " ^ txt ^ " expected"
        | _ ->
            let txt1 = name_of_symbol_failed entry sep in
            txt1 ^ " or " ^ txt ^ " expected"
        end
    | Slist1sep (s, sep) ->
        begin match prev_symb_result with
          [] ->
            let txt1 = name_of_symbol_failed entry s in
            txt1 ^ " or " ^ txt ^ " expected"
        | _ ->
            let txt1 = name_of_symbol_failed entry sep in
            txt1 ^ " or " ^ txt ^ " expected"
        end
    | Sopt _ -> txt ^ " expected"
    | Stree _ -> txt ^ " expected"
    | Snterm _ | Snterml _ | Sself | Snext
    | Stoken _ | Stokens _ -> txt ^ " expected after " ^ name_of_symbol_failed entry prev_symb
  in
  txt ^ " (in [" ^ entry.ename ^ "])"

let symb_failed entry prev_symb_result prev_symb symb =
  let tree = Node (MayRec3, {node = symb; brother = DeadEnd; son = DeadEnd}) in
  tree_failed entry prev_symb_result prev_symb tree

(* XXX don't use exceptions for this *)
exception TokenListFailed : 's ty_entry * 'a * ('s, 'tr, 'a) ty_symbol * ('s, 'b, 'c) ty_tree -> exn

let level_number entry lab =
  let rec lookup levn =
    function
      [] -> failwith ("unknown level " ^ lab)
    | lev :: levs ->
        if is_level_labelled lab lev then levn else lookup (succ levn) levs
  in
  match entry.edesc with
    Dlevels elev -> lookup 0 elev
  | Dparser _ -> raise Not_found

let rec top_symb : type s tr a. s ty_entry -> (s, tr, a) ty_symbol -> (s, norec, a) ty_symbol parser_v =
  fun entry ->
  function
    Sself -> Ok (Snterm entry)
  | Snext -> Ok (Snterm entry)
  | Snterml (e, _) -> Ok (Snterm e)
  | Slist1sep (s, sep) -> let+ s = top_symb entry s in Slist1sep (s, sep)
  | _ -> Error ()

let entry_of_symb : type s tr a. s ty_entry -> (s, tr, a) ty_symbol -> a ty_entry parser_v =
  fun entry ->
  function
    Sself -> Ok entry
  | Snext -> Ok entry
  | Snterm e -> Ok e
  | Snterml (e, _) -> Ok e
  | _ -> Error ()

let top_tree : type s tr a. s ty_entry -> (s, tr, a) ty_tree -> (s, tr, a) ty_tree parser_v =
  fun entry ->
  function
  | Node (MayRec3, {node = s; brother = bro; son = son}) ->
    let+ s' = top_symb entry s in
    Node (MayRec3, {node = s'; brother = bro; son = son})
  | Node (NoRec3, {node = s; brother = bro; son = son}) ->
    let+ s' = top_symb entry s in
    Node (NoRec3, {node = s'; brother = bro; son = son})
  | LocAct _ | DeadEnd -> Error ()

let locate_pos = LStream.current

let interval_loc bpos epos =
  let bp = LStream.pos_offset bpos in
  let ep = LStream.pos_offset epos in
  let () = assert (bp <= ep) in
  if Int.equal bp ep then
    let cur = LStream.pos_current bpos in
    Loc.after cur 0 0
  else
    let next = LStream.pos_next bpos in
    let last = LStream.pos_current epos in
    Loc.merge next last

let warn_tolerance =
  CWarnings.(create_in (create_warning ~name:"level-tolerance"
                          ~from:[CoreCategories.parsing; Deprecation.Version.v9_2] ())
    ~quickfix:(fun ~loc (_, _, qf) -> qf)
    Pp.(fun (e, msg, _) ->
        strbrk "In " ++ str e ++ str ", tolerating this expression at" ++
        strbrk " a higher level than expected " ++ strbrk msg ++ str "." ++
        strbrk " This tolerance will be eventually removed." ++
        strbrk " Insert parentheses or try to lower the level at which the top symbol of this expression is parsed."))

let warn_recover_qf ename bp ?ep strm__ msg =
  let has_ep = Option.has_some ep in
  let ep = Option.default (locate_pos strm__) ep in
  let loc = interval_loc bp ep in
  let qf =
    let paren_enames = ["term"; "pattern"; "ltac_expr"] in
    if not (has_ep && List.mem ename paren_enames) then [] else
      let qf le s = Quickfix.make ~loc:(le loc 0 0) (Pp.str s) in
      [qf Loc.sub "("; qf Loc.after ")"] in
  warn_tolerance ~loc (ename, msg, qf)

let warn_recover ename bp ?ep strm__ =
  warn_recover_qf ename bp ?ep strm__ "by the notation started on the left"

let warn_recover_continuation ename bp ep strm__ strict =
  let msg = "by the notation continuing on the right"
    ^ if not strict then "" else " (which is not left-associative)" in
  warn_recover_qf ename bp ~ep strm__ msg

let warn_recover_last_start ename bp ep strm__ =
  warn_recover_qf ename bp ~ep strm__ "(there is no next level of last level)"

let empty_entry ename levn strm =
  raise (ParseError ("entry [" ^ ename ^ "] is empty"))

let start_parser_of_entry gstate entry levn (strm:_ LStream.t) =
  (get_entry gstate.estate entry).estart gstate levn strm

let continue_parser_of_entry gstate entry levfrom levn bp a (strm:_ LStream.t) =
  (get_entry gstate.estate entry).econtinue gstate levfrom levn bp a strm

(**
  nlevn: level for Snext
  alevn: level for recursive calls on the right-hand side of the rule (depending on associativity)
*)
let rec parser_of_tree : type s tr r. s ty_entry -> int -> int -> (s, tr, r) ty_tree -> GState.t -> r parser_t =
  fun entry nlevn alevn ->
  function
  | DeadEnd -> (fun _ (strm__ : _ LStream.t) -> Error ())
  | LocAct act -> (fun _ (strm__ : _ LStream.t) -> Ok act)
  | Node (_, {node = Sself; son = LocAct act; brother = DeadEnd}) ->
      (* SELF on the right-hand side of the last rule *)
      (fun gstate (strm__ : _ LStream.t) ->
         let+ a = start_parser_of_entry gstate entry alevn strm__ in act a)
  | Node (_, {node = Sself; son = LocAct act; brother = bro}) ->
      (* SELF on the right-hand side of a rule *)
      let p2 = parser_of_tree entry nlevn alevn bro in
      (fun gstate (strm__ : _ LStream.t) ->
         match start_parser_of_entry gstate entry alevn strm__ with
         | Ok a -> Ok (act a)
         | Error () -> p2 gstate strm__)
  | Node (_, {node = Stoken tok; son = son; brother = DeadEnd}) ->
          parser_of_token_list entry nlevn alevn tok son
  | Node (_, {node = Stoken tok; son = son; brother = bro}) ->
          let p2 = parser_of_tree entry nlevn alevn bro in
          let p1 = parser_of_token_list entry nlevn alevn tok son in
          (fun gstate (strm__ : _ LStream.t) ->
             p1 gstate strm__ <+> (fun () -> p2 gstate strm__))
  | Node (_, {node = s; son = son; brother = DeadEnd}) ->
          let ps = parser_of_symbol entry nlevn s in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn s son in
          (fun gstate (strm__ : _ LStream.t) ->
             let bp = locate_pos strm__ in
             let* a = ps gstate strm__ in
             p1 gstate bp a strm__)
  | Node (_, {node = s; son = son; brother = bro}) ->
          let ps = parser_of_symbol entry nlevn s in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn s son in
          let p2 = parser_of_tree entry nlevn alevn bro in
          (fun gstate (strm : _ LStream.t) ->
             let bp = locate_pos strm in
             match ps gstate strm with
             | Ok a -> p1 gstate bp a strm
             | Error () -> p2 gstate strm)

and parser_cont : type s tr tr' a r.
  (GState.t -> (a -> r) parser_t) -> s ty_entry -> int -> int -> (s, tr, a) ty_symbol -> (s, tr', a -> r) ty_tree -> GState.t -> position -> a -> _ -> r parser_v =
  fun p1 entry nlevn alevn s son gstate bp a0 (strm__ : _ LStream.t) ->
  match p1 gstate strm__ with
  | Ok v -> Ok (v a0)
  | Error () ->
    let fail a = raise (ParseError (tree_failed entry a s son)) in
    let or_fail a x = match x with Ok x -> x | Error () -> fail a in
    (* Recover from a success on [s] with result [a] followed by a
        failure on [son] in a rule of the form [a = s; son] *)
    (* Discard the rule if what has been consumed before failing is
       the empty sequence (due to some OPT or LIST0); example:
       « OPT "!"; ident » fails to see an ident and the OPT was resolved
       into the empty sequence, with application e.g. to being able to
       safely write « LIST1 [ OPT "!"; id = ident -> id] ». *)
    if LStream.count strm__ == LStream.pos_offset bp then Error ()
    else if not gstate.recover then fail a0
    else
      (* Try to replay the son with the top occurrence of NEXT (by
         default at level nlevn) and trailing SELF (by default at alevn)
         replaced with self at top level;
         This allows for instance to recover from a failure on the
         second SELF of « SELF; "\/"; SELF » by doing as if it were
         « SELF; "\/"; same-entry-at-top-level » with application e.g. to
         accept "A \/ forall x, x = x" w/o requiring the expected
         parentheses as in "A \/ (forall x, x = x)". *)
      match let* top = top_tree entry son in parser_of_tree entry nlevn alevn top gstate strm__ with
      | Ok a ->
        warn_recover entry.ename bp strm__;
        Ok (a a0)
      | Error () ->
        (* In case of success on just SELF, NEXT or an explicit call to
           a subentry followed by a failure on the rest (son), retry
           parsing as if this entry had been called at its toplevel;
           example: « "{"; entry-at-some-level; "}" » fails on "}" and
           is retried with « "{"; same-entry-at-top-level; "}" », allowing
           e.g. to parse « {1 + 1} » while « {(1 + 1)} » would
           have been expected according to the level. *)
        let p1 = parser_of_tree entry nlevn alevn son in
        let a =
          let* s' = entry_of_symb entry s in
          continue_parser_of_entry gstate s' None 0 bp a0 strm__
        in
        let ep = locate_pos strm__ in
        let a = or_fail a0 a in
        let act = or_fail a (p1 gstate strm__) in
        warn_recover entry.ename bp ~ep strm__;
        Ok (act a)

(** [parser_of_token_list] attempts to look-ahead an arbitrary-long
finite sequence of tokens. E.g., in
[ [ "foo"; "bar1"; "bar3"; ... -> action1
  | "foo"; "bar2"; ... -> action2
  | other-rules ] ]
compiled as:
[ [ "foo"; ["bar1"; "bar3"; ... -> action1
           |"bar2"; ... -> action2]
  | other-rules ] ]
this is able to look ahead "foo"; "bar1"; "bar3" and if not found
"foo"; "bar1", then, if still not found, "foo"; "bar2" _without_
consuming the tokens until it is sure that a longest chain of tokens
(before finding non-terminals or the end of the production) is found
(and backtracking to [other-rules] if no such longest chain can be
found). *)
and parser_of_token_list : type s tr lt r.
  s ty_entry -> int -> int -> lt pattern -> (s, tr, lt -> r) ty_tree -> GState.t -> r parser_t =
  fun entry nlevn alevn tok tree ->
  let rec loop : type tr lt r. int -> lt pattern -> (s, tr, r) ty_tree -> GState.t -> lt -> r parser_t =
    fun n last_tok tree -> match tree with
    | Node (_, {node = Stoken tok; son = son; brother = bro}) ->
       let p2 = loop n last_tok bro in
       let p1 = loop (n+1) tok son in
       fun gstate last_a strm ->
        (match Option.bind (LStream.peek_nth gstate.kwstate n strm) (L.tok_match tok) with
         | Some a ->
           (match p1 gstate a strm with
            | Ok act -> Ok (act a)
            | Error () ->
              (try p2 gstate last_a strm
               with TokenListFailed _ -> raise (TokenListFailed (entry, a, Stoken tok, son))))
         | None ->
            (try p2 gstate last_a strm
             with TokenListFailed _ -> raise (TokenListFailed (entry, last_a, Stoken last_tok, tree))))
    | DeadEnd -> fun gstate last_a strm -> Error ()
    | _ ->
       let ps = parser_of_tree entry nlevn alevn tree in
       fun gstate last_a strm ->
         for _i = 1 to n do LStream.junk gstate.kwstate strm done;
         let v = ps gstate strm in
         let v =
           if not gstate.recover then v else
             v <+> fun () ->
               (* Tolerance: retry w/o granting the level constraint (see recover) *)
               let bp = locate_pos strm in
               let* top = top_tree entry tree in
               let+ a = parser_of_tree entry nlevn alevn top gstate strm in
               warn_recover entry.ename bp strm;
               a
         in
         match v with
         | Ok v -> Ok v
         | Error () -> raise (TokenListFailed (entry, last_a, (Stoken last_tok), tree))
  in
  let ps = loop 1 tok tree in
  fun gstate strm ->
    match LStream.peek gstate.kwstate strm with
    | Some tok' ->
      (match L.tok_match tok tok' with
       | Some a ->
         begin
           try let+ act = ps gstate a strm in act a
           with TokenListFailed (entry, a, tok, tree) ->
             raise (ParseError (tree_failed entry a tok tree))
         end
       | None -> Error ())
    | None -> Error ()
and parser_of_symbol : type s tr a.
  s ty_entry -> int -> (s, tr, a) ty_symbol -> GState.t -> a parser_t =
  fun entry nlevn ->
  function
  | Slist0 s ->
      let ps = parser_of_symbol entry nlevn s in
      let rec loop gstate al (strm__ : _ LStream.t) =
        match ps gstate strm__ with
        | Ok a -> loop gstate (a::al) strm__
        | Error () -> al
      in
      (fun gstate (strm__ : _ LStream.t) ->
         let a = loop gstate [] strm__ in Ok (List.rev a))
  | Slist0sep (symb, sep) ->
      let ps = parser_of_symbol entry nlevn symb in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont gstate al (strm__ : _ LStream.t) =
        match pt gstate strm__ with
        | Ok v ->
            let a = match ps gstate strm__ with
              | Ok a -> a
              | Error () ->
                raise (ParseError (symb_failed entry v sep symb))
            in
            kont gstate (a::al) strm__
        | Error () -> al
      in
      (fun gstate (strm__ : _ LStream.t) ->
         match ps gstate strm__ with
         | Ok a -> let a = kont gstate [a] strm__ in Ok (List.rev a)
         | Error () -> Ok [])
  | Slist1 s ->
      let ps = parser_of_symbol entry nlevn s in
      let rec loop gstate al (strm__ : _ LStream.t) =
        match ps gstate strm__ with
        | Ok a -> loop gstate (a::al) strm__
        | Error () -> al
      in
      (fun gstate (strm__ : _ LStream.t) ->
         let* a = ps gstate strm__ in
         let a = loop gstate [a] strm__ in Ok (List.rev a))
  | Slist1sep (symb, sep) ->
      let ps = parser_of_symbol entry nlevn symb in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont gstate al (strm__ : _ LStream.t) =
        match pt gstate strm__ with
        | Ok v ->
          let* a =
            match ps gstate strm__ with
            | Ok a -> Ok a
            | Error () ->
              if not gstate.recover then Error () else
                let bp = locate_pos strm__ in
                let a =
                  match
                    let* top = top_symb entry symb in
                    parser_of_symbol entry 0 top gstate strm__
                  with
                  | Ok a -> a
                  | Error () ->
                    raise (ParseError (symb_failed entry v sep symb))
                in
                let () = warn_recover entry.ename bp strm__ in
                Ok a
          in
          kont gstate (a::al) strm__
        | Error () -> Ok al
      in
      (fun gstate (strm__ : _ LStream.t) ->
         let* a = ps gstate strm__ in
         let+ a = kont gstate [a] strm__ in List.rev a)
  | Sopt s ->
      let ps = parser_of_symbol entry nlevn s in
      (fun gstate (strm__ : _ LStream.t) ->
         match ps gstate strm__ with
         | Ok a -> Ok (Some a)
         | Error () -> Ok None)
  | Stree t ->
      let pt = parser_of_tree entry 1 0 t in
      (fun gstate (strm__ : _ LStream.t) ->
         let bp = locate_pos strm__ in
         let+ a = pt gstate strm__ in
         let ep = locate_pos strm__ in
         let loc = interval_loc bp ep in a loc)
  | Snterm e -> (fun gstate (strm__ : _ LStream.t) -> start_parser_of_entry gstate e 0 strm__)
  | Snterml (e, l) ->
    (fun gstate (strm__ : _ LStream.t) ->
       start_parser_of_entry gstate e (level_number (get_entry gstate.estate e) l) strm__)
  | Sself -> (fun gstate (strm__ : _ LStream.t) -> start_parser_of_entry gstate entry 0 strm__)
  | Snext -> (fun gstate (strm__ : _ LStream.t) -> start_parser_of_entry gstate entry nlevn strm__)
  | Stoken tok -> let p = parser_of_token entry tok in (fun gstate strm -> p gstate.kwstate strm)
  | Stokens tokl -> let p = parser_of_tokens entry tokl in (fun gstate strm -> p gstate.kwstate strm)
and parser_of_token : type s a.
  s ty_entry -> a pattern -> L.keyword_state -> a parser_t =
  fun entry tok ->
  let f = L.tok_match tok in
  fun kwstate strm ->
    match LStream.peek kwstate strm with
    | Some tok ->
      (match f tok with
       | Some r -> LStream.junk kwstate strm; Ok r
       | None -> Error ())
    | None -> Error ()
and parser_of_tokens : type s.
  s ty_entry -> ty_pattern list -> L.keyword_state -> unit parser_t =
  fun entry tokl ->
  let rec loop n = function
  | [] -> fun kwstate strm -> for _i = 1 to n do LStream.junk kwstate strm done; Ok ()
  | TPattern tok :: tokl ->
     fun kwstate strm ->
       let tok' = LStream.peek_nth kwstate n strm in
       match Option.bind tok' (L.tok_match tok) with
       | Some _ -> loop (n+1) tokl kwstate strm
       | None -> Error ()
  in
  loop 0 tokl

(** [start_parser_of_levels entry clevn levels levn strm] goes
    top-down from level [clevn] to the last level, ignoring rules
    between [levn] and [clevn], as if starting from
    [max(clevn,levn)]. On each rule of the form [prefix] (where
    [prefix] is a rule not starting with [SELF]), it tries to consume
    the stream [strm].

    The interesting case is [entry.estart] which is
    [start_parser_of_levels entry 0 entry.edesc], thus practically
    going from [levn] to the end.

    More schematically, assuming each level has the normalized form

    level n: [ a = SELF; b = suffix_tree_n -> action_n(a,b)
             | a = prefix_tree_n -> action'_n(a) ]

    then the main loop does the following:

    estart n =
      if prefix_tree_n matches the stream as a then econtinue n (action'_n(a))
      else start (n+1)

    econtinue n a =
      if suffix_tree_n matches the stream as b then econtinue n (action_n(a,b))
      else if n=0 then a else econtinue (n-1) a
*)

let rec start_parser_of_levels entry clevn =
  function
    [] -> (fun _gstate levn (strm__ : _ LStream.t) -> Error ())
  | Level lev :: levs ->
      let p1 = start_parser_of_levels entry (succ clevn) levs in
      match lev.lprefix with
        DeadEnd -> p1
      | tree ->
          let alevn = if self_on_the_right lev.assoc then clevn else succ clevn in
          let p2 = parser_of_tree entry (succ clevn) alevn tree in
          match levs with
            [] ->
              (fun gstate levn strm ->
                (* Recovery here means that a grammar entry e: [[ "x"; a = e | "y" ]]
                   works even though it should be: e: [RIGHTA[ "x"; a = e | "y" ]] *)
                if not gstate.recover && levn > clevn then Error ()
                else
                 let (strm__ : _ LStream.t) = strm in
                 let bp = locate_pos strm__ in
                 let* act = p2 gstate strm__ in
                 let ep = locate_pos strm__ in
                 let a = act (interval_loc bp ep) in
                 let () = if levn > clevn then
                     warn_recover_last_start entry.ename bp ep strm__
                 in
                 continue_parser_of_entry gstate entry (Some clevn) levn bp a strm)
          | _ ->
              fun gstate levn strm ->
                if levn > clevn then
                  (* Skip rules before [levn] *)
                  p1 gstate levn strm
                else
                  let (strm__ : _ LStream.t) = strm in
                  let bp = locate_pos strm__ in
                  match p2 gstate strm__ with
                  | Ok act ->
                      let ep = locate_pos strm__ in
                      let a = act (interval_loc bp ep) in
                      continue_parser_of_entry gstate entry (Some clevn) levn bp a strm
                  | Error () -> p1 gstate levn strm__

(** [continue_parser_of_levels entry clevn levels levn bp a strm] goes
    bottom-up from the last level to level [clevn], ignoring rules
    between [levn] and [clevn], as if stopping at [max(clevn,levn)].
    It tries to consume the stream [strm] on the suffix of rules of
    the form [SELF; suffix] knowing that [a] is what consumed [SELF]
    at level [levn] (or [levn+1] depending on associativity).

    The interesting case is [entry.econtinue levn bp a] which is [try
    continue_parser_of_levels entry 0 entry.edesc levn bp a with
    Failure -> a], thus practically going from the end to [levn].
*)
let rec continue_parser_of_levels entry clevn =
  function
    [] -> (fun _gstate levfrom levn bp a (strm__ : _ LStream.t) -> Error ())
  | Level lev :: levs ->
      let p1 = continue_parser_of_levels entry (succ clevn) levs in
      match lev.lsuffix with
        DeadEnd -> p1
      | tree ->
          let alevn = if self_on_the_right lev.assoc then clevn else succ clevn in
          let p2 = parser_of_tree entry (succ clevn) alevn tree in
          fun gstate levfrom levn bp a strm ->
            let tolerance = match levfrom with
              | Some levfrom when levfrom = clevn && not (self_on_the_left lev.assoc) -> Some true
              | Some levfrom when levfrom < clevn -> Some false
              | _ -> None
            in
            (* Apply the lsuffix continuation if the level is in the interval [levn;levfrom] *)
            if levn > clevn then
              (* Skip rules before [levn] *)
              p1 gstate levfrom levn bp a strm
            else if (not gstate.recover && Option.has_some tolerance) then
              Error ()
            else
              let (strm__ : _ LStream.t) = strm in
              let ep = locate_pos strm__ in
              let+ c = p1 gstate levfrom levn bp a strm__ <+> fun () ->
                  let* act = p2 gstate strm__ in
                  let ep = locate_pos strm__ in
                  let a = act a (interval_loc bp ep) in
                  if gstate.has_non_assoc && lev.assoc = NonA then
                    if clevn = levn then
                      Ok a
                    else
                      continue_parser_of_entry gstate entry (Some (clevn-1)) levn bp a strm
                  else
                    continue_parser_of_entry gstate entry (Some clevn) levn bp a strm in
              let () = Option.iter (warn_recover_continuation entry.ename bp ep strm__) tolerance in
              c

(* Don't use Lazy because if it gets interrupted it is unrecoverable *)
let lazy_fun f =
  let r = ref None in
  fun () ->
    match !r with
    | Some f -> f
    | None ->
      let f = f () in
      r := Some f;
      f

let make_continue_parser_of_entry entry = function
  | [] -> (fun _ _ _ _ _ (_ : _ LStream.t) -> Error ())
  | elev ->
    let p = lazy_fun (fun () -> continue_parser_of_levels entry 0 elev) in
    (fun gstate levfrom levn bp a (strm__ : _ LStream.t) ->
       p () gstate levfrom levn bp a strm__ <+> fun () -> Ok a)

let make_start_parser_of_entry entry = function
  | [] -> empty_entry entry.ename
  | elev ->
    let p = lazy_fun (fun () -> start_parser_of_levels entry 0 elev) in
    (fun gstate levn (strm:_ LStream.t) -> p () gstate levn strm)

let make_entry_data entry elev = {
  eentry = entry;
  edesc = Dlevels elev;
  estart = make_start_parser_of_entry entry elev;
  econtinue = make_continue_parser_of_entry entry elev;
}

(* Extend syntax *)

let modify_entry estate e f = try EState.modify (DMap.tag_of_onetag e.etag) f estate
  with Not_found -> CErrors.anomaly Pp.(str "modify_entry: " ++ str e.ename ++ str " not found")

let add_entry otag estate e v =
  assert (not (EState.mem (DMap.tag_of_onetag e.etag) estate));
  EState.add otag v estate

let extend_entry estate entry statement =
  let estate = modify_entry estate entry (fun edata ->
      let elev = levels_of_rules entry edata statement in
      make_entry_data entry elev)
  in
  estate

(* Normal interface *)

module Parsable = struct

  type t =
    { pa_tok_strm : (L.keyword_state,L.te) LStream.t
    ; lexer_state : L.State.t ref }

  let parse_parsable gstate entry p =
    let efun = start_parser_of_entry gstate entry 0 in
    let ts = p.pa_tok_strm in
    let get_parsing_loc () =
      (* Build the loc spanning from just after what is consumed (count)
         up to the further token known to have been read (max_peek).
         Being a parsing error, there needs to be a next token that
         caused the failure, except when the rule is empty (e.g. an
         empty custom entry); thus, we need to ensure that the token
         at location cnt has been peeked (which in turn ensures that
         the max peek is at least the current position) *)
      let _ = LStream.peek gstate.kwstate ts in
      let loc' = LStream.max_peek_loc ts in
      let loc = LStream.get_relative_loc 0 ts in
      Loc.merge loc loc'
    in
    match efun ts with
    | Ok v -> v
    | Error () ->
      let loc = get_parsing_loc () in
      let exn = ParseError ("illegal begin of " ^ entry.ename) in
      Loc.raise ~loc exn
    | exception (ParseError _ as exn) ->
      let exn, info = Exninfo.capture exn in
      let loc = get_parsing_loc () in
      let info = Loc.add_loc info loc in
      Exninfo.iraise (exn, info)
    | exception exc ->
      (* An error produced by the evaluation of the right-hand side *)
      (* of a rule, or a signal such as Sys.Break; we leave to the *)
      (* error the responsibility of locating itself *)
      let exc,info = Exninfo.capture exc in
      Exninfo.iraise (exc,info)

  let parse_parsable gstate e p =
    L.State.set !(p.lexer_state);
    try
      let c = parse_parsable gstate e p in
      p.lexer_state := L.State.get ();
      c
    with exn ->
      let exn,info = Exninfo.capture exn in
      L.State.drop ();
      Exninfo.iraise (exn,info)

  let make ?loc cs =
    let lexer_state = ref (L.State.init ()) in
    L.State.set !lexer_state;
    let ts = L.tok_func ?loc cs in
    lexer_state := L.State.get ();
    {pa_tok_strm = ts; lexer_state}

  let comments p = L.State.get_comments !(p.lexer_state)

  let drop_comments p = p.lexer_state := L.State.drop_comments !(p.lexer_state)

  let loc t = LStream.current_loc t.pa_tok_strm
  let consume { pa_tok_strm } len kwstate = LStream.njunk kwstate len pa_tok_strm
end

module Entry = struct
  type 'a t = 'a ty_entry

  let fresh n =
    let etag = DMap.make () in
    { ename = n; etag }, etag

  let empty_entry_val e = {
    eentry = e;
    edesc = Dlevels [];
    estart = empty_entry e.ename;
    econtinue = (fun _ _ _ _ _ (strm__ : _ LStream.t) -> assert false);
  }

  let make n estate =
    let e, otag = fresh n in
    let estate = add_entry otag estate e (empty_entry_val e)
    in
    estate, e

  let parse (e : 'a t) p gstate : 'a =
    Parsable.parse_parsable gstate e p
  let parse_token_stream (e : 'a t) ts gstate : 'a parser_v =
    start_parser_of_entry gstate e 0 ts
  let name e = e.ename

  type 'a parser_fun = { parser_fun : L.keyword_state -> (L.keyword_state,te) LStream.t -> 'a parser_v }
  let of_parser_val e { parser_fun = p } = {
    eentry = e;
    estart = (fun gstate _ (strm:_ LStream.t) -> p gstate.kwstate strm);
    econtinue = (fun _ _ _ _ _ (strm__ : _ LStream.t) -> Error ());
    edesc = Dparser p;
  }
  let of_parser n p estate =
    let e, otag = fresh n in
    let estate = add_entry otag estate e (of_parser_val e p) in
    estate, e

  let print ~flatten ppf e estate kwstate = fprintf ppf "%a@." (print_entry ~flatten estate kwstate) e

  let is_empty e estate = match (get_entry estate e).edesc with
  | Dparser _ -> failwith "Arbitrary parser entry"
  | Dlevels elev -> List.is_empty elev

  type any_t = Any : 'a t -> any_t

  let rec iter_in_symbols : _ -> ex_symbols -> unit = fun f symbols ->
    match symbols with
    | ExNil -> ()
    | ExCns (symbol, symbols) ->
      iter_in_symbol f symbol;
      List.iter (iter_in_symbols f) symbols

  and iter_in_symbol : type s tr r. _ -> (s, tr, r) ty_symbol -> unit = fun f ->
    function
    | Snterml (e, _) | Snterm e -> f (Any e)
    | Slist0 s -> iter_in_symbol f s
    | Slist0sep (s, t) -> iter_in_symbol f s; iter_in_symbol f t
    | Slist1 s -> iter_in_symbol f s
    | Slist1sep (s, t) -> iter_in_symbol f s; iter_in_symbol f t
    | Sopt s -> iter_in_symbol f s
    | Stoken _ | Stokens _ -> ()
    | Sself | Snext -> ()
    | Stree t -> List.iter (fun rule -> iter_in_symbols f rule) (ex_tree ~flatten:false t)

  let iter_in estate f e = match (get_entry estate e).edesc with
    | Dparser _ -> ()
    | Dlevels elev ->
      List.iter (fun (Level lev) ->
          let rules = ex_level ~flatten:false lev in
          List.iter (fun rule -> iter_in_symbols f rule) rules)
        elev

  let same_entry (Any e) (Any e') = Option.has_some (eq_entry e e')

  let all_in () estate =
    let add_entry (Any e as a) acc = String.Map.update e.ename (function
        | None -> Some [a]
        | Some l -> Some (a::l))
        acc
    in
    EState.fold { fold = fun _ data acc -> add_entry (Any data.eentry) acc} estate String.Map.empty

  let accumulate_in initial estate =
    let add_visited visited (Any e as any) =
      String.Map.update e.ename (function
          | None -> Some [any]
          | Some vl as v ->
            if List.mem_f same_entry any vl then v else Some (any :: vl))
        visited
    in
    let todo = ref initial in
    let visited = List.fold_left add_visited String.Map.empty initial in
    let visited = ref visited in
    while not (List.is_empty !todo) do
      let Any e = List.hd !todo in
      todo := List.tl !todo;
      iter_in estate (fun (Any e as any) ->
          let visited' = add_visited !visited any in
          if not (!visited == visited') then begin
            visited := visited';
            todo := any :: !todo
          end)
        e
    done;
    !visited
end

module rec Symbol : sig

  type ('self, 'trec, 'a) t = ('self, 'trec, 'a) ty_symbol

  val nterm : 'a Entry.t -> ('self, norec, 'a) t
  val nterml : 'a Entry.t -> string -> ('self, norec, 'a) t
  val list0 : ('self, 'trec, 'a) t -> ('self, 'trec, 'a list) t
  val list0sep :
    ('self, 'trec, 'a) t -> ('self, norec, unit) t ->
    ('self, 'trec, 'a list) t
  val list1 : ('self, 'trec, 'a) t -> ('self, 'trec, 'a list) t
  val list1sep :
    ('self, 'trec, 'a) t -> ('self, norec, unit) t ->
    ('self, 'trec, 'a list) t
  val opt : ('self, 'trec, 'a) t -> ('self, 'trec, 'a option) t
  val self : ('self, mayrec, 'self) t
  val next : ('self, mayrec, 'self) t
  val token : 'c pattern -> ('self, norec, 'c) t
  val tokens : ty_pattern list -> ('self, norec, unit) t
  val rules : 'a Rules.t list -> ('self, norec, 'a) t

end = struct

  type ('self, 'trec, 'a) t = ('self, 'trec, 'a) ty_symbol
  let nterm e = Snterm e
  let nterml e l = Snterml (e, l)
  let list0 s = Slist0 s
  let list0sep s sep = Slist0sep (s, sep)
  let list1 s = Slist1 s
  let list1sep s sep = Slist1sep (s, sep)
  let opt s = Sopt s
  let self = Sself
  let next = Snext
  let token tok = Stoken tok
  let tokens tokl = Stokens tokl
  let rules (t : 'a Rules.t list) = srules t

end and Rule : sig

  type ('self, 'trec, 'f, 'r) t = ('self, 'trec, 'f, 'r) ty_rule

  val stop : ('self, norec, 'r, 'r) t
  val next :
    ('self, _, 'a, 'r) t -> ('self, _, 'b) Symbol.t ->
    ('self, mayrec, 'b -> 'a, 'r) t
  val next_norec :
    ('self, norec, 'a, 'r) Rule.t -> ('self, norec, 'b) Symbol.t ->
    ('self, norec, 'b -> 'a, 'r) t

end = struct

  type ('self, 'trec, 'f, 'r) t = ('self, 'trec, 'f, 'r) ty_rule

  let stop = TStop
  let next r s = TNext (MayRec2, r, s)
  let next_norec r s = TNext (NoRec2, r, s)

end and Rules : sig

  type 'a t = 'a ty_rules
  val make : (_, norec, 'f, Loc.t -> 'a) Rule.t -> 'f -> 'a t

end = struct

  type 'a t = 'a ty_rules
  let make p act = TRules (p, act)

end

module Production = struct

  type 'a t = 'a ty_production
  let make p act = TProd (p, act)

end

module Unsafe = struct
  let existing_entry estate e =
    add_entry e.etag estate e (Entry.empty_entry_val e)

  let existing_of_parser estate e p =
    add_entry e.etag estate e (Entry.of_parser_val e p)
end

let safe_extend = extend_entry

let level_of_nonterm (type rec_) (sym:(_,rec_,_) Symbol.t) = match sym with
  | Snterml (_,l) -> Some l
  | _ -> None

exception SelfSymbol

let rec generalize_symbol :
  type a tr s u. (s, tr, a) Symbol.t -> (u, norec, a) ty_symbol =
  function
  | Stoken tok ->
    Stoken tok
  | Stokens tokl ->
    Stokens tokl
  | Slist1 e ->
    Slist1 (generalize_symbol e)
  | Slist1sep (e, sep) ->
    let e = generalize_symbol e in
    let sep = generalize_symbol sep in
    Slist1sep (e, sep)
  | Slist0 e ->
    Slist0 (generalize_symbol e)
  | Slist0sep (e, sep) ->
    let e = generalize_symbol e in
    let sep = generalize_symbol sep in
    Slist0sep (e, sep)
  | Sopt e ->
    Sopt (generalize_symbol e)
  | Sself ->
    raise SelfSymbol
  | Snext ->
    raise SelfSymbol
  | Snterm e ->
    Snterm e
  | Snterml (e, l) ->
    Snterml (e, l)
  | Stree r ->
    Stree (generalize_tree r)
and generalize_tree : type a tr s u.
  (s, tr, a) ty_tree -> (u, norec, a) ty_tree = fun r ->
  match r with
  | Node (fi, n) ->
    let fi = match fi with
      | NoRec3 -> NoRec3
      | MayRec3 -> raise SelfSymbol
    in
    let n = match n with
      | { node; son; brother } ->
        let node = generalize_symbol node in
        let son = generalize_tree son in
        let brother = generalize_tree brother in
        { node; son; brother }
    in
    Node (fi, n)
  | LocAct _ as r -> r
  | DeadEnd as r -> r

let generalize_symbol s =
  try Some (generalize_symbol s)
  with SelfSymbol -> None

end
