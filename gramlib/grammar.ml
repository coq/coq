(* camlp5r *)
(* grammar.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Gramext
open Format
open Util

(* Functorial interface *)

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
    val create : string -> 'a t
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
  | Fresh of Gramext.position * 'a single_extend_statement list

  val generalize_symbol : ('a, 'tr, 'c) Symbol.t -> ('a, norec, 'c) Symbol.t option

  (* Used in custom entries, should tweak? *)
  val level_of_nonterm : ('a, norec, 'c) Symbol.t -> string option

end

module type ExtS = sig

  include S

  val safe_extend : 'a Entry.t -> 'a extend_statement -> unit
  val safe_delete_rule : 'a Entry.t -> 'a Production.t -> unit

  module Unsafe : sig
    val clear_entry : 'a Entry.t -> unit
  end

end

(* Implementation *)

module GMake (L : Plexing.S) = struct

type te = L.te
type 'c pattern = 'c L.pattern
type ty_pattern = TPattern : 'a pattern -> ty_pattern

type 'a parser_t = L.te LStream.t -> 'a

type grammar =
  { gtokens : (string * string option, int ref) Hashtbl.t }

let egram =
  { gtokens = Hashtbl.create 301 }

(** Used to propagate possible presence of SELF/NEXT in a rule (binary and) *)
type ('a, 'b, 'c) ty_and_rec =
| NoRec2 : (norec, norec, norec) ty_and_rec
| MayRec2 : ('a, 'b, mayrec) ty_and_rec

(** Used to propagate possible presence of SELF/NEXT in a tree (ternary and) *)
type ('a, 'b, 'c, 'd) ty_and_rec3 =
| NoRec3 : (norec, norec, norec, norec) ty_and_rec3
| MayRec3 : ('a, 'b, 'c, mayrec) ty_and_rec3

type 'a ty_entry = {
  ename : string;
  mutable estart : int -> 'a parser_t;
  mutable econtinue : int -> int -> 'a -> 'a parser_t;
  mutable edesc : 'a ty_desc;
}

and 'a ty_desc =
| Dlevels of 'a ty_level list
| Dparser of 'a parser_t

and 'a ty_level = Level : (_, _, 'a) ty_rec_level -> 'a ty_level

and ('trecs, 'trecp, 'a) ty_rec_level = {
  assoc : g_assoc;
  lname : string option;
  lsuffix : ('a, 'trecs, 'a -> Loc.t -> 'a) ty_tree;
  lprefix : ('a, 'trecp, Loc.t -> 'a) ty_tree;
}

and ('self, 'trec, 'a) ty_symbol =
| Stoken : 'c pattern -> ('self, norec, 'c) ty_symbol
| Stokens : ty_pattern list -> ('self, norec, unit) ty_symbol
| Slist1 : ('self, 'trec, 'a) ty_symbol -> ('self, 'trec, 'a list) ty_symbol
| Slist1sep : ('self, 'trec, 'a) ty_symbol * ('self, norec, unit) ty_symbol * bool -> ('self, 'trec, 'a list) ty_symbol
| Slist0 : ('self, 'trec, 'a) ty_symbol -> ('self, 'trec, 'a list) ty_symbol
| Slist0sep : ('self, 'trec, 'a) ty_symbol * ('self, norec, unit) ty_symbol * bool -> ('self, 'trec, 'a list) ty_symbol
| Sopt : ('self, 'trec, 'a) ty_symbol -> ('self, 'trec, 'a option) ty_symbol
| Sself : ('self, mayrec, 'self) ty_symbol
| Snext : ('self, mayrec, 'self) ty_symbol
| Snterm : 'a ty_entry -> ('self, norec, 'a) ty_symbol
    (* norec but the entry can nevertheless introduce a loop with the current entry*)
| Snterml : 'a ty_entry * string -> ('self, norec, 'a) ty_symbol
| Stree : ('self, 'trec, Loc.t -> 'a) ty_tree -> ('self, 'trec, 'a) ty_symbol

and ('self, _, _, 'r) ty_rule =
| TStop : ('self, norec, 'r, 'r) ty_rule
| TNext : ('trr, 'trs, 'tr) ty_and_rec * ('self, 'trr, 'a, 'r) ty_rule * ('self, 'trs, 'b) ty_symbol -> ('self, 'tr, 'b -> 'a, 'r) ty_rule

and ('self, 'trec, 'a) ty_tree =
| Node : ('trn, 'trs, 'trb, 'tr) ty_and_rec3 * ('self, 'trn, 'trs, 'trb, 'b, 'a) ty_node -> ('self, 'tr, 'a) ty_tree
| LocAct : 'k * 'k list -> ('self, norec, 'k) ty_tree
| DeadEnd : ('self, norec, 'k) ty_tree

and ('self, 'trec, 'trecs, 'trecb, 'a, 'r) ty_node = {
  node : ('self, 'trec, 'a) ty_symbol;
  son : ('self, 'trecs, 'a -> 'r) ty_tree;
  brother : ('self, 'trecb, 'r) ty_tree;
}

type 'a ty_rules =
| TRules : (_, norec, 'act, Loc.t -> 'a) ty_rule * 'act -> 'a ty_rules

type 'a ty_production =
| TProd : ('a, _, 'act, Loc.t -> 'a) ty_rule * 'act -> 'a ty_production

let rec derive_eps : type s r a. (s, r, a) ty_symbol -> bool =
  function
    Slist0 _ -> true
  | Slist0sep (_, _, _) -> true
  | Sopt _ -> true
  | Stree t -> tree_derive_eps t
  | Slist1 _ -> false
  | Slist1sep (_, _, _) -> false
  | Snterm _ -> false | Snterml (_, _) -> false
  | Snext -> false
  | Sself -> false
  | Stoken _ -> false
  | Stokens _ -> false
and tree_derive_eps : type s tr a. (s, tr, a) ty_tree -> bool =
  function
    LocAct (_, _) -> true
  | Node (_, {node = s; brother = bro; son = son}) ->
      derive_eps s && tree_derive_eps son || tree_derive_eps bro
  | DeadEnd -> false

(** FIXME: find a way to do that type-safely *)
let eq_entry : type a1 a2. a1 ty_entry -> a2 ty_entry -> (a1, a2) eq option = fun e1 e2 ->
  if (Obj.magic e1) == (Obj.magic e2) then Some (Obj.magic Refl)
  else None

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
  | Slist0sep (s1, sep1, b1), Slist0sep (s2, sep2, b2) ->
    if b1 = b2 then match eq_symbol s1 s2 with
    | None -> None
    | Some Refl ->
      match eq_symbol sep1 sep2 with
      | None -> None
      | Some Refl -> Some Refl
    else None
  | Slist1 s1, Slist1 s2 ->
    begin match eq_symbol s1 s2 with None -> None | Some Refl -> Some Refl end
  | Slist1sep (s1, sep1, b1), Slist1sep (s2, sep2, b2) ->
    if b1 = b2 then match eq_symbol s1 s2 with
    | None -> None
    | Some Refl ->
      match eq_symbol sep1 sep2 with
      | None -> None
      | Some Refl -> Some Refl
    else None
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
     snd (L.tok_pattern_strings p1) <> None
     && snd (L.tok_pattern_strings p2) = None
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
 * when compiling Coq and its standard library) *)
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
        | NR11, LocAct (old_action, action_list) ->
          (* What to do about this warning? For now it is disabled *)
          if false then
            begin
              let msg =
                "<W> Grammar extension: " ^
                (if entry_name = "" then "" else "in ["^entry_name^"%s], ") ^
                "some rule has been masked" in
              Feedback.msg_warning (Pp.str msg)
            end;
          LocAct (action, old_action :: action_list)
        | NR11, DeadEnd -> LocAct (action, [])
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
    | LocAct (_, _) -> None | DeadEnd -> None
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
    | LocAct (k, kl) -> LocAct (k, kl)
    | DeadEnd -> DeadEnd
  and retype_symbol : type s a. (s, norec, a) ty_symbol -> (self, norec, a) ty_symbol =
    function
    | Stoken p -> Stoken p
    | Stokens l -> Stokens l
    | Slist1 s -> Slist1 (retype_symbol s)
    | Slist1sep (s, sep, b) -> Slist1sep (retype_symbol s, retype_symbol sep, b)
    | Slist0 s -> Slist0 (retype_symbol s)
    | Slist0sep (s, sep, b) -> Slist0sep (retype_symbol s, retype_symbol sep, b)
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

let insert_token gram tok =
  L.tok_using tok;
  let r =
    let tok = L.tok_pattern_strings tok in
    try Hashtbl.find gram.gtokens tok with
      Not_found -> let r = ref 0 in Hashtbl.add gram.gtokens tok r; r
  in
  incr r

let insert_tokens gram symbols =
  let rec insert : type s trec a. (s, trec, a) ty_symbol -> unit =
    function
    | Slist0 s -> insert s
    | Slist1 s -> insert s
    | Slist0sep (s, t, _) -> insert s; insert t
    | Slist1sep (s, t, _) -> insert s; insert t
    | Sopt s -> insert s
    | Stree t -> tinsert t
    | Stoken tok -> insert_token gram tok
    | Stokens (TPattern tok::_) -> insert_token gram tok (* Only the first token is liable to trigger a keyword effect *)
    | Stokens [] -> assert false
    | Snterm _ -> () | Snterml (_, _) -> ()
    | Snext -> ()
    | Sself -> ()
  and tinsert : type s tr a. (s, tr, a) ty_tree -> unit =
    function
      Node (_, {node = s; brother = bro; son = son}) ->
        insert s; tinsert bro; tinsert son
    | LocAct (_, _) -> () | DeadEnd -> ()
  and linsert : type s tr p. (s, tr, p) ty_symbols -> unit = function
  | TNil -> ()
  | TCns (_, s, r) -> insert s; linsert r
  in
  linsert symbols

type 'a single_extend_statement =
  string option * Gramext.g_assoc option * 'a ty_production list

type 'a extend_statement =
| Reuse of string option * 'a ty_production list
| Fresh of Gramext.position * 'a single_extend_statement list

let add_prod entry lev (TProd (symbols, action)) =
  let MayRecRule symbols = change_to_self entry symbols in
  let AnyS (symbols, pf) = get_symbols symbols in
  insert_tokens egram symbols;
  insert_level entry.ename symbols pf action lev

let levels_of_rules entry st =
  let elev =
    match entry.edesc with
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

let logically_eq_symbols entry =
  let rec eq_symbols : type s1 s2 trec1 trec2 a1 a2. (s1, trec1, a1) ty_symbol -> (s2, trec2, a2) ty_symbol -> bool = fun s1 s2 ->
    match s1, s2 with
      Snterm e1, Snterm e2 -> e1.ename = e2.ename
    | Snterm e1, Sself -> e1.ename = entry.ename
    | Sself, Snterm e2 -> entry.ename = e2.ename
    | Snterml (e1, l1), Snterml (e2, l2) -> e1.ename = e2.ename && l1 = l2
    | Slist0 s1, Slist0 s2 -> eq_symbols s1 s2
    | Slist0sep (s1, sep1, b1), Slist0sep (s2, sep2, b2) ->
        eq_symbols s1 s2 && eq_symbols sep1 sep2 && b1 = b2
    | Slist1 s1, Slist1 s2 -> eq_symbols s1 s2
    | Slist1sep (s1, sep1, b1), Slist1sep (s2, sep2, b2) ->
        eq_symbols s1 s2 && eq_symbols sep1 sep2 && b1 = b2
    | Sopt s1, Sopt s2 -> eq_symbols s1 s2
    | Stree t1, Stree t2 -> eq_trees t1 t2
    | Stoken p1, Stoken p2 -> L.tok_pattern_eq p1 p2 <> None
    | Stokens pl1, Stokens pl2 -> tok_pattern_eq_list pl1 pl2 <> None
    | Sself, Sself -> true
    | Snext, Snext -> true
    | _ -> false
  and eq_trees : type s1 s2 tr1 tr2 a1 a2. (s1, tr1, a1) ty_tree -> (s2, tr2, a2) ty_tree -> bool = fun t1 t2 ->
    match t1, t2 with
      Node (_, n1), Node (_, n2) ->
        eq_symbols n1.node n2.node && eq_trees n1.son n2.son &&
        eq_trees n1.brother n2.brother
    | LocAct _, LocAct _ -> true
    | LocAct _, DeadEnd -> true
    | DeadEnd, LocAct _ -> true
    | DeadEnd, DeadEnd -> true
    | _ -> false
  in
  eq_symbols

(* [delete_rule_in_tree] returns
     [Some (dsl, t)] if success
        [dsl] =
           Some (list of deleted nodes) if branch deleted
           None if action replaced by previous version of action
        [t] = remaining tree
     [None] if failure *)

type 's ex_symbols =
| ExS : ('s, 'tr, 'p) ty_symbols -> 's ex_symbols

let delete_rule_in_tree entry =
  let rec delete_in_tree :
    type s tr tr' p r. (s, tr, p) ty_symbols -> (s, tr', r) ty_tree -> (s ex_symbols option * (s, r) ty_mayrec_tree) option =
    fun symbols tree ->
    match symbols, tree with
    | TCns (_, s, sl), Node (_, n) ->
        if logically_eq_symbols entry s n.node then delete_son sl n
        else
          begin match delete_in_tree symbols n.brother with
            Some (dsl, MayRecTree t) ->
              Some (dsl, MayRecTree (Node (MayRec3, {node = n.node; son = n.son; brother = t})))
          | None -> None
          end
    | TCns (_, s, sl), _ -> None
    | TNil, Node (_, n) ->
        begin match delete_in_tree TNil n.brother with
          Some (dsl, MayRecTree t) ->
            Some (dsl, MayRecTree (Node (MayRec3, {node = n.node; son = n.son; brother = t})))
        | None -> None
        end
    | TNil, DeadEnd -> None
    | TNil, LocAct (_, []) -> Some (Some (ExS TNil), MayRecTree DeadEnd)
    | TNil, LocAct (_, action :: list) -> Some (None, MayRecTree (LocAct (action, list)))
  and delete_son :
    type s p tr trn trs trb a r. (s, tr, p) ty_symbols -> (s, trn, trs, trb, a, r) ty_node -> (s ex_symbols option * (s, r) ty_mayrec_tree) option =
    fun sl n ->
    match delete_in_tree sl n.son with
      Some (Some (ExS dsl), MayRecTree DeadEnd) -> Some (Some (ExS (TCns (MayRec2, n.node, dsl))), MayRecTree n.brother)
    | Some (Some (ExS dsl), MayRecTree t) ->
        let t = Node (MayRec3, {node = n.node; son = t; brother = n.brother}) in
        Some (Some (ExS (TCns (MayRec2, n.node, dsl))), MayRecTree t)
    | Some (None, MayRecTree t) ->
        let t = Node (MayRec3, {node = n.node; son = t; brother = n.brother}) in
        Some (None, MayRecTree t)
    | None -> None
  in
  delete_in_tree

let decr_keyw_use_in_token gram tok =
  let tok' = L.tok_pattern_strings tok in
  let r = Hashtbl.find gram.gtokens tok' in
  decr r;
  if !r == 0 then
    begin
      Hashtbl.remove gram.gtokens tok';
      L.tok_removing tok
    end

let rec decr_keyw_use : type s tr a. _ -> (s, tr, a) ty_symbol -> unit = fun gram ->
  function
    Stoken tok -> decr_keyw_use_in_token gram tok
  | Stokens (TPattern tok :: _) -> decr_keyw_use_in_token gram tok
  | Stokens [] -> assert false
  | Slist0 s -> decr_keyw_use gram s
  | Slist1 s -> decr_keyw_use gram s
  | Slist0sep (s1, s2, _) -> decr_keyw_use gram s1; decr_keyw_use gram s2
  | Slist1sep (s1, s2, _) -> decr_keyw_use gram s1; decr_keyw_use gram s2
  | Sopt s -> decr_keyw_use gram s
  | Stree t -> decr_keyw_use_in_tree gram t
  | Sself -> ()
  | Snext -> ()
  | Snterm _ -> () | Snterml (_, _) -> ()
and decr_keyw_use_in_tree : type s tr a. _ -> (s, tr, a) ty_tree -> unit = fun gram ->
  function
    DeadEnd -> () | LocAct (_, _) -> ()
  | Node (_, n) ->
      decr_keyw_use gram n.node;
      decr_keyw_use_in_tree gram n.son;
      decr_keyw_use_in_tree gram n.brother
and decr_keyw_use_in_list : type s tr p. _ -> (s, tr, p) ty_symbols -> unit = fun gram ->
  function
  | TNil -> ()
  | TCns (_, s, l) -> decr_keyw_use gram s; decr_keyw_use_in_list gram l

let rec delete_rule_in_suffix entry symbols =
  function
    Level lev :: levs ->
      begin match delete_rule_in_tree entry symbols lev.lsuffix with
        Some (dsl, MayRecTree t) ->
          begin match dsl with
            Some (ExS dsl) -> decr_keyw_use_in_list egram dsl
          | None -> ()
          end;
          begin match t, lev.lprefix with
            DeadEnd, DeadEnd -> levs
          | _ ->
              let lev =
                {assoc = lev.assoc; lname = lev.lname; lsuffix = t;
                 lprefix = lev.lprefix}
              in
              Level lev :: levs
          end
      | None ->
          let levs = delete_rule_in_suffix entry symbols levs in
          Level lev :: levs
      end
  | [] -> raise Not_found

let rec delete_rule_in_prefix entry symbols =
  function
    Level lev :: levs ->
      begin match delete_rule_in_tree entry symbols lev.lprefix with
        Some (dsl, MayRecTree t) ->
          begin match dsl with
            Some (ExS dsl) -> decr_keyw_use_in_list egram dsl
          | None -> ()
          end;
          begin match t, lev.lsuffix with
            DeadEnd, DeadEnd -> levs
          | _ ->
              let lev =
                {assoc = lev.assoc; lname = lev.lname; lsuffix = lev.lsuffix;
                 lprefix = t}
              in
              Level lev :: levs
          end
      | None ->
          let levs = delete_rule_in_prefix entry symbols levs in
          Level lev :: levs
      end
  | [] -> raise Not_found

let delete_rule_in_level_list (type s tr p) (entry : s ty_entry) (symbols : (s, tr, p) ty_symbols) levs =
  match symbols with
    TCns (_, Sself, symbols) -> delete_rule_in_suffix entry symbols levs
  | TCns (_, Snterm e, symbols') ->
    begin match eq_entry e entry with
    | None -> delete_rule_in_prefix entry symbols levs
    | Some Refl ->
      delete_rule_in_suffix entry symbols' levs
    end
  | _ -> delete_rule_in_prefix entry symbols levs

let rec flatten_tree : type s tr a. (s, tr, a) ty_tree -> s ex_symbols list =
  function
    DeadEnd -> []
  | LocAct (_, _) -> [ExS TNil]
  | Node (_, {node = n; brother = b; son = s}) ->
      List.map (fun (ExS l) -> ExS (TCns (MayRec2, n, l))) (flatten_tree s) @ flatten_tree b

let utf8_print = ref true

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

let string_escaped s =
  if !utf8_print then utf8_string_escaped s else String.escaped s

let print_str ppf s = fprintf ppf "\"%s\"" (string_escaped s)

let print_token b ppf p =
  match L.tok_pattern_strings p with
  | "", Some s -> print_str ppf s
  | con, Some prm -> if b then fprintf ppf "%s@ %a" con print_str prm else fprintf ppf "(%s@ %a)" con print_str prm
  | con, None -> fprintf ppf "%s" con

let print_tokens ppf = function
  | [] -> assert false
  | TPattern p :: pl ->
    fprintf ppf "[%a%a]"
    (print_token true) p
    (fun ppf -> List.iter (function TPattern p -> fprintf ppf ";@ "; print_token true ppf p))
    pl

let rec print_symbol : type s tr r. formatter -> (s, tr, r) ty_symbol -> unit =
  fun ppf ->
  function
  | Slist0 s -> fprintf ppf "LIST0 %a" print_symbol1 s
  | Slist0sep (s, t, osep) ->
      fprintf ppf "LIST0 %a SEP %a%s" print_symbol1 s print_symbol1 t
        (if osep then " OPT_SEP" else "")
  | Slist1 s -> fprintf ppf "LIST1 %a" print_symbol1 s
  | Slist1sep (s, t, osep) ->
      fprintf ppf "LIST1 %a SEP %a%s" print_symbol1 s print_symbol1 t
        (if osep then " OPT_SEP" else "")
  | Sopt s -> fprintf ppf "OPT %a" print_symbol1 s
  | Stoken p -> print_token true ppf p
  | Stokens [TPattern p] -> print_token true ppf p
  | Stokens pl -> print_tokens ppf pl
  | Snterml (e, l) ->
      fprintf ppf "%s%s@ LEVEL@ %a" e.ename ""
        print_str l
  | s -> print_symbol1 ppf s
and print_symbol1 : type s tr r. formatter -> (s, tr, r) ty_symbol -> unit =
  fun ppf ->
  function
  | Snterm e -> fprintf ppf "%s%s" e.ename ""
  | Sself -> pp_print_string ppf "SELF"
  | Snext -> pp_print_string ppf "NEXT"
  | Stoken p -> print_token false ppf p
  | Stokens [TPattern p] -> print_token false ppf p
  | Stokens pl -> print_tokens ppf pl
  | Stree t -> print_level ppf pp_print_space (flatten_tree t)
  | s ->
      fprintf ppf "(%a)" print_symbol s
and print_rule : type s tr p. formatter -> (s, tr, p) ty_symbols -> unit =
  fun ppf symbols ->
  fprintf ppf "@[<hov 0>";
  let rec fold : type s tr p. _ -> (s, tr, p) ty_symbols -> unit =
    fun sep symbols ->
    match symbols with
    | TNil -> ()
    | TCns (_, symbol, symbols) ->
      fprintf ppf "%t%a" sep print_symbol symbol;
      fold (fun ppf -> fprintf ppf ";@ ") symbols
  in
  let () = fold (fun ppf -> ()) symbols in
  fprintf ppf "@]"
and print_level : type s. _ -> _ -> s ex_symbols list -> _ =
  fun ppf pp_print_space rules ->
  fprintf ppf "@[<hov 0>[ ";
  let () =
    Format.pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "%a| " pp_print_space ())
      (fun ppf (ExS rule) -> print_rule ppf rule)
      ppf rules
  in
  fprintf ppf " ]@]"

let print_levels ppf elev =
  Format.pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@,| ")
    (fun ppf (Level lev) ->
       let rules =
         List.map (fun (ExS t) -> ExS (TCns (MayRec2, Sself, t))) (flatten_tree lev.lsuffix) @
         flatten_tree lev.lprefix
       in
       fprintf ppf "@[<hov 2>";
       begin match lev.lname with
           Some n -> fprintf ppf "%a@;<1 2>" print_str n
         | None -> ()
       end;
       begin match lev.assoc with
           LeftA -> fprintf ppf "LEFTA"
         | RightA -> fprintf ppf "RIGHTA"
         | NonA -> fprintf ppf "NONA"
       end;
       fprintf ppf "@]@;<1 2>";
       print_level ppf pp_force_newline rules)
    ppf elev

let print_entry ppf e =
  fprintf ppf "@[<v 0>[ ";
  begin match e.edesc with
    Dlevels elev -> print_levels ppf elev
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
  | Slist0sep (s, _, _) -> name_of_symbol_failed entry s
  | Slist1 s -> name_of_symbol_failed entry s
  | Slist1sep (s, _, _) -> name_of_symbol_failed entry s
  | Sopt s -> name_of_symbol_failed entry s
  | Stree t -> name_of_tree_failed entry t
  | s -> name_of_symbol entry s
and name_of_tree_failed : type s tr a. s ty_entry -> (s, tr, a) ty_tree -> _ =
  fun entry ->
  function
    Node (_, {node = s; brother = bro; son = son}) ->
      let tokl =
        match s with
          Stoken tok -> get_token_list entry tok TokNil son
        | _ -> None
      in
      begin match tokl with
        None ->
          let txt = name_of_symbol_failed entry s in
          let txt =
            match s, son with
              Sopt _, Node _ -> txt ^ " or " ^ name_of_tree_failed entry son
            | _ -> txt
          in
          let txt =
            match bro with
              DeadEnd -> txt | LocAct (_, _) -> txt
            | Node _ -> txt ^ " or " ^ name_of_tree_failed entry bro
          in
          txt
      | Some (TokTree (last_tok, _, rev_tokl)) ->
         let rec build_str : type a b. string -> (a, b) tok_list -> string =
           fun s -> function
           | TokNil -> s
           | TokCns (tok, t) -> build_str (L.tok_text tok ^ " " ^ s) t in
         build_str (L.tok_text last_tok) rev_tokl
      end
  | DeadEnd -> "???" | LocAct (_, _) -> "action"

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
    | Slist0sep (s, sep, _) ->
        begin match prev_symb_result with
          [] ->
            let txt1 = name_of_symbol_failed entry s in
            txt1 ^ " or " ^ txt ^ " expected"
        | _ ->
            let txt1 = name_of_symbol_failed entry sep in
            txt1 ^ " or " ^ txt ^ " expected"
        end
    | Slist1sep (s, sep, _) ->
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
    | _ -> txt ^ " expected after " ^ name_of_symbol_failed entry prev_symb
  in
  txt ^ " (in [" ^ entry.ename ^ "])"

let symb_failed entry prev_symb_result prev_symb symb =
  let tree = Node (MayRec3, {node = symb; brother = DeadEnd; son = DeadEnd}) in
  tree_failed entry prev_symb_result prev_symb tree

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

let rec top_symb : type s tr a. s ty_entry -> (s, tr, a) ty_symbol -> (s, norec, a) ty_symbol =
  fun entry ->
  function
    Sself -> Snterm entry
  | Snext -> Snterm entry
  | Snterml (e, _) -> Snterm e
  | Slist1sep (s, sep, b) -> Slist1sep (top_symb entry s, sep, b)
  | _ -> raise Stream.Failure

let entry_of_symb : type s tr a. s ty_entry -> (s, tr, a) ty_symbol -> a ty_entry =
  fun entry ->
  function
    Sself -> entry
  | Snext -> entry
  | Snterm e -> e
  | Snterml (e, _) -> e
  | _ -> raise Stream.Failure

let top_tree : type s tr a. s ty_entry -> (s, tr, a) ty_tree -> (s, tr, a) ty_tree =
  fun entry ->
  function
    Node (MayRec3, {node = s; brother = bro; son = son}) ->
      Node (MayRec3, {node = top_symb entry s; brother = bro; son = son})
  | Node (NoRec3, {node = s; brother = bro; son = son}) ->
      Node (NoRec3, {node = top_symb entry s; brother = bro; son = son})
  | LocAct (_, _) -> raise Stream.Failure | DeadEnd -> raise Stream.Failure

let skip_if_empty bp p strm =
  if LStream.count strm == bp then fun a -> p strm
  else raise Stream.Failure

let continue entry bp a symb son p1 (strm__ : _ LStream.t) =
  let a = (entry_of_symb entry symb).econtinue 0 bp a strm__ in
  let act =
    try p1 strm__ with
      Stream.Failure -> raise (Stream.Error (tree_failed entry a symb son))
  in
  fun _ -> act a

(** Recover from a success on [symb] with result [a] followed by a
    failure on [son] in a rule of the form [a = symb; son] *)
let do_recover parser_of_tree entry nlevn alevn bp a symb son
    (strm__ : _ LStream.t) =
  try
    (* Try to replay the son with the top occurrence of NEXT (by
       default at level nlevn) and trailing SELF (by default at alevn)
       replaced with self at top level;
       This allows for instance to recover from a failure on the
       second SELF of « SELF; "\/"; SELF » by doing as if it were
       « SELF; "\/"; same-entry-at-top-level » with application e.g. to
       accept "A \/ forall x, x = x" w/o requiring the expected
       parentheses as in "A \/ (forall x, x = x)". *)
    parser_of_tree entry nlevn alevn (top_tree entry son) strm__
  with
    Stream.Failure ->
      try
      (* Discard the rule if what has been consumed before failing is
         the empty sequence (due to some OPT or LIST0); example:
         « OPT "!"; ident » fails to see an ident and the OPT was resolved
         into the empty sequence, with application e.g. to being able to
         safely write « LIST1 [ OPT "!"; id = ident -> id] ». *)
        skip_if_empty bp (fun (strm__ : _ LStream.t) -> raise Stream.Failure)
          strm__
      with Stream.Failure ->
      (* In case of success on just SELF, NEXT or an explicit call to
         a subentry followed by a failure on the rest (son), retry
         parsing as if this entry had been called at its toplevel;
         example: « "{"; entry-at-some-level; "}" » fails on "}" and
         is retried with « "{"; same-entry-at-top-level; "}" », allowing
         e.g. to parse « {1 + 1} » while « {(1 + 1)} » would
         have been expected according to the level. *)
        continue entry bp a symb son (parser_of_tree entry nlevn alevn son)
          strm__

let recover parser_of_tree entry nlevn alevn bp a symb son strm =
  do_recover parser_of_tree entry nlevn alevn bp a symb son strm

let item_skipped = ref false

let call_and_push ps al strm =
  item_skipped := false;
  let a = ps strm in
  let al = if !item_skipped then al else a :: al in item_skipped := false; al

let token_ematch tok =
  let tematch = L.tok_match tok in
  fun tok -> tematch tok

(**
  nlevn: level for Snext
  alevn: level for recursive calls on the left-hand side of the rule (depending on associativity)
*)

let rec parser_of_tree : type s tr r. s ty_entry -> int -> int -> (s, tr, r) ty_tree -> r parser_t =
  fun entry nlevn alevn ->
  function
    DeadEnd -> (fun (strm__ : _ LStream.t) -> raise Stream.Failure)
  | LocAct (act, _) -> (fun (strm__ : _ LStream.t) -> act)
  | Node (_, {node = Sself; son = LocAct (act, _); brother = DeadEnd}) ->
      (* SELF on the right-hand side of the last rule *)
      (fun (strm__ : _ LStream.t) ->
         let a = entry.estart alevn strm__ in act a)
  | Node (_, {node = Sself; son = LocAct (act, _); brother = bro}) ->
      (* SELF on the right-hand side of a rule *)
      let p2 = parser_of_tree entry nlevn alevn bro in
      (fun (strm__ : _ LStream.t) ->
         match
           try Some (entry.estart alevn strm__) with Stream.Failure -> None
         with
           Some a -> act a
         | _ -> p2 strm__)
  | Node (_, {node = Stoken tok; son = son; brother = DeadEnd}) ->
          parser_of_token_list entry nlevn alevn tok son
  | Node (_, {node = Stoken tok; son = son; brother = bro}) ->
          let p2 = parser_of_tree entry nlevn alevn bro in
          let p1 = parser_of_token_list entry nlevn alevn tok son in
          (fun (strm__ : _ LStream.t) ->
            try p1 strm__ with Stream.Failure -> p2 strm__)
  | Node (_, {node = s; son = son; brother = DeadEnd}) ->
          let ps = parser_of_symbol entry nlevn s in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn s son in
          (fun (strm__ : _ LStream.t) ->
             let bp = LStream.count strm__ in
             let a = ps strm__ in
             let act =
               try p1 bp a strm__ with
                 Stream.Failure ->
                   raise (Stream.Error (tree_failed entry a s son))
             in
             act a)
  | Node (_, {node = s; son = son; brother = bro}) ->
          let ps = parser_of_symbol entry nlevn s in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn s son in
          let p2 = parser_of_tree entry nlevn alevn bro in
          (fun (strm : _ LStream.t) ->
             let bp = LStream.count strm in
             match try Some (ps strm) with Stream.Failure -> None with
               Some a ->
                 begin match
                   (try Some (p1 bp a strm) with Stream.Failure -> None)
                 with
                   Some act -> act a
                 | None -> raise (Stream.Error (tree_failed entry a s son))
                 end
             | None -> p2 strm)
and parser_cont : type s tr tr' a r.
  (a -> r) parser_t -> s ty_entry -> int -> int -> (s, tr, a) ty_symbol -> (s, tr', a -> r) ty_tree -> int -> a -> (a -> r) parser_t =
  fun p1 entry nlevn alevn s son bp a (strm__ : _ LStream.t) ->
  try p1 strm__ with
    Stream.Failure ->
      recover parser_of_tree entry nlevn alevn bp a s son strm__

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
  s ty_entry -> int -> int -> lt pattern -> (s, tr, lt -> r) ty_tree -> r parser_t =
  fun entry nlevn alevn tok tree ->
  let rec loop : type tr lt r. int -> lt pattern -> (s, tr, r) ty_tree -> lt -> r parser_t =
    fun n last_tok tree -> match tree with
    | Node (_, {node = Stoken tok; son = son; brother = bro}) ->
       let tematch = token_ematch tok in
       let p2 = loop n last_tok bro in
       let p1 = loop (n+1) tok son in
       fun last_a strm ->
        (match (try Some (tematch (LStream.peek_nth n strm)) with Stream.Failure -> None) with
         | Some a ->
           (match try Some (p1 a strm) with Stream.Failure -> None with
            | Some act -> act a
            | None -> p2 last_a strm)
         | None -> p2 last_a strm)
    | DeadEnd -> fun last_a strm -> raise Stream.Failure
    | _ ->
       let ps = parser_of_tree entry nlevn alevn tree in
       fun last_a strm ->
         for _i = 1 to n do LStream.junk strm done;
         match
           try Some (ps strm) with Stream.Failure ->
           (* Tolerance: retry w/o granting the level constraint (see recover) *)
           try Some (parser_of_tree entry nlevn alevn (top_tree entry tree) strm) with Stream.Failure -> None
         with
         | Some act -> act
         | None -> raise (Stream.Error (tree_failed entry last_a (Stoken last_tok) tree))
  in
  let ps = loop 1 tok tree in
  let tematch = token_ematch tok in
  fun strm ->
    match LStream.peek strm with
    | Some tok -> let a = tematch tok in let act = ps a strm in act a
    | None -> raise Stream.Failure
and parser_of_symbol : type s tr a.
  s ty_entry -> int -> (s, tr, a) ty_symbol -> a parser_t =
  fun entry nlevn ->
  function
  | Slist0 s ->
      let ps = call_and_push (parser_of_symbol entry nlevn s) in
      let rec loop al (strm__ : _ LStream.t) =
        match try Some (ps al strm__) with Stream.Failure -> None with
          Some al -> loop al strm__
        | _ -> al
      in
      (fun (strm__ : _ LStream.t) ->
         let a = loop [] strm__ in List.rev a)
  | Slist0sep (symb, sep, false) ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al (strm__ : _ LStream.t) =
        match try Some (pt strm__) with Stream.Failure -> None with
          Some v ->
            let al =
              try ps al strm__ with
                Stream.Failure ->
                  raise (Stream.Error (symb_failed entry v sep symb))
            in
            kont al strm__
        | _ -> al
      in
      (fun (strm__ : _ LStream.t) ->
         match try Some (ps [] strm__) with Stream.Failure -> None with
           Some al -> let a = kont al strm__ in List.rev a
         | _ -> [])
  | Slist0sep (symb, sep, true) ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al (strm__ : _ LStream.t) =
        match try Some (pt strm__) with Stream.Failure -> None with
          Some v ->
            begin match
              (try Some (ps al strm__) with Stream.Failure -> None)
            with
              Some al -> kont al strm__
            | _ -> al
            end
        | _ -> al
      in
      (fun (strm__ : _ LStream.t) ->
         match try Some (ps [] strm__) with Stream.Failure -> None with
           Some al -> let a = kont al strm__ in List.rev a
         | _ -> [])
  | Slist1 s ->
      let ps = call_and_push (parser_of_symbol entry nlevn s) in
      let rec loop al (strm__ : _ LStream.t) =
        match try Some (ps al strm__) with Stream.Failure -> None with
          Some al -> loop al strm__
        | _ -> al
      in
      (fun (strm__ : _ LStream.t) ->
         let al = ps [] strm__ in
         let a = loop al strm__ in List.rev a)
  | Slist1sep (symb, sep, false) ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al (strm__ : _ LStream.t) =
        match try Some (pt strm__) with Stream.Failure -> None with
          Some v ->
            let al =
              try ps al strm__ with
                Stream.Failure ->
                  let a =
                    try parse_top_symb entry symb strm__ with
                      Stream.Failure ->
                        raise (Stream.Error (symb_failed entry v sep symb))
                  in
                  a :: al
            in
            kont al strm__
        | _ -> al
      in
      (fun (strm__ : _ LStream.t) ->
         let al = ps [] strm__ in
         let a = kont al strm__ in List.rev a)
  | Slist1sep (symb, sep, true) ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al (strm__ : _ LStream.t) =
        match try Some (pt strm__) with Stream.Failure -> None with
          Some v ->
            begin match
              (try Some (ps al strm__) with Stream.Failure -> None)
            with
              Some al -> kont al strm__
            | _ ->
                match
                  try Some (parse_top_symb entry symb strm__) with
                    Stream.Failure -> None
                with
                  Some a -> kont (a :: al) strm__
                | _ -> al
            end
        | _ -> al
      in
      (fun (strm__ : _ LStream.t) ->
         let al = ps [] strm__ in
         let a = kont al strm__ in List.rev a)
  | Sopt s ->
      let ps = parser_of_symbol entry nlevn s in
      (fun (strm__ : _ LStream.t) ->
         match try Some (ps strm__) with Stream.Failure -> None with
           Some a -> Some a
         | _ -> None)
  | Stree t ->
      let pt = parser_of_tree entry 1 0 t in
      (fun (strm__ : _ LStream.t) ->
         let bp = LStream.count strm__ in
         let a = pt strm__ in
         let ep = LStream.count strm__ in
         let loc = LStream.interval_loc bp ep strm__ in a loc)
  | Snterm e -> (fun (strm__ : _ LStream.t) -> e.estart 0 strm__)
  | Snterml (e, l) ->
      (fun (strm__ : _ LStream.t) -> e.estart (level_number e l) strm__)
  | Sself -> (fun (strm__ : _ LStream.t) -> entry.estart 0 strm__)
  | Snext -> (fun (strm__ : _ LStream.t) -> entry.estart nlevn strm__)
  | Stoken tok -> parser_of_token entry tok
  | Stokens tokl -> parser_of_tokens entry tokl
and parser_of_token : type s a.
  s ty_entry -> a pattern -> a parser_t =
  fun entry tok ->
  let f = L.tok_match tok in
  fun strm ->
    match LStream.peek strm with
      Some tok -> let r = f tok in LStream.junk strm; r
    | None -> raise Stream.Failure
and parser_of_tokens : type s.
  s ty_entry -> ty_pattern list -> unit parser_t =
  fun entry tokl ->
  let rec loop n = function
  | [] -> fun strm -> for _i = 1 to n do LStream.junk strm done; ()
  | TPattern tok :: tokl ->
     let tematch = token_ematch tok in
     fun strm ->
     ignore (tematch (LStream.peek_nth n strm)); loop (n+1) tokl strm
  in
  loop 0 tokl
and parse_top_symb : type s tr a. s ty_entry -> (s, tr, a) ty_symbol -> a parser_t =
  fun entry symb ->
  parser_of_symbol entry 0 (top_symb entry symb)

(** [start_parser_of_levels entry clevn levels levn strm] goes
    top-down from level [clevn] to the last level, ignoring rules
    between [levn] and [clevn], as if starting from
    [max(clevn,levn)]. On each rule of the form [prefix] (where
    [prefix] is a rule not starting with [SELF]), it tries to consume
    the stream [strm].

    The interesting case is [entry.estart] which is
    [start_parser_of_levels entry 0 entry.edesc], thus practically
    going from [levn] to the end.

    More schematically, assuming each level has the form

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
    [] -> (fun levn (strm__ : _ LStream.t) -> raise Stream.Failure)
  | Level lev :: levs ->
      let p1 = start_parser_of_levels entry (succ clevn) levs in
      match lev.lprefix with
        DeadEnd -> p1
      | tree ->
          let alevn =
            match lev.assoc with
              LeftA | NonA -> succ clevn
            | RightA -> clevn
          in
          let p2 = parser_of_tree entry (succ clevn) alevn tree in
          match levs with
            [] ->
              (fun levn strm ->
                 (* this code should be there but is commented to preserve
                    compatibility with previous versions... with this code,
                    the grammar entry e: [[ "x"; a = e | "y" ]] should fail
                    because it should be: e: [RIGHTA[ "x"; a = e | "y" ]]...
                 if levn > clevn then match strm with parser []
                 else
                 *)
                 let (strm__ : _ LStream.t) = strm in
                 let bp = LStream.count strm__ in
                 let act = p2 strm__ in
                 let ep = LStream.count strm__ in
                 let a = act (LStream.interval_loc bp ep strm__) in
                 entry.econtinue levn bp a strm)
          | _ ->
              fun levn strm ->
                if levn > clevn then
                  (* Skip rules before [levn] *)
                  p1 levn strm
                else
                  let (strm__ : _ LStream.t) = strm in
                  let bp = LStream.count strm__ in
                  match try Some (p2 strm__) with Stream.Failure -> None with
                    Some act ->
                      let ep = LStream.count strm__ in
                      let a = act (LStream.interval_loc bp ep strm__) in
                      entry.econtinue levn bp a strm
                  | _ -> p1 levn strm__

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
    [] -> (fun levn bp a (strm__ : _ LStream.t) -> raise Stream.Failure)
  | Level lev :: levs ->
      let p1 = continue_parser_of_levels entry (succ clevn) levs in
      match lev.lsuffix with
        DeadEnd -> p1
      | tree ->
          let alevn =
            match lev.assoc with
              LeftA | NonA -> succ clevn
            | RightA -> clevn
          in
          let p2 = parser_of_tree entry (succ clevn) alevn tree in
          fun levn bp a strm ->
            if levn > clevn then
              (* Skip rules before [levn] *)
              p1 levn bp a strm
            else
              let (strm__ : _ LStream.t) = strm in
              try p1 levn bp a strm__ with
                Stream.Failure ->
                  let act = p2 strm__ in
                  let ep = LStream.count strm__ in
                  let a = act a (LStream.interval_loc bp ep strm__) in
                  entry.econtinue levn bp a strm

let continue_parser_of_entry entry =
  match entry.edesc with
    Dlevels elev ->
      let p = continue_parser_of_levels entry 0 elev in
      (fun levn bp a (strm__ : _ LStream.t) ->
         try p levn bp a strm__ with Stream.Failure -> a)
  | Dparser p -> fun levn bp a (strm__ : _ LStream.t) -> raise Stream.Failure

let empty_entry ename levn strm =
  raise (Stream.Error ("entry [" ^ ename ^ "] is empty"))

let start_parser_of_entry entry =
  match entry.edesc with
    Dlevels [] -> empty_entry entry.ename
  | Dlevels elev -> start_parser_of_levels entry 0 elev
  | Dparser p -> fun levn strm -> p strm

(* Extend syntax *)

let init_entry_functions entry =
  entry.estart <-
    (fun lev strm ->
       let f = start_parser_of_entry entry in entry.estart <- f; f lev strm);
  entry.econtinue <-
    (fun lev bp a strm ->
       let f = continue_parser_of_entry entry in
       entry.econtinue <- f; f lev bp a strm)

let extend_entry entry statement =
    let elev = levels_of_rules entry statement in
    entry.edesc <- Dlevels elev; init_entry_functions entry

(* Deleting a rule *)

let delete_rule entry sl =
  match entry.edesc with
    Dlevels levs ->
      let levs = delete_rule_in_level_list entry sl levs in
      entry.edesc <- Dlevels levs;
      entry.estart <-
        (fun lev strm ->
           let f = start_parser_of_entry entry in
           entry.estart <- f; f lev strm);
      entry.econtinue <-
        (fun lev bp a strm ->
           let f = continue_parser_of_entry entry in
           entry.econtinue <- f; f lev bp a strm)
  | Dparser _ -> ()

(* Normal interface *)

module Parsable = struct

  type t =
    { pa_tok_strm : L.te LStream.t
    ; lexer_state : L.State.t ref }

  let parse_parsable entry p =
    let efun = entry.estart 0 in
    let ts = p.pa_tok_strm in
    let get_parsing_loc () =
      (* Build the loc spanning from just after what is consumed (count)
         up to the further token known to have been read (max_peek).
         Being a parsing error, there needs to be a next token that
         caused the failure, except when the rule is empty (e.g. an
         empty custom entry); thus, we need to ensure that the token
         at location cnt has been peeked (which in turn ensures that
         the max peek is at least the current position) *)
      let _ = LStream.peek ts in
      let loc' = LStream.max_peek_loc ts in
      let loc = LStream.get_loc (LStream.count ts) ts in
      Loc.merge loc loc'
    in
    try efun ts with
      Stream.Failure ->
      let loc = get_parsing_loc () in
      Loc.raise ~loc (Stream.Error ("illegal begin of " ^ entry.ename))
    | Stream.Error _ as exc ->
      let loc = get_parsing_loc () in
      Loc.raise ~loc exc
    | exc ->
      (* An error produced by the evaluation of the right-hand side *)
      (* of a rule, or a signal such as Sys.Break; we leave to the *)
      (* error the responsibility of locating itself *)
      let exc,info = Exninfo.capture exc in
      Exninfo.iraise (exc,info)

  let parse_parsable e p =
    L.State.set !(p.lexer_state);
    try
      let c = parse_parsable e p in
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

end

module Entry = struct
  type 'a t = 'a ty_entry
  let make n =
    { ename = n; estart = empty_entry n;
      econtinue =
        (fun _ _ _ (strm__ : _ LStream.t) -> raise Stream.Failure);
      edesc = Dlevels []}
  let create = make
  let parse (e : 'a t) p : 'a =
    Parsable.parse_parsable e p
  let parse_token_stream (e : 'a t) ts : 'a =
    e.estart 0 ts
  let name e = e.ename
  type 'a parser_fun = { parser_fun : te LStream.t -> 'a }
  let of_parser n { parser_fun = (p : te LStream.t -> 'a) } : 'a t =
    { ename = n;
      estart = (fun _ -> p);
      econtinue =
        (fun _ _ _ (strm__ : _ LStream.t) -> raise Stream.Failure);
      edesc = Dparser p}
  let print ppf e = fprintf ppf "%a@." print_entry e

  let is_empty e = match e.edesc with
  | Dparser _ -> failwith "Arbitrary parser entry"
  | Dlevels elev -> List.is_empty elev
end

module rec Symbol : sig

  type ('self, 'trec, 'a) t = ('self, 'trec, 'a) ty_symbol

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

end = struct

  type ('self, 'trec, 'a) t = ('self, 'trec, 'a) ty_symbol
  let nterm e = Snterm e
  let nterml e l = Snterml (e, l)
  let list0 s = Slist0 s
  let list0sep s sep b = Slist0sep (s, sep, b)
  let list1 s = Slist1 s
  let list1sep s sep b = Slist1sep (s, sep, b)
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

  let clear_entry e =
    e.estart <- (fun _ (strm__ : _ LStream.t) -> raise Stream.Failure);
    e.econtinue <- (fun _ _ _ (strm__ : _ LStream.t) -> raise Stream.Failure);
    match e.edesc with
      Dlevels _ -> e.edesc <- Dlevels []
    | Dparser _ -> ()

end

let safe_extend (e : 'a Entry.t) data =
  extend_entry e data

let safe_delete_rule e (TProd (r,_act)) =
  let AnyS (symbols, _) = get_symbols r in
  delete_rule e symbols

let level_of_nonterm sym = match sym with
  | Snterml (_,l) -> Some l
  | _ -> None

exception SelfSymbol

let rec generalize_symbol :
  type a tr s. (s, tr, a) Symbol.t -> (s, norec, a) ty_symbol =
  function
  | Stoken tok ->
    Stoken tok
  | Stokens tokl ->
    Stokens tokl
  | Slist1 e ->
    Slist1 (generalize_symbol e)
  | Slist1sep (e, sep, b) ->
    let e = generalize_symbol e in
    let sep = generalize_symbol sep in
    Slist1sep (e, sep, b)
  | Slist0 e ->
    Slist0 (generalize_symbol e)
  | Slist0sep (e, sep, b) ->
    let e = generalize_symbol e in
    let sep = generalize_symbol sep in
    Slist0sep (e, sep, b)
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
and generalize_tree : type a tr s .
  (s, tr, a) ty_tree -> (s, norec, a) ty_tree = fun r ->
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
