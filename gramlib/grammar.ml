(* camlp5r *)
(* grammar.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Gramext
open Format
open Util

(* Functorial interface *)

module type GLexerType = Plexing.Lexer

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
        val of_parser : string -> (te Stream.t -> 'a) -> 'a e
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
    val safe_delete_rule : 'a Entry.e -> ('a, _, 'r, 'f) ty_rule -> unit
  end

(* Implementation *)

module GMake (L : GLexerType) =
struct

type te = L.te
type 'c pattern = 'c L.pattern

type 'a parser_t = L.te Stream.t -> 'a

type grammar =
  { gtokens : (string * string option, int ref) Hashtbl.t }

let egram =
  {gtokens = Hashtbl.create 301 }

let tokens con =
  let list = ref [] in
  Hashtbl.iter
    (fun (p_con, p_prm) c -> if p_con = con then list := (p_prm, !c) :: !list)
    egram.gtokens;
  !list

type ty_norec = TyNoRec
type ty_mayrec = TyMayRec

type ('a, 'b, 'c) ty_and_rec =
| NoRec2 : (ty_norec, ty_norec, ty_norec) ty_and_rec
| MayRec2 : ('a, 'b, ty_mayrec) ty_and_rec

type ('a, 'b, 'c, 'd) ty_and_rec3 =
| NoRec3 : (ty_norec, ty_norec, ty_norec, ty_norec) ty_and_rec3
| MayRec3 : ('a, 'b, 'c, ty_mayrec) ty_and_rec3

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
| Stoken : 'c pattern -> ('self, ty_norec, 'c) ty_symbol
| Slist1 : ('self, 'trec, 'a) ty_symbol -> ('self, 'trec, 'a list) ty_symbol
| Slist1sep : ('self, 'trec, 'a) ty_symbol * ('self, ty_norec, _) ty_symbol * bool -> ('self, 'trec, 'a list) ty_symbol
| Slist0 : ('self, 'trec, 'a) ty_symbol -> ('self, 'trec, 'a list) ty_symbol
| Slist0sep : ('self, 'trec, 'a) ty_symbol * ('self, ty_norec, _) ty_symbol * bool -> ('self, 'trec, 'a list) ty_symbol
| Sopt : ('self, 'trec, 'a) ty_symbol -> ('self, 'trec, 'a option) ty_symbol
| Sself : ('self, ty_mayrec, 'self) ty_symbol
| Snext : ('self, ty_mayrec, 'self) ty_symbol
| Snterm : 'a ty_entry -> ('self, ty_norec, 'a) ty_symbol
| Snterml : 'a ty_entry * string -> ('self, ty_norec, 'a) ty_symbol
| Stree : ('self, 'trec, Loc.t -> 'a) ty_tree -> ('self, 'trec, 'a) ty_symbol

and ('self, _, _, 'r) ty_rule =
| TStop : ('self, ty_norec, 'r, 'r) ty_rule
| TNext : ('trr, 'trs, 'tr) ty_and_rec * ('self, 'trr, 'a, 'r) ty_rule * ('self, 'trs, 'b) ty_symbol -> ('self, 'tr, 'b -> 'a, 'r) ty_rule

and ('self, 'trec, 'a) ty_tree =
| Node : ('trn, 'trs, 'trb, 'tr) ty_and_rec3 * ('self, 'trn, 'trs, 'trb, 'b, 'a) ty_node -> ('self, 'tr, 'a) ty_tree
| LocAct : 'k * 'k list -> ('self, ty_norec, 'k) ty_tree
| DeadEnd : ('self, ty_norec, 'k) ty_tree

and ('self, 'trec, 'trecs, 'trecb, 'a, 'r) ty_node = {
  node : ('self, 'trec, 'a) ty_symbol;
  son : ('self, 'trecs, 'a -> 'r) ty_tree;
  brother : ('self, 'trecb, 'r) ty_tree;
}

type 'a ty_rules =
| TRules : (_, ty_norec, 'act, Loc.t -> 'a) ty_rule * 'act -> 'a ty_rules

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
  | _ -> None

let is_before : type s1 s2 r1 r2 a1 a2. (s1, r1, a1) ty_symbol -> (s2, r2, a2) ty_symbol -> bool = fun s1 s2 ->
  match s1, s2 with
  | Stoken p1, Stoken p2 ->
     snd (L.tok_pattern_strings p1) <> None
     && snd (L.tok_pattern_strings p2) = None
  | Stoken _, _ -> true
  | _ -> false

(** Ancillary datatypes *)

type 'a ty_rec = MayRec : ty_mayrec ty_rec | NoRec : ty_norec ty_rec

type ('a, 'b, 'c) ty_and_ex =
| NR00 : (ty_mayrec, ty_mayrec, ty_mayrec) ty_and_ex
| NR01 : (ty_mayrec, ty_norec, ty_mayrec) ty_and_ex
| NR10 : (ty_norec, ty_mayrec, ty_mayrec) ty_and_ex
| NR11 : (ty_norec, ty_norec, ty_norec) ty_and_ex

type ('a, 'b) ty_mayrec_and_ex =
| MayRecNR : ('a, 'b, _) ty_and_ex -> ('a, 'b) ty_mayrec_and_ex

type ('s, 'a) ty_mayrec_symbol =
| MayRecSymbol : ('s, _, 'a) ty_symbol -> ('s, 'a) ty_mayrec_symbol

type ('s, 'a) ty_mayrec_tree =
| MayRecTree : ('s, 'tr, 'a) ty_tree -> ('s, 'a) ty_mayrec_tree

type ('s, 'a, 'r) ty_mayrec_rule =
| MayRecRule : ('s, _, 'a, 'r) ty_rule -> ('s, 'a, 'r) ty_mayrec_rule

type ('self, 'trec, _) ty_symbols =
| TNil : ('self, ty_norec, unit) ty_symbols
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

let insert_tree (type s trs trt tr p k a) ~warning entry_name (ar : (trs, trt, tr) ty_and_ex) (gsymbols : (s, trs, p) ty_symbols) (pf : (p, k, a) rel_prod) (action : k) (tree : (s, trt, a) ty_tree) : (s, tr, a) ty_tree =
  let rec insert : type trs trt tr p f k. (trs, trt, tr) ty_and_ex -> (s, trs, p) ty_symbols -> (p, k, f) rel_prod -> (s, trt, f) ty_tree -> k -> (s, tr, f) ty_tree  =
    fun ar symbols pf tree action ->
    match symbols, pf with
      TCns (ars, s, sl), RelS pf -> insert_in_tree ar ars s sl pf tree action
    | TNil, Rel0 ->
        let node (type tb) ({node = s; son = son; brother = bro} : (_, _, _, tb, _, _) ty_node) =
          let ar : (ty_norec, tb, tb) ty_and_ex =
            match get_rec_tree bro with MayRec -> NR10 | NoRec -> NR11 in
          {node = s; son = son; brother = insert ar TNil Rel0 bro action} in
        match ar, tree with
        | NR10, Node (_, n) -> Node (MayRec3, node n)
        | NR11, Node (NoRec3, n) -> Node (NoRec3, node n)
        | NR11, LocAct (old_action, action_list) ->
          begin match warning with
            | None -> ()
            | Some warn_fn ->
              let msg =
                "<W> Grammar extension: " ^
                (if entry_name = "" then "" else "in ["^entry_name^"%s], ") ^
                "some rule has been masked" in
              warn_fn msg
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
    fun ar ars s sl pf tree action ->
    match tree with
      Node (arn, {node = s1; son = son; brother = bro}) ->
        begin match eq_symbol s s1 with
        | Some Refl ->
          let MayRecNR arss = and_symbols_tree sl son in
          let son = insert arss sl pf son action in
          let node = {node = s1; son = son; brother = bro} in
          begin match ar, ars, arn, arss with
          | MayRec2, _, _, _ -> Some (Node (MayRec3, node))
          | NoRec2, NoRec2, NoRec3, NR11 -> Some (Node (NoRec3, node)) end
        | None ->
        let ar' = and_and_tree ar arn bro in
        if is_before s1 s || derive_eps s && not (derive_eps s1) then
          let bro =
            match try_insert ar' ars s sl pf bro action with
              Some bro -> bro
            | None ->
                let MayRecNR arss = and_symbols_tree sl DeadEnd in
                let son = insert arss sl pf DeadEnd action in
                let node = {node = s; son = son; brother = bro} in
                match ar, ars, arn, arss with
                | MayRec2, _, _, _ -> Node (MayRec3, node)
                | NoRec2, NoRec2, NoRec3, NR11 -> Node (NoRec3, node)
          in
          let node = {node = s1; son = son; brother = bro} in
          match ar, arn with
            | MayRec2, _ -> Some (Node (MayRec3, node))
            | NoRec2, NoRec3 -> Some (Node (NoRec3, node))
        else
          match try_insert ar' ars s sl pf bro action with
            Some bro ->
              let node = {node = s1; son = son; brother = bro} in
              begin match ar, arn with
                | MayRec2, _ -> Some (Node (MayRec3, node))
                | NoRec2, NoRec3 -> Some (Node (NoRec3, node)) end
          | None -> None
        end
    | LocAct (_, _) -> None | DeadEnd -> None
  in
  insert ar gsymbols pf tree action

let insert_tree_norec (type s p k a) ~warning entry_name (gsymbols : (s, ty_norec, p) ty_symbols) (pf : (p, k, a) rel_prod) (action : k) (tree : (s, ty_norec, a) ty_tree) : (s, ty_norec, a) ty_tree =
  insert_tree ~warning entry_name NR11 gsymbols pf action tree

let insert_tree (type s trs trt p k a) ~warning entry_name (gsymbols : (s, trs, p) ty_symbols) (pf : (p, k, a) rel_prod) (action : k) (tree : (s, trt, a) ty_tree) : (s, a) ty_mayrec_tree =
  let MayRecNR ar = and_symbols_tree gsymbols tree in
  MayRecTree (insert_tree ~warning entry_name ar gsymbols pf action tree)

let srules (type self a) ~warning (rl : a ty_rules list) : (self, ty_norec, a) ty_symbol =
  let rec retype_tree : type s a. (s, ty_norec, a) ty_tree -> (self, ty_norec, a) ty_tree =
    function
    | Node (NoRec3, {node = s; son = son; brother = bro}) ->
      Node (NoRec3, {node = retype_symbol s; son = retype_tree son; brother = retype_tree bro})
    | LocAct (k, kl) -> LocAct (k, kl)
    | DeadEnd -> DeadEnd
  and retype_symbol : type s a. (s, ty_norec, a) ty_symbol -> (self, ty_norec, a) ty_symbol =
    function
    | Stoken p -> Stoken p
    | Slist1 s -> Slist1 (retype_symbol s)
    | Slist1sep (s, sep, b) -> Slist1sep (retype_symbol s, retype_symbol sep, b)
    | Slist0 s -> Slist0 (retype_symbol s)
    | Slist0sep (s, sep, b) -> Slist0sep (retype_symbol s, retype_symbol sep, b)
    | Sopt s -> Sopt (retype_symbol s)
    | Snterm e -> Snterm e
    | Snterml (e, l) -> Snterml (e, l)
    | Stree t -> Stree (retype_tree t) in
  let rec retype_rule : type s k r. (s, ty_norec, k, r) ty_rule -> (self, ty_norec, k, r) ty_rule =
    function
    | TStop -> TStop
    | TNext (NoRec2, r, s) -> TNext (NoRec2, retype_rule r, retype_symbol s) in
  let t =
    List.fold_left
      (fun tree (TRules (symbols, action)) ->
        let symbols = retype_rule symbols in
        let AnyS (symbols, pf) = get_symbols symbols in
        insert_tree_norec ~warning "" symbols pf action tree)
      DeadEnd rl
  in
  Stree t

let is_level_labelled n (Level lev) =
  match lev.lname with
    Some n1 -> n = n1
  | None -> false

let insert_level (type s tr p k) ~warning entry_name (symbols : (s, tr, p) ty_symbols) (pf : (p, k, Loc.t -> s) rel_prod) (action : k) (slev : s ty_level) : s ty_level =
  match symbols with
  | TCns (_, Sself, symbols) ->
      let Level slev = slev in
      let RelS pf = pf in
      let MayRecTree lsuffix = insert_tree ~warning entry_name symbols pf action slev.lsuffix in
      Level
      {assoc = slev.assoc; lname = slev.lname;
       lsuffix = lsuffix;
       lprefix = slev.lprefix}
  | _ ->
      let Level slev = slev in
      let MayRecTree lprefix = insert_tree ~warning entry_name symbols pf action slev.lprefix in
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

let change_lev ~warning (Level lev) n lname assoc =
  let a =
    match assoc with
      None -> lev.assoc
    | Some a ->
      if a <> lev.assoc then
        begin
          match warning with
          | None -> ()
          | Some warn_fn ->
            warn_fn ("<W> Changing associativity of level \""^n^"\"")
        end;
        a
  in
  begin match lname with
    Some n ->
      if lname <> lev.lname then
        begin match warning with
          | None -> ()
          | Some warn_fn ->
            warn_fn ("<W> Level label \""^n^"\" ignored")
        end;
  | None -> ()
  end;
  Level
  {assoc = a; lname = lev.lname; lsuffix = lev.lsuffix; lprefix = lev.lprefix}

let get_level ~warning entry position levs =
  match position with
    Some First -> [], empty_lev, levs
  | Some Last -> levs, empty_lev, []
  | Some (Level n) ->
      let rec get =
        function
          [] ->
            eprintf "No level labelled \"%s\" in entry \"%s\"\n" n
              entry.ename;
            flush stderr;
            failwith "Grammar.extend"
        | lev :: levs ->
            if is_level_labelled n lev then [], change_lev ~warning lev n, levs
            else
              let (levs1, rlev, levs2) = get levs in lev :: levs1, rlev, levs2
      in
      get levs
  | Some (Before n) ->
      let rec get =
        function
          [] ->
            eprintf "No level labelled \"%s\" in entry \"%s\"\n" n
              entry.ename;
            flush stderr;
            failwith "Grammar.extend"
        | lev :: levs ->
            if is_level_labelled n lev then [], empty_lev, lev :: levs
            else
              let (levs1, rlev, levs2) = get levs in lev :: levs1, rlev, levs2
      in
      get levs
  | Some (After n) ->
      let rec get =
        function
          [] ->
            eprintf "No level labelled \"%s\" in entry \"%s\"\n" n
              entry.ename;
            flush stderr;
            failwith "Grammar.extend"
        | lev :: levs ->
            if is_level_labelled n lev then [lev], empty_lev, levs
            else
              let (levs1, rlev, levs2) = get levs in lev :: levs1, rlev, levs2
      in
      get levs
  | None ->
      match levs with
        lev :: levs -> [], change_lev ~warning lev "<top>", levs
      | [] -> [], empty_lev, []

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

let insert_tokens gram symbols =
  let rec insert : type s trec a. (s, trec, a) ty_symbol -> unit =
    function
    | Slist0 s -> insert s
    | Slist1 s -> insert s
    | Slist0sep (s, t, _) -> insert s; insert t
    | Slist1sep (s, t, _) -> insert s; insert t
    | Sopt s -> insert s
    | Stree t -> tinsert t
    | Stoken tok ->
        L.tok_using tok;
        let r =
          let tok = L.tok_pattern_strings tok in
          try Hashtbl.find gram.gtokens tok with
            Not_found -> let r = ref 0 in Hashtbl.add gram.gtokens tok r; r
        in
        incr r
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

let levels_of_rules ~warning entry position rules =
  let elev =
    match entry.edesc with
      Dlevels elev -> elev
    | Dparser _ ->
        eprintf "Error: entry not extensible: \"%s\"\n" entry.ename;
        flush stderr;
        failwith "Grammar.extend"
  in
  match rules with
  | [] -> elev
  | _ ->
    let (levs1, make_lev, levs2) = get_level ~warning entry position elev in
    let (levs, _) =
      List.fold_left
        (fun (levs, make_lev) (lname, assoc, level) ->
           let lev = make_lev lname assoc in
           let lev =
             List.fold_left
               (fun lev (TProd (symbols, action)) ->
                  let MayRecRule symbols = change_to_self entry symbols in
                  let AnyS (symbols, pf) = get_symbols symbols in
                  insert_tokens egram symbols;
                  insert_level ~warning entry.ename symbols pf action lev)
               lev level
           in
           lev :: levs, empty_lev)
        ([], make_lev) rules
    in
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

let rec decr_keyw_use : type s tr a. _ -> (s, tr, a) ty_symbol -> unit = fun gram ->
  function
    Stoken tok ->
      let tok' = L.tok_pattern_strings tok in
      let r = Hashtbl.find gram.gtokens tok' in
      decr r;
      if !r == 0 then
        begin
          Hashtbl.remove gram.gtokens tok';
          L.tok_removing tok
        end
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
  | Stoken p when L.tok_pattern_strings p <> ("", None) ->
     begin match L.tok_pattern_strings p with
     | con, Some prm -> fprintf ppf "%s@ %a" con print_str prm
     | con, None -> fprintf ppf "%s" con end
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
  | Stoken p ->
     begin match L.tok_pattern_strings p with
     | "", Some s -> print_str ppf s
     | con, None -> pp_print_string ppf con
     | con, Some prm -> fprintf ppf "(%s@ %a)" con print_str prm end
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
  let _ =
    List.fold_left
      (fun sep (ExS rule) ->
         fprintf ppf "%t%a" sep print_rule rule;
         fun ppf -> fprintf ppf "%a| " pp_print_space ())
      (fun ppf -> ()) rules ppf
  in
  fprintf ppf " ]@]"

let print_levels ppf elev =
  let _ =
    List.fold_left
      (fun sep (Level lev) ->
         let rules =
           List.map (fun (ExS t) -> ExS (TCns (MayRec2, Sself, t))) (flatten_tree lev.lsuffix) @
           flatten_tree lev.lprefix
         in
         fprintf ppf "%t@[<hov 2>" sep;
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
         print_level ppf pp_force_newline rules;
         fun ppf -> fprintf ppf "@,| ")
      (fun ppf -> ()) elev ppf
  in
  ()

let print_entry ppf e =
  fprintf ppf "@[<v 0>[ ";
  begin match e.edesc with
    Dlevels elev -> print_levels ppf elev
  | Dparser _ -> fprintf ppf "<parser>"
  end;
  fprintf ppf " ]@]"

let floc = ref (fun _ -> failwith "internal error when computing location")

let loc_of_token_interval bp ep =
  if bp == ep then
    if bp == 0 then Ploc.dummy else Ploc.after (!floc (bp - 1)) 0 1
  else
    let loc1 = !floc bp in let loc2 = !floc (pred ep) in Loc.merge loc1 loc2

let name_of_symbol : type s tr a. s ty_entry -> (s, tr, a) ty_symbol -> string =
  fun entry ->
  function
    Snterm e -> "[" ^ e.ename ^ "]"
  | Snterml (e, l) -> "[" ^ e.ename ^ " level " ^ l ^ "]"
  | Sself -> "[" ^ entry.ename ^ "]"
  | Snext -> "[" ^ entry.ename ^ "]"
  | Stoken tok -> L.tok_text tok
  | _ -> "???"

type ('r, 'f) tok_list =
| TokNil : ('f, 'f) tok_list
| TokCns : 'a pattern * ('r, 'f) tok_list -> ('a -> 'r, 'f) tok_list

type ('s, 'f) tok_tree = TokTree : 'a pattern * ('s, _, 'a -> 'r) ty_tree * ('r, 'f) tok_list -> ('s, 'f) tok_tree

let rec tok_list_length : type a b. (a, b) tok_list -> int =
  function
  | TokNil -> 0
  | TokCns (_, t) -> 1 + tok_list_length t

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
  | DeadEnd -> "???" | LocAct (_, _) -> "???"

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

let rec top_symb : type s tr a. s ty_entry -> (s, tr, a) ty_symbol -> (s, ty_norec, a) ty_symbol =
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
  if Stream.count strm == bp then fun a -> p strm
  else raise Stream.Failure

let continue entry bp a s son p1 (strm__ : _ Stream.t) =
  let a = (entry_of_symb entry s).econtinue 0 bp a strm__ in
  let act =
    try p1 strm__ with
      Stream.Failure -> raise (Stream.Error (tree_failed entry a s son))
  in
  fun _ -> act a

let do_recover parser_of_tree entry nlevn alevn bp a s son
    (strm__ : _ Stream.t) =
  try parser_of_tree entry nlevn alevn (top_tree entry son) strm__ with
    Stream.Failure ->
      try
        skip_if_empty bp (fun (strm__ : _ Stream.t) -> raise Stream.Failure)
          strm__
      with Stream.Failure ->
        continue entry bp a s son (parser_of_tree entry nlevn alevn son)
          strm__

let recover parser_of_tree entry nlevn alevn bp a s son strm =
  do_recover parser_of_tree entry nlevn alevn bp a s son strm

let token_count = ref 0

let peek_nth n strm =
  let list = Stream.npeek n strm in
  token_count := Stream.count strm + n;
  let rec loop list n =
    match list, n with
      x :: _, 1 -> Some x
    | _ :: l, n -> loop l (n - 1)
    | [], _ -> None
  in
  loop list n

let item_skipped = ref false

let call_and_push ps al strm =
  item_skipped := false;
  let a = ps strm in
  let al = if !item_skipped then al else a :: al in item_skipped := false; al

let token_ematch gram tok =
  let tematch = L.tok_match tok in
  fun tok -> tematch tok

let rec parser_of_tree : type s tr r. s ty_entry -> int -> int -> (s, tr, r) ty_tree -> r parser_t =
  fun entry nlevn alevn ->
  function
    DeadEnd -> (fun (strm__ : _ Stream.t) -> raise Stream.Failure)
  | LocAct (act, _) -> (fun (strm__ : _ Stream.t) -> act)
  | Node (_, {node = Sself; son = LocAct (act, _); brother = DeadEnd}) ->
      (fun (strm__ : _ Stream.t) ->
         let a = entry.estart alevn strm__ in act a)
  | Node (_, {node = Sself; son = LocAct (act, _); brother = bro}) ->
      let p2 = parser_of_tree entry nlevn alevn bro in
      (fun (strm__ : _ Stream.t) ->
         match
           try Some (entry.estart alevn strm__) with Stream.Failure -> None
         with
           Some a -> act a
         | _ -> p2 strm__)
  | Node (_, {node = s; son = son; brother = DeadEnd}) ->
      let tokl =
        match s with
          Stoken tok -> get_token_list entry tok TokNil son
        | _ -> None
      in
      begin match tokl with
        None ->
          let ps = parser_of_symbol entry nlevn s in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn s son in
          (fun (strm__ : _ Stream.t) ->
             let bp = Stream.count strm__ in
             let a = ps strm__ in
             let act =
               try p1 bp a strm__ with
                 Stream.Failure ->
                   raise (Stream.Error (tree_failed entry a s son))
             in
             act a)
      | Some (TokTree (last_tok, son, rev_tokl)) ->
          let lt = Stoken last_tok in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn lt son in
          parser_of_token_list entry son p1 rev_tokl last_tok
      end
  | Node (_, {node = s; son = son; brother = bro}) ->
      let tokl =
        match s with
          Stoken tok -> get_token_list entry tok TokNil son
        | _ -> None
      in
      match tokl with
        None ->
          let ps = parser_of_symbol entry nlevn s in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn s son in
          let p2 = parser_of_tree entry nlevn alevn bro in
          (fun (strm : _ Stream.t) ->
             let bp = Stream.count strm in
             match try Some (ps strm) with Stream.Failure -> None with
               Some a ->
                 begin match
                   (try Some (p1 bp a strm) with Stream.Failure -> None)
                 with
                   Some act -> act a
                 | None -> raise (Stream.Error (tree_failed entry a s son))
                 end
             | None -> p2 strm)
      | Some (TokTree (last_tok, son, rev_tokl)) ->
          let lt = Stoken last_tok in
          let p2 = parser_of_tree entry nlevn alevn bro in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn lt son in
          let p1 =
            parser_of_token_list entry son p1 rev_tokl last_tok
          in
          fun (strm__ : _ Stream.t) ->
            try p1 strm__ with Stream.Failure -> p2 strm__
and parser_cont : type s tr tr' a r.
  (a -> r) parser_t -> s ty_entry -> int -> int -> (s, tr, a) ty_symbol -> (s, tr', a -> r) ty_tree -> int -> a -> (a -> r) parser_t =
  fun p1 entry nlevn alevn s son bp a (strm__ : _ Stream.t) ->
  try p1 strm__ with
    Stream.Failure ->
      recover parser_of_tree entry nlevn alevn bp a s son strm__
and parser_of_token_list : type s tr lt r f.
  s ty_entry -> (s, tr, lt -> r) ty_tree ->
    (int -> lt -> (lt -> r) parser_t) -> (r, f) tok_list -> lt pattern -> f parser_t =
  fun entry son p1 rev_tokl last_tok ->
  let n = tok_list_length rev_tokl + 1 in
  let plast : r parser_t =
    let tematch = token_ematch egram last_tok in
    let ps strm =
      match peek_nth n strm with
        Some tok ->
          let r = tematch tok in
          for _i = 1 to n do Stream.junk strm done; r
      | None -> raise Stream.Failure
    in
    fun (strm : _ Stream.t) ->
      let bp = Stream.count strm in
      let a = ps strm in
      match try Some (p1 bp a strm) with Stream.Failure -> None with
        Some act -> act a
      | None -> raise (Stream.Error (tree_failed entry a (Stoken last_tok) son))
  in
  let rec loop : type s f. _ -> (s, f) tok_list -> s parser_t -> f parser_t =
    fun n tokl plast -> match tokl with
    | TokNil -> plast
    | TokCns (tok, tokl) ->
       let tematch = token_ematch egram tok in
       let ps strm =
         match peek_nth n strm with
           Some tok -> tematch tok
         | None -> raise Stream.Failure
       in
       let plast = fun (strm : _ Stream.t) ->
         let a = ps strm in let act = plast strm in act a in
       loop (n - 1) tokl plast in
  loop (n - 1) rev_tokl plast
and parser_of_symbol : type s tr a.
  s ty_entry -> int -> (s, tr, a) ty_symbol -> a parser_t =
  fun entry nlevn ->
  function
  | Slist0 s ->
      let ps = call_and_push (parser_of_symbol entry nlevn s) in
      let rec loop al (strm__ : _ Stream.t) =
        match try Some (ps al strm__) with Stream.Failure -> None with
          Some al -> loop al strm__
        | _ -> al
      in
      (fun (strm__ : _ Stream.t) ->
         let a = loop [] strm__ in List.rev a)
  | Slist0sep (symb, sep, false) ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al (strm__ : _ Stream.t) =
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
      (fun (strm__ : _ Stream.t) ->
         match try Some (ps [] strm__) with Stream.Failure -> None with
           Some al -> let a = kont al strm__ in List.rev a
         | _ -> [])
  | Slist0sep (symb, sep, true) ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al (strm__ : _ Stream.t) =
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
      (fun (strm__ : _ Stream.t) ->
         match try Some (ps [] strm__) with Stream.Failure -> None with
           Some al -> let a = kont al strm__ in List.rev a
         | _ -> [])
  | Slist1 s ->
      let ps = call_and_push (parser_of_symbol entry nlevn s) in
      let rec loop al (strm__ : _ Stream.t) =
        match try Some (ps al strm__) with Stream.Failure -> None with
          Some al -> loop al strm__
        | _ -> al
      in
      (fun (strm__ : _ Stream.t) ->
         let al = ps [] strm__ in
         let a = loop al strm__ in List.rev a)
  | Slist1sep (symb, sep, false) ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al (strm__ : _ Stream.t) =
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
      (fun (strm__ : _ Stream.t) ->
         let al = ps [] strm__ in
         let a = kont al strm__ in List.rev a)
  | Slist1sep (symb, sep, true) ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al (strm__ : _ Stream.t) =
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
      (fun (strm__ : _ Stream.t) ->
         let al = ps [] strm__ in
         let a = kont al strm__ in List.rev a)
  | Sopt s ->
      let ps = parser_of_symbol entry nlevn s in
      (fun (strm__ : _ Stream.t) ->
         match try Some (ps strm__) with Stream.Failure -> None with
           Some a -> Some a
         | _ -> None)
  | Stree t ->
      let pt = parser_of_tree entry 1 0 t in
      (fun (strm__ : _ Stream.t) ->
         let bp = Stream.count strm__ in
         let a = pt strm__ in
         let ep = Stream.count strm__ in
         let loc = loc_of_token_interval bp ep in a loc)
  | Snterm e -> (fun (strm__ : _ Stream.t) -> e.estart 0 strm__)
  | Snterml (e, l) ->
      (fun (strm__ : _ Stream.t) -> e.estart (level_number e l) strm__)
  | Sself -> (fun (strm__ : _ Stream.t) -> entry.estart 0 strm__)
  | Snext -> (fun (strm__ : _ Stream.t) -> entry.estart nlevn strm__)
  | Stoken tok -> parser_of_token entry tok
and parser_of_token : type s a.
  s ty_entry -> a pattern -> a parser_t =
  fun entry tok ->
  let f = L.tok_match tok in
  fun strm ->
    match Stream.peek strm with
      Some tok -> let r = f tok in Stream.junk strm; r
    | None -> raise Stream.Failure
and parse_top_symb : type s tr a. s ty_entry -> (s, tr, a) ty_symbol -> a parser_t =
  fun entry symb ->
  parser_of_symbol entry 0 (top_symb entry symb)

let rec start_parser_of_levels entry clevn =
  function
    [] -> (fun levn (strm__ : _ Stream.t) -> raise Stream.Failure)
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
                 let (strm__ : _ Stream.t) = strm in
                 let bp = Stream.count strm__ in
                 let act = p2 strm__ in
                 let ep = Stream.count strm__ in
                 let a = act (loc_of_token_interval bp ep) in
                 entry.econtinue levn bp a strm)
          | _ ->
              fun levn strm ->
                if levn > clevn then p1 levn strm
                else
                  let (strm__ : _ Stream.t) = strm in
                  let bp = Stream.count strm__ in
                  match try Some (p2 strm__) with Stream.Failure -> None with
                    Some act ->
                      let ep = Stream.count strm__ in
                      let a = act (loc_of_token_interval bp ep) in
                      entry.econtinue levn bp a strm
                  | _ -> p1 levn strm__

let rec continue_parser_of_levels entry clevn =
  function
    [] -> (fun levn bp a (strm__ : _ Stream.t) -> raise Stream.Failure)
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
            if levn > clevn then p1 levn bp a strm
            else
              let (strm__ : _ Stream.t) = strm in
              try p1 levn bp a strm__ with
                Stream.Failure ->
                  let act = p2 strm__ in
                  let ep = Stream.count strm__ in
                  let a = act a (loc_of_token_interval bp ep) in
                  entry.econtinue levn bp a strm

let continue_parser_of_entry entry =
  match entry.edesc with
    Dlevels elev ->
      let p = continue_parser_of_levels entry 0 elev in
      (fun levn bp a (strm__ : _ Stream.t) ->
         try p levn bp a strm__ with Stream.Failure -> a)
  | Dparser p -> fun levn bp a (strm__ : _ Stream.t) -> raise Stream.Failure

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

let extend_entry ~warning entry position rules =
    let elev = levels_of_rules ~warning entry position rules in
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

type parsable =
  { pa_chr_strm : char Stream.t;
    pa_tok_strm : L.te Stream.t;
    pa_loc_func : Plexing.location_function }

let parse_parsable entry p =
  let efun = entry.estart 0 in
  let ts = p.pa_tok_strm in
  let cs = p.pa_chr_strm in
  let fun_loc = p.pa_loc_func in
  let restore =
    let old_floc = !floc in
    let old_tc = !token_count in
    fun () -> floc := old_floc; token_count := old_tc
  in
  let get_loc () =
    try
      let cnt = Stream.count ts in
      (* Ensure that the token at location cnt has been peeked so that
         the location function knows about it *)
      let _ = Stream.peek ts in
      let loc = fun_loc cnt in
      if !token_count - 1 <= cnt then loc
      else Loc.merge loc (fun_loc (!token_count - 1))
    with Failure _ -> Ploc.make_unlined (Stream.count cs, Stream.count cs + 1)
  in
  floc := fun_loc;
  token_count := 0;
  try let r = efun ts in restore (); r with
    Stream.Failure ->
      let loc = get_loc () in
      restore ();
      Ploc.raise loc (Stream.Error ("illegal begin of " ^ entry.ename))
  | Stream.Error _ as exc ->
      let loc = get_loc () in restore (); Ploc.raise loc exc
  | exc ->
      let loc = Stream.count cs, Stream.count cs + 1 in
      restore (); Ploc.raise (Ploc.make_unlined loc) exc

(* Unsafe *)

let clear_entry e =
  e.estart <- (fun _ (strm__ : _ Stream.t) -> raise Stream.Failure);
  e.econtinue <- (fun _ _ _ (strm__ : _ Stream.t) -> raise Stream.Failure);
  match e.edesc with
    Dlevels _ -> e.edesc <- Dlevels []
  | Dparser _ -> ()

    let parsable ?loc cs =
      let (ts, lf) = L.tok_func ?loc cs in
      {pa_chr_strm = cs; pa_tok_strm = ts; pa_loc_func = lf}
    module Entry =
      struct
        type 'a e = 'a ty_entry
        let create n =
          { ename = n; estart = empty_entry n;
           econtinue =
             (fun _ _ _ (strm__ : _ Stream.t) -> raise Stream.Failure);
           edesc = Dlevels []}
        let parse (e : 'a e) p : 'a =
          parse_parsable e p
        let parse_token_stream (e : 'a e) ts : 'a =
          e.estart 0 ts
        let name e = e.ename
        let of_parser n (p : te Stream.t -> 'a) : 'a e =
          { ename = n;
           estart = (fun _ -> p);
           econtinue =
             (fun _ _ _ (strm__ : _ Stream.t) -> raise Stream.Failure);
           edesc = Dparser p}
        let print ppf e = fprintf ppf "%a@." print_entry e
      end
    let s_nterm e = Snterm e
    let s_nterml e l = Snterml (e, l)
    let s_list0 s = Slist0 s
    let s_list0sep s sep b = Slist0sep (s, sep, b)
    let s_list1 s = Slist1 s
    let s_list1sep s sep b = Slist1sep (s, sep, b)
    let s_opt s = Sopt s
    let s_self = Sself
    let s_next = Snext
    let s_token tok = Stoken tok
    let s_rules ~warning (t : 'a ty_rules list) = srules ~warning t
    let r_stop = TStop
    let r_next r s = TNext (MayRec2, r, s)
    let r_next_norec r s = TNext (NoRec2, r, s)
    let rules (p, act) = TRules (p, act)
    let production (p, act) = TProd (p, act)
    module Unsafe =
      struct
        let clear_entry = clear_entry
      end
    let safe_extend ~warning (e : 'a Entry.e) pos
        (r :
         (string option * Gramext.g_assoc option * 'a ty_production list)
           list) =
      extend_entry ~warning e pos r
    let safe_delete_rule e r =
      let AnyS (symbols, _) = get_symbols r in
      delete_rule e symbols

end
