(* camlp5r *)
(* gramext.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Printf;

type parser_t 'a = Stream.t 'a -> Obj.t;
type fparser_t 'a = Fstream.t 'a -> option (Obj.t * Fstream.t 'a);
type bparser_t 'a = Fstream.bp 'a Obj.t;

type parse_algorithm =
  [ Predictive | Functional | Backtracking | DefaultAlgorithm ];

type grammar 'te =
  { gtokens : Hashtbl.t Plexing.pattern (ref int);
    glexer : mutable Plexing.lexer 'te;
    galgo : mutable parse_algorithm }
;

type g_entry 'te =
  { egram : grammar 'te;
    ename : string;
    elocal : bool;
    estart : mutable int -> parser_t 'te;
    econtinue : mutable int -> int -> Obj.t -> parser_t 'te;
    fstart : mutable int -> err_fun -> fparser_t 'te;
    fcontinue : mutable int -> int -> Obj.t -> err_fun -> fparser_t 'te;
    bstart : mutable int -> err_fun -> bparser_t 'te;
    bcontinue : mutable int -> int -> Obj.t -> err_fun -> bparser_t 'te;
    edesc : mutable g_desc 'te }
and g_desc 'te =
  [ Dlevels of list (g_level 'te)
  | Dparser of parser_t 'te ]
and g_level 'te =
  { assoc : g_assoc;
    lname : option string;
    lsuffix : g_tree 'te;
    lprefix : g_tree 'te }
and g_assoc = [ NonA | RightA | LeftA ]
and g_symbol 'te =
  [ Sfacto of g_symbol 'te
  | Smeta of string and list (g_symbol 'te) and Obj.t
  | Snterm of g_entry 'te
  | Snterml of g_entry 'te and string
  | Slist0 of g_symbol 'te
  | Slist0sep of g_symbol 'te and g_symbol 'te and bool
  | Slist1 of g_symbol 'te
  | Slist1sep of g_symbol 'te and g_symbol 'te and bool
  | Sopt of g_symbol 'te
  | Sflag of g_symbol 'te
  | Sself
  | Snext
  | Scut
  | Stoken of Plexing.pattern
  | Stree of g_tree 'te
  | Svala of list string and g_symbol 'te ]
and g_action = Obj.t
and g_tree 'te =
  [ Node of g_node 'te
  | LocAct of g_action and list g_action
  | DeadEnd ]
and g_node 'te =
  { node : g_symbol 'te; son : g_tree 'te; brother : g_tree 'te }
and err_fun = unit -> string;

type position =
  [ First
  | Last
  | Before of string
  | After of string
  | Like of string
  | Level of string ]
;

value warning_verbose = ref True;

value rec derive_eps =
  fun
  [ Slist0 _ -> True
  | Slist0sep _ _ _ -> True
  | Sopt _ | Sflag _ -> True
  | Sfacto s -> derive_eps s
  | Stree t -> tree_derive_eps t
  | Svala _ s -> derive_eps s
  | Smeta _ _ _ | Slist1 _ | Slist1sep _ _ _ | Snterm _ | Snterml _ _ |
    Snext | Sself | Scut | Stoken _ ->
      False ]
and tree_derive_eps =
  fun
  [ LocAct _ _ -> True
  | Node {node = s; brother = bro; son = son} ->
      derive_eps s && tree_derive_eps son || tree_derive_eps bro
  | DeadEnd -> False ]
;

value rec eq_symbol s1 s2 =
  match (s1, s2) with
  [ (Snterm e1, Snterm e2) -> e1 == e2
  | (Snterml e1 l1, Snterml e2 l2) -> e1 == e2 && l1 = l2
  | (Slist0 s1, Slist0 s2) -> eq_symbol s1 s2
  | (Slist0sep s1 sep1 b1, Slist0sep s2 sep2 b2) ->
      eq_symbol s1 s2 && eq_symbol sep1 sep2 && b1 = b2
  | (Slist1 s1, Slist1 s2) -> eq_symbol s1 s2
  | (Slist1sep s1 sep1 b1, Slist1sep s2 sep2 b2) ->
      eq_symbol s1 s2 && eq_symbol sep1 sep2 && b1 = b2
  | (Sflag s1, Sflag s2) -> eq_symbol s1 s2
  | (Sopt s1, Sopt s2) -> eq_symbol s1 s2
  | (Svala ls1 s1, Svala ls2 s2) -> ls1 = ls2 && eq_symbol s1 s2
  | (Stree _, Stree _) -> False
  | (Sfacto (Stree t1), Sfacto (Stree t2)) ->
      (* The only goal of the node 'Sfacto' is to allow tree comparison
         (therefore factorization) without looking at the semantic
         actions; allow factorization of rules like "SV foo" which are
         actually expanded into a tree. *)
      eq_tree t1 t2 where rec eq_tree t1 t2 =
        match (t1, t2) with
        [ (Node n1, Node n2) ->
            eq_symbol n1.node n2.node && eq_tree n1.son n2.son &&
            eq_tree n1.brother n2.brother
        | (LocAct _ _, LocAct _ _) -> True
        | (DeadEnd, DeadEnd) -> True
        | _ -> False ]
  | _ -> s1 = s2 ]
;

value is_before s1 s2 =
  let s1 = match s1 with [ Svala _ s -> s | _ -> s1 ] in
  let s2 = match s2 with [ Svala _ s -> s | _ -> s2 ] in
  match (s1, s2) with
  [ (Stoken ("ANY", _), _) -> False
  | (_, Stoken ("ANY", _)) -> True
  | (Stoken (_, s), Stoken (_, "")) when s <> "" -> True
  | (Stoken _, Stoken _) -> False
  | (Stoken _, _) -> True
  | _ -> False ]
;

value insert_tree entry_name gsymbols action tree =
  let rec insert symbols tree =
    match symbols with
    [ [s :: sl] -> insert_in_tree s sl tree
    | [] ->
        match tree with
        [ Node {node = s; son = son; brother = bro} ->
            Node {node = s; son = son; brother = insert [] bro}
        | LocAct old_action action_list -> do {
            if warning_verbose.val then do {
              eprintf "<W> Grammar extension: ";
              if entry_name <> "" then eprintf "in [%s], " entry_name else ();
              eprintf "some rule has been masked\n";
              flush stderr
            }
            else ();
            LocAct action [old_action :: action_list]
          }
        | DeadEnd -> LocAct action [] ] ]
  and insert_in_tree s sl tree =
    match try_insert s sl tree with
    [ Some t -> t
    | None -> Node {node = s; son = insert sl DeadEnd; brother = tree} ]
  and try_insert s sl tree =
    match tree with
    [ Node {node = s1; son = son; brother = bro} ->
        if eq_symbol s s1 then
          let t = Node {node = s1; son = insert sl son; brother = bro} in
          Some t
        else if s = Scut then
          try_insert s sl (Node {node = s; son = tree; brother = DeadEnd})
        else if s1 = Scut then
          try_insert s1 [s :: sl] tree
        else if is_before s1 s || derive_eps s && not (derive_eps s1) then
          let bro =
            match try_insert s sl bro with
            [ Some bro -> bro
            | None ->
                Node {node = s; son = insert sl DeadEnd; brother = bro} ]
          in
          let t = Node {node = s1; son = son; brother = bro} in
          Some t
        else
          match try_insert s sl bro with
          [ Some bro ->
              let t = Node {node = s1; son = son; brother = bro} in
              Some t
          | None -> None ]
    | LocAct _ _ | DeadEnd -> None ]
  in
  insert gsymbols tree
;

value srules rl =
  let t =
    List.fold_left
      (fun tree (symbols, action) -> insert_tree "" symbols action tree)
      DeadEnd rl
  in
  Stree t
;

external action : 'a -> g_action = "%identity";

value is_level_labelled n lev =
  match lev.lname with
  [ Some n1 -> n = n1
  | None -> False ]
;

value rec token_exists_in_level f lev =
  token_exists_in_tree f lev.lprefix || token_exists_in_tree f lev.lsuffix
and token_exists_in_tree f =
  fun
  [ Node n ->
      token_exists_in_symbol f n.node || token_exists_in_tree f n.brother ||
      token_exists_in_tree f n.son
  | LocAct _ _ | DeadEnd -> False ]
and token_exists_in_symbol f =
  fun
  [ Sfacto sy -> token_exists_in_symbol f sy
  | Smeta _ syl _ -> List.exists (token_exists_in_symbol f) syl
  | Slist0 sy -> token_exists_in_symbol f sy
  | Slist0sep sy sep _ ->
      token_exists_in_symbol f sy || token_exists_in_symbol f sep
  | Slist1 sy -> token_exists_in_symbol f sy
  | Slist1sep sy sep _ ->
      token_exists_in_symbol f sy || token_exists_in_symbol f sep
  | Sopt sy -> token_exists_in_symbol f sy
  | Sflag sy -> token_exists_in_symbol f sy
  | Stoken tok -> f tok
  | Stree t -> token_exists_in_tree f t
  | Svala _ sy -> token_exists_in_symbol f sy
  | Snterm _ | Snterml _ _ | Snext | Sself | Scut -> False ]
;

value insert_level entry_name e1 symbols action slev =
  match e1 with
  [ True ->
      {assoc = slev.assoc; lname = slev.lname;
       lsuffix = insert_tree entry_name symbols action slev.lsuffix;
       lprefix = slev.lprefix}
  | False ->
      {assoc = slev.assoc; lname = slev.lname; lsuffix = slev.lsuffix;
       lprefix = insert_tree entry_name symbols action slev.lprefix} ]
;

value empty_lev lname assoc =
  let assoc =
    match assoc with
    [ Some a -> a
    | None -> LeftA ]
  in
  {assoc = assoc; lname = lname; lsuffix = DeadEnd; lprefix = DeadEnd}
;

value change_lev lev n lname assoc = do {
  let a =
    match assoc with
    [ None -> lev.assoc
    | Some a -> do {
        if a <> lev.assoc && warning_verbose.val then do {
          eprintf "<W> Changing associativity of level \"%s\"\n" n;
          flush stderr
        }
        else ();
        a
      } ]
  in
  match lname with
  [ Some n ->
      if lname <> lev.lname && warning_verbose.val then do {
        eprintf "<W> Level label \"%s\" ignored\n" n;
        flush stderr
      }
      else ()
  | None -> () ];
  {assoc = a; lname = lev.lname; lsuffix = lev.lsuffix; lprefix = lev.lprefix}
};

value get_level entry position levs =
  match position with
  [ Some First -> ([], empty_lev, levs)
  | Some Last -> (levs, empty_lev, [])
  | Some (Level n) ->
      get levs where rec get =
        fun
        [ [] -> do {
            eprintf "No level labelled \"%s\" in entry \"%s\"\n" n
              entry.ename;
            flush stderr;
            failwith "Grammar.extend"
          }
        | [lev :: levs] ->
            if is_level_labelled n lev then ([], change_lev lev n, levs)
            else
              let (levs1, rlev, levs2) = get levs in
              ([lev :: levs1], rlev, levs2) ]
  | Some (Before n) ->
      get levs where rec get =
        fun
        [ [] -> do {
            eprintf "No level labelled \"%s\" in entry \"%s\"\n" n
              entry.ename;
            flush stderr;
            failwith "Grammar.extend"
          }
        | [lev :: levs] ->
            if is_level_labelled n lev then ([], empty_lev, [lev :: levs])
            else
              let (levs1, rlev, levs2) = get levs in
              ([lev :: levs1], rlev, levs2) ]
  | Some (After n) ->
      get levs where rec get =
        fun
        [ [] -> do {
            eprintf "No level labelled \"%s\" in entry \"%s\"\n" n
              entry.ename;
            flush stderr;
            failwith "Grammar.extend"
          }
        | [lev :: levs] ->
            if is_level_labelled n lev then ([lev], empty_lev, levs)
            else
              let (levs1, rlev, levs2) = get levs in
              ([lev :: levs1], rlev, levs2) ]
  | Some (Like n) ->
      let f (tok, prm) = n = tok || n = prm in
      get levs where rec get =
        fun
        [ [] -> do {
            eprintf "No level with \"%s\" in entry \"%s\"\n" n entry.ename;
            flush stderr;
            failwith "Grammar.extend"
          }
        | [lev :: levs] ->
            if token_exists_in_level f lev then ([], change_lev lev n, levs)
            else
              let (levs1, rlev, levs2) = get levs in
              ([lev :: levs1], rlev, levs2) ]
  | None ->
      match levs with
      [ [lev :: levs] -> ([], change_lev lev "<top>", levs)
      | [] -> ([], empty_lev, []) ] ]
;

value rec check_gram entry =
  fun
  [ Snterm e ->
      if e.egram != entry.egram then do {
        eprintf "\
Error: entries \"%s\" and \"%s\" do not belong to the same grammar.\n"
          entry.ename e.ename;
        flush stderr;
        failwith "Grammar.extend error"
      }
      else ()
  | Snterml e _ ->
      if e.egram != entry.egram then do {
        eprintf "\
Error: entries \"%s\" and \"%s\" do not belong to the same grammar.\n"
          entry.ename e.ename;
        flush stderr;
        failwith "Grammar.extend error"
      }
      else ()
  | Sfacto s -> check_gram entry s
  | Smeta _ sl _ -> List.iter (check_gram entry) sl
  | Slist0sep s t _ -> do { check_gram entry t; check_gram entry s }
  | Slist1sep s t _ -> do { check_gram entry t; check_gram entry s }
  | Slist0 s -> check_gram entry s
  | Slist1 s -> check_gram entry s
  | Sopt s -> check_gram entry s
  | Sflag s -> check_gram entry s
  | Stree t -> tree_check_gram entry t
  | Svala _ s -> check_gram entry s
  | Snext | Sself | Scut | Stoken _ -> () ]
and tree_check_gram entry =
  fun
  [ Node {node = n; brother = bro; son = son} -> do {
      check_gram entry n;
      tree_check_gram entry bro;
      tree_check_gram entry son
    }
  | LocAct _ _ | DeadEnd -> () ]
;

value change_to_self entry =
  fun
  [ Snterm e when e == entry -> Sself
  | x -> x ]
;

value get_initial entry =
  fun
  [ [Sself :: symbols] -> (True, symbols)
  | symbols -> (False, symbols) ]
;

value insert_tokens gram symbols =
  let rec insert =
    fun
    [ Sfacto s -> insert s
    | Smeta _ sl _ -> List.iter insert sl
    | Slist0 s -> insert s
    | Slist1 s -> insert s
    | Slist0sep s t _ -> do { insert s; insert t }
    | Slist1sep s t _ -> do { insert s; insert t }
    | Sopt s -> insert s
    | Sflag s -> insert s
    | Stree t -> tinsert t
    | Svala _ s -> insert s
    | Stoken ("ANY", _) -> ()
    | Stoken tok -> do {
        gram.glexer.Plexing.tok_using tok;
        let r =
          try Hashtbl.find gram.gtokens tok with
          [ Not_found -> do {
              let r = ref 0 in
              Hashtbl.add gram.gtokens tok r;
              r
            } ]
        in
        incr r
      }
    | Snterm _ | Snterml _ _ | Snext | Sself | Scut -> () ]
  and tinsert =
    fun
    [ Node {node = s; brother = bro; son = son} -> do {
        insert s;
        tinsert bro;
        tinsert son
      }
    | LocAct _ _ | DeadEnd -> () ]
  in
  List.iter insert symbols
;

value levels_of_rules entry position rules =
  let elev =
    match entry.edesc with
    [ Dlevels elev -> elev
    | Dparser _ -> do {
        eprintf "Error: entry not extensible: \"%s\"\n" entry.ename;
        flush stderr;
        failwith "Grammar.extend"
      } ]
  in
  if rules = [] then elev
  else
    let (levs1, make_lev, levs2) = get_level entry position elev in
    let (levs, _) =
      List.fold_left
        (fun (levs, make_lev) (lname, assoc, level) ->
           let lev = make_lev lname assoc in
           let lev =
             List.fold_left
               (fun lev (symbols, action) -> do {
                  let symbols = List.map (change_to_self entry) symbols in
                  List.iter (check_gram entry) symbols;
                  let (e1, symbols) = get_initial entry symbols in
                  insert_tokens entry.egram symbols;
                  insert_level entry.ename e1 symbols action lev
                })
               lev level
           in
           ([lev :: levs], empty_lev))
        ([], make_lev) rules
    in
    levs1 @ List.rev levs @ levs2
;

value logically_eq_symbols entry =
  let rec eq_symbols s1 s2 =
    match (s1, s2) with
    [ (Snterm e1, Snterm e2) -> e1.ename = e2.ename
    | (Snterm e1, Sself) -> e1.ename = entry.ename
    | (Sself, Snterm e2) -> entry.ename = e2.ename
    | (Snterml e1 l1, Snterml e2 l2) -> e1.ename = e2.ename && l1 = l2
    | (Slist0 s1, Slist0 s2) -> eq_symbols s1 s2
    | (Slist0sep s1 sep1 b1, Slist0sep s2 sep2 b2) ->
        eq_symbols s1 s2 && eq_symbols sep1 sep2 && b1 = b2
    | (Slist1 s1, Slist1 s2) -> eq_symbols s1 s2
    | (Slist1sep s1 sep1 b1, Slist1sep s2 sep2 b2) ->
        eq_symbols s1 s2 && eq_symbols sep1 sep2 && b1 = b2
    | (Sopt s1, Sopt s2) -> eq_symbols s1 s2
    | (Stree t1, Stree t2) -> eq_trees t1 t2
    | _ -> s1 = s2 ]
  and eq_trees t1 t2 =
    match (t1, t2) with
    [ (Node n1, Node n2) ->
        eq_symbols n1.node n2.node && eq_trees n1.son n2.son &&
        eq_trees n1.brother n2.brother
    | (LocAct _ _ | DeadEnd, LocAct _ _ | DeadEnd) -> True
    | _ -> False ]
  in
  eq_symbols
;

(* [delete_rule_in_tree] returns
     [Some (dsl, t)] if success
        [dsl] =
           Some (list of deleted nodes) if branch deleted
           None if action replaced by previous version of action
        [t] = remaining tree
     [None] if failure *)

value delete_rule_in_tree entry =
  let rec delete_in_tree symbols tree =
    match (symbols, tree) with
    [ ([s :: sl], Node n) ->
        if logically_eq_symbols entry s n.node then delete_son sl n
        else
          match delete_in_tree symbols n.brother with
          [ Some (dsl, t) ->
              Some (dsl, Node {node = n.node; son = n.son; brother = t})
          | None -> None ]
    | ([s :: sl], _) -> None
    | ([], Node n) ->
        match delete_in_tree [] n.brother with
        [ Some (dsl, t) ->
            Some (dsl, Node {node = n.node; son = n.son; brother = t})
        | None -> None ]
    | ([], DeadEnd) -> None
    | ([], LocAct _ []) -> Some (Some [], DeadEnd)
    | ([], LocAct _ [action :: list]) -> Some (None, LocAct action list) ]
  and delete_son sl n =
    match delete_in_tree sl n.son with
    [ Some (Some dsl, DeadEnd) -> Some (Some [n.node :: dsl], n.brother)
    | Some (Some dsl, t) ->
        let t = Node {node = n.node; son = t; brother = n.brother} in
        Some (Some [n.node :: dsl], t)
    | Some (None, t) ->
        let t = Node {node = n.node; son = t; brother = n.brother} in
        Some (None, t)
    | None -> None ]
  in
  delete_in_tree
;

value rec decr_keyw_use gram =
  fun
  [ Stoken tok -> do {
      let r = Hashtbl.find gram.gtokens tok in
      decr r;
      if r.val == 0 then do {
        Hashtbl.remove gram.gtokens tok;
        gram.glexer.Plexing.tok_removing tok
      }
      else ()
    }
  | Sfacto s -> decr_keyw_use gram s
  | Smeta _ sl _ -> List.iter (decr_keyw_use gram) sl
  | Slist0 s -> decr_keyw_use gram s
  | Slist1 s -> decr_keyw_use gram s
  | Slist0sep s1 s2 _ -> do { decr_keyw_use gram s1; decr_keyw_use gram s2 }
  | Slist1sep s1 s2 _ -> do { decr_keyw_use gram s1; decr_keyw_use gram s2 }
  | Sopt s -> decr_keyw_use gram s
  | Sflag s -> decr_keyw_use gram s
  | Stree t -> decr_keyw_use_in_tree gram t
  | Svala _ s -> decr_keyw_use gram s
  | Sself | Snext | Scut | Snterm _ | Snterml _ _ -> () ]
and decr_keyw_use_in_tree gram =
  fun
  [ DeadEnd | LocAct _ _ -> ()
  | Node n -> do {
      decr_keyw_use gram n.node;
      decr_keyw_use_in_tree gram n.son;
      decr_keyw_use_in_tree gram n.brother
    } ]
;

value rec delete_rule_in_suffix entry symbols =
  fun
  [ [lev :: levs] ->
      match delete_rule_in_tree entry symbols lev.lsuffix with
      [ Some (dsl, t) -> do {
          match dsl with
          [ Some dsl -> List.iter (decr_keyw_use entry.egram) dsl
          | None -> () ];
          match t with
          [ DeadEnd when lev.lprefix == DeadEnd -> levs
          | _ ->
              let lev =
                {assoc = lev.assoc; lname = lev.lname; lsuffix = t;
                 lprefix = lev.lprefix}
              in
              [lev :: levs] ]
        }
      | None ->
          let levs = delete_rule_in_suffix entry symbols levs in
          [lev :: levs] ]
  | [] -> raise Not_found ]
;

value rec delete_rule_in_prefix entry symbols =
  fun
  [ [lev :: levs] ->
      match delete_rule_in_tree entry symbols lev.lprefix with
      [ Some (dsl, t) -> do {
          match dsl with
          [ Some dsl -> List.iter (decr_keyw_use entry.egram) dsl
          | None -> () ];
          match t with
          [ DeadEnd when lev.lsuffix == DeadEnd -> levs
          | _ ->
              let lev =
                {assoc = lev.assoc; lname = lev.lname; lsuffix = lev.lsuffix;
                 lprefix = t}
              in
              [lev :: levs] ]
        }
      | None ->
          let levs = delete_rule_in_prefix entry symbols levs in
          [lev :: levs] ]
  | [] -> raise Not_found ]
;

value rec delete_rule_in_level_list entry symbols levs =
  match symbols with
  [ [Sself :: symbols] -> delete_rule_in_suffix entry symbols levs
  | [Snterm e :: symbols] when e == entry ->
      delete_rule_in_suffix entry symbols levs
  | _ -> delete_rule_in_prefix entry symbols levs ]
;
