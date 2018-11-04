(* camlp5r *)
(* gramext.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Printf

type 'a parser_t = 'a Stream.t -> Obj.t

type 'te grammar =
  { gtokens : (Plexing.pattern, int ref) Hashtbl.t;
    mutable glexer : 'te Plexing.lexer }

type 'te g_entry =
  { egram : 'te grammar;
    ename : string;
    elocal : bool;
    mutable estart : int -> 'te parser_t;
    mutable econtinue : int -> int -> Obj.t -> 'te parser_t;
    mutable edesc : 'te g_desc }
and 'te g_desc =
    Dlevels of 'te g_level list
  | Dparser of 'te parser_t
and 'te g_level =
  { assoc : g_assoc;
    lname : string option;
    lsuffix : 'te g_tree;
    lprefix : 'te g_tree }
and g_assoc = NonA | RightA | LeftA
and 'te g_symbol =
  | Snterm of 'te g_entry
  | Snterml of 'te g_entry * string
  | Slist0 of 'te g_symbol
  | Slist0sep of 'te g_symbol * 'te g_symbol * bool
  | Slist1 of 'te g_symbol
  | Slist1sep of 'te g_symbol * 'te g_symbol * bool
  | Sopt of 'te g_symbol
  | Sself
  | Snext
  | Scut
  | Stoken of Plexing.pattern
  | Stree of 'te g_tree
and g_action = Obj.t
and 'te g_tree =
    Node of 'te g_node
  | LocAct of g_action * g_action list
  | DeadEnd
and 'te g_node =
  { node : 'te g_symbol; son : 'te g_tree; brother : 'te g_tree }
and err_fun = unit -> string

type position =
    First
  | Last
  | Before of string
  | After of string
  | Like of string
  | Level of string

let warning_verbose = ref true

let rec derive_eps =
  function
    Slist0 _ -> true
  | Slist0sep (_, _, _) -> true
  | Sopt _ -> true
  | Stree t -> tree_derive_eps t
  | Slist1 _ | Slist1sep (_, _, _) | Snterm _ |
    Snterml (_, _) | Snext | Sself | Scut | Stoken _ ->
      false
and tree_derive_eps =
  function
    LocAct (_, _) -> true
  | Node {node = s; brother = bro; son = son} ->
      derive_eps s && tree_derive_eps son || tree_derive_eps bro
  | DeadEnd -> false

let rec eq_symbol s1 s2 =
  match s1, s2 with
    Snterm e1, Snterm e2 -> e1 == e2
  | Snterml (e1, l1), Snterml (e2, l2) -> e1 == e2 && l1 = l2
  | Slist0 s1, Slist0 s2 -> eq_symbol s1 s2
  | Slist0sep (s1, sep1, b1), Slist0sep (s2, sep2, b2) ->
      eq_symbol s1 s2 && eq_symbol sep1 sep2 && b1 = b2
  | Slist1 s1, Slist1 s2 -> eq_symbol s1 s2
  | Slist1sep (s1, sep1, b1), Slist1sep (s2, sep2, b2) ->
      eq_symbol s1 s2 && eq_symbol sep1 sep2 && b1 = b2
  | Sopt s1, Sopt s2 -> eq_symbol s1 s2
  | Stree _, Stree _ -> false
  | _ -> s1 = s2

let is_before s1 s2 =
  match s1, s2 with
    Stoken ("ANY", _), _ -> false
  | _, Stoken ("ANY", _) -> true
  | Stoken (_, s), Stoken (_, "") when s <> "" -> true
  | Stoken _, Stoken _ -> false
  | Stoken _, _ -> true
  | _ -> false

let insert_tree entry_name gsymbols action tree =
  let rec insert symbols tree =
    match symbols with
      s :: sl -> insert_in_tree s sl tree
    | [] ->
        match tree with
          Node {node = s; son = son; brother = bro} ->
            Node {node = s; son = son; brother = insert [] bro}
        | LocAct (old_action, action_list) ->
            if !warning_verbose then
              begin
                eprintf "<W> Grammar extension: ";
                if entry_name <> "" then eprintf "in [%s], " entry_name;
                eprintf "some rule has been masked\n";
                flush stderr
              end;
            LocAct (action, old_action :: action_list)
        | DeadEnd -> LocAct (action, [])
  and insert_in_tree s sl tree =
    match try_insert s sl tree with
      Some t -> t
    | None -> Node {node = s; son = insert sl DeadEnd; brother = tree}
  and try_insert s sl tree =
    match tree with
      Node {node = s1; son = son; brother = bro} ->
        if eq_symbol s s1 then
          let t = Node {node = s1; son = insert sl son; brother = bro} in
          Some t
        else if s = Scut then
          try_insert s sl (Node {node = s; son = tree; brother = DeadEnd})
        else if s1 = Scut then try_insert s1 (s :: sl) tree
        else if is_before s1 s || derive_eps s && not (derive_eps s1) then
          let bro =
            match try_insert s sl bro with
              Some bro -> bro
            | None -> Node {node = s; son = insert sl DeadEnd; brother = bro}
          in
          let t = Node {node = s1; son = son; brother = bro} in Some t
        else
          begin match try_insert s sl bro with
            Some bro ->
              let t = Node {node = s1; son = son; brother = bro} in Some t
          | None -> None
          end
    | LocAct (_, _) | DeadEnd -> None
  in
  insert gsymbols tree

let srules rl =
  let t =
    List.fold_left
      (fun tree (symbols, action) -> insert_tree "" symbols action tree)
      DeadEnd rl
  in
  Stree t

external action : 'a -> g_action = "%identity"

let is_level_labelled n lev =
  match lev.lname with
    Some n1 -> n = n1
  | None -> false

let rec token_exists_in_level f lev =
  token_exists_in_tree f lev.lprefix || token_exists_in_tree f lev.lsuffix
and token_exists_in_tree f =
  function
    Node n ->
      token_exists_in_symbol f n.node || token_exists_in_tree f n.brother ||
      token_exists_in_tree f n.son
  | LocAct (_, _) | DeadEnd -> false
and token_exists_in_symbol f =
  function
  | Slist0 sy -> token_exists_in_symbol f sy
  | Slist0sep (sy, sep, _) ->
      token_exists_in_symbol f sy || token_exists_in_symbol f sep
  | Slist1 sy -> token_exists_in_symbol f sy
  | Slist1sep (sy, sep, _) ->
      token_exists_in_symbol f sy || token_exists_in_symbol f sep
  | Sopt sy -> token_exists_in_symbol f sy
  | Stoken tok -> f tok
  | Stree t -> token_exists_in_tree f t
  | Snterm _ | Snterml (_, _) | Snext | Sself | Scut -> false

let insert_level entry_name e1 symbols action slev =
  match e1 with
    true ->
      {assoc = slev.assoc; lname = slev.lname;
       lsuffix = insert_tree entry_name symbols action slev.lsuffix;
       lprefix = slev.lprefix}
  | false ->
      {assoc = slev.assoc; lname = slev.lname; lsuffix = slev.lsuffix;
       lprefix = insert_tree entry_name symbols action slev.lprefix}

let empty_lev lname assoc =
  let assoc =
    match assoc with
      Some a -> a
    | None -> LeftA
  in
  {assoc = assoc; lname = lname; lsuffix = DeadEnd; lprefix = DeadEnd}

let change_lev lev n lname assoc =
  let a =
    match assoc with
      None -> lev.assoc
    | Some a ->
        if a <> lev.assoc && !warning_verbose then
          begin
            eprintf "<W> Changing associativity of level \"%s\"\n" n;
            flush stderr
          end;
        a
  in
  begin match lname with
    Some n ->
      if lname <> lev.lname && !warning_verbose then
        begin eprintf "<W> Level label \"%s\" ignored\n" n; flush stderr end
  | None -> ()
  end;
  {assoc = a; lname = lev.lname; lsuffix = lev.lsuffix; lprefix = lev.lprefix}

let get_level entry position levs =
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
            if is_level_labelled n lev then [], change_lev lev n, levs
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
  | Some (Like n) ->
      let f (tok, prm) = n = tok || n = prm in
      let rec get =
        function
          [] ->
            eprintf "No level with \"%s\" in entry \"%s\"\n" n entry.ename;
            flush stderr;
            failwith "Grammar.extend"
        | lev :: levs ->
            if token_exists_in_level f lev then [], change_lev lev n, levs
            else
              let (levs1, rlev, levs2) = get levs in lev :: levs1, rlev, levs2
      in
      get levs
  | None ->
      match levs with
        lev :: levs -> [], change_lev lev "<top>", levs
      | [] -> [], empty_lev, []

let rec check_gram entry =
  function
    Snterm e ->
      if e.egram != entry.egram then
        begin
          eprintf "\
Error: entries \"%s\" and \"%s\" do not belong to the same grammar.\n"
            entry.ename e.ename;
          flush stderr;
          failwith "Grammar.extend error"
        end
  | Snterml (e, _) ->
      if e.egram != entry.egram then
        begin
          eprintf "\
Error: entries \"%s\" and \"%s\" do not belong to the same grammar.\n"
            entry.ename e.ename;
          flush stderr;
          failwith "Grammar.extend error"
        end
  | Slist0sep (s, t, _) -> check_gram entry t; check_gram entry s
  | Slist1sep (s, t, _) -> check_gram entry t; check_gram entry s
  | Slist0 s -> check_gram entry s
  | Slist1 s -> check_gram entry s
  | Sopt s -> check_gram entry s
  | Stree t -> tree_check_gram entry t
  | Snext | Sself | Scut | Stoken _ -> ()
and tree_check_gram entry =
  function
    Node {node = n; brother = bro; son = son} ->
      check_gram entry n; tree_check_gram entry bro; tree_check_gram entry son
  | LocAct (_, _) | DeadEnd -> ()

let change_to_self entry =
  function
    Snterm e when e == entry -> Sself
  | x -> x

let get_initial entry =
  function
    Sself :: symbols -> true, symbols
  | symbols -> false, symbols

let insert_tokens gram symbols =
  let rec insert =
    function
    | Slist0 s -> insert s
    | Slist1 s -> insert s
    | Slist0sep (s, t, _) -> insert s; insert t
    | Slist1sep (s, t, _) -> insert s; insert t
    | Sopt s -> insert s
    | Stree t -> tinsert t
    | Stoken ("ANY", _) -> ()
    | Stoken tok ->
        gram.glexer.Plexing.tok_using tok;
        let r =
          try Hashtbl.find gram.gtokens tok with
            Not_found -> let r = ref 0 in Hashtbl.add gram.gtokens tok r; r
        in
        incr r
    | Snterm _ | Snterml (_, _) | Snext | Sself | Scut -> ()
  and tinsert =
    function
      Node {node = s; brother = bro; son = son} ->
        insert s; tinsert bro; tinsert son
    | LocAct (_, _) | DeadEnd -> ()
  in
  List.iter insert symbols

let levels_of_rules entry position rules =
  let elev =
    match entry.edesc with
      Dlevels elev -> elev
    | Dparser _ ->
        eprintf "Error: entry not extensible: \"%s\"\n" entry.ename;
        flush stderr;
        failwith "Grammar.extend"
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
               (fun lev (symbols, action) ->
                  let symbols = List.map (change_to_self entry) symbols in
                  List.iter (check_gram entry) symbols;
                  let (e1, symbols) = get_initial entry symbols in
                  insert_tokens entry.egram symbols;
                  insert_level entry.ename e1 symbols action lev)
               lev level
           in
           lev :: levs, empty_lev)
        ([], make_lev) rules
    in
    levs1 @ List.rev levs @ levs2

let logically_eq_symbols entry =
  let rec eq_symbols s1 s2 =
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
    | _ -> s1 = s2
  and eq_trees t1 t2 =
    match t1, t2 with
      Node n1, Node n2 ->
        eq_symbols n1.node n2.node && eq_trees n1.son n2.son &&
        eq_trees n1.brother n2.brother
    | (LocAct (_, _) | DeadEnd), (LocAct (_, _) | DeadEnd) -> true
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

let delete_rule_in_tree entry =
  let rec delete_in_tree symbols tree =
    match symbols, tree with
      s :: sl, Node n ->
        if logically_eq_symbols entry s n.node then delete_son sl n
        else
          begin match delete_in_tree symbols n.brother with
            Some (dsl, t) ->
              Some (dsl, Node {node = n.node; son = n.son; brother = t})
          | None -> None
          end
    | s :: sl, _ -> None
    | [], Node n ->
        begin match delete_in_tree [] n.brother with
          Some (dsl, t) ->
            Some (dsl, Node {node = n.node; son = n.son; brother = t})
        | None -> None
        end
    | [], DeadEnd -> None
    | [], LocAct (_, []) -> Some (Some [], DeadEnd)
    | [], LocAct (_, action :: list) -> Some (None, LocAct (action, list))
  and delete_son sl n =
    match delete_in_tree sl n.son with
      Some (Some dsl, DeadEnd) -> Some (Some (n.node :: dsl), n.brother)
    | Some (Some dsl, t) ->
        let t = Node {node = n.node; son = t; brother = n.brother} in
        Some (Some (n.node :: dsl), t)
    | Some (None, t) ->
        let t = Node {node = n.node; son = t; brother = n.brother} in
        Some (None, t)
    | None -> None
  in
  delete_in_tree

let rec decr_keyw_use gram =
  function
    Stoken tok ->
      let r = Hashtbl.find gram.gtokens tok in
      decr r;
      if !r == 0 then
        begin
          Hashtbl.remove gram.gtokens tok;
          gram.glexer.Plexing.tok_removing tok
        end
  | Slist0 s -> decr_keyw_use gram s
  | Slist1 s -> decr_keyw_use gram s
  | Slist0sep (s1, s2, _) -> decr_keyw_use gram s1; decr_keyw_use gram s2
  | Slist1sep (s1, s2, _) -> decr_keyw_use gram s1; decr_keyw_use gram s2
  | Sopt s -> decr_keyw_use gram s
  | Stree t -> decr_keyw_use_in_tree gram t
  | Sself | Snext | Scut | Snterm _ | Snterml (_, _) -> ()
and decr_keyw_use_in_tree gram =
  function
    DeadEnd | LocAct (_, _) -> ()
  | Node n ->
      decr_keyw_use gram n.node;
      decr_keyw_use_in_tree gram n.son;
      decr_keyw_use_in_tree gram n.brother

let rec delete_rule_in_suffix entry symbols =
  function
    lev :: levs ->
      begin match delete_rule_in_tree entry symbols lev.lsuffix with
        Some (dsl, t) ->
          begin match dsl with
            Some dsl -> List.iter (decr_keyw_use entry.egram) dsl
          | None -> ()
          end;
          begin match t with
            DeadEnd when lev.lprefix == DeadEnd -> levs
          | _ ->
              let lev =
                {assoc = lev.assoc; lname = lev.lname; lsuffix = t;
                 lprefix = lev.lprefix}
              in
              lev :: levs
          end
      | None ->
          let levs = delete_rule_in_suffix entry symbols levs in lev :: levs
      end
  | [] -> raise Not_found

let rec delete_rule_in_prefix entry symbols =
  function
    lev :: levs ->
      begin match delete_rule_in_tree entry symbols lev.lprefix with
        Some (dsl, t) ->
          begin match dsl with
            Some dsl -> List.iter (decr_keyw_use entry.egram) dsl
          | None -> ()
          end;
          begin match t with
            DeadEnd when lev.lsuffix == DeadEnd -> levs
          | _ ->
              let lev =
                {assoc = lev.assoc; lname = lev.lname; lsuffix = lev.lsuffix;
                 lprefix = t}
              in
              lev :: levs
          end
      | None ->
          let levs = delete_rule_in_prefix entry symbols levs in lev :: levs
      end
  | [] -> raise Not_found

let delete_rule_in_level_list entry symbols levs =
  match symbols with
    Sself :: symbols -> delete_rule_in_suffix entry symbols levs
  | Snterm e :: symbols when e == entry ->
      delete_rule_in_suffix entry symbols levs
  | _ -> delete_rule_in_prefix entry symbols levs
