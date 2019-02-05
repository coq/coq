(* camlp5r *)
(* grammar.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Gramext
open Format

(* Functorial interface *)

module type GLexerType = sig type te val lexer : te Plexing.lexer end

module type S =
  sig
    type te
    type parsable
    val parsable : char Stream.t -> parsable
    val tokens : string -> (string * int) list
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
    val s_self : ('self, 'self) ty_symbol
    val s_next : ('self, 'self) ty_symbol
    val s_token : Plexing.pattern -> ('self, string) ty_symbol
    val s_rules : warning:(string -> unit) option -> 'a ty_production list -> ('self, 'a) ty_symbol
    val r_stop : ('self, 'r, 'r) ty_rule
    val r_next :
      ('self, 'a, 'r) ty_rule -> ('self, 'b) ty_symbol ->
        ('self, 'b -> 'a, 'r) ty_rule
    val production : ('a, 'f, Loc.t -> 'a) ty_rule * 'f -> 'a ty_production
    module Unsafe :
      sig
        val clear_entry : 'a Entry.e -> unit
      end
    val safe_extend : warning:(string -> unit) option ->
      'a Entry.e -> Gramext.position option ->
        (string option * Gramext.g_assoc option * 'a ty_production list)
          list ->
        unit
    val safe_delete_rule : 'a Entry.e -> ('a, 'r, 'f) ty_rule -> unit
  end

(* Implementation *)

module GMake (L : GLexerType) =
struct

type 'a parser_t = 'a Stream.t -> Obj.t

type 'te grammar =
  { gtokens : (Plexing.pattern, int ref) Hashtbl.t;
    glexer : 'te Plexing.lexer }

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
  | Stoken of Plexing.pattern
  | Stree of 'te g_tree
and g_action = Obj.t
and 'te g_tree =
    Node of 'te g_node
  | LocAct of g_action * g_action list
  | DeadEnd
and 'te g_node =
  { node : 'te g_symbol; son : 'te g_tree; brother : 'te g_tree }

let rec derive_eps =
  function
    Slist0 _ -> true
  | Slist0sep (_, _, _) -> true
  | Sopt _ -> true
  | Stree t -> tree_derive_eps t
  | Slist1 _ | Slist1sep (_, _, _) | Snterm _ |
    Snterml (_, _) | Snext | Sself | Stoken _ ->
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

let insert_tree ~warning entry_name gsymbols action tree =
  let rec insert symbols tree =
    match symbols with
      s :: sl -> insert_in_tree s sl tree
    | [] ->
        match tree with
          Node {node = s; son = son; brother = bro} ->
            Node {node = s; son = son; brother = insert [] bro}
        | LocAct (old_action, action_list) ->
          begin match warning with
            | None -> ()
            | Some warn_fn ->
              let msg =
                "<W> Grammar extension: " ^
                (if entry_name <> "" then "" else "in ["^entry_name^"%s], ") ^
                "some rule has been masked" in
              warn_fn msg
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

let srules ~warning rl =
  let t =
    List.fold_left
      (fun tree (symbols, action) -> insert_tree ~warning "" symbols action tree)
      DeadEnd rl
  in
  Stree t

let is_level_labelled n lev =
  match lev.lname with
    Some n1 -> n = n1
  | None -> false

let insert_level ~warning entry_name e1 symbols action slev =
  match e1 with
    true ->
      {assoc = slev.assoc; lname = slev.lname;
       lsuffix = insert_tree ~warning entry_name symbols action slev.lsuffix;
       lprefix = slev.lprefix}
  | false ->
      {assoc = slev.assoc; lname = slev.lname; lsuffix = slev.lsuffix;
       lprefix = insert_tree ~warning entry_name symbols action slev.lprefix}

let empty_lev lname assoc =
  let assoc =
    match assoc with
      Some a -> a
    | None -> LeftA
  in
  {assoc = assoc; lname = lname; lsuffix = DeadEnd; lprefix = DeadEnd}

let change_lev ~warning lev n lname assoc =
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
    | Snterm _ | Snterml (_, _) | Snext | Sself -> ()
  and tinsert =
    function
      Node {node = s; brother = bro; son = son} ->
        insert s; tinsert bro; tinsert son
    | LocAct (_, _) | DeadEnd -> ()
  in
  List.iter insert symbols

let levels_of_rules ~warning entry position rules =
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
    let (levs1, make_lev, levs2) = get_level ~warning entry position elev in
    let (levs, _) =
      List.fold_left
        (fun (levs, make_lev) (lname, assoc, level) ->
           let lev = make_lev lname assoc in
           let lev =
             List.fold_left
               (fun lev (symbols, action) ->
                  let symbols = List.map (change_to_self entry) symbols in
                  let (e1, symbols) = get_initial entry symbols in
                  insert_tokens entry.egram symbols;
                  insert_level ~warning entry.ename e1 symbols action lev)
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
  | Sself | Snext | Snterm _ | Snterml (_, _) -> ()
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

external gramext_action : 'a -> g_action = "%identity"

let rec flatten_tree =
  function
    DeadEnd -> []
  | LocAct (_, _) -> [[]]
  | Node {node = n; brother = b; son = s} ->
      List.map (fun l -> n :: l) (flatten_tree s) @ flatten_tree b

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

let rec print_symbol ppf =
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
  | Stoken (con, prm) when con <> "" && prm <> "" ->
      fprintf ppf "%s@ %a" con print_str prm
  | Snterml (e, l) ->
      fprintf ppf "%s%s@ LEVEL@ %a" e.ename (if e.elocal then "*" else "")
        print_str l
  | Snterm _ | Snext | Sself | Stoken _ | Stree _ as s ->
      print_symbol1 ppf s
and print_symbol1 ppf =
  function
  | Snterm e -> fprintf ppf "%s%s" e.ename (if e.elocal then "*" else "")
  | Sself -> pp_print_string ppf "SELF"
  | Snext -> pp_print_string ppf "NEXT"
  | Stoken ("", s) -> print_str ppf s
  | Stoken (con, "") -> pp_print_string ppf con
  | Stree t -> print_level ppf pp_print_space (flatten_tree t)
  | Snterml (_, _) | Slist0 _ | Slist0sep (_, _, _) |
    Slist1 _ | Slist1sep (_, _, _) | Sopt _ | Stoken _ as s ->
      fprintf ppf "(%a)" print_symbol s
and print_rule ppf symbols =
  fprintf ppf "@[<hov 0>";
  let _ =
    List.fold_left
      (fun sep symbol ->
         fprintf ppf "%t%a" sep print_symbol symbol;
         fun ppf -> fprintf ppf ";@ ")
      (fun ppf -> ()) symbols
  in
  fprintf ppf "@]"
and print_level ppf pp_print_space rules =
  fprintf ppf "@[<hov 0>[ ";
  let _ =
    List.fold_left
      (fun sep rule ->
         fprintf ppf "%t%a" sep print_rule rule;
         fun ppf -> fprintf ppf "%a| " pp_print_space ())
      (fun ppf -> ()) rules
  in
  fprintf ppf " ]@]"

let print_levels ppf elev =
  let _ =
    List.fold_left
      (fun sep lev ->
         let rules =
           List.map (fun t -> Sself :: t) (flatten_tree lev.lsuffix) @
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
      (fun ppf -> ()) elev
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

let name_of_symbol entry =
  function
    Snterm e -> "[" ^ e.ename ^ "]"
  | Snterml (e, l) -> "[" ^ e.ename ^ " level " ^ l ^ "]"
  | Sself | Snext -> "[" ^ entry.ename ^ "]"
  | Stoken tok -> entry.egram.glexer.Plexing.tok_text tok
  | _ -> "???"

let rec get_token_list entry rev_tokl last_tok tree =
  match tree with
    Node {node = Stoken tok; son = son; brother = DeadEnd} ->
      get_token_list entry (last_tok :: rev_tokl) tok son
  | _ -> if rev_tokl = [] then None else Some (rev_tokl, last_tok, tree)

let rec name_of_symbol_failed entry =
  function
  | Slist0 s -> name_of_symbol_failed entry s
  | Slist0sep (s, _, _) -> name_of_symbol_failed entry s
  | Slist1 s -> name_of_symbol_failed entry s
  | Slist1sep (s, _, _) -> name_of_symbol_failed entry s
  | Sopt s -> name_of_symbol_failed entry s
  | Stree t -> name_of_tree_failed entry t
  | s -> name_of_symbol entry s
and name_of_tree_failed entry =
  function
    Node {node = s; brother = bro; son = son} ->
      let tokl =
        match s with
          Stoken tok -> get_token_list entry [] tok son
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
              DeadEnd | LocAct (_, _) -> txt
            | Node _ -> txt ^ " or " ^ name_of_tree_failed entry bro
          in
          txt
      | Some (rev_tokl, last_tok, son) ->
          List.fold_left
            (fun s tok ->
               (if s = "" then "" else s ^ " ") ^
               entry.egram.glexer.Plexing.tok_text tok)
            "" (List.rev (last_tok :: rev_tokl))
      end
  | DeadEnd | LocAct (_, _) -> "???"

let tree_failed entry prev_symb_result prev_symb tree =
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
        begin match Obj.magic prev_symb_result with
          [] ->
            let txt1 = name_of_symbol_failed entry s in
            txt1 ^ " or " ^ txt ^ " expected"
        | _ ->
            let txt1 = name_of_symbol_failed entry sep in
            txt1 ^ " or " ^ txt ^ " expected"
        end
    | Slist1sep (s, sep, _) ->
        begin match Obj.magic prev_symb_result with
          [] ->
            let txt1 = name_of_symbol_failed entry s in
            txt1 ^ " or " ^ txt ^ " expected"
        | _ ->
            let txt1 = name_of_symbol_failed entry sep in
            txt1 ^ " or " ^ txt ^ " expected"
        end
    | Sopt _ | Stree _ -> txt ^ " expected"
    | _ -> txt ^ " expected after " ^ name_of_symbol_failed entry prev_symb
  in
  txt ^ " (in [" ^ entry.ename ^ "])"

let symb_failed entry prev_symb_result prev_symb symb =
  let tree = Node {node = symb; brother = DeadEnd; son = DeadEnd} in
  tree_failed entry prev_symb_result prev_symb tree

external app : Obj.t -> 'a = "%identity"

let is_level_labelled n lev =
  match lev.lname with
    Some n1 -> n = n1
  | None -> false

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

let rec top_symb entry =
  function
    Sself | Snext -> Snterm entry
  | Snterml (e, _) -> Snterm e
  | Slist1sep (s, sep, b) -> Slist1sep (top_symb entry s, sep, b)
  | _ -> raise Stream.Failure

let entry_of_symb entry =
  function
    Sself | Snext -> entry
  | Snterm e -> e
  | Snterml (e, _) -> e
  | _ -> raise Stream.Failure

let top_tree entry =
  function
    Node {node = s; brother = bro; son = son} ->
      Node {node = top_symb entry s; brother = bro; son = son}
  | LocAct (_, _) | DeadEnd -> raise Stream.Failure

let skip_if_empty bp p strm =
  if Stream.count strm == bp then gramext_action (fun a -> p strm)
  else raise Stream.Failure

let continue entry bp a s son p1 (strm__ : _ Stream.t) =
  let a = (entry_of_symb entry s).econtinue 0 bp a strm__ in
  let act =
    try p1 strm__ with
      Stream.Failure -> raise (Stream.Error (tree_failed entry a s son))
  in
  gramext_action (fun _ -> app act a)

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
  let tematch = gram.glexer.Plexing.tok_match tok in
  fun tok -> Obj.repr (tematch tok : string)

let rec parser_of_tree entry nlevn alevn =
  function
    DeadEnd -> (fun (strm__ : _ Stream.t) -> raise Stream.Failure)
  | LocAct (act, _) -> (fun (strm__ : _ Stream.t) -> act)
  | Node {node = Sself; son = LocAct (act, _); brother = DeadEnd} ->
      (fun (strm__ : _ Stream.t) ->
         let a = entry.estart alevn strm__ in app act a)
  | Node {node = Sself; son = LocAct (act, _); brother = bro} ->
      let p2 = parser_of_tree entry nlevn alevn bro in
      (fun (strm__ : _ Stream.t) ->
         match
           try Some (entry.estart alevn strm__) with Stream.Failure -> None
         with
           Some a -> app act a
         | _ -> p2 strm__)
  | Node {node = s; son = son; brother = DeadEnd} ->
      let tokl =
        match s with
          Stoken tok -> get_token_list entry [] tok son
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
             app act a)
      | Some (rev_tokl, last_tok, son) ->
          let lt = Stoken last_tok in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn lt son in
          parser_of_token_list entry s son p1
            (fun (strm__ : _ Stream.t) -> raise Stream.Failure) rev_tokl
            last_tok
      end
  | Node {node = s; son = son; brother = bro} ->
      let tokl =
        match s with
          Stoken tok -> get_token_list entry [] tok son
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
                   Some act -> app act a
                 | None -> raise (Stream.Error (tree_failed entry a s son))
                 end
             | None -> p2 strm)
      | Some (rev_tokl, last_tok, son) ->
          let lt = Stoken last_tok in
          let p2 = parser_of_tree entry nlevn alevn bro in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn lt son in
          let p1 =
            parser_of_token_list entry lt son p1 p2 rev_tokl last_tok
          in
          fun (strm__ : _ Stream.t) ->
            try p1 strm__ with Stream.Failure -> p2 strm__
and parser_cont p1 entry nlevn alevn s son bp a (strm__ : _ Stream.t) =
  try p1 strm__ with
    Stream.Failure ->
      recover parser_of_tree entry nlevn alevn bp a s son strm__
and parser_of_token_list entry s son p1 p2 rev_tokl last_tok =
  let plast =
    let n = List.length rev_tokl + 1 in
    let tematch = token_ematch entry.egram last_tok in
    let ps strm =
      match peek_nth n strm with
        Some tok ->
          let r = tematch tok in
          for _i = 1 to n do Stream.junk strm done; Obj.repr r
      | None -> raise Stream.Failure
    in
    fun (strm : _ Stream.t) ->
      let bp = Stream.count strm in
      let a = ps strm in
      match try Some (p1 bp a strm) with Stream.Failure -> None with
        Some act -> app act a
      | None -> raise (Stream.Error (tree_failed entry a s son))
  in
  match List.rev rev_tokl with
    [] -> (fun (strm__ : _ Stream.t) -> plast strm__)
  | tok :: tokl ->
      let tematch = token_ematch entry.egram tok in
      let ps strm =
        match peek_nth 1 strm with
          Some tok -> tematch tok
        | None -> raise Stream.Failure
      in
      let p1 =
        let rec loop n =
          function
            [] -> plast
          | tok :: tokl ->
              let tematch = token_ematch entry.egram tok in
              let ps strm =
                match peek_nth n strm with
                  Some tok -> tematch tok
                | None -> raise Stream.Failure
              in
              let p1 = loop (n + 1) tokl in
              fun (strm__ : _ Stream.t) ->
                let a = ps strm__ in let act = p1 strm__ in app act a
        in
        loop 2 tokl
      in
      fun (strm__ : _ Stream.t) ->
        let a = ps strm__ in let act = p1 strm__ in app act a
and parser_of_symbol entry nlevn =
  function
  | Slist0 s ->
      let ps = call_and_push (parser_of_symbol entry nlevn s) in
      let rec loop al (strm__ : _ Stream.t) =
        match try Some (ps al strm__) with Stream.Failure -> None with
          Some al -> loop al strm__
        | _ -> al
      in
      (fun (strm__ : _ Stream.t) ->
         let a = loop [] strm__ in Obj.repr (List.rev a))
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
           Some al -> let a = kont al strm__ in Obj.repr (List.rev a)
         | _ -> Obj.repr [])
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
           Some al -> let a = kont al strm__ in Obj.repr (List.rev a)
         | _ -> Obj.repr [])
  | Slist1 s ->
      let ps = call_and_push (parser_of_symbol entry nlevn s) in
      let rec loop al (strm__ : _ Stream.t) =
        match try Some (ps al strm__) with Stream.Failure -> None with
          Some al -> loop al strm__
        | _ -> al
      in
      (fun (strm__ : _ Stream.t) ->
         let al = ps [] strm__ in
         let a = loop al strm__ in Obj.repr (List.rev a))
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
         let a = kont al strm__ in Obj.repr (List.rev a))
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
         let a = kont al strm__ in Obj.repr (List.rev a))
  | Sopt s ->
      let ps = parser_of_symbol entry nlevn s in
      (fun (strm__ : _ Stream.t) ->
         match try Some (ps strm__) with Stream.Failure -> None with
           Some a -> Obj.repr (Some a)
         | _ -> Obj.repr None)
  | Stree t ->
      let pt = parser_of_tree entry 1 0 t in
      (fun (strm__ : _ Stream.t) ->
         let bp = Stream.count strm__ in
         let a = pt strm__ in
         let ep = Stream.count strm__ in
         let loc = loc_of_token_interval bp ep in app a loc)
  | Snterm e -> (fun (strm__ : _ Stream.t) -> e.estart 0 strm__)
  | Snterml (e, l) ->
      (fun (strm__ : _ Stream.t) -> e.estart (level_number e l) strm__)
  | Sself -> (fun (strm__ : _ Stream.t) -> entry.estart 0 strm__)
  | Snext -> (fun (strm__ : _ Stream.t) -> entry.estart nlevn strm__)
  | Stoken tok -> parser_of_token entry tok
and parser_of_token entry tok =
  let f = entry.egram.glexer.Plexing.tok_match tok in
  fun strm ->
    match Stream.peek strm with
      Some tok -> let r = f tok in Stream.junk strm; Obj.repr r
    | None -> raise Stream.Failure
and parse_top_symb entry symb = parser_of_symbol entry 0 (top_symb entry symb)

let rec start_parser_of_levels entry clevn =
  function
    [] -> (fun levn (strm__ : _ Stream.t) -> raise Stream.Failure)
  | lev :: levs ->
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
                 let a = app act (loc_of_token_interval bp ep) in
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
                      let a = app act (loc_of_token_interval bp ep) in
                      entry.econtinue levn bp a strm
                  | _ -> p1 levn strm__

let rec continue_parser_of_levels entry clevn =
  function
    [] -> (fun levn bp a (strm__ : _ Stream.t) -> raise Stream.Failure)
  | lev :: levs ->
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
                  let a = app act a (loc_of_token_interval bp ep) in
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
    let elev = Gramext.levels_of_rules ~warning entry position rules in
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

let create_toktab () = Hashtbl.create 301
let gcreate glexer =
  {gtokens = create_toktab (); glexer = glexer }

let tokens g con =
  let list = ref [] in
  Hashtbl.iter
    (fun (p_con, p_prm) c -> if p_con = con then list := (p_prm, !c) :: !list)
    g.gtokens;
  !list

type 'te gen_parsable =
  { pa_chr_strm : char Stream.t;
    pa_tok_strm : 'te Stream.t;
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

    type te = L.te
    type parsable = te gen_parsable
    let gram = gcreate L.lexer
    let parsable cs =
      let (ts, lf) = L.lexer.Plexing.tok_func cs in
      {pa_chr_strm = cs; pa_tok_strm = ts; pa_loc_func = lf}
    let tokens = tokens gram
    module Entry =
      struct
        type 'a e = te g_entry
        let create n =
          {egram = gram; ename = n; elocal = false; estart = empty_entry n;
           econtinue =
             (fun _ _ _ (strm__ : _ Stream.t) -> raise Stream.Failure);
           edesc = Dlevels []}
        external obj : 'a e -> te g_entry = "%identity"
        let parse (e : 'a e) p : 'a =
          Obj.magic (parse_parsable e p : Obj.t)
        let parse_token_stream (e : 'a e) ts : 'a =
          Obj.magic (e.estart 0 ts : Obj.t)
        let name e = e.ename
        let of_parser n (p : te Stream.t -> 'a) : 'a e =
          {egram = gram; ename = n; elocal = false;
           estart = (fun _ -> (Obj.magic p : te Stream.t -> Obj.t));
           econtinue =
             (fun _ _ _ (strm__ : _ Stream.t) -> raise Stream.Failure);
           edesc = Dparser (Obj.magic p : te Stream.t -> Obj.t)}
        let print ppf e = fprintf ppf "%a@." print_entry (obj e)
      end
    type ('self, 'a) ty_symbol = te g_symbol
    type ('self, 'f, 'r) ty_rule = ('self, Obj.t) ty_symbol list
    type 'a ty_production = ('a, Obj.t, Obj.t) ty_rule * g_action
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
    let s_rules ~warning (t : Obj.t ty_production list) = srules ~warning (Obj.magic t)
    let r_stop = []
    let r_next r s = r @ [s]
    let production
        (p : ('a, 'f, Loc.t -> 'a) ty_rule * 'f) : 'a ty_production =
      Obj.magic p
    module Unsafe =
      struct
        let clear_entry = clear_entry
      end
    let safe_extend ~warning e pos
        (r :
         (string option * Gramext.g_assoc option * Obj.t ty_production list)
           list) =
      extend_entry ~warning e pos (Obj.magic r)
    let safe_delete_rule e r = delete_rule (Entry.obj e) r

end
