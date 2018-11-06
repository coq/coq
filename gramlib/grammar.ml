(* camlp5r *)
(* grammar.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Gramext
open Format

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
    let loc1 = !floc bp in let loc2 = !floc (pred ep) in Ploc.encl loc1 loc2

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

let search_tree_in_entry prev_symb tree =
  function
    Dlevels levels ->
      let rec search_levels =
        function
          [] -> tree
        | level :: levels ->
            match search_level level with
              Some tree -> tree
            | None -> search_levels levels
      and search_level level =
        match search_tree level.lsuffix with
          Some t -> Some (Node {node = Sself; son = t; brother = DeadEnd})
        | None -> search_tree level.lprefix
      and search_tree t =
        if tree <> DeadEnd && t == tree then Some t
        else
          match t with
            Node n ->
              begin match search_symbol n.node with
                Some symb ->
                  Some (Node {node = symb; son = n.son; brother = DeadEnd})
              | None ->
                  match search_tree n.son with
                    Some t ->
                      Some (Node {node = n.node; son = t; brother = DeadEnd})
                  | None -> search_tree n.brother
              end
          | LocAct (_, _) | DeadEnd -> None
      and search_symbol symb =
        match symb with
          Snterm _ | Snterml (_, _) | Slist0 _ | Slist0sep (_, _, _) |
          Slist1 _ | Slist1sep (_, _, _) | Sopt _ | Stoken _ | Stree _
          when symb == prev_symb ->
            Some symb
        | Slist0 symb ->
            begin match search_symbol symb with
              Some symb -> Some (Slist0 symb)
            | None -> None
            end
        | Slist0sep (symb, sep, b) ->
            begin match search_symbol symb with
              Some symb -> Some (Slist0sep (symb, sep, b))
            | None ->
                match search_symbol sep with
                  Some sep -> Some (Slist0sep (symb, sep, b))
                | None -> None
            end
        | Slist1 symb ->
            begin match search_symbol symb with
              Some symb -> Some (Slist1 symb)
            | None -> None
            end
        | Slist1sep (symb, sep, b) ->
            begin match search_symbol symb with
              Some symb -> Some (Slist1sep (symb, sep, b))
            | None ->
                match search_symbol sep with
                  Some sep -> Some (Slist1sep (symb, sep, b))
                | None -> None
            end
        | Sopt symb ->
            begin match search_symbol symb with
              Some symb -> Some (Sopt symb)
            | None -> None
            end
        | Stree t ->
            begin match search_tree t with
              Some t -> Some (Stree t)
            | None -> None
            end
        | _ -> None
      in
      search_levels levels
  | Dparser _ -> tree

let error_verbose = ref false

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
  if !error_verbose then
    begin let tree = search_tree_in_entry prev_symb tree entry.edesc in
      let ppf = err_formatter in
      fprintf ppf "@[<v 0>@,";
      fprintf ppf "----------------------------------@,";
      fprintf ppf "Parse error in entry [%s], rule:@;<0 2>" entry.ename;
      fprintf ppf "@[";
      print_level ppf pp_force_newline (flatten_tree tree);
      fprintf ppf "@]@,";
      fprintf ppf "----------------------------------@,";
      fprintf ppf "@]@."
    end;
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
  if Stream.count strm == bp then Gramext.action (fun a -> p strm)
  else raise Stream.Failure

let continue entry bp a s son p1 (strm__ : _ Stream.t) =
  let a = (entry_of_symb entry s).econtinue 0 bp a strm__ in
  let act =
    try p1 strm__ with
      Stream.Failure -> raise (Stream.Error (tree_failed entry a s son))
  in
  Gramext.action (fun _ -> app act a)

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

let strict_parsing = ref false

let recover parser_of_tree entry nlevn alevn bp a s son strm =
  if !strict_parsing then raise (Stream.Error (tree_failed entry a s son))
  else do_recover parser_of_tree entry nlevn alevn bp a s son strm

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

let extend_entry entry position rules =
  try
    let elev = Gramext.levels_of_rules entry position rules in
    entry.edesc <- Dlevels elev; init_entry_functions entry
  with Plexing.Error s ->
    Printf.eprintf "Lexer initialization error:\n- %s\n" s;
    flush stderr;
    failwith "Grammar.extend"

(* Deleting a rule *)

let delete_rule entry sl =
  match entry.edesc with
    Dlevels levs ->
      let levs = Gramext.delete_rule_in_level_list entry sl levs in
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

let glexer g = g.glexer

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
      else Ploc.encl loc (fun_loc (!token_count - 1))
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

let gram_reinit g glexer = Hashtbl.clear g.gtokens; g.glexer <- glexer

(* Functorial interface *)

module type GLexerType = sig type te val lexer : te Plexing.lexer end

module type S =
  sig
    type te
    type parsable
    val parsable : char Stream.t -> parsable
    val tokens : string -> (string * int) list
    val glexer : te Plexing.lexer
    module Entry :
      sig
        type 'a e
        val create : string -> 'a e
        val parse : 'a e -> parsable -> 'a
        val name : 'a e -> string
        val of_parser : string -> (te Stream.t -> 'a) -> 'a e
        val parse_token_stream : 'a e -> te Stream.t -> 'a
        val print : Format.formatter -> 'a e -> unit
        external obj : 'a e -> te Gramext.g_entry = "%identity"
        val parse_token : 'a e -> te Stream.t -> 'a
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
    val s_rules : 'a ty_production list -> ('self, 'a) ty_symbol
    val r_stop : ('self, 'r, 'r) ty_rule
    val r_next :
      ('self, 'a, 'r) ty_rule -> ('self, 'b) ty_symbol ->
        ('self, 'b -> 'a, 'r) ty_rule
    val production : ('a, 'f, Ploc.t -> 'a) ty_rule * 'f -> 'a ty_production
    module Unsafe :
      sig
        val gram_reinit : te Plexing.lexer -> unit
        val clear_entry : 'a Entry.e -> unit
      end
    val extend :
      'a Entry.e -> Gramext.position option ->
        (string option * Gramext.g_assoc option *
           (te Gramext.g_symbol list * Gramext.g_action) list)
          list ->
        unit
    val safe_extend :
      'a Entry.e -> Gramext.position option ->
        (string option * Gramext.g_assoc option * 'a ty_production list)
          list ->
        unit
    val delete_rule : 'a Entry.e -> te Gramext.g_symbol list -> unit
    val safe_delete_rule : 'a Entry.e -> ('a, 'r, 'f) ty_rule -> unit
  end

module GMake (L : GLexerType) =
  struct
    type te = L.te
    type parsable = te gen_parsable
    let gram = gcreate L.lexer
    let parsable cs =
      let (ts, lf) = L.lexer.Plexing.tok_func cs in
      {pa_chr_strm = cs; pa_tok_strm = ts; pa_loc_func = lf}
    let tokens = tokens gram
    let glexer = glexer gram
    module Entry =
      struct
        type 'a e = te g_entry
        let create n =
          {egram = gram; ename = n; elocal = false; estart = empty_entry n;
           econtinue =
             (fun _ _ _ (strm__ : _ Stream.t) -> raise Stream.Failure);
           edesc = Dlevels []}
        external obj : 'a e -> te Gramext.g_entry = "%identity"
        let parse (e : 'a e) p : 'a =
          Obj.magic (parse_parsable e p : Obj.t)
        let parse_token_stream (e : 'a e) ts : 'a =
          Obj.magic (e.estart 0 ts : Obj.t)
        let _warned_using_parse_token = ref false
        let parse_token (entry : 'a e) ts : 'a =
          (* commented: too often warned in Coq...
          if not warned_using_parse_token.val then do {
            eprintf "<W> use of Entry.parse_token ";
            eprintf "deprecated since 2017-06-16\n%!";
            eprintf "use Entry.parse_token_stream instead\n%! ";
            warned_using_parse_token.val := True
          }
          else ();
          *)
          parse_token_stream entry ts
        let name e = e.ename
        let of_parser n (p : te Stream.t -> 'a) : 'a e =
          {egram = gram; ename = n; elocal = false;
           estart = (fun _ -> (Obj.magic p : te Stream.t -> Obj.t));
           econtinue =
             (fun _ _ _ (strm__ : _ Stream.t) -> raise Stream.Failure);
           edesc = Dparser (Obj.magic p : te Stream.t -> Obj.t)}
        let print ppf e = fprintf ppf "%a@." print_entry (obj e)
      end
    type ('self, 'a) ty_symbol = te Gramext.g_symbol
    type ('self, 'f, 'r) ty_rule = ('self, Obj.t) ty_symbol list
    type 'a ty_production = ('a, Obj.t, Obj.t) ty_rule * Gramext.g_action
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
    let s_rules (t : Obj.t ty_production list) = Gramext.srules (Obj.magic t)
    let r_stop = []
    let r_next r s = r @ [s]
    let production
        (p : ('a, 'f, Ploc.t -> 'a) ty_rule * 'f) : 'a ty_production =
      Obj.magic p
    module Unsafe =
      struct
        let gram_reinit = gram_reinit gram
        let clear_entry = clear_entry
      end
    let extend = extend_entry
    let safe_extend e pos
        (r :
         (string option * Gramext.g_assoc option * Obj.t ty_production list)
           list) =
      extend e pos (Obj.magic r)
    let delete_rule e r = delete_rule (Entry.obj e) r
    let safe_delete_rule = delete_rule
  end
