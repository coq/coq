(* camlp5r *)
(* grammar.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_fstream.cmo";

value pervasives_stderr = stderr;

open Gramext;
open Format;

value stderr = pervasives_stderr;

value rec flatten_tree =
  fun
  [ DeadEnd -> []
  | LocAct _ _ -> [[]]
  | Node {node = n; brother = b; son = s} ->
      List.map (fun l -> [n :: l]) (flatten_tree s) @ flatten_tree b ]
;

value utf8_print = ref True;

value utf8_string_escaped s =
  let b = Buffer.create (String.length s) in
  loop 0 where rec loop i =
    if i = String.length s then Buffer.contents b
    else do {
      match s.[i] with
      | '"' → Buffer.add_string b "\\\""
      | '\\' → Buffer.add_string b "\\\\"
      | '\n' → Buffer.add_string b "\\n"
      | '\t' → Buffer.add_string b "\\t"
      | '\r' → Buffer.add_string b "\\r"
      | '\b' → Buffer.add_string b "\\b"
      | c → Buffer.add_char b c
      end;
      loop (i + 1)
    }
;

value string_escaped s =
  if utf8_print.val then utf8_string_escaped s
  else String.escaped s
;

value print_str ppf s = fprintf ppf "\"%s\"" (string_escaped s);

value rec print_symbol ppf =
  fun
  [ Sfacto s -> print_symbol ppf s
  | Smeta n sl _ -> print_meta ppf n sl
  | Slist0 s -> fprintf ppf "LIST0 %a" print_symbol1 s
  | Slist0sep s t osep ->
      fprintf ppf "LIST0 %a SEP %a%s" print_symbol1 s print_symbol1 t
        (if osep then " OPT_SEP" else "")
  | Slist1 s -> fprintf ppf "LIST1 %a" print_symbol1 s
  | Slist1sep s t osep ->
      fprintf ppf "LIST1 %a SEP %a%s" print_symbol1 s print_symbol1 t
        (if osep then " OPT_SEP" else "")
  | Sopt s -> fprintf ppf "OPT %a" print_symbol1 s
  | Sflag s -> fprintf ppf "FLAG %a" print_symbol1 s
  | Stoken (con, prm) when con <> "" && prm <> "" ->
      fprintf ppf "%s@ %a" con print_str prm
  | Svala _ s -> fprintf ppf "V %a" print_symbol s
  | Snterml e l ->
      fprintf ppf "%s%s@ LEVEL@ %a" e.ename (if e.elocal then "*" else "")
        print_str l
  | Snterm _ | Snext | Sself | Scut | Stoken _ | Stree _ as s ->
      print_symbol1 ppf s ]
and print_meta ppf n sl =
  loop 0 sl where rec loop i =
    fun
    [ [] -> ()
    | [s :: sl] -> do {
        let j =
          try String.index_from n i ' ' with [ Not_found -> String.length n ]
        in
        fprintf ppf "%s %a" (String.sub n i (j - i)) print_symbol1 s;
        if sl = [] then ()
        else do { fprintf ppf " "; loop (min (j + 1) (String.length n)) sl }
      } ]
and print_symbol1 ppf =
  fun
  [ Sfacto s -> print_symbol1 ppf s
  | Snterm e -> fprintf ppf "%s%s" e.ename (if e.elocal then "*" else "")
  | Sself -> pp_print_string ppf "SELF"
  | Snext -> pp_print_string ppf "NEXT"
  | Scut -> pp_print_string ppf "/"
  | Stoken ("", s) -> print_str ppf s
  | Stoken (con, "") -> pp_print_string ppf con
  | Stree t -> print_level ppf pp_print_space (flatten_tree t)
  | Smeta _ _ _ | Snterml _ _ | Slist0 _ | Slist0sep _ _ _ | Slist1 _ |
    Slist1sep _ _ _ | Sopt _ | Sflag _ | Stoken _ | Svala _ _ as s ->
      fprintf ppf "(%a)" print_symbol s ]
and print_rule ppf symbols = do {
  fprintf ppf "@[<hov 0>";
  let _ =
    List.fold_left
      (fun sep symbol -> do {
         fprintf ppf "%t%a" sep print_symbol symbol;
         fun ppf -> fprintf ppf ";@ "
       })
      (fun ppf -> ()) symbols
  in
  fprintf ppf "@]"
}
and print_level ppf pp_print_space rules = do {
  fprintf ppf "@[<hov 0>[ ";
  let _ =
    List.fold_left
      (fun sep rule -> do {
         fprintf ppf "%t%a" sep print_rule rule;
         fun ppf -> fprintf ppf "%a| " pp_print_space ()
       })
      (fun ppf -> ()) rules
  in
  fprintf ppf " ]@]"
};

value print_levels ppf elev =
  let _ =
    List.fold_left
      (fun sep lev -> do {
         let rules =
           List.map (fun t -> [Sself :: t]) (flatten_tree lev.lsuffix) @
           flatten_tree lev.lprefix
         in
         fprintf ppf "%t@[<hov 2>" sep;
         match lev.lname with
         [ Some n -> fprintf ppf "%a@;<1 2>" print_str n
         | None -> () ];
         match lev.assoc with
         [ LeftA -> fprintf ppf "LEFTA"
         | RightA -> fprintf ppf "RIGHTA"
         | NonA -> fprintf ppf "NONA" ];
         fprintf ppf "@]@;<1 2>";
         print_level ppf pp_force_newline rules;
         fun ppf -> fprintf ppf "@,| "
       })
      (fun ppf -> ()) elev
  in
  ()
;

value print_entry ppf e = do {
  fprintf ppf "@[<v 0>[ ";
  match e.edesc with
  [ Dlevels elev -> print_levels ppf elev
  | Dparser _ -> fprintf ppf "<parser>" ];
  fprintf ppf " ]@]"
};

value iter_entry f e =
  let treated = ref [] in
  let rec do_entry e =
    if List.memq e treated.val then ()
    else do {
      treated.val := [e :: treated.val];
      f e;
      match e.edesc with
      [ Dlevels ll -> List.iter do_level ll
      | Dparser _ -> () ]
    }
  and do_level lev = do { do_tree lev.lsuffix; do_tree lev.lprefix }
  and do_tree =
    fun
    [ Node n -> do_node n
    | LocAct _ _ | DeadEnd -> () ]
  and do_node n = do { do_symbol n.node; do_tree n.son; do_tree n.brother }
  and do_symbol =
    fun
    [ Sfacto s -> do_symbol s
    | Smeta _ sl _ -> List.iter do_symbol sl
    | Snterm e -> do_entry e
    | Snterml e _ -> do_entry e
    | Slist0 s -> do_symbol s
    | Slist1 s -> do_symbol s
    | Sopt s -> do_symbol s
    | Sflag s -> do_symbol s
    | Slist0sep s1 s2 _ -> do { do_symbol s1; do_symbol s2 }
    | Slist1sep s1 s2 _ -> do { do_symbol s1; do_symbol s2 }
    | Stree t -> do_tree t
    | Svala _ s -> do_symbol s
    | Sself | Snext | Scut | Stoken _ -> () ]
  in
  do_entry e
;

value fold_entry f e init =
  let treated = ref [] in
  let rec do_entry accu e =
    if List.memq e treated.val then accu
    else do {
      treated.val := [e :: treated.val];
      let accu = f e accu in
      match e.edesc with
      [ Dlevels ll -> List.fold_left do_level accu ll
      | Dparser _ -> accu ]
    }
  and do_level accu lev =
    let accu = do_tree accu lev.lsuffix in
    do_tree accu lev.lprefix
  and do_tree accu =
    fun
    [ Node n -> do_node accu n
    | LocAct _ _ | DeadEnd -> accu ]
  and do_node accu n =
    let accu = do_symbol accu n.node in
    let accu = do_tree accu n.son in
    do_tree accu n.brother
  and do_symbol accu =
    fun
    [ Sfacto s -> do_symbol accu s
    | Smeta _ sl _ -> List.fold_left do_symbol accu sl
    | Snterm e -> do_entry accu e
    | Snterml e _ -> do_entry accu e
    | Slist0 s -> do_symbol accu s
    | Slist1 s -> do_symbol accu s
    | Sopt s -> do_symbol accu s
    | Sflag s -> do_symbol accu s
    | Slist0sep s1 s2 _ -> do_symbol (do_symbol accu s1) s2
    | Slist1sep s1 s2 _ -> do_symbol (do_symbol accu s1) s2
    | Stree t -> do_tree accu t
    | Svala _ s -> do_symbol accu s
    | Sself | Snext | Scut | Stoken _ -> accu ]
  in
  do_entry init e
;

value floc = ref (fun _ -> failwith "internal error when computing location");

value loc_of_token_interval bp ep =
  if bp == ep then
    if bp == 0 then Ploc.dummy
    else Ploc.after (floc.val (bp - 1)) 0 1
  else
    let loc1 = floc.val bp in
    let loc2 = floc.val (pred ep) in
    Ploc.encl loc1 loc2
;

value rec name_of_symbol entry =
  fun
  [ Snterm e -> "[" ^ e.ename ^ "]"
  | Snterml e l -> "[" ^ e.ename ^ " level " ^ l ^ "]"
  | Sself | Snext -> "[" ^ entry.ename ^ "]"
  | Stoken tok -> entry.egram.glexer.Plexing.tok_text tok
  | _ -> "???" ]
;

value rec get_token_list entry rev_tokl last_tok tree =
  match tree with
  [ Node {node = Stoken tok; son = son; brother = DeadEnd} ->
      get_token_list entry [last_tok :: rev_tokl] (tok, None) son
  | Node {node = Svala ls (Stoken tok); son = son; brother = DeadEnd} ->
      get_token_list entry [last_tok :: rev_tokl] (tok, Some ls) son
  | _ ->
      if rev_tokl = [] then None
      else Some (rev_tokl, last_tok, tree) ]
;

value rec name_of_symbol_failed entry =
  fun
  [ Sfacto s -> name_of_symbol_failed entry s
  | Slist0 s -> name_of_symbol_failed entry s
  | Slist0sep s _ _ -> name_of_symbol_failed entry s
  | Slist1 s -> name_of_symbol_failed entry s
  | Slist1sep s _ _ -> name_of_symbol_failed entry s
  | Sopt s -> name_of_symbol_failed entry s
  | Sflag s -> name_of_symbol_failed entry s
  | Stree t -> name_of_tree_failed entry t
  | Svala _ s -> name_of_symbol_failed entry s
  | Smeta _ [s :: _] _ -> name_of_symbol_failed entry s
  | s -> name_of_symbol entry s ]
and name_of_tree_failed entry =
  fun
  [ Node {node = s; brother = bro; son = son} ->
      let tokl =
        match s with
        [ Stoken tok -> get_token_list entry [] (tok, None) son
        | Svala ls (Stoken tok) -> get_token_list entry [] (tok, Some ls) son
        | _ -> None ]
      in
      match tokl with
      [ None ->
          let txt = name_of_symbol_failed entry s in
          let txt =
            match (s, son) with
            [ (Sopt _, Node _) -> txt ^ " or " ^ name_of_tree_failed entry son
            | _ -> txt ]
          in
          let txt =
            match bro with
            [ DeadEnd | LocAct _ _ -> txt
            | Node _ -> txt ^ " or " ^ name_of_tree_failed entry bro ]
          in
          txt
      | Some (rev_tokl, last_tok, son) ->
          List.fold_left
            (fun s (tok, _) ->
               (if s = "" then "" else s ^ " ") ^
               entry.egram.glexer.Plexing.tok_text tok)
            "" (List.rev [last_tok :: rev_tokl]) ]
  | DeadEnd | LocAct _ _ -> "???" ]
;

value search_tree_in_entry prev_symb tree =
  fun
  [ Dlevels levels ->
      let rec search_levels =
        fun
        [ [] -> tree
        | [level :: levels] ->
            match search_level level with
            [ Some tree -> tree
            | None -> search_levels levels ] ]
      and search_level level =
        match search_tree level.lsuffix with
        [ Some t -> Some (Node {node = Sself; son = t; brother = DeadEnd})
        | None -> search_tree level.lprefix ]
      and search_tree t =
        if tree <> DeadEnd && t == tree then Some t
        else
          match t with
          [ Node n ->
              match search_symbol n.node with
              [ Some symb ->
                  Some (Node {node = symb; son = n.son; brother = DeadEnd})
              | None ->
                  match search_tree n.son with
                  [ Some t ->
                      Some (Node {node = n.node; son = t; brother = DeadEnd})
                  | None -> search_tree n.brother ] ]
          | LocAct _ _ | DeadEnd -> None ]
      and search_symbol symb =
        match symb with
        [ Snterm _ | Snterml _ _ | Slist0 _ | Slist0sep _ _ _ | Slist1 _ |
          Slist1sep _ _ _ | Sopt _ | Stoken _ | Stree _
          when symb == prev_symb ->
            Some symb
        | Slist0 symb ->
            match search_symbol symb with
            [ Some symb -> Some (Slist0 symb)
            | None -> None ]
        | Slist0sep symb sep b ->
            match search_symbol symb with
            [ Some symb -> Some (Slist0sep symb sep b)
            | None ->
                match search_symbol sep with
                [ Some sep -> Some (Slist0sep symb sep b)
                | None -> None ] ]
        | Slist1 symb ->
            match search_symbol symb with
            [ Some symb -> Some (Slist1 symb)
            | None -> None ]
        | Slist1sep symb sep b ->
            match search_symbol symb with
            [ Some symb -> Some (Slist1sep symb sep b)
            | None ->
                match search_symbol sep with
                [ Some sep -> Some (Slist1sep symb sep b)
                | None -> None ] ]
        | Sopt symb ->
            match search_symbol symb with
            [ Some symb -> Some (Sopt symb)
            | None -> None ]
        | Stree t ->
            match search_tree t with
            [ Some t -> Some (Stree t)
            | None -> None ]
        | _ -> None ]
      in
      search_levels levels
  | Dparser _ -> tree ]
;

value error_verbose = ref False;

value tree_failed entry prev_symb_result prev_symb tree = do {
  let txt = name_of_tree_failed entry tree in
  let txt =
    match prev_symb with
    [ Slist0 s ->
        let txt1 = name_of_symbol_failed entry s in
        txt1 ^ " or " ^ txt ^ " expected"
    | Slist1 s ->
        let txt1 = name_of_symbol_failed entry s in
        txt1 ^ " or " ^ txt ^ " expected"
    | Slist0sep s sep _ ->
        match Obj.magic prev_symb_result with
        [ [] ->
            let txt1 = name_of_symbol_failed entry s in
            txt1 ^ " or " ^ txt ^ " expected"
        | _ ->
            let txt1 = name_of_symbol_failed entry sep in
            txt1 ^ " or " ^ txt ^ " expected" ]
    | Slist1sep s sep _ ->
        match Obj.magic prev_symb_result with
        [ [] ->
            let txt1 = name_of_symbol_failed entry s in
            txt1 ^ " or " ^ txt ^ " expected"
        | _ ->
            let txt1 = name_of_symbol_failed entry sep in
            txt1 ^ " or " ^ txt ^ " expected" ]
    | Sopt _ | Sflag _ | Stree _ | Svala _ _ -> txt ^ " expected"
    | _ -> txt ^ " expected after " ^ name_of_symbol_failed entry prev_symb ]
  in
  if error_verbose.val then do {
    let tree = search_tree_in_entry prev_symb tree entry.edesc in
    let ppf = err_formatter in
    fprintf ppf "@[<v 0>@,";
    fprintf ppf "----------------------------------@,";
    fprintf ppf "Parse error in entry [%s], rule:@;<0 2>" entry.ename;
    fprintf ppf "@[";
    print_level ppf pp_force_newline (flatten_tree tree);
    fprintf ppf "@]@,";
    fprintf ppf "----------------------------------@,";
    fprintf ppf "@]@."
  }
  else ();
  txt ^ " (in [" ^ entry.ename ^ "])"
};

value symb_failed entry prev_symb_result prev_symb symb =
  let tree = Node {node = symb; brother = DeadEnd; son = DeadEnd} in
  tree_failed entry prev_symb_result prev_symb tree
;

external app : Obj.t -> 'a = "%identity";

value is_level_labelled n lev =
  match lev.lname with
  [ Some n1 -> n = n1
  | None -> False ]
;

value level_number entry lab =
  let rec lookup levn =
    fun
    [ [] -> failwith ("unknown level " ^ lab)
    | [lev :: levs] ->
        if is_level_labelled lab lev then levn else lookup (succ levn) levs ]
  in
  match entry.edesc with
  [ Dlevels elev -> lookup 0 elev
  | Dparser _ -> raise Not_found ]
;

value rec top_symb entry =
  fun
  [ Sself | Snext -> Snterm entry
  | Snterml e _ -> Snterm e
  | Slist1sep s sep b -> Slist1sep (top_symb entry s) sep b
  | _ -> raise Stream.Failure ]
;

value entry_of_symb entry =
  fun
  [ Sself | Snext -> entry
  | Snterm e -> e
  | Snterml e _ -> e
  | _ -> raise Stream.Failure ]
;

value top_tree entry =
  fun
  [ Node {node = s; brother = bro; son = son} ->
      Node {node = top_symb entry s; brother = bro; son = son}
  | LocAct _ _ | DeadEnd -> raise Stream.Failure ]
;

value skip_if_empty bp p strm =
  if Stream.count strm == bp then Gramext.action (fun a -> p strm)
  else raise Stream.Failure
;

value continue entry bp a s son p1 =
  parser
    [: a = (entry_of_symb entry s).econtinue 0 bp a;
       act = p1 ? tree_failed entry a s son :] ->
      Gramext.action (fun _ -> app act a)
;

value do_recover parser_of_tree entry nlevn alevn bp a s son =
  parser
  [ [: a = parser_of_tree entry nlevn alevn (top_tree entry son) :] -> a
  | [: a = skip_if_empty bp (parser []) :] -> a
  | [: a =
         continue entry bp a s son
           (parser_of_tree entry nlevn alevn son) :] ->
      a ]
;

value strict_parsing = ref False;

value recover parser_of_tree entry nlevn alevn bp a s son strm =
  if strict_parsing.val then raise (Stream.Error (tree_failed entry a s son))
  else do_recover parser_of_tree entry nlevn alevn bp a s son strm
;

value token_count = ref 0;

value peek_nth n strm = do {
  let list = Stream.npeek n strm in
  token_count.val := Stream.count strm + n;
  let rec loop list n =
    match (list, n) with
    [ ([x :: _], 1) -> Some x
    | ([_ :: l], n) -> loop l (n - 1)
    | ([], _) -> None ]
  in
  loop list n
};

value item_skipped = ref False;
value skip_item a = do { item_skipped.val := True; a };

value call_and_push ps al strm = do {
  item_skipped.val := False;
  let a = ps strm in
  let al = if item_skipped.val then al else [a :: al] in
  item_skipped.val := False;
  al
};

value fcall_and_push ps al err strm = do {
  item_skipped.val := False;
  match ps err strm with
  [ Some (a, strm) -> do {
      let al = if item_skipped.val then al else [a :: al] in
      item_skipped.val := False;
      Some (al, strm)
    }
  | None -> None ]
};

value bcall_and_push ps al err strm = do {
  item_skipped.val := False;
  match ps err strm with
  [ Some (a, strm, Fstream.K kont) -> do {
      let rec kont2 kont () = do {
        item_skipped.val := False;
        match kont () with
        [ Some (a, strm, Fstream.K kont) -> do {
            let al = if item_skipped.val then al else [a :: al] in
            item_skipped.val := False;
            Some (al, strm, Fstream.K (kont2 kont))
          }
        | None -> None ]
      }
      in
      let al = if item_skipped.val then al else [a :: al] in
      item_skipped.val := False;
      Some (al, strm, Fstream.K (kont2 kont))
    }
  | None -> None ]
};

value token_ematch gram (tok, vala) =
  let tematch = gram.glexer.Plexing.tok_match tok in
  match vala with
  | Some al ->
      let pa =
        match al with
        [ [] ->
            let t = "V " ^ fst tok in
            gram.glexer.Plexing.tok_match (t, "")
        | al ->
            loop al where rec loop =
              fun
              [ [a :: al] ->
                  let pa = gram.glexer.Plexing.tok_match ("V", a) in
                  let pal = loop al in
                  fun tok ->
                    try pa tok with [ Stream.Failure -> pal tok ]
              | [] -> fun tok -> raise Stream.Failure ] ]
      in
      fun tok ->
        try Obj.repr (Ploc.VaAnt (Obj.magic (pa tok : string))) with
        [ Stream.Failure -> Obj.repr (Ploc.VaVal (tematch tok)) ]
  | None ->
      fun tok -> Obj.repr (tematch tok : string)
  end
;

value rec parser_of_tree entry nlevn alevn =
  fun
  [ DeadEnd -> parser []
  | LocAct act _ -> parser [: :] -> act
  | Node {node = Sself; son = LocAct act _; brother = DeadEnd} ->
      parser [: a = entry.estart alevn :] -> app act a
  | Node {node = Scut; son = son; brother = _} ->
      parser_of_tree entry nlevn alevn son
  | Node {node = Sself; son = LocAct act _; brother = bro} ->
      let p2 = parser_of_tree entry nlevn alevn bro in
      parser
      [ [: a = entry.estart alevn :] -> app act a
      | [: a = p2 :] -> a ]
  | Node {node = s; son = son; brother = DeadEnd} ->
      let tokl =
        match s with
        [ Stoken tok -> get_token_list entry [] (tok, None) son
        | Svala ls (Stoken tok) -> get_token_list entry [] (tok, Some ls) son
        | _ -> None ]
      in
      match tokl with
      [ None ->
          let ps = parser_of_symbol entry nlevn s in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn s son in
          parser bp
            [: a = ps;
               act = p1 bp a ? tree_failed entry a s son :] -> app act a
      | Some (rev_tokl, (last_tok, svala), son) ->
          let lt =
            let t = Stoken last_tok in
            match svala with
            [ Some l -> Svala l t
            | None -> t ]
          in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn lt son in
          parser_of_token_list entry s son p1 (parser []) rev_tokl
            (last_tok, svala) ]
  | Node {node = s; son = son; brother = bro} ->
      let tokl =
        match s with
        [ Stoken tok -> get_token_list entry [] (tok, None) son
        | Svala ls (Stoken tok) -> get_token_list entry [] (tok, Some ls) son
        | _ -> None ]
      in
      match tokl with
      [ None ->
          let ps = parser_of_symbol entry nlevn s in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn s son in
          let p2 = parser_of_tree entry nlevn alevn bro in
          fun (strm : Stream.t _) ->
            let bp = Stream.count strm in
            match try Some (ps strm) with [ Stream.Failure -> None ] with
            | Some a ->
                match
                  try Some (p1 bp a strm) with [ Stream.Failure -> None ]
                with
                | Some act -> app act a
                | None -> raise (Stream.Error (tree_failed entry a s son))
                end
            | None -> p2 strm
            end
      | Some (rev_tokl, (last_tok, vala), son) ->
          let lt =
            let t = Stoken last_tok in
            match vala with
            [ Some ls -> Svala ls t
            | None -> t ]
          in
          let p2 = parser_of_tree entry nlevn alevn bro in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn lt son in
          let p1 =
            parser_of_token_list entry lt son p1 p2 rev_tokl
              (last_tok, vala)
          in
          parser
          [ [: a = p1 :] -> a
          | [: a = p2 :] -> a ] ] ]
and parser_cont p1 entry nlevn alevn s son bp a =
  parser
  [ [: a = p1 :] -> a
  | [: a = recover parser_of_tree entry nlevn alevn bp a s son :] -> a ]
and parser_of_token_list entry s son p1 p2 rev_tokl last_tok =
  let plast =
    let n = List.length rev_tokl + 1 in
    let tematch = token_ematch entry.egram last_tok in
    let ps strm =
      match peek_nth n strm with
      [ Some tok -> do {
          let r = tematch tok in
          for i = 1 to n do { Stream.junk strm };
          Obj.repr r
        }
      | None -> raise Stream.Failure ]
    in
    fun (strm : Stream.t _) ->
      let bp = Stream.count strm in
      let a = ps strm in
      match try Some (p1 bp a strm) with [ Stream.Failure -> None ] with
      | Some act -> app act a
      | None -> raise (Stream.Error (tree_failed entry a s son))
      end
  in
  match List.rev rev_tokl with
  | [] -> parser [: a = plast :] -> a
  | [tok :: tokl] ->
      let tematch = token_ematch entry.egram tok in
      let ps strm =
        match peek_nth 1 strm with
        [ Some tok -> tematch tok
        | None -> raise Stream.Failure ]
      in
      let p1 =
        loop 2 tokl where rec loop n =
          fun
          | [] -> plast
          | [tok :: tokl] ->
              let tematch = token_ematch entry.egram tok in
              let ps strm =
                match peek_nth n strm with
                | Some tok -> tematch tok
                | None -> raise Stream.Failure
                end
              in
              let p1 = loop (n + 1) tokl in
              parser [: a = ps; act = p1 ! :] -> app act a
          end
      in
      parser [: a = ps; act = p1 ! :] -> app act a
  end
and parser_of_symbol entry nlevn =
  fun
  [ Sfacto s -> parser_of_symbol entry nlevn s
  | Smeta _ symbl act ->
      let act = Obj.magic act entry symbl in
      Obj.magic
        (List.fold_left
           (fun act symb -> Obj.magic act (parser_of_symbol entry nlevn symb))
           act symbl)
  | Slist0 s ->
      let ps = call_and_push (parser_of_symbol entry nlevn s) in
      let rec loop al =
        parser
        [ [: al = ps al; a = loop al ! :] -> a
        | [: :] -> al ]
      in
      parser [: a = loop [] :] -> Obj.repr (List.rev a)
  | Slist0sep symb sep False ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al =
        parser
        [ [: v = pt; al = ps al ? symb_failed entry v sep symb;
             a = kont al ! :] ->
            a
        | [: :] -> al ]
      in
      parser
      [ [: al = ps []; a = kont al ! :] -> Obj.repr (List.rev a)
      | [: :] -> Obj.repr [] ]
  | Slist0sep symb sep True ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al =
        parser
        [ [: v = pt; al = ps al; a = kont al ! :] -> a
        | [: v = pt :] -> al
        | [: :] -> al ]
      in
      parser
      [ [: al = ps []; a = kont al ! :] -> Obj.repr (List.rev a)
      | [: :] -> Obj.repr [] ]
  | Slist1 s ->
      let ps = call_and_push (parser_of_symbol entry nlevn s) in
      let rec loop al =
        parser
        [ [: al = ps al; a = loop al ! :] -> a
        | [: :] -> al ]
      in
      parser [: al = ps []; a = loop al ! :] -> Obj.repr (List.rev a)
  | Slist1sep symb sep False ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al =
        parser
        [ [: v = pt;
             al =
               parser
               [ [: a = ps al :] -> a
               | [: a = parse_top_symb entry symb :] -> [a :: al]
               | [: :] ->
                   raise (Stream.Error (symb_failed entry v sep symb)) ] !;
             a = kont al ! :] ->
            a
        | [: :] -> al ]
      in
      parser [: al = ps []; a = kont al ! :] -> Obj.repr (List.rev a)
  | Slist1sep symb sep True ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al =
        parser
        [ [: v = pt; al = ps al; al = kont al ! :] -> al
        | [: v = pt; a = parse_top_symb entry symb;
             al = kont [a :: al] ! :] -> al
        | [: v = pt :] -> al
        | [: :] -> al ]
      in
      parser [: al = ps []; a = kont al ! :] -> Obj.repr (List.rev a)
  | Sopt s ->
      let ps = parser_of_symbol entry nlevn s in
      parser
      [ [: a = ps :] -> Obj.repr (Some a)
      | [: :] -> Obj.repr None ]
  | Sflag s ->
      let ps = parser_of_symbol entry nlevn s in
      parser
      [ [: _ = ps :] -> Obj.repr True
      | [: :] -> Obj.repr False ]
  | Stree t ->
      let pt = parser_of_tree entry 1 0 t in
      parser bp
        [: a = pt :] ep ->
          let loc = loc_of_token_interval bp ep in
          app a loc
  | Svala al s ->
      let pa =
        match al with
        [ [] ->
            let t =
              match s with
              [ Sflag _ -> Some "V FLAG"
              | Sopt _ -> Some "V OPT"
              | Slist0 _ | Slist0sep _ _ _ -> Some "V LIST"
              | Slist1 _ | Slist1sep _ _ _ -> Some "V LIST"
              | Stoken (con, "") -> Some ("V " ^ con)
              | _ -> None ]
            in
            match t with
            [ Some t -> parser_of_token entry (t, "")
            | None -> parser [] ]
        | al ->
            loop al where rec loop =
              fun
              [ [a :: al] ->
                  let pa = parser_of_token entry ("V", a) in
                  let pal = loop al in
                  parser
                  [ [: a = pa :] -> a
                  | [: a = pal :] -> a ]
              | [] -> parser [] ] ]
      in
      let ps = parser_of_symbol entry nlevn s in
      parser
      [ [: a = pa :] -> Obj.repr (Ploc.VaAnt (Obj.magic a : string))
      | [: a = ps :] -> Obj.repr (Ploc.VaVal a) ]
  | Snterm e -> parser [: a = e.estart 0 :] -> a
  | Snterml e l -> parser [: a = e.estart (level_number e l) :] -> a
  | Sself -> parser [: a = entry.estart 0 :] -> a
  | Snext -> parser [: a = entry.estart nlevn :] -> a
  | Scut -> parser [: :] -> Obj.repr ()
  | Stoken tok -> parser_of_token entry tok ]
and parser_of_token entry tok =
  let f = entry.egram.glexer.Plexing.tok_match tok in
  fun strm ->
    match Stream.peek strm with
    [ Some tok -> do {
        let r = f tok in
        Stream.junk strm;
        Obj.repr r
      }
    | None -> raise Stream.Failure ]
and parse_top_symb entry symb =
  parser_of_symbol entry 0 (top_symb entry symb)
;

value symb_failed_txt e s1 s2 = symb_failed e 0 s1 s2;

value rec start_parser_of_levels entry clevn =
  fun
  [ [] -> fun levn -> parser []
  | [lev :: levs] ->
      let p1 = start_parser_of_levels entry (succ clevn) levs in
      match lev.lprefix with
      [ DeadEnd -> p1
      | tree ->
          let alevn =
            match lev.assoc with
            [ LeftA | NonA -> succ clevn
            | RightA -> clevn ]
          in
          let p2 = parser_of_tree entry (succ clevn) alevn tree in
          match levs with
          [ [] ->
              fun levn strm ->
                (* this code should be there but is commented to preserve
                   compatibility with previous versions... with this code,
                   the grammar entry e: [[ "x"; a = e | "y" ]] should fail
                   because it should be: e: [RIGHTA[ "x"; a = e | "y" ]]...
                if levn > clevn then match strm with parser []
                else
                *)
                match strm with parser bp
                  [: act = p2 :] ep ->
                    let a = app act (loc_of_token_interval bp ep) in
                    entry.econtinue levn bp a strm
          | _ ->
              fun levn strm ->
                if levn > clevn then p1 levn strm
                else
                  match strm with parser bp
                  [ [: act = p2 :] ep ->
                      let a = app act (loc_of_token_interval bp ep) in
                      entry.econtinue levn bp a strm
                  | [: a = p1 levn :] -> a ] ] ] ]
;

value rec continue_parser_of_levels entry clevn =
  fun
  [ [] -> fun levn bp a -> parser []
  | [lev :: levs] ->
      let p1 = continue_parser_of_levels entry (succ clevn) levs in
      match lev.lsuffix with
      [ DeadEnd -> p1
      | tree ->
          let alevn =
            match lev.assoc with
            [ LeftA | NonA -> succ clevn
            | RightA -> clevn ]
          in
          let p2 = parser_of_tree entry (succ clevn) alevn tree in
          fun levn bp a strm ->
            if levn > clevn then p1 levn bp a strm
            else
              match strm with parser
              [ [: a = p1 levn bp a :] -> a
              | [: act = p2 :] ep ->
                  let a = app act a (loc_of_token_interval bp ep) in
                  entry.econtinue levn bp a strm ] ] ]
;

value continue_parser_of_entry entry =
  match entry.edesc with
  [ Dlevels elev ->
      let p = continue_parser_of_levels entry 0 elev in
      fun levn bp a ->
        parser
        [ [: a = p levn bp a :] -> a
        | [: :] -> a ]
  | Dparser p -> fun levn bp a -> parser [] ]
;

value empty_entry ename levn strm =
  raise (Stream.Error ("entry [" ^ ename ^ "] is empty"))
;

value start_parser_of_entry entry =
  match entry.edesc with
  [ Dlevels [] -> empty_entry entry.ename
  | Dlevels elev -> start_parser_of_levels entry 0 elev
  | Dparser p -> fun levn strm -> p strm ]
;

value default_algorithm_var = ref DefaultAlgorithm;
value set_default_algorithm algo = default_algorithm_var.val := algo;
value default_algorithm () = default_algorithm_var.val;

(* deprecated since 2017-06-06: use 'set_default_algorithm' instead *)
value backtrack_parse = ref False;
value warned_using_backtrack_parse = ref False;
value compatible_deprecated_backtrack_parse () =
  if backtrack_parse.val then do {
    if not warned_using_backtrack_parse.val then do {
      eprintf "<W> use of Grammar.backtrace_parse ";
      eprintf "deprecated since 2017-06-06\n%!";
      warned_using_backtrack_parse.val := True
    }
    else ();
    backtrack_parse.val := False;
    set_default_algorithm Backtracking
  }
  else ()
;

(* parsing with functional streams *)

value backtrack_trace = ref False;
value backtrack_stalling_limit = ref 10000;
value backtrack_trace_try = ref False;
value tind = ref "";
value max_fcount = ref None;
value nb_ftry = ref 0;

value no_err () = "";
value ftree_failed entry prev_symb_result prev_symb tree () =
  tree_failed entry prev_symb_result prev_symb tree
;
value fsymb_failed entry prev_symb_result prev_symb symb () =
  symb_failed entry prev_symb_result prev_symb symb
;

value bfparser_of_token entry tok return_value =
  let f = entry.egram.glexer.Plexing.tok_match tok in
  fun err strm ->
    let _ =
      if backtrack_trace.val then do {
        Printf.eprintf "%stesting (\"%s\", \"%s\") ..." tind.val (fst tok)
          (snd tok);
        flush stderr;
      }
      else ()
    in
    let _ =
      if backtrack_stalling_limit.val > 0 || backtrack_trace_try.val then
        let m =
          match max_fcount.val with
          | Some (m, _, _) -> m
          | None -> 0
          end
        in
        if Fstream.count strm > m then do {
          if backtrack_trace.val then
            Printf.eprintf " (token count max %d)%!" (Fstream.count strm)
          else ();
          let e : g_entry Obj.t = Obj.magic (entry : g_entry _) in
          let cnt = Fstream.count strm in
          max_fcount.val := Some (cnt, e, err);
          nb_ftry.val := 0
        }
        else do {
          if backtrack_trace.val then
            Printf.eprintf " (token count %d/%d)%!" (Fstream.count strm) m
          else ();
          incr nb_ftry;
          if backtrack_trace_try.val then do {
            Printf.eprintf "\ntokens read: %d; tokens tests: %d" m
              nb_ftry.val;
            flush stderr;
          }
          else ();
          if backtrack_stalling_limit.val > 0 &&
             nb_ftry.val >= backtrack_stalling_limit.val
          then do {
            if backtrack_trace.val || backtrack_trace_try.val then
              Printf.eprintf " (stalling limit reached)\n%!"
            else ();
            raise Stream.Failure
          }
          else ()
        }
      else ()
    in
    match Fstream.next strm with
    [ Some (tok, strm) ->
        try do {
          let r = f tok in
          let _ =
            if backtrack_trace.val then Printf.eprintf " yes \"%s\"\n%!" r
            else ()
          in
          nb_ftry.val := 0;
          return_value r strm
        }
        with
        [ Stream.Failure ->
            let _ =
              if backtrack_trace.val then Printf.eprintf " not found\n%!"
              else ()
            in
            None ]
    | None ->
        let _ =
          if backtrack_trace.val then do {
            Printf.eprintf " eos\n";
            flush stderr;
          }
          else ()
        in
        None ]
;

let s = try Sys.getenv "CAMLP5PARAM" with [ Not_found -> "" ] in
loop 0 where rec loop i =
  if i = String.length s then ()
  else if s.[i] = 'b' then do {
    set_default_algorithm Backtracking;
    loop (i + 1)
  }
  else if s.[i] = 'f' then do {
    set_default_algorithm Functional;
    loop (i + 1)
  }
  else if s.[i] = 'p' then do {
    set_default_algorithm Predictive;
    loop (i + 1)
  }
  else if s.[i] = 'l' && i + 1 < String.length s && s.[i+1] = '=' then do {
    let (n, i) =
      loop 0 (i + 2) where rec loop n i =
        if i = String.length s then (n, i)
        else if s.[i] >= '0' && s.[i] <= '9' then
          loop (10 * n + Char.code s.[i] - Char.code '0') (i + 1)
        else (n, i)
    in
    backtrack_stalling_limit.val := n;
    loop i
  }
  else if s.[i] = 't' then do {
    backtrack_trace.val := True;
    loop (i + 1)
  }
  else if s.[i] = 'y' then do {
    backtrack_trace_try.val := True;
    loop (i + 1)
  }
  else
    loop (i + 1)
;

(* version with functional streams and limited backtracking *)

value fcount = fparser bp [: :] → bp;

value rec ftop_symb entry =
  fun
  [ Sself | Snext -> Some (Snterm entry)
  | Snterml e _ -> Some (Snterm e)
  | Slist1sep s sep b ->
      match ftop_symb entry s with
      [ Some s -> Some (Slist1sep s sep b)
      | None -> None ]
  | _ -> None ]
;

value ftop_tree entry son strm =
  match son with
  [ Node {node = s; brother = bro; son = son} ->
      match ftop_symb entry s with
      [ Some sy ->
          let r = Node {node = sy; brother = bro; son = son} in
          let _ =
            if backtrack_trace.val then
              Printf.eprintf "%srecovering pos %d\n%!" tind.val
                (Fstream.count strm)
            else ()
          in
          match strm with fparser [: :] -> r
      | None ->
          None ]
  | LocAct _ _ | DeadEnd ->
      None ]
;

value frecover fparser_of_tree entry next_levn assoc_levn son err =
  fparser
  [ [: t = ftop_tree entry son;
       a = fparser_of_tree entry next_levn assoc_levn t err :] -> a ]
;

value fparser_of_token entry tok =
  let return_value r strm = match strm with fparser [: :] -> Obj.repr r in
  bfparser_of_token entry tok return_value
;

value rec fparser_of_tree entry next_levn assoc_levn =
  fun
  [ DeadEnd -> fun err -> fparser []
  | LocAct act _ -> fun err -> fparser [: :] -> act
  | Node {node = Sself; son = LocAct act _; brother = DeadEnd} ->
      fun err -> fparser [: a = entry.fstart assoc_levn err :] -> app act a
  | Node {node = Sself; son = LocAct act _; brother = bro} ->
      let p2 = fparser_of_tree entry next_levn assoc_levn bro in
      fun err ->
        fparser
        [ [: a = entry.fstart assoc_levn err :] -> app act a
        | [: a = p2 err :] -> a ]
  | Node {node = Scut; son = son; brother = _} ->
      let p1 = fparser_of_tree entry next_levn assoc_levn son in
      fun err ->
        fparser
        [ [: !; a = p1 err :] -> a ]
  | Node {node = s; son = son; brother = DeadEnd} ->
      let ps = fparser_of_symbol entry next_levn s in
      let p1 = fparser_of_tree entry next_levn assoc_levn son in
      let p1 = fparser_cont p1 entry next_levn assoc_levn son in
      fun err ->
        fparser [: a = ps err; act = p1 (ftree_failed entry a s son) :] ->
          app act a
  | Node {node = s; son = son; brother = bro} ->
      let ps = fparser_of_symbol entry next_levn s in
      let p1 = fparser_of_tree entry next_levn assoc_levn son in
      let p1 = fparser_cont p1 entry next_levn assoc_levn son in
      let p2 = fparser_of_tree entry next_levn assoc_levn bro in
      fun err ->
        fparser
        [ [: a = ps err; act = p1 (ftree_failed entry a s son) :] -> app act a
        | [: a = p2 err :] -> a ] ]
and fparser_cont p1 entry next_levn assoc_levn son err =
  fparser
  [ [: a = p1 err :] -> a
  | [: a = frecover fparser_of_tree entry next_levn assoc_levn son err :] ->
         a ]
and fparser_of_symbol entry next_levn =
  fun
  [ Sfacto s -> fparser_of_symbol entry next_levn s
  | Smeta _ symbl act ->
      let _ = failwith "Smeta for fparser not impl" in
      let act = Obj.magic act entry symbl in
      Obj.magic
        (List.fold_left
           (fun act symb ->
              Obj.magic act (fparser_of_symbol entry next_levn symb))
           act symbl)
  | Slist0 s ->
      let ps = fparser_of_symbol entry next_levn s in
      let ps = fcall_and_push ps in
      let rec loop al err =
        fparser
        [ [: al = ps al err; a = loop al err :] -> a
        | [: :] -> al ]
      in
      fun err -> fparser [: a = loop [] err :] -> Obj.repr (List.rev a)
  | Slist0sep symb sep False ->
      let ps = fparser_of_symbol entry next_levn symb in
      let ps = fcall_and_push ps in
      let pt = fparser_of_symbol entry next_levn sep in
      let rec kont al err =
        fparser
        [ [: v = pt err; al = ps al (fsymb_failed entry v sep symb);
             a = kont al err :] -> a
        | [: :] -> al ]
      in
      fun err ->
        fparser
        [ [: al = ps [] err; a = kont al err :] -> Obj.repr (List.rev a)
        | [: :] -> Obj.repr [] ]
  | Slist1 s ->
      let ps = fparser_of_symbol entry next_levn s in
      let ps = fcall_and_push ps in
      let rec loop al err =
        fparser
        [ [: al = ps al err; a = loop al err :] -> a
        | [: :] -> al ]
      in
      fun err ->
        fparser [: al = ps [] err; a = loop al err :] -> Obj.repr (List.rev a)
  | Slist0sep symb sep True ->
      failwith "LIST0 _ SEP _ OPT_SEP not implemented; please report"
  | Slist1sep symb sep False ->
      let ps = fparser_of_symbol entry next_levn symb in
      let ps = fcall_and_push ps in
      let pt = fparser_of_symbol entry next_levn sep in
      let pts = fparse_top_symb entry symb in
      let rec kont al err =
        fparser
        [ [: v = pt err;
             al =
               fparser
               [ [: a = ps al (fsymb_failed entry v sep symb) :] -> a
               | [: a = pts (fsymb_failed entry v sep symb) :] -> [a :: al] ];
             a = kont al err :] ->
            a
        | [: :] -> al ]
      in
      fun err ->
        fparser [: al = ps [] err; a = kont al err :] -> Obj.repr (List.rev a)
  | Slist1sep symb sep True ->
      let ps = fparser_of_symbol entry next_levn symb in
      let ps = fcall_and_push ps in
      let pt = fparser_of_symbol entry next_levn sep in
      let pts = fparse_top_symb entry symb in
      let rec kont al err =
        fparser
        [ [: v = pt err; al = ps al err; al = kont al err :] -> al
        | [: v = pt err; a = pts err; al = kont [a :: al] err :] -> al
        | [: v = pt err :] -> al
        | [: :] -> al ]
      in
      fun err ->
        fparser [: al = ps [] err; a = kont al err :] -> Obj.repr (List.rev a)
  | Sopt s ->
      let ps = fparser_of_symbol entry next_levn s in
      fun err ->
        fparser
        [ [: a = ps err :] -> Obj.repr (Some a)
        | [: :] -> Obj.repr None ]
  | Sflag s ->
      let ps = fparser_of_symbol entry next_levn s in
      fun err ->
        fparser
        [ [: _ = ps err :] -> Obj.repr True
        | [: :] -> Obj.repr False ]
  | Stree t ->
      let pt = fparser_of_tree entry 1 0 t in
      fun err ->
        fparser bp
          [: a = pt err :] ep ->
            let loc = loc_of_token_interval bp ep in
            app a loc
  | Svala al s ->
      let pa =
        match al with
        [ [] ->
            let t =
              match s with
              [ Sflag _ -> Some "V FLAG"
              | Sopt _ -> Some "V OPT"
              | Slist0 _ | Slist0sep _ _ _ -> Some "V LIST"
              | Slist1 _ | Slist1sep _ _ _ -> Some "V LIST"
              | Stoken (con, "") -> Some ("V " ^ con)
              | _ -> None ]
            in
            match t with
            [ Some t -> fparser_of_token entry (t, "")
            | None -> fun err -> fparser [] ]
        | al ->
            loop al where rec loop =
              fun
              [ [a :: al] ->
                  let pa = fparser_of_token entry ("V", a) in
                  let pal = loop al in
                  fun err ->
                    fparser
                    [ [: a = pa err :] -> a
                    | [: a = pal err :] -> a ]
              | [] -> fun err -> fparser [] ] ]
      in
      let ps = fparser_of_symbol entry next_levn s in
      fun err ->
        fparser
        [ [: a = pa err :] -> Obj.repr (Ploc.VaAnt (Obj.magic a : string))
        | [: a = ps err :] -> Obj.repr (Ploc.VaVal a) ]
  | Snterm e ->
      fun err -> fparser [: a = e.fstart 0 err :] -> a
  | Snterml e l ->
      fun err -> fparser [: a = e.fstart (level_number e l) err :] -> a
  | Sself -> fun err -> fparser [: a = entry.fstart 0 err :] -> a
  | Snext -> fun err -> fparser [: a = entry.fstart next_levn err :] -> a
  | Scut -> fun err -> fparser [: ! :] -> Obj.repr ()
  | Stoken tok -> fparser_of_token entry tok ]
and fparse_top_symb entry symb =
  match ftop_symb entry symb with
  [ Some sy -> fparser_of_symbol entry 0 sy
  | None -> fun err -> fparser [] ]
;

value rec fstart_parser_of_levels entry clevn =
  fun
  [ [] -> fun levn err -> fparser []
  | [lev :: levs] ->
      let p1 = fstart_parser_of_levels entry (succ clevn) levs in
      match lev.lprefix with
      [ DeadEnd -> p1
      | tree ->
          let alevn =
            match lev.assoc with
            [ LeftA | NonA -> succ clevn
            | RightA -> clevn ]
          in
          let p2 = fparser_of_tree entry (succ clevn) alevn tree in
          match levs with
          [ [] ->
              fun levn err strm ->
                match strm with fparser bp
                  [: act = p2 err; ep = fcount;
                     a =
                       entry.fcontinue levn bp
                         (app act (loc_of_token_interval bp ep)) err :] ->
                    a
          | _ ->
              fun levn err strm ->
                if levn > clevn then p1 levn err strm
                else
                  match strm with fparser bp
                  [ [: act = p2 err; ep = fcount;
                       a =
                         entry.fcontinue levn bp
                           (app act (loc_of_token_interval bp ep)) err :] ->
                      a
                  | [: a = p1 levn err :] -> a ] ] ] ]
;

value rec fcontinue_parser_of_levels entry clevn =
  fun
  [ [] -> fun levn bp a err -> fparser []
  | [lev :: levs] ->
      let p1 = fcontinue_parser_of_levels entry (succ clevn) levs in
      match lev.lsuffix with
      [ DeadEnd -> p1
      | tree ->
          let alevn =
            match lev.assoc with
            [ LeftA | NonA -> succ clevn
            | RightA -> clevn ]
          in
          let p2 = fparser_of_tree entry (succ clevn) alevn tree in
          fun levn bp a err strm ->
            if levn > clevn then p1 levn bp a err strm
            else
              match strm with fparser
              [ [: a = p1 levn bp a err :] -> a
              | [: act = p2 err; ep = fcount;
                   a =
                     entry.fcontinue levn bp
                       (app act a (loc_of_token_interval bp ep)) err :] ->
                  a ] ] ]
;

value fstart_parser_of_entry entry =
  match entry.edesc with
  [ Dlevels [] -> fun _ err -> fparser []
  | Dlevels elev -> fstart_parser_of_levels entry 0 elev
  | Dparser p -> fun levn err strm -> failwith "Dparser for Fstream" ]
;

value fcontinue_parser_of_entry entry =
  match entry.edesc with
  [ Dlevels elev ->
      let p = fcontinue_parser_of_levels entry 0 elev in
      fun levn bp a err ->
        fparser
        [ [: a = p levn bp a err :] -> a
        | [: :] -> a ]
  | Dparser p -> fun levn bp a err -> fparser [] ]
;

(* version with functional streams and full backtracking *)

value rec btop_symb entry =
  fun
  [ Sself | Snext -> Some (Snterm entry)
  | Snterml e _ -> Some (Snterm e)
  | Slist1sep s sep b ->
      match btop_symb entry s with
      [ Some s -> Some (Slist1sep s sep b)
      | None -> None ]
  | _ -> None ]
;

value btop_tree entry son strm =
  match son with
  [ Node {node = s; brother = bro; son = son} ->
      match btop_symb entry s with
      [ Some sy ->
          let r = Node {node = sy; brother = bro; son = son} in
          let _ =
            if backtrack_trace.val then
              Printf.eprintf "%srecovering pos %d\n%!" tind.val
                (Fstream.count strm)
            else ()
          in
          match strm with bparser [: :] -> r
      | None ->
          None ]
  | LocAct _ _ | DeadEnd ->
      None ]
;

value brecover bparser_of_tree entry next_levn assoc_levn son err =
  bparser
  [ [: t = btop_tree entry son;
       a = bparser_of_tree entry next_levn assoc_levn t err :] -> a ]
;

value bparser_of_token entry tok =
  let return_value r strm = match strm with bparser [: :] -> Obj.repr r in
  bfparser_of_token entry tok return_value
;

value rec bparser_of_tree entry next_levn assoc_levn =
  fun
  [ DeadEnd -> fun err -> bparser []
  | LocAct act _ -> fun err -> bparser [: :] -> act
  | Node {node = Sself; son = LocAct act _; brother = DeadEnd} ->
      fun err -> bparser [: a = entry.bstart assoc_levn err :] -> app act a
  | Node {node = Sself; son = LocAct act _; brother = bro} ->
      let p2 = bparser_of_tree entry next_levn assoc_levn bro in
      fun err ->
        bparser
        [ [: a = entry.bstart assoc_levn err :] -> app act a
        | [: a = p2 err :] -> a ]
  | Node {node = Scut; son = son; brother = _} ->
      let p1 = bparser_of_tree entry next_levn assoc_levn son in
      fun err ->
        bparser
        [ [: !; a = p1 err :] -> a ]
  | Node {node = s; son = son; brother = DeadEnd} ->
      let ps = bparser_of_symbol entry next_levn s in
      let p1 = bparser_of_tree entry next_levn assoc_levn son in
      let p1 = bparser_cont p1 entry next_levn assoc_levn son in
      fun err ->
        bparser [: a = ps err; act = p1 (ftree_failed entry a s son) :] ->
          app act a
  | Node {node = s; son = son; brother = bro} ->
      let ps = bparser_of_symbol entry next_levn s in
      let p1 = bparser_of_tree entry next_levn assoc_levn son in
      let p1 = bparser_cont p1 entry next_levn assoc_levn son in
      let p2 = bparser_of_tree entry next_levn assoc_levn bro in
      fun err ->
        bparser
        [ [: a = ps err; act = p1 (ftree_failed entry a s son) :] -> app act a
        | [: a = p2 err :] -> a ] ]
and bparser_cont p1 entry next_levn assoc_levn son err =
  bparser
  [ [: a = p1 err :] -> a
  | [: a = brecover bparser_of_tree entry next_levn assoc_levn son err :] ->
         a ]
and bparser_of_symbol entry next_levn =
  fun
  [ Sfacto s -> bparser_of_symbol entry next_levn s
  | Smeta _ symbl act ->
      let _ = failwith "Smeta for bparser not impl" in
      let act = Obj.magic act entry symbl in
      Obj.magic
        (List.fold_left
           (fun act symb ->
              Obj.magic act (bparser_of_symbol entry next_levn symb))
           act symbl)
  | Slist0 s ->
      let ps = bparser_of_symbol entry next_levn s in
      let ps = bcall_and_push ps in
      let rec loop al err =
        bparser
        [ [: al = ps al err; a = loop al err :] -> a
        | [: :] -> al ]
      in
      fun err -> bparser [: a = loop [] err :] -> Obj.repr (List.rev a)
  | Slist0sep symb sep False ->
      let ps = bparser_of_symbol entry next_levn symb in
      let ps = bcall_and_push ps in
      let pt = bparser_of_symbol entry next_levn sep in
      let rec kont al err =
        bparser
        [ [: v = pt err; al = ps al (fsymb_failed entry v sep symb);
             a = kont al err :] -> a
        | [: :] -> al ]
      in
      fun err ->
        bparser
        [ [: al = ps [] err; a = kont al err :] -> Obj.repr (List.rev a)
        | [: :] -> Obj.repr [] ]
  | Slist1 s ->
      let ps = bparser_of_symbol entry next_levn s in
      let ps = bcall_and_push ps in
      let rec loop al err =
        bparser
        [ [: al = ps al err; a = loop al err :] -> a
        | [: :] -> al ]
      in
      fun err ->
        bparser [: al = ps [] err; a = loop al err :] -> Obj.repr (List.rev a)
  | Slist0sep symb sep True ->
      failwith "LIST0 _ SEP _ OPT_SEP not implemented; please report"
  | Slist1sep symb sep False ->
      let ps = bparser_of_symbol entry next_levn symb in
      let ps = bcall_and_push ps in
      let pt = bparser_of_symbol entry next_levn sep in
      let pts = bparse_top_symb entry symb in
      let rec kont al err =
        bparser
        [ [: v = pt err;
             al =
               bparser
               [ [: a = ps al (fsymb_failed entry v sep symb) :] -> a
               | [: a = pts (fsymb_failed entry v sep symb) :] -> [a :: al] ];
             a = kont al err :] ->
            a
        | [: :] -> al ]
      in
      fun err ->
        bparser [: al = ps [] err; a = kont al err :] -> Obj.repr (List.rev a)
  | Slist1sep symb sep True ->
      let ps = bparser_of_symbol entry next_levn symb in
      let ps = bcall_and_push ps in
      let pt = bparser_of_symbol entry next_levn sep in
      let pts = bparse_top_symb entry symb in
      let rec kont al err =
        bparser
        [ [: v = pt err; al = ps al err; al = kont al err :] -> al
        | [: v = pt err; a = pts err; al = kont [a :: al] err :] -> al
        | [: v = pt err :] -> al
        | [: :] -> al ]
      in
      fun err ->
        bparser [: al = ps [] err; a = kont al err :] -> Obj.repr (List.rev a)
  | Sopt s ->
      let ps = bparser_of_symbol entry next_levn s in
      fun err ->
        bparser
        [ [: a = ps err :] -> Obj.repr (Some a)
        | [: :] -> Obj.repr None ]
  | Sflag s ->
      let ps = bparser_of_symbol entry next_levn s in
      fun err ->
        bparser
        [ [: _ = ps err :] -> Obj.repr True
        | [: :] -> Obj.repr False ]
  | Stree t ->
      let pt = bparser_of_tree entry 1 0 t in
      fun err ->
        bparser bp
          [: a = pt err :] ep ->
            let loc = loc_of_token_interval bp ep in
            app a loc
  | Svala al s ->
      let pa =
        match al with
        [ [] ->
            let t =
              match s with
              [ Sflag _ -> Some "V FLAG"
              | Sopt _ -> Some "V OPT"
              | Slist0 _ | Slist0sep _ _ _ -> Some "V LIST"
              | Slist1 _ | Slist1sep _ _ _ -> Some "V LIST"
              | Stoken (con, "") -> Some ("V " ^ con)
              | _ -> None ]
            in
            match t with
            [ Some t -> bparser_of_token entry (t, "")
            | None -> fun err -> bparser [] ]
        | al ->
            loop al where rec loop =
              fun
              [ [a :: al] ->
                  let pa = bparser_of_token entry ("V", a) in
                  let pal = loop al in
                  fun err ->
                    bparser
                    [ [: a = pa err :] -> a
                    | [: a = pal err :] -> a ]
              | [] -> fun err -> bparser [] ] ]
      in
      let ps = bparser_of_symbol entry next_levn s in
      fun err ->
        bparser
        [ [: a = pa err :] -> Obj.repr (Ploc.VaAnt (Obj.magic a : string))
        | [: a = ps err :] -> Obj.repr (Ploc.VaVal a) ]
  | Snterm e ->
      fun err -> bparser [: a = e.bstart 0 err :] -> a
  | Snterml e l ->
      fun err -> bparser [: a = e.bstart (level_number e l) err :] -> a
  | Sself -> fun err -> bparser [: a = entry.bstart 0 err :] -> a
  | Snext -> fun err -> bparser [: a = entry.bstart next_levn err :] -> a
  | Scut -> fun err -> bparser [: ! :] -> Obj.repr ()
  | Stoken tok -> bparser_of_token entry tok ]
and bparse_top_symb entry symb =
  match btop_symb entry symb with
  [ Some sy -> bparser_of_symbol entry 0 sy
  | None -> fun err -> bparser [] ]
;

value bcount strm = match strm with bparser [: :] -> Fstream.count strm;

value rec bstart_parser_of_levels entry clevn =
  fun
  [ [] -> fun levn err -> bparser []
  | [lev :: levs] ->
      let p1 = bstart_parser_of_levels entry (succ clevn) levs in
      match lev.lprefix with
      [ DeadEnd -> p1
      | tree ->
          let alevn =
            match lev.assoc with
            [ LeftA | NonA -> succ clevn
            | RightA -> clevn ]
          in
          let p2 = bparser_of_tree entry (succ clevn) alevn tree in
          match levs with
          [ [] ->
              fun levn err strm ->
                match strm with bparser bp
                  [: act = p2 err; ep = bcount;
                     a =
                       entry.bcontinue levn bp
                         (app act (loc_of_token_interval bp ep)) err :] ->
                    a
          | _ ->
              fun levn err strm ->
                if levn > clevn then p1 levn err strm
                else
                  match strm with bparser bp
                  [ [: act = p2 err; ep = bcount;
                       a =
                         entry.bcontinue levn bp
                           (app act (loc_of_token_interval bp ep)) err :] ->
                      a
                  | [: a = p1 levn err :] -> a ] ] ] ]
;

value rec bcontinue_parser_of_levels entry clevn =
  fun
  [ [] -> fun levn bp a err -> bparser []
  | [lev :: levs] ->
      let p1 = bcontinue_parser_of_levels entry (succ clevn) levs in
      match lev.lsuffix with
      [ DeadEnd -> p1
      | tree ->
          let alevn =
            match lev.assoc with
            [ LeftA | NonA -> succ clevn
            | RightA -> clevn ]
          in
          let p2 = bparser_of_tree entry (succ clevn) alevn tree in
          fun levn bp a err strm ->
            if levn > clevn then p1 levn bp a err strm
            else
              match strm with bparser
              [ [: a = p1 levn bp a err :] -> a
              | [: act = p2 err; ep = bcount;
                   a =
                     entry.bcontinue levn bp
                       (app act a (loc_of_token_interval bp ep)) err :] ->
                  a ] ] ]
;

value bstart_parser_of_entry entry =
  match entry.edesc with
  [ Dlevels [] -> fun _ err -> bparser []
  | Dlevels elev -> bstart_parser_of_levels entry 0 elev
  | Dparser p -> fun levn err strm -> failwith "Dparser for Fstream" ]
;

value bcontinue_parser_of_entry entry =
  match entry.edesc with
  [ Dlevels elev ->
      let p = bcontinue_parser_of_levels entry 0 elev in
      fun levn bp a err ->
        bparser
        [ [: a = p levn bp a err :] -> a
        | [: :] -> a ]
  | Dparser p -> fun levn bp a err -> bparser [] ]
;

(* Extend syntax *)

value trace_entry_lev_name entry lev =
  match entry.edesc with
  | Dlevels ll ->
      if lev < List.length ll then
        let glev = List.nth ll lev in
        match glev.lname with
        | Some "" | None -> ()
        | Some s -> Printf.eprintf " (\"%s\")" s
        end
      else ()
  | Dparser _ -> ()
  end
;

value may_trace_start entry f =
  if backtrack_trace.val then
    fun lev err strm -> do {
      let t = tind.val in
      Printf.eprintf "%s>> start %s lev %d" tind.val entry.ename lev;
      trace_entry_lev_name entry lev;
      Printf.eprintf "\n%!";
      tind.val := tind.val ^ " ";
      try do {
        let r = f lev err strm in
        tind.val := t;
        Printf.eprintf "%s<< end %s lev %d" tind.val entry.ename lev;
        trace_entry_lev_name entry lev;
        Printf.eprintf "\n%!";
        r
      }
      with e -> do {
        tind.val := t;
        Printf.eprintf "%sexception \"%s\"\n" tind.val
          (Printexc.to_string e);
        flush stderr;
        raise e
      }
    }
  else f
;

value may_trace_continue entry f =
  if backtrack_trace.val then
    fun lev bp a err strm -> do {
      let t = tind.val in
      Printf.eprintf "%s>> continue %s lev %d bp %d pos %d" tind.val
        entry.ename lev bp (Fstream.count strm);
      trace_entry_lev_name entry lev;
      Printf.eprintf "\n%!";
      tind.val := tind.val ^ " ";
      try do {
        let r = f lev bp a err strm in
        tind.val := t;
        Printf.eprintf "%s<< end continue %s lev %d %d" tind.val
          entry.ename lev bp;
        trace_entry_lev_name entry lev;
        Printf.eprintf "\n%!";
        r
      }
      with e -> do {
        tind.val := t;
        Printf.eprintf "%sexception \"%s\"" tind.val
          (Printexc.to_string e);
        trace_entry_lev_name entry lev;
        Printf.eprintf "\n%!";
        raise e
      }
    }
  else f
;

value init_entry_functions entry = do {
  entry.estart :=
    fun lev strm -> do {
      let f = start_parser_of_entry entry in
      entry.estart := f;
      f lev strm
    };
  entry.econtinue :=
    fun lev bp a strm -> do {
      let f = continue_parser_of_entry entry in
      entry.econtinue := f;
      f lev bp a strm
    };
  entry.fstart :=
    fun lev err strm -> do {
      let f = fstart_parser_of_entry entry in
      let f = may_trace_start entry f in
      entry.fstart := f;
      f lev err strm
    };
  entry.fcontinue :=
    fun lev bp a err strm -> do {
      let f = fcontinue_parser_of_entry entry in
      let f = may_trace_continue entry f in
      entry.fcontinue := f;
      f lev bp a err strm
    };
  entry.bstart :=
    fun lev err strm -> do {
      let f = bstart_parser_of_entry entry in
      let f = may_trace_start entry f in
      entry.bstart := f;
      f lev err strm
    };
  entry.bcontinue :=
    fun lev bp a err strm -> do {
      let f = bcontinue_parser_of_entry entry in
      let f = may_trace_continue entry f in
      entry.bcontinue := f;
      f lev bp a err strm
    }
};

value reinit_entry_functions entry =
  match entry.edesc with
  [ Dlevels elev -> init_entry_functions entry
  | _ -> () ]
;

value extend_entry entry position rules =
  try do {
    let elev = Gramext.levels_of_rules entry position rules in
    entry.edesc := Dlevels elev;
    init_entry_functions entry
  }
  with
  [ Plexing.Error s -> do {
      Printf.eprintf "Lexer initialization error:\n- %s\n" s;
      flush stderr;
      failwith "Grammar.extend"
    } ]
;

value extend entry_rules_list =
  let gram = ref None in
  List.iter
    (fun (entry, position, rules) -> do {
       match gram.val with
       [ Some g ->
           if g != entry.egram then do {
             Printf.eprintf "Error: entries with different grammars\n";
             flush stderr;
             failwith "Grammar.extend"
           }
           else ()
       | None -> gram.val := Some entry.egram ];
       extend_entry entry position rules
     })
    entry_rules_list
;

(* Deleting a rule *)

value delete_rule entry sl =
  match entry.edesc with
  [ Dlevels levs -> do {
      let levs = Gramext.delete_rule_in_level_list entry sl levs in
      entry.edesc := Dlevels levs;
      entry.estart :=
        fun lev strm -> do {
          let f = start_parser_of_entry entry in
          entry.estart := f;
          f lev strm
        };
      entry.econtinue :=
        fun lev bp a strm -> do {
          let f = continue_parser_of_entry entry in
          entry.econtinue := f;
          f lev bp a strm
        };
      entry.fstart :=
        fun lev err strm -> do {
          let f = fstart_parser_of_entry entry in
          entry.fstart := f;
          f lev err strm
        };
      entry.fcontinue :=
        fun lev bp a err strm -> do {
          let f = fcontinue_parser_of_entry entry in
          entry.fcontinue := f;
          f lev bp a err strm
        };
      entry.bstart :=
        fun lev err strm -> do {
          let f = bstart_parser_of_entry entry in
          entry.bstart := f;
          f lev err strm
        };
      entry.bcontinue :=
        fun lev bp a err strm -> do {
          let f = bcontinue_parser_of_entry entry in
          entry.bcontinue := f;
          f lev bp a err strm
        }
    }
  | Dparser _ -> () ]
;

value safe_delete_rule = delete_rule;

type parse_algorithm = Gramext.parse_algorithm ==
  [ Predictive | Functional | Backtracking | DefaultAlgorithm ]
;

value warning_verbose = Gramext.warning_verbose;

(* Normal interface *)

type token = (string * string);
type g = Gramext.grammar token;

type ty_symbol 'self 'a = Gramext.g_symbol token;
type ty_rule 'self 'f 'r = list (ty_symbol 'self Obj.t);
type ty_production 'a = (ty_rule 'a Obj.t Obj.t * Gramext.g_action);
type ty_extension =
  (Gramext.g_entry token * option Gramext.position * list (option string * option Gramext.g_assoc * list (ty_production Obj.t)));

value s_facto s = Sfacto s;
value s_nterm e = Snterm e;
value s_nterml e l = Snterml e l;
value s_list0 s = Slist0 s;
value s_list0sep s sep b = Slist0sep s sep b;
value s_list1 s = Slist1 s;
value s_list1sep s sep b = Slist1sep s sep b;
value s_opt s = Sopt s;
value s_flag s = Sflag s;
value s_self = Sself;
value s_next = Snext;
value s_token tok = Stoken tok;
value s_rules (t : list (ty_production Obj.t)) = Gramext.srules (Obj.magic t);
value s_vala sl s = Svala sl s;

value r_stop = [];
value r_next r s = r @ [s];
value r_cut r = r @ [Scut];

value production (p : (ty_rule 'a 'f (Ploc.t -> 'a) * 'f)) = (Obj.magic p : ty_production 'a);
value extension e pos (r : list (option string * option Gramext.g_assoc * list (ty_production Obj.t))) = ((e, pos, Obj.magic r) : ty_extension);

value safe_extend (l : list ty_extension) = extend (Obj.magic l);

value create_toktab () = Hashtbl.create 301;
value gcreate glexer =
  {gtokens = create_toktab (); glexer = glexer; galgo = DefaultAlgorithm}
;

value set_algorithm g algo = g.galgo := algo;

value tokens g con = do {
  let list = ref [] in
  Hashtbl.iter
    (fun (p_con, p_prm) c ->
       if p_con = con then list.val := [(p_prm, c.val) :: list.val] else ())
    g.gtokens;
  list.val
};

value glexer g = g.glexer;

type gen_parsable 'te =
  { pa_chr_strm : Stream.t char;
    pa_tok_strm : Stream.t 'te;
    pa_tok_fstrm : mutable Fstream.t 'te;
    pa_loc_func : Plexing.location_function }
;

type parsable = gen_parsable token;

value fstream_of_stream ts =
  Fstream.from
    (fun _ ->
       match Stream.peek ts with
       | None -> None
       | x -> do { Stream.junk ts; x }
       end)
;

value parsable g cs =
  let (ts, lf) = g.glexer.Plexing.tok_func cs in
  let fts = fstream_of_stream ts in
  {pa_chr_strm = cs; pa_tok_strm = ts; pa_tok_fstrm = fts; pa_loc_func = lf}
;

value parse_parsable entry p = do {
  let efun = entry.estart 0 in
  let ts = p.pa_tok_strm in
  let cs = p.pa_chr_strm in
  let fun_loc = p.pa_loc_func in
  let restore =
    let old_floc = floc.val in
    let old_tc = token_count.val in
    fun () -> do {
      floc.val := old_floc;
      token_count.val := old_tc;
    }
  in
  let get_loc () =
    try
      let cnt = Stream.count ts in
      let loc = fun_loc cnt in
      if token_count.val - 1 <= cnt then loc
      else Ploc.encl loc (fun_loc (token_count.val - 1))
    with
    [ Failure _ -> Ploc.make_unlined (Stream.count cs, Stream.count cs + 1) ]
  in
  floc.val := fun_loc;
  token_count.val := 0;
  try do {
    let r = efun ts in
    restore ();
    r
  }
  with
  [ Stream.Failure -> do {
      let loc = get_loc () in
      restore ();
      Ploc.raise loc (Stream.Error ("illegal begin of " ^ entry.ename))
    }
  | Stream.Error _ as exc -> do {
      let loc = get_loc () in
      restore ();
      Ploc.raise loc exc
    }
  | exc -> do {
      let loc = (Stream.count cs, Stream.count cs + 1) in
      restore ();
      Ploc.raise (Ploc.make_unlined loc) exc
    } ]
};

value bfparse entry efun restore2 p = do {
  let default_loc () =
    let cs = p.pa_chr_strm in
    Ploc.make_unlined (Stream.count cs, Stream.count cs + 1)
  in
  let restore =
    let old_tc = token_count.val in
    let old_nb_ftry = nb_ftry.val in
    fun () -> do {
      token_count.val := old_tc;
      nb_ftry.val := old_nb_ftry;
      restore2 ();
    }
  in
  let get_loc cnt =
    try
      let loc = p.pa_loc_func cnt in
      if token_count.val - 1 <= cnt then loc
      else Ploc.encl loc (p.pa_loc_func (token_count.val - 1))
    with
    [ Failure _ -> default_loc ()
    | e -> do { restore (); raise e } ]
  in
  token_count.val := 0;
  nb_ftry.val := 0;
  if backtrack_trace_try.val then do {
    Printf.eprintf "\n";
    flush stderr;
  }
  else ();
  let r =
    let fts = p.pa_tok_fstrm in
    try efun no_err fts with
    [ Stream.Failure | Fstream.Cut -> do {
        let cnt = Fstream.count fts + Fstream.count_unfrozen fts - 1 in
        let loc = get_loc cnt in
        let mess =
          match max_fcount.val with
          | Some (cnt, entry, err) ->
              let mess = err () in
              let mess =
                if mess = "" then sprintf "failure in [%s]" entry.ename
                else mess
              in
              if backtrack_trace.val then
                mess ^ Printf.sprintf " (max token count %d)" cnt
              else mess
          | None ->
              sprintf "[%s] failed" entry.ename
          end
        in
        let mess =
          if backtrack_trace.val then
            mess ^ Printf.sprintf " (cnt %d) (cnt+unfrozen %d)"
              token_count.val cnt
          else mess
        in
        restore ();
        Ploc.raise loc (Stream.Error mess)
      }
    | exc -> do {
        restore ();
        Ploc.raise (default_loc ()) exc
    } ]
  in
  restore (); r
};

value bfparse_token_stream entry efun ts = do {
  let restore2 () = () in
  if backtrack_trace.val then
    Printf.eprintf "%sbfparse_token_stream [%s]\n%!" tind.val entry.ename
  else ();
  let p =
    {pa_chr_strm = [: :];
     pa_tok_strm = ts;
     pa_tok_fstrm = fstream_of_stream ts;
     pa_loc_func = floc.val}
  in
  bfparse entry efun restore2 p
};

value bfparse_parsable entry p efun = do {
  let restore2 =
    let old_floc = floc.val in
    let old_max_fcount = max_fcount.val in
    fun () -> do {
      floc.val := old_floc;
      max_fcount.val := old_max_fcount;
    }
  in
  floc.val := p.pa_loc_func;
  max_fcount.val := None;
  if backtrack_trace.val then
    Printf.eprintf "%sbfparse_parsable [%s]\n%!" tind.val entry.ename
  else ();
  bfparse entry efun restore2 p
};

value fparse_token_stream entry ts =
  let efun err fts =
    match entry.fstart 0 err fts with
    | Some (a, _) -> Obj.magic a
    | None -> raise Stream.Failure
    end
  in
  bfparse_token_stream entry efun ts
;

value fparse_parsable entry p =
  let efun err fts =
    match entry.fstart 0 err fts with
    [ Some (r, strm) -> do { p.pa_tok_fstrm := strm; r }
    | None -> raise Stream.Failure ]
  in
  bfparse_parsable entry p efun
;

value bparse_token_stream entry ts =
  let efun err fts =
    match entry.bstart 0 err fts with
    | Some (a, _, _) -> Obj.magic a
    | None -> raise Stream.Failure
    end
  in
  bfparse_token_stream entry efun ts
;

value bparse_parsable entry p =
  let efun err fts =
    match entry.bstart 0 err fts with
    [ Some (r, strm, _) -> do { p.pa_tok_fstrm := strm; r }
    | None -> raise Stream.Failure ]
  in
  bfparse_parsable entry p efun
;

value bparse_parsable_all entry p = do {
  let efun = entry.bstart 0 in
  let fts = p.pa_tok_fstrm in
  let cs = p.pa_chr_strm in
  let fun_loc = p.pa_loc_func in
  let restore =
    let old_floc = floc.val in
    let old_tc = token_count.val in
    let old_max_fcount = max_fcount.val in
    let old_nb_ftry = nb_ftry.val in
    fun () -> do {
      floc.val := old_floc;
      token_count.val := old_tc;
      max_fcount.val := old_max_fcount;
      nb_ftry.val := old_nb_ftry;
    }
  in
  floc.val := fun_loc;
  token_count.val := 0;
  max_fcount.val := None;
  if backtrack_trace.val then
    Printf.eprintf "%sbparse_parsable_all [%s]: max token count reset\n%!"
      tind.val entry.ename
  else
  nb_ftry.val := 0;
  if backtrack_trace_try.val then do {
    Printf.eprintf "\n";
    flush stderr;
  }
  else ();
  try do {
    let rl =
      loop [] (efun no_err fts) where rec loop rev_rl =
        fun
        [ Some (r, strm, k) ->
            let _ =
              if backtrack_trace.val then do {
                Printf.eprintf "result found !\n\n";
                flush stderr;
              }
              else ()
            in
            loop [r :: rev_rl] (Fstream.bcontinue k)
        | None -> List.rev rev_rl ]
    in
    restore ();
    rl
  }
  with exc -> do {
    let loc = (Stream.count cs, Stream.count cs + 1) in
    restore ();
    Ploc.raise (Ploc.make_unlined loc) exc
  }
};

value find_entry e s =
  let rec find_levels =
    fun
    [ [] -> None
    | [lev :: levs] ->
        match find_tree lev.lsuffix with
        [ None ->
            match find_tree lev.lprefix with
            [ None -> find_levels levs
            | x -> x ]
        | x -> x ] ]
  and find_symbol =
    fun
    [ Sfacto s -> find_symbol s
    | Snterm e -> if e.ename = s then Some e else None
    | Snterml e _ -> if e.ename = s then Some e else None
    | Smeta _ sl _ -> find_symbol_list sl
    | Slist0 s -> find_symbol s
    | Slist0sep s _ _ -> find_symbol s
    | Slist1 s -> find_symbol s
    | Slist1sep s _ _ -> find_symbol s
    | Sopt s -> find_symbol s
    | Sflag s -> find_symbol s
    | Stree t -> find_tree t
    | Svala _ s -> find_symbol s
    | Sself | Snext | Scut | Stoken _ -> None ]
  and find_symbol_list =
    fun
    [ [s :: sl] ->
        match find_symbol s with
        [ None -> find_symbol_list sl
        | x -> x ]
    | [] -> None ]
  and find_tree =
    fun
    [ Node {node = s; brother = bro; son = son} ->
        match find_symbol s with
        [ None ->
            match find_tree bro with
            [ None -> find_tree son
            | x -> x ]
        | x -> x ]
    | LocAct _ _ | DeadEnd -> None ]
  in
  match e.edesc with
  [ Dlevels levs ->
      match find_levels levs with
      [ Some e -> e
      | None -> raise Not_found ]
  | Dparser _ -> raise Not_found ]
;

value bfparser_of_parser p fstrm return_value = do {
  let shift_token_number = Fstream.count fstrm in
  let old_floc = floc.val in
  let restore () = floc.val := old_floc in
  floc.val := fun i -> old_floc (shift_token_number + i);
  let ts =
    let fts = ref fstrm in
    Stream.from
      (fun _ ->
         match Fstream.next fts.val with
         [ Some (v, fstrm) -> do { fts.val := fstrm; Some v }
         | None -> None ])
  in
  let r =
    try
      let r = (Obj.magic p ts : Obj.t) in
      let fstrm =
        loop fstrm (Stream.count ts) where rec loop fstrm i =
          if i = 0 then fstrm
          else
            match Fstream.next fstrm with
            [ Some (_, fstrm) -> loop fstrm (i - 1)
            | None -> failwith "internal error in Entry.of_parser" ]
      in
      return_value r fstrm
    with e -> do {
      restore ();
      match e with
      | Stream.Failure -> None
      | _ -> raise e
      end
    }
  in
  do { restore (); r }
};

value fparser_of_parser p err fstrm =
  let return_value r fstrm = match fstrm with fparser [: :] -> r in
  bfparser_of_parser p fstrm return_value
;

value bparser_of_parser p err fstrm =
  let return_value r fstrm = match fstrm with bparser [: :] -> r in
  bfparser_of_parser p fstrm return_value
;

module Entry =
  struct
    type te = token;
    type e 'a = g_entry te;
    value create g n =
      {egram = g; ename = n; elocal = False; estart = empty_entry n;
       econtinue _ _ _ = parser []; fstart _ _ = fparser [];
       fcontinue _ _ _ _ = fparser []; bstart _ _ = bparser [];
       bcontinue _ _ _ _ = bparser []; edesc = Dlevels []}
    ;
    value parse_parsable (entry : e 'a) p : 'a =
      let _ = compatible_deprecated_backtrack_parse () in
      match entry.egram.galgo with
      [ DefaultAlgorithm ->
          match default_algorithm_var.val with
          | Predictive | DefaultAlgorithm ->
              Obj.magic (parse_parsable entry p : Obj.t)
          | Backtracking ->
              Obj.magic (bparse_parsable entry p : Obj.t)
          | Functional ->
              Obj.magic (fparse_parsable entry p : Obj.t)
          end
      | Predictive ->
          Obj.magic (parse_parsable entry p : Obj.t)
      | Functional ->
          Obj.magic (fparse_parsable entry p : Obj.t)
      | Backtracking ->
          Obj.magic (bparse_parsable entry p : Obj.t) ]
    ;
    value parse (entry : e 'a) cs : 'a =
      let parsable = parsable entry.egram cs in
      parse_parsable entry parsable
    ;
    value parse_parsable_all (entry : e 'a) p : 'a =
      let _ = compatible_deprecated_backtrack_parse () in
      match entry.egram.galgo with
      [ DefaultAlgorithm ->
          match default_algorithm_var.val with
          | Predictive | DefaultAlgorithm ->
              try Obj.magic [(parse_parsable entry p : Obj.t)] with
              [ Stream.Failure | Stream.Error _ -> [] ]
          | Backtracking ->
             Obj.magic (bparse_parsable_all entry p : list Obj.t)
          | Functional ->
              failwith "Entry.parse_parsable_all: func parsing not impl"
          end
      | Predictive ->
          try Obj.magic [(parse_parsable entry p : Obj.t)] with
          [ Stream.Failure | Stream.Error _ -> [] ]
      | Functional ->
          failwith "parse_parsable_all: functional parsing not impl"
      | Backtracking ->
          Obj.magic (bparse_parsable_all entry p : list Obj.t) ]
    ;
    value parse_all (entry : e 'a) cs : 'a =
      let parsable = parsable entry.egram cs in
      parse_parsable_all entry parsable
    ;
    value parse_token_stream (entry : e 'a) ts : 'a =
      let _ = compatible_deprecated_backtrack_parse () in
      match entry.egram.galgo with
      | DefaultAlgorithm ->
          match default_algorithm_var.val with
          | Predictive | DefaultAlgorithm ->
              Obj.magic (entry.estart 0 ts : Obj.t)
          | Backtracking ->
              failwith "not impl Entry.parse_token_stream default backtrack"
          | Functional ->
              failwith "Entry.parse_token_stream: func parsing not impl"
          end
      | Predictive -> Obj.magic (entry.estart 0 ts : Obj.t)
      | Functional ->
          failwith "not impl Entry.parse_token_stream functional"
      | Backtracking ->
          failwith "not impl Entry.parse_token_stream backtrack"
      end
    ;
    value warned_using_parse_token = ref False;
    value parse_token (entry : e 'a) ts : 'a = do {
      (* commented: too often warned in Coq...
      if not warned_using_parse_token.val then do {
        eprintf "<W> use of Grammar.Entry.parse_token ";
        eprintf "deprecated since 2017-06-16\n%!";
        eprintf "use Grammar.Entry.parse_token_stream instead\n%! ";
        warned_using_parse_token.val := True
      }
      else ();
      *)
      parse_token_stream entry ts
    };
    value name e = e.ename;
    value of_parser g n (p : Stream.t te -> 'a) : e 'a =
      {egram = g; ename = n; elocal = False;
       estart _ = (Obj.magic p : Stream.t te -> Obj.t);
       econtinue _ _ _ = parser [];
       fstart _ = fparser_of_parser p;
       fcontinue _ _ _ _ = fparser [];
       bstart _ = bparser_of_parser p;
       bcontinue _ _ _ _ = bparser [];
       edesc = Dparser (Obj.magic p : Stream.t te -> Obj.t)}
    ;
    external obj : e 'a -> Gramext.g_entry te = "%identity";
    value print ppf e = fprintf ppf "%a@." print_entry (obj e);
    value find e s = find_entry (obj e) s;
  end
;

value of_entry e = e.egram;

value create_local_entry g n =
  {egram = g; ename = n; elocal = True; estart = empty_entry n;
   econtinue _ _ _ = parser []; fstart _ _ = fparser [];
   fcontinue _ _ _ _ = fparser []; bstart _ _ = bparser [];
   bcontinue _ _ _ _ = bparser []; edesc = Dlevels []}
;

(* Unsafe *)

value clear_entry e = do {
  e.estart := fun _ -> parser [];
  e.econtinue := fun _ _ _ -> parser [];
  e.fstart := fun _ _ -> fparser [];
  e.fcontinue := fun _ _ _ _ -> fparser [];
  e.bstart := fun _ _ -> bparser [];
  e.bcontinue := fun _ _ _ _ -> bparser [];
  match e.edesc with
  [ Dlevels _ -> e.edesc := Dlevels []
  | Dparser _ -> () ]
};

value gram_reinit g glexer = do {
  Hashtbl.clear g.gtokens;
  g.glexer := glexer
};

module Unsafe =
  struct
    value gram_reinit = gram_reinit;
    value clear_entry = clear_entry;
  end
;

(* Functorial interface *)

module type GLexerType =
  sig
    type te = 'x;
    value lexer : Plexing.lexer te;
  end
;

module type S =
  sig
    type te = 'x;
    type parsable = 'x;
    value parsable : Stream.t char -> parsable;
    value tokens : string -> list (string * int);
    value glexer : Plexing.lexer te;
    value set_algorithm : parse_algorithm -> unit;
    module Entry :
      sig
        type e 'a = 'x;
        value create : string -> e 'a;
        value parse : e 'a -> parsable -> 'a;
        value name : e 'a -> string;
        value of_parser : string -> (Stream.t te -> 'a) -> e 'a;
        value parse_token_stream : e 'a -> Stream.t te -> 'a;
        value print : Format.formatter -> e 'a -> unit;
        external obj : e 'a -> Gramext.g_entry te = "%identity";
        value parse_token : e 'a -> Stream.t te -> 'a;
      end
    ;
    type ty_symbol 'self 'a = 'x;
    (** Type of grammar symbols. A type-safe wrapper around Gramext.symbol. The
        first type argument is the type of the ambient entry, the second one is the
        type of the produced value. *)

    type ty_rule 'self 'f 'r = 'x;

    type ty_production 'a = 'x;

    value s_facto : ty_symbol 'self 'a -> ty_symbol 'self 'a;
    (*   | Smeta of string and list (g_symbol 'te) and Obj.t *)
    value s_nterm : Entry.e 'a -> ty_symbol 'self 'a;
    value s_nterml : Entry.e 'a -> string -> ty_symbol 'self 'a;
    value s_list0 : ty_symbol 'self 'a -> ty_symbol 'self (list 'a);
    value s_list0sep : ty_symbol 'self 'a -> ty_symbol 'self 'b -> bool -> ty_symbol 'self (list 'a);
    value s_list1 : ty_symbol 'self 'a -> ty_symbol 'self (list 'a);
    value s_list1sep : ty_symbol 'self 'a -> ty_symbol 'self 'b -> bool -> ty_symbol 'self (list 'a);
    value s_opt : ty_symbol 'self 'a -> ty_symbol 'self (option 'a);
    value s_flag : ty_symbol 'self 'a -> ty_symbol 'self bool;
    value s_self : ty_symbol 'self 'self;
    value s_next : ty_symbol 'self 'self;
    value s_token : Plexing.pattern -> ty_symbol 'self string;
    value s_rules : list (ty_production 'a) -> ty_symbol 'self 'a;
    value s_vala : list string -> ty_symbol 'self 'a -> ty_symbol 'self (Ploc.vala 'a);

    value r_stop : ty_rule 'self 'r 'r;
    value r_next : ty_rule 'self 'a 'r -> ty_symbol 'self 'b -> ty_rule 'self ('b -> 'a) 'r;
    value r_cut : ty_rule 'self 'a 'r -> ty_rule 'self 'a 'r;

    value production : (ty_rule 'a 'f (Ploc.t -> 'a) * 'f) -> ty_production 'a;

    module Unsafe :
      sig
        value gram_reinit : Plexing.lexer te -> unit;
        value clear_entry : Entry.e 'a -> unit;
      end
    ;
    value extend :
      Entry.e 'a -> option Gramext.position ->
        list
          (option string * option Gramext.g_assoc *
           list (list (Gramext.g_symbol te) * Gramext.g_action)) ->
        unit;
    value safe_extend :
      Entry.e 'a -> option Gramext.position ->
        list
          (option string * option Gramext.g_assoc *
            list (ty_production 'a)) ->
        unit;
    value delete_rule : Entry.e 'a -> list (Gramext.g_symbol te) -> unit;
    value safe_delete_rule : Entry.e 'a -> ty_rule 'a 'r 'f -> unit;
  end
;

module GMake (L : GLexerType) =
  struct
    type te = L.te;
    type parsable = gen_parsable te;
    value gram = gcreate L.lexer;
    value parsable cs =
      let (ts, lf) = L.lexer.Plexing.tok_func cs in
      let fts = fstream_of_stream ts in
      {pa_chr_strm = cs; pa_tok_strm = ts; pa_tok_fstrm = fts;
       pa_loc_func = lf}
    ;
    value tokens = tokens gram;
    value glexer = glexer gram;
    value set_algorithm algo = gram.galgo := algo;
    module Entry =
      struct
        type e 'a = g_entry te;
        value create n =
          {egram = gram; ename = n; elocal = False; estart = empty_entry n;
           econtinue _ _ _ = parser []; fstart _ _ = fparser [];
           fcontinue _ _ _ _ = bparser []; bstart _ _ = bparser [];
           bcontinue _ _ _ _ = bparser []; edesc = Dlevels []}
        ;
        external obj : e 'a -> Gramext.g_entry te = "%identity";
        value parse (e : e 'a) p : 'a =
          let _ = compatible_deprecated_backtrack_parse () in
          match gram.galgo with
          [ DefaultAlgorithm ->
              match default_algorithm_var.val with
              | Predictive | DefaultAlgorithm ->
                  Obj.magic (parse_parsable e p : Obj.t)
              | Backtracking ->
                  Obj.magic (bparse_parsable e p : Obj.t)
              | Functional ->
                  Obj.magic (fparse_parsable e p : Obj.t)
              end
          | Predictive ->
              Obj.magic (parse_parsable e p : Obj.t)
          | Functional ->
              Obj.magic (fparse_parsable e p : Obj.t)
          | Backtracking ->
              Obj.magic (bparse_parsable e p : Obj.t) ]
        ;
        value parse_token_stream (e : e 'a) ts : 'a =
          let _ = compatible_deprecated_backtrack_parse () in
          match e.egram.galgo with
          | DefaultAlgorithm ->
              match default_algorithm_var.val with
              | Predictive | DefaultAlgorithm ->
                  Obj.magic (e.estart 0 ts : Obj.t)
              | Backtracking ->
                  bparse_token_stream e ts
              | Functional ->
                  fparse_token_stream e ts
              end
          | Predictive -> Obj.magic (e.estart 0 ts : Obj.t)
          | Functional -> fparse_token_stream e ts
          | Backtracking -> bparse_token_stream e ts
          end
        ;
        value warned_using_parse_token = ref False;
        value parse_token (entry : e 'a) ts : 'a = do {
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
        };
        value name e = e.ename;
        value of_parser n (p : Stream.t te -> 'a) : e 'a =
          {egram = gram; ename = n; elocal = False;
           estart _ = (Obj.magic p : Stream.t te -> Obj.t);
           econtinue _ _ _ = parser [];
           fstart _ = fparser_of_parser p;
           fcontinue _ _ _ _ = fparser [];
           bstart _ = bparser_of_parser p;
           bcontinue _ _ _ _ = bparser [];
           edesc = Dparser (Obj.magic p : Stream.t te -> Obj.t)}
        ;
        value print ppf e = fprintf ppf "%a@." print_entry (obj e);
      end
    ;
    type ty_symbol 'self 'a = Gramext.g_symbol te;
    type ty_rule 'self 'f 'r = list (ty_symbol 'self Obj.t);
    type ty_production 'a = (ty_rule 'a Obj.t Obj.t * Gramext.g_action);

    value s_facto s = Sfacto s;
    value s_nterm e = Snterm e;
    value s_nterml e l = Snterml e l;
    value s_list0 s = Slist0 s;
    value s_list0sep s sep b = Slist0sep s sep b;
    value s_list1 s = Slist1 s;
    value s_list1sep s sep b = Slist1sep s sep b;
    value s_opt s = Sopt s;
    value s_flag s = Sflag s;
    value s_self = Sself;
    value s_next = Snext;
    value s_token tok = Stoken tok;
    value s_rules (t : list (ty_production Obj.t)) = Gramext.srules (Obj.magic t);
    value s_vala sl s = Svala sl s;

    value r_stop = [];
    value r_next r s = r @ [s];
    value r_cut r = r @ [Scut];

    value production (p : (ty_rule 'a 'f (Ploc.t -> 'a) * 'f)) = (Obj.magic p : ty_production 'a);

    module Unsafe =
      struct
        value gram_reinit = gram_reinit gram;
        value clear_entry = clear_entry;
      end
    ;
    value extend = extend_entry;
    value safe_extend e pos (r : list (option string * option Gramext.g_assoc * list (ty_production Obj.t))) = extend e pos (Obj.magic r);
    value delete_rule e r = delete_rule (Entry.obj e) r;
    value safe_delete_rule = delete_rule;
  end
;
