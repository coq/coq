(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Constrexpr
open Constrexpr_ops
open Vernacexpr
open Notation_term
open Notation_gram
open Notation_ops
open Ppextend
open Extend
open Libobject
open Constrintern
open Libnames
open Notation
open Nameops

(**********************************************************************)
(* Tokens                                                             *)

let cache_token (_,s) = CLexer.add_keyword s

let inToken : string -> obj =
  declare_object @@ global_object_nodischarge "TOKEN"
    ~cache:cache_token
    ~subst:(Some Libobject.ident_subst_function)

let add_token_obj s = Lib.add_anonymous_leaf (inToken s)

(**********************************************************************)
(* Printing grammar entries                                           *)

let entry_buf = Buffer.create 64

let pr_entry e =
  let () = Buffer.clear entry_buf in
  let ft = Format.formatter_of_buffer entry_buf in
  let () = Pcoq.Entry.print ft e in
  str (Buffer.contents entry_buf)

let pr_registered_grammar name =
  let gram = Pcoq.find_grammars_by_name name in
  match gram with
  | [] -> user_err Pp.(str "Unknown or unprintable grammar entry.")
  | entries ->
    let pr_one (Pcoq.AnyEntry e) =
      str "Entry " ++ str (Pcoq.Entry.name e) ++ str " is" ++ fnl () ++
      pr_entry e
    in
    prlist pr_one entries

let pr_grammar = function
  | "constr" | "term" | "binder_constr" ->
      str "Entry constr is" ++ fnl () ++
      pr_entry Pcoq.Constr.constr ++
      str "and lconstr is" ++ fnl () ++
      pr_entry Pcoq.Constr.lconstr ++
      str "where binder_constr is" ++ fnl () ++
      pr_entry Pcoq.Constr.binder_constr ++
      str "and term is" ++ fnl () ++
      pr_entry Pcoq.Constr.term
  | "pattern" ->
      pr_entry Pcoq.Constr.pattern
  | "vernac" ->
      str "Entry vernac_control is" ++ fnl () ++
      pr_entry Pvernac.Vernac_.vernac_control ++
      str "Entry command is" ++ fnl () ++
      pr_entry Pvernac.Vernac_.command ++
      str "Entry syntax is" ++ fnl () ++
      pr_entry Pvernac.Vernac_.syntax ++
      str "Entry gallina is" ++ fnl () ++
      pr_entry Pvernac.Vernac_.gallina ++
      str "Entry gallina_ext is" ++ fnl () ++
      pr_entry Pvernac.Vernac_.gallina_ext
  | name -> pr_registered_grammar name

let pr_custom_grammar name = pr_registered_grammar ("custom:"^name)

(**********************************************************************)
(* Parse a format (every terminal starting with a letter or a single
   quote (except a single quote alone) must be quoted) *)

let parse_format ({CAst.loc;v=str} : lstring) =
  let len = String.length str in
  (* TODO: update the line of the location when the string contains newlines *)
  let make_loc i j = Option.map (Loc.shift_loc (i+1) (j-len)) loc in
  let push_token loc a = function
    | (i,cur)::l -> (i,(loc,a)::cur)::l
    | [] -> assert false in
  let push_white i n l =
    if Int.equal n 0 then l else push_token (make_loc i (i+n)) (UnpTerminal (String.make n ' ')) l in
  let close_box start stop b = function
    | (_,a)::(_::_ as l) -> push_token (make_loc start stop) (UnpBox (b,a)) l
    | [a] -> user_err ?loc:(make_loc start stop) Pp.(str "Non terminated box in format.")
    | [] -> assert false in
  let close_quotation start i =
    if i < len && str.[i] == '\'' then
      if (Int.equal (i+1) len || str.[i+1] == ' ')
      then i+1
      else user_err ?loc:(make_loc (i+1) (i+1)) Pp.(str "Space expected after quoted expression.")
    else
      user_err ?loc:(make_loc start (i-1)) Pp.(str "Beginning of quoted expression expected to be ended by a quote.") in
  let rec spaces n i =
    if i < len && str.[i] == ' ' then spaces (n+1) (i+1)
    else n in
  let rec nonspaces quoted n i =
    if i < len && str.[i] != ' ' then
      if str.[i] == '\'' && quoted &&
        (i+1 >= len || str.[i+1] == ' ')
      then if Int.equal n 0 then user_err ?loc:(make_loc (i-1) i) Pp.(str "Empty quoted token.") else n
      else nonspaces quoted (n+1) (i+1)
    else
      if quoted then user_err ?loc:(make_loc i i) Pp.(str "Spaces are not allowed in (quoted) symbols.")
      else n in
  let rec parse_non_format i =
    let n = nonspaces false 0 i in
    push_token (make_loc i (i+n-1)) (UnpTerminal (String.sub str i n)) (parse_token 1 (i+n))
  and parse_quoted n k i =
    if i < len then match str.[i] with
      (* Parse " // " *)
      | '/' when i+1 < len && str.[i+1] == '/' ->
          (* We discard the useless n spaces... *)
          push_token (make_loc (i-n) (i+1)) (UnpCut PpFnl)
            (parse_token 1 (close_quotation i (i+2)))
      (* Parse " .. / .. " *)
      | '/' when i+1 < len ->
          let p = spaces 0 (i+1) in
          push_token (make_loc (i-n) (i+p)) (UnpCut (PpBrk (n,p)))
            (parse_token 1 (close_quotation i (i+p+1)))
      | c ->
      (* The spaces are real spaces *)
      push_white (i-n-1-k) n (match c with
      | '[' ->
          if i+1 < len then match str.[i+1] with
            (* Parse " [h .. ",  *)
            | 'h' when i+1 <= len && str.[i+2] == 'v' ->
                  (parse_box i (fun n -> PpHVB n) (i+3))
                (* Parse " [v .. ",  *)
            | 'v' ->
                    parse_box i (fun n -> PpVB n) (i+2)
                (* Parse " [ .. ",  *)
            | ' ' | '\'' ->
                parse_box i (fun n -> PpHOVB n) (i+1)
            | _ -> user_err ?loc:(make_loc i i) Pp.(str "\"v\", \"hv\", \" \" expected after \"[\" in format.")
          else user_err ?loc:(make_loc i i) Pp.(str "\"v\", \"hv\" or \" \" expected after \"[\" in format.")
      (* Parse "]"  *)
      | ']' ->
          ((i,[]) :: parse_token 1 (close_quotation i (i+1)))
      (* Parse a non formatting token *)
      | c ->
          let n = nonspaces true 0 i in
          push_token (make_loc i (i+n-1)) (UnpTerminal (String.sub str (i-1) (n+2)))
            (parse_token 1 (close_quotation i (i+n))))
    else
      if Int.equal n 0 then []
      else user_err ?loc:(make_loc (len-n) len) Pp.(str "Ending spaces non part of a format annotation.")
  and parse_box start box i =
    let n = spaces 0 i in
    close_box start (i+n-1) (box n) (parse_token 1 (close_quotation i (i+n)))
  and parse_token k i =
    let n = spaces 0 i in
    let i = i+n in
    if i < len then match str.[i] with
      (* Parse a ' *)
      |	'\'' when i+1 >= len || str.[i+1] == ' ' ->
          push_white (i-n) (n-k) (push_token (make_loc i (i+1)) (UnpTerminal "'") (parse_token 1 (i+1)))
      (* Parse the beginning of a quoted expression *)
      |	'\'' ->
          parse_quoted (n-k) k (i+1)
      (* Otherwise *)
      | _ ->
          push_white (i-n) (n-k) (parse_non_format i)
    else push_white (i-n) n [(len,[])]
  in
  if not (String.is_empty str) then
    match parse_token 0 0 with
    | [_,l] -> l
    | (i,_)::_ -> user_err ?loc:(make_loc i i) Pp.(str "Box closed without being opened.")
    | [] -> assert false
  else
    []

(***********************)
(* Analyzing notations *)

(* Find non-terminal tokens of notation *)

(* To protect alphabetic tokens and quotes from being seen as variables *)
let quote_notation_token x =
  let n = String.length x in
  let norm = CLexer.is_ident x in
  if (n > 0 && norm) || (n > 2 && x.[0] == '\'') then "'"^x^"'"
  else x

let is_numeral_in_constr entry symbs =
  match entry, List.filter (function Break _ -> false | _ -> true) symbs with
  | InConstrEntry, ([Terminal "-"; Terminal x] | [Terminal x]) ->
      NumTok.Unsigned.parse_string x <> None
  | _ ->
      false

let analyze_notation_tokens ~onlyprinting ~infix entry df =
  let df = if infix then quote_notation_token df else df in
  let { recvars; mainvars; symbols } as res = decompose_raw_notation df in
    (* don't check for nonlinearity if printing only, see Bug 5526 *)
  (if not onlyprinting then
    match List.duplicates Id.equal (mainvars @ List.map snd recvars) with
    | id :: _ ->
        user_err ~hdr:"Metasyntax.get_notation_vars"
          (str "Variable " ++ Id.print id ++ str " occurs more than once.")
    | _ -> ());
  let isnumeral = is_numeral_in_constr entry symbols in
  res, isnumeral

let adjust_symbols vars notation_symbols =
  let x = Namegen.next_ident_away (Id.of_string "x") vars in
  let y = Namegen.next_ident_away (Id.of_string "y") (Id.Set.add x vars) in
  let notation_symbols = {
      recvars = notation_symbols.recvars; mainvars = x::notation_symbols.mainvars@[y];
      symbols = NonTerminal x :: notation_symbols.symbols @ [NonTerminal y];
    } in
  x, y, notation_symbols

let adjust_reserved_infix_notation notation_symbols =
  let vars = Id.Set.of_list (List.map_filter (function NonTerminal x -> Some x | _ -> None) notation_symbols.symbols) in
  let _, _, notation_symbols = adjust_symbols vars notation_symbols in
  notation_symbols

let adjust_infix_notation df notation_symbols c =
  let vars = names_of_constr_expr c in
  let x, y, notation_symbols = adjust_symbols vars notation_symbols in
  let df = Id.to_string x ^ " " ^ df ^ " " ^ Id.to_string y in
  let inject_var x = CAst.make @@ CRef (qualid_of_ident x,None) in
  let metas = [inject_var x; inject_var y] in
  let c = mkAppC (c,metas) in
  df, notation_symbols, c

let warn_unexpected_primitive_token_modifier =
  CWarnings.create ~name:"primitive-token-modifier" ~category:"parsing"
         (fun () -> str "Notations for numbers are primitive; skipping this modifier.")

let check_no_syntax_modifiers_for_numeral = function
  | [] -> ()
  | l -> List.iter (function {CAst.loc} -> warn_unexpected_primitive_token_modifier ?loc ()) l

let error_not_same_scope x y =
  user_err ~hdr:"Metasyntax.error_not_name_scope"
    (str "Variables " ++ Id.print x ++ str " and " ++ Id.print y ++ str " must be in the same scope.")

(**********************************************************************)
(* Build pretty-printing rules                                        *)

let pr_notation_entry = function
  | InConstrEntry -> str "constr"
  | InCustomEntry s -> str "custom " ++ str s

let precedence_of_position_and_level from_level = function
  | NumLevel n, BorderProd (b,Some a) ->
    (let open Gramlib.Gramext in
     match a, b with
     | RightA, Left -> LevelLt n
     | RightA, Right -> LevelLe n
     | LeftA, Left -> LevelLe n
     | LeftA, Right -> LevelLt n
     | NonA, _ -> LevelLt n), Some b
  | NumLevel n, _ -> LevelLe n, None
  | NextLevel, _ -> LevelLt from_level, None
  | DefaultLevel, _ -> LevelSome, None

(** Computing precedences of subentries for parsing *)
let precedence_of_entry_type (from_custom,from_level) = function
  | ETConstr (custom,_,x) when notation_entry_eq custom from_custom ->
    fst (precedence_of_position_and_level from_level x)
  | ETConstr (custom,_,(NumLevel n,_)) -> LevelLe n
  | ETConstr (custom,_,(NextLevel,_)) ->
    user_err (strbrk "\"next level\" is only for sub-expressions in the same entry as where the notation is (" ++
              quote (pr_notation_entry custom) ++ strbrk " is different from " ++
              quote (pr_notation_entry from_custom) ++ str ").")
  | ETPattern (_,n) -> let n = match n with None -> 0 | Some n -> n in LevelLe n
  | _ -> LevelSome (* should not matter *)

(** Computing precedences for future insertion of parentheses at
    the time of printing using hard-wired constr levels *)
let unparsing_precedence_of_entry_type from_level = function
  | ETConstr (InConstrEntry,_,x) ->
    (* Possible insertion of parentheses at printing time to deal
       with precedence in a constr entry is managed using [prec_less]
       in [ppconstr.ml] *)
    precedence_of_position_and_level from_level x
  | ETConstr (custom,_,_) ->
    (* Precedence of printing for a custom entry is managed using
       explicit insertion of entry coercions at the time of building
       a [constr_expr] *)
    LevelSome, None
  | ETPattern (_,n) -> (* in constr *) LevelLe (match n with Some n -> n | None -> 0), None
  | _ -> LevelSome, None (* should not matter *)

(* Some breaking examples *)
(* "x = y" : "x /1 = y" (breaks before any symbol) *)
(* "x =S y" : "x /1 =S /1 y" (protect from confusion; each side for symmetry)*)
(* "+ {" : "+ {" may breaks reversibility without space but oth. not elegant *)
(* "x y" : "x spc y" *)
(* "{ x } + { y }" : "{ x } / + { y }" *)
(* "< x , y > { z , t }" : "< x , / y > / { z , / t }" *)

let starts_with_left_bracket s =
  let l = String.length s in not (Int.equal l 0) &&
  (s.[0] == '{' || s.[0] == '[' || s.[0] == '(')

let ends_with_right_bracket s =
  let l = String.length s in not (Int.equal l 0) &&
  (s.[l-1] == '}' || s.[l-1] == ']' || s.[l-1] == ')')

let is_left_bracket s =
  starts_with_left_bracket s && not (ends_with_right_bracket s)

let is_right_bracket s =
  not (starts_with_left_bracket s) && ends_with_right_bracket s

let is_comma s =
  let l = String.length s in not (Int.equal l 0) &&
  (s.[0] == ',' || s.[0] == ';')

let is_operator s =
  let l = String.length s in not (Int.equal l 0) &&
  (s.[0] == '+' || s.[0] == '*' || s.[0] == '=' ||
   s.[0] == '-' || s.[0] == '/' || s.[0] == '<' || s.[0] == '>' ||
   s.[0] == '@' || s.[0] == '\\' || s.[0] == '&' || s.[0] == '~' || s.[0] == '$')

let is_non_terminal = function
  | NonTerminal _ | SProdList _ -> true
  | _ -> false

let is_next_non_terminal b = function
| [] -> b
| pr :: _ -> is_non_terminal pr

let is_next_terminal = function Terminal _ :: _ -> true | _ -> false

let is_next_break = function Break _ :: _ -> true | _ -> false

let add_break n l = (None,UnpCut (PpBrk(n,0))) :: l

let add_break_if_none n b = function
  | (_,UnpCut (PpBrk _)) :: _ as l -> l
  | [] when not b -> []
  | l -> (None,UnpCut (PpBrk(n,0))) :: l

let check_open_binder isopen sl m =
  let pr_token = function
  | Terminal s -> str s
  | Break n -> str "␣"
  | _ -> assert false
  in
  if isopen && not (List.is_empty sl) then
    user_err  (str "as " ++ Id.print m ++
      str " is a non-closed binder, no such \"" ++
      prlist_with_sep spc pr_token sl
      ++ strbrk "\" is allowed to occur.")

let unparsing_metavar i from typs =
  let x = List.nth typs (i-1) in
  let prec,side = unparsing_precedence_of_entry_type from x in
  match x with
  | ETConstr _ | ETGlobal | ETBigint ->
     UnpMetaVar (prec,side)
  | ETPattern _ | ETName _ | ETIdent ->
     UnpBinderMetaVar (prec,NotQuotedPattern)
  | ETBinder isopen ->
     UnpBinderMetaVar (prec,QuotedPattern)

(* Heuristics for building default printing rules *)

let index_id id l = List.index Id.equal id l

let make_hunks etyps symbols from_level =
  let vars,typs = List.split etyps in
  let rec make b = function
    | NonTerminal m :: prods ->
        let i = index_id m vars in
        let u = unparsing_metavar i from_level typs in
        if is_next_non_terminal b prods then
          (None, u) :: add_break_if_none 1 b (make b prods)
        else
          (None, u) :: make_with_space b prods
    | Terminal s :: prods
         when (* true to simulate presence of non-terminal *) b || List.exists is_non_terminal prods ->
        if (is_comma s || is_operator s) then
          (* Always a breakable space after comma or separator *)
          (None, UnpTerminal s) :: add_break_if_none 1 b (make b prods)
        else if is_right_bracket s && is_next_terminal prods then
          (* Always no space after right bracked, but possibly a break *)
          (None, UnpTerminal s) :: add_break_if_none 0 b (make b prods)
        else if is_left_bracket s  && is_next_non_terminal b prods then
          (None, UnpTerminal s) :: make b prods
        else if not (is_next_break prods) then
          (* Add rigid space, no break, unless user asked for something *)
          (None, UnpTerminal (s^" ")) :: make b prods
        else
          (* Rely on user spaces *)
          (None, UnpTerminal s) :: make b prods

    | Terminal s :: prods ->
        (* Separate but do not cut a trailing sequence of terminal *)
        (match prods with
        | Terminal _ :: _ -> (None,UnpTerminal (s^" ")) :: make b prods
        | _ -> (None,UnpTerminal s) :: make b prods)

    | Break n :: prods ->
        add_break n (make b prods)

    | SProdList (m,sl) :: prods ->
        let i = index_id m vars in
        let typ = List.nth typs (i-1) in
        let prec,side = unparsing_precedence_of_entry_type from_level typ in
        let sl' =
          (* If no separator: add a break *)
          if List.is_empty sl then add_break 1 []
          (* We add NonTerminal for simulation but remove it afterwards *)
          else make true sl in
        let hunk = match typ with
          | ETConstr _ -> UnpListMetaVar (prec,List.map snd sl',side)
          | ETBinder isopen ->
              check_open_binder isopen sl m;
              UnpBinderListMetaVar (isopen,List.map snd sl')
          | _ -> assert false in
        (None, hunk) :: make_with_space b prods

    | [] -> []

  and make_with_space b prods =
    match prods with
    | Terminal s' :: prods'->
        if is_operator s' then
          (* A rigid space before operator and a breakable after *)
          (None,UnpTerminal (" "^s')) :: add_break_if_none 1 b (make b prods')
        else if is_comma s' then
          (* No space whatsoever before comma *)
          make b prods
        else if is_right_bracket s' then
          make b prods
        else
          (* A breakable space between any other two terminals *)
          add_break_if_none 1 b (make b prods)
    | (NonTerminal _ | SProdList _) :: _ ->
        (* A breakable space before a non-terminal *)
        add_break_if_none 1 b (make b prods)
    | Break _ :: _ ->
        (* Rely on user wish *)
        make b prods
    | [] -> []

  in make false symbols

(* Build default printing rules from explicit format *)

let error_format ?loc () = user_err ?loc Pp.(str "The format does not match the notation.")

let warn_format_break =
  CWarnings.create ~name:"notation-both-format-and-spaces" ~category:"parsing"
         (fun () ->
          strbrk "Discarding format implicitly indicated by multiple spaces in notation because an explicit format modifier is given.")

let has_ldots l =
  List.exists (function (_,UnpTerminal s) -> String.equal s (Id.to_string Notation_ops.ldots_var) | _ -> false) l

let rec split_format_at_ldots hd = function
  | (loc,UnpTerminal s) :: fmt when String.equal s (Id.to_string Notation_ops.ldots_var) -> loc, List.rev hd, fmt
  | u :: fmt ->
      check_no_ldots_in_box u;
      split_format_at_ldots (u::hd) fmt
  | [] -> raise Exit

and check_no_ldots_in_box = function
  | (_,UnpBox (_,fmt)) ->
      (try
        let loc,_,_ = split_format_at_ldots [] fmt in
        user_err ?loc Pp.(str ("The special symbol \"..\" must occur at the same formatting depth than the variables of which it is the ellipse."))
      with Exit -> ())
  | _ -> ()

let error_not_same ?loc () =
  user_err ?loc Pp.(str "The format is not the same on the right- and left-hand sides of the special token \"..\".")

let find_prod_list_loc sfmt fmt =
  (* [fmt] is some [UnpTerminal x :: sfmt @ UnpTerminal ".." :: sfmt @ UnpTerminal y :: rest] *)
  if List.is_empty sfmt then
    (* No separators; we highlight the sequence "x .." *)
    Loc.merge_opt (fst (List.hd fmt)) (fst (List.hd (List.tl fmt)))
  else
    (* A separator; we highlight the separating sequence *)
    Loc.merge_opt (fst (List.hd sfmt)) (fst (List.last sfmt))

let is_blank s =
  let n = String.length s in
  let rec aux i s = i >= n || s.[i] = ' ' && aux (i+1) s in
  aux 0 s

let is_formatting = function
  | (_,UnpCut _) -> true
  | (_,UnpTerminal s) -> is_blank s
  | _ -> false

let rec is_var_in_recursive_format = function
  | (_,UnpTerminal s) when not (is_blank s) -> true
  | (loc,UnpBox (b,l)) ->
    (match List.filter (fun a -> not (is_formatting a)) l with
    | [a] -> is_var_in_recursive_format a
    | _ -> error_not_same ?loc ())
  | _ -> false

let rec check_eq_var_upto_name = function
  | (_,UnpTerminal s1), (_,UnpTerminal s2) when not (is_blank s1 && is_blank s2) || s1 = s2 -> ()
  | (_,UnpBox (b1,l1)), (_,UnpBox (b2,l2)) when b1 = b2 -> List.iter check_eq_var_upto_name (List.combine l1 l2)
  | (_,UnpCut b1), (_,UnpCut b2) when b1 = b2 -> ()
  | _, (loc,_) -> error_not_same ?loc ()

let skip_var_in_recursive_format = function
  | a :: sl when is_var_in_recursive_format a -> a, sl
  | (loc,_) :: _ -> error_not_same ?loc ()
  | [] -> assert false

let read_recursive_format sl fmt =
  (* Turn [[UnpTerminal s :: some-list @ UnpTerminal ".." :: same-some-list @ UnpTerminal s' :: rest] *)
  (* into [(some-list,rest)] *)
  let get_head fmt =
    let var,sl = skip_var_in_recursive_format fmt in
    try var, split_format_at_ldots [] sl
    with Exit -> error_not_same ?loc:(fst (List.last (if sl = [] then fmt else sl))) () in
  let rec get_tail = function
    | (loc,a) :: sepfmt, (_,b) :: fmt when (=) a b -> get_tail (sepfmt, fmt) (* FIXME *)
    | [], tail -> skip_var_in_recursive_format tail
    | (loc,_) :: _, ([] | (_,UnpTerminal _) :: _)-> error_not_same ?loc ()
    | _, (loc,_)::_ -> error_not_same ?loc () in
  let var1, (loc, slfmt, fmt) = get_head fmt in
  let var2, res = get_tail (slfmt, fmt) in
  check_eq_var_upto_name (var1,var2);
  (* To do, though not so important: check that the names match
     the names in the notation *)
  slfmt, res

let hunks_of_format (from_level,(vars,typs)) symfmt =
  let rec aux = function
  | symbs, (_,(UnpTerminal s' as u)) :: fmt
      when String.equal s' (String.make (String.length s') ' ') ->
      let symbs, l = aux (symbs,fmt) in symbs, u :: l
  | Terminal s :: symbs, (_,UnpTerminal s') :: fmt
      when String.equal s (String.drop_simple_quotes s') ->
      let symbs, l = aux (symbs,fmt) in symbs, UnpTerminal s :: l
  | NonTerminal s :: symbs, (_,UnpTerminal s') :: fmt when Id.equal s (Id.of_string s') ->
      let i = index_id s vars in
      let symbs, l = aux (symbs,fmt) in symbs, unparsing_metavar i from_level typs :: l
  | symbs, (_,(UnpCut _ as u)) :: fmt ->
      let symbs, l = aux (symbs,fmt) in symbs, u :: l
  | SProdList (m,sl) :: symbs, fmt when has_ldots fmt ->
      let i = index_id m vars in
      let typ = List.nth typs (i-1) in
      let prec,side = unparsing_precedence_of_entry_type from_level typ in
      let loc_slfmt,rfmt = read_recursive_format sl fmt in
      let sl, slfmt = aux (sl,loc_slfmt) in
      if not (List.is_empty sl) then error_format ?loc:(find_prod_list_loc loc_slfmt fmt) ();
      let symbs, l = aux (symbs,rfmt) in
      let hunk = match typ with
        | ETConstr _ -> UnpListMetaVar (prec,slfmt,side)
        | ETBinder isopen ->
            check_open_binder isopen sl m;
            UnpBinderListMetaVar (isopen,slfmt)
        | _ -> assert false in
      symbs, hunk :: l
  | symbs, (_,UnpBox (a,b)) :: fmt ->
      let symbs', b' = aux (symbs,b) in
      let symbs', l = aux (symbs',fmt) in
      symbs', UnpBox (a,List.map (fun x -> (None,x)) b') :: l
  | symbs, [] -> symbs, []
  | Break _ :: symbs, fmt -> warn_format_break (); aux (symbs,fmt)
  | _, fmt -> error_format ?loc:(fst (List.hd fmt)) ()
  in
  match aux symfmt with
  | [], l -> l
  | _ -> error_format ()

(**********************************************************************)
(* Build parsing rules                                                *)

let assoc_of_type from n (_,typ) = precedence_of_entry_type (from,n) typ

let is_not_small_constr = function
    ETProdConstr _ -> true
  | _ -> false

let distribute a ll = List.map (fun l -> a @ l) ll

  (* Expand LIST1(t,sep);sep;t;...;t (with the trailing pattern
     occurring p times, possibly p=0) into the combination of
     t;sep;t;...;t;sep;t (p+1 times)
     t;sep;t;...;t;sep;t;sep;t (p+2 times)
     ...
     t;sep;t;...;t;sep;t;...;t;sep;t (p+n times)
     t;sep;t;...;t;sep;t;...;t;sep;t;LIST1(t,sep) *)

let expand_list_rule s typ tkl x n p ll =
  let camlp5_message_name = Some (add_suffix x ("_"^string_of_int n)) in
  let main = GramConstrNonTerminal (ETProdConstr (s,typ), camlp5_message_name) in
  let tks = List.map (fun (kw,s) -> GramConstrTerminal (kw, s)) tkl in
  let rec aux i hds ll =
  if i < p then aux (i+1) (main :: tks @ hds) ll
  else if Int.equal i (p+n) then
    let hds =
      GramConstrListMark (p+n,true,p) :: hds
      @	[GramConstrNonTerminal (ETProdConstrList (s, typ,tkl), Some x)] in
    distribute hds ll
  else
    distribute (GramConstrListMark (i+1,false,p) :: hds @ [main]) ll @
       aux (i+1) (main :: tks @ hds) ll in
  aux 0 [] ll

let is_constr_typ (s,lev) x etyps =
  match List.assoc x etyps with
  (* TODO: factorize these rules with the ones computing the effective
     sublevel sent to camlp5, so as to include the case of
     DefaultLevel which are valid *)
  | ETConstr (s',_,(lev',InternalProd | (NumLevel _ | NextLevel as lev'), _)) ->
    Notation.notation_entry_eq s s' && production_level_eq lev lev'
  | _ -> false

let include_possible_similar_trailing_pattern typ etyps sl l =
  let rec aux n = function
  | Terminal s :: sl, Terminal s'::l' when s = s' -> aux n (sl,l')
  | [], NonTerminal x ::l' when is_constr_typ typ x etyps -> try_aux n l'
  | Break _ :: sl, l -> aux n (sl,l)
  | sl, Break _ :: l -> aux n (sl,l)
  | _ -> raise Exit
  and try_aux n l =
    try aux (n+1) (sl,l)
    with Exit -> n,l in
  try_aux 0 l

let prod_entry_type = function
  | ETIdent -> ETProdIdent
  | ETName _ -> ETProdName
  | ETGlobal -> ETProdReference
  | ETBigint -> ETProdBigint
  | ETBinder o -> ETProdOneBinder o
  | ETConstr (s,_,p) -> ETProdConstr (s,p)
  | ETPattern (_,n) -> ETProdPattern (match n with None -> 0 | Some n -> n)

let keyword_needed need s =
  (* Ensure that IDENT articulation terminal symbols are keywords *)
  match CLexer.terminal s with
  | Tok.PIDENT (Some k) ->
    if need then
      Flags.if_verbose Feedback.msg_info (str "Identifier '" ++ str k ++ str "' now a keyword");
    need
  | _ ->
  match NumTok.Unsigned.parse_string s with
  | Some n ->
    if need then
      Flags.if_verbose Feedback.msg_info (str "Number '" ++ NumTok.Unsigned.print n ++ str "' now a keyword");
    need
  | _ -> true

let make_production (_,lev,_) etyps symbols =
  let rec aux need = function
    | [] -> [[]]
    | NonTerminal m :: l ->
        let typ = prod_entry_type (List.assoc m etyps) in
        distribute [GramConstrNonTerminal (typ, Some m)] (aux (is_not_small_constr typ) l)
    | Terminal s :: l ->
        let keyword = keyword_needed need s in
        distribute [GramConstrTerminal (keyword,s)] (aux false l)
    | Break _ :: l ->
        aux need l
    | SProdList (x,sl) :: l ->
        let tkl = List.flatten
          (List.map (function Terminal s -> [s]
            | Break _ -> []
            | _ -> anomaly (Pp.str "Found a non terminal token in recursive notation separator.")) sl) in
        let tkl = List.map_i (fun i x -> let need = (i=0) in (keyword_needed need x, x)) 0 tkl in
        match List.assoc x etyps with
        | ETConstr (s,_,(lev,_ as typ)) ->
            let p,l' = include_possible_similar_trailing_pattern (s,lev) etyps sl l in
            expand_list_rule s typ tkl x 1 p (aux true l')
        | ETBinder o ->
            check_open_binder o sl x;
            let typ = if o then (assert (tkl = []); ETBinderOpen) else ETBinderClosed tkl in
            distribute
              [GramConstrNonTerminal (ETProdBinderList typ, Some x)] (aux false l)
        | _ ->
           user_err Pp.(str "Components of recursive patterns in notation must be terms or binders.") in
  let need = (* a leading ident/number factorizes iff at level 0 *) lev <> 0 in
  aux need symbols

let rec find_symbols c_current c_next c_last = function
  | [] -> []
  | NonTerminal id :: sl ->
      let prec = if not (List.is_empty sl) then c_current else c_last in
      (id, prec) :: (find_symbols c_next c_next c_last sl)
  | Terminal s :: sl -> find_symbols c_next c_next c_last sl
  | Break n :: sl -> find_symbols c_current c_next c_last sl
  | SProdList (x,_) :: sl' ->
      (x,c_next)::(find_symbols c_next c_next c_last sl')

let border = function
  | (_,(ETConstr(_,_,(_,BorderProd (_,a))))) :: _ -> a
  | _ -> None

let recompute_assoc typs = let open Gramlib.Gramext in
  match border typs, border (List.rev typs) with
    | Some LeftA, Some RightA -> assert false
    | Some LeftA, _ -> Some LeftA
    | _, Some RightA -> Some RightA
    | _ -> None

(**************************************************************************)
(* Registration of syntax extensions (parsing/printing, no interpretation)*)

let pr_arg_level from (lev,typ) =
  let pplev = function
  | LevelLt n when Int.equal n from -> spc () ++ str "at next level"
  | LevelLe n -> spc () ++ str "at level " ++ int n
  | LevelLt n -> spc () ++ str "at level below " ++ int n
  | LevelSome -> mt () in
  Ppvernac.pr_set_entry_type (fun _ -> (*TO CHECK*) mt()) typ ++ pplev lev

let pr_level ntn (from,fromlevel,args) typs =
  (match from with InConstrEntry -> mt () | InCustomEntry s -> str "in " ++ str s ++ spc()) ++
  str "at level " ++ int fromlevel ++ spc () ++ str "with arguments" ++ spc() ++
  prlist_with_sep pr_comma (pr_arg_level fromlevel) (List.combine args typs)

let error_incompatible_level ntn oldprec oldtyps prec typs =
  user_err
    (str "Notation " ++ pr_notation ntn ++ str " is already defined" ++ spc() ++
    pr_level ntn oldprec oldtyps ++
    spc() ++ str "while it is now required to be" ++ spc() ++
    pr_level ntn prec typs ++ str ".")

let error_parsing_incompatible_level ntn ntn' oldprec oldtyps prec typs =
  user_err
    (str "Notation " ++ pr_notation ntn ++ str " relies on a parsing rule for " ++ pr_notation ntn' ++ spc() ++
    str " which is already defined" ++ spc() ++
    pr_level ntn oldprec oldtyps ++
    spc() ++ str "while it is now required to be" ++ spc() ++
    pr_level ntn prec typs ++ str ".")

let warn_incompatible_format =
  CWarnings.create ~name:"notation-incompatible-format" ~category:"parsing"
    (fun (specific,ntn) ->
       let head,scope = match specific with
       | None -> str "Notation", mt ()
       | Some LastLonelyNotation -> str "Lonely notation", mt ()
       | Some (NotationInScope sc) -> str "Notation", strbrk (" in scope " ^ sc) in
       head ++ spc () ++ pr_notation ntn ++
       strbrk " was already defined with a different format" ++ scope ++ str ".")

type syntax_extension = {
  synext_level : level;
  synext_nottyps : constr_entry_key list;
  synext_notgram : notation_grammar option;
  synext_notprint : generic_notation_printing_rules option;
}

type syntax_rules =
  | PrimTokenSyntax
  | SpecificSyntax of syntax_extension

let syntax_rules_iter f = function
  | PrimTokenSyntax -> ()
  | SpecificSyntax synext -> f synext

let check_reserved_format ntn rules rules' =
  try
    let { notation_printing_reserved = reserved; notation_printing_rules = generic_rules } = rules in
    if reserved &&
       (not (List.for_all2eq unparsing_eq rules'.notation_printing_unparsing generic_rules.notation_printing_unparsing)
       || rules'.notation_printing_extra <> generic_rules.notation_printing_extra)
    then
      warn_incompatible_format (None,ntn)
  with Not_found -> ()

let specific_format_to_declare (specific,ntn as specific_ntn) rules =
  try
    let specific_rules = Ppextend.find_specific_notation_printing_rule specific_ntn in
    if not (List.for_all2eq unparsing_eq rules.notation_printing_unparsing specific_rules.notation_printing_unparsing)
       || rules.notation_printing_extra <> specific_rules.notation_printing_extra then
      (warn_incompatible_format (Some specific,ntn); true)
    else false
  with Not_found -> true

type syntax_extension_obj =
  locality_flag * (notation * syntax_extension)

let check_and_extend_constr_grammar ntn rule =
  try
    let ntn_for_grammar = rule.notgram_notation in
    if notation_eq ntn ntn_for_grammar then raise Not_found;
    let prec = rule.notgram_level in
    let typs = rule.notgram_typs in
    let oldprec = Notation.level_of_notation ntn_for_grammar in
    let oldparsing =
      try
        Some (Notgram_ops.grammar_of_notation ntn_for_grammar)
      with Not_found -> None
    in
    let oldtyps = Notgram_ops.subentries_of_notation ntn_for_grammar in
    if not (Notation.level_eq prec oldprec) && oldparsing <> None then
      error_parsing_incompatible_level ntn ntn_for_grammar oldprec oldtyps prec typs;
    if oldparsing = None then raise Not_found
  with Not_found ->
    Egramcoq.extend_constr_grammar rule

let cache_one_syntax_extension (ntn,synext) =
  let prec = synext.synext_level in
  (* Check and ensure that the level and the precomputed parsing rule is declared *)
  let oldparsing =
    try
      let oldprec = Notation.level_of_notation ntn in
      let oldparsing =
        try
          Some (Notgram_ops.grammar_of_notation ntn)
        with Not_found -> None
      in
      let oldtyps = Notgram_ops.subentries_of_notation ntn in
      if not (Notation.level_eq prec oldprec) && (oldparsing <> None || synext.synext_notgram = None) then
        error_incompatible_level ntn oldprec oldtyps prec synext.synext_nottyps;
      oldparsing
    with Not_found ->
      (* Declare the level and the precomputed parsing rule *)
      let () = Notation.declare_notation_level ntn prec in
      let () = Notgram_ops.declare_notation_subentries ntn synext.synext_nottyps in
      let () = Option.iter (Notgram_ops.declare_notation_grammar ntn) synext.synext_notgram in
      None in
  (* Declare the parsing rule *)
  begin match oldparsing, synext.synext_notgram with
  | None, Some grams -> List.iter (check_and_extend_constr_grammar ntn) grams
  | _ -> (* The grammars rules are canonically derived from the string and the precedence*) ()
  end;
  (* Printing *)
  Option.iter (declare_generic_notation_printing_rules ntn) synext.synext_notprint

let cache_syntax_extension (_, (_, sy)) =
  cache_one_syntax_extension sy

let subst_syntax_extension (subst, (local, (ntn, synext))) =
  (local, (ntn, synext))

let classify_syntax_definition (local, _ as o) =
  if local then Dispose else Substitute o

let open_syntax_extension i o =
  if Int.equal i 1 then cache_syntax_extension o

let inSyntaxExtension : syntax_extension_obj -> obj =
  declare_object {(default_object "SYNTAX-EXTENSION") with
       open_function = simple_open open_syntax_extension;
       cache_function = cache_syntax_extension;
       subst_function = subst_syntax_extension;
       classify_function = classify_syntax_definition}

(**************************************************************************)
(* Precedences                                                            *)

(* Interpreting user-provided modifiers *)

(* XXX: We could move this to the parser itself *)

module NotationMods = struct

type notation_modifier = {
  assoc         : Gramlib.Gramext.g_assoc option;
  level         : int option;
  etyps         : (Id.t * simple_constr_prod_entry_key) list;

  (* common to syn_data below *)
  format        : lstring option;
  extra         : (string * string) list;
}

let default = {
  assoc         = None;
  level         = None;
  etyps         = [];
  format        = None;
  extra         = [];
}

end

(* To be turned into a fatal warning in 8.14 *)
let warn_deprecated_ident_entry =
  CWarnings.create ~name:"deprecated-ident-entry" ~category:"deprecated"
         (fun () -> strbrk "grammar entry \"ident\" permitted \"_\" in addition to proper identifiers; this use is deprecated and its meaning will change in the future; use \"name\" instead.")

let interp_modifiers entry modl = let open NotationMods in
  let rec interp subtyps acc = function
  | [] -> subtyps, acc
  | CAst.{loc;v} :: l -> match v with
    | SetEntryType (s,typ) ->
        let id = Id.of_string s in
        if Id.List.mem_assoc id acc.etyps then
          user_err ?loc ~hdr:"Metasyntax.interp_modifiers"
            (str s ++ str " is already assigned to an entry or constr level.");
        interp subtyps { acc with etyps = (id,typ) :: acc.etyps; } l
    | SetItemLevel ([],bko,n) ->
        interp subtyps acc l
    | SetItemLevel (s::idl,bko,n) ->
        let id = Id.of_string s in
        if Id.List.mem_assoc id acc.etyps then
          user_err ?loc ~hdr:"Metasyntax.interp_modifiers"
            (str s ++ str " is already assigned to an entry or constr level.");
        interp ((id,bko,n)::subtyps) acc ((CAst.make ?loc @@ SetItemLevel (idl,bko,n))::l)
    | SetLevel n ->
        (match entry with
        | InCustomEntry s ->
          if acc.level <> None then
            user_err ?loc (str ("isolated \"at level " ^ string_of_int n ^ "\" unexpected."))
          else
            user_err ?loc (str ("use \"in custom " ^ s ^ " at level " ^ string_of_int n ^
                         "\"") ++ spc () ++ str "rather than" ++ spc () ++
                         str ("\"at level " ^ string_of_int n ^ "\"") ++
                         spc () ++ str "isolated.")
        | InConstrEntry ->
          if acc.level <> None then
            user_err ?loc (str "A level is already assigned.");
          interp subtyps { acc with level = Some n; } l)
    | SetCustomEntry (s,Some n) ->
        (* Note: name of entry already registered in interp_non_syntax_modifiers *)
        if acc.level <> None then
          user_err ?loc (str ("isolated \"at level " ^ string_of_int (Option.get acc.level) ^ "\" unexpected."));
        interp subtyps { acc with level = Some n } l
    | SetAssoc a ->
        if not (Option.is_empty acc.assoc) then user_err ?loc Pp.(str "An associativity is given more than once.");
        interp subtyps { acc with assoc = Some a; } l
    | SetOnlyParsing | SetOnlyPrinting | SetCustomEntry (_,None) | SetFormat _ | SetItemScope _ ->
        (* interpreted in interp_non_syntax_modifiers *)
        assert false
  in
  let subtyps, mods = interp [] default modl in
  (* interpret item levels wrt to main entry *)
  let extra_etyps = List.map (fun (id,bko,n) -> (id,ETConstr (entry,bko,n))) subtyps in
  (* Temporary hack: "ETName false" (i.e. "ident" in deprecation phase) means "ETIdent" for custom entries *)
  let mods =
    { mods with etyps = List.map (function
        | (id,ETName false) ->
           if entry = InConstrEntry then (warn_deprecated_ident_entry (); (id,ETName true))
           else (id,ETIdent)
        | x -> x) mods.etyps } in
  { mods with etyps = extra_etyps@mods.etyps }

let check_useless_entry_types recvars mainvars etyps =
  let vars = let (l1,l2) = List.split recvars in l1@l2@mainvars in
  match List.filter (fun (x,etyp) -> not (List.mem x vars)) etyps with
  | (x,_)::_ -> user_err ~hdr:"Metasyntax.check_useless_entry_types"
                  (Id.print x ++ str " is unbound in the notation.")
  | _ -> ()

type notation_main_data = {
  onlyparsing  : bool;
  onlyprinting : bool;
  deprecation  : Deprecation.t option;
  entry        : notation_entry;
  format       : unparsing Loc.located list option;
  extra        : (string * string) list;
  itemscopes  : (Id.t * scope_name) list;
}

let warn_only_parsing_reserved_notation =
  CWarnings.create ~name:"irrelevant-reserved-notation-only-parsing" ~category:"parsing"
    (fun () -> strbrk "The only parsing modifier has no effect in Reserved Notation.")

let warn_only_parsing_discarded_format =
  CWarnings.create ~name:"discarded-format-only-parsing" ~category:"parsing"
    (fun () -> strbrk "The format modifier has no effect for only-parsing notations.")

let error_onlyparsing_onlyprinting ?loc =
  user_err ?loc (str "A notation cannot be both \"only printing\" and \"only parsing\".")

let set_onlyparsing ?loc ~reserved main_data =
  if reserved then
    (warn_only_parsing_reserved_notation ?loc ();
     main_data)
  else
    (if main_data.onlyparsing then user_err ?loc (str "\"only parsing\" is given more than once.");
     if main_data.onlyprinting then error_onlyparsing_onlyprinting ?loc;
     { main_data with onlyparsing = true })

let set_onlyprinting ?loc main_data =
  if main_data.onlyprinting then user_err ?loc (str "\"only printing\" is given more than once.");
  if main_data.onlyparsing then error_onlyparsing_onlyprinting ?loc;
  { main_data with onlyprinting = true }

let set_custom_entry ?loc main_data entry' =
  match main_data.entry with
  | InConstrEntry -> { main_data with entry = InCustomEntry entry' }
  | _ -> user_err ?loc (str "\"in custom\" is given more than once.")

let warn_irrelevant_format =
  CWarnings.create ~name:"irrelevant-format-only-parsing" ~category:"parsing"
    (fun () -> str "The format modifier is irrelevant for only-parsing rules.")

let set_format ?loc main_data format =
  if not (Option.is_empty main_data.format) then user_err ?loc Pp.(str "A format is given more than once.");
  let format = if main_data.onlyparsing then (warn_irrelevant_format ?loc (); None) else Some (parse_format format) in
  { main_data with format }

let set_extra_format ?loc main_data (k,s) =
  if List.mem_assoc k main_data.extra then user_err ?loc Pp.(str "A format for " ++ str k ++ str " is given more than once.");
  let extra = if main_data.onlyparsing then (warn_irrelevant_format ?loc (); main_data.extra) else (k,s.CAst.v)::main_data.extra in
  { main_data with extra }

let set_item_scope ?loc main_data ids sc =
  let itemscopes = List.map (fun id -> (Id.of_string id,sc)) ids @ main_data.itemscopes in
  match List.duplicates (fun (id1,_) (id2,_) -> Id.equal id1 id2) itemscopes  with
  | (id,_)::_ -> user_err ?loc (str "Notation scope for argument " ++ Id.print id ++ str " can be specified only once.")
  | [] -> { main_data with itemscopes }

let interp_non_syntax_modifiers ~reserved ~infix ~syndef deprecation mods =
  let set (main_data,rest) = CAst.with_loc_val (fun ?loc -> function
    | SetOnlyParsing ->
       if not (Option.is_empty main_data.format && List.is_empty main_data.extra) then
         (warn_only_parsing_discarded_format ?loc (); (main_data, rest))
       else
         (set_onlyparsing ?loc ~reserved main_data,rest)
    | SetOnlyPrinting when not syndef -> (set_onlyprinting ?loc main_data,rest)
    | SetCustomEntry (entry,None) when not syndef -> (set_custom_entry ?loc main_data entry,rest)
    | SetCustomEntry (entry,Some _) as x when not syndef -> (set_custom_entry main_data entry,CAst.make ?loc x :: rest)
    | SetEntryType _ when infix -> user_err ?loc Pp.(str "Unexpected entry type in infix notation.")
    | SetItemLevel _ when infix -> user_err ?loc Pp.(str "Unexpected entry level in infix notation.")
    | SetFormat (TextFormat s) when not syndef -> (set_format ?loc main_data s, rest)
    | SetFormat (ExtraFormat (k,s)) when not syndef -> (set_extra_format ?loc main_data (k,s), rest)
    | SetItemScope (ids,sc) -> (set_item_scope ?loc main_data ids sc, rest)
    | modif -> (main_data,(CAst.make ?loc modif)::rest))
  in
  let main_data =
    {
      onlyparsing = false; onlyprinting = false; deprecation;
      entry = InConstrEntry; format = None; extra = []; itemscopes = []
    }
  in
  List.fold_left set (main_data,[]) mods

(* Check if an interpretation can be used for printing a cases printing *)
let has_no_binders_type =
  List.for_all (fun (_,(_,typ)) ->
  match typ with
  | NtnTypeBinder _ | NtnTypeBinderList -> false
  | NtnTypeConstr | NtnTypeConstrList -> true)

(* Compute precedences from modifiers (or find default ones) *)

let set_entry_type from n etyps (x,typ) =
  let make_lev n s = match typ with
    | BorderProd _ -> NumLevel n
    | InternalProd -> DefaultLevel in
  let typ = try
    match List.assoc x etyps, typ with
      | ETConstr (s,bko,DefaultLevel), _ ->
         if notation_entry_eq from s then ETConstr (s,bko,(make_lev n s,typ))
         else ETConstr (s,bko,(DefaultLevel,typ))
      | ETConstr (s,bko,n), BorderProd (left,_) ->
          ETConstr (s,bko,(n,BorderProd (left,None)))
      | ETConstr (s,bko,n), InternalProd ->
          ETConstr (s,bko,(n,InternalProd))
      | ETPattern (b,n), _ -> ETPattern (b,n)
      | (ETIdent | ETName _ | ETBigint | ETGlobal | ETBinder _ as x), _ -> x
    with Not_found ->
      ETConstr (from,None,(make_lev n from,typ))
  in (x,typ)

let join_auxiliary_recursive_types recvars etyps =
  List.fold_right (fun (x,y) typs ->
    let xtyp = try Some (List.assoc x etyps) with Not_found -> None in
    let ytyp = try Some (List.assoc y etyps) with Not_found -> None in
    match xtyp,ytyp with
    | None, None -> typs
    | Some _, None -> typs
    | None, Some ytyp -> (x,ytyp)::typs
    | Some xtyp, Some ytyp when (=) xtyp ytyp -> typs (* FIXME *)
    | Some xtyp, Some ytyp ->
        user_err
          (strbrk "In " ++ Id.print x ++ str " .. " ++ Id.print y ++
           strbrk ", both ends have incompatible types."))
    recvars etyps

let internalization_type_of_entry_type = function
  | ETBinder _ -> NtnInternTypeOnlyBinder
  | ETConstr _ | ETBigint | ETGlobal
  | ETIdent | ETName _ | ETPattern _ -> NtnInternTypeAny None

let make_internalization_vars recvars maintyps =
  let maintyps = List.map (on_snd internalization_type_of_entry_type) maintyps in
  let extratyps = List.map (fun (x,y) -> (y,List.assoc x maintyps)) recvars in
  maintyps @ extratyps

let make_interpretation_type isrec isonlybinding default_if_binding = function
  (* Parsed as constr list *)
  | ETConstr (_,None,_) when isrec -> NtnTypeConstrList
  (* Parsed as constr, but interpreted as a binder *)
  | ETConstr (_,Some bk,_) -> NtnTypeBinder (NtnBinderParsedAsConstr bk)
  | ETConstr (_,None,_) when isonlybinding -> NtnTypeBinder (NtnBinderParsedAsConstr default_if_binding)
  (* Parsed as constr, interpreted as constr *)
  | ETConstr (_,None,_) -> NtnTypeConstr
  (* Others *)
  | ETIdent -> NtnTypeBinder NtnParsedAsIdent
  | ETName _ -> NtnTypeBinder NtnParsedAsName
  | ETPattern (ppstrict,_) -> NtnTypeBinder (NtnParsedAsPattern ppstrict) (* Parsed as ident/pattern, primarily interpreted as binder; maybe strict at printing *)
  | ETBigint | ETGlobal -> NtnTypeConstr
  | ETBinder _ ->
     if isrec then NtnTypeBinderList
     else NtnTypeBinder NtnParsedAsBinder

let subentry_of_constr_prod_entry from_level = function
  (* Specific 8.2 approximation *)
  | ETConstr (InCustomEntry s,_,x) ->
    let n = match fst (precedence_of_position_and_level from_level x) with
     | LevelLt n -> n-1
     | LevelLe n -> n
     | LevelSome -> max_int in
    InCustomEntryLevel (s,n)
  (* level and use of parentheses for coercion is hard-wired for "constr";
     we don't remember the level *)
  | ETConstr (InConstrEntry,_,_) -> InConstrEntrySomeLevel
  | _ -> InConstrEntrySomeLevel

let make_interpretation_vars
  (* For binders, default is to parse only as an ident *) ?(default_if_binding=AsName)
   recvars level allvars typs =
  let eq_subscope (sc1, l1) (sc2, l2) =
    Option.equal String.equal sc1 sc2 &&
    List.equal String.equal l1 l2
  in
  let check (x, y) =
    let (_,scope1) = Id.Map.find x allvars in
    let (_,scope2) = Id.Map.find y allvars in
    if not (eq_subscope scope1 scope2) then error_not_same_scope x y
  in
  let () = List.iter check recvars in
  let useless_recvars = List.map snd recvars in
  let mainvars =
    Id.Map.filter (fun x _ -> not (Id.List.mem x useless_recvars)) allvars in
  Id.Map.mapi (fun x (isonlybinding, sc) ->
    let typ = Id.List.assoc x typs in
    ((subentry_of_constr_prod_entry level typ,sc),
     make_interpretation_type (Id.List.mem_assoc x recvars) isonlybinding default_if_binding typ)) mainvars

let check_rule_productivity l =
  if List.for_all (function NonTerminal _ | Break _ -> true | _ -> false) l then
    user_err Pp.(str "A notation must include at least one symbol.");
  if (match l with SProdList _ :: _ -> true | _ -> false) then
    user_err Pp.(str "A recursive notation must start with at least one symbol.")

let warn_notation_bound_to_variable =
  CWarnings.create ~name:"notation-bound-to-variable" ~category:"parsing"
         (fun () ->
          strbrk "This notation will not be used for printing as it is bound to a single variable.")

let warn_non_reversible_notation =
  CWarnings.create ~name:"non-reversible-notation" ~category:"parsing"
         (function
          | APrioriReversible -> assert false
          | HasLtac ->
             strbrk "This notation contains Ltac expressions: it will not be used for printing."
          | NonInjective ids ->
             let n = List.length ids in
             strbrk (String.plural n "Variable") ++ spc () ++ pr_enum Id.print ids ++ spc () ++
             strbrk (if n > 1 then "do" else "does") ++
             str " not occur in the right-hand side." ++ spc() ++
             strbrk "The notation will not be used for printing as it is not reversible.")

let is_coercion level typs =
  match level, typs with
  | Some (custom,n,_), [_,e] ->
     (match e, custom with
     | ETConstr _, _ ->
         let customkey = make_notation_entry_level custom n in
         let subentry = subentry_of_constr_prod_entry n e in
         if notation_entry_level_eq subentry customkey then None
         else Some (IsEntryCoercion subentry)
     | ETGlobal, InCustomEntry s -> Some (IsEntryGlobal (s,n))
     | ETIdent, InCustomEntry s -> Some (IsEntryIdent (s,n))
     | _ -> None)
  | Some _, _ -> assert false
  | None, _ -> None

let printability level typs onlyparsing reversibility = function
| NVar _ when reversibility = APrioriReversible ->
  let coe = is_coercion level typs in
  if not onlyparsing && coe = None then
    warn_notation_bound_to_variable ();
  true, coe
| _ ->
   (if not onlyparsing && reversibility <> APrioriReversible then
     (warn_non_reversible_notation reversibility; true)
    else onlyparsing),None

let find_precedence custom lev etyps symbols onlyprint =
  let first_symbol =
    let rec aux = function
      | Break _ :: t -> aux t
      | h :: t -> Some h
      | [] -> None in
    aux symbols in
  let last_is_terminal () =
    let rec aux b = function
      | Break _ :: t -> aux b t
      | Terminal _ :: t -> aux true t
      | _ :: t -> aux false t
      | [] -> b in
    aux false symbols in
  match first_symbol with
  | None -> [],0
  | Some (NonTerminal x) ->
      let test () =
        if onlyprint then
          if Option.is_empty lev then
            user_err Pp.(str "Explicit level needed in only-printing mode when the level of the leftmost non-terminal is given.")
          else [],Option.get lev
        else
          user_err Pp.(str "The level of the leftmost non-terminal cannot be changed.") in
      (try match List.assoc x etyps, custom with
        | ETConstr (s,_,(NumLevel _ | NextLevel)), s' when s = s' -> test ()
        | (ETIdent | ETName _ | ETBigint | ETGlobal), _ ->
            begin match lev with
            | None ->
              ([fun () -> Flags.if_verbose (Feedback.msg_info ?loc:None) (strbrk "Setting notation at level 0.")],0)
            | Some 0 ->
              ([],0)
            | _ ->
              user_err Pp.(str "A notation starting with an atomic expression must be at level 0.")
            end
        | (ETPattern _ | ETBinder _), InConstrEntry when not onlyprint ->
            (* Don't know exactly if we can make sense of this case *)
            user_err Pp.(str "Binders or patterns not supported in leftmost position.")
        | (ETPattern _ | ETBinder _ | ETConstr _), _ ->
            (* Give a default ? *)
            if Option.is_empty lev then
              user_err Pp.(str "Need an explicit level.")
            else [],Option.get lev
      with Not_found ->
        if Option.is_empty lev then
          user_err Pp.(str "A left-recursive notation must have an explicit level.")
        else [],Option.get lev)
  | Some (Terminal _) when last_is_terminal () ->
      if Option.is_empty lev then
        ([fun () -> Flags.if_verbose (Feedback.msg_info ?loc:None) (strbrk "Setting notation at level 0.")], 0)
      else [],Option.get lev
  | Some _ ->
      if Option.is_empty lev then user_err Pp.(str "Cannot determine the level.");
      [],Option.get lev

let check_curly_brackets_notation_exists () =
  try let _ = Notation.level_of_notation (InConstrEntry,"{ _ }") in ()
  with Not_found ->
    user_err Pp.(str "Notations involving patterns of the form \"{ _ }\" are treated \n\
specially and require that the notation \"{ _ }\" is already reserved.")

(* Remove patterns of the form "{ _ }", unless it is the "{ _ }" notation *)
let remove_curly_brackets l =
  let rec skip_break acc = function
    | Break _ as br :: l -> skip_break (br::acc) l
    | l -> List.rev acc, l in
  let rec aux deb = function
  | [] -> []
  | Terminal "{" as t1 :: l ->
      let br,next = skip_break [] l in
      (match next with
        | NonTerminal _ as x :: l' ->
            let br',next' = skip_break [] l' in
            (match next' with
              | Terminal "}" as t2 :: l'' ->
                  if deb && List.is_empty l'' then [t1;x;t2] else begin
                    check_curly_brackets_notation_exists ();
                    x :: aux false l''
                  end
              | l1 -> t1 :: br @ x :: br' @ aux false l1)
        | l0 -> t1 :: aux false l0)
  | x :: l -> x :: aux false l
  in aux true l

let has_implicit_format symbols =
  List.exists (function Break _ -> true | _ -> false) symbols

(* Because of the special treatment for { }, the grammar rule sent
   to the parser may be different than what the user sees; e.g. for
   "{ A } + { B }", it is "A + B" which is sent to the parser *)
type syn_pa_data = {
    ntn_for_grammar : notation;
    prec_for_grammar : level;
    typs_for_grammar : constr_entry_key list;
    need_squash : bool;
  }

module SynData = struct

  type subentry_types = (Id.t * constr_entry_key) list

  (* XXX: Document *)
  type syn_data = {

    (* XXX: Callback to printing, must remove *)
    msgs          : (unit -> unit) list;

    (* Notation data for parsing *)
    level         : level;
    subentries    : subentry_types;
    pa_syntax_data : subentry_types * symbol list;
    pp_syntax_data : subentry_types * symbol list;
    not_data      : syn_pa_data;
  }

end

let find_subentry_types from n assoc etyps symbols =
  let typs =
    find_symbols
      (BorderProd(Left,assoc))
      (InternalProd)
      (BorderProd(Right,assoc))
      symbols in
  let sy_typs = List.map (set_entry_type from n etyps) typs in
  let prec = List.map (assoc_of_type from n) sy_typs in
  sy_typs, prec

let check_locality_compatibility local custom i_typs =
  if not local then
    let subcustom = List.map_filter (function _,ETConstr (InCustomEntry s,_,_) -> Some s | _ -> None) i_typs in
    let allcustoms = match custom with InCustomEntry s -> s::subcustom | _ -> subcustom in
    List.iter (fun s ->
        if Egramcoq.locality_of_custom_entry s then
          user_err (strbrk "Notation has to be declared local as it depends on custom entry " ++ str s ++
                    strbrk " which is local."))
      (List.uniquize allcustoms)

let compute_syntax_data ~local main_data notation_symbols ntn mods =
  let open SynData in
  let open NotationMods in
  if main_data.itemscopes <> [] then user_err (str "General notations don't support 'in scope'.");
  let {recvars;mainvars;symbols} = notation_symbols in
  let assoc = Option.append mods.assoc (Some Gramlib.Gramext.NonA) in
  let _ = check_useless_entry_types recvars mainvars mods.etyps in

  (* Notations for interp and grammar  *)
  let msgs,n = find_precedence main_data.entry mods.level mods.etyps symbols main_data.onlyprinting in
  let symbols_for_grammar =
    if main_data.entry = InConstrEntry then remove_curly_brackets symbols else symbols in
  let need_squash = not (List.equal Notation.symbol_eq symbols symbols_for_grammar) in
  let ntn_for_grammar = if need_squash then make_notation_key main_data.entry symbols_for_grammar else ntn in
  if main_data.entry = InConstrEntry && not main_data.onlyprinting then check_rule_productivity symbols_for_grammar;
  (* To globalize... *)
  let etyps = join_auxiliary_recursive_types recvars mods.etyps in
  let sy_typs, prec =
    find_subentry_types main_data.entry n assoc etyps symbols in
  let sy_typs_for_grammar, prec_for_grammar =
    if need_squash then
      find_subentry_types main_data.entry n assoc etyps symbols_for_grammar
    else
      sy_typs, prec in
  check_locality_compatibility local main_data.entry sy_typs;
  let pa_sy_data = (sy_typs_for_grammar,symbols_for_grammar) in
  let pp_sy_data = (sy_typs,symbols) in
  let sy_fulldata = {
      ntn_for_grammar;
      prec_for_grammar = (main_data.entry,n,prec_for_grammar);
      typs_for_grammar = List.map snd sy_typs_for_grammar;
      need_squash
    } in

  (* Return relevant data for interpretation and for parsing/printing *)
  {
    msgs;
    level  = (main_data.entry,n,prec);
    subentries = sy_typs;
    pa_syntax_data = pa_sy_data;
    pp_syntax_data = pp_sy_data;
    not_data    = sy_fulldata;
  }

(**********************************************************************)
(* Registration of notations interpretation                            *)

type notation_obj = {
  notobj_local : bool;
  notobj_scope : scope_name option;
  notobj_interp : interpretation;
  notobj_coercion : entry_coercion_kind option;
  notobj_use : notation_use option;
  notobj_deprecation : Deprecation.t option;
  notobj_notation : notation * notation_location;
  notobj_specific_pp_rules : notation_printing_rules option;
  notobj_also_in_cases_pattern : bool;
}

let load_notation_common silently_define_scope_if_undefined _ (_, nobj) =
  (* When the default shall be to require that a scope already exists *)
  (* the call to ensure_scope will have to be removed *)
  if silently_define_scope_if_undefined then
    (* Don't warn if the scope is not defined: *)
    (* there was already a warning at "cache" time *)
    Option.iter Notation.declare_scope nobj.notobj_scope
  else
    Option.iter Notation.ensure_scope nobj.notobj_scope

let load_notation =
  load_notation_common true

let open_notation i (_, nobj) =
  if Int.equal i 1 then begin
    let scope = nobj.notobj_scope in
    let (ntn, df) = nobj.notobj_notation in
    let pat = nobj.notobj_interp in
    let deprecation = nobj.notobj_deprecation in
    let scope = match scope with None -> LastLonelyNotation | Some sc -> NotationInScope sc in
    let also_in_cases_pattern = nobj.notobj_also_in_cases_pattern in
    (* Declare the notation *)
    (match nobj.notobj_use with
    | Some use -> Notation.declare_notation (scope,ntn) pat df ~use ~also_in_cases_pattern nobj.notobj_coercion deprecation
    | None -> ());
    (* Declare specific format if any *)
    (match nobj.notobj_specific_pp_rules with
    | Some pp_sy ->
      if specific_format_to_declare (scope,ntn) pp_sy then
        Ppextend.declare_specific_notation_printing_rules (scope,ntn) pp_sy
    | None -> ())
  end

let cache_notation o =
  load_notation_common false 1 o;
  open_notation 1 o

let subst_notation (subst, nobj) =
  { nobj with notobj_interp = subst_interpretation subst nobj.notobj_interp; }

let classify_notation nobj =
  if nobj.notobj_local then Dispose else Substitute nobj

let inNotation : notation_obj -> obj =
  declare_object {(default_object "NOTATION") with
       open_function = simple_open open_notation;
       cache_function = cache_notation;
       subst_function = subst_notation;
       load_function = load_notation;
       classify_function = classify_notation}

(**********************************************************************)

let with_lib_stk_protection f x =
  let fs = Lib.freeze () in
  try let a = f x in Lib.unfreeze fs; a
  with reraise ->
    let reraise = Exninfo.capture reraise in
    let () = Lib.unfreeze fs in
    Exninfo.iraise reraise

let with_syntax_protection f x =
  with_lib_stk_protection
    (Pcoq.with_grammar_rule_protection
       (with_notation_protection f)) x

(**********************************************************************)
(* Recovering existing syntax                                         *)

exception NoSyntaxRule

let recover_notation_syntax ntn =
  try
    let prec = Notation.level_of_notation ntn in
    let pa_typs = Notgram_ops.subentries_of_notation ntn in
    let pa_rule = try Some (Notgram_ops.grammar_of_notation ntn) with Not_found -> None in
    let pp_rule = try Some (find_generic_notation_printing_rule ntn) with Not_found -> None in
    {
      synext_level = prec;
      synext_nottyps = pa_typs;
      synext_notgram = pa_rule;
      synext_notprint = pp_rule;
    }
  with Not_found ->
    raise NoSyntaxRule

let recover_squash_syntax sy =
  let sq = recover_notation_syntax (InConstrEntry,"{ _ }") in
  match sq.synext_notgram with
  | Some gram -> sy :: gram
  | None -> raise NoSyntaxRule

(**********************************************************************)
(* Main entry point for building parsing and printing rules           *)

let make_pa_rule (typs,symbols) parsing_data =
  let { ntn_for_grammar; prec_for_grammar; typs_for_grammar; need_squash } = parsing_data in
  let assoc = recompute_assoc typs in
  let prod = make_production prec_for_grammar typs symbols in
  let sy = {
    notgram_level = prec_for_grammar;
    notgram_assoc = assoc;
    notgram_notation = ntn_for_grammar;
    notgram_prods = prod;
    notgram_typs = typs_for_grammar;
  } in
  (* By construction, the rule for "{ _ }" is declared, but we need to
     redeclare it because the file where it is declared needs not be open
     when the current file opens (especially in presence of -nois) *)
  if need_squash then recover_squash_syntax sy else [sy]

let make_pp_rule level (typs,symbols) fmt =
  match fmt with
  | None ->
     let hunks = make_hunks typs symbols level in
     if List.exists (function _,(UnpCut (PpBrk _) | UnpListMetaVar _) -> true | _ -> false) hunks then
       [UnpBox (PpHOVB 0,hunks)]
     else
       (* Optimization to work around what seems an ocaml Format bug (see Mantis #7804/#7807) *)
       List.map snd hunks (* drop locations which are dummy *)
  | Some fmt ->
     hunks_of_format (level, List.split typs) (symbols, fmt)

let make_parsing_rules main_data (sd : SynData.syn_data) =
  let open SynData in
  if main_data.onlyprinting then None
  else Some (make_pa_rule sd.pa_syntax_data sd.not_data)

let make_generic_printing_rules reserved main_data ntn sd =
  let open SynData in
  let custom,level,_ = sd.level in
  let make_rule rule =
    {
      notation_printing_reserved = reserved;
      notation_printing_rules =
        {
          notation_printing_unparsing = rule;
          notation_printing_level = level;
          notation_printing_extra  = main_data.extra;
        }
    }
  in
  try
    let rules = (Ppextend.find_generic_notation_printing_rule ntn) in
    match main_data.format with
    | None when not (has_implicit_format (snd sd.pp_syntax_data)) ->
      (* No intent to define a format, we reuse the existing generic rules *)
      Some rules
    | _ ->
      let rules' = make_rule (make_pp_rule level sd.pp_syntax_data main_data.format) in
      check_reserved_format ntn rules rules'.notation_printing_rules;
      Some rules'
  with Not_found ->
    Some (make_rule (make_pp_rule level sd.pp_syntax_data main_data.format))

let make_syntax_rules reserved main_data ntn sd =
  let open SynData in
  (* Prepare the parsing and printing rules *)
  let pa_rules = make_parsing_rules main_data sd in
  let pp_rules = make_generic_printing_rules reserved main_data ntn sd in
  {
    synext_level    = sd.level;
    synext_nottyps = List.map snd sd.subentries;
    synext_notgram  = pa_rules;
    synext_notprint = pp_rules;
  }

(**********************************************************************)
(* Main entry point for building specific printing rules              *)

let merge_extra extra1 extra2 =
  List.fold_left (fun extras (k,s) -> (k,s) :: List.remove_assoc k extras)
    extra1 extra2

let make_specific_printing_rules etyps symbols level pp_rule (format,new_extra) =
  match level with
  | None -> None
  | Some (_,level,_) ->
  let old_extra = match pp_rule with Some { notation_printing_rules = { notation_printing_extra } } -> notation_printing_extra | None -> [] in
  match format, new_extra, pp_rule with
    | None, [], Some _ when not (has_implicit_format symbols) -> None
    | _ ->
       Some
         {
           notation_printing_unparsing = make_pp_rule level (etyps,symbols) format;
           notation_printing_level = level;
           notation_printing_extra = merge_extra old_extra new_extra;
         }

(**********************************************************************)
(* Miscellaneous                                                      *)

let warn_unused_interpretation =
  CWarnings.create ~name:"unused-notation" ~category:"parsing"
         (fun b ->
          strbrk "interpretation is used neither for printing nor for parsing, " ++
          (if b then strbrk "the declaration could be replaced by \"Reserved Notation\"."
          else strbrk "the declaration could be removed."))

let make_use reserved onlyparse onlyprint =
  match onlyparse, onlyprint with
  | false, false -> Some ParsingAndPrinting
  | true, false -> Some OnlyParsing
  | false, true -> Some OnlyPrinting
  | true, true -> warn_unused_interpretation reserved; None

(**********************************************************************)
(* Main functions about notations                                     *)

let to_map l =
  let fold accu (x, v) = Id.Map.add x v accu in
  List.fold_left fold Id.Map.empty l

let make_notation_interpretation ~local main_data notation_symbols ntn syntax_rules df env ?(impls=empty_internalization_env) c scope =
  let {recvars;mainvars;symbols} = notation_symbols in
  (* Recover types of variables and pa/pp rules; redeclare them if needed *)
  let level, i_typs, main_data, sy_pp_rules =
    match syntax_rules with
    | PrimTokenSyntax -> None, [], main_data, None
    | SpecificSyntax sy ->
    (* If the only printing flag has been explicitly requested, put it back *)
    let main_data = { main_data with onlyprinting = main_data.onlyprinting || sy.synext_notgram = None } in
    Some sy.synext_level, List.combine mainvars sy.synext_nottyps, main_data, sy.synext_notprint
  in
  (* Declare interpretation *)
  let sy_pp_rules = make_specific_printing_rules i_typs symbols level sy_pp_rules (main_data.format, main_data.extra) in
  let path = (Lib.library_dp(), Lib.current_dirpath true) in
  let df' = ntn, (path,df) in
  let i_vars = make_internalization_vars recvars i_typs in
  let nenv = {
    ninterp_var_type = to_map i_vars;
    ninterp_rec_vars = to_map recvars;
  } in
  let (acvars, ac, reversibility) = interp_notation_constr env ~impls nenv c in
  let plevel = match level with Some (from,level,l) -> level | None (* numeral: irrelevant )*) -> 0 in
  let interp = make_interpretation_vars recvars plevel acvars i_typs in
  let map (x, _) = try Some (x, Id.Map.find x interp) with Not_found -> None in
  let vars = List.map_filter map i_vars in (* Order of elements is important here! *)
  let also_in_cases_pattern = has_no_binders_type vars in
  let onlyparsing,coe = printability level i_typs main_data.onlyparsing reversibility ac in
  let main_data = { main_data with onlyparsing } in
  let use = make_use false onlyparsing main_data.onlyprinting in
  {
    notobj_local = local;
    notobj_scope = scope;
    notobj_use = use;
    notobj_interp = (vars, ac);
    notobj_coercion = coe;
    notobj_deprecation = main_data.deprecation;
    notobj_notation = df';
    notobj_specific_pp_rules = sy_pp_rules;
    notobj_also_in_cases_pattern = also_in_cases_pattern;
  }

(* Notations without interpretation (Reserved Notation) *)

let add_reserved_notation ~local ~infix ({CAst.loc;v=df},mods) =
  let open SynData in
  let (main_data,mods) = interp_non_syntax_modifiers ~reserved:true ~infix ~syndef:false None mods in
  let mods = interp_modifiers main_data.entry mods in
  let notation_symbols, isnumeral = analyze_notation_tokens ~onlyprinting:main_data.onlyprinting ~infix main_data.entry df in
  let notation_symbols = if infix then adjust_reserved_infix_notation notation_symbols else notation_symbols in
  let ntn = make_notation_key main_data.entry notation_symbols.symbols in
  if isnumeral then user_err ?loc (str "Notations for numbers are primitive and need not be reserved.");
  let sd = compute_syntax_data ~local main_data notation_symbols ntn mods in
  let synext = make_syntax_rules true main_data ntn sd in
  List.iter (fun f -> f ()) sd.msgs;
  Lib.add_anonymous_leaf (inSyntaxExtension(local,(ntn,synext)))

(* Notations associated to a where clause *)

type where_decl_notation =
  decl_notation * notation_main_data * notation_symbols * notation * syntax_rules

let prepare_where_notation decl_ntn =
  let
    { decl_ntn_string = { CAst.loc ; v = df };
      decl_ntn_interp = c;
      decl_ntn_modifiers = modifiers;
      decl_ntn_scope = sc;
    } = decl_ntn in
  let (main_data,mods) = interp_non_syntax_modifiers ~reserved:false ~infix:false ~syndef:false None modifiers in
  match mods with
  | _::_ -> CErrors.user_err (str"Only modifiers not affecting parsing are supported here.")
  | [] ->
    let notation_symbols, isnumeral = analyze_notation_tokens ~onlyprinting:main_data.onlyprinting ~infix:false main_data.entry df in
    let ntn = make_notation_key main_data.entry notation_symbols.symbols in
    let syntax_rules =
      if isnumeral then PrimTokenSyntax else
      try SpecificSyntax (recover_notation_syntax ntn)
      with NoSyntaxRule ->
        user_err Pp.(str "Parsing rule for this notation has to be previously declared.") in
    (decl_ntn, main_data, notation_symbols, ntn, syntax_rules)

let add_notation_interpretation ~local env (decl_ntn, main_data, notation_symbols, ntn, syntax_rules) =
  let { decl_ntn_string = { CAst.loc ; v = df }; decl_ntn_interp = c; decl_ntn_scope = sc } = decl_ntn in
  let notation = make_notation_interpretation ~local main_data notation_symbols ntn syntax_rules df env c sc in
  syntax_rules_iter (fun sy -> Lib.add_anonymous_leaf (inSyntaxExtension (local,(ntn,sy)))) syntax_rules;
  Lib.add_anonymous_leaf (inNotation notation);
  Dumpglob.dump_notation (CAst.make ?loc ntn) sc true

(* interpreting a where clause *)
let set_notation_for_interpretation env impls (decl_ntn, main_data, notation_symbols, ntn, syntax_rules) =
  let { decl_ntn_string = { CAst.loc ; v = df }; decl_ntn_interp = c; decl_ntn_scope = sc } = decl_ntn in
  let notation = make_notation_interpretation ~local:true main_data notation_symbols ntn syntax_rules df env ~impls c sc in
  syntax_rules_iter (fun sy -> Lib.add_anonymous_leaf (inSyntaxExtension (true,(ntn,sy)))) syntax_rules;
  Lib.add_anonymous_leaf (inNotation notation);
  Option.iter (fun sc -> Notation.open_close_scope (false,true,sc)) sc

(* Main entry point for command Notation *)

let add_notation ~local ~infix deprecation env c ({CAst.loc;v=df},modifiers) sc =
  (* Extract the modifiers not affecting the parsing rule *)
  let (main_data,syntax_modifiers) = interp_non_syntax_modifiers ~reserved:false ~infix ~syndef:false deprecation modifiers in
  (* Extract the modifiers not affecting the parsing rule *)
  let notation_symbols, isnumeral = analyze_notation_tokens ~onlyprinting:main_data.onlyprinting ~infix main_data.entry df in
  (* Add variables on both sides if an infix notation *)
  let df, notation_symbols, c = if infix then adjust_infix_notation df notation_symbols c else df, notation_symbols, c in
  (* Build the canonical identifier of the syntactic part of the notation *)
  let ntn = make_notation_key main_data.entry notation_symbols.symbols in
  (* Build or rebuild the syntax rules *)
  let syntax_rules =
    if isnumeral then (check_no_syntax_modifiers_for_numeral syntax_modifiers; PrimTokenSyntax) else
    match syntax_modifiers with
    | [] ->
      (* No syntax data: try to rely on a previously declared rule *)
      (try SpecificSyntax (recover_notation_syntax ntn)
      with NoSyntaxRule ->
        (* Try to determine a default syntax rule *)
        let sd = compute_syntax_data ~local main_data notation_symbols ntn NotationMods.default in
        SpecificSyntax (make_syntax_rules false main_data ntn sd))

    | _ ->
      let mods = interp_modifiers main_data.entry syntax_modifiers in
      let sd = compute_syntax_data ~local main_data notation_symbols ntn mods in
      SpecificSyntax (make_syntax_rules false main_data ntn sd)
  in
  (* Build the interpretation *)
  let notation = make_notation_interpretation ~local main_data notation_symbols ntn syntax_rules df env c sc in
  (* Declare both syntax and interpretation *)
  syntax_rules_iter (fun sy -> Lib.add_anonymous_leaf (inSyntaxExtension (local,(ntn,sy)))) syntax_rules;
  Lib.add_anonymous_leaf (inNotation notation);
  (* Dump the location of the notation for coqdoc *)
  Dumpglob.dump_notation (CAst.make ?loc ntn) sc true

(* Main entry point for Format Notation *)

let add_notation_extra_printing_rule df k v =
  let notk =
    let { symbols }, isnumeral = analyze_notation_tokens ~onlyprinting:true ~infix:false InConstrEntry df in
    if isnumeral then user_err (str "Notations for numbers are primitive.");
    make_notation_key InConstrEntry symbols in
  add_notation_extra_printing_rule notk k v

(**********************************************************************)
(* Scopes, delimiters and classes bound to scopes                     *)

type scope_command =
  | ScopeDeclare
  | ScopeDelimAdd of string
  | ScopeDelimRemove
  | ScopeClasses of scope_class list

let load_scope_command_common silently_define_scope_if_undefined _ (_,(local,scope,o)) =
  let declare_scope_if_needed =
    if silently_define_scope_if_undefined then Notation.declare_scope
    else Notation.ensure_scope in
  match o with
  | ScopeDeclare -> Notation.declare_scope scope
  (* When the default shall be to require that a scope already exists *)
  (* the call to declare_scope_if_needed will have to be removed below *)
  | ScopeDelimAdd dlm -> declare_scope_if_needed scope
  | ScopeDelimRemove -> declare_scope_if_needed scope
  | ScopeClasses cl -> declare_scope_if_needed scope

let load_scope_command =
  load_scope_command_common true

let open_scope_command i (_,(local,scope,o)) =
  if Int.equal i 1 then
    match o with
    | ScopeDeclare -> ()
    | ScopeDelimAdd dlm -> Notation.declare_delimiters scope dlm
    | ScopeDelimRemove -> Notation.remove_delimiters scope
    | ScopeClasses cl -> List.iter (Notation.declare_scope_class scope) cl

let cache_scope_command o =
  load_scope_command_common false 1 o;
  open_scope_command 1 o

let subst_scope_command (subst,(local,scope,o as x)) = match o with
  | ScopeClasses cl ->
      let env = Global.env () in
      let cl' = List.map_filter (subst_scope_class env subst) cl in
      let cl' =
        if List.for_all2eq (==) cl cl' then cl
        else cl' in
      local, scope, ScopeClasses cl'
  | _ -> x

let classify_scope_command (local, _, _ as o) =
  if local then Dispose else Substitute o

let inScopeCommand : locality_flag * scope_name * scope_command -> obj =
  declare_object {(default_object "DELIMITERS") with
      cache_function = cache_scope_command;
      open_function = simple_open open_scope_command;
      load_function = load_scope_command;
      subst_function = subst_scope_command;
      classify_function = classify_scope_command}

let declare_scope local scope =
  Lib.add_anonymous_leaf (inScopeCommand(local,scope,ScopeDeclare))

let add_delimiters local scope key =
  Lib.add_anonymous_leaf (inScopeCommand(local,scope,ScopeDelimAdd key))

let remove_delimiters local scope =
  Lib.add_anonymous_leaf (inScopeCommand(local,scope,ScopeDelimRemove))

let add_class_scope local scope cl =
  Lib.add_anonymous_leaf (inScopeCommand(local,scope,ScopeClasses cl))

let interp_syndef_modifiers deprecation modl =
  let mods, skipped = interp_non_syntax_modifiers ~reserved:false ~infix:false ~syndef:true deprecation modl in
  if skipped <> [] then
    (let modifier = List.hd skipped in
    user_err ?loc:modifier.CAst.loc (str "Abbreviations don't support " ++ Ppvernac.pr_syntax_modifier modifier));
  (mods.onlyparsing, mods.itemscopes)

let add_syntactic_definition ~local deprecation env ident (vars,c) modl =
  let (only_parsing, scopes) = interp_syndef_modifiers deprecation modl in
  let vars = List.map (fun v -> v, List.assoc_opt v scopes) vars in
  let acvars,pat,reversibility =
    match vars, intern_name_alias c with
    | [], Some(r,u) ->
      (* Check if abbreviation to a name and avoid early insertion of
         maximal implicit arguments *)
      Id.Map.empty, NRef(r, u), APrioriReversible
    | _ ->
      let fold accu (id,scope) = Id.Map.add id (NtnInternTypeAny scope) accu in
      let i_vars = List.fold_left fold Id.Map.empty vars in
      let nenv = {
        ninterp_var_type = i_vars;
        ninterp_rec_vars = Id.Map.empty;
      } in
      interp_notation_constr env nenv c
  in
  let in_pat (id,_) = (id,ETConstr (Constrexpr.InConstrEntry,None,(NextLevel,InternalProd))) in
  let interp = make_interpretation_vars ~default_if_binding:AsNameOrPattern [] 0 acvars (List.map in_pat vars) in
  let vars = List.map (fun (x,_) -> (x, Id.Map.find x interp)) vars in
  let also_in_cases_pattern = has_no_binders_type vars in
  let onlyparsing = only_parsing || fst (printability None [] false reversibility pat) in
  Syntax_def.declare_syntactic_definition ~local ~also_in_cases_pattern deprecation ident ~onlyparsing (vars,pat)

(**********************************************************************)
(* Declaration of custom entry                                        *)

let warn_custom_entry =
  CWarnings.create ~name:"custom-entry-overridden" ~category:"parsing"
         (fun s ->
          strbrk "Custom entry " ++ str s ++ strbrk " has been overridden.")

let load_custom_entry _ (_,(local,s)) =
  if Egramcoq.exists_custom_entry s then warn_custom_entry s
  else Egramcoq.create_custom_entry ~local s

let cache_custom_entry o = load_custom_entry 1 o

let subst_custom_entry (subst,x) = x

let classify_custom_entry (local,s as o) =
  if local then Dispose else Substitute o

let inCustomEntry : locality_flag * string -> obj =
  declare_object {(default_object "CUSTOM-ENTRIES") with
      cache_function = cache_custom_entry;
      load_function = load_custom_entry;
      subst_function = subst_custom_entry;
      classify_function = classify_custom_entry}

let declare_custom_entry local s =
  if Egramcoq.exists_custom_entry s then
    user_err Pp.(str "Custom entry " ++ str s ++ str " already exists.")
  else
    Lib.add_anonymous_leaf (inCustomEntry (local,s))
