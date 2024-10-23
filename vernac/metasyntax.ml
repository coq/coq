(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
open Notationextern
open Notation_gram
open Notation_ops
open Ppextend
open Extend
open Libobject
open Constrintern
open Libnames
open Notation
open Nameops

(** **************************************************************** **)
(** Printing grammar entries                                         **)

let entry_buf = Buffer.create 64

let pr_entry e =
  let () = Buffer.clear entry_buf in
  let ft = Format.formatter_of_buffer entry_buf in
  let () = Procq.Entry.print ft e in
  str (Buffer.contents entry_buf)

let error_unknown_entry ?loc name =
  user_err ?loc Pp.(str "Unknown or unprintable grammar entry " ++ str name ++ str".")

let pr_registered_grammar name =
  let gram = Procq.find_grammars_by_name name in
  match gram with
  | [] -> error_unknown_entry name
  | entries ->
    let pr_one (Procq.Entry.Any e) =
      str "Entry " ++ str (Procq.Entry.name e) ++ str " is" ++ fnl () ++
      pr_entry e
    in
    prlist pr_one entries

let pr_grammar_subset grammar =
  let pp = String.Map.mapi (fun name l -> match l with
      | []  -> assert false
      | entries ->
        str "Entry " ++ str name ++ str " is" ++ fnl() ++
        prlist_with_sep (fun () -> str "or" ++ fnl())
          (fun (Procq.Entry.Any e) -> pr_entry e)
          entries)
      grammar
  in
  let pp = CString.Map.bindings pp in
  prlist_with_sep fnl (fun (_,pp) -> pp) pp

let is_known = let open Procq.Entry in function
  | "constr" | "term" | "binder_constr" ->
    Some [ Any Procq.Constr.constr;
      Any Procq.Constr.lconstr;
      Any Procq.Constr.binder_constr;
      Any Procq.Constr.term;
    ]
  | "vernac" ->
    Some Pvernac.Vernac_.[
        Any vernac_control;
        (* main_entry="vernac", included not because it's interesting but because otherwise it's shadowed by the "vernac" group defined here *)
        Any main_entry;
        Any command;
        Any syntax;
        Any gallina;
        Any gallina_ext;
    ]
  | name ->
    let gram = Procq.find_grammars_by_name name in
    match gram with
    | [] -> None
    | entries -> Some entries

let full_grammar () =
  let open Pvernac.Vernac_ in
  let open Procq.Entry in
  let proof_modes = List.map (fun (_,e) -> Any e)
      (CString.Map.bindings (Pvernac.list_proof_modes()))
  in
  let entries = (Any vernac_control) :: (Any noedit_mode) :: proof_modes in
  Procq.Entry.accumulate_in entries

let same_entry (Procq.Entry.Any e) (Procq.Entry.Any e') = (Obj.magic e) == (Obj.magic e')

let pr_grammar = function
  | [] ->
    let grammar = full_grammar () in
    pr_grammar_subset grammar
  | names ->
    let known, other = List.fold_left (fun (known,other) name ->
        match is_known name with
        | Some v -> v @ known, other
        | None -> known, name::other)
        ([],[])
        names
    in
    let grammar = if List.is_empty other then String.Map.empty else full_grammar () in
    let () = List.iter (fun name ->
        if not (String.Map.mem name grammar)
        then error_unknown_entry name)
        other
    in
    let other = String.Set.of_list other in
    let grammar = String.Map.filter (fun name _ -> String.Set.mem name other) grammar in
    let grammar = List.fold_left (fun grammar (Procq.Entry.Any e as any) ->
        String.Map.update (Procq.Entry.name e) (function
            | None -> Some [any]
            | Some vl as v ->
              if List.mem_f same_entry any vl
              then v else Some (any :: vl))
          grammar)
        grammar known
    in
    pr_grammar_subset grammar

let pr_custom_grammar name = pr_registered_grammar ("custom:"^name)

let pr_keywords () =
  Pp.prlist_with_sep Pp.fnl Pp.str (CString.Set.elements (CLexer.keywords (Procq.get_keyword_state())))

(** **************************************************************** **)
(** Parse a format (every terminal starting with a letter or a single
    quote (except a single quote alone) must be quoted) **)

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

(** **************************************************************** **)
(** Analyzing notations                                              **)

(* Find non-terminal tokens of notation *)

(* To protect alphabetic tokens and quotes from being seen as variables *)
let quote_notation_token x =
  let n = String.length x in
  let norm = CLexer.is_ident x in
  if (n > 0 && norm) || (n > 2 && x.[0] == '\'') then "'"^x^"'"
  else x

let analyze_notation_tokens ~onlyprinting ~infix entry df =
  let df = if infix then quote_notation_token df else df in
  let { recvars; mainvars; symbols } as res = decompose_raw_notation df in
    (* don't check for nonlinearity if printing only, see Bug 5526 *)
  (if not onlyprinting then
    match List.duplicates Id.equal (mainvars @ List.map snd recvars) with
    | id :: _ ->
        user_err
          (str "Variable " ++ Id.print id ++ str " occurs more than once.")
    | _ -> ());
  let is_prim_token = is_prim_token_constant_in_constr (entry, symbols) in
  res, is_prim_token

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
  CWarnings.create ~name:"primitive-token-modifier" ~category:CWarnings.CoreCategories.parsing
         (fun () -> str "Notations for numbers or strings are primitive; skipping this modifier.")

let check_no_syntax_modifiers_for_numeral = function
  | [] -> ()
  | l -> List.iter (function {CAst.loc} -> warn_unexpected_primitive_token_modifier ?loc ()) l

let error_not_same_scope x y =
  user_err
    (str "Variables " ++ Id.print x ++ str " and " ++ Id.print y ++ str " must be in the same scope.")

(** **************************************************************** **)
(** Build pretty-printing rules                                      **)

let pr_notation_entry = function
  | InConstrEntry -> str "constr"
  | InCustomEntry s -> str "custom " ++ str s

let side = function
  | BorderProd (b,_) -> Some b
  | _ -> None

let precedence_of_position_and_level from_level = function
  | NumLevel n, BorderProd (b,Some a) ->
    let prec =
     let open Gramlib.Gramext in
     match a, b with
     | RightA, Left -> LevelLt n
     | RightA, Right -> LevelLe n
     | LeftA, Left -> LevelLe n
     | LeftA, Right -> LevelLt n
     | NonA, _ -> LevelLt n in
    {notation_subentry = InConstrEntry; notation_relative_level = prec; notation_position = Some b}
  | NumLevel n, b -> {notation_subentry = InConstrEntry; notation_relative_level = LevelLe n; notation_position = side b}
  | NextLevel, b -> {notation_subentry = InConstrEntry; notation_relative_level = LevelLt from_level; notation_position = side b}
  | DefaultLevel, b -> {notation_subentry = InConstrEntry; notation_relative_level = LevelSome; notation_position = side b}

(** Computing precedences of non-terminals for parsing *)
let precedence_of_entry_type { notation_entry = from_custom; notation_level = from_level } = function
  | ETConstr (custom,_,x) when notation_entry_eq custom from_custom ->
    (precedence_of_position_and_level from_level x).notation_relative_level
  | ETConstr (custom,_,(NumLevel n,_)) -> LevelLe n
  | ETConstr (custom,_,(NextLevel,_)) ->
    user_err (strbrk "\"next level\" is only for sub-expressions in the same entry as where the notation is (" ++
              quote (pr_notation_entry custom) ++ strbrk " is different from " ++
              quote (pr_notation_entry from_custom) ++ str ").")
  | ETPattern (_,n) -> let n = match n with None -> 0 | Some n -> n in LevelLe n
  | _ -> LevelSome (* should not matter *)

let pattern_entry_level = function None -> 0 | Some n -> n

(** Computing precedences for future insertion of parentheses at
    the time of printing using hard-wired constr levels *)
let unparsing_precedence_of_entry_type from_level = function
  | ETConstr (InConstrEntry,_,x) ->
    (* Possible insertion of parentheses at printing time to deal
       with precedence in a constr entry is managed using [prec_less]
       in [ppconstr.ml] *)
    precedence_of_position_and_level from_level x
  | ETConstr (custom,_,(_,b)) ->
    (* Precedence of printing for a custom entry is managed using
       explicit insertion of entry coercions at the time of building
       a [constr_expr] *)
    {notation_subentry = custom; notation_relative_level = LevelSome; notation_position = side b}
  | ETPattern (_,n) -> (* in constr *)
    {notation_subentry = InConstrEntry; notation_relative_level = LevelLe (pattern_entry_level n); notation_position = None}
  | _ -> (* should not matter *)
    {notation_subentry = InConstrEntry; notation_relative_level = LevelSome; notation_position = None}

(** Utilities for building default printing rules *)

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
  let subentry = unparsing_precedence_of_entry_type from x in
  match x with
  | ETConstr _ | ETGlobal | ETBigint ->
     UnpMetaVar subentry
  | ETPattern _ | ETName | ETIdent ->
     UnpBinderMetaVar (subentry,NotQuotedPattern)
  | ETBinder isopen ->
     UnpBinderMetaVar (subentry,QuotedPattern)

(** Heuristics for building default printing rules *)

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
        let subentry = unparsing_precedence_of_entry_type from_level typ in
        let sl' =
          (* If no separator: add a break *)
          if List.is_empty sl then add_break 1 []
          (* We add NonTerminal for simulation but remove it afterwards *)
          else make true sl in
        let hunk = match typ with
          | ETConstr _ -> UnpListMetaVar (subentry,List.map snd sl')
          | ETBinder isopen ->
              check_open_binder isopen sl m;
              UnpBinderListMetaVar (isopen,true,List.map snd sl')
          | ETName | ETIdent ->
              UnpBinderListMetaVar (false,true,List.map snd sl')
          | ETPattern _ ->
              UnpBinderListMetaVar (false,false,List.map snd sl')
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

(** Build default printing rules from explicit format *)

let error_format ?loc () = user_err ?loc Pp.(str "The format does not match the notation.")

let warn_format_break =
  CWarnings.create ~name:"notation-both-format-and-spaces" ~category:CWarnings.CoreCategories.parsing
         (fun () ->
          strbrk "Discarding format implicitly indicated by multiple spaces in notation because an explicit format modifier is given.")

let has_ldots l =
  List.exists (function (_,UnpTerminal s) -> String.equal s (Id.to_string Notation_ops.ldots_var) | _ -> false) l

let rec split_format_at_ldots hd = function
  | (loc,UnpTerminal s) :: fmt when String.equal s (Id.to_string Notation_ops.ldots_var) -> loc, List.rev hd, fmt
  | u :: fmt ->
      check_no_ldots_in_box u;
      split_format_at_ldots (u::hd) fmt
  | [] -> raise_notrace Exit

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
      let subentry = unparsing_precedence_of_entry_type from_level typ in
      let loc_slfmt,rfmt = read_recursive_format sl fmt in
      let sl, slfmt = aux (sl,loc_slfmt) in
      if not (List.is_empty sl) then error_format ?loc:(find_prod_list_loc loc_slfmt fmt) ();
      let symbs, l = aux (symbs,rfmt) in
      let hunk = match typ with
        | ETConstr _ -> UnpListMetaVar (subentry,slfmt)
        | ETBinder isopen ->
            check_open_binder isopen sl m;
            UnpBinderListMetaVar (isopen,true,slfmt)
        | ETName | ETIdent ->
            UnpBinderListMetaVar (false,true,slfmt)
        | ETPattern _ ->
            UnpBinderListMetaVar (false,false,slfmt)
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

(** **************************************************************** **)
(** Build parsing rules                                              **)

let assoc_of_type from n (_,typ) = precedence_of_entry_type {notation_entry = from; notation_level = n} typ

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
    notation_entry_eq s s' && production_level_eq lev lev'
  | _ -> false

let include_possible_similar_trailing_pattern typ etyps sl l =
  let rec aux n = function
  | Terminal s :: sl, Terminal s'::l' when s = s' -> aux n (sl,l')
  | [], NonTerminal x ::l' when is_constr_typ typ x etyps -> try_aux n l'
  | Break _ :: sl, l -> aux n (sl,l)
  | sl, Break _ :: l -> aux n (sl,l)
  | _ -> raise_notrace Exit
  and try_aux n l =
    try aux (n+1) (sl,l)
    with Exit -> n,l in
  try_aux 0 l

let prod_entry_type = function
  | ETIdent -> ETProdIdent
  | ETName -> ETProdName
  | ETGlobal -> ETProdGlobal
  | ETBigint -> ETProdBigint
  | ETBinder o -> ETProdOneBinder o
  | ETConstr (s,_,p) -> ETProdConstr (s,p)
  | ETPattern (_,n) -> ETProdPattern (pattern_entry_level n)

let keyword_needed need s =
  (* Ensure that IDENT articulation terminal symbols are keywords *)
  match Procq.terminal s with
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
  | None ->
  match String.unquote_coq_string s with
  | Some _ ->
    if need then
      Flags.if_verbose Feedback.msg_info (str "String '" ++ str s ++ str "' now a keyword");
    need
  | _ -> true

let make_production ({notation_level = lev}, _) etyps symbols =
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
            let typ = if o then (assert (tkl = []); ETBinderOpen) else ETBinderClosed (None,tkl) in
            distribute
              [GramConstrNonTerminal (ETProdBinderList typ, Some x)] (aux false l)
        | ETIdent ->
            distribute
              [GramConstrNonTerminal (ETProdBinderList (ETBinderClosed (Some ETProdIdent,tkl)), Some x)] (aux false l)
        | ETName ->
            distribute
              [GramConstrNonTerminal (ETProdBinderList (ETBinderClosed (Some ETProdName,tkl)), Some x)] (aux false l)
        | ETPattern (st,n) ->
            distribute
              [GramConstrNonTerminal (ETProdBinderList (ETBinderClosed (Some (ETProdPattern (pattern_entry_level n)),tkl)), Some x)] (aux false l)
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

(** ******************************************************************** **)
(** Registration of syntax extensions                                    **)
(** (parsing/printing, no interpretation)                                **)

let pr_arg_level from (lev,typ) =
  let pplev = function
  | LevelLt n when Int.equal n from -> spc () ++ str "at next level"
  | LevelLe n -> spc () ++ str "at level " ++ int n
  | LevelLt n -> spc () ++ str "at level below " ++ int n
  | LevelSome -> mt () in
  Ppvernac.pr_set_entry_type (fun _ -> (*TO CHECK*) mt()) typ ++ pplev lev

let pr_level ntn ({notation_entry = from; notation_level = fromlevel}, args) typs =
  (match from with InConstrEntry -> mt () | InCustomEntry s -> str "in " ++ str s ++ spc()) ++
  str "at level " ++ int fromlevel ++
  (match args with | [] -> mt () | _ :: _ ->
     spc () ++ str "with arguments" ++ spc()
     ++ prlist_with_sep pr_comma (pr_arg_level fromlevel) (List.combine args typs))

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
  CWarnings.create ~name:"notation-incompatible-format" ~category:CWarnings.CoreCategories.parsing
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
       (not (List.for_all2eq unparsing_eq rules'.notation_printing_unparsing generic_rules.notation_printing_unparsing))
    then
      warn_incompatible_format (None,ntn)
  with Not_found -> ()

let specific_format_to_declare (specific,ntn as specific_ntn) rules =
  try
    let specific_rules = Ppextend.find_specific_notation_printing_rule specific_ntn in
    if not (List.for_all2eq unparsing_eq rules.notation_printing_unparsing specific_rules.notation_printing_unparsing)
    then (warn_incompatible_format (Some specific,ntn); true)
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
    let oldtyps = Notgram_ops.non_terminals_of_notation ntn_for_grammar in
    if not (level_eq prec oldprec) && oldparsing <> None then
      error_parsing_incompatible_level ntn ntn_for_grammar oldprec oldtyps prec typs;
    if oldparsing = None then raise Not_found
  with Not_found ->
    Egramrocq.extend_constr_grammar rule

let warn_prefix_incompatible_level =
  CWarnings.create ~name:"notation-incompatible-prefix"
    ~category:CWarnings.CoreCategories.parsing
    (fun (pref, ntn, pref_prec, pref_nottyps, prec, nottyps) ->
      str "Notations " ++ pr_notation pref
      ++ spc () ++ str "defined " ++ pr_level pref pref_prec pref_nottyps
      ++ spc () ++ str "and " ++ pr_notation ntn
      ++ spc () ++ str "defined " ++ pr_level ntn prec nottyps
      ++ spc () ++ str "have incompatible prefixes."
      ++ spc () ++ str "One of them will likely not work.")

let level_firstn k (lvl, lvls) =
  lvl, try CList.firstn k lvls with Failure _ -> []

let check_prefix_incompatible_level ntn prec nottyps =
  match Notgram_ops.longest_common_prefix ntn with
  | None -> ()
  | Some (pref, k) ->
     try
       let pref_prec = Notation.level_of_notation pref in
       let pref_prec = level_firstn k pref_prec in
       let prec = level_firstn k prec in
       let pref_nottyps = Notgram_ops.non_terminals_of_notation pref in
       let pref_nottyps = CList.firstn k pref_nottyps in
       let nottyps = CList.firstn k nottyps in
       if not (level_eq prec pref_prec && List.for_all2 Extend.constr_entry_key_eq_ignore_binder_kind nottyps pref_nottyps) then
         warn_prefix_incompatible_level (pref, ntn, pref_prec, pref_nottyps, prec, nottyps);
     with Not_found | Failure _ -> ()

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
      let oldtyps = Notgram_ops.non_terminals_of_notation ntn in
      if not (level_eq prec oldprec && List.for_all2 Extend.constr_entry_key_eq synext.synext_nottyps oldtyps) &&
         (oldparsing <> None || synext.synext_notgram = None) then
        error_incompatible_level ntn oldprec oldtyps prec synext.synext_nottyps;
      oldparsing
    with Not_found ->
      check_prefix_incompatible_level ntn prec synext.synext_nottyps;
      (* Declare the level and the precomputed parsing rule *)
      let () = Notation.declare_notation_level ntn prec in
      let () = Notgram_ops.declare_notation_non_terminals ntn synext.synext_nottyps in
      let () = Option.iter (Notgram_ops.declare_notation_grammar ntn) synext.synext_notgram in
      None in
  (* Declare the parsing rule *)
  begin match oldparsing, synext.synext_notgram with
  | None, Some grams -> List.iter (check_and_extend_constr_grammar ntn) grams
  | _ -> (* The grammars rules are canonically derived from the string and the precedence*) ()
  end;
  (* Printing *)
  Option.iter (declare_generic_notation_printing_rules ntn) synext.synext_notprint

let cache_syntax_extension (_, sy) =
  cache_one_syntax_extension sy

let subst_syntax_extension (subst, (local, (ntn, synext))) =
  (local, (ntn, synext))

let classify_syntax_definition (local, _) =
  if local then Dispose else Substitute

let open_syntax_extension i o =
  if Int.equal i 1 then cache_syntax_extension o

let inSyntaxExtension : syntax_extension_obj -> obj =
  declare_object
    {(default_object "SYNTAX-EXTENSION") with
     object_stage = Summary.Stage.Synterp;
     open_function = simple_open ~cat:notation_cat open_syntax_extension;
     cache_function = cache_syntax_extension;
     subst_function = subst_syntax_extension;
     classify_function = classify_syntax_definition}

(** ******************************************************************** **)
(** Precedences                                                          **)

(* Interpreting user-provided modifiers *)

(* XXX: We could move this to the parser itself *)

module NotationMods = struct

type notation_modifier = {
  assoc         : Gramlib.Gramext.g_assoc option;
  level         : int option;
  etyps         : (Id.t * simple_constr_prod_entry_key) list;

  (* common to syn_data below *)
  format        : lstring option;
}

let default = {
  assoc         = None;
  level         = None;
  etyps         = [];
  format        = None;
}

end

exception UnknownCustomEntry of string

let () = CErrors.register_handler @@ function
  | UnknownCustomEntry entry -> Some Pp.(str "Unknown custom entry: " ++ str entry ++ str ".")
  | _ -> None

let check_custom_entry entry =
  if not (Egramrocq.exists_custom_entry entry) then
    raise @@ UnknownCustomEntry entry

let check_entry_type = function
  | ETConstr (InCustomEntry entry,_,_) -> check_custom_entry entry
  | ETConstr (InConstrEntry,_,_) | ETPattern _
  | ETIdent | ETGlobal | ETBigint | ETName | ETBinder _-> ()

let interp_modifiers entry modl = let open NotationMods in
  let rec interp acc = function
  | [] -> acc
  | CAst.{loc;v} :: l -> match v with
    | SetEntryType (s,typ) ->
        let id = Id.of_string s in
        check_entry_type typ;
        if Id.List.mem_assoc id acc.etyps then
          user_err ?loc
            (str s ++ str " is already assigned to an entry or constr level.");
        interp { acc with etyps = (id,typ) :: acc.etyps; } l
    | SetItemLevel ([],bko,n) ->
        interp acc l
    | SetItemLevel (s::idl,bko,n) ->
        let id = Id.of_string s in
        if Id.List.mem_assoc id acc.etyps then
          user_err ?loc
            (str s ++ str " is already assigned to an entry or constr level.");
        interp { acc with etyps = (id,ETConstr (entry,bko,n)) :: acc.etyps } ((CAst.make ?loc @@ SetItemLevel (idl,bko,n))::l)
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
          interp { acc with level = Some n; } l)
    | SetCustomEntry (s,Some n) ->
        (* Note: name of entry already registered in interp_non_syntax_modifiers *)
        if acc.level <> None then
          user_err ?loc (str ("isolated \"at level " ^ string_of_int (Option.get acc.level) ^ "\" unexpected."));
        interp { acc with level = Some n } l
    | SetAssoc a ->
        if not (Option.is_empty acc.assoc) then user_err ?loc Pp.(str "An associativity is given more than once.");
        interp { acc with assoc = Some a; } l
    | SetOnlyParsing | SetOnlyPrinting | SetCustomEntry (_,None) | SetFormat _ | SetItemScope _ ->
        (* interpreted in interp_non_syntax_modifiers *)
        assert false
  in
  interp default modl

let check_useless_entry_types recvars mainvars etyps =
  let vars = let (l1,l2) = List.split recvars in l1@l2@mainvars in
  match List.filter (fun (x,etyp) -> not (List.mem x vars)) etyps with
  | (x,_)::_ -> user_err
                  (Id.print x ++ str " is unbound in the notation.")
  | _ -> ()

type notation_main_data = {
  onlyparsing  : bool;
  onlyprinting : bool;
  user_warns   : Globnames.extended_global_reference UserWarn.with_qf option;
  entry        : notation_entry;
  format       : unparsing Loc.located list option;
  itemscopes  : (Id.t * scope_name) list;
}

let warn_only_parsing_reserved_notation =
  CWarnings.create ~name:"irrelevant-reserved-notation-only-parsing" ~category:CWarnings.CoreCategories.parsing
    (fun () -> strbrk "The only parsing modifier has no effect in Reserved Notation.")

let warn_only_parsing_discarded_format =
  CWarnings.create ~name:"discarded-format-only-parsing" ~category:CWarnings.CoreCategories.parsing
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
  check_custom_entry entry';
  match main_data.entry with
  | InConstrEntry -> { main_data with entry = InCustomEntry entry' }
  | _ -> user_err ?loc (str "\"in custom\" is given more than once.")

let warn_irrelevant_format =
  CWarnings.create ~name:"irrelevant-format-only-parsing" ~category:CWarnings.CoreCategories.parsing
    (fun () -> str "The format modifier is irrelevant for only-parsing rules.")

let set_format ?loc main_data format =
  if not (Option.is_empty main_data.format) then user_err ?loc Pp.(str "A format is given more than once.");
  let format = if main_data.onlyparsing then (warn_irrelevant_format ?loc (); None) else Some (parse_format format) in
  { main_data with format }

let set_item_scope ?loc main_data ids sc =
  let itemscopes = List.map (fun id -> (Id.of_string id,sc)) ids @ main_data.itemscopes in
  match List.duplicates (fun (id1,_) (id2,_) -> Id.equal id1 id2) itemscopes  with
  | (id,_)::_ -> user_err ?loc (str "Notation scope for argument " ++ Id.print id ++ str " can be specified only once.")
  | [] -> { main_data with itemscopes }

let interp_non_syntax_modifiers ~reserved ~infix ~abbrev user_warns mods =
  let set (main_data,rest) = CAst.with_loc_val (fun ?loc -> function
    | SetOnlyParsing ->
       if not (Option.is_empty main_data.format) then
         (warn_only_parsing_discarded_format ?loc (); (main_data, rest))
       else
         (set_onlyparsing ?loc ~reserved main_data,rest)
    | SetOnlyPrinting when not abbrev -> (set_onlyprinting ?loc main_data,rest)
    | SetCustomEntry (entry,None) when not abbrev -> (set_custom_entry ?loc main_data entry,rest)
    | SetCustomEntry (entry,Some _) as x when not abbrev -> (set_custom_entry main_data entry,CAst.make ?loc x :: rest)
    | SetEntryType _ when infix -> user_err ?loc Pp.(str "Unexpected entry type in infix notation.")
    | SetItemLevel _ when infix -> user_err ?loc Pp.(str "Unexpected entry level in infix notation.")
    | SetFormat (TextFormat s) when not abbrev -> (set_format ?loc main_data s, rest)
    | SetItemScope (ids,sc) -> (set_item_scope ?loc main_data ids sc, rest)
    | modif -> (main_data,(CAst.make ?loc modif)::rest))
  in
  let main_data =
    {
      onlyparsing = false; onlyprinting = false; user_warns;
      entry = InConstrEntry; format = None; itemscopes = []
    }
  in
  let main_data, rest = List.fold_left set (main_data,[]) mods in
  main_data, List.rev rest

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
      | (ETIdent | ETName | ETBigint | ETGlobal | ETBinder _ as x), _ -> x
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
  | ETBinder _ | ETConstr (_,Some _,_) -> NtnInternTypeOnlyBinder
  | ETConstr (_,None,_) | ETBigint | ETGlobal
  | ETIdent | ETName | ETPattern _ -> NtnInternTypeAny None

let make_internalization_vars recvars maintyps =
  let maintyps = List.map (on_snd internalization_type_of_entry_type) maintyps in
  let extratyps = List.map (fun (x,y) -> (y,List.assoc x maintyps)) recvars in
  maintyps @ extratyps

let make_interpretation_type isrec isbinding default_if_binding typ =
  match typ, isrec with
  (* Parsed as constr, but interpreted as a specific kind of binder *)
  | ETConstr (_,Some bk,_), true -> NtnTypeBinderList (NtnBinderParsedAsConstr bk)
  | ETConstr (_,Some bk,_), false -> NtnTypeBinder (NtnBinderParsedAsConstr bk)
  (* Parsed as constr list but interpreted as the default kind of binder *)
  | ETConstr (_,None,_), true when isbinding -> NtnTypeBinderList (NtnBinderParsedAsConstr default_if_binding)
  | ETConstr (_,None,_), false when isbinding -> NtnTypeBinder (NtnBinderParsedAsConstr default_if_binding)
  (* Parsed as constr, interpreted as constr *)
  | ETConstr (_,None,_), true -> NtnTypeConstrList
  | ETConstr (_,None,_), false -> NtnTypeConstr
  (* Different way of parsing binders, maybe interpreted also as
     constr, but conventionally internally binders *)
  | ETIdent, true -> NtnTypeBinderList (NtnBinderParsedAsSomeBinderKind AsIdent)
  | ETIdent, false -> NtnTypeBinder (NtnBinderParsedAsSomeBinderKind AsIdent)
  | ETName, true -> NtnTypeBinderList (NtnBinderParsedAsSomeBinderKind AsName)
  | ETName, false -> NtnTypeBinder (NtnBinderParsedAsSomeBinderKind AsName)
  (* Parsed as ident/pattern, primarily interpreted as binder; maybe strict at printing *)
  | ETPattern (ppstrict,_), true -> NtnTypeBinderList (NtnBinderParsedAsSomeBinderKind (if ppstrict then AsStrictPattern else AsAnyPattern))
  | ETPattern (ppstrict,_), false -> NtnTypeBinder (NtnBinderParsedAsSomeBinderKind (if ppstrict then AsStrictPattern else AsAnyPattern))
  | ETBinder _, true -> NtnTypeBinderList NtnBinderParsedAsBinder
  | ETBinder _, false -> NtnTypeBinder NtnBinderParsedAsBinder
  (* Others *)
  | ETBigint, true | ETGlobal, true -> NtnTypeConstrList
  | ETBigint, false | ETGlobal, false -> NtnTypeConstr

let entry_relative_level_of_constr_prod_entry from_level = function
  | ETConstr (entry,_,(_,y)) as x ->
     let side = match y with BorderProd (side,_) -> Some side | _ -> None in
     { notation_subentry = entry; notation_relative_level = precedence_of_entry_type from_level x; notation_position = side }
  | _ -> constr_some_level

let make_interpretation_vars
  (* For binders, default is to parse only as an ident *) ?(default_if_binding=AsName)
   recvars allvars (entry,_) typs =
  let eq_subscope (sc1, l1) (sc2, l2) =
    List.equal String.equal sc1 sc2 &&
    List.equal String.equal l1 l2
  in
  let check (x, y) =
    let (_,scope1,_ntn_binding_ids1) = Id.Map.find x allvars in
    let (_,scope2,_ntn_binding_ids2) = Id.Map.find y allvars in
    if not (eq_subscope scope1 scope2) then error_not_same_scope x y
    (* Note: binding_ids should currently be the same, and even with
      eventually more complex notations, such as e.g.
        Notation "!! x .. y , P .. Q" := (fun x => (P, .. (fun y => (Q, True)) ..)).
      each occurrence of the recursive notation variables may have its own binders *)
  in
  let () = List.iter check recvars in
  let useless_recvars = List.map snd recvars in
  let mainvars =
    Id.Map.filter (fun x _ -> not (Id.List.mem x useless_recvars)) allvars in
  Id.Map.mapi (fun x (isonlybinding, sc, ntn_binding_ids) ->
    let typ = Id.List.assoc x typs in
    ((entry_relative_level_of_constr_prod_entry entry typ, sc), ntn_binding_ids,
     make_interpretation_type (Id.List.mem_assoc x recvars) isonlybinding default_if_binding typ)) mainvars

let check_rule_productivity l =
  if List.for_all (function NonTerminal _ | Break _ -> true | _ -> false) l then
    user_err Pp.(str "A notation must include at least one symbol.");
  if (match l with SProdList _ :: _ -> true | _ -> false) then
    user_err Pp.(str "A recursive notation must start with at least one symbol.")

let warn_notation_bound_to_variable =
  CWarnings.create ~name:"notation-bound-to-variable" ~category:CWarnings.CoreCategories.parsing
         (fun () ->
          strbrk "This notation will not be used for printing as it is bound to a single variable.")

let warn_non_reversible_notation =
  CWarnings.create ~name:"non-reversible-notation" ~category:CWarnings.CoreCategories.parsing
         (function[@warning "+9"]
          | APrioriReversible -> assert false
          | Forgetful {
              forget_ltac=ltac;
              forget_volatile_cast=cast;
            } ->
            let what = (if ltac then ["Ltac expressions"] else [])
                       @ (if cast then ["volatile casts"] else [])
            in
            strbrk "This notation contains " ++
            prlist_with_sep (fun () -> strbrk " and ") str what ++ str ":" ++ spc() ++
            str "it will not be used for printing."
          | NonInjective ids ->
             let n = List.length ids in
             strbrk (String.plural n "Variable") ++ spc () ++ pr_enum Id.print ids ++ spc () ++
             strbrk (if n > 1 then "do" else "does") ++
             str " not occur in the right-hand side." ++ spc() ++
             strbrk "The notation will not be used for printing as it is not reversible.")

let is_coercion level typs =
  match level, typs with
  | Some ({notation_entry = custom; notation_level = n} as entry,_), [_,e] ->
     (match e, custom with
     | ETConstr _, _ ->
         let entry_relative = entry_relative_level_of_constr_prod_entry entry e in
         if is_coercion entry entry_relative then
           Some (IsEntryCoercion (entry,entry_relative))
         else
           None
     | ETGlobal, InCustomEntry s -> Some (IsEntryGlobal (s,n))
     | ETIdent, InCustomEntry s -> Some (IsEntryIdent (s,n))
     | _ -> None)
  | Some _, _ -> assert false
  | None, _ -> None

let printability level typs vars onlyparsing reversibility = function
| NVar id when reversibility = APrioriReversible && List.mem_assoc_f Id.equal id vars ->
  let coe = is_coercion level typs in
  let onlyparsing =
    if not onlyparsing && Option.is_empty coe then
      (warn_notation_bound_to_variable (); true)
    else
      onlyparsing in
  onlyparsing, coe
| _ ->
   (if not onlyparsing && reversibility <> APrioriReversible then
     (warn_non_reversible_notation reversibility; true)
    else onlyparsing),None

let warn_closed_notation_not_level_0 =
  CWarnings.create ~name:"closed-notation-not-level-0" ~category:CWarnings.CoreCategories.parsing
    (fun () -> strbrk "Closed notations (i.e. starting and ending with a \
                       terminal symbol) should usually be at level 0 \
                       (default).")

let warn_postfix_notation_not_level_1 =
  CWarnings.create ~name:"postfix-notation-not-level-1" ~category:CWarnings.CoreCategories.parsing
    (fun () -> strbrk "Postfix notations (i.e. starting with a \
                       nonterminal symbol and ending with a terminal \
                       symbol) should usually be at level 1 (default).")

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
      let msgs, lev = match last_is_terminal (), lev with
        | false, _ -> [], lev
        | true, None -> [fun () -> Flags.if_verbose (Feedback.msg_info ?loc:None) (strbrk "Setting postfix notation at level 1.")], Some 1
        | true, Some 1 -> [], Some 1
        | true, Some n -> [fun () -> warn_postfix_notation_not_level_1 ()], Some n in
      let test () =
        if onlyprint then
          if Option.is_empty lev then
            user_err Pp.(str "Explicit level needed in only-printing mode when the level of the leftmost non-terminal is given.")
          else msgs,Option.get lev
        else
          user_err Pp.(str "The level of the leftmost non-terminal cannot be changed.") in
      (try match List.assoc x etyps, custom with
        | ETConstr (s,_,(NumLevel _ | NextLevel)), s' when s = s' -> test ()
        | (ETIdent | ETName | ETBigint | ETGlobal), _ ->
            begin match lev with
            | None ->
              ([fun () -> Flags.if_verbose (Feedback.msg_info ?loc:None) (strbrk "Setting notation at level 0.")],0)
            | Some 0 ->
              (msgs,0)
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
            else msgs,Option.get lev
      with Not_found ->
        if Option.is_empty lev then
          user_err Pp.(str "A left-recursive notation must have an explicit level.")
        else msgs,Option.get lev)
  | Some (Terminal _) when last_is_terminal () ->
      begin match lev with
      | None -> [fun () -> Flags.if_verbose (Feedback.msg_info ?loc:None) (strbrk "Setting notation at level 0.")], 0
      | Some 0 -> [], 0
      | Some n -> [fun () -> warn_closed_notation_not_level_0 ()], n
      end
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
        if Egramrocq.locality_of_custom_entry s then
          user_err (strbrk "Notation has to be declared local as it depends on custom entry " ++ str s ++
                    strbrk " which is local."))
      (List.uniquize allcustoms)

let longest_common_prefix_level ntn =
  Notgram_ops.longest_common_prefix ntn
  |> Option.map (fun (ntn, sz) ->
         let level, levels = level_firstn sz (Notation.level_of_notation ntn) in
         ntn, level.notation_level, levels)

let default_prefix_level ntn_prefix =
  let with_prefix prefix level =
    Flags.if_verbose Feedback.msg_info
      (strbrk "Setting notation at level " ++ int level ++ spc ()
       ++ str "to match previous notation with longest common prefix:"
       ++ spc () ++ str "\"" ++ str (snd prefix) ++ str "\".");
    level in
  function Some n -> Some n | None ->
    Option.map (fun (prefix, level, _) -> with_prefix prefix level) ntn_prefix

let default_prefix_level_subentries ntn ntn_prefix symbols etyps =
  let with_prefix prefix from_level levels =
    let default_entry etyps (x, l) =
      let l' = match l with
        | LevelLt n when Int.equal n from_level -> NextLevel
        | LevelLe n | LevelLt n -> NumLevel n
        | LevelSome -> DefaultLevel in
      let e = List.assoc_opt x etyps
        |> Option.default (ETConstr (fst ntn, None, DefaultLevel)) in
      match l', e with
      | (NumLevel _ | NextLevel), ETConstr (n, b, DefaultLevel) ->
         Flags.if_verbose Feedback.msg_info
           (strbrk "Setting " ++ Id.print x ++ str " "
            ++ pr_arg_level from_level (l, e) ++ spc ()
            ++ str "to match previous notation with longest common prefix:"
            ++ spc () ++ str "\"" ++ str (snd prefix) ++ str "\".");
         (x, ETConstr (n, b, l')) :: List.remove_assoc x etyps
      | _ -> etyps in
    let levels =
      let rec aux levs symbs = match levs, symbs with
        | [], _ | _, [] | _, SProdList _ :: _ -> []
        (* not handling recursive notations *)
        | _, (Terminal _ | Break _) :: symbs -> aux levs symbs
        | l :: levs, NonTerminal x :: symbs -> (x, l) :: aux levs symbs in
      match levels, symbols with
      (* don't mess up with level of left border terminal *)
      | _ :: levs, NonTerminal _ :: symbs | levs, symbs -> aux levs symbs in
    List.fold_left default_entry etyps levels in
  match ntn_prefix with
  | None -> etyps
  | Some (prefix, from_level, levels) -> with_prefix prefix from_level levels

let compute_syntax_data ~local main_data notation_symbols ntn mods =
  let open SynData in
  let open NotationMods in
  if main_data.itemscopes <> [] then user_err (str "General notations don't support 'in scope'.");
  let {recvars;mainvars;symbols} = notation_symbols in
  let assoc = Option.append mods.assoc (Some Gramlib.Gramext.NonA) in
  let _ = check_useless_entry_types recvars mainvars mods.etyps in

  (* Notations for interp and grammar  *)
  let ntn_prefix = longest_common_prefix_level ntn in
  let level = default_prefix_level ntn_prefix mods.level in
  let msgs,n = find_precedence main_data.entry level mods.etyps symbols main_data.onlyprinting in
  let symbols_for_grammar =
    if main_data.entry = InConstrEntry then remove_curly_brackets symbols else symbols in
  let need_squash = not (List.equal Notation.symbol_eq symbols symbols_for_grammar) in
  let ntn_for_grammar = if need_squash then make_notation_key main_data.entry symbols_for_grammar else ntn in
  if main_data.entry = InConstrEntry && not main_data.onlyprinting then check_rule_productivity symbols_for_grammar;
  (* To globalize... *)
  let etyps = default_prefix_level_subentries ntn ntn_prefix symbols mods.etyps in
  let etyps = join_auxiliary_recursive_types recvars etyps in
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
      prec_for_grammar = ({notation_entry = main_data.entry; notation_level = n}, prec_for_grammar);
      typs_for_grammar = List.map snd sy_typs_for_grammar;
      need_squash
    } in

  (* Return relevant data for interpretation and for parsing/printing *)
  {
    msgs;
    level = ({notation_entry = main_data.entry; notation_level = n}, prec);
    subentries = sy_typs;
    pa_syntax_data = pa_sy_data;
    pp_syntax_data = pp_sy_data;
    not_data    = sy_fulldata;
  }

(** **************************************************************** **)
(** Registration of notation interpretation                          **)

type notation_obj = {
  notobj_local : bool;
  notobj_scope : scope_name option;
  notobj_interp : interpretation;
  notobj_coercion : entry_coercion_kind option;
  notobj_use : notation_use option;
  notobj_user_warns : UserWarn.t option;
  notobj_notation : notation * notation_location;
  notobj_specific_pp_rules : notation_printing_rules option;
}

let load_notation_common silently_define_scope_if_undefined _ nobj =
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

let open_notation i nobj =
  if Int.equal i 1 then begin
    let scope = nobj.notobj_scope in
    let (ntn, df) = nobj.notobj_notation in
    let pat = nobj.notobj_interp in
    let user_warns = nobj.notobj_user_warns in
    let scope = match scope with None -> LastLonelyNotation | Some sc -> NotationInScope sc in
    (* Declare the notation *)
    (match nobj.notobj_use with
    | Some use -> Notation.declare_notation (scope,ntn) pat df ~use nobj.notobj_coercion user_warns
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
  if nobj.notobj_local then Dispose else Substitute

let inNotation : notation_obj -> obj =
  declare_object {(default_object "NOTATION") with
       open_function = simple_open ~cat:notation_cat open_notation;
       cache_function = cache_notation;
       subst_function = subst_notation;
       load_function = load_notation;
       classify_function = classify_notation}

(**********************************************************************)
(* Registration of interpretation scopes opening/closing              *)

let open_scope i (local,op,sc) =
  if Int.equal i 1 then
    if op then Notation.open_scope sc else Notation.close_scope sc

let cache_scope o =
  open_scope 1 o

let subst_scope (subst,sc) = sc

let discharge_scope (local,_,_ as o) =
  if local then None else Some o

let classify_scope (local,_,_) =
  if local then Dispose else Substitute

let inScope : bool * bool * scope_name -> obj =
  declare_object {(default_object "SCOPE") with
      cache_function = cache_scope;
      open_function = simple_open ~cat:notation_cat open_scope;
      subst_function = subst_scope;
      discharge_function = discharge_scope;
      classify_function = classify_scope }

let open_close_scope local ~to_open sc =
  Lib.add_leaf (inScope (local,to_open,normalize_scope sc))

(**********************************************************************)

let with_lib_stk_protection f x =
  let fs = Lib.Interp.freeze () in
  try let a = f x in Lib.Interp.unfreeze fs; a
  with reraise ->
    let reraise = Exninfo.capture reraise in
    let () = Lib.Interp.unfreeze fs in
    Exninfo.iraise reraise

let with_syntax_protection f x =
  with_lib_stk_protection
    (Procq.with_grammar_rule_protection
       (with_notation_protection f)) x

(** **************************************************************** **)
(** Recovering existing syntax                                       **)

exception NoSyntaxRule

let recover_notation_syntax ntn =
  try
    let prec = Notation.level_of_notation ntn in
    let pa_typs = Notgram_ops.non_terminals_of_notation ntn in
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

(** **************************************************************** **)
(** Main entry point for building parsing and printing rules         **)

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

(** **************************************************************** **)
(** Main functions about notations                                   **)

let make_generic_printing_rules reserved main_data ntn sd =
  let open SynData in
  let {notation_entry = custom; notation_level = level},_ = sd.level in
  let make_rule rule =
    {
      notation_printing_reserved = reserved;
      notation_printing_rules =
        {
          notation_printing_unparsing = rule;
          notation_printing_level = level;
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
      if not reserved && main_data.onlyprinting then
        (* No intent to define a generic format *)
        Some rules
      else
        let rules' = make_rule (make_pp_rule level sd.pp_syntax_data main_data.format) in
        let () = check_reserved_format ntn rules rules'.notation_printing_rules in
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

let make_specific_printing_rules etyps symbols level pp_rule format =
  match level with
  | None -> None
  | Some ({ notation_level = level},_) ->
  match format, pp_rule with
    | None, Some _ when not (has_implicit_format symbols) -> None
    | _ ->
       Some
         {
           notation_printing_unparsing = make_pp_rule level (etyps,symbols) format;
           notation_printing_level = level;
         }

(**********************************************************************)
(* Miscellaneous                                                      *)

let warn_unused_interpretation =
  CWarnings.create ~name:"unused-notation" ~category:CWarnings.CoreCategories.parsing
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

let make_notation_interpretation ~local main_data notation_symbols ntn syntax_rules df env ?(impls=empty_internalization_env) c scope =
  let {recvars;mainvars;symbols} = notation_symbols in
  (* Recover types of variables and pa/pp rules; redeclare them if needed *)
  let level, i_typs, main_data, sy_pp_rules =
    match syntax_rules with
    | PrimTokenSyntax -> None, [], main_data, None
    | SpecificSyntax sy ->
    (* If the only printing flag has been explicitly requested, put it back *)
    let main_data = { main_data with onlyprinting = main_data.onlyprinting || (sy.synext_notgram = None && not main_data.onlyparsing) } in
    Some sy.synext_level, List.combine mainvars sy.synext_nottyps, main_data, sy.synext_notprint
  in
  (* Declare interpretation *)
  let sy_pp_rules = make_specific_printing_rules i_typs symbols level sy_pp_rules main_data.format in
  let path = (Lib.library_dp(), Lib.current_dirpath true) in
  let df' = ntn, (path,df) in
  let i_vars = make_internalization_vars recvars i_typs in
  let nenv = {
    ninterp_var_type = Id.Map.of_list i_vars;
    ninterp_rec_vars = Id.Map.of_list recvars;
  } in
  let (acvars, ac, reversibility) = interp_notation_constr env ~impls nenv c in
  let plevel = match level with Some (entry,l) -> (entry,l) | None (* numeral: irrelevant )*) -> (constr_lowest_level,[]) in
  let interp = make_interpretation_vars recvars acvars plevel i_typs in
  let map (x, _) = try Some (x, Id.Map.find x interp) with Not_found -> None in
  let vars = List.map_filter map i_vars in (* Order of elements is important here! *)
  let onlyparsing,coe = printability level i_typs vars main_data.onlyparsing reversibility ac in
  let main_data = { main_data with onlyparsing } in
  let use = make_use false onlyparsing main_data.onlyprinting in
  {
    notobj_local = local;
    notobj_scope = scope;
    notobj_use = use;
    notobj_interp = (vars, ac);
    notobj_coercion = coe;
    notobj_user_warns = main_data.user_warns |> Option.map UserWarn.drop_qf;
    notobj_notation = df';
    notobj_specific_pp_rules = sy_pp_rules;
  }

(* Notations without interpretation (Reserved Notation) *)

let add_reserved_notation ~local ~infix ({CAst.loc;v=df},mods) =
  let open SynData in
  let (main_data,mods) = interp_non_syntax_modifiers ~reserved:true ~infix ~abbrev:false None mods in
  let mods = interp_modifiers main_data.entry mods in
  let notation_symbols, is_prim_token = analyze_notation_tokens ~onlyprinting:main_data.onlyprinting ~infix main_data.entry df in
  let notation_symbols = if infix then adjust_reserved_infix_notation notation_symbols else notation_symbols in
  let ntn = make_notation_key main_data.entry notation_symbols.symbols in
  if is_prim_token then user_err ?loc (str "Notations for numbers or strings are primitive and need not be reserved.");
  let sd = compute_syntax_data ~local main_data notation_symbols ntn mods in
  let synext = make_syntax_rules true main_data ntn sd in
  List.iter (fun f -> f ()) sd.msgs;
  Lib.add_leaf (inSyntaxExtension(local,(ntn,synext)))

type notation_interpretation_decl =
  notation_declaration * notation_main_data * notation_symbols * notation * syntax_rules

(* Notations associated to a where clause *)

let prepare_where_notation ntn_decl =
  let
    { ntn_decl_string = { CAst.loc ; v = df };
      ntn_decl_interp = c;
      ntn_decl_modifiers = modifiers;
      ntn_decl_scope = sc;
    } = ntn_decl in
  let (main_data,mods) = interp_non_syntax_modifiers ~reserved:false ~infix:false ~abbrev:false None modifiers in
  match mods with
  | _::_ -> CErrors.user_err (str"Only modifiers not affecting parsing are supported here.")
  | [] ->
    let notation_symbols, is_prim_token = analyze_notation_tokens ~onlyprinting:main_data.onlyprinting ~infix:false main_data.entry df in
    let ntn = make_notation_key main_data.entry notation_symbols.symbols in
    let syntax_rules =
      if is_prim_token then PrimTokenSyntax else
      try SpecificSyntax (recover_notation_syntax ntn)
      with NoSyntaxRule ->
        user_err Pp.(str "Parsing rule for this notation has to be previously declared.") in
    (ntn_decl, main_data, notation_symbols, ntn, syntax_rules)

let add_notation_interpretation ~local env (ntn_decl, main_data, notation_symbols, ntn, syntax_rules) =
  let { ntn_decl_string = { CAst.loc ; v = df }; ntn_decl_interp = c; ntn_decl_scope = sc } = ntn_decl in
  let notation = make_notation_interpretation ~local main_data notation_symbols ntn syntax_rules df env c sc in
  Lib.add_leaf (inNotation notation);
  Dumpglob.dump_notation (CAst.make ?loc ntn) sc true

(* interpreting a where clause *)
let set_notation_for_interpretation env impls (ntn_decl, main_data, notation_symbols, ntn, syntax_rules) =
  let { ntn_decl_string = { CAst.loc ; v = df }; ntn_decl_interp = c; ntn_decl_scope = sc } = ntn_decl in
  let notation = make_notation_interpretation ~local:true main_data notation_symbols ntn syntax_rules df env ~impls c sc in
  Lib.add_leaf (inNotation notation);
  Option.iter (fun sc -> Lib.add_leaf (inScope (false,true,sc))) sc

let build_notation_syntax ~local ~infix user_warns ntn_decl =
  let { ntn_decl_string = {CAst.loc;v=df}; ntn_decl_modifiers = modifiers; ntn_decl_interp = c } = ntn_decl in
  (* Extract the modifiers not affecting the parsing rule *)
  let user_warns = Option.map UserWarn.with_empty_qf user_warns in
  let (main_data,syntax_modifiers) = interp_non_syntax_modifiers ~reserved:false ~infix ~abbrev:false user_warns modifiers in
  (* Extract the modifiers not affecting the parsing rule *)
  let notation_symbols, is_prim_token = analyze_notation_tokens ~onlyprinting:main_data.onlyprinting ~infix main_data.entry df in
  (* Add variables on both sides if an infix notation *)
  let df, notation_symbols, c = if infix then adjust_infix_notation df notation_symbols c else df, notation_symbols, c in
  (* Build the canonical identifier of the syntactic part of the notation *)
  let ntn = make_notation_key main_data.entry notation_symbols.symbols in
  let syntax_rules = if is_prim_token then (check_no_syntax_modifiers_for_numeral syntax_modifiers; PrimTokenSyntax) else
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
  main_data, notation_symbols, ntn, syntax_rules, c, df

let add_notation_syntax ~local ~infix user_warns ntn_decl =
  (* Build or rebuild the syntax rules *)
  let main_data, notation_symbols, ntn, syntax_rules, c, df = build_notation_syntax ~local ~infix user_warns ntn_decl in
  (* Declare syntax *)
  syntax_rules_iter (fun sy -> Lib.add_leaf (inSyntaxExtension (local,(ntn,sy)))) syntax_rules;
  let ntn_decl_string = CAst.make ?loc:ntn_decl.ntn_decl_string.CAst.loc df in
  let ntn_decl = { ntn_decl with ntn_decl_interp = c; ntn_decl_string } in
  ntn_decl, main_data, notation_symbols, ntn, syntax_rules

(** **************************************************************** **)
(** Scopes, delimiters and classes bound to scopes                   **)

type scope_command =
  | ScopeDeclare
  | ScopeDelimAdd of string
  | ScopeDelimRemove
  | ScopeClasses of add_scope_where option * scope_class list

let load_scope_command_common silently_define_scope_if_undefined _ (local,scope,o) =
  let declare_scope_if_needed =
    if silently_define_scope_if_undefined then Notation.declare_scope
    else Notation.ensure_scope in
  match o with
  | ScopeDeclare -> Notation.declare_scope scope
  (* When the default shall be to require that a scope already exists *)
  (* the call to declare_scope_if_needed will have to be removed below *)
  | ScopeDelimAdd dlm -> declare_scope_if_needed scope
  | ScopeDelimRemove -> declare_scope_if_needed scope
  | ScopeClasses _ -> declare_scope_if_needed scope

let load_scope_command =
  load_scope_command_common true

let open_scope_command i (noexport,scope,o) =
  if Int.equal i 1 then
    match o with
    | ScopeDeclare -> ()
    | ScopeDelimAdd dlm -> Notation.declare_delimiters scope dlm
    | ScopeDelimRemove -> Notation.remove_delimiters scope
    | ScopeClasses (where, cl) ->
      let local = Lib.sections_are_opened () in
      List.iter (Notation.declare_scope_class local scope ?where) cl

let cache_scope_command o =
  load_scope_command_common false 1 o;
  open_scope_command 1 o

let subst_scope_command (subst,(noexport,scope,o as x)) = match o with
  | ScopeClasses (where, cl) ->
      let env = Global.env () in
      let cl' = List.map_filter (subst_scope_class env subst) cl in
      let cl' =
        if List.for_all2eq (==) cl cl' then cl
        else cl' in
      noexport, scope, ScopeClasses (where, cl')
  | _ -> x

let classify_scope_command (noexport, _, _) =
  if noexport then Dispose else Substitute

let inScopeCommand : locality_flag * scope_name * scope_command -> obj =
  declare_object {(default_object "DELIMITERS") with
      cache_function = cache_scope_command;
      open_function = simple_open ~cat:notation_cat open_scope_command;
      load_function = load_scope_command;
      subst_function = subst_scope_command;
      classify_function = classify_scope_command}

let declare_scope local scope =
  Lib.add_leaf (inScopeCommand(local,scope,ScopeDeclare))

let add_delimiters local scope key =
  Lib.add_leaf (inScopeCommand(local,scope,ScopeDelimAdd key))

let remove_delimiters local scope =
  Lib.add_leaf (inScopeCommand(local,scope,ScopeDelimRemove))

let add_class_scope local scope where cl =
  Lib.add_leaf (inScopeCommand(local,scope,ScopeClasses (where, cl)))

let interp_abbreviation_modifiers user_warns modl =
  let mods, skipped = interp_non_syntax_modifiers ~reserved:false ~infix:false ~abbrev:true user_warns modl in
  if skipped <> [] then
    (let modifier = List.hd skipped in
    user_err ?loc:modifier.CAst.loc (str "Abbreviations don't support " ++ Ppvernac.pr_syntax_modifier modifier));
  (mods.onlyparsing, mods.itemscopes)

let add_abbreviation ~local user_warns env ident (vars,c) modl =
  let (only_parsing, scopes) = interp_abbreviation_modifiers user_warns modl in
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
  let level_arg = NumLevel 9 (* level of arguments of an application *) in
  let in_pat (id,_) = (id,ETConstr (Constrexpr.InConstrEntry,None,(level_arg,InternalProd))) in
  let level = (* not relevant *) (constr_lowest_level,[]) in
  let interp = make_interpretation_vars ~default_if_binding:AsAnyPattern [] acvars level (List.map in_pat vars) in
  let vars = List.map (fun (x,_) -> (x, Id.Map.find x interp)) vars in
  let onlyparsing = only_parsing || fst (printability None [] vars false reversibility pat) in
  Abbreviation.declare_abbreviation ~local user_warns ident ~onlyparsing (vars,pat)

(**********************************************************************)
(* Activating/deactivating notations                                  *)

let load_notation_toggle _ _ = ()

let open_notation_toggle _ (local,(on,all,pat)) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  toggle_notations ~on ~all ~verbose:(not !Flags.quiet) (Constrextern.without_symbols (Printer.pr_glob_constr_env env sigma)) pat

let cache_notation_toggle o =
  load_notation_toggle 1 o;
  open_notation_toggle 1 o

let subst_notation_toggle (subst,(local,(on,all,pat))) =
  let {notation_entry_pattern; interp_rule_key_pattern; use_pattern;
       scope_pattern; interpretation_pattern} = pat in
  let interpretation_pattern = Option.map (subst_interpretation subst) interpretation_pattern in
  let interp_rule_key_pattern = interp_rule_key_pattern in
  (local,(on,all,{notation_entry_pattern; interp_rule_key_pattern; use_pattern;
                  scope_pattern; interpretation_pattern}))

let classify_notation_toggle (local,_) =
  if local then Dispose else Substitute

let inNotationActivation : locality_flag * (bool * bool * notation_query_pattern) -> obj =
  declare_object {(default_object "NOTATION-TOGGLE") with
      cache_function = cache_notation_toggle;
      open_function = simple_open open_notation_toggle;
      load_function = load_notation_toggle;
      subst_function = subst_notation_toggle;
      classify_function = classify_notation_toggle}

let declare_notation_toggle local ~on ~all s =
  Lib.add_leaf (inNotationActivation (local,(on,all,s)))

(** **************************************************************** **)
(** Declaration of custom entries                                    **)

let warn_custom_entry =
  CWarnings.create ~name:"custom-entry-overridden" ~category:CWarnings.CoreCategories.parsing
         (fun s ->
          strbrk "Custom entry " ++ str s ++ strbrk " has been overridden.")

let load_custom_entry _ (local,s) =
  if Egramrocq.exists_custom_entry s then warn_custom_entry s
  else Egramrocq.create_custom_entry ~local s

let cache_custom_entry o = load_custom_entry 1 o

let subst_custom_entry (subst,x) = x

let classify_custom_entry (local,s) =
  if local then Dispose else Substitute

let inCustomEntry : locality_flag * string -> obj =
  declare_object {(default_object "CUSTOM-ENTRIES") with
      object_stage = Summary.Stage.Synterp;
      cache_function = cache_custom_entry;
      load_function = load_custom_entry;
      subst_function = subst_custom_entry;
      classify_function = classify_custom_entry}

let declare_custom_entry local s =
  if Egramrocq.exists_custom_entry s then
    user_err Pp.(str "Custom entry " ++ str s ++ str " already exists.")
  else
    Lib.add_leaf (inCustomEntry (local,s))
