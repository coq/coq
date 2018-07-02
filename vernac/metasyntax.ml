(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
open Notation_term
open Notation_gram
open Notation_ops
open Ppextend
open Extend
open Libobject
open Constrintern
open Vernacexpr
open Libnames
open Tok
open Notation
open Nameops

(**********************************************************************)
(* Tokens                                                             *)

let cache_token (_,s) = CLexer.add_keyword s

let inToken : string -> obj =
  declare_object {(default_object "TOKEN") with
       open_function = (fun i o -> if Int.equal i 1 then cache_token o);
       cache_function = cache_token;
       subst_function = Libobject.ident_subst_function;
       classify_function = (fun o -> Substitute o)}

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
  let gram = try Some (Pcoq.find_grammars_by_name name) with Not_found -> None in
  match gram with
  | None -> user_err Pp.(str "Unknown or unprintable grammar entry.")
  | Some entries ->
    let pr_one (Pcoq.AnyEntry e) =
      str "Entry " ++ str (Pcoq.Gram.Entry.name e) ++ str " is" ++ fnl () ++
      pr_entry e
    in
    prlist pr_one entries

let pr_grammar = function
  | "constr" | "operconstr" | "binder_constr" ->
      str "Entry constr is" ++ fnl () ++
      pr_entry Pcoq.Constr.constr ++
      str "and lconstr is" ++ fnl () ++
      pr_entry Pcoq.Constr.lconstr ++
      str "where binder_constr is" ++ fnl () ++
      pr_entry Pcoq.Constr.binder_constr ++
      str "and operconstr is" ++ fnl () ++
      pr_entry Pcoq.Constr.operconstr
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
  and parse_quoted n i =
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
      push_white i n (match c with
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
          parse_quoted (n-k) (i+1)
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

(* Interpret notations with a recursive component *)

let out_nt = function NonTerminal x -> x | _ -> assert false

let msg_expected_form_of_recursive_notation =
  "In the notation, the special symbol \"..\" must occur in\na configuration of the form \"x symbs .. symbs y\"."

let rec find_pattern nt xl = function
  | Break n as x :: l, Break n' :: l' when Int.equal n n' ->
      find_pattern nt (x::xl) (l,l')
  | Terminal s as x :: l, Terminal s' :: l' when String.equal s s' ->
      find_pattern nt (x::xl) (l,l')
  | [], NonTerminal x' :: l' ->
      (out_nt nt,x',List.rev xl),l'
  | _, Break s :: _ | Break s :: _, _ ->
      user_err Pp.(str ("A break occurs on one side of \"..\" but not on the other side."))
  | _, Terminal s :: _ | Terminal s :: _, _ ->
      user_err ~hdr:"Metasyntax.find_pattern"
        (str "The token \"" ++ str s ++ str "\" occurs on one side of \"..\" but not on the other side.")
  | _, [] ->
      user_err Pp.(str msg_expected_form_of_recursive_notation)
  | ((SProdList _ | NonTerminal _) :: _), _ | _, (SProdList _ :: _) ->
      anomaly (Pp.str "Only Terminal or Break expected on left, non-SProdList on right.")

let rec interp_list_parser hd = function
  | [] -> [], List.rev hd
  | NonTerminal id :: tl when Id.equal id ldots_var ->
      if List.is_empty hd then user_err Pp.(str msg_expected_form_of_recursive_notation);
      let hd = List.rev hd in
      let ((x,y,sl),tl') = find_pattern (List.hd hd) [] (List.tl hd,tl) in
      let xyl,tl'' = interp_list_parser [] tl' in
      (* We remember each pair of variable denoting a recursive part to *)
      (* remove the second copy of it afterwards *)
      (x,y)::xyl, SProdList (x,sl) :: tl''
  | (Terminal _ | Break _) as s :: tl ->
      if List.is_empty hd then
        let yl,tl' = interp_list_parser [] tl in
        yl, s :: tl'
      else
        interp_list_parser (s::hd) tl
  | NonTerminal _ as x :: tl ->
      let xyl,tl' = interp_list_parser [x] tl in
      xyl, List.rev_append hd tl'
  | SProdList _ :: _ -> anomaly (Pp.str "Unexpected SProdList in interp_list_parser.")


(* Find non-terminal tokens of notation *)

(* To protect alphabetic tokens and quotes from being seen as variables *)
let quote_notation_token x =
  let n = String.length x in
  let norm = CLexer.is_ident x in
  if (n > 0 && norm) || (n > 2 && x.[0] == '\'') then "'"^x^"'"
  else x

let is_numeral symbs =
  match List.filter (function Break _ -> false | _ -> true) symbs with
  | ([Terminal "-"; Terminal x] | [Terminal x]) ->
      (try let _ = Bigint.of_string x in true with Failure _ -> false)
  | _ ->
      false

let rec get_notation_vars onlyprint = function
  | [] -> []
  | NonTerminal id :: sl ->
      let vars = get_notation_vars onlyprint sl in
      if Id.equal id ldots_var then vars else
	(* don't check for nonlinearity if printing only, see Bug 5526 *)
	if not onlyprint && Id.List.mem id vars then 
	  user_err ~hdr:"Metasyntax.get_notation_vars"
            (str "Variable " ++ Id.print id ++ str " occurs more than once.")
	else id::vars
  | (Terminal _ | Break _) :: sl -> get_notation_vars onlyprint sl
  | SProdList _ :: _ -> assert false

let analyze_notation_tokens ~onlyprint ntn =
  let l = decompose_raw_notation ntn in
  let vars = get_notation_vars onlyprint l in
  let recvars,l = interp_list_parser [] l in
  recvars, List.subtract Id.equal vars (List.map snd recvars), l

let error_not_same_scope x y =
  user_err ~hdr:"Metasyntax.error_not_name_scope"
    (str "Variables " ++ Id.print x ++ str " and " ++ Id.print y ++ str " must be in the same scope.")

(**********************************************************************)
(* Build pretty-printing rules                                        *)

let pr_notation_entry = function
  | InConstrEntry -> str "constr"
  | InCustomEntry s -> str "custom " ++ str s

let prec_assoc = function
  | RightA -> (L,E)
  | LeftA -> (E,L)
  | NonA -> (L,L)

let precedence_of_position_and_level from_level = function
  | NumLevel n, BorderProd (_,None) -> n, Prec n
  | NumLevel n, BorderProd (b,Some a) ->
      n, let (lp,rp) = prec_assoc a in if b == Left then lp else rp
  | NumLevel n, InternalProd -> n, Prec n
  | NextLevel, _ -> from_level, L

let precedence_of_entry_type (from_custom,from_level) = function
  | ETConstr (custom,_,x) when notation_entry_eq custom from_custom ->
    precedence_of_position_and_level from_level x
  | ETConstr (custom,_,(NumLevel n,_)) -> n, Prec n
  | ETConstr (custom,_,(NextLevel,_)) ->
    user_err (strbrk "\"next level\" is only for sub-expressions in the same entry as where the notation is (" ++
              quote (pr_notation_entry custom) ++ strbrk " is different from " ++
              quote (pr_notation_entry from_custom) ++ str ").")
  | ETPattern (_,n) -> let n = match n with None -> 0 | Some n -> n in n, Prec n
  | _ -> 0, E (* should not matter *)

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
  let prec = snd (precedence_of_entry_type from x) in
  match x with
  | ETConstr _ | ETGlobal | ETBigint ->
     UnpMetaVar (i,prec)
  | ETPattern _ ->
     UnpBinderMetaVar (i,prec)
  | ETIdent ->
     UnpBinderMetaVar (i,prec)
  | ETBinder isopen ->
     assert false

(* Heuristics for building default printing rules *)

let index_id id l = List.index Id.equal id l

let make_hunks etyps symbols from =
  let vars,typs = List.split etyps in
  let rec make b = function
    | NonTerminal m :: prods ->
	let i = index_id m vars in
        let u = unparsing_metavar i from typs in
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
	let _,prec = precedence_of_entry_type from typ in
        let sl' =
          (* If no separator: add a break *)
	  if List.is_empty sl then add_break 1 []
          (* We add NonTerminal for simulation but remove it afterwards *)
          else make true sl in
	let hunk = match typ with
	  | ETConstr _ -> UnpListMetaVar (i,prec,List.map snd sl')
	  | ETBinder isopen ->
	      check_open_binder isopen sl m;
	      UnpBinderListMetaVar (i,isopen,List.map snd sl')
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

let skip_var_in_recursive_format = function
  | (_,UnpTerminal s) :: sl (* skip first var *) when not (List.for_all (fun c -> c = " ") (String.explode s)) ->
      (* To do, though not so important: check that the names match
         the names in the notation *)
      sl
  | (loc,_) :: _ -> error_not_same ?loc ()
  | [] -> assert false

let read_recursive_format sl fmt =
  (* Turn [[UnpTerminal s :: some-list @ UnpTerminal ".." :: same-some-list @ UnpTerminal s' :: rest] *)
  (* into [(some-list,rest)] *)
  let get_head fmt =
    let sl = skip_var_in_recursive_format fmt in
    try split_format_at_ldots [] sl with Exit -> error_not_same ?loc:(fst (List.last (if sl = [] then fmt else sl))) () in
  let rec get_tail = function
    | (loc,a) :: sepfmt, (_,b) :: fmt when Pervasives.(=) a b -> get_tail (sepfmt, fmt) (* FIXME *)
    | [], tail -> skip_var_in_recursive_format tail
    | (loc,_) :: _, ([] | (_,UnpTerminal _) :: _)-> error_not_same ?loc ()
    | _, (loc,_)::_ -> error_not_same ?loc () in
  let loc, slfmt, fmt = get_head fmt in
  slfmt, get_tail (slfmt, fmt)

let hunks_of_format (from,(vars,typs)) symfmt =
  let rec aux = function
  | symbs, (_,(UnpTerminal s' as u)) :: fmt
      when String.equal s' (String.make (String.length s') ' ') ->
      let symbs, l = aux (symbs,fmt) in symbs, u :: l
  | Terminal s :: symbs, (_,UnpTerminal s') :: fmt
      when String.equal s (String.drop_simple_quotes s') ->
      let symbs, l = aux (symbs,fmt) in symbs, UnpTerminal s :: l
  | NonTerminal s :: symbs, (_,UnpTerminal s') :: fmt when Id.equal s (Id.of_string s') ->
      let i = index_id s vars in
      let symbs, l = aux (symbs,fmt) in symbs, unparsing_metavar i from typs :: l
  | symbs, (_,UnpBox (a,b)) :: fmt ->
      let symbs', b' = aux (symbs,b) in
      let symbs', l = aux (symbs',fmt) in
      symbs', UnpBox (a,List.map (fun x -> (None,x)) b') :: l
  | symbs, (_,(UnpCut _ as u)) :: fmt ->
      let symbs, l = aux (symbs,fmt) in symbs, u :: l
  | SProdList (m,sl) :: symbs, fmt ->
      let i = index_id m vars in
      let typ = List.nth typs (i-1) in
      let _,prec = precedence_of_entry_type from typ in
      let loc_slfmt,rfmt = read_recursive_format sl fmt in
      let sl, slfmt = aux (sl,loc_slfmt) in
      if not (List.is_empty sl) then error_format ?loc:(find_prod_list_loc loc_slfmt fmt) ();
      let symbs, l = aux (symbs,rfmt) in
      let hunk = match typ with
	| ETConstr _ -> UnpListMetaVar (i,prec,slfmt)
	| ETBinder isopen ->
	    check_open_binder isopen sl m;
	    UnpBinderListMetaVar (i,isopen,slfmt)
	| _ -> assert false in
      symbs, hunk :: l
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

let rec define_keywords_aux = function
  | GramConstrNonTerminal(e,Some _) as n1 :: GramConstrTerminal(IDENT k) :: l
      when is_not_small_constr e ->
      Flags.if_verbose Feedback.msg_info (str "Identifier '" ++ str k ++ str "' now a keyword");
      CLexer.add_keyword k;
      n1 :: GramConstrTerminal(KEYWORD k) :: define_keywords_aux l
  | n :: l -> n :: define_keywords_aux l
  | [] -> []

  (* Ensure that IDENT articulation terminal symbols are keywords *)
let define_keywords = function
  | GramConstrTerminal(IDENT k)::l ->
      Flags.if_verbose Feedback.msg_info (str "Identifier '" ++ str k ++ str "' now a keyword");
      CLexer.add_keyword k;
      GramConstrTerminal(KEYWORD k) :: define_keywords_aux l
  | l -> define_keywords_aux l

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
  let tks = List.map (fun x -> GramConstrTerminal x) tkl in
  let rec aux i hds ll =
  if i < p then aux (i+1) (main :: tks @ hds) ll
  else if Int.equal i (p+n) then
    let hds =
      GramConstrListMark (p+n,true,p) :: hds
      @	[GramConstrNonTerminal (ETProdConstrList (typ,tkl), Some x)] in
    distribute hds ll
  else
    distribute (GramConstrListMark (i+1,false,p) :: hds @ [main]) ll @
       aux (i+1) (main :: tks @ hds) ll in
  aux 0 [] ll

let is_constr_typ typ x etyps =
  match List.assoc x etyps with
  | ETConstr (_,_,typ') -> typ = typ'
  | _ -> false

let include_possible_similar_trailing_pattern typ etyps sl l =
  let rec aux n = function
  | Terminal s :: sl, Terminal s'::l' when s = s' -> aux n (sl,l')
  | [], NonTerminal x ::l' when is_constr_typ typ x etyps -> try_aux n l'
  | _ -> raise Exit
  and try_aux n l =
    try aux (n+1) (sl,l)
    with Exit -> n,l in
  try_aux 0 l

let prod_entry_type = function
  | ETIdent -> ETProdName
  | ETGlobal -> ETProdReference
  | ETBigint -> ETProdBigint
  | ETBinder _ -> assert false (* See check_binder_type *)
  | ETConstr (s,_,p) -> ETProdConstr (s,p)
  | ETPattern (_,n) -> ETProdPattern (match n with None -> 0 | Some n -> n)

let make_production etyps symbols =
  let rec aux = function
    | [] -> [[]]
    | NonTerminal m :: l ->
        let typ = List.assoc m etyps in
        distribute [GramConstrNonTerminal (prod_entry_type typ, Some m)] (aux l)
    | Terminal s :: l ->
        distribute [GramConstrTerminal (CLexer.terminal s)] (aux l)
    | Break _ :: l ->
        aux l
    | SProdList (x,sl) :: l ->
        let tkl = List.flatten
          (List.map (function Terminal s -> [CLexer.terminal s]
            | Break _ -> []
            | _ -> anomaly (Pp.str "Found a non terminal token in recursive notation separator.")) sl) in
	match List.assoc x etyps with
        | ETConstr (s,_,typ) ->
            let p,l' = include_possible_similar_trailing_pattern typ etyps sl l in
            expand_list_rule s typ tkl x 1 p (aux l')
        | ETBinder o ->
            check_open_binder o sl x;
            let typ = if o then (assert (tkl = []); ETBinderOpen) else ETBinderClosed tkl in
            distribute
              [GramConstrNonTerminal (ETProdBinderList typ, Some x)] (aux l)
        | _ ->
           user_err Pp.(str "Components of recursive patterns in notation must be terms or binders.") in
  let prods = aux symbols in
  List.map define_keywords prods

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

let recompute_assoc typs =
  match border typs, border (List.rev typs) with
    | Some LeftA, Some RightA -> assert false
    | Some LeftA, _ -> Some LeftA
    | _, Some RightA -> Some RightA
    | _ -> None

(**************************************************************************)
(* Registration of syntax extensions (parsing/printing, no interpretation)*)

let pr_arg_level from (lev,typ) =
  let pplev = function
  | (n,L) when Int.equal n from -> str "at next level"
  | (n,E) -> str "at level " ++ int n
  | (n,L) -> str "at level below " ++ int n
  | (n,Prec m) when Int.equal m n -> str "at level " ++ int n
  | (n,_) -> str "Unknown level" in
  Ppvernac.pr_set_entry_type (fun _ -> (*TO CHECK*) mt()) typ ++
  (match typ with
   | ETConstr _ | ETPattern _ -> spc () ++ pplev lev
   | _ -> mt ())

let pr_level ntn (from,fromlevel,args,typs) =
  (match from with InConstrEntry -> mt () | InCustomEntry s -> str "in " ++ str s ++ spc()) ++
  str "at level " ++ int fromlevel ++ spc () ++ str "with arguments" ++ spc() ++
  prlist_with_sep pr_comma (pr_arg_level fromlevel) (List.combine args typs)

let error_incompatible_level ntn oldprec prec =
  user_err 
    (str "Notation " ++ pr_notation ntn ++ str " is already defined" ++ spc() ++
    pr_level ntn oldprec ++
    spc() ++ str "while it is now required to be" ++ spc() ++
    pr_level ntn prec ++ str ".")

let error_parsing_incompatible_level ntn ntn' oldprec prec =
  user_err
    (str "Notation " ++ pr_notation ntn ++ str " relies on a parsing rule for " ++ pr_notation ntn' ++ spc() ++
    str " which is already defined" ++ spc() ++
    pr_level ntn oldprec ++
    spc() ++ str "while it is now required to be" ++ spc() ++
    pr_level ntn prec ++ str ".")

type syntax_extension = {
  synext_level : Notation_gram.level;
  synext_notation : notation;
  synext_notgram : notation_grammar;
  synext_unparsing : unparsing list;
  synext_extra : (string * string) list;
  synext_compat : Flags.compat_version option;
}

let is_active_compat = function
| None -> true
| Some v -> 0 <= Flags.version_compare v !Flags.compat_version

type syntax_extension_obj = locality_flag * syntax_extension

let check_and_extend_constr_grammar ntn rule =
  try
    let ntn_for_grammar = rule.notgram_notation in
    if notation_eq ntn ntn_for_grammar then raise Not_found;
    let prec = rule.notgram_level in
    let oldprec = Notgram_ops.level_of_notation ntn_for_grammar in
    if not (Notgram_ops.level_eq prec oldprec) then error_parsing_incompatible_level ntn ntn_for_grammar oldprec prec;
  with Not_found ->
    Egramcoq.extend_constr_grammar rule

let cache_one_syntax_extension se =
  let ntn = se.synext_notation in
  let prec = se.synext_level in
  let onlyprint = se.synext_notgram.notgram_onlyprinting in
  try
    let oldprec = Notgram_ops.level_of_notation ~onlyprint ntn in
    if not (Notgram_ops.level_eq prec oldprec) then error_incompatible_level ntn oldprec prec;
  with Not_found ->
    if is_active_compat se.synext_compat then begin
      (* Reserve the notation level *)
      Notgram_ops.declare_notation_level ntn prec ~onlyprint;
      (* Declare the parsing rule *)
      if not onlyprint then List.iter (check_and_extend_constr_grammar ntn) se.synext_notgram.notgram_rules;
      (* Declare the notation rule *)
      declare_notation_rule ntn
        ~extra:se.synext_extra (se.synext_unparsing, let (_,lev,_,_) = prec in lev) se.synext_notgram
    end

let cache_syntax_extension (_, (_, sy)) =
  cache_one_syntax_extension sy

let subst_parsing_rule subst x = x

let subst_printing_rule subst x = x

let subst_syntax_extension (subst, (local, sy)) =
  (local, { sy with
    synext_notgram = { sy.synext_notgram with notgram_rules = List.map (subst_parsing_rule subst) sy.synext_notgram.notgram_rules };
    synext_unparsing = subst_printing_rule subst sy.synext_unparsing;
  })

let classify_syntax_definition (local, _ as o) =
  if local then Dispose else Substitute o

let inSyntaxExtension : syntax_extension_obj -> obj =
  declare_object {(default_object "SYNTAX-EXTENSION") with
       open_function = (fun i o -> if Int.equal i 1 then cache_syntax_extension o);
       cache_function = cache_syntax_extension;
       subst_function = subst_syntax_extension;
       classify_function = classify_syntax_definition}

(**************************************************************************)
(* Precedences                                                            *)

(* Interpreting user-provided modifiers *)

(* XXX: We could move this to the parser itself *)
module NotationMods = struct

type notation_modifier = {
  assoc         : gram_assoc option;
  level         : int option;
  custom        : notation_entry;
  etyps         : (Id.t * simple_constr_prod_entry_key) list;
  subtyps       : (Id.t * production_level) list;

  (* common to syn_data below *)
  only_parsing  : bool;
  only_printing : bool;
  compat        : Flags.compat_version option;
  format        : lstring option;
  extra         : (string * string) list;
}

let default = {
  assoc         = None;
  level         = None;
  custom        = InConstrEntry;
  etyps         = [];
  subtyps       = [];
  only_parsing  = false;
  only_printing = false;
  compat        = None;
  format        = None;
  extra         = [];
}

end

let interp_modifiers modl = let open NotationMods in
  let rec interp subtyps acc = function
    | [] -> subtyps, acc
    | SetEntryType (s,typ) :: l ->
	let id = Id.of_string s in
	if Id.List.mem_assoc id acc.etyps then
	  user_err ~hdr:"Metasyntax.interp_modifiers"
            (str s ++ str " is already assigned to an entry or constr level.");
        interp subtyps { acc with etyps = (id,typ) :: acc.etyps; } l
    | SetItemLevel ([],bko,n) :: l ->
        interp subtyps acc l
    | SetItemLevel (s::idl,bko,n) :: l ->
	let id = Id.of_string s in
	if Id.List.mem_assoc id acc.etyps then
	  user_err ~hdr:"Metasyntax.interp_modifiers"
            (str s ++ str " is already assigned to an entry or constr level.");
        interp ((id,bko,n)::subtyps) acc (SetItemLevel (idl,bko,n)::l)
    | SetLevel n :: l ->
        (match acc.custom with
        | InCustomEntry s ->
          if acc.level <> None then
            user_err (str ("isolated \"at level " ^ string_of_int n ^ "\" unexpected."))
          else
            user_err (str ("use \"in custom " ^ s ^ " at level " ^ string_of_int n ^
                         "\"") ++ spc () ++ str "rather than" ++ spc () ++
                         str ("\"at level " ^ string_of_int n ^ "\"") ++
                         spc () ++ str "isolated.")
        | InConstrEntry ->
          if acc.level <> None then
            user_err (str "A level is already assigned.");
          interp subtyps { acc with level = Some n; } l)
    | SetCustomEntry (s,n) :: l ->
        if acc.level <> None then
          (if n = None then
            user_err (str ("use \"in custom " ^ s ^ " at level " ^
                         string_of_int (Option.get acc.level) ^
                         "\"") ++ spc () ++ str "rather than" ++ spc () ++
                         str ("\"at level " ^
                         string_of_int (Option.get acc.level) ^ "\"") ++
                         spc () ++ str "isolated.")
          else
            user_err (str ("isolated \"at level " ^ string_of_int (Option.get acc.level) ^ "\" unexpected.")));
        if acc.custom <> InConstrEntry then
           user_err (str "Entry is already assigned to custom " ++ str s ++ (match acc.level with None -> mt () | Some lev -> str " at level " ++ int lev) ++ str ".");
        interp subtyps { acc with custom = InCustomEntry s; level = n } l
    | SetAssoc a :: l ->
	if not (Option.is_empty acc.assoc) then user_err Pp.(str "An associativity is given more than once.");
        interp subtyps { acc with assoc = Some a; } l
     | SetOnlyParsing :: l ->
        interp subtyps { acc with only_parsing = true; } l
    | SetOnlyPrinting :: l ->
        interp subtyps { acc with only_printing = true; } l
    | SetCompatVersion v :: l ->
        interp subtyps { acc with compat = Some v; } l
    | SetFormat ("text",s) :: l ->
	if not (Option.is_empty acc.format) then user_err Pp.(str "A format is given more than once.");
        interp subtyps { acc with format = Some s; } l
    | SetFormat (k,s) :: l ->
        interp subtyps { acc with extra = (k,s.CAst.v)::acc.extra; } l
  in
  let subtyps,mods = interp [] default modl in
  (* interpret item levels wrt to main entry *)
  let extra_etyps = List.map (fun (id,bko,n) -> (id,ETConstr (mods.custom,bko,n))) subtyps in
  { mods with etyps = extra_etyps@mods.etyps }

let check_infix_modifiers modifiers =
  let mods = interp_modifiers modifiers in
  let t = mods.NotationMods.etyps in
  let u = mods.NotationMods.subtyps in
  if not (List.is_empty t) || not (List.is_empty u) then
    user_err Pp.(str "Explicit entry level or type unexpected in infix notation.")

let check_useless_entry_types recvars mainvars etyps =
  let vars = let (l1,l2) = List.split recvars in l1@l2@mainvars in
  match List.filter (fun (x,etyp) -> not (List.mem x vars)) etyps with
  | (x,_)::_ -> user_err ~hdr:"Metasyntax.check_useless_entry_types"
                  (Id.print x ++ str " is unbound in the notation.")
  | _ -> ()

let check_binder_type recvars etyps =
  let l1,l2 = List.split recvars in
  let l = l1@l2 in
  List.iter (function
    | (x,ETBinder b) when not (List.mem x l) ->
       CErrors.user_err (str (if b then "binder" else "closed binder") ++
                 strbrk " is only for use in recursive notations for binders.")
    | _ -> ()) etyps

let not_a_syntax_modifier = function
| SetOnlyParsing -> true
| SetOnlyPrinting -> true
| SetCompatVersion _ -> true
| _ -> false

let no_syntax_modifiers mods = List.for_all not_a_syntax_modifier mods

let is_only_parsing mods =
  let test = function SetOnlyParsing -> true | _ -> false in
  List.exists test mods

let is_only_printing mods =
  let test = function SetOnlyPrinting -> true | _ -> false in
  List.exists test mods

let get_compat_version mods =
  let test = function SetCompatVersion v -> Some v | _ -> None in
  try Some (List.find_map test mods) with Not_found -> None

(* Compute precedences from modifiers (or find default ones) *)

let set_entry_type from etyps (x,typ) =
  let typ = try
    match List.assoc x etyps, typ with
      | ETConstr (s,bko,Some n), (_,BorderProd (left,_)) ->
          ETConstr (s,bko,(n,BorderProd (left,None)))
      | ETConstr (s,bko,Some n), (_,InternalProd) ->
         ETConstr (s,bko,(n,InternalProd))
      | ETPattern (b,n), _ -> ETPattern (b,n)
      | (ETIdent | ETBigint | ETGlobal | ETBinder _ as x), _ -> x
      | ETConstr (s,bko,None), _ -> ETConstr (s,bko,typ)
    with Not_found ->
      ETConstr (from,None,typ)
  in (x,typ)

let join_auxiliary_recursive_types recvars etyps =
  List.fold_right (fun (x,y) typs ->
    let xtyp = try Some (List.assoc x etyps) with Not_found -> None in
    let ytyp = try Some (List.assoc y etyps) with Not_found -> None in
    match xtyp,ytyp with
    | None, None -> typs
    | Some _, None -> typs
    | None, Some ytyp -> (x,ytyp)::typs
    | Some xtyp, Some ytyp when Pervasives.(=) xtyp ytyp -> typs (* FIXME *)
    | Some xtyp, Some ytyp ->
	user_err 
	  (strbrk "In " ++ Id.print x ++ str " .. " ++ Id.print y ++
	   strbrk ", both ends have incompatible types."))
    recvars etyps

let internalization_type_of_entry_type = function
  | ETBinder _ -> NtnInternTypeOnlyBinder
  | ETConstr _ | ETBigint | ETGlobal
  | ETIdent | ETPattern _ -> NtnInternTypeAny

let set_internalization_type typs =
  List.map (fun (_, e) -> internalization_type_of_entry_type e) typs

let make_internalization_vars recvars mainvars typs =
  let maintyps = List.combine mainvars typs in
  let extratyps = List.map (fun (x,y) -> (y,List.assoc x maintyps)) recvars in
  maintyps @ extratyps

let make_interpretation_type isrec isonlybinding = function
  (* Parsed as constr list *)
  | ETConstr (_,None,_) when isrec -> NtnTypeConstrList
  (* Parsed as constr, but interpreted as a binder: default is to parse it as an ident only *)
  | ETConstr (_,Some bk,_) -> NtnTypeBinder (NtnBinderParsedAsConstr bk)
  | ETConstr (_,None,_) when isonlybinding -> NtnTypeBinder (NtnBinderParsedAsConstr AsIdent)
  (* Parsed as constr, interpreted as constr *)
  | ETConstr (_,None,_) -> NtnTypeConstr
  (* Others *)
  | ETIdent -> NtnTypeBinder NtnParsedAsIdent
  | ETPattern (ppstrict,_) -> NtnTypeBinder (NtnParsedAsPattern ppstrict) (* Parsed as ident/pattern, primarily interpreted as binder; maybe strict at printing *)
  | ETBigint | ETGlobal -> NtnTypeConstr
  | ETBinder _ ->
     if isrec then NtnTypeBinderList
     else anomaly Pp.(str "Type binder is only for use in recursive notations for binders.")

let subentry_of_constr_prod_entry = function
  | ETConstr (InCustomEntry s,_,(NumLevel n,_)) -> InCustomEntryLevel (s,n)
  (* level and use of parentheses for coercion is hard-wired for "constr";
     we don't remember the level *)
  | ETConstr (InConstrEntry,_,_) -> InConstrEntrySomeLevel
  | _ -> InConstrEntrySomeLevel

let make_interpretation_vars recvars allvars typs =
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
    ((subentry_of_constr_prod_entry typ,sc),
     make_interpretation_type (Id.List.mem_assoc x recvars) isonlybinding typ)) mainvars

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

let make_custom_entry custom level =
  match custom with
  | InConstrEntry -> InConstrEntrySomeLevel
  | InCustomEntry s -> InCustomEntryLevel (s,level)

type entry_coercion_kind =
  | IsEntryCoercion of notation_entry_level
  | IsEntryGlobal of string * int
  | IsEntryIdent of string * int

let is_coercion = function
  | Some (custom,n,_,[e]) ->
     (match e, custom with
     | ETConstr _, _ ->
         let customkey = make_custom_entry custom n in
         let subentry = subentry_of_constr_prod_entry e in
         if notation_entry_level_eq subentry customkey then None
         else Some (IsEntryCoercion subentry)
     | ETGlobal, InCustomEntry s -> Some (IsEntryGlobal (s,n))
     | ETIdent, InCustomEntry s -> Some (IsEntryIdent (s,n))
     | _ -> None)
  | Some _ -> assert false
  | None -> None

let printability level onlyparse reversibility = function
| NVar _ when reversibility = APrioriReversible ->
  let coe = is_coercion level in
  if not onlyparse && coe = None then
    warn_notation_bound_to_variable ();
  true, coe
| _ ->
   (if not onlyparse && reversibility <> APrioriReversible then
     (warn_non_reversible_notation reversibility; true)
    else onlyparse),None

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
        | ETConstr (s,_,Some _), s' when s = s' -> test ()
        | (ETIdent | ETBigint | ETGlobal), _ ->
            begin match lev with
            | None ->
	      ([Feedback.msg_info ?loc:None ,strbrk "Setting notation at level 0."],0)
            | Some 0 ->
              ([],0)
            | _ ->
              user_err Pp.(str "A notation starting with an atomic expression must be at level 0.")
            end
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
	([Feedback.msg_info ?loc:None ,strbrk "Setting notation at level 0."], 0)
      else [],Option.get lev
  | Some _ ->
      if Option.is_empty lev then user_err Pp.(str "Cannot determine the level.");
      [],Option.get lev

let check_curly_brackets_notation_exists () =
  try let _ = Notgram_ops.level_of_notation (InConstrEntrySomeLevel,"{ _ }") in ()
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

module SynData = struct

  type subentry_types = (Id.t * constr_entry_key) list

  (* XXX: Document *)
  type syn_data = {

    (* Notation name and location *)
    info          : notation * notation_location;

    (* Fields coming from the vernac-level modifiers *)
    only_parsing  : bool;
    only_printing : bool;
    compat        : Flags.compat_version option;
    format        : lstring option;
    extra         : (string * string) list;

    (* XXX: Callback to printing, must remove *)
    msgs          : ((Pp.t -> unit) * Pp.t) list;

    (* Fields for internalization *)
    recvars       : (Id.t * Id.t) list;
    mainvars      : Id.List.elt list;
    intern_typs   : notation_var_internalization_type list;

    (* Notation data for parsing *)
    level         : level;
    pa_syntax_data : subentry_types * symbol list;
    pp_syntax_data : subentry_types * symbol list;
    not_data      : notation *                   (* notation *)
                    level *                      (* level, precedence, types *)
                    bool;                        (* needs_squash *)
  }

end

let find_subentry_types from n assoc etyps symbols =
  let innerlevel = NumLevel 200 in
  let typs =
    find_symbols
      (NumLevel n,BorderProd(Left,assoc))
      (innerlevel,InternalProd)
      (NumLevel n,BorderProd(Right,assoc))
      symbols in
  let sy_typs = List.map (set_entry_type from etyps) typs in
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

let compute_syntax_data local df modifiers =
  let open SynData in
  let open NotationMods in
  let mods = interp_modifiers modifiers in
  let onlyprint = mods.only_printing in
  let onlyparse = mods.only_parsing in
  if onlyprint && onlyparse then user_err (str "A notation cannot be both 'only printing' and 'only parsing'.");
  let assoc = Option.append mods.assoc (Some NonA) in
  let (recvars,mainvars,symbols) = analyze_notation_tokens ~onlyprint df in
  let _ = check_useless_entry_types recvars mainvars mods.etyps in
  let _ = check_binder_type recvars mods.etyps in

  (* Notations for interp and grammar  *)
  let msgs,n = find_precedence mods.custom mods.level mods.etyps symbols onlyprint in
  let custom = make_custom_entry mods.custom n in
  let ntn_for_interp = make_notation_key custom symbols in
  let symbols_for_grammar =
    if custom = InConstrEntrySomeLevel then remove_curly_brackets symbols else symbols in
  let need_squash = not (List.equal Notation.symbol_eq symbols symbols_for_grammar) in
  let ntn_for_grammar = if need_squash then make_notation_key custom symbols_for_grammar else ntn_for_interp in
  if mods.custom = InConstrEntry && not onlyprint then check_rule_productivity symbols_for_grammar;
  (* To globalize... *)
  let etyps = join_auxiliary_recursive_types recvars mods.etyps in
  let sy_typs, prec =
    find_subentry_types mods.custom n assoc etyps symbols in
  let sy_typs_for_grammar, prec_for_grammar =
    if need_squash then
      find_subentry_types mods.custom n assoc etyps symbols_for_grammar
    else
      sy_typs, prec in
  let i_typs = set_internalization_type sy_typs in
  check_locality_compatibility local mods.custom sy_typs;
  let pa_sy_data = (sy_typs_for_grammar,symbols_for_grammar) in
  let pp_sy_data = (sy_typs,symbols) in
  let sy_fulldata = (ntn_for_grammar,(mods.custom,n,prec_for_grammar,List.map snd sy_typs_for_grammar),need_squash) in
  let df' = ((Lib.library_dp(),Lib.current_dirpath true),df) in
  let i_data = ntn_for_interp, df' in

  (* Return relevant data for interpretation and for parsing/printing *)
  { info = i_data;

    only_parsing  = mods.only_parsing;
    only_printing = mods.only_printing;
    compat        = mods.compat;
    format        = mods.format;
    extra         = mods.extra;

    msgs;

    recvars;
    mainvars;
    intern_typs = i_typs;

    level  = (mods.custom,n,prec,List.map snd sy_typs);
    pa_syntax_data = pa_sy_data;
    pp_syntax_data = pp_sy_data;
    not_data    = sy_fulldata;
  }

let compute_pure_syntax_data local df mods =
  let open SynData in
  let sd = compute_syntax_data local df mods in
  let msgs =
    if sd.only_parsing then
      (Feedback.msg_warning ?loc:None,
      strbrk "The only parsing modifier has no effect in Reserved Notation.")::sd.msgs
    else sd.msgs in
  { sd with msgs }

(**********************************************************************)
(* Registration of notations interpretation                            *)

type notation_obj = {
  notobj_local : bool;
  notobj_scope : scope_name option;
  notobj_interp : interpretation;
  notobj_coercion : entry_coercion_kind option;
  notobj_onlyparse : bool;
  notobj_onlyprint : bool;
  notobj_compat : Flags.compat_version option;
  notobj_notation : notation * notation_location;
}

let load_notation _ (_, nobj) =
  Option.iter Notation.declare_scope nobj.notobj_scope

let open_notation i (_, nobj) =
  let scope = nobj.notobj_scope in
  let (ntn, df) = nobj.notobj_notation in
  let pat = nobj.notobj_interp in
  let onlyprint = nobj.notobj_onlyprint  in
  let fresh = not (Notation.exists_notation_in_scope scope ntn onlyprint pat) in
  let active = is_active_compat nobj.notobj_compat in
  if Int.equal i 1 && fresh && active then begin
    (* Declare the interpretation *)
    let () = Notation.declare_notation_interpretation ntn scope pat df ~onlyprint in
    (* Declare the uninterpretation *)
    if not nobj.notobj_onlyparse then
      Notation.declare_uninterpretation (NotationRule (scope, ntn)) pat;
    (* Declare a possible coercion *)
    (match nobj.notobj_coercion with
    | Some (IsEntryCoercion entry) -> Notation.declare_entry_coercion ntn entry
    | Some (IsEntryGlobal (entry,n)) -> Notation.declare_custom_entry_has_global entry n
    | Some (IsEntryIdent (entry,n)) -> Notation.declare_custom_entry_has_ident entry n
    | None -> ())
  end

let cache_notation o =
  load_notation 1 o;
  open_notation 1 o

let subst_notation (subst, nobj) =
  { nobj with notobj_interp = subst_interpretation subst nobj.notobj_interp; }

let classify_notation nobj =
  if nobj.notobj_local then Dispose else Substitute nobj

let inNotation : notation_obj -> obj =
  declare_object {(default_object "NOTATION") with
       open_function = open_notation;
       cache_function = cache_notation;
       subst_function = subst_notation;
       load_function = load_notation;
       classify_function = classify_notation}

(**********************************************************************)

let with_lib_stk_protection f x =
  let fs = Lib.freeze ~marshallable:`No in
  try let a = f x in Lib.unfreeze fs; a
  with reraise ->
    let reraise = CErrors.push reraise in
    let () = Lib.unfreeze fs in
    iraise reraise

let with_syntax_protection f x =
  with_lib_stk_protection
    (Pcoq.with_grammar_rule_protection
       (with_notation_protection f)) x

(**********************************************************************)
(* Recovering existing syntax                                         *)

exception NoSyntaxRule

let recover_notation_syntax ntn =
  try
    let prec = Notgram_ops.level_of_notation ~onlyprint:true ntn (* Be as little restrictive as possible *) in
    let pp_rule,_ = find_notation_printing_rule ntn in
    let pp_extra_rules = find_notation_extra_printing_rules ntn in
    let pa_rule = find_notation_parsing_rules ntn in
    { synext_level = prec;
      synext_notation = ntn;
      synext_notgram = pa_rule;
      synext_unparsing = pp_rule;
      synext_extra = pp_extra_rules;
      synext_compat = None;
    }
  with Not_found ->
    raise NoSyntaxRule

let recover_squash_syntax sy =
  let sq = recover_notation_syntax (InConstrEntrySomeLevel,"{ _ }") in
  sy :: sq.synext_notgram.notgram_rules

(**********************************************************************)
(* Main entry point for building parsing and printing rules           *)

let make_pa_rule level (typs,symbols) ntn need_squash =
  let assoc = recompute_assoc typs in
  let prod = make_production typs symbols in
  let sy = {
    notgram_level = level;
    notgram_assoc = assoc;
    notgram_notation = ntn;
    notgram_prods = prod;
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
     hunks_of_format (level, List.split typs) (symbols, parse_format fmt)

(* let make_syntax_rules i_typs (ntn,prec,need_squash) sy_data fmt extra onlyprint compat = *)
let make_syntax_rules (sd : SynData.syn_data) = let open SynData in
  let ntn_for_grammar, prec_for_grammar, need_squash = sd.not_data in
  let custom,level,_,_ = sd.level in
  let pa_rule = make_pa_rule prec_for_grammar sd.pa_syntax_data ntn_for_grammar need_squash in
  let pp_rule = make_pp_rule (custom,level) sd.pp_syntax_data sd.format in {
    synext_level    = sd.level;
    synext_notation = fst sd.info;
    synext_notgram  = { notgram_onlyprinting = sd.only_printing; notgram_rules = pa_rule };
    synext_unparsing = pp_rule;
    synext_extra  = sd.extra;
    synext_compat = sd.compat;
  }

(**********************************************************************)
(* Main functions about notations                                     *)

let to_map l =
  let fold accu (x, v) = Id.Map.add x v accu in
  List.fold_left fold Id.Map.empty l

let add_notation_in_scope local df env c mods scope =
  let open SynData in
  let sd = compute_syntax_data local df mods in
  (* Prepare the interpretation *)
  (* Prepare the parsing and printing rules *)
  let sy_rules = make_syntax_rules sd in
  let i_vars = make_internalization_vars sd.recvars sd.mainvars sd.intern_typs in
  let nenv = {
    ninterp_var_type = to_map i_vars;
    ninterp_rec_vars = to_map sd.recvars;
  } in
  let (acvars, ac, reversibility) = interp_notation_constr env nenv c in
  let interp = make_interpretation_vars sd.recvars acvars (fst sd.pa_syntax_data) in
  let map (x, _) = try Some (x, Id.Map.find x interp) with Not_found -> None in
  let onlyparse,coe = printability (Some sd.level) sd.only_parsing reversibility ac in
  let notation = {
    notobj_local = local;
    notobj_scope = scope;
    notobj_interp = (List.map_filter map i_vars, ac);
    (** Order is important here! *)
    notobj_onlyparse = onlyparse;
    notobj_coercion = coe;
    notobj_onlyprint = sd.only_printing;
    notobj_compat = sd.compat;
    notobj_notation = sd.info;
  } in
  (* Ready to change the global state *)
  Flags.if_verbose (List.iter (fun (f,x) -> f x)) sd.msgs;
  Lib.add_anonymous_leaf (inSyntaxExtension (local, sy_rules));
  Lib.add_anonymous_leaf (inNotation notation);
  sd.info

let add_notation_interpretation_core local df env ?(impls=empty_internalization_env) c scope onlyparse onlyprint compat =
  let (recvars,mainvars,symbs) = analyze_notation_tokens ~onlyprint df in
  (* Recover types of variables and pa/pp rules; redeclare them if needed *)
  let level, i_typs, onlyprint = if not (is_numeral symbs) then begin
    let sy = recover_notation_syntax (make_notation_key InConstrEntrySomeLevel symbs) in
    let () = Lib.add_anonymous_leaf (inSyntaxExtension (local,sy)) in
    (** If the only printing flag has been explicitly requested, put it back *)
    let onlyprint = onlyprint || sy.synext_notgram.notgram_onlyprinting in
    let _,_,_,typs = sy.synext_level in
    Some sy.synext_level, typs, onlyprint
  end else None, [], false in
  (* Declare interpretation *)
  let path = (Lib.library_dp(), Lib.current_dirpath true) in
  let df'  = (make_notation_key InConstrEntrySomeLevel symbs, (path,df)) in
  let i_vars = make_internalization_vars recvars mainvars (List.map internalization_type_of_entry_type i_typs) in
  let nenv = {
    ninterp_var_type = to_map i_vars;
    ninterp_rec_vars = to_map recvars;
  } in
  let (acvars, ac, reversibility) = interp_notation_constr env ~impls nenv c in
  let interp = make_interpretation_vars recvars acvars (List.combine mainvars i_typs) in
  let map (x, _) = try Some (x, Id.Map.find x interp) with Not_found -> None in
  let onlyparse,coe = printability level onlyparse reversibility ac in
  let notation = {
    notobj_local = local;
    notobj_scope = scope;
    notobj_interp = (List.map_filter map i_vars, ac);
    (** Order is important here! *)
    notobj_onlyparse = onlyparse;
    notobj_coercion = coe;
    notobj_onlyprint = onlyprint;
    notobj_compat = compat;
    notobj_notation = df';
  } in
  Lib.add_anonymous_leaf (inNotation notation);
  df'

(* Notations without interpretation (Reserved Notation) *)

let add_syntax_extension local ({CAst.loc;v=df},mods) = let open SynData in
  let psd = compute_pure_syntax_data local df mods in
  let sy_rules = make_syntax_rules {psd with compat = None} in
  Flags.if_verbose (List.iter (fun (f,x) -> f x)) psd.msgs;
  Lib.add_anonymous_leaf (inSyntaxExtension(local,sy_rules))

(* Notations with only interpretation *)

let add_notation_interpretation env ({CAst.loc;v=df},c,sc) =
  let df' = add_notation_interpretation_core false df env c sc false false None in
  Dumpglob.dump_notation (loc,df') sc true

let set_notation_for_interpretation env impls ({CAst.v=df},c,sc) =
  (try ignore
    (Flags.silently (fun () -> add_notation_interpretation_core false df env ~impls c sc false false None) ());
  with NoSyntaxRule ->
    user_err Pp.(str "Parsing rule for this notation has to be previously declared."));
  Option.iter (fun sc -> Notation.open_close_scope (false,true,sc)) sc

(* Main entry point *)

let add_notation local env c ({CAst.loc;v=df},modifiers) sc =
  let df' =
   if no_syntax_modifiers modifiers then
    (* No syntax data: try to rely on a previously declared rule *)
    let onlyparse = is_only_parsing modifiers in
    let onlyprint = is_only_printing modifiers in
    let compat = get_compat_version modifiers in
    try add_notation_interpretation_core local df env c sc onlyparse onlyprint compat
    with NoSyntaxRule ->
      (* Try to determine a default syntax rule *)
      add_notation_in_scope local df env c modifiers sc
   else
    (* Declare both syntax and interpretation *)
    add_notation_in_scope local df env c modifiers sc
  in
  Dumpglob.dump_notation (loc,df') sc true

let add_notation_extra_printing_rule df k v =
  let notk = 
    let _,_, symbs = analyze_notation_tokens ~onlyprint:true df in
    make_notation_key InConstrEntrySomeLevel symbs in
  add_notation_extra_printing_rule notk k v

(* Infix notations *)

let inject_var x = CAst.make @@ CRef (qualid_of_ident (Id.of_string x),None)

let add_infix local env ({CAst.loc;v=inf},modifiers) pr sc =
  check_infix_modifiers modifiers;
  (* check the precedence *)
  let metas = [inject_var "x"; inject_var "y"] in
  let c = mkAppC (pr,metas) in
  let df = CAst.make ?loc @@ "x "^(quote_notation_token inf)^" y" in
  add_notation local env c (df,modifiers) sc

(**********************************************************************)
(* Delimiters and classes bound to scopes                             *)

type scope_command =
  | ScopeDelim of string
  | ScopeClasses of scope_class list
  | ScopeRemove

let load_scope_command _ (_,(scope,dlm)) =
  Notation.declare_scope scope

let open_scope_command i (_,(scope,o)) =
  if Int.equal i 1 then
    match o with
    | ScopeDelim dlm -> Notation.declare_delimiters scope dlm
    | ScopeClasses cl -> List.iter (Notation.declare_scope_class scope) cl
    | ScopeRemove -> Notation.remove_delimiters scope

let cache_scope_command o =
  load_scope_command 1 o;
  open_scope_command 1 o

let subst_scope_command (subst,(scope,o as x)) = match o with
  | ScopeClasses cl ->
      let cl' = List.map_filter (subst_scope_class subst) cl in
      let cl' =
        if List.for_all2eq (==) cl cl' then cl
        else cl' in
      scope, ScopeClasses cl'
  | _ -> x

let inScopeCommand : scope_name * scope_command -> obj =
  declare_object {(default_object "DELIMITERS") with
      cache_function = cache_scope_command;
      open_function = open_scope_command;
      load_function = load_scope_command;
      subst_function = subst_scope_command;
      classify_function = (fun obj -> Substitute obj)}

let add_delimiters scope key =
  Lib.add_anonymous_leaf (inScopeCommand(scope,ScopeDelim key))

let remove_delimiters scope =
  Lib.add_anonymous_leaf (inScopeCommand(scope,ScopeRemove))

let add_class_scope scope cl =
  Lib.add_anonymous_leaf (inScopeCommand(scope,ScopeClasses cl))

(* Check if abbreviation to a name and avoid early insertion of
   maximal implicit arguments *)
let try_interp_name_alias = function
  | [], { CAst.v = CRef (ref,_) } -> intern_reference ref
  | _ -> raise Not_found

let add_syntactic_definition env ident (vars,c) local onlyparse =
  let vars,reversibility,pat =
    try [], APrioriReversible, NRef (try_interp_name_alias (vars,c))
    with Not_found ->
      let fold accu id = Id.Map.add id NtnInternTypeAny accu in
      let i_vars = List.fold_left fold Id.Map.empty vars in
      let nenv = {
        ninterp_var_type = i_vars;
        ninterp_rec_vars = Id.Map.empty;
      } in
      let nvars, pat, reversibility = interp_notation_constr env nenv c in
      let map id = let (_,sc) = Id.Map.find id nvars in (id, sc) in
      List.map map vars, reversibility, pat
  in
  let onlyparse = match onlyparse with
    | None when fst (printability None false reversibility pat) -> Some Flags.Current
    | p -> p
  in
  Syntax_def.declare_syntactic_definition local ident onlyparse (vars,pat)

(**********************************************************************)
(* Declaration of custom entry                                        *)

let load_custom_entry _ _ = ()

let open_custom_entry _ (_,(local,s)) =
  Egramcoq.create_custom_entry ~local s

let cache_custom_entry o =
  load_custom_entry 1 o;
  open_custom_entry 1 o

let subst_custom_entry (subst,x) = x

let classify_custom_entry (local,s as o) =
  if local then Dispose else Substitute o

let inCustomEntry : locality_flag * string -> obj =
  declare_object {(default_object "CUSTOM-ENTRIES") with
      cache_function = cache_custom_entry;
      open_function = open_custom_entry;
      load_function = load_custom_entry;
      subst_function = subst_custom_entry;
      classify_function = classify_custom_entry}

let declare_custom_entry local s =
  Lib.add_anonymous_leaf (inCustomEntry (local,s))
