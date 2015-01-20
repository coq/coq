(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Flags
open Errors
open Util
open Names
open Constrexpr
open Constrexpr_ops
open Notation_term
open Notation_ops
open Ppextend
open Extend
open Libobject
open Constrintern
open Vernacexpr
open Pcoq
open Libnames
open Tok
open Egramml
open Egramcoq
open Notation
open Nameops

(**********************************************************************)
(* Tokens                                                             *)

let cache_token (_,s) = Lexer.add_keyword s

let inToken : string -> obj =
  declare_object {(default_object "TOKEN") with
       open_function = (fun i o -> if Int.equal i 1 then cache_token o);
       cache_function = cache_token;
       subst_function = Libobject.ident_subst_function;
       classify_function = (fun o -> Substitute o)}

let add_token_obj s = Lib.add_anonymous_leaf (inToken s)

(**********************************************************************)
(* Tactic Notation                                                    *)

let interp_prod_item lev = function
  | TacTerm s -> GramTerminal s
  | TacNonTerm (loc, nt, po) ->
      let sep = match po with Some (_,sep) -> sep | _ -> "" in
      let (etyp, e) = interp_entry_name true (Some lev) nt sep in
      GramNonTerminal (loc, etyp, e, Option.map fst po)

let make_terminal_status = function
  | GramTerminal s -> Some s
  | GramNonTerminal _ -> None

let rec make_tags = function
  | GramTerminal s :: l -> make_tags l
  | GramNonTerminal (loc, etyp, _, po) :: l -> etyp :: make_tags l
  | [] -> []

type tactic_grammar_obj = {
  tacobj_local : locality_flag;
  tacobj_tacgram : tactic_grammar;
  tacobj_tacpp : Pptactic.pp_tactic;
  tacobj_body : Tacexpr.glob_tactic_expr
}

let cache_tactic_notation ((_, key), tobj) =
  Tacenv.register_alias key tobj.tacobj_body;
  Egramcoq.extend_tactic_grammar key tobj.tacobj_tacgram;
  Pptactic.declare_notation_tactic_pprule key tobj.tacobj_tacpp

let open_tactic_notation i ((_, key), tobj) =
  if Int.equal i 1 && not tobj.tacobj_local then
    Egramcoq.extend_tactic_grammar key tobj.tacobj_tacgram

let load_tactic_notation i ((_, key), tobj) =
  (** Only add the printing and interpretation rules. *)
  Tacenv.register_alias key tobj.tacobj_body;
  Pptactic.declare_notation_tactic_pprule key tobj.tacobj_tacpp;
  if Int.equal i 1 && not tobj.tacobj_local then
    Egramcoq.extend_tactic_grammar key tobj.tacobj_tacgram

let subst_tactic_notation (subst, tobj) =
  { tobj with tacobj_body = Tacsubst.subst_tactic subst tobj.tacobj_body; }

let classify_tactic_notation tacobj = Substitute tacobj

let inTacticGrammar : tactic_grammar_obj -> obj =
  declare_object {(default_object "TacticGrammar") with
       open_function = open_tactic_notation;
       load_function = load_tactic_notation;
       cache_function = cache_tactic_notation;
       subst_function = subst_tactic_notation;
       classify_function = classify_tactic_notation}

let cons_production_parameter l = function
  | GramTerminal _ -> l
  | GramNonTerminal (_,_,_,ido) -> Option.List.cons ido l

let add_tactic_notation (local,n,prods,e) =
  let prods = List.map (interp_prod_item n) prods in
  let tags = make_tags prods in
  let pprule = {
    Pptactic.pptac_args = tags;
    pptac_prods = (n, List.map make_terminal_status prods);
  } in
  let ids = List.fold_left cons_production_parameter [] prods in
  let tac = Tacintern.glob_tactic_env ids (Global.env()) e in
  let parule = {
    tacgram_level = n;
    tacgram_prods = prods;
  } in
  let tacobj = {
    tacobj_local = local;
    tacobj_tacgram = parule;
    tacobj_tacpp = pprule;
    tacobj_body = tac;
  } in
  Lib.add_anonymous_leaf (inTacticGrammar tacobj)

(**********************************************************************)
(* ML Tactic entries                                                  *)

type atomic_entry = string * Genarg.glob_generic_argument list option

type ml_tactic_grammar_obj = {
  mltacobj_name : Tacexpr.ml_tactic_name;
  (** ML-side unique name *)
  mltacobj_prod : grammar_prod_item list list;
  (** Grammar rules generating the ML tactic. *)
}

(** ML tactic notations whose use can be restricted to an identifier are added
    as true Ltac entries. *)
let extend_atomic_tactic name entries =
  let add_atomic i (id, args) = match args with
  | None -> ()
  | Some args ->
    let open Tacexpr in
    let entry = { mltac_name = name; mltac_index = i } in
    let body = TacML (Loc.ghost, entry, args) in
    Tacenv.register_ltac false false (Names.Id.of_string id) body
  in
  List.iteri add_atomic entries

let cache_ml_tactic_notation (_, obj) =
  extend_ml_tactic_grammar obj.mltacobj_name obj.mltacobj_prod

let open_ml_tactic_notation i obj =
  if Int.equal i 1 then cache_ml_tactic_notation obj

let inMLTacticGrammar : ml_tactic_grammar_obj -> obj =
  declare_object { (default_object "MLTacticGrammar") with
    open_function = open_ml_tactic_notation;
    cache_function = cache_ml_tactic_notation;
    classify_function = (fun o -> Substitute o);
    subst_function = (fun (_, o) -> o);
  }

let add_ml_tactic_notation name prods atomic =
  let obj = {
    mltacobj_name = name;
    mltacobj_prod = prods;
  } in
  Lib.add_anonymous_leaf (inMLTacticGrammar obj);
  extend_atomic_tactic name atomic

(**********************************************************************)
(* Printing grammar entries                                           *)

let entry_buf = Buffer.create 64

let pr_entry e =
  let () = Buffer.clear entry_buf in
  let ft = Format.formatter_of_buffer entry_buf in
  let () = Gram.entry_print ft e in
  str (Buffer.contents entry_buf)

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
  | "tactic" ->
      str "Entry tactic_expr is" ++ fnl () ++
      pr_entry Pcoq.Tactic.tactic_expr ++
      str "Entry binder_tactic is" ++ fnl () ++
      pr_entry Pcoq.Tactic.binder_tactic ++
      str "Entry simple_tactic is" ++ fnl () ++
      pr_entry Pcoq.Tactic.simple_tactic ++
      str "Entry tactic_arg is" ++ fnl () ++
      pr_entry Pcoq.Tactic.tactic_arg
  | "vernac" ->
      str "Entry vernac is" ++ fnl () ++
      pr_entry Pcoq.Vernac_.vernac ++
      str "Entry command is" ++ fnl () ++
      pr_entry Pcoq.Vernac_.command ++
      str "Entry syntax is" ++ fnl () ++
      pr_entry Pcoq.Vernac_.syntax ++
      str "Entry gallina is" ++ fnl () ++
      pr_entry Pcoq.Vernac_.gallina ++
      str "Entry gallina_ext is" ++ fnl () ++
      pr_entry Pcoq.Vernac_.gallina_ext
  | _ -> error "Unknown or unprintable grammar entry."

(**********************************************************************)
(* Parse a format (every terminal starting with a letter or a single
   quote (except a single quote alone) must be quoted) *)

let parse_format ((loc, str) : lstring) =
  let str = " "^str in
  let l = String.length str in
  let push_token a = function
    | cur::l -> (a::cur)::l
    | [] -> [[a]] in
  let push_white n l =
    if Int.equal n 0 then l else push_token (UnpTerminal (String.make n ' ')) l in
  let close_box i b = function
    | a::(_::_ as l) -> push_token (UnpBox (b,a)) l
    | _ -> error "Non terminated box in format." in
  let close_quotation i =
    if i < String.length str && str.[i] == '\'' && (Int.equal (i+1) l || str.[i+1] == ' ')
    then i+1
    else error "Incorrectly terminated quoted expression." in
  let rec spaces n i =
    if i < String.length str && str.[i] == ' ' then spaces (n+1) (i+1)
    else n in
  let rec nonspaces quoted n i =
    if i < String.length str && str.[i] != ' ' then
      if str.[i] == '\'' && quoted &&
        (i+1 >= String.length str || str.[i+1] == ' ')
      then if Int.equal n 0 then error "Empty quoted token." else n
      else nonspaces quoted (n+1) (i+1)
    else
      if quoted then error "Spaces are not allowed in (quoted) symbols."
      else n in
  let rec parse_non_format i =
    let n = nonspaces false 0 i in
    push_token (UnpTerminal (String.sub str i n)) (parse_token (i+n))
  and parse_quoted n i =
    if i < String.length str then match str.[i] with
      (* Parse " // " *)
      | '/' when i <= String.length str && str.[i+1] == '/' ->
          (* We forget the useless n spaces... *)
	  push_token (UnpCut PpFnl)
            (parse_token (close_quotation (i+2)))
      (* Parse " .. / .. " *)
      | '/' when i <= String.length str ->
	  let p = spaces 0 (i+1) in
	  push_token (UnpCut (PpBrk (n,p)))
            (parse_token (close_quotation (i+p+1)))
      | c ->
      (* The spaces are real spaces *)
      push_white n (match c with
      | '[' ->
	  if i <= String.length str then match str.[i+1] with
	    (* Parse " [h .. ",  *)
	    | 'h' when i+1 <= String.length str && str.[i+2] == 'v' ->
		  (parse_box (fun n -> PpHVB n) (i+3))
		(* Parse " [v .. ",  *)
	    | 'v' ->
		    parse_box (fun n -> PpVB n) (i+2)
		(* Parse " [ .. ",  *)
	    | ' ' | '\'' ->
		parse_box (fun n -> PpHOVB n) (i+1)
	    | _ -> error "\"v\", \"hv\", \" \" expected after \"[\" in format."
	  else error "\"v\", \"hv\" or \" \" expected after \"[\" in format."
      (* Parse "]"  *)
      | ']' ->
	  ([] :: parse_token (close_quotation (i+1)))
      (* Parse a non formatting token *)
      | c ->
	  let n = nonspaces true 0 i in
	  push_token (UnpTerminal (String.sub str (i-1) (n+2)))
	    (parse_token (close_quotation (i+n))))
    else
      if Int.equal n 0 then []
      else error "Ending spaces non part of a format annotation."
  and parse_box box i =
    let n = spaces 0 i in
    close_box i (box n) (parse_token (close_quotation (i+n)))
  and parse_token i =
    let n = spaces 0 i in
    let i = i+n in
    if i < l then match str.[i] with
      (* Parse a ' *)
      |	'\'' when i+1 >= String.length str || str.[i+1] == ' ' ->
	  push_white (n-1) (push_token (UnpTerminal "'") (parse_token (i+1)))
      (* Parse the beginning of a quoted expression *)
      |	'\'' ->
          parse_quoted (n-1) (i+1)
      (* Otherwise *)
      | _ ->
          push_white (n-1) (parse_non_format i)
    else push_white n [[]]
  in
  try
    if not (String.is_empty str) then match parse_token 0 with
      | [l] -> l
      | _ -> error "Box closed without being opened in format."
    else
      error "Empty format."
  with reraise ->
    let (e, info) = Errors.push reraise in
    let info = Loc.add_loc info loc in
    iraise (e, info)

(***********************)
(* Analyzing notations *)

type symbol_token = WhiteSpace of int | String of string

let split_notation_string str =
  let push_token beg i l =
    if Int.equal beg i then l else
      let s = String.sub str beg (i - beg) in
      String s :: l
  in
  let push_whitespace beg i l =
    if Int.equal beg i then l else WhiteSpace (i-beg) :: l
  in
  let rec loop beg i =
    if i < String.length str then
      if str.[i] == ' ' then
	push_token beg i (loop_on_whitespace (i+1) (i+1))
      else
	loop beg (i+1)
    else
      push_token beg i []
  and loop_on_whitespace beg i =
    if i < String.length str then
      if str.[i] != ' ' then
	push_whitespace beg i (loop i (i+1))
      else
	loop_on_whitespace beg (i+1)
    else
      push_whitespace beg i []
  in
  loop 0 0

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
      error ("A break occurs on one side of \"..\" but not on the other side.")
  | _, Terminal s :: _ | Terminal s :: _, _ ->
      error ("The token \""^s^"\" occurs on one side of \"..\" but not on the other side.")
  | _, [] ->
      error msg_expected_form_of_recursive_notation
  | ((SProdList _ | NonTerminal _) :: _), _ | _, (SProdList _ :: _) ->
      anomaly (Pp.str "Only Terminal or Break expected on left, non-SProdList on right")

let rec interp_list_parser hd = function
  | [] -> [], List.rev hd
  | NonTerminal id :: tl when Id.equal id ldots_var ->
      if List.is_empty hd then error msg_expected_form_of_recursive_notation;
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
  | SProdList _ :: _ -> anomaly (Pp.str "Unexpected SProdList in interp_list_parser")


(* Find non-terminal tokens of notation *)

(* To protect alphabetic tokens and quotes from being seen as variables *)
let quote_notation_token x =
  let n = String.length x in
  let norm = Lexer.is_ident x in
  if (n > 0 && norm) || (n > 2 && x.[0] == '\'') then "'"^x^"'"
  else x

let rec raw_analyze_notation_tokens = function
  | []    -> []
  | String ".." :: sl -> NonTerminal ldots_var :: raw_analyze_notation_tokens sl
  | String "_" :: _ -> error "_ must be quoted."
  | String x :: sl when Lexer.is_ident x ->
      NonTerminal (Names.Id.of_string x) :: raw_analyze_notation_tokens sl
  | String s :: sl ->
      Terminal (String.drop_simple_quotes s) :: raw_analyze_notation_tokens sl
  | WhiteSpace n :: sl ->
      Break n :: raw_analyze_notation_tokens sl

let is_numeral symbs =
  match List.filter (function Break _ -> false | _ -> true) symbs with
  | ([Terminal "-"; Terminal x] | [Terminal x]) ->
      (try let _ = Bigint.of_string x in true with Failure _ -> false)
  | _ ->
      false

let rec get_notation_vars = function
  | [] -> []
  | NonTerminal id :: sl ->
      let vars = get_notation_vars sl in
      if Id.equal id ldots_var then vars else
	if Id.List.mem id vars then
	  error ("Variable "^Id.to_string id^" occurs more than once.")
	else
          id::vars
  | (Terminal _ | Break _) :: sl -> get_notation_vars sl
  | SProdList _ :: _ -> assert false

let analyze_notation_tokens l =
  let l = raw_analyze_notation_tokens l in
  let vars = get_notation_vars l in
  let recvars,l = interp_list_parser [] l in
  recvars, List.subtract Id.equal vars (List.map snd recvars), l

let error_not_same_scope x y =
  error ("Variables "^Id.to_string x^" and "^Id.to_string y^
    " must be in the same scope.")

(**********************************************************************)
(* Build pretty-printing rules                                        *)

let prec_assoc = function
  | RightA -> (L,E)
  | LeftA -> (E,L)
  | NonA -> (L,L)

let precedence_of_entry_type from = function
  | ETConstr (NumLevel n,BorderProd (_,None)) -> n, Prec n
  | ETConstr (NumLevel n,BorderProd (b,Some a)) ->
      n, let (lp,rp) = prec_assoc a in if b == Left then lp else rp
  | ETConstr (NumLevel n,InternalProd) -> n, Prec n
  | ETConstr (NextLevel,_) -> from, L
  | _ -> 0, E (* ?? *)

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

let is_next_non_terminal = function
| [] -> false
| pr :: _ -> is_non_terminal pr

let is_next_terminal = function Terminal _ :: _ -> true | _ -> false

let is_next_break = function Break _ :: _ -> true | _ -> false

let add_break n l = UnpCut (PpBrk(n,0)) :: l

let add_break_if_none n = function
  | ((UnpCut (PpBrk _) :: _) | []) as l -> l
  | l -> UnpCut (PpBrk(n,0)) :: l

let check_open_binder isopen sl m =
  if isopen && not (List.is_empty sl) then
    errorlabstrm "" (str "as " ++ pr_id m ++
      str " is a non-closed binder, no such \"" ++
      prlist_with_sep spc (function Terminal s -> str s | _ -> assert false) sl
      ++ strbrk "\" is allowed to occur.")

(* Heuristics for building default printing rules *)

let index_id id l = List.index Id.equal id l

let make_hunks etyps symbols from =
  let vars,typs = List.split etyps in
  let rec make = function
    | NonTerminal m :: prods ->
	let i = index_id m vars in
	let _,prec = precedence_of_entry_type from (List.nth typs (i-1)) in
	let u = UnpMetaVar (i,prec) in
	if is_next_non_terminal prods then
	  u :: add_break_if_none 1 (make prods)
	else
	  u :: make_with_space prods
    | Terminal s :: prods when List.exists is_non_terminal prods ->
        if (is_comma s || is_operator s) then
          (* Always a breakable space after comma or separator *)
	  UnpTerminal s :: add_break_if_none 1 (make prods)
	else if is_right_bracket s && is_next_terminal prods then
          (* Always no space after right bracked, but possibly a break *)
	  UnpTerminal s :: add_break_if_none 0 (make prods)
        else if is_left_bracket s  && is_next_non_terminal prods then
	  UnpTerminal s :: make prods
	else if not (is_next_break prods) then
          (* Add rigid space, no break, unless user asked for something *)
          UnpTerminal (s^" ") :: make prods
        else
          (* Rely on user spaces *)
          UnpTerminal s :: make prods

    | Terminal s :: prods ->
        (* Separate but do not cut a trailing sequence of terminal *)
        (match prods with
        | Terminal _ :: _ -> UnpTerminal (s^" ") :: make prods
        | _ -> UnpTerminal s :: make prods)

    | Break n :: prods ->
	add_break n (make prods)

    | SProdList (m,sl) :: prods ->
	let i = index_id m vars in
	let typ = List.nth typs (i-1) in
	let _,prec = precedence_of_entry_type from typ in
        let sl' =
          (* If no separator: add a break *)
	  if List.is_empty sl then add_break 1 []
          (* We add NonTerminal for simulation but remove it afterwards *)
	  else snd (List.sep_last (make (sl@[NonTerminal m]))) in
	let hunk = match typ with
	  | ETConstr _ -> UnpListMetaVar (i,prec,sl')
	  | ETBinder isopen ->
	      check_open_binder isopen sl m;
	      UnpBinderListMetaVar (i,isopen,sl')
	  | _ -> assert false in
	hunk :: make_with_space prods

    | [] -> []

  and make_with_space prods =
    match prods with
    | Terminal s' :: prods'->
        if is_operator s' then
          (* A rigid space before operator and a breakable after *)
          UnpTerminal (" "^s') :: add_break_if_none 1 (make prods')
        else if is_comma s' then
          (* No space whatsoever before comma *)
          make prods
        else if is_right_bracket s' then
          make prods
        else
          (* A breakable space between any other two terminals *)
          add_break_if_none 1 (make prods)
    | (NonTerminal _ | SProdList _) :: _ ->
        (* A breakable space before a non-terminal *)
        add_break_if_none 1 (make prods)
    | Break _ :: _ ->
        (* Rely on user wish *)
        make prods
    | [] -> []

  in make symbols

(* Build default printing rules from explicit format *)

let error_format () = error "The format does not match the notation."

let rec split_format_at_ldots hd = function
  | UnpTerminal s :: fmt when String.equal s (Id.to_string ldots_var) -> List.rev hd, fmt
  | u :: fmt ->
      check_no_ldots_in_box u;
      split_format_at_ldots (u::hd) fmt
  | [] -> raise Exit

and check_no_ldots_in_box = function
  | UnpBox (_,fmt) ->
      (try
        let _ = split_format_at_ldots [] fmt in
        error ("The special symbol \"..\" must occur at the same formatting depth than the variables of which it is the ellipse.")
      with Exit -> ())
  | _ -> ()

let skip_var_in_recursive_format = function
  | UnpTerminal _ :: sl (* skip first var *) ->
      (* To do, though not so important: check that the names match
         the names in the notation *)
      sl
  | _ -> error_format ()

let read_recursive_format sl fmt =
  let get_head fmt =
    let sl = skip_var_in_recursive_format fmt in
    try split_format_at_ldots [] sl with Exit -> error_format () in
  let rec get_tail = function
    | a :: sepfmt, b :: fmt when Pervasives.(=) a b -> get_tail (sepfmt, fmt) (* FIXME *)
    | [], tail -> skip_var_in_recursive_format tail
    | _ -> error "The format is not the same on the right and left hand side of the special token \"..\"." in
  let slfmt, fmt = get_head fmt in
  slfmt, get_tail (slfmt, fmt)

let hunks_of_format (from,(vars,typs)) symfmt =
  let rec aux = function
  | symbs, (UnpTerminal s' as u) :: fmt
      when String.equal s' (String.make (String.length s') ' ') ->
      let symbs, l = aux (symbs,fmt) in symbs, u :: l
  | Terminal s :: symbs, (UnpTerminal s') :: fmt
      when String.equal s (String.drop_simple_quotes s') ->
      let symbs, l = aux (symbs,fmt) in symbs, UnpTerminal s :: l
  | NonTerminal s :: symbs, UnpTerminal s' :: fmt when Id.equal s (Id.of_string s') ->
      let i = index_id s vars in
      let _,prec = precedence_of_entry_type from (List.nth typs (i-1)) in
      let symbs, l = aux (symbs,fmt) in symbs, UnpMetaVar (i,prec) :: l
  | symbs, UnpBox (a,b) :: fmt ->
      let symbs', b' = aux (symbs,b) in
      let symbs', l = aux (symbs',fmt) in
      symbs', UnpBox (a,b') :: l
  | symbs, (UnpCut _ as u) :: fmt ->
      let symbs, l = aux (symbs,fmt) in symbs, u :: l
  | SProdList (m,sl) :: symbs, fmt ->
      let i = index_id m vars in
      let typ = List.nth typs (i-1) in
      let _,prec = precedence_of_entry_type from typ in
      let slfmt,fmt = read_recursive_format sl fmt in
      let sl, slfmt = aux (sl,slfmt) in
      if not (List.is_empty sl) then error_format ();
      let symbs, l = aux (symbs,fmt) in
      let hunk = match typ with
	| ETConstr _ -> UnpListMetaVar (i,prec,slfmt)
	| ETBinder isopen ->
	    check_open_binder isopen sl m;
	    UnpBinderListMetaVar (i,isopen,slfmt)
	| _ -> assert false in
      symbs, hunk :: l
  | symbs, [] -> symbs, []
  | _, _ -> error_format ()
  in
  match aux symfmt with
  | [], l -> l
  | _ -> error_format ()

(**********************************************************************)
(* Build parsing rules                                                *)

let assoc_of_type n (_,typ) = precedence_of_entry_type n typ

let is_not_small_constr = function
    ETConstr _ -> true
  | ETOther("constr","binder_constr") -> true
  | _ -> false

let rec define_keywords_aux = function
  | GramConstrNonTerminal(e,Some _) as n1 :: GramConstrTerminal(IDENT k) :: l
      when is_not_small_constr e ->
      Flags.if_verbose msg_info (strbrk ("Identifier '"^k^"' now a keyword"));
      Lexer.add_keyword k;
      n1 :: GramConstrTerminal(KEYWORD k) :: define_keywords_aux l
  | n :: l -> n :: define_keywords_aux l
  | [] -> []

  (* Ensure that IDENT articulation terminal symbols are keywords *)
let define_keywords = function
  | GramConstrTerminal(IDENT k)::l ->
      Flags.if_verbose msg_info (strbrk ("Identifier '"^k^"' now a keyword"));
      Lexer.add_keyword k;
      GramConstrTerminal(KEYWORD k) :: define_keywords_aux l
  | l -> define_keywords_aux l

let distribute a ll = List.map (fun l -> a @ l) ll

  (* Expand LIST1(t,sep) into the combination of t and t;sep;LIST1(t,sep)
     as many times as expected in [n] argument *)
let rec expand_list_rule typ tkl x n i hds ll =
  if Int.equal i n then
    let hds =
      GramConstrListMark (n,true) :: hds
      @	[GramConstrNonTerminal (ETConstrList (typ,tkl), Some x)] in
    distribute hds ll
  else
    let camlp4_message_name = Some (add_suffix x ("_"^string_of_int n)) in
    let main = GramConstrNonTerminal (ETConstr typ, camlp4_message_name) in
    let tks = List.map (fun x -> GramConstrTerminal x) tkl in
    distribute (GramConstrListMark (i+1,false) :: hds @ [main]) ll @
      expand_list_rule typ tkl x n (i+1) (main :: tks @ hds) ll

let make_production etyps symbols =
  let prod =
    List.fold_right
      (fun t ll -> match t with
        | NonTerminal m ->
	    let typ = List.assoc m etyps in
	    distribute [GramConstrNonTerminal (typ, Some m)] ll
        | Terminal s ->
	    distribute [GramConstrTerminal (Lexer.terminal s)] ll
        | Break _ ->
            ll
        | SProdList (x,sl) ->
            let tkl = List.flatten
              (List.map (function Terminal s -> [Lexer.terminal s]
                | Break _ -> []
                | _ -> anomaly (Pp.str "Found a non terminal token in recursive notation separator")) sl) in
	    match List.assoc x etyps with
            | ETConstr typ -> expand_list_rule typ tkl x 1 0 [] ll
            | ETBinder o ->
		distribute
                  [GramConstrNonTerminal (ETBinderList (o,tkl), Some x)] ll
            | _ ->
                error "Components of recursive patterns in notation must be terms or binders.")
      symbols [[]] in
  List.map define_keywords prod

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
  | (_,ETConstr(_,BorderProd (_,a))) :: _ -> a
  | _ -> None

let recompute_assoc typs =
  match border typs, border (List.rev typs) with
    | Some LeftA, Some RightA -> assert false
    | Some LeftA, _ -> Some LeftA
    | _, Some RightA -> Some RightA
    | _ -> None

(**************************************************************************)
(* Registration of syntax extensions (parsing/printing, no interpretation)*)

let pr_arg_level from = function
  | (n,L) when Int.equal n from -> str "at next level"
  | (n,E) -> str "at level " ++ int n
  | (n,L) -> str "at level below " ++ int n
  | (n,Prec m) when Int.equal m n -> str "at level " ++ int n
  | (n,_) -> str "Unknown level"

let pr_level ntn (from,args) =
  str "at level " ++ int from ++ spc () ++ str "with arguments" ++ spc() ++
  prlist_with_sep pr_comma (pr_arg_level from) args

let error_incompatible_level ntn oldprec prec =
  errorlabstrm ""
    (str ("Notation "^ntn^" is already defined") ++ spc() ++
    pr_level ntn oldprec ++
    spc() ++ str "while it is now required to be" ++ spc() ++
    pr_level ntn prec ++ str ".")

type syntax_extension = {
  synext_level : Notation.level;
  synext_notation : notation;
  synext_notgram : notation_grammar;
  synext_unparsing : unparsing list;
  synext_extra : (string * string) list;
}

type syntax_extension_obj = locality_flag * syntax_extension list

let cache_one_syntax_extension se =
  let ntn = se.synext_notation in
  let prec = se.synext_level in
  try
    let oldprec = Notation.level_of_notation ntn in
    if not (Notation.level_eq prec oldprec) then error_incompatible_level ntn oldprec prec
  with Not_found ->
    (* Reserve the notation level *)
    Notation.declare_notation_level ntn prec;
    (* Declare the parsing rule *)
    Egramcoq.extend_constr_grammar prec se.synext_notgram;
    (* Declare the printing rule *)
    Notation.declare_notation_printing_rule ntn
      ~extra:se.synext_extra (se.synext_unparsing, fst prec)

let cache_syntax_extension (_, (_, sy)) =
  List.iter cache_one_syntax_extension sy

let subst_parsing_rule subst x = x

let subst_printing_rule subst x = x

let subst_syntax_extension (subst, (local, sy)) =
  let map sy = { sy with
    synext_notgram = subst_parsing_rule subst sy.synext_notgram;
    synext_unparsing = subst_printing_rule subst sy.synext_unparsing;
  } in
  (local, List.map map sy)

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

let interp_modifiers modl =
  let onlyparsing = ref false in
  let rec interp assoc level etyps format extra = function
    | [] ->
	(assoc,level,etyps,!onlyparsing,format,extra)
    | SetEntryType (s,typ) :: l ->
	let id = Id.of_string s in
	if Id.List.mem_assoc id etyps then
	  error (s^" is already assigned to an entry or constr level.");
	interp assoc level ((id,typ)::etyps) format extra l
    | SetItemLevel ([],n) :: l ->
	interp assoc level etyps format extra l
    | SetItemLevel (s::idl,n) :: l ->
	let id = Id.of_string s in
	if Id.List.mem_assoc id etyps then
	  error (s^" is already assigned to an entry or constr level.");
	let typ = ETConstr (n,()) in
	interp assoc level ((id,typ)::etyps) format extra (SetItemLevel (idl,n)::l)
    | SetLevel n :: l ->
	if not (Option.is_empty level) then error "A level is given more than once.";
	interp assoc (Some n) etyps format extra l
    | SetAssoc a :: l ->
	if not (Option.is_empty assoc) then error"An associativity is given more than once.";
	interp (Some a) level etyps format extra l
    | SetOnlyParsing _ :: l ->
	onlyparsing := true;
	interp assoc level etyps format extra l
    | SetFormat ("text",s) :: l ->
	if not (Option.is_empty format) then error "A format is given more than once.";
	interp assoc level etyps (Some s) extra l
    | SetFormat (k,(_,s)) :: l ->
	interp assoc level etyps format ((k,s) :: extra) l
  in interp None None [] None [] modl

let check_infix_modifiers modifiers =
  let (assoc,level,t,b,fmt,extra) = interp_modifiers modifiers in
  if not (List.is_empty t) then
    error "Explicit entry level or type unexpected in infix notation."

let check_useless_entry_types recvars mainvars etyps =
  let vars = let (l1,l2) = List.split recvars in l1@l2@mainvars in
  match List.filter (fun (x,etyp) -> not (List.mem x vars)) etyps with
  | (x,_)::_ -> error (Id.to_string x ^ " is unbound in the notation.")
  | _ -> ()

let no_syntax_modifiers = function
  | [] | [SetOnlyParsing _] -> true
  | _ -> false

let is_only_parsing = function
  | [SetOnlyParsing _] -> true
  | _ -> false

(* Compute precedences from modifiers (or find default ones) *)

let set_entry_type etyps (x,typ) =
  let typ = try
    match List.assoc x etyps, typ with
      | ETConstr (n,()), (_,BorderProd (left,_)) ->
          ETConstr (n,BorderProd (left,None))
      | ETConstr (n,()), (_,InternalProd) -> ETConstr (n,InternalProd)
      | (ETPattern | ETName | ETBigint | ETOther _ |
	 ETReference | ETBinder _ as t), _ -> t
      | (ETBinderList _ |ETConstrList _), _ -> assert false
    with Not_found -> ETConstr typ
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
	errorlabstrm ""
	  (strbrk "In " ++ pr_id x ++ str " .. " ++ pr_id y ++
	   strbrk ", both ends have incompatible types."))
    recvars etyps

let internalization_type_of_entry_type = function
  | ETConstr _ -> NtnInternTypeConstr
  | ETBigint | ETReference -> NtnInternTypeConstr
  | ETBinder _ -> NtnInternTypeBinder
  | ETName -> NtnInternTypeIdent
  | ETPattern | ETOther _ -> error "Not supported."
  | ETBinderList _ | ETConstrList _ -> assert false

let set_internalization_type typs =
  List.map (fun (_, e) -> internalization_type_of_entry_type e) typs

let make_internalization_vars recvars mainvars typs =
  let maintyps = List.combine mainvars typs in
  let extratyps = List.map (fun (x,y) -> (y,List.assoc x maintyps)) recvars in
  maintyps @ extratyps

let make_interpretation_type isrec = function
  | NtnInternTypeConstr when isrec -> NtnTypeConstrList
  | NtnInternTypeConstr | NtnInternTypeIdent -> NtnTypeConstr
  | NtnInternTypeBinder when isrec -> NtnTypeBinderList
  | NtnInternTypeBinder -> error "Type not allowed in recursive notation."

let make_interpretation_vars recvars allvars =
  let eq_subscope (sc1, l1) (sc2, l2) =
    Option.equal String.equal sc1 sc2 &&
    List.equal String.equal l1 l2
  in
  let check (x, y) =
    let (scope1, _) = Id.Map.find x allvars in
    let (scope2, _) = Id.Map.find y allvars in
    if not (eq_subscope scope1 scope2) then error_not_same_scope x y
  in
  let () = List.iter check recvars in
  let useless_recvars = List.map snd recvars in
  let mainvars =
    Id.Map.filter (fun x _ -> not (Id.List.mem x useless_recvars)) allvars in
  Id.Map.mapi (fun x (sc, typ) ->
    (sc, make_interpretation_type (Id.List.mem_assoc x recvars) typ)) mainvars

let check_rule_productivity l =
  if List.for_all (function NonTerminal _ -> true | _ -> false) l then
    error "A notation must include at least one symbol.";
  if (match l with SProdList _ :: _ -> true | _ -> false) then
    error "A recursive notation must start with at least one symbol."

let is_not_printable onlyparse noninjective = function
| NVar _ ->
  let () = if not onlyparse then
    msg_warning (strbrk "This notation will not be used for printing as it is bound to a single variable.")
  in
  true
| _ ->
  if not onlyparse && noninjective then
    let () = msg_warning (strbrk "This notation will not be used for printing as it is not reversible.") in
    true
  else onlyparse

let find_precedence lev etyps symbols =
  match symbols with
  | NonTerminal x :: _ ->
      (try match List.assoc x etyps with
	| ETConstr _ ->
	    error "The level of the leftmost non-terminal cannot be changed."
	| ETName | ETBigint | ETReference ->
            begin match lev with
            | None ->
	      ([msg_info,strbrk "Setting notation at level 0."],0)
            | Some 0 ->
              ([],0)
            | _ ->
	      error "A notation starting with an atomic expression must be at level 0."
            end
	| ETPattern | ETBinder _ | ETOther _ -> (* Give a default ? *)
	    if Option.is_empty lev then
	      error "Need an explicit level."
	    else [],Option.get lev
        | ETConstrList _ | ETBinderList _ ->
	    assert false (* internally used in grammar only *)
      with Not_found ->
	if Option.is_empty lev then
	  error "A left-recursive notation must have an explicit level."
	else [],Option.get lev)
  | Terminal _ ::l when
      (match List.last symbols with Terminal _ -> true |_ -> false)
      ->
      if Option.is_empty lev then
	([msg_info,strbrk "Setting notation at level 0."], 0)
      else [],Option.get lev
  | _ ->
      if Option.is_empty lev then error "Cannot determine the level.";
      [],Option.get lev

let check_curly_brackets_notation_exists () =
  try let _ = Notation.level_of_notation "{ _ }" in ()
  with Not_found ->
    error "Notations involving patterns of the form \"{ _ }\" are treated \n\
specially and require that the notation \"{ _ }\" is already reserved."

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
        | NonTerminal _ as x :: l' as l0 ->
            let br',next' = skip_break [] l' in
            (match next' with
              | Terminal "}" as t2 :: l'' as l1 ->
                  if not (List.equal Notation.symbol_eq l l0) || not (List.equal Notation.symbol_eq l' l1) then
                    msg_warning (strbrk "Skipping spaces inside curly brackets");
                  if deb && List.is_empty l'' then [t1;x;t2] else begin
                    check_curly_brackets_notation_exists ();
                    x :: aux false l''
                  end
              | l1 -> t1 :: br @ x :: br' @ aux false l1)
        | l0 -> t1 :: aux false l0)
  | x :: l -> x :: aux false l
  in aux true l

let compute_syntax_data df modifiers =
  let (assoc,n,etyps,onlyparse,fmt,extra) = interp_modifiers modifiers in
  let assoc = match assoc with None -> (* default *) Some NonA | a -> a in
  let toks = split_notation_string df in
  let (recvars,mainvars,symbols) = analyze_notation_tokens toks in
  let _ = check_useless_entry_types recvars mainvars etyps in
  let ntn_for_interp = make_notation_key symbols in
  let symbols' = remove_curly_brackets symbols in
  let need_squash = not (List.equal Notation.symbol_eq symbols symbols') in
  let ntn_for_grammar = make_notation_key symbols' in
  check_rule_productivity symbols';
  let msgs,n = find_precedence n etyps symbols' in
  let innerlevel = NumLevel 200 in
  let typs =
    find_symbols
      (NumLevel n,BorderProd(Left,assoc))
      (innerlevel,InternalProd)
      (NumLevel n,BorderProd(Right,assoc))
      symbols' in
  (* To globalize... *)
  let etyps = join_auxiliary_recursive_types recvars etyps in
  let sy_typs = List.map (set_entry_type etyps) typs in
  let prec = (n,List.map (assoc_of_type n) sy_typs) in
  let i_typs = set_internalization_type sy_typs in
  let sy_data = (n,sy_typs,symbols',fmt) in
  let sy_fulldata = (i_typs,ntn_for_grammar,prec,need_squash,sy_data) in
  let df' = ((Lib.library_dp(),Lib.current_dirpath true),df) in
  let i_data = (onlyparse,recvars,mainvars,(ntn_for_interp,df')) in
  (* Return relevant data for interpretation and for parsing/printing *)
  (msgs,i_data,i_typs,sy_fulldata,extra)

let compute_pure_syntax_data df mods =
  let (msgs,(onlyparse,_,_,_),_,sy_data,extra) = compute_syntax_data df mods in
  let msgs =
    if onlyparse then
      (msg_warning,
      strbrk "The only parsing modifier has no effect in Reserved Notation.")::msgs
    else msgs in
  msgs, sy_data, extra

(**********************************************************************)
(* Registration of notations interpretation                            *)

type notation_obj = {
  notobj_local : bool;
  notobj_scope : scope_name option;
  notobj_interp : interpretation;
  notobj_onlyparse : bool;
  notobj_notation : notation * notation_location;
}

let load_notation _ (_, nobj) =
  Option.iter Notation.declare_scope nobj.notobj_scope

let open_notation i (_, nobj) =
  let scope = nobj.notobj_scope in
  let (ntn, df) = nobj.notobj_notation in
  let pat = nobj.notobj_interp in
  if Int.equal i 1 then begin
    (* Declare the interpretation *)
    Notation.declare_notation_interpretation ntn scope pat df;
    (* Declare the uninterpretation *)
    if not nobj.notobj_onlyparse then
      Notation.declare_uninterpretation (NotationRule (scope, ntn)) pat
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
  let fs = Lib.freeze `No in
  try let a = f x in Lib.unfreeze fs; a
  with reraise ->
    let reraise = Errors.push reraise in
    let () = Lib.unfreeze fs in
    iraise reraise

let with_syntax_protection f x =
  with_lib_stk_protection
    (with_grammar_rule_protection
       (with_notation_protection f)) x

(**********************************************************************)
(* Recovering existing syntax                                         *)

let contract_notation ntn =
  if String.equal ntn "{ _ }" then ntn else
  let rec aux ntn i =
    if i <= String.length ntn - 5 then
      let ntn' =
        if String.is_sub "{ _ }" ntn i then
          String.sub ntn 0 i ^ "_" ^
          String.sub ntn (i+5) (String.length ntn -i-5)
        else ntn in
      aux ntn' (i+1)
    else ntn in
  aux ntn 0

exception NoSyntaxRule

let recover_syntax ntn =
  try
    let prec = Notation.level_of_notation ntn in
    let pp_rule,_ = Notation.find_notation_printing_rule ntn in
    let pp_extra_rules = Notation.find_notation_extra_printing_rules ntn in
    let pa_rule = Egramcoq.recover_constr_grammar ntn prec in
    { synext_level = prec;
      synext_notation = ntn;
      synext_notgram = pa_rule;
      synext_unparsing = pp_rule;
      synext_extra = pp_extra_rules }
  with Not_found ->
    raise NoSyntaxRule

let recover_squash_syntax sy =
  let sq = recover_syntax "{ _ }" in
  [sy; sq]

let recover_notation_syntax rawntn =
  let ntn = contract_notation rawntn in
  let sy = recover_syntax ntn in
  let need_squash = not (String.equal ntn rawntn) in
  let rules = if need_squash then recover_squash_syntax sy else [sy] in
  sy.synext_notgram.notgram_typs, rules

(**********************************************************************)
(* Main entry point for building parsing and printing rules           *)

let make_pa_rule i_typs (n,typs,symbols,_) ntn =
  let assoc = recompute_assoc typs in
  let prod = make_production typs symbols in
  { notgram_level = n;
    notgram_assoc = assoc;
    notgram_notation = ntn;
    notgram_prods = prod;
    notgram_typs = i_typs; }

let make_pp_rule (n,typs,symbols,fmt) =
  match fmt with
  | None -> [UnpBox (PpHOVB 0, make_hunks typs symbols n)]
  | Some fmt -> hunks_of_format (n, List.split typs) (symbols, parse_format fmt)

let make_syntax_rules (i_typs,ntn,prec,need_squash,sy_data) extra =
  let pa_rule = make_pa_rule i_typs sy_data ntn in
  let pp_rule = make_pp_rule sy_data in
  let sy = {
    synext_level = prec;
    synext_notation = ntn;
    synext_notgram = pa_rule;
    synext_unparsing = pp_rule;
    synext_extra = extra;
  } in
  (* By construction, the rule for "{ _ }" is declared, but we need to
     redeclare it because the file where it is declared needs not be open
     when the current file opens (especially in presence of -nois) *)
  if need_squash then recover_squash_syntax sy else [sy]

(**********************************************************************)
(* Main functions about notations                                     *)

let to_map l =
  let fold accu (x, v) = Id.Map.add x v accu in
  List.fold_left fold Id.Map.empty l

let add_notation_in_scope local df c mods scope =
  let (msgs,i_data,i_typs,sy_data,extra) = compute_syntax_data df mods in
  (* Prepare the parsing and printing rules *)
  let sy_rules = make_syntax_rules sy_data extra in
  (* Prepare the interpretation *)
  let (onlyparse, recvars,mainvars, df') = i_data in
  let i_vars = make_internalization_vars recvars mainvars i_typs in
  let nenv = {
    ninterp_var_type = to_map i_vars;
    ninterp_rec_vars = to_map recvars;
    ninterp_only_parse = false;
  } in
  let (acvars, ac) = interp_notation_constr nenv c in
  let interp = make_interpretation_vars recvars acvars in
  let map (x, _) = try Some (x, Id.Map.find x interp) with Not_found -> None in
  let onlyparse = is_not_printable onlyparse nenv.ninterp_only_parse ac in
  let notation = {
    notobj_local = local;
    notobj_scope = scope;
    notobj_interp = (List.map_filter map i_vars, ac);
    (** Order is important here! *)
    notobj_onlyparse = onlyparse;
    notobj_notation = df';
  } in
  (* Ready to change the global state *)
  Flags.if_verbose (List.iter (fun (f,x) -> f x)) msgs;
  Lib.add_anonymous_leaf (inSyntaxExtension (local, sy_rules));
  Lib.add_anonymous_leaf (inNotation notation);
  df'

let add_notation_interpretation_core local df ?(impls=empty_internalization_env) c scope onlyparse =
  let dfs = split_notation_string df in
  let (recvars,mainvars,symbs) = analyze_notation_tokens dfs in
  (* Recover types of variables and pa/pp rules; redeclare them if needed *)
  let i_typs = if not (is_numeral symbs) then begin
    let i_typs,sy_rules = recover_notation_syntax (make_notation_key symbs) in
    Lib.add_anonymous_leaf (inSyntaxExtension (local,sy_rules)); i_typs
  end else [] in
  (* Declare interpretation *)
  let path = (Lib.library_dp(),Lib.current_dirpath true) in
  let df' = (make_notation_key symbs,(path,df)) in
  let i_vars = make_internalization_vars recvars mainvars i_typs in
  let nenv = {
    ninterp_var_type = to_map i_vars;
    ninterp_rec_vars = to_map recvars;
    ninterp_only_parse = false;
  } in
  let (acvars, ac) = interp_notation_constr ~impls nenv c in
  let interp = make_interpretation_vars recvars acvars in
  let map (x, _) = try Some (x, Id.Map.find x interp) with Not_found -> None in
  let onlyparse = is_not_printable onlyparse nenv.ninterp_only_parse ac in
  let notation = {
    notobj_local = local;
    notobj_scope = scope;
    notobj_interp = (List.map_filter map i_vars, ac);
    (** Order is important here! *)
    notobj_onlyparse = onlyparse;
    notobj_notation = df';
  } in
  Lib.add_anonymous_leaf (inNotation notation);
  df'

(* Notations without interpretation (Reserved Notation) *)

let add_syntax_extension local ((loc,df),mods) =
  let msgs, sy_data, extra = compute_pure_syntax_data df mods in
  let sy_rules = make_syntax_rules sy_data extra in
  Flags.if_verbose (List.iter (fun (f,x) -> f x)) msgs;
  Lib.add_anonymous_leaf (inSyntaxExtension(local,sy_rules))

(* Notations with only interpretation *)

let add_notation_interpretation ((loc,df),c,sc) =
  let df' = add_notation_interpretation_core false df c sc false in
  Dumpglob.dump_notation (loc,df') sc true

let set_notation_for_interpretation impls ((_,df),c,sc) =
  (try ignore
    (silently (add_notation_interpretation_core false df ~impls c sc) false);
  with NoSyntaxRule ->
    error "Parsing rule for this notation has to be previously declared.");
  Option.iter (fun sc -> Notation.open_close_scope (false,true,sc)) sc

(* Main entry point *)

let add_notation local c ((loc,df),modifiers) sc =
  let df' =
   if no_syntax_modifiers modifiers then
    (* No syntax data: try to rely on a previously declared rule *)
    let onlyparse = is_only_parsing modifiers in
    try add_notation_interpretation_core local df c sc onlyparse
    with NoSyntaxRule ->
      (* Try to determine a default syntax rule *)
      add_notation_in_scope local df c modifiers sc
   else
    (* Declare both syntax and interpretation *)
    add_notation_in_scope local df c modifiers sc
  in
  Dumpglob.dump_notation (loc,df') sc true

let add_notation_extra_printing_rule df k v =
  let notk = 
    let dfs = split_notation_string df in
    let _,_, symbs = analyze_notation_tokens dfs in
    make_notation_key symbs in
  Notation.add_notation_extra_printing_rule notk k v

(* Infix notations *)

let inject_var x = CRef (Ident (Loc.ghost, Id.of_string x),None)

let add_infix local ((loc,inf),modifiers) pr sc =
  check_infix_modifiers modifiers;
  (* check the precedence *)
  let metas = [inject_var "x"; inject_var "y"] in
  let c = mkAppC (pr,metas) in
  let df = "x "^(quote_notation_token inf)^" y" in
  add_notation local c ((loc,df),modifiers) sc

(**********************************************************************)
(* Delimiters and classes bound to scopes                             *)

type scope_command = ScopeDelim of string | ScopeClasses of scope_class list

let load_scope_command _ (_,(scope,dlm)) =
  Notation.declare_scope scope

let open_scope_command i (_,(scope,o)) =
  if Int.equal i 1 then
    match o with
    | ScopeDelim dlm -> Notation.declare_delimiters scope dlm
    | ScopeClasses cl -> List.iter (Notation.declare_scope_class scope) cl

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

let add_class_scope scope cl =
  Lib.add_anonymous_leaf (inScopeCommand(scope,ScopeClasses cl))

(* Check if abbreviation to a name and avoid early insertion of
   maximal implicit arguments *)
let try_interp_name_alias = function
  | [], CRef (ref,_) -> intern_reference ref
  | _ -> raise Not_found

let add_syntactic_definition ident (vars,c) local onlyparse =
  let nonprintable = ref false in
  let vars,pat =
    try [], NRef (try_interp_name_alias (vars,c))
    with Not_found ->
      let fold accu id = Id.Map.add id NtnInternTypeConstr accu in
      let i_vars = List.fold_left fold Id.Map.empty vars in
      let nenv = {
        ninterp_var_type = i_vars;
        ninterp_rec_vars = Id.Map.empty;
        ninterp_only_parse = false;
      } in
      let nvars, pat = interp_notation_constr nenv c in
      let () = nonprintable := nenv.ninterp_only_parse in
      let map id = let (sc, _) = Id.Map.find id nvars in (id, sc) in
      List.map map vars, pat
  in
  let onlyparse = match onlyparse with
    | None when (is_not_printable false !nonprintable pat) -> Some Flags.Current
    | p -> p
  in
  Syntax_def.declare_syntactic_definition local ident onlyparse (vars,pat)

