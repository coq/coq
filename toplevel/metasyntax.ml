(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Flags
open Util
open Names
open Topconstr
open Ppextend
open Extend
open Libobject
open Summary
open Constrintern
open Vernacexpr
open Pcoq
open Rawterm
open Libnames
open Lexer
open Egrammar
open Notation

(**********************************************************************)
(* Tokens                                                             *)

let cache_token (_,s) = add_token ("", s)

let (inToken, outToken) =
  declare_object {(default_object "TOKEN") with
       open_function = (fun i o -> if i=1 then cache_token o);
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

let cache_tactic_notation (_,(pa,pp)) =
  Egrammar.extend_grammar (Egrammar.TacticGrammar pa);
  Pptactic.declare_extra_tactic_pprule pp

let subst_tactic_parule subst (key,n,p,(d,tac)) =
  (key,n,p,(d,Tacinterp.subst_tactic subst tac))

let subst_tactic_notation (subst,(pa,pp)) =
  (subst_tactic_parule subst pa,pp)

let (inTacticGrammar, outTacticGrammar) =
  declare_object {(default_object "TacticGrammar") with
       open_function = (fun i o -> if i=1 then cache_tactic_notation o);
       cache_function = cache_tactic_notation;
       subst_function = subst_tactic_notation;
       classify_function = (fun o -> Substitute o)}

let cons_production_parameter l = function
  | GramTerminal _ -> l
  | GramNonTerminal (_,_,_,ido) -> Option.List.cons ido l

let rec tactic_notation_key = function
  | GramTerminal id :: _ -> id
  | _ :: l -> tactic_notation_key l
  | [] -> "terminal_free_notation"

let rec next_key_away key t =
  if Pptactic.exists_extra_tactic_pprule key t then next_key_away (key^"'") t
  else key

let add_tactic_notation (n,prods,e) =
  let prods = List.map (interp_prod_item n) prods in
  let tags = make_tags prods in
  let key = next_key_away (tactic_notation_key prods) tags in
  let pprule = (key,tags,(n,List.map make_terminal_status prods)) in
  let ids = List.fold_left cons_production_parameter [] prods in
  let tac = Tacinterp.glob_tactic_env ids (Global.env()) e in
  let parule = (key,n,prods,(Lib.cwd(),tac)) in
  Lib.add_anonymous_leaf (inTacticGrammar (parule,pprule))

(**********************************************************************)
(* Printing grammar entries                                           *)

let print_grammar = function
  | "constr" | "operconstr" | "binder_constr" ->
      msgnl (str "Entry constr is");
      Gram.Entry.print Pcoq.Constr.constr;
      msgnl (str "and lconstr is");
      Gram.Entry.print Pcoq.Constr.lconstr;
      msgnl (str "where binder_constr is");
      Gram.Entry.print Pcoq.Constr.binder_constr;
      msgnl (str "and operconstr is");
      Gram.Entry.print Pcoq.Constr.operconstr;
  | "pattern" ->
      Gram.Entry.print Pcoq.Constr.pattern
  | "tactic" ->
      msgnl (str "Entry tactic_expr is");
      Gram.Entry.print Pcoq.Tactic.tactic_expr;
      msgnl (str "Entry binder_tactic is");
      Gram.Entry.print Pcoq.Tactic.binder_tactic;
      msgnl (str "Entry simple_tactic is");
      Gram.Entry.print Pcoq.Tactic.simple_tactic;
  | "vernac" ->
      msgnl (str "Entry vernac is");
      Gram.Entry.print Pcoq.Vernac_.vernac;
      msgnl (str "Entry command is");
      Gram.Entry.print Pcoq.Vernac_.command;
      msgnl (str "Entry syntax is");
      Gram.Entry.print Pcoq.Vernac_.syntax;
      msgnl (str "Entry gallina is");
      Gram.Entry.print Pcoq.Vernac_.gallina;
      msgnl (str "Entry gallina_ext is");
      Gram.Entry.print Pcoq.Vernac_.gallina_ext;
  | _ -> error "Unknown or unprintable grammar entry."

(**********************************************************************)
(* Parse a format (every terminal starting with a letter or a single
   quote (except a single quote alone) must be quoted) *)

let parse_format (loc,str) =
  let str = " "^str in
  let l = String.length str in
  let push_token a = function
    | cur::l -> (a::cur)::l
    | [] -> [[a]] in
  let push_white n l =
    if n = 0 then l else push_token (UnpTerminal (String.make n ' ')) l in
  let close_box i b = function
    | a::(_::_ as l) -> push_token (UnpBox (b,a)) l
    | _ -> error "Non terminated box in format." in
  let close_quotation i =
    if i < String.length str & str.[i] = '\'' & (i+1 = l or str.[i+1] = ' ')
    then i+1
    else error "Incorrectly terminated quoted expression." in
  let rec spaces n i =
    if i < String.length str & str.[i] = ' ' then spaces (n+1) (i+1)
    else n in
  let rec nonspaces quoted n i =
    if i < String.length str & str.[i] <> ' ' then
      if str.[i] = '\'' & quoted &
        (i+1 >= String.length str or str.[i+1] = ' ')
      then if n=0 then error "Empty quoted token." else n
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
      | '/' when i <= String.length str & str.[i+1] = '/' ->
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
	    | 'h' when i+1 <= String.length str & str.[i+2] = 'v' ->
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
      if n = 0 then []
      else error "Ending spaces non part of a format annotation."
  and parse_box box i =
    let n = spaces 0 i in
    close_box i (box n) (parse_token (close_quotation (i+n)))
  and parse_token i =
    let n = spaces 0 i in
    let i = i+n in
    if i < l then match str.[i] with
      (* Parse a ' *)
      |	'\'' when i+1 >= String.length str or str.[i+1] = ' ' ->
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
    if str <> "" then match parse_token 0 with
      | [l] -> l
      | _ -> error "Box closed without being opened in format."
    else
      error "Empty format."
  with e ->
    Stdpp.raise_with_loc loc e

(***********************)
(* Analyzing notations *)

type symbol_token = WhiteSpace of int | String of string

let split_notation_string str =
  let push_token beg i l =
    if beg = i then l else
      let s = String.sub str beg (i - beg) in
      String s :: l
  in
  let push_whitespace beg i l =
    if beg = i then l else WhiteSpace (i-beg) :: l
  in
  let rec loop beg i =
    if i < String.length str then
      if str.[i] = ' ' then
	push_token beg i (loop_on_whitespace (i+1) (i+1))
      else
	loop beg (i+1)
    else
      push_token beg i []
  and loop_on_whitespace beg i =
    if i < String.length str then
      if str.[i] <> ' ' then
	push_whitespace beg i (loop i (i+1))
      else
	loop_on_whitespace beg (i+1)
    else
      push_whitespace beg i []
  in
  loop 0 0

(* Interpret notations with a recursive component *)

let rec find_pattern xl = function
  | Break n as x :: l, Break n' :: l' when n=n' ->
      find_pattern (x::xl) (l,l')
  | Terminal s as x :: l, Terminal s' :: l' when s = s' ->
      find_pattern (x::xl) (l,l')
  | [NonTerminal x], NonTerminal x' :: l' ->
      (x,x',xl),l'
  | [NonTerminal _], Terminal s :: _ | Terminal s :: _, _ ->
      error ("The token "^s^" occurs on one side of \"..\" but not on the other side.")
  | [NonTerminal _], Break s :: _ | Break s :: _, _ ->
      error ("A break occurs on one side of \"..\" but not on the other side.")
  | ((SProdList _ | NonTerminal _) :: _ | []), _ ->
      error ("The special symbol \"..\" must occur in a configuration of the form\n\"x symbs .. symbs y\".")

let rec interp_list_parser hd = function
  | [] -> [], [], List.rev hd
  | NonTerminal id :: tl when id = ldots_var ->
      let ((x,y,sl),tl') = find_pattern [] (hd,tl) in
      let yl,xl,tl'' = interp_list_parser [] tl' in
      (* We remember each pair of variable denoting a recursive part to *)
      (* remove the second copy of it afterwards *)
      (y,x)::yl, x::xl, SProdList (x,sl) :: tl''
  | (Terminal _ | Break _) as s :: tl ->
      if hd = [] then
        let yl,xl,tl' = interp_list_parser [] tl in
        yl, xl, s :: tl'
      else
        interp_list_parser (s::hd) tl
  | NonTerminal _ as x :: tl ->
      let yl,xl,tl' = interp_list_parser [x] tl in
      yl, xl, List.rev_append hd tl'
  | SProdList _ :: _ -> anomaly "Unexpected SProdList in interp_list_parser"

(* Find non-terminal tokens of notation *)

let is_normal_token str =
  try let _ = Lexer.check_ident str in true with Lexer.Error _ -> false

(* To protect alphabetic tokens and quotes from being seen as variables *)
let quote_notation_token x =
  let n = String.length x in
  let norm = is_normal_token x in
  if (n > 0 & norm) or (n > 2 & x.[0] = '\'') then "'"^x^"'"
  else x

let rec raw_analyze_notation_tokens = function
  | []    -> []
  | String ".." :: sl -> NonTerminal ldots_var :: raw_analyze_notation_tokens sl
  | String "_" :: _ -> error "_ must be quoted."
  | String x :: sl when is_normal_token x ->
      Lexer.check_ident x;
      NonTerminal (Names.id_of_string x) :: raw_analyze_notation_tokens sl
  | String s :: sl ->
      Lexer.check_keyword s;
      Terminal (drop_simple_quotes s) :: raw_analyze_notation_tokens sl
  | WhiteSpace n :: sl ->
      Break n :: raw_analyze_notation_tokens sl

let is_numeral symbs =
  match List.filter (function Break _ -> false | _ -> true) symbs with
  | ([Terminal "-"; Terminal x] | [Terminal x]) ->
      (try let _ = Bigint.of_string x in true with _ -> false)
  | _ ->
      false

let rec get_notation_vars = function
  | [] -> []
  | NonTerminal id :: sl ->
      let vars = get_notation_vars sl in
      if List.mem id vars then
        if id <> ldots_var then
	  error ("Variable "^string_of_id id^" occurs more than once.")
        else
          vars
      else
        id::vars
  | (Terminal _ | Break _) :: sl -> get_notation_vars sl
  | SProdList _ :: _ -> assert false

let analyze_notation_tokens l =
  let l = raw_analyze_notation_tokens l in
  let vars = get_notation_vars l in
  let extrarecvars,recvars,l = interp_list_parser [] l in
  (if extrarecvars = [] then [], [], vars, l
   else extrarecvars, recvars, list_subtract vars recvars, l)

let remove_extravars extrarecvars (vars,recvars) =
  let vars =
    List.fold_right (fun (x,y) l ->
      if List.assoc x l <> List.assoc y recvars then
	error
	 "Two end variables of a recursive notation are not in the same scope."
      else
	List.remove_assoc x l)
      extrarecvars (List.remove_assoc ldots_var vars) in
  (vars,recvars)

(**********************************************************************)
(* Build pretty-printing rules                                        *)

type printing_precedence = int * parenRelation
type parsing_precedence = int option

let prec_assoc = function
  | Gramext.RightA -> (L,E)
  | Gramext.LeftA -> (E,L)
  | Gramext.NonA -> (L,L)

let precedence_of_entry_type from = function
  | ETConstr (NumLevel n,BorderProd (_,None)) -> n, Prec n
  | ETConstr (NumLevel n,BorderProd (b,Some a)) ->
      n, let (lp,rp) = prec_assoc a in if b=Left then lp else rp
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

let is_left_bracket s =
  let l = String.length s in l <> 0 &
  (s.[0] = '{' or s.[0] = '[' or s.[0] = '(')

let is_right_bracket s =
  let l = String.length s in l <> 0 &
  (s.[l-1] = '}' or s.[l-1] = ']' or s.[l-1] = ')')

let is_left_bracket_on_left s =
  let l = String.length s in l <> 0 & s.[l-1] = '>'

let is_right_bracket_on_right s =
  let l = String.length s in l <> 0 & s.[0] = '<'

let is_comma s =
  let l = String.length s in l <> 0 &
  (s.[0] = ',' or s.[0] = ';')

let is_operator s =
  let l = String.length s in l <> 0 &
  (s.[0] = '+' or s.[0] = '*' or s.[0] = '=' or
   s.[0] = '-' or s.[0] = '/' or s.[0] = '<' or s.[0] = '>' or
   s.[0] = '@' or s.[0] = '\\' or s.[0] = '&' or s.[0] = '~' or s.[0] = '$')

let is_prod_ident = function
  | Terminal s when is_letter s.[0] or s.[0] = '_' -> true
  | _ -> false

let rec is_non_terminal = function
  | NonTerminal _ | SProdList _ -> true
  | _ -> false

let add_break n l = UnpCut (PpBrk(n,0)) :: l

(* Heuristics for building default printing rules *)

type previous_prod_status = NoBreak | CanBreak

let make_hunks etyps symbols from =
  let vars,typs = List.split etyps in
  let rec make ws = function
    | NonTerminal m :: prods ->
	let i = list_index m vars in
	let _,prec = precedence_of_entry_type from (List.nth typs (i-1)) in
	let u = UnpMetaVar (i,prec) in
	if prods <> [] && is_non_terminal (List.hd prods) then
	  u :: add_break 1 (make CanBreak prods)
	else
	  u :: make CanBreak prods

    | Terminal s :: prods when List.exists is_non_terminal prods ->
        if is_comma s then
	  UnpTerminal s :: add_break 1 (make NoBreak prods)
	else if is_right_bracket s then
	  UnpTerminal s :: add_break 0 (make NoBreak prods)
	else if is_left_bracket s then
          if ws = CanBreak then
	    add_break 1 (UnpTerminal s :: make CanBreak prods)
	  else
	    UnpTerminal s :: make CanBreak prods
	else if is_operator s then
	  if ws = CanBreak then
	    UnpTerminal (" "^s) :: add_break 1 (make NoBreak prods)
	  else
	    UnpTerminal s :: add_break 1 (make NoBreak prods)
	else if is_ident_tail s.[String.length s - 1] then
	  let sep = if is_prod_ident (List.hd prods) then "" else " " in
	  if ws = CanBreak then
	    add_break 1 (UnpTerminal (s^sep) :: make CanBreak prods)
	  else
	    UnpTerminal (s^sep) :: make CanBreak prods
	else if ws = CanBreak then
	  add_break 1 (UnpTerminal (s^" ") :: make CanBreak prods)
	else
	  UnpTerminal s :: make CanBreak prods

    | Terminal s :: prods ->
	if is_right_bracket s then
	  UnpTerminal s ::make NoBreak prods
        else if ws = CanBreak then
	  add_break 1 (UnpTerminal s :: make NoBreak prods)
        else
          UnpTerminal s :: make NoBreak prods

    | Break n :: prods ->
	add_break n (make NoBreak prods)

    | SProdList (m,sl) :: prods ->
	let i = list_index m vars in
	let _,prec = precedence_of_entry_type from (List.nth typs (i-1)) in
        let sl' =
          (* If no separator: add a break *)
	  if sl = [] then add_break 1 []
          (* We add NonTerminal for simulation but remove it afterwards *)
	  else snd (list_sep_last (make NoBreak (sl@[NonTerminal m])))
	in
	UnpListMetaVar (i,prec,sl') :: make CanBreak prods

    | [] -> []

  in make NoBreak symbols

(* Build default printing rules from explicit format *)

let error_format () = error "The format does not match the notation."

let rec split_format_at_ldots hd = function
  | UnpTerminal s :: fmt when s = string_of_id ldots_var -> List.rev hd, fmt
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
    | a :: sepfmt, b :: fmt when a = b -> get_tail (sepfmt, fmt)
    | [], tail -> skip_var_in_recursive_format tail
    | _ -> error "The format is not the same on the right and left hand side of the special token \"..\"." in
  let slfmt, fmt = get_head fmt in
  slfmt, get_tail (slfmt, fmt)

let hunks_of_format (from,(vars,typs)) symfmt =
  let rec aux = function
  | symbs, (UnpTerminal s' as u) :: fmt
      when s' = String.make (String.length s') ' ' ->
      let symbs, l = aux (symbs,fmt) in symbs, u :: l
  | Terminal s :: symbs, (UnpTerminal s') :: fmt
      when s = drop_simple_quotes s' ->
      let symbs, l = aux (symbs,fmt) in symbs, UnpTerminal s :: l
  | NonTerminal s :: symbs, UnpTerminal s' :: fmt when s = id_of_string s' ->
      let i = list_index s vars in
      let _,prec = precedence_of_entry_type from (List.nth typs (i-1)) in
      let symbs, l = aux (symbs,fmt) in symbs, UnpMetaVar (i,prec) :: l
  | symbs, UnpBox (a,b) :: fmt ->
      let symbs', b' = aux (symbs,b) in
      let symbs', l = aux (symbs',fmt) in
      symbs', UnpBox (a,b') :: l
  | symbs, (UnpCut _ as u) :: fmt ->
      let symbs, l = aux (symbs,fmt) in symbs, u :: l
  | SProdList (m,sl) :: symbs, fmt ->
      let i = list_index m vars in
      let _,prec = precedence_of_entry_type from (List.nth typs (i-1)) in
      let slfmt,fmt = read_recursive_format sl fmt in
      let sl, slfmt = aux (sl,slfmt) in
      if sl <> [] then error_format ();
      let symbs, l = aux (symbs,fmt) in
      symbs, UnpListMetaVar (i,prec,slfmt) :: l
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
    GramConstrNonTerminal(e,Some _) as n1 :: GramConstrTerminal("IDENT",k) :: l
      when is_not_small_constr e ->
      message ("Defining '"^k^"' as keyword");
      Lexer.add_token("",k);
      n1 :: GramConstrTerminal("",k) :: define_keywords_aux l
  | n :: l -> n :: define_keywords_aux l
  | [] -> []

let define_keywords = function
    GramConstrTerminal("IDENT",k)::l ->
      message ("Defining '"^k^"' as keyword");
      Lexer.add_token("",k);
      GramConstrTerminal("",k) :: define_keywords_aux l
  | l -> define_keywords_aux l

let make_production etyps symbols =
  let prod =
    List.fold_right
      (fun t l -> match t with
        | NonTerminal m ->
	    let typ = List.assoc m etyps in
	    GramConstrNonTerminal (typ, Some m) :: l
        | Terminal s ->
	    GramConstrTerminal (terminal s) :: l
        | Break _ ->
            l
        | SProdList (x,sl) ->
            let sl = List.flatten
              (List.map (function Terminal s -> [terminal s]
                | Break _ -> []
                | _ -> anomaly "Found a non terminal token in recursive notation separator") sl) in
	    let y = match List.assoc x etyps with
              | ETConstr x -> x
              | _ ->
                  error "Component of recursive patterns in notation must be constr." in
            let typ = ETConstrList (y,sl) in
            GramConstrNonTerminal (typ, Some x) :: l)
      symbols [] in
  define_keywords prod

let rec find_symbols c_current c_next c_last = function
  | [] -> []
  | NonTerminal id :: sl ->
      let prec = if sl <> [] then c_current else c_last in
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
    | Some Gramext.LeftA, Some Gramext.RightA -> assert false
    | Some Gramext.LeftA, _ -> Some Gramext.LeftA
    | _, Some Gramext.RightA -> Some Gramext.RightA
    | _ -> None

(**************************************************************************)
(* Registration of syntax extensions (parsing/printing, no interpretation)*)

let pr_arg_level from = function
  | (n,L) when n=from -> str "at next level"
  | (n,E) -> str "at level " ++ int n
  | (n,L) -> str "at level below " ++ int n
  | (n,Prec m) when m=n -> str "at level " ++ int n
  | (n,_) -> str "Unknown level"

let pr_level ntn (from,args) =
  str "at level " ++ int from ++ spc () ++ str "with arguments" ++ spc() ++
  prlist_with_sep pr_coma (pr_arg_level from) args

let error_incompatible_level ntn oldprec prec =
  errorlabstrm ""
    (str ("Notation "^ntn^" is already defined") ++ spc() ++
    pr_level ntn oldprec ++
    spc() ++ str "while it is now required to be" ++ spc() ++
    pr_level ntn prec ++ str ".")

let cache_one_syntax_extension (prec,ntn,gr,pp) =
  try
    let oldprec = Notation.level_of_notation ntn in
    if prec <> oldprec then error_incompatible_level ntn oldprec prec
  with Not_found ->
    (* Reserve the notation level *)
    Notation.declare_notation_level ntn prec;
    (* Declare the parsing rule *)
    Egrammar.extend_grammar (Egrammar.Notation (prec,gr));
    (* Declare the printing rule *)
    Notation.declare_notation_printing_rule ntn (pp,fst prec)

let cache_syntax_extension (_,(_,sy_rules)) =
  List.iter cache_one_syntax_extension sy_rules

let subst_parsing_rule subst x = x

let subst_printing_rule subst x = x

let subst_syntax_extension (subst,(local,sy)) =
  (local, List.map (fun (prec,ntn,gr,pp) ->
     (prec,ntn, subst_parsing_rule subst gr, subst_printing_rule subst pp)) sy)

let classify_syntax_definition (local,_ as o) =
  if local then Dispose else Substitute o

let (inSyntaxExtension, outSyntaxExtension) =
  declare_object {(default_object "SYNTAX-EXTENSION") with
       open_function = (fun i o -> if i=1 then cache_syntax_extension o);
       cache_function = cache_syntax_extension;
       subst_function = subst_syntax_extension;
       classify_function = classify_syntax_definition}

(**************************************************************************)
(* Precedences                                                            *)

(* Interpreting user-provided modifiers *)

let interp_modifiers modl =
  let onlyparsing = ref false in
  let rec interp assoc level etyps format = function
    | [] ->
	(assoc,level,etyps,!onlyparsing,format)
    | SetEntryType (s,typ) :: l ->
	let id = id_of_string s in
	if List.mem_assoc id etyps then
	  error (s^" is already assigned to an entry or constr level.");
	interp assoc level ((id,typ)::etyps) format l
    | SetItemLevel ([],n) :: l ->
	interp assoc level etyps format l
    | SetItemLevel (s::idl,n) :: l ->
	let id = id_of_string s in
	if List.mem_assoc id etyps then
	  error (s^" is already assigned to an entry or constr level.");
	let typ = ETConstr (n,()) in
	interp assoc level ((id,typ)::etyps) format (SetItemLevel (idl,n)::l)
    | SetLevel n :: l ->
	if level <> None then error "A level is given more than once.";
	interp assoc (Some n) etyps format l
    | SetAssoc a :: l ->
	if assoc <> None then error"An associativity is given more than once.";
	interp (Some a) level etyps format l
    | SetOnlyParsing :: l ->
	onlyparsing := true;
	interp assoc level etyps format l
    | SetFormat s :: l ->
	if format <> None then error "A format is given more than once.";
	interp assoc level etyps (Some s) l
  in interp None None [] None modl

let check_infix_modifiers modifiers =
  let (assoc,level,t,b,fmt) = interp_modifiers modifiers in
  if t <> [] then
    error "Explicit entry level or type unexpected in infix notation."

let no_syntax_modifiers modifiers =
  modifiers = [] or modifiers = [SetOnlyParsing]

(* Compute precedences from modifiers (or find default ones) *)

let set_entry_type etyps (x,typ) =
  let typ = try
    match List.assoc x etyps, typ with
      | ETConstr (n,()), (_,BorderProd (left,_)) ->
          ETConstr (n,BorderProd (left,None))
      | ETConstr (n,()), (_,InternalProd) -> ETConstr (n,InternalProd)
      | (ETPattern | ETName | ETBigint | ETOther _ | ETReference as t), _ -> t
      | (ETConstrList _, _) -> assert false
    with Not_found -> ETConstr typ
  in (x,typ)

let check_rule_productivity l =
  if List.for_all (function NonTerminal _ -> true | _ -> false) l then
    error "A notation must include at least one symbol.";
  if (match l with SProdList _ :: _ -> true | _ -> false) then
    error "A recursive notation must start with at least one symbol."

let is_not_printable = function
  | AVar _ -> warning "This notation will not be used for printing as it is bound to a \nsingle variable"; true
  | _ -> false

let find_precedence lev etyps symbols =
  match symbols with
  | NonTerminal x :: _ ->
      (try match List.assoc x etyps with
	| ETConstr _ ->
	    error "The level of the leftmost non-terminal cannot be changed."
	| ETName | ETBigint | ETReference ->
	    if lev = None then
	      if_verbose msgnl (str "Setting notation at level 0.")
	    else
	    if lev <> Some 0 then
	      error "A notation starting with an atomic expression must be at level 0.";
	    0
	| ETPattern | ETOther _ -> (* Give a default ? *)
	    if lev = None then
	      error "Need an explicit level."
	    else Option.get lev
        | ETConstrList _ -> assert false (* internally used in grammar only *)
      with Not_found ->
	if lev = None then
	  error "A left-recursive notation must have an explicit level."
	else Option.get lev)
  | Terminal _ ::l when
      (match list_last symbols with Terminal _ -> true |_ -> false)
      ->
      if lev = None then
	(if_verbose msgnl (str "Setting notation at level 0."); 0)
      else Option.get lev
  | _ ->
      if lev = None then error "Cannot determine the level.";
      Option.get lev

let check_curly_brackets_notation_exists () =
  try let _ = Notation.level_of_notation "{ _ }" in ()
  with Not_found ->
    error "Notations involving patterns of the form \"{ _ }\" are treated \n\
specially and require that the notation \"{ _ }\" is already reserved."

(* Remove patterns of the form "{ _ }", unless it is the "{ _ }" notation *)
let remove_curly_brackets l =
  let rec next = function
    | Break _ :: l -> next l
    | l -> l in
  let rec aux deb = function
  | [] -> []
  | Terminal "{" as t1 :: l ->
      (match next l with
        | NonTerminal _ as x :: l' as l0 ->
            (match next l' with
              | Terminal "}" as t2 :: l'' as l1 ->
                  if l <> l0 or l' <> l1 then
                    warning "Skipping spaces inside curly brackets";
                  if deb & l'' = [] then [t1;x;t2] else begin
                    check_curly_brackets_notation_exists ();
                    x :: aux false l''
                  end
              | l1 -> t1 :: x :: aux false l1)
        | l0 -> t1 :: aux false l0)
  | x :: l -> x :: aux false l
  in aux true l

let compute_syntax_data (df,modifiers) =
  let (assoc,n,etyps,onlyparse,fmt) = interp_modifiers modifiers in
  (* Notation defaults to NONA *)
  let assoc = match assoc with None -> Some Gramext.NonA | a -> a in
  let toks = split_notation_string df in
  let (extrarecvars,recvars,vars,symbols) = analyze_notation_tokens toks in
  let ntn_for_interp = make_notation_key symbols in
  let symbols' = remove_curly_brackets symbols in
  let need_squash = (symbols <> symbols') in
  let ntn_for_grammar = make_notation_key symbols' in
  check_rule_productivity symbols';
  let n = find_precedence n etyps symbols' in
  let innerlevel = NumLevel 200 in
  let typs =
    find_symbols
      (NumLevel n,BorderProd(Left,assoc))
      (innerlevel,InternalProd)
      (NumLevel n,BorderProd(Right,assoc))
      symbols' in
  (* To globalize... *)
  let typs = List.map (set_entry_type etyps) typs in
  let prec = (n,List.map (assoc_of_type n) typs) in
  let sy_data = (ntn_for_grammar,prec,need_squash,(n,typs,symbols',fmt)) in
  let df' = (Lib.library_dp(),df) in
  let i_data = (onlyparse,extrarecvars,recvars,vars,(ntn_for_interp,df')) in
  (i_data,sy_data)

(**********************************************************************)
(* Registration of notations interpretation                            *)

let load_notation _ (_,(_,scope,pat,onlyparse,_)) =
  Option.iter Notation.declare_scope scope

let open_notation i (_,(_,scope,pat,onlyparse,(ntn,df))) =
  if i=1 & not (Notation.exists_notation_in_scope scope ntn pat) then begin
    (* Declare the interpretation *)
    Notation.declare_notation_interpretation ntn scope pat df;
    (* Declare the uninterpretation *)
    if not onlyparse then
      Notation.declare_uninterpretation (NotationRule (scope,ntn)) pat
  end

let cache_notation o =
  load_notation 1 o;
  open_notation 1 o

let subst_notation (subst,(lc,scope,pat,b,ndf)) =
  (lc,scope,subst_interpretation subst pat,b,ndf)

let classify_notation (local,_,_,_,_ as o) =
  if local then Dispose else Substitute o

let (inNotation, outNotation) =
  declare_object {(default_object "NOTATION") with
       open_function = open_notation;
       cache_function = cache_notation;
       subst_function = subst_notation;
       load_function = load_notation;
       classify_function = classify_notation}

(**********************************************************************)
(* Recovering existing syntax                                         *)

let contract_notation ntn =
  if ntn = "{ _ }" then ntn else
  let rec aux ntn i =
    if i <= String.length ntn - 5 then
      let ntn' =
        if String.sub ntn i 5 = "{ _ }" then
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
    let pprule,_ = Notation.find_notation_printing_rule ntn in
    let gr = Egrammar.recover_notation_grammar ntn prec in
    (prec,ntn,gr,pprule)
  with Not_found ->
    raise NoSyntaxRule

let recover_squash_syntax () = recover_syntax "{ _ }"

let recover_notation_syntax rawntn =
  let ntn = contract_notation rawntn in
  let sy_rule = recover_syntax ntn in
  let need_squash = ntn<>rawntn in
  if need_squash then [sy_rule; recover_squash_syntax ()] else [sy_rule]

(**********************************************************************)
(* Main entry point for building parsing and printing rules           *)

let make_pa_rule (n,typs,symbols,_) ntn =
  let assoc = recompute_assoc typs in
  let prod = make_production typs symbols in
  (n,assoc,ntn,prod)

let make_pp_rule (n,typs,symbols,fmt) =
  match fmt with
  | None -> [UnpBox (PpHOVB 0, make_hunks typs symbols n)]
  | Some fmt -> hunks_of_format (n,List.split typs) (symbols,parse_format fmt)

let make_syntax_rules (ntn,prec,need_squash,sy_data) =
  let pa_rule = make_pa_rule sy_data ntn in
  let pp_rule = make_pp_rule sy_data in
  let sy_rule = (prec,ntn,pa_rule,pp_rule) in
  (* By construction, the rule for "{ _ }" is declared, but we need to
     redeclare it because the file where it is declared needs not be open
     when the current file opens (especially in presence of -nois) *)
  if need_squash then [sy_rule; recover_squash_syntax ()] else [sy_rule]

(**********************************************************************)
(* Main functions about notations                                     *)

let add_notation_in_scope local df c mods scope =
  let (i_data,sy_data) = compute_syntax_data (df,mods) in
  (* Declare the parsing and printing rules *)
  let sy_rules = make_syntax_rules sy_data in
  Lib.add_anonymous_leaf (inSyntaxExtension(local,sy_rules));
  (* Declare interpretation *)
  let (onlyparse,extrarecvars,recvars,vars,df') = i_data in
  let (acvars,ac) = interp_aconstr (vars,recvars) c in
  let a = (remove_extravars extrarecvars acvars,ac) in
  let onlyparse = onlyparse or is_not_printable ac in
  Lib.add_anonymous_leaf (inNotation (local,scope,a,onlyparse,df'))

let add_notation_interpretation_core local df ?(impls=empty_internalization_env) c scope onlyparse =
  let dfs = split_notation_string df in
  let (extrarecvars,recvars,vars,symbs) = analyze_notation_tokens dfs in
  (* Redeclare pa/pp rules *)
  if not (is_numeral symbs) then begin
    let sy_rules = recover_notation_syntax (make_notation_key symbs) in
    Lib.add_anonymous_leaf (inSyntaxExtension (local,sy_rules))
  end;
  (* Declare interpretation *)
  let df' = (make_notation_key symbs,(Lib.library_dp(),df)) in
  let (acvars,ac) = interp_aconstr ~impls (vars,recvars) c in
  let a = (remove_extravars extrarecvars acvars,ac) in
  let onlyparse = onlyparse or is_not_printable ac in
  Lib.add_anonymous_leaf (inNotation (local,scope,a,onlyparse,df'))

(* Notations without interpretation (Reserved Notation) *)

let add_syntax_extension local mv =
  let (_,sy_data) = compute_syntax_data mv in
  let sy_rules = make_syntax_rules sy_data in
  Lib.add_anonymous_leaf (inSyntaxExtension(local,sy_rules))

(* Notations with only interpretation *)

let add_notation_interpretation (df,c,sc) =
  add_notation_interpretation_core false df c sc false

let set_notation_for_interpretation impls (df,c,sc) =
  Option.iter (fun sc -> Notation.open_close_scope (false,true,sc)) sc;
  try silently (add_notation_interpretation_core false df ~impls c sc) false;
  with NoSyntaxRule ->
    error "Parsing rule for this notation has to be previously declared."

(* Main entry point *)

let add_notation local c (df,modifiers) sc =
  if no_syntax_modifiers modifiers then
    (* No syntax data: try to rely on a previously declared rule *)
    let onlyparse = modifiers=[SetOnlyParsing] in
    try add_notation_interpretation_core local df c sc onlyparse
    with NoSyntaxRule ->
      (* Try to determine a default syntax rule *)
      add_notation_in_scope local df c modifiers sc
  else
    (* Declare both syntax and interpretation *)
    add_notation_in_scope local df c modifiers sc

(* Infix notations *)

let inject_var x = CRef (Ident (dummy_loc, id_of_string x))

let add_infix local (inf,modifiers) pr sc =
  check_infix_modifiers modifiers;
  (* check the precedence *)
  let metas = [inject_var "x"; inject_var "y"] in
  let c = mkAppC (pr,metas) in
  let df = "x "^(quote_notation_token inf)^" y" in
  add_notation local c (df,modifiers) sc

(**********************************************************************)
(* Delimiters and classes bound to scopes                             *)

type scope_command = ScopeDelim of string | ScopeClasses of Classops.cl_typ

let load_scope_command _ (_,(scope,dlm)) =
  Notation.declare_scope scope

let open_scope_command i (_,(scope,o)) =
  if i=1 then
    match o with
    | ScopeDelim dlm -> Notation.declare_delimiters scope dlm
    | ScopeClasses cl -> Notation.declare_class_scope scope cl

let cache_scope_command o =
  load_scope_command 1 o;
  open_scope_command 1 o

let subst_scope_command (subst,(scope,o as x)) = match o with
  | ScopeClasses cl ->
      let cl' = Classops.subst_cl_typ subst cl in if cl'==cl then x else
      scope, ScopeClasses cl'
  | _ -> x

let (inScopeCommand,outScopeCommand) =
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
  | [], CRef ref -> intern_reference ref
  | _ -> raise Not_found

let add_syntactic_definition ident (vars,c) local onlyparse =
  let vars,pat =
    try [], ARef (try_interp_name_alias (vars,c))
    with Not_found -> let (vars,_),pat = interp_aconstr (vars,[]) c in vars,pat
  in
  let onlyparse = onlyparse or is_not_printable pat in
  Syntax_def.declare_syntactic_definition local ident onlyparse (vars,pat)

