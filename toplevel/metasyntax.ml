(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Topconstr
open Coqast
open Ast
open Ppextend
open Extend
open Esyntax
open Libobject
open Library
open Summary
open Constrintern
open Vernacexpr
open Pcoq
open Rawterm
open Libnames

let interp_global_rawconstr_with_vars vars c =
  interp_rawconstr_gen false Evd.empty (Global.env()) false (vars,[]) c

(**********************************************************************)
(* Parsing via ast (used in Zsyntax) *)

(* This updates default parsers for Grammar actions and Syntax *)
(* patterns by inserting globalization *)
(* Done here to get parsing/g_*.ml4 non dependent from kernel *)
let constr_to_ast a =
  Termast.ast_of_rawconstr (interp_rawconstr Evd.empty (Global.env()) a)

(* This installs default quotations parsers to escape the ast parser *)
(* "constr" is used by default in quotations found in the ast parser *) 
let constr_parser_with_glob = Pcoq.map_entry constr_to_ast Constr.constr

let _ = define_ast_quotation true "constr" constr_parser_with_glob

(**********************************************************************)
(* Globalisation for constr_expr *)

let globalize_ref vars ref =
  match Constrintern.interp_reference (vars,[]) ref with
  | RRef (loc,VarRef a) -> Ident (loc,a)
  | RRef (loc,a) -> Qualid (loc,qualid_of_sp (Nametab.sp_of_global a))
  | RVar (loc,x) -> Ident (loc,x)
  | _ -> anomaly "globalize_ref: not a reference"

let globalize_ref_term vars ref =
  match Constrintern.interp_reference (vars,[]) ref with
  | RRef (loc,VarRef a) -> CRef (Ident (loc,a))
  | RRef (loc,a) -> CRef (Qualid (loc,qualid_of_sp (Nametab.sp_of_global a)))
  | RVar (loc,x) -> CRef (Ident (loc,x))
  | c -> Constrextern.extern_rawconstr Idset.empty c 

let rec globalize_constr_expr vars = function
  | CRef ref -> globalize_ref_term vars ref
  | CAppExpl (_,(p,ref),l) ->
      let f = 
	map_constr_expr_with_binders globalize_constr_expr
	  (fun x e -> e) vars
      in
      CAppExpl (dummy_loc,(p,globalize_ref vars ref), List.map f l)
  | c ->
      map_constr_expr_with_binders globalize_constr_expr (fun id e -> id::e)
        vars c

let without_translation f x =
  let old = Options.do_translate () in
  let oldv7 = !Options.v7 in
  Options.make_translate false;
  try let r = f x in Options.make_translate old; Options.v7:=oldv7; r
  with e -> Options.make_translate old; Options.v7:=oldv7; raise e

let _ = set_constr_globalizer
  (fun vars e -> for_grammar (without_translation (globalize_constr_expr vars)) e)

(**********************************************************************)
(** For old ast printer *)

(* Pretty-printer state summary *)
let _ = 
  declare_summary "syntax"
    { freeze_function = Esyntax.freeze;
      unfreeze_function = Esyntax.unfreeze;
      init_function = Esyntax.init;
      survive_module = false;
      survive_section = false }

(* Pretty-printing objects = syntax_entry *)
let cache_syntax (_,ppobj) = Esyntax.add_ppobject ppobj

let subst_syntax (_,subst,ppobj) = 
  Extend.subst_syntax_command Ast.subst_astpat subst ppobj

let (inPPSyntax,outPPSyntax) =
  declare_object {(default_object "PPSYNTAX") with
       open_function = (fun i o -> if i=1 then cache_syntax o);
       cache_function = cache_syntax;
       subst_function = subst_syntax;
       classify_function = (fun (_,o) -> Substitute o);       
       export_function = (fun x -> Some x) }

(* Syntax extension functions (registered in the environnement) *)

(* Checking the pretty-printing rules against free meta-variables.
 * Note that object are checked before they are added in the environment.
 * Syntax objects in compiled modules are not re-checked. *)

let add_syntax_obj whatfor sel =
(*  if not !Options.v7_only then*)
  Lib.add_anonymous_leaf (inPPSyntax (interp_syntax_entry whatfor sel))

(* Tokens *)

let cache_token (_,s) = Pcoq.lexer.Token.using ("", s)

let (inToken, outToken) =
  declare_object {(default_object "TOKEN") with
       open_function = (fun i o -> if i=1 then cache_token o);
       cache_function = cache_token;
       subst_function = Libobject.ident_subst_function;
       classify_function = (fun (_,o) -> Substitute o);
       export_function = (fun x -> Some x)}

let add_token_obj s = Lib.add_anonymous_leaf (inToken s)

(**********************************************************************)
(* Grammars (especially Tactic Notation) *)

let make_terminal_status = function
  | VTerm s -> Some s
  | VNonTerm _ -> None

let qualified_nterm current_univ = function
  | NtQual (univ, en) -> (univ, en)
  | NtShort en -> (current_univ, en)

let rec make_tags = function
  | VTerm s :: l -> make_tags l
  | VNonTerm (loc, nt, po) :: l ->
      let (u,nt) = qualified_nterm "tactic" nt in
      let (etyp, _) = Egrammar.interp_entry_name u nt in
      etyp :: make_tags l
  | [] -> []

let declare_pprule = function
  (* Pretty-printing rules only for Grammar (Tactic Notation) *)
  | Egrammar.TacticGrammar (_,pp) ->
      let f (s,t,p) =
        Pptactic.declare_extra_tactic_pprule true s (t,p);
        Pptactic.declare_extra_tactic_pprule false s (t,p) in
      List.iter f pp
  | _ -> ()

let cache_grammar (_,a) =
  Egrammar.extend_grammar a;
  declare_pprule a

let subst_grammar (_,subst,a) =
  Egrammar.subst_all_grammar_command subst a

let (inGrammar, outGrammar) =
  declare_object {(default_object "GRAMMAR") with
       open_function = (fun i o -> if i=1 then cache_grammar o);
       cache_function = cache_grammar;
       subst_function = subst_grammar;
       classify_function = (fun (_,o) -> Substitute o);
       export_function = (fun x -> Some x)}

(**********************************************************************)
(* V7 Grammar                                                         *)

open Genarg

let check_entry_type (u,n) =
  if u = "tactic" or u = "vernac" then error "tactic and vernac not supported";
  match entry_type (get_univ u) n with
    | None -> Pcoq.create_entry_if_new (get_univ u) n ConstrArgType
    | Some (ConstrArgType | IdentArgType | RefArgType) -> ()
    | _ -> error "Cannot arbitrarily extend non constr/ident/ref entries"

let add_grammar_obj univ entryl =
  let u = create_univ_if_new univ in
  let g = interp_grammar_command univ check_entry_type entryl in
  Lib.add_anonymous_leaf (inGrammar (Egrammar.Grammar g))

(**********************************************************************)
(* V8 Grammar *)

(* Tactic notations *)

let rec tactic_notation_key = function
  | VTerm id :: _ -> id
  | _ :: l -> tactic_notation_key l
  | [] -> "terminal_free_notation"

let rec next_key_away key t =
  if Pptactic.exists_extra_tactic_pprule key t then next_key_away (key^"'") t
  else key

let locate_tactic_body dir (s,(s',prods as x),e) =
  let tags = make_tags prods in
  let s = if s="" then next_key_away (tactic_notation_key prods) tags else s in
  (s,x,(dir,e)),(s,tags,(s',List.map make_terminal_status prods))

let add_tactic_grammar g =
  let dir = Lib.cwd () in
  let pa,pp = List.split (List.map (locate_tactic_body dir) g) in
  Lib.add_anonymous_leaf (inGrammar (Egrammar.TacticGrammar (pa,pp)))

(* Printing grammar entries *)

let print_grammar univ entry =
  if !Options.v7 then
    let u = get_univ univ in
    let typ = explicitize_entry (fst u) entry in
    let te,_,_ = get_constr_entry false typ in
    Gram.Entry.print te
  else
    match entry with
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
	  Gram.Entry.print Pcoq.Tactic.simple_tactic
      | _ -> error "Unknown or unprintable grammar entry"

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
    | _ -> error "Non terminated box in format" in
  let close_quotation i =
    if i < String.length str & str.[i] = '\'' & (i+1 = l or str.[i+1] = ' ')
    then i+1
    else error "Incorrectly terminated quoted expression" in
  let rec spaces n i =
    if i < String.length str & str.[i] = ' ' then spaces (n+1) (i+1)
    else n in
  let rec nonspaces quoted n i =
    if i < String.length str & str.[i] <> ' ' then
      if str.[i] = '\'' & quoted &
        (i+1 >= String.length str or str.[i+1] = ' ')
      then if n=0 then error "Empty quoted token" else n
      else nonspaces quoted (n+1) (i+1)
    else
      if quoted then error "Spaces are not allowed in (quoted) symbols"
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
	    | _ -> error "\"v\", \"hv\", \" \" expected after \"[\" in format"
	  else error "\"v\", \"hv\" or \" \" expected after \"[\" in format"
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
      else error "Ending spaces non part of a format annotation"
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
      | _ -> error "Box closed without being opened in format"
    else
      error "Empty format"
  with e ->
    Stdpp.raise_with_loc loc e

(***********************)
(* Analysing notations *)

open Symbols

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

let unquote_notation_token s =
  let n = String.length s in
  if n > 2 & s.[0] = '\'' & s.[n-1] = '\'' then String.sub s 1 (n-2) else s

let is_normal_token str =
  try let _ = Lexer.check_ident str in true with Lexer.Error _ -> false

(* To protect alphabetic tokens and quotes from being seen as variables *)
let quote_notation_token x =
  let n = String.length x in
  let norm = is_normal_token x in
  if (n > 0 & norm) or (n > 2 & x.[0] = '\'') then "'"^x^"'"
  else x

let rec raw_analyse_notation_tokens = function
  | []    -> [], []
  | String ".." :: sl ->
      let (vars,l) = raw_analyse_notation_tokens sl in
      (list_add_set ldots_var vars, NonTerminal ldots_var :: l)
  | String x :: sl when is_normal_token x ->
      Lexer.check_ident x;
      let id = Names.id_of_string x in
      let (vars,l) = raw_analyse_notation_tokens sl in
      if List.mem id vars then
	error ("Variable "^x^" occurs more than once");
      (id::vars, NonTerminal id :: l)
  | String s :: sl ->
      Lexer.check_keyword s;
      let (vars,l) = raw_analyse_notation_tokens sl in
      (vars, Terminal (unquote_notation_token s) :: l)
  | WhiteSpace n :: sl ->
      let (vars,l) = raw_analyse_notation_tokens sl in
      (vars, Break n :: l)

let rec find_pattern xl = function
  | Break n as x :: l, Break n' :: l' when n=n' -> 
      find_pattern (x::xl) (l,l')
  | Terminal s as x :: l, Terminal s' :: l' when s = s' -> 
      find_pattern (x::xl) (l,l')
  | [NonTerminal x], NonTerminal x' :: l' ->
      (x,x',xl),l'
  | [NonTerminal _], Terminal s :: _ | Terminal s :: _, _ ->
      error ("The token "^s^" occurs on one side of \"..\" but not on the other side")
  | [NonTerminal _], Break s :: _ | Break s :: _, _ ->
      error ("A break occurs on one side of \"..\" but not on the other side")
  | ((SProdList _ | NonTerminal _) :: _ | []), _ -> 
      error ("The special symbol \"..\" must occur in a configuration of the form\n\"x symbs .. symbs y\"")

let rec interp_list_parser hd = function
  | [] -> [], List.rev hd
  | NonTerminal id :: tl when id = ldots_var ->
      let ((x,y,sl),tl') = find_pattern [] (hd,tl) in
      let yl,tl'' = interp_list_parser [] tl' in
      (* We remember the second copy of each recursive part variable to *)
      (* remove it afterwards *)
      y::yl, SProdList (x,sl) :: tl''
  | (Terminal _ | Break _) as s :: tl ->
      if hd = [] then 
        let yl,tl' = interp_list_parser [] tl in
        yl, s :: tl'
      else
        interp_list_parser (s::hd) tl
  | NonTerminal _ as x :: tl ->
      let yl,tl' = interp_list_parser [x] tl in
      yl, List.rev_append hd tl'
  | SProdList _ :: _ -> anomaly "Unexpected SProdList in interp_list_parser"

let analyse_notation_tokens l =
  let vars,l = raw_analyse_notation_tokens l in
  let recvars,l = interp_list_parser [] l in
  ((if recvars = [] then [] else ldots_var::recvars), vars, l)

let remove_vars = List.fold_right List.remove_assoc
 
(* Build the syntax and grammar rules *)

type printing_precedence = int * parenRelation
type parsing_precedence = int option

let prec_assoc = function
  | Gramext.RightA -> (L,E)
  | Gramext.LeftA -> (E,L)
  | Gramext.NonA -> (L,L)

(* For old ast printer *)
let meta_pattern m = Pmeta(m,Tany)

type white_status = Juxtapose | Separate of int | NextIsTerminal

let precedence_of_entry_type from = function
  | ETConstr (NumLevel n,BorderProd (_,None)) -> n, Prec n
  | ETConstr (NumLevel n,BorderProd (left,Some a)) ->
      n, let (lp,rp) = prec_assoc a in if left then lp else rp
  | ETConstr (NumLevel n,InternalProd) -> n, Prec n
  | ETConstr (NextLevel,_) -> from, L
  | ETOther ("constr","annot") -> 10, Prec 10
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
   s.[0] = '@' or s.[0] = '\\' or s.[0] = '&' or s.[0] = '~')

type previous_prod_status = NoBreak | CanBreak

let rec is_non_terminal = function
  | NonTerminal _ | SProdList _ -> true
  | _ -> false

let add_break n l = UNP_BRK (n,1) :: l

(* For old ast printer *)
let make_hunks_ast symbols etyps from =
  let rec make ws = function
    | NonTerminal m :: prods ->
	let _,lp = precedence_of_entry_type from (List.assoc m etyps) in
	let u = PH (meta_pattern (string_of_id m), None, lp) in
	if prods <> [] && is_non_terminal (List.hd prods) then
	  u :: add_break 1 (make CanBreak prods)
	else
	  u :: make CanBreak prods

    | Terminal s :: prods when List.exists is_non_terminal prods ->
	let protect =
	  is_letter s.[0] ||
	  (is_non_terminal (List.hd prods) &&
	    (is_letter (s.[String.length s -1])) ||
	    (is_digit (s.[String.length s -1]))) in
	if is_comma s || is_right_bracket s then
	  RO s :: add_break 0 (make NoBreak prods)
	else if (is_operator s || is_left_bracket s) && ws = CanBreak then
	  add_break (if protect then 1 else 0)
	    (RO (if protect then s^" " else s) :: make CanBreak prods)
	else
          if protect then
            (if ws = CanBreak then add_break 1 else (fun x -> x))
	    (RO (s^" ") :: make CanBreak prods)
          else
	    RO s :: make CanBreak prods

    | Terminal s :: prods ->
	RO s :: make NoBreak prods

    | Break n :: prods ->
	add_break n (make NoBreak prods)

    | SProdList _ :: _ ->
        anomaly "Recursive notations not supported in old syntax"

    | [] -> []

  in make NoBreak symbols

let add_break n l = UnpCut (PpBrk(n,0)) :: l

let make_hunks etyps symbols from =
  let vars,typs = List.split etyps in
  let rec make ws = function
    | NonTerminal m :: prods ->
	let i = list_index m vars in
	let _,prec = precedence_of_entry_type from (List.nth typs (i-1)) in
	let u = UnpMetaVar (i ,prec) in
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
	  if ws = CanBreak then
	    add_break 1 (UnpTerminal (s^" ") :: make CanBreak prods)
	  else
	    UnpTerminal (s^" ") :: make CanBreak prods
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
        (* We add NonTerminal for simulation but remove it afterwards *)
        let _,sl' = list_sep_last (make NoBreak (sl@[NonTerminal m])) in
	UnpListMetaVar (i,prec,sl') :: make CanBreak prods

    | [] -> []

  in make NoBreak symbols

let error_format () = error "The format does not match the notation"

let rec split_format_at_ldots hd = function
  | UnpTerminal s :: fmt when id_of_string s = ldots_var -> List.rev hd, fmt
  | u :: fmt -> 
      check_no_ldots_in_box u;
      split_format_at_ldots (u::hd) fmt
  | [] -> raise Exit

and check_no_ldots_in_box = function
  | UnpBox (_,fmt) ->
      (try 
        let _ = split_format_at_ldots [] fmt in
        error ("The special symbol \"..\" must occur at the same formatting depth than the variables of which it is the ellipse")
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
    | _ -> error "The format is not the same on the right and left hand side of the special token \"..\"" in
  let slfmt, fmt = get_head fmt in
  slfmt, get_tail (slfmt, fmt)

let hunks_of_format (from,(vars,typs) as vt) symfmt = 
  let rec aux = function
  | symbs, (UnpTerminal s' as u) :: fmt
      when s' = String.make (String.length s') ' ' ->
      let symbs, l = aux (symbs,fmt) in symbs, u :: l
  | Terminal s :: symbs, (UnpTerminal s' as u) :: fmt
      when s = unquote_notation_token s' ->
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

let string_of_prec (n,p) =
  (string_of_int n)^(match p with E -> "E" | L -> "L" | _ -> "")

let assoc_of_type n (_,typ) = precedence_of_entry_type n typ

let string_of_assoc = function
  | Some(Gramext.RightA) -> "RIGHTA"
  | Some(Gramext.LeftA) | None -> "LEFTA"
  | Some(Gramext.NonA) -> "NONA"

let is_not_small_constr = function
    ETConstr _ -> true
  | ETOther("constr","binder_constr") -> true
  | _ -> false

let rec define_keywords = function
    NonTerm(_,Some(_,e)) as n1 :: Term("IDENT",k) :: l
     when not !Options.v7 && is_not_small_constr e ->
      prerr_endline ("Defining '"^k^"' as keyword");
      Lexer.add_token("",k);
      n1 :: Term("",k) :: define_keywords l
  | n :: l -> n :: define_keywords l
  | [] -> []

let define_keywords = function
    Term("IDENT",k)::l when not !Options.v7 ->
      prerr_endline ("Defining '"^k^"' as keyword");
      Lexer.add_token("",k);
      Term("",k) :: define_keywords l
  | l -> define_keywords l

let make_production etyps symbols =
  let prod =
    List.fold_right
      (fun t l -> match t with
        | NonTerminal m ->
	    let typ = List.assoc m etyps in
	    NonTerm (typ, Some (m,typ)) :: l
        | Terminal s ->
	    Term (Extend.terminal s) :: l
        | Break _ ->
            l
        | SProdList (x,sl) ->
            let sl = List.flatten
              (List.map (function Terminal s -> [Extend.terminal s] 
                | Break _ -> []
                | _ -> anomaly "Found a non terminal token in recursive notation separator") sl) in
	    let y = match List.assoc x etyps with
              | ETConstr x -> x
              | _ ->
                  error "Component of recursive patterns in notation must be constr" in
            let typ = ETConstrList (y,sl) in
            NonTerm (typ, Some (x,typ)) :: l)
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

let make_grammar_rule n typs symbols ntn perm =
  let assoc = recompute_assoc typs in
  let prod = make_production typs symbols in
  (n,assoc,ntn,prod, perm)

(* For old ast printer *)
let metas_of sl =
  List.fold_right
    (fun it metatl -> match it with
      | NonTerminal m -> m::metatl
      | _ -> metatl)
    sl []

(* For old ast printer *)
let make_pattern symbols ast =
  let env = List.map (fun m -> (string_of_id m,ETast)) (metas_of symbols) in
  fst (to_pat env ast)

(* For old ast printer *)
let make_syntax_rule n name symbols typs ast ntn sc =
  [{syn_id = name;
    syn_prec = n;
    syn_astpat = make_pattern symbols ast;
    syn_hunks =
      [UNP_SYMBOLIC(sc,ntn,UNP_BOX (PpHOVB 1,make_hunks_ast symbols typs n))]}]

let make_pp_rule (n,typs,symbols,fmt) =
  match fmt with
    | None -> [UnpBox (PpHOVB 0, make_hunks typs symbols n)]
    | Some fmt -> 
	[UnpBox (PpHOVB 0, 
	 hunks_of_format (n,List.split typs) (symbols,parse_format fmt))]

(**************************************************************************)
(* Syntax extenstion: common parsing/printing rules and no interpretation *)

(* v7 and translator : prec is for v7 (None if V8Notation), prec8 is for v8 *)
(* v8 : prec is for v8, prec8 is the same *)

let pr_arg_level from = function
  | (n,L) when n=from -> str "at next level"
  | (n,E) -> str "at level " ++ int n
  | (n,L) -> str "at level below " ++ int n
  | (n,Prec m) when m=n -> str "at level " ++ int n
  | (n,_) -> str "Unknown level"

let pr_level ntn (from,args) =
  let lopen = ntn.[0] = '_' and ropen = ntn.[String.length ntn - 1] = '_' in
(*
  let ppassoc, args = match args with
    | [] -> mt (), []
    | (nl,lpr)::l when nl=from & fst (list_last l)=from ->
	let (_,rpr),l = list_sep_last l in
	match lpr, snd (list_last l) with
	  | L,E -> Gramext.RightA, l
	  | E,L -> Gramext.LeftA, l
	  | L,L -> Gramext.NoneA, l
	  | _ -> args
*)
  str "at level " ++ int from ++ spc () ++ str "with arguments" ++ spc() ++
  prlist_with_sep pr_coma (pr_arg_level from) args

(* In v8: prec = Some prec8 is for both parsing and printing *)
(* In v7 and translator: 
     prec is for parsing (None if V8Notation), 
     prec8 for v8 printing (v7 printing is via ast) *)
let cache_syntax_extension (_,(_,((prec,prec8),ntn,gr,se))) =
  try 
    let oldprec, oldprec8 = Symbols.level_of_notation ntn in
    if prec8 <> oldprec8 & (Options.do_translate () or not !Options.v7) then
      errorlabstrm ""
	(str ((if Options.do_translate () then "For new syntax, notation "
	else "Notation ")
	^ntn^" is already defined") ++ spc() ++ pr_level ntn oldprec8 ++ 
	spc() ++ str "while it is now required to be" ++ spc() ++ 
	pr_level ntn prec8)
    else
      (* Inconsistent v8 notations but not while translating; forget... *)
      ();
    (* V8 notations are consistent (from both translator or v8) *)
    if prec <> None & !Options.v7 then begin
      (* Update the V7 parsing rule *)
      if oldprec <> None & out_some oldprec <> out_some prec then
	(* None of them is V8Notation and they are different: warn *)
	Options.if_verbose
	  warning ("Notation "^ntn^
	  " was already assigned a different level or sublevels");
      if oldprec = None or out_some oldprec <> out_some prec then
        Egrammar.extend_grammar (Egrammar.Notation (out_some prec,out_some gr))
    end
  with Not_found ->
    (* Reserve the notation level *)
    Symbols.declare_notation_level ntn (prec,prec8);
    (* Declare the parsing rule *)
    option_iter (fun gr -> 
      Egrammar.extend_grammar (Egrammar.Notation (out_some prec,gr))) gr;
    (* Declare the printing rule *)
    Symbols.declare_notation_printing_rule ntn (se,fst prec8)

let subst_notation_grammar subst x = x

let subst_printing_rule subst x = x

let subst_syntax_extension (_,subst,(local,(prec,ntn,gr,se))) =
  (local,(prec,ntn,
   option_app (subst_notation_grammar subst) gr,
   subst_printing_rule subst se))

let classify_syntax_definition (_,(local,_ as o)) =
  if local then Dispose else Substitute o

let export_syntax_definition (local,_ as o) =
  if local then None else Some o

let (inSyntaxExtension, outSyntaxExtension) =
  declare_object {(default_object "SYNTAX-EXTENSION") with
       open_function = (fun i o -> if i=1 then cache_syntax_extension o);
       cache_function = cache_syntax_extension;
       subst_function = subst_syntax_extension;
       classify_function = classify_syntax_definition;
       export_function = export_syntax_definition}

let interp_modifiers modl =
  let onlyparsing = ref false in
  let rec interp assoc level etyps format = function
    | [] ->
	(assoc,level,etyps,!onlyparsing,format)
    | SetEntryType (s,typ) :: l ->
	let id = id_of_string s in
	if List.mem_assoc id etyps then
	  error (s^" is already assigned to an entry or constr level")
	else interp assoc level ((id,typ)::etyps) format l
    | SetItemLevel ([],n) :: l ->
	interp assoc level etyps format l
    | SetItemLevel (s::idl,n) :: l ->
	let id = id_of_string s in
	if List.mem_assoc id etyps then
	  error (s^" is already assigned to an entry or constr level")
	else
	  let typ = ETConstr (n,()) in
	  interp assoc level ((id,typ)::etyps) format (SetItemLevel (idl,n)::l)
    | SetLevel n :: l ->
	if level <> None then error "A level is given more than once"
	else interp assoc (Some n) etyps format l
    | SetAssoc a :: l ->
	if assoc <> None then error "An associativity is given more than once"
	else interp (Some a) level etyps format l
    | SetOnlyParsing :: l ->
	onlyparsing := true;
	interp assoc level etyps format l
    | SetFormat s :: l ->
	if format <> None then error "A format is given more than once";
	interp assoc level etyps (Some s) l
  in interp None None [] None modl

let merge_modifiers a n l =
  (match a with None -> [] | Some a -> [SetAssoc a]) @
  (match n with None -> [] | Some n -> [SetLevel n]) @ l

let interp_infix_modifiers modl =
  let (assoc,level,t,b,fmt) = interp_modifiers modl in
  if t <> [] then
    error "explicit entry level or type unexpected in infix notation";
  (assoc,level,b,fmt)

(* 2nd list of types has priority *)
let rec merge_entry_types etyps' = function
  | [] -> etyps'
  | (x,_ as e)::etyps ->
      e :: merge_entry_types (List.remove_assoc x etyps') etyps

let set_entry_type etyps (x,typ) =
  let typ = try 
    match List.assoc x etyps, typ with
      | ETConstr (n,()), (_,BorderProd (left,_)) ->
          ETConstr (n,BorderProd (left,None))
      | ETConstr (n,()), (_,InternalProd) -> ETConstr (n,InternalProd)
      | (ETPattern | ETIdent | ETBigint | ETOther _ | ETReference as t), _ -> t
      | (ETConstrList _, _) -> assert false
    with Not_found -> ETConstr typ
  in (x,typ)

let check_rule_reversibility l = 
  if List.for_all (function NonTerminal _ -> true | _ -> false) l then
    error "A notation must include at least one symbol"

let is_not_printable = function
  | AVar _ -> warning "This notation won't be used for printing as it is bound to a \nsingle variable"; true
  | _ -> false

let find_precedence_v7 lev etyps symbols =
  (match symbols with
    | NonTerminal x :: _ ->
	(try match List.assoc x etyps with
	  | ETConstr _ ->
	      error "The level of the leftmost non-terminal cannot be changed"
	  | _ -> ()
	with Not_found -> ())
    | _ -> ());
  if lev = None then 1 else out_some lev

let find_precedence lev etyps symbols =
  match symbols with
  | NonTerminal x :: _ ->
      (try match List.assoc x etyps with
	| ETConstr _ ->
	    error "The level of the leftmost non-terminal cannot be changed"
	| ETIdent | ETBigint | ETReference -> 
	    if lev = None then 
	      Options.if_verbose msgnl (str "Setting notation at level 0")
	    else
	    if lev <> Some 0 then
	      error "A notation starting with an atomic expression must be at level 0";
	    0
	| ETPattern | ETOther _ -> (* Give a default ? *)
	    if lev = None then
	      error "Need an explicit level"
	    else out_some lev
        | ETConstrList _ -> assert false (* internally used in grammar only *)
      with Not_found -> 
	if lev = None then
	  error "A left-recursive notation must have an explicit level"
	else out_some lev)
  | Terminal _ ::l when
      (match list_last symbols with Terminal _ -> true |_ -> false)
      -> 
      if lev = None then
	(Options.if_verbose msgnl (str "Setting notation at level 0"); 0)
      else out_some lev
  | _ ->
      if lev = None then error "Cannot determine the level";
      out_some lev

let check_curly_brackets_notation_exists () =
  try let _ = Symbols.level_of_notation "{ _ }" in ()
  with Not_found -> 
    error "Notations involving patterns of the form \"{ _ }\" are treated \n\
specially and require that the notation \"{ _ }\" is already reserved"

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

let compute_syntax_data forv7 (df,modifiers) =
  let (assoc,n,etyps,onlyparse,fmt) = interp_modifiers modifiers in
  (* Notation defaults to NONA *)
  let assoc = match assoc with None -> Some Gramext.NonA | a -> a in
  let toks = split_notation_string df in
  let (recvars,vars,symbols) = analyse_notation_tokens toks in
  let ntn_for_interp = make_notation_key symbols in
  let symbols = remove_curly_brackets symbols in
  let notation = make_notation_key symbols in
  check_rule_reversibility symbols;
  let n =
    if !Options.v7 then find_precedence_v7 n etyps symbols
    else find_precedence n etyps symbols in
  let innerlevel = NumLevel (if forv7 then 10 else 200) in
  let typs =
    find_symbols
      (NumLevel n,BorderProd(true,assoc))
      (innerlevel,InternalProd)
      (NumLevel n,BorderProd(false,assoc))
      symbols in
  (* To globalize... *)
  let typs = List.map (set_entry_type etyps) typs in
  let ppdata = (n,typs,symbols,fmt) in
  let prec = (n,List.map (assoc_of_type n) typs) in
  ((onlyparse,recvars,vars,
    ntn_for_interp,notation),prec,ppdata,(Lib.library_dp(),df))

(* Uninterpreted (reserved) notations *)
let add_syntax_extension local mv mv8 =
  (* from v7: 
       if mv8 <> None: tells the translator how to print in v8
       if mv <> None: tells how to parse and, how to print in v7
       mv = None = mv8 does not occur   
     from v8 (mv8 is always None and mv is always Some)
       mv tells how to parse and print in v8
  *)
  let data8 = option_app (compute_syntax_data false) mv8 in
  let data = option_app (compute_syntax_data !Options.v7) mv in
  let prec,gram_rule = match data with
  | None -> None, None (* Case of V8Notation from v7 *)
  | Some ((_,_,_,_,notation),prec,(n,typs,symbols,_),_) -> 
      Some prec, Some (make_grammar_rule n typs symbols notation None) in
  match data, data8 with
  | None, None -> (* Nothing to do: V8Notation while not translating *) () 
  | _, Some d | Some d, None ->
    let ((_,_,_,_,ntn),ppprec,ppdata,_) = d in (* tells how to print *)
    let ntn' = match data with Some ((_,_,_,_,ntn),_,_,_) -> ntn | _ -> ntn in
    let pp_rule = make_pp_rule ppdata in
    Lib.add_anonymous_leaf
      (inSyntaxExtension (local,((prec,ppprec),ntn',gram_rule,pp_rule)))

(**********************************************************************)
(* Distfix, Infix, Symbols *)

(* A notation comes with a grammar rule, a pretty-printing rule, an
   identifiying pattern called notation and an associated scope *)
let load_notation _ (_,(_,_,ntn,scope,pat,onlyparse,_,_)) =
  option_iter Symbols.declare_scope scope

let open_notation i (_,(_,oldse,ntn,scope,pat,onlyparse,pp8only,df)) =
  if i=1 then begin
    let b,oldpp8only = Symbols.exists_notation_in_scope scope ntn pat in
    (* Declare the old printer rule and its interpretation *)
    if (not b or oldpp8only) & oldse <> None then
      Esyntax.add_ppobject {sc_univ="constr";sc_entries=out_some oldse};
    (* Declare the interpretation *)
    if not b then
      Symbols.declare_notation_interpretation ntn scope pat df pp8only;
    if oldpp8only & not pp8only then
      Options.silently 
	(Symbols.declare_notation_interpretation ntn scope pat df) pp8only;
    if not b & not onlyparse then
      Symbols.declare_uninterpretation (NotationRule (scope,ntn)) pat
  end

let cache_notation o =
  load_notation 1 o;
  open_notation 1 o

let subst_notation (_,subst,(lc,oldse,ntn,scope,(metas,pat),b,b',df)) =
  (lc,option_app
    (list_smartmap (Extend.subst_syntax_entry Ast.subst_astpat subst)) oldse,
   ntn,scope,
   (metas,subst_aconstr subst pat), b, b', df)

let classify_notation (_,(local,_,_,_,_,_,_,_ as o)) =
  if local then Dispose else Substitute o

let export_notation (local,_,_,_,_,_,_,_ as o) =
  if local then None else Some o

let (inNotation, outNotation) =
  declare_object {(default_object "NOTATION") with
       open_function = open_notation;
       cache_function = cache_notation;
       subst_function = subst_notation;
       load_function = load_notation;
       classify_function = classify_notation;
       export_function = export_notation}

(* For old ast printer *)
let rec reify_meta_ast vars = function
  | Smetalam (loc,s,body) -> Smetalam (loc,s,reify_meta_ast vars body)
(*  | Node(loc,"META",[Num (_,n)]) -> Nmeta (loc,create_meta n)*)
  | Node(loc,"ISEVAR",[]) -> Nmeta (loc,"$_")
  | Node(loc,op,args) -> Node (loc,op, List.map (reify_meta_ast vars) args)
  | Slam(loc,Some id,body) when List.mem id vars ->
      Smetalam (loc,string_of_id id,reify_meta_ast vars body)
  | Slam(loc,na,body) -> Slam(loc,na,reify_meta_ast vars body)
  | Nvar (loc,id) when List.mem id vars -> Nmeta (loc,string_of_id id)
  | Nmeta _ | Id _ | Nvar _ | Str _ | Num _ | Path _ as a -> a
  | Dynamic _ as a -> (* Hum... what to do here *) a

(* For old ast syntax *)
let make_old_pp_rule n symbols typs r ntn scope vars =
  let ast = Termast.ast_of_rawconstr r in
  let ast = reify_meta_ast vars ast in
  let scope_name = match scope with Some s -> s | None -> "core_scope" in
  let rule_name = ntn^"_"^scope_name^"_notation" in
  make_syntax_rule n rule_name symbols typs ast ntn scope

(* maps positions in v8-notation into positions in v7-notation (used
   for parsing).
   For instance  Notation "x < y < z" := .. V8only "y < z < x"
   yields [1; 2; 0] (y is the second arg in v7; z is 3rd; x is fst) *)
let mk_permut vars7 vars8 =
  if vars7=vars8 then None else
    Some
      (List.fold_right
        (fun v8 subs -> list_index v8 vars7 - 1 :: subs)
        vars8 [])

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

let add_notation_in_scope local df c mods omodv8 scope toks =
  let ((onlyparse,recs,vars,intnot,notation),prec,(n,typs,symbols,_ as ppdata),df')=
    compute_syntax_data !Options.v7 (df,mods) in
  (* Declare the parsing and printing rules if not already done *)
    (* For both v7 and translate: parsing is as described for v7 in v7 file *)
    (* For v8: parsing is as described in v8 file *)
    (* For v7: printing is by the old printer - see below *)
    (* For translate: printing is as described for v8 in v7 file *)
    (* For v8: printing is as described in v8 file *)
    (* In short: parsing does not depend on omodv8 *)
    (* Printing depends on mv8 if defined, otherwise of mods (scaled by 10) *)
    (* if in v7, or of mods without scaling if in v8 *)
  let intnot,ntn,pprecvars,ppvars,ppprec,pp_rule =
    match omodv8 with
    | Some mv8 ->
        let (_,recs8,vars8,intnot8,ntn8),p,d,_ = compute_syntax_data false mv8 in
        intnot8,ntn8,recs8,vars8,p,make_pp_rule d
    | None when not !Options.v7 -> 
        intnot,notation,recs,vars,prec,make_pp_rule ppdata
    | None ->
	(* means the rule already exists: recover it *)
        (* occurs only with V8only flag alone *)
	try 
          let ntn = contract_notation notation in
	  let _, oldprec8 = Symbols.level_of_notation ntn in
	  let rule,_ = Symbols.find_notation_printing_rule ntn in
	  notation,ntn,recs,vars,oldprec8,rule
	with Not_found -> error "No known parsing rule for this notation in V8"
  in
  let permut = mk_permut vars ppvars in
  let gram_rule = make_grammar_rule n typs symbols ntn permut in
  Lib.add_anonymous_leaf
    (inSyntaxExtension
      (local,((Some prec,ppprec),ntn,Some gram_rule,pp_rule)));

  (* Declare interpretation *)
  let (acvars,ac) = interp_aconstr [] ppvars c in
  let a = (remove_vars pprecvars acvars,ac) (* For recursive parts *) in
  let old_pp_rule =
    (* Used only by v7; disable if contains a recursive pattern *)
    if onlyparse or pprecvars <> [] or not (!Options.v7) then None
    else
      let r = interp_global_rawconstr_with_vars vars c in
      Some (make_old_pp_rule n symbols typs r intnot scope vars) in
  let onlyparse = onlyparse or !Options.v7_only or is_not_printable ac in
  Lib.add_anonymous_leaf
    (inNotation(local,old_pp_rule,intnot,scope,a,onlyparse,false,df'))

let level_rule (n,p) = if p = E then n else max (n-1) 0

let recover_syntax ntn = 
  try 
    match Symbols.level_of_notation ntn with
      | (Some prec,_ as pprec) -> 
	  let rule,_ = Symbols.find_notation_printing_rule ntn in
	  let gr = Egrammar.recover_notation_grammar ntn prec in
	  Some (pprec,ntn,Some gr,rule)
      | None,_ -> None
  with Not_found -> None

let recover_notation_syntax rawntn =
  let ntn = contract_notation rawntn in
  match recover_syntax ntn with
    | None -> None
    | Some gr -> Some (gr,if ntn=rawntn then None else recover_syntax "{ _ }")

let set_data_for_v7_pp recs a vars =
  if not !Options.v7 then None else
    if recs=[] then Some (a,vars)
    else (warning "No recursive notation in v7 syntax";None)

let build_old_pp_rule notation scope symbs (r,vars) =
  let prec = 
    try
      let a,_ = Symbols.level_of_notation (contract_notation notation) in
      if a = None then raise Not_found else out_some a
    with Not_found ->
      error "Parsing rule for this notation has to be previously declared" in
  let typs = List.map2 
    (fun id n -> 
      id,ETConstr (NumLevel (level_rule n),InternalProd)) vars (snd prec) in
  make_old_pp_rule (fst prec) symbs typs r notation scope vars

let add_notation_interpretation_core local symbs for_old df a scope onlyparse 
  onlypp gram_data =
  let notation = make_notation_key symbs in
  let old_pp_rule = 
    if !Options.v7 then 
      option_app (build_old_pp_rule notation scope symbs) for_old
    else None in
  option_iter
    (fun (x,y) ->
      Lib.add_anonymous_leaf (inSyntaxExtension (local,x));
      option_iter
	(fun z -> Lib.add_anonymous_leaf (inSyntaxExtension (local,z))) y)
    gram_data;
  Lib.add_anonymous_leaf
    (inNotation(local,old_pp_rule,notation,scope,a,onlyparse,onlypp,
     (Lib.library_dp(),df)))

let add_notation_interpretation df names c sc =
  let (recs,vars,symbs) = analyse_notation_tokens (split_notation_string df) in
  let gram_data = recover_notation_syntax (make_notation_key symbs) in
  if gram_data = None then
    error "Parsing rule for this notation has to be previously declared";
  let (acvars,ac) = interp_aconstr names vars c in
  let a = (remove_vars recs acvars,ac) (* For recursive parts *) in
  let a_for_old = interp_rawconstr_with_implicits Evd.empty (Global.env()) vars names c in
  let for_oldpp = set_data_for_v7_pp recs a_for_old vars in
  let onlyparse = is_not_printable ac in
  add_notation_interpretation_core false symbs for_oldpp df a sc onlyparse 
    false gram_data

let add_notation_in_scope_v8only local df c mv8 scope toks =
  let (_,recs,vars,intnot,notation),prec,ppdata,df' = compute_syntax_data false (df,mv8) in
  let pp_rule = make_pp_rule ppdata in
  Lib.add_anonymous_leaf
    (inSyntaxExtension(local,((None,prec),notation,None,pp_rule)));
  (* Declare the interpretation *)
  let (acvars,ac) = interp_aconstr [] vars c in
  let a = (remove_vars recs acvars,ac) (* For recursive parts *) in
  let onlyparse = is_not_printable ac in
  Lib.add_anonymous_leaf
    (inNotation(local,None,intnot,scope,a,onlyparse,true,df'))

let add_notation_v8only local c (df,modifiers) sc =
  let toks = split_notation_string df in
  match toks with 
    | [String x] when (modifiers = [] or modifiers = [SetOnlyParsing]) ->
	(* This is a ident to be declared as a rule *)
        add_notation_in_scope_v8only local df c (SetLevel 0::modifiers) sc toks
    | _ ->
	let (assoc,lev,typs,onlyparse,fmt) = interp_modifiers modifiers	in
	match lev with
	  | None->
	      if modifiers <> [] & modifiers <> [SetOnlyParsing] then
		error "Parsing rule for this notation includes no level"
	      else
	        (* Declare only interpretation *)
		let (recs,vars,symbs) = analyse_notation_tokens toks in
                let (acvars,ac) = interp_aconstr [] vars c in
		let onlyparse = modifiers = [SetOnlyParsing] 
                  or is_not_printable ac in
                let a = (remove_vars recs acvars,ac) in
		add_notation_interpretation_core local symbs None df a sc 
		  onlyparse true None
	  | Some n ->
	    (* Declare both syntax and interpretation *)
	      let mods =
		if List.for_all (function SetAssoc _ -> false | _ -> true)
		  modifiers 
		then SetAssoc Gramext.NonA :: modifiers else modifiers in
	      add_notation_in_scope_v8only local df c mods sc toks

let is_quoted_ident x =
  let x' = unquote_notation_token x in
  x <> x' & try Lexer.check_ident x'; true with _ -> false

(* v7: dfmod=None; mv8=Some: add only v8 printing rule *)
(*     dfmod=Some: add v7 parsing rule; mv8=Some: add v8 printing rule *)
(*     dfmod=Some; mv8=None: same v7-parsing and v8-printing rules *)
(* v8: dfmod=Some; mv8=None: same v8 parsing and printing rules *)
let add_notation local c dfmod mv8 sc =
  match dfmod with
  | None -> add_notation_v8only local c (out_some mv8) sc
  | Some (df,modifiers) ->
  let toks = split_notation_string df in
  match toks with 
    | [String x] when (modifiers = [] or modifiers = [SetOnlyParsing]) ->
	(* This is a ident to be declared as a rule *)
        add_notation_in_scope local df c (SetLevel 0::modifiers) mv8 sc toks
    | _ ->
	let (assoc,lev,typs,onlyparse,fmt) = interp_modifiers modifiers	in
	match lev with
	  | None->
	      if modifiers <> [] & modifiers <> [SetOnlyParsing] then
		error "Parsing rule for this notation includes no level"
	      else
	        (* Declare only interpretation *)
		let (recs,vars,symbs) = analyse_notation_tokens toks in
                let gram_data =
		  recover_notation_syntax (make_notation_key symbs) in
		if gram_data <> None then
                  let (acvars,ac) = interp_aconstr [] vars c in
                  let a = (remove_vars recs acvars,ac) in
		  let onlyparse = modifiers = [SetOnlyParsing] 
                    or is_not_printable ac in
		  let a_for_old = interp_global_rawconstr_with_vars vars c in
                  let for_old = set_data_for_v7_pp recs a_for_old vars in
		  add_notation_interpretation_core local symbs for_old df a
		    sc onlyparse false gram_data
                else
                  add_notation_in_scope local df c modifiers mv8 sc toks
	  | Some n ->
	    (* Declare both syntax and interpretation *)
	    let assoc = match assoc with None -> Some Gramext.NonA | a -> a in
            add_notation_in_scope local df c modifiers mv8 sc toks

(* TODO add boxes information in the expression *)

let inject_var x = CRef (Ident (dummy_loc, id_of_string x))

let rec rename x vars n = function
  | [] ->
      (vars,[])
  | String "_"::l ->
      let (vars,l) = rename x vars (n+1) l in
      let xn = x^(string_of_int n) in
      ((inject_var xn)::vars,xn::l)
  | String y::l ->
      let (vars,l) = rename x vars n l in (vars,(quote_notation_token y)::l)
  | WhiteSpace _::l ->
      rename x vars n l

let translate_distfix assoc df r = 
  let (vars,l) = rename "x" [] 1 (split_notation_string df) in
  let df = String.concat " " l in
  let a = mkAppC (mkRefC r, vars) in
  let assoc = match assoc with None -> Gramext.LeftA | Some a -> a in
  (assoc,df,a)

let add_distfix local assoc n df r sc =
  (* "x" cannot clash since r is globalized (included section vars) *)
  let (vars,l) = rename "x" [] 1 (split_notation_string df) in
  let df = String.concat " " l in
  let a = mkAppC (mkRefC r, vars) in
  let assoc = match assoc with None -> Gramext.LeftA | Some a -> a in
  add_notation_in_scope local df a [SetAssoc assoc;SetLevel n] None sc
    (split_notation_string df)

let make_infix_data n assoc modl mv8 =
  (* Infix defaults to LEFTA in V7 (cf doc) *)
  let mv = match n with None when !Options.v7 -> SetLevel 1 :: modl | _ -> modl in
  let mv = match assoc with None when !Options.v7 -> SetAssoc Gramext.LeftA :: mv | _ -> mv in
  let mv8 = match mv8 with
      None -> None
    | Some(s8,mv8) ->
	if List.for_all (function SetLevel _ -> false | _ -> true) mv8 then
	  error "Needs a level"
	else Some (("x "^quote_notation_token s8^" y"),mv8) in
  mv,mv8

let add_infix local (inf,modl) pr mv8 sc =
  if inf="" (* Code for V8Infix only *) then
    let (p8,mv8) = out_some mv8 in
    let (a8,n8,onlyparse,fmt) = interp_infix_modifiers mv8 in
    let metas = [inject_var "x"; inject_var "y"] in
    let a = mkAppC (mkRefC pr,metas) in
    let df = "x "^(quote_notation_token p8)^" y" in
    let toks = split_notation_string df in
    if a8=None & n8=None & fmt=None then
      (* Declare only interpretation *)
      let (recs,vars,symbs) = analyse_notation_tokens toks in
      let (acvars,ac) = interp_aconstr [] vars a in
      let a' = (remove_vars recs acvars,ac) in
      let a_for_old = interp_global_rawconstr_with_vars vars a in
      add_notation_interpretation_core local symbs None df a' sc 
	onlyparse true None
    else
      if n8 = None then error "Needs a level" else
      let mv8 = match a8 with None -> SetAssoc Gramext.NonA :: mv8 |_ -> mv8 in
      add_notation_in_scope_v8only local df a mv8 sc toks
  else begin
  let (assoc,n,onlyparse,fmt) = interp_infix_modifiers modl in
  (* check the precedence *)
  if !Options.v7 & (n<> None & (out_some n < 1 or out_some n > 10)) then
    errorlabstrm "Metasyntax.infix_grammar_entry"
      (str"Precedence must be between 1 and 10.");
  (*
  if (assoc<>None) & (n<6 or n>9) then
    errorlabstrm "Vernacentries.infix_grammar_entry"
      (str"Associativity Precedence must be 6,7,8 or 9.");
  *)
  let metas = [inject_var "x"; inject_var "y"] in
  let a = mkAppC (mkRefC pr,metas) in
  let df = "x "^(quote_notation_token inf)^" y" in
  let toks = split_notation_string df in
  if not !Options.v7 & n=None & assoc=None then
    (* En v8, une notation sans information de parsing signifie *)
    (* de ne déclarer que l'interprétation *)
    (* Declare only interpretation *)
    let (recs,vars,symbs) = analyse_notation_tokens toks in
    let gram_data = recover_notation_syntax (make_notation_key symbs) in
    if gram_data <> None then 
      let (acvars,ac) = interp_aconstr [] vars a in
      let a' = (remove_vars recs acvars,ac) in
      let a_for_old = interp_global_rawconstr_with_vars vars a in
      let for_old = set_data_for_v7_pp recs a_for_old vars in
      add_notation_interpretation_core local symbs for_old df a' sc 
        onlyparse false gram_data
    else
      let mv,mv8 = make_infix_data n assoc modl mv8 in
      add_notation_in_scope local df a mv mv8 sc toks
  else
    let mv,mv8 = make_infix_data n assoc modl mv8 in
    add_notation_in_scope local df a mv mv8 sc toks
  end

let standardise_locatable_notation ntn =
  let unquote = function
    | String s -> [unquote_notation_token s]
    | _ -> [] in
  if String.contains ntn ' ' then
    String.concat " " 
      (List.flatten (List.map unquote (split_notation_string ntn)))
  else
    unquote_notation_token ntn

(* Delimiters and classes bound to scopes *)
type scope_command = ScopeDelim of string | ScopeClasses of Classops.cl_typ

let load_scope_command _ (_,(scope,dlm)) =
  Symbols.declare_scope scope

let open_scope_command i (_,(scope,o)) =
  if i=1 then
    match o with
    | ScopeDelim dlm -> Symbols.declare_delimiters scope dlm
    | ScopeClasses cl -> Symbols.declare_class_scope scope cl

let cache_scope_command o =
  load_scope_command 1 o;
  open_scope_command 1 o

let subst_scope_command (_,subst,(scope,o as x)) = match o with
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
      classify_function = (fun (_,obj) -> Substitute obj);
      export_function = (fun x -> Some x) }

let add_delimiters scope key =
  Lib.add_anonymous_leaf (inScopeCommand(scope,ScopeDelim key))

let add_class_scope scope cl = 
  Lib.add_anonymous_leaf (inScopeCommand(scope,ScopeClasses cl))
