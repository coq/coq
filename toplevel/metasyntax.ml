(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

(*************************
 **** PRETTY-PRINTING ****
 *************************)

(* This updates default parsers for Grammar actions and Syntax *)
(* patterns by inserting globalization *)
(* Done here to get parsing/g_*.ml4 non dependent from kernel *)
let constr_to_ast a =
  Termast.ast_of_rawconstr (interp_rawconstr Evd.empty (Global.env()) a)

(* This installs default quotations parsers to escape the ast parser *)
(* "constr" is used by default in quotations found in the ast parser *) 
let constr_parser_with_glob = Pcoq.map_entry constr_to_ast Constr.constr

let globalize_ref vars ref =
  match Constrintern.interp_reference (vars,[]) ref with
  | RRef (loc,VarRef id) -> Ident (loc,id)
  | RRef (loc,a) -> Qualid (loc,qualid_of_sp (Nametab.sp_of_global None a))
  | RVar (loc,x) -> Ident (loc,x)
  | _ -> anomaly "globalize_ref: not a reference"

let globalize_ref_term vars ref =
  match Constrintern.interp_reference (vars,[]) ref with
  | RRef (loc,VarRef id) -> CRef (Ident (loc,id))
  | RRef (loc,a) -> 
      CRef (Qualid (loc,qualid_of_sp (Nametab.sp_of_global None a)))
  | RVar (loc,x) -> CRef (Ident (loc,x))
  | c -> Constrextern.extern_rawconstr c 

let rec globalize_constr_expr vars = function
  | CRef ref -> globalize_ref_term vars ref
  | CAppExpl (_,ref,l) ->
      let f = 
	map_constr_expr_with_binders globalize_constr_expr
	  (fun x e -> e) vars
      in
      CAppExpl (dummy_loc,globalize_ref vars ref, List.map f l)
  | c ->
      map_constr_expr_with_binders globalize_constr_expr (fun id e -> id::e)
        vars c

let _ = set_constr_globalizer
  (fun vars e -> for_grammar (globalize_constr_expr vars) e)

let _ = define_ast_quotation true "constr" constr_parser_with_glob

(** For old ast printer *)

(* Pretty-printer state summary *)
let _ = 
  declare_summary "syntax"
    { freeze_function = Esyntax.freeze;
      unfreeze_function = Esyntax.unfreeze;
      init_function = Esyntax.init;
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
  Lib.add_anonymous_leaf (inPPSyntax (interp_syntax_entry whatfor sel))


(**********************************************************************)
(* Grammar                                                            *)

let _ = 
  declare_summary "GRAMMAR_LEXER"
    { freeze_function = Egrammar.freeze;
      unfreeze_function = Egrammar.unfreeze;
      init_function = Egrammar.init;
      survive_section = false }

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

(* Grammar rules *)
let cache_grammar (_,a) = Egrammar.extend_grammar a
let subst_grammar (_,subst,a) = Egrammar.subst_all_grammar_command subst a

let (inGrammar, outGrammar) =
  declare_object {(default_object "GRAMMAR") with
       open_function = (fun i o -> if i=1 then cache_grammar o);
       cache_function = cache_grammar;
       subst_function = subst_grammar;
       classify_function = (fun (_,o) -> Substitute o);
       export_function = (fun x -> Some x)}

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

let add_tactic_grammar g = 
  Lib.add_anonymous_leaf (inGrammar (Egrammar.TacticGrammar g))

(* printing grammar entries *)
let print_grammar univ entry =
  let u = get_univ univ in
  let typ = explicitize_entry (fst u) entry in
  let te,_,_ = get_constr_entry typ in
  Gram.Entry.print te

(* Infix, distfix, notations *)

type token = WhiteSpace of int | String of string

let split str =
  let push_token beg i l =
    if beg == i then l else String (String.sub str beg (i - beg)) :: l 
  in
  let push_whitespace beg i l =
    if beg = i then l else WhiteSpace (i-beg) :: l 
  in
  let rec loop beg i =
    if i < String.length str then
      if str.[i] == ' ' then
	push_token beg i (loop_on_whitespace (succ i) (succ i))
      else
	loop beg (succ i)
    else
      push_token beg i []
  and loop_on_whitespace beg i =
    if i < String.length str then
      if str.[i] <> ' ' then
	push_whitespace beg i (loop i (succ i))
      else
	loop_on_whitespace beg (succ i)
    else
      push_whitespace beg i []
  in
  loop 0 0

(* Build the syntax and grammar rules *)

type printing_precedence = int * parenRelation
type parsing_precedence = int option

type symbol =
  | Terminal of string
  | NonTerminal of identifier
  | Break of int

let prec_assoc = function
  | Gramext.RightA -> (L,E)
  | Gramext.LeftA -> (E,L)
  | Gramext.NonA -> (L,L)

let level_rule (n,p) = if p = E then n else max (n-1) 0

(* For old ast printer *)
let meta_pattern m = Pmeta(m,Tany)

open Symbols

type white_status = Juxtapose | Separate of int | NextIsTerminal

let precedence_of_entry_type = function
  | ETConstr (n,BorderProd (_,None)) -> n, Prec n
  | ETConstr (n,BorderProd (left,Some a)) ->
      n, let (lp,rp) = prec_assoc a in if left then lp else rp
  | ETConstr (n,InternalProd) -> n, Prec n
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
  (s.[0] = ',' or s.[0] = ';' or s.[0] = ':')

let is_operator s =
  let l = String.length s in l <> 0 &
  (s.[0] = '+' or s.[0] = '*' or s.[0] = '=' or
   s.[0] = '-' or s.[0] = '/' or s.[0] = '<' or s.[0] = '>' or
   s.[0] = '@')

type previous_prod_status = NoBreak | CanBreak

let is_non_terminal = function
  | NonTerminal _ -> true
  | _ -> false

let add_break n l = UNP_BRK (n,1) :: l

(* For old ast printer *)
let make_hunks_ast symbols etyps from =
  let rec make ws = function
    | NonTerminal m :: prods ->
	let _,lp = precedence_of_entry_type (List.assoc m etyps) in
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

    | [] -> []

  in make NoBreak symbols

let add_break n l = UnpCut (PpBrk(n,1)) :: l

let make_hunks etyps symbols =
  let vars,typs = List.split etyps in
  let rec make ws = function
    | NonTerminal m :: prods ->
	let i = list_index m vars in
	let _,prec = precedence_of_entry_type (List.nth typs (i-1)) in
	let u = UnpMetaVar (i ,prec) in
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
	  UnpTerminal s :: add_break 0 (make NoBreak prods)
	else if (is_operator s || is_left_bracket s) && ws = CanBreak then
	  add_break (if protect then 1 else 0)
	    (UnpTerminal (if protect then s^" " else s) :: make CanBreak prods)
	else
          if protect then
            (if ws = CanBreak then add_break 1 else (fun x -> x))
	      (UnpTerminal (s^" ") :: make CanBreak prods)
          else
	    UnpTerminal s :: make CanBreak prods

    | Terminal s :: prods ->
	UnpTerminal s :: make NoBreak prods

    | Break n :: prods ->
	add_break n (make NoBreak prods)

    | [] -> []

  in make NoBreak symbols

let string_of_prec (n,p) =
  (string_of_int n)^(match p with E -> "E" | L -> "L" | _ -> "")

let string_of_symbol = function
  | NonTerminal _ -> ["_"]
  | Terminal s -> [s]
  | Break _ -> []

let assoc_of_type (_,typ) = level_rule (precedence_of_entry_type typ)

let string_of_assoc = function
  | Some(Gramext.RightA) -> "RIGHTA"
  | Some(Gramext.LeftA) | None -> "LEFTA"
  | Some(Gramext.NonA) -> "NONA"

let make_symbolic n symbols etyps =
  (n,List.map assoc_of_type etyps),
  (String.concat " " (List.flatten (List.map string_of_symbol symbols)))

let make_production etyps symbols =
  List.fold_right
    (fun t l -> match t with
      | NonTerminal m ->
	  let typ = List.assoc m etyps in
	  NonTerm (ProdPrimitive typ, Some (m,typ)) :: l
      | Terminal s ->
	  Term (Extend.terminal s) :: l
      | Break _ ->
	  l)
    symbols []

let strip s =
  let n = String.length s in
  if n > 2 & s.[0] = '\'' & s.[n-1] = '\'' then String.sub s 1 (n-2) else s

(* To protect alphabetic tokens from being seen as variables *)
let quote x =
  let n = String.length x in
  if n > 0 &
    (is_letter x.[0] or is_letter x.[n-1] or is_digit x.[n-1] or x.[n-1]='\'')
  then
    "\'"^x^"\'"
  else
    x

let is_symbol = function String s -> not (is_letter s.[0]) | _ -> false

let rec find_symbols c_current c_next c_last vars = function
  | []    -> (vars, [])
  | String x :: sl when is_letter x.[0] ->
      let id = Names.id_of_string x in
      if List.mem_assoc id vars then
	error ("Variable "^x^" occurs more than once");
(*      let prec = if List.exists is_symbol sl then c_current else c_last in*)
      let prec = if sl <> [] then c_current else c_last in
      let (vars,l) = find_symbols c_next c_next c_last vars sl in
      ((id,prec)::vars, NonTerminal id :: l)
(*
  | "_"::sl ->
      warning "Found '_'";
      let prec = if List.exists is_symbols sl then c_first else c_last in
      let (vars,l) =
        find_symbols c_next c_next c_last vars (new_var+1) varprecl sl in
      let meta = create_meta new_var in
      (vars, NonTerminal (prec, meta) :: l)
*)
  | String s :: sl ->
      let (vars,l) = find_symbols c_next c_next c_last vars sl in
      (vars, Terminal (strip s) :: l)
  | WhiteSpace n :: sl ->
      let (vars,l) = find_symbols c_current c_next c_last vars sl in
      (vars, Break n :: l)

let make_grammar_rule n assoc typs symbols ntn =
  let prod = make_production typs symbols in
  (n,assoc,ntn,prod)

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

let make_pp_rule symbols typs =
  [UnpBox (PpHOVB 0, make_hunks symbols typs)]


(**************************************************************************)
(* Syntax extenstion: common parsing/printing rules and no interpretation *)

let cache_syntax_extension (_,(prec,ntn,gr,se)) =
  if not (Symbols.exists_notation prec ntn) then begin
    Egrammar.extend_grammar (Egrammar.Notation gr);
    if se<>None then
      Symbols.declare_notation_printing_rule ntn (out_some se,fst prec)
  end

let subst_notation_grammar subst x = x

let subst_printing_rule subst x = x

let subst_syntax_extension (_,subst,(prec,ntn,gr,se)) =
  (prec,ntn,
   subst_notation_grammar subst gr,
   option_app (subst_printing_rule subst) se)

let (inSyntaxExtension, outSyntaxExtension) =
  declare_object {(default_object "SYNTAX-EXTENSION") with
       open_function = (fun i o -> if i=1 then cache_syntax_extension o);
       cache_function = cache_syntax_extension;
       subst_function = subst_syntax_extension;
       classify_function = (fun (_,o) -> Substitute o);
       export_function = (fun x -> Some x)}

let interp_modifiers a n =
  let onlyparsing = ref false in
  let rec interp assoc level etyps = function
    | [] ->
	let n = match level with None -> 1 | Some n -> n in
	(assoc,n,etyps,!onlyparsing)
    | SetEntryType (s,typ) :: l ->
	let id = id_of_string s in
	if List.mem_assoc id etyps then
	  error (s^" is already assigned to an entry or constr level")
	else interp assoc level ((id,typ)::etyps) l
    | SetItemLevel ([],n) :: l ->
	interp assoc level etyps l
    | SetItemLevel (s::idl,n) :: l ->
	let id = id_of_string s in
	if List.mem_assoc id etyps then
	  error (s^" is already assigned to an entry or constr level")
	else
	  let typ = ETConstr (n,()) in
	  interp assoc level ((id,typ)::etyps) (SetItemLevel (idl,n)::l)
    | SetLevel n :: l ->
	if level <> None then error "A level is mentioned more than twice"
	else interp assoc (Some n) etyps l
    | SetAssoc a :: l ->
	if assoc <> None then error "already an associativity"
	else interp (Some a) level etyps l
    | SetOnlyParsing :: l ->
	onlyparsing := true;
	interp assoc level etyps l
  in interp a n []

(* Infix defaults to LEFTA (cf doc) *)
let interp_infix_modifiers a n l =
  let (assoc,n,t,b) = interp_modifiers a n l in
  if t <> [] then
    error "explicit entry level or type unexpected in infix notation";
  let assoc = match assoc with None -> Some Gramext.LeftA | a -> a in
  (assoc,n,b)

(* Notation defaults to NONA *)
let interp_notation_modifiers modl =
  let (assoc,n,t,b) = interp_modifiers None None modl in
  let assoc = match assoc with None -> Some Gramext.NonA | a -> a in
  (assoc,n,t,b)

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
    with Not_found -> ETConstr typ
  in (x,typ)

let border = function
  | (_,ETConstr(_,BorderProd (_,a))) :: _ -> a
  | _ -> None

let recompute_assoc typs =
  match border typs, border (List.rev typs) with
    | Some Gramext.LeftA, Some Gramext.RightA -> assert false
    | Some Gramext.LeftA, _ -> Some Gramext.LeftA
    | _, Some Gramext.RightA -> Some Gramext.RightA
    | _ -> None

let add_syntax_extension df modifiers =
  let (assoc,n,etyps,onlyparse) = interp_notation_modifiers modifiers in
  let (typs,symbs) =
    find_symbols
      (n,BorderProd(true,assoc)) (10,InternalProd) (n,BorderProd(false,assoc))
      [] (split df) in
  let typs = List.map (set_entry_type etyps) typs in
  let assoc = recompute_assoc typs in
  let (prec,notation) = make_symbolic n symbs typs in
  let gram_rule = make_grammar_rule n assoc typs symbs notation in
  let pp_rule = if onlyparse then None else Some (make_pp_rule typs symbs) in
  Lib.add_anonymous_leaf (inSyntaxExtension(prec,notation,gram_rule,pp_rule))

(**********************************************************************)
(* Distfix, Infix, Notations *)

(* A notation comes with a grammar rule, a pretty-printing rule, an
   identifiying pattern called notation and an associated scope *)
let load_notation _ (_,(_,prec,ntn,scope,pat,onlyparse,_)) =
  Symbols.declare_scope scope

let open_notation i (_,(oldse,prec,ntn,scope,pat,onlyparse,df)) =
  if i=1 then begin
    let b = Symbols.exists_notation_in_scope scope prec ntn pat in
    (* Declare the old printer rule and its interpretation *)
    if not b & oldse <> None then
      Esyntax.add_ppobject {sc_univ="constr";sc_entries=out_some oldse};
    (* Declare the interpretation *)
    if not b then
      Symbols.declare_notation_interpretation ntn scope pat prec df;
    if not b & not onlyparse then
      Symbols.declare_uninterpretation (NotationRule (scope,ntn)) pat
  end

let cache_notation o =
  load_notation 1 o;
  open_notation 1 o

let subst_notation (_,subst,(oldse,prec,ntn,scope,(metas,pat),b,df)) =
  (option_app
    (list_smartmap (Extend.subst_syntax_entry Ast.subst_astpat subst)) oldse,
   prec,ntn,
   scope,
   (metas,subst_aconstr subst pat), b, df)

let (inNotation, outNotation) =
  declare_object {(default_object "NOTATION") with
       open_function = open_notation;
       cache_function = cache_notation;
       subst_function = subst_notation;
       load_function = load_notation;
       classify_function = (fun (_,o) -> Substitute o);
       export_function = (fun x -> Some x)}

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
  let rule_name = ntn^"_"^scope^"_notation" in
  make_syntax_rule n rule_name symbols typs ast ntn scope

let add_notation_in_scope df c (assoc,n,etyps,onlyparse) sc toks =
  let scope = match sc with None -> Symbols.default_scope | Some sc -> sc in
  let (typs,symbols) =
    find_symbols
      (n,BorderProd(true,assoc)) (10,InternalProd) (n,BorderProd(false,assoc))
      [] toks in
  let vars = List.map fst typs in
  (* To globalize... *)
  let a = interp_aconstr vars c in
  let typs = List.map (set_entry_type etyps) typs in
  let assoc = recompute_assoc typs in
  (* Declare the parsing and printing rules if not already done *)
  let (prec,notation) = make_symbolic n symbols typs in
  let gram_rule = make_grammar_rule n assoc typs symbols notation in
  let pp_rule = if onlyparse then None else Some (make_pp_rule typs symbols) in
  Lib.add_anonymous_leaf (inSyntaxExtension(prec,notation,gram_rule,pp_rule));
  let old_pp_rule =
    if onlyparse then None
    else 
      let r = 
	interp_rawconstr_gen false Evd.empty (Global.env()) [] false (vars,[]) c in
      Some (make_old_pp_rule n symbols typs r notation scope vars) in
  (* Declare the interpretation *)
  let vars = List.map (fun id -> id,[] (* insert the right scope *)) vars in
  Lib.add_anonymous_leaf
    (inNotation(old_pp_rule,prec,notation,scope,a,onlyparse,df))

let add_notation df a modifiers sc =
  let toks = split df in
  match toks with 
    | [String x] when quote(strip x) = x & modifiers = [] ->
        (* Means a Syntactic Definition *)
        let ident = id_of_string (strip x) in
	let c = snd (interp_aconstr [] a) in
        Syntax_def.declare_syntactic_definition ident c
    | _ ->
       add_notation_in_scope df a (interp_notation_modifiers modifiers) sc toks

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
      let (vars,l) = rename x vars n l in (vars,(quote y)::l)
  | WhiteSpace _::l ->
      rename x vars n l

let add_distfix assoc n df r sc =
  (* "x" cannot clash since r is globalized (included section vars) *)
  let (vars,l) = rename "x" [] 1 (split df) in
  let df = String.concat " " l in
  let a = mkAppC (mkRefC r, vars) in
  let assoc = match assoc with None -> Gramext.LeftA | Some a -> a in
  add_notation_in_scope df a (Some assoc,n,[],false) sc (split df)

let add_infix assoc n inf pr onlyparse sc =
(*  let pr = Astterm.globalize_qualid pr in*)
  (* check the precedence *)
  if n<1 or n>10 then
    errorlabstrm "Metasyntax.infix_grammar_entry"
      (str"Precedence must be between 1 and 10.");
  (*
  if (assoc<>None) & (n<6 or n>9) then
    errorlabstrm "Vernacentries.infix_grammar_entry"
      (str"Associativity Precedence must be 6,7,8 or 9.");
  *)
  let metas = [inject_var "x"; inject_var "y"] in
  let a = mkAppC (mkRefC pr,metas) in
  let df = "x "^(quote inf)^" y" in
  add_notation_in_scope df a (assoc,n,[],onlyparse) sc (split df)

(* Delimiters *)
let load_delimiters _ (_,(scope,dlm)) =
  Symbols.declare_scope scope

let open_delimiters i (_,(scope,dlm)) =
  if i=1 then Symbols.declare_delimiters scope dlm

let cache_delimiters o =
  load_delimiters 1 o;
  open_delimiters 1 o

let (inDelim,outDelim) = 
  declare_object {(default_object "DELIMITERS") with
      cache_function = cache_delimiters;
      open_function = open_delimiters;
      load_function = load_delimiters;
      export_function = (fun x -> Some x) }

let add_delimiters scope key =
  Lib.add_anonymous_leaf (inDelim(scope,key))
