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
  if not !Options.v7_only then
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
  (s.[0] = ',' or s.[0] = ';' or s.[0] = ':')

let is_operator s =
  let l = String.length s in l <> 0 &
  (s.[0] = '+' or s.[0] = '*' or s.[0] = '=' or
   s.[0] = '-' or s.[0] = '/' or s.[0] = '<' or s.[0] = '>' or
   s.[0] = '@' or s.[0] = '\\' or s.[0] = '&' or s.[0] = '~')

type previous_prod_status = NoBreak | CanBreak

let is_non_terminal = function
  | NonTerminal _ -> true
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
	else
	  if ws = CanBreak or is_ident_tail s.[String.length s - 1] then
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

    | [] -> []

  in make NoBreak symbols

let string_of_prec (n,p) =
  (string_of_int n)^(match p with E -> "E" | L -> "L" | _ -> "")

let string_of_symbol = function
  | NonTerminal _ -> ["_"]
  | Terminal s -> [s]
  | Break _ -> []

let assoc_of_type n (_,typ) = level_rule (precedence_of_entry_type n typ)

let string_of_assoc = function
  | Some(Gramext.RightA) -> "RIGHTA"
  | Some(Gramext.LeftA) | None -> "LEFTA"
  | Some(Gramext.NonA) -> "NONA"

let make_anon_notation symbols =
  String.concat " " (List.flatten (List.map string_of_symbol symbols))

let make_symbolic n symbols etyps =
  ((n,List.map (assoc_of_type n) etyps), make_anon_notation symbols)

let rec define_keywords = function
    NonTerm(_,Some(_,(ETConstr _|ETOther("constr","binder_constr")))) as n1 ::
    Term("IDENT",k) :: l when not !Options.v7 ->
      prerr_endline ("Defining '"^k^"' as keyword");
      Lexer.add_token("",k);
      n1 :: Term("",k) :: define_keywords l
  | n :: l -> n :: define_keywords l
  | [] -> []

let make_production etyps symbols =
  let prod =
    List.fold_right
      (fun t l -> match t with
        | NonTerminal m ->
	    let typ = List.assoc m etyps in
	    NonTerm (ProdPrimitive typ, Some (m,typ)) :: l
        | Terminal s ->
	    Term (Extend.terminal s) :: l
        | Break _ ->
	    l)
      symbols [] in
  define_keywords prod

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

let rec analyse_tokens = function
  | []    -> [], []
  | String x :: sl when Lexer.is_normal_token x ->
      Lexer.check_ident x;
      let id = Names.id_of_string x in
      let (vars,l) = analyse_tokens sl in
      if List.mem id vars then
	error ("Variable "^x^" occurs more than once");
      (id::vars, NonTerminal id :: l)
  | String s :: sl ->
      Lexer.check_special_token s;
      let (vars,l) = analyse_tokens sl in (vars, Terminal (strip s) :: l)
  | WhiteSpace n :: sl ->
      let (vars,l) = analyse_tokens sl in (vars, Break n :: l)

let rec find_symbols c_current c_next c_last = function
  | [] -> []
  | NonTerminal id :: sl ->
      let prec = if sl <> [] then c_current else c_last in
      (id, prec) :: (find_symbols c_next c_next c_last sl)
  | Terminal s :: sl -> find_symbols c_next c_next c_last sl
  | Break n :: sl -> find_symbols c_current c_next c_last sl

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

let make_pp_rule symbols typs n =
  [UnpBox (PpHOVB 0, make_hunks symbols typs n)]


(**************************************************************************)
(* Syntax extenstion: common parsing/printing rules and no interpretation *)

let cache_syntax_extension (_,(_,prec,ntn,gr,se,translate)) =
  try 
    let oldprec = Symbols.level_of_notation ntn in
    if translate (* In case the ntn was only for the printer - V8Notation *)
    then raise Not_found else 
    if oldprec <> prec then
      if !Options.v7 then begin
	Options.if_verbose
	  warning ("Notation "^ntn^" was already assigned a different level");
	raise Not_found
      end else
	error ("Notation "^ntn^" is already assigned a different level")
    else
    (* The notation is already declared; no need to redeclare it *)
      ()
  with Not_found ->
    (* Reserve the notation level *)
    Symbols.declare_notation_level ntn prec;
    (* Declare the parsing rule *)
    option_iter (fun gr -> Egrammar.extend_grammar (Egrammar.Notation gr)) gr;
    (* Declare the printing rule *)
    Symbols.declare_notation_printing_rule ntn (se,fst prec)

let subst_notation_grammar subst x = x

let subst_printing_rule subst x = x

let subst_syntax_extension (_,subst,(local,prec,ntn,gr,se,t)) =
  (local,prec,ntn,
   option_app (subst_notation_grammar subst) gr,
   subst_printing_rule subst se, t)

let classify_syntax_definition (_,(local,_,_,_,_,_ as o)) =
  if local then Dispose else Substitute o

let export_syntax_definition (local,_,_,_,_,_ as o) =
  if local then None else Some o

let (inSyntaxExtension, outSyntaxExtension) =
  declare_object {(default_object "SYNTAX-EXTENSION") with
       open_function = (fun i o -> if i=1 then cache_syntax_extension o);
       cache_function = cache_syntax_extension;
       subst_function = subst_syntax_extension;
       classify_function = classify_syntax_definition;
       export_function = export_syntax_definition}

let interp_modifiers a n =
  let onlyparsing = ref false in
  let rec interp assoc level etyps = function
    | [] ->
	(assoc,level,etyps,!onlyparsing)
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
  let (assoc,level,t,b) = interp_modifiers a n l in
  if t <> [] then
    error "explicit entry level or type unexpected in infix notation";
  let assoc = match assoc with None -> Some Gramext.LeftA | a -> a in
  let n = match level with None -> 1 | Some n -> n in
  (assoc,n,b)

(* Notation defaults to NONA *)
let interp_notation_modifiers modl =
  let (assoc,n,t,b) = interp_modifiers None None modl in
  let assoc = match assoc with None -> Some Gramext.NonA | a -> a in
  let n = match n with None -> 1 | Some n -> n in
  (assoc,n,t,b)

(* 2nd list of types has priority *)
let rec merge_entry_types etyps' = function
  | [] -> etyps'
  | (x,_ as e)::etyps ->
      e :: merge_entry_types (List.remove_assoc x etyps') etyps

let set_entry_type etyps (x,typ) =
  let typ = try 
    match List.assoc x etyps, typ with
      | _, (_,BorderProd (true,_)) ->
	  error "The level of the leftmost non-terminal cannot be changed"
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

let add_syntax_extension_v8only local mv8 =
  let (df,modifiers) = out_some mv8 in
  let (assoc,n,etyps,onlyparse) = interp_notation_modifiers modifiers in
  let inner = if !Options.v7 then (NumLevel 10,InternalProd) else
    (NumLevel 200,InternalProd) in
  let (_,symbs) = analyse_tokens (split df) in
  let typs =
    find_symbols
      (NumLevel n,BorderProd(true,assoc)) inner
      (NumLevel n,BorderProd(false,assoc)) symbs in
  let typs = List.map (set_entry_type etyps) typs in
  let assoc = recompute_assoc typs in
  let (prec,notation) = make_symbolic n symbs typs in
  let pp_rule = make_pp_rule typs symbs n in
  Lib.add_anonymous_leaf
    (inSyntaxExtension(local,prec,notation,None,pp_rule,Options.do_translate()))

let add_syntax_extension local dfmod mv8 = match dfmod with
  | None -> add_syntax_extension_v8only local mv8
  | Some (df,modifiers) ->
  let (assoc,n,etyps,onlyparse) = interp_notation_modifiers modifiers in
  let inner = if !Options.v7 then (NumLevel 10,InternalProd) else
    (NumLevel 200,InternalProd) in
  let (_,symbs) = analyse_tokens (split df) in
  let typs =
    find_symbols
      (NumLevel n,BorderProd(true,assoc)) inner
      (NumLevel n,BorderProd(false,assoc)) symbs in
  let typs = List.map (set_entry_type etyps) typs in
  let assoc = recompute_assoc typs in
  let (prec,notation) = make_symbolic n symbs typs in
  let (ppprec,ppn,pptyps,ppsymbols) =
    let omodv8 = option_app (fun (s8,ml8) ->
      let toks8 = split s8 in 
      let im8 = interp_notation_modifiers ml8 in
      (toks8,im8)) mv8 in
    match omodv8 with
        Some(toks8,(a8,n8,typs8,_)) when Options.do_translate() ->
          let (_,symbols) = analyse_tokens toks8 in
          let typs =
            find_symbols
              (NumLevel n8,BorderProd(true,a8)) (NumLevel 200,InternalProd)
              (NumLevel n8,BorderProd(false,a8))
              symbols in
          let typs = List.map (set_entry_type typs8) typs in
          let (prec,notation) = make_symbolic n8 symbols typs in
          (prec, n8, typs, symbols)
    | _ -> (prec, n, typs, symbs) in
  let gram_rule = make_grammar_rule n assoc typs symbs notation in
  let pp_rule = make_pp_rule pptyps ppsymbols ppn in
  Lib.add_anonymous_leaf
    (inSyntaxExtension(local,ppprec,notation,Some gram_rule,pp_rule,Options.do_translate()))

(**********************************************************************)
(* Distfix, Infix, Notations *)

(* A notation comes with a grammar rule, a pretty-printing rule, an
   identifiying pattern called notation and an associated scope *)
let load_notation _ (_,(_,_,ntn,scope,pat,onlyparse,_,_)) =
  Symbols.declare_scope scope

let open_notation i (_,(_,oldse,ntn,scope,pat,onlyparse,onlypp,df)) =
  if i=1 then begin
    let b = Symbols.exists_notation_in_scope scope ntn pat in
    (* Declare the old printer rule and its interpretation *)
    if not b & oldse <> None then
      Esyntax.add_ppobject {sc_univ="constr";sc_entries=out_some oldse};
    (* Declare the interpretation *)
    if not b & not onlypp then
      Symbols.declare_notation_interpretation ntn scope pat df;
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
  let rule_name = ntn^"_"^scope^"_notation" in
  make_syntax_rule n rule_name symbols typs ast ntn scope

let add_notation_in_scope local df c (assoc,n,etyps,onlyparse) omodv8 sc toks =
  let onlyparse = onlyparse or !Options.v7_only in
  let scope = match sc with None -> Symbols.default_scope | Some sc -> sc in
  let inner =
    if !Options.v7 then (NumLevel 10,InternalProd)
    else (NumLevel 200,InternalProd) in
  let (vars,symbols) = analyse_tokens toks in
  let typs =
    find_symbols
      (NumLevel n,BorderProd(true,assoc)) inner 
      (NumLevel n,BorderProd(false,assoc)) symbols in
  (* To globalize... *)
  let a = interp_aconstr vars c in
  let typs = List.map (set_entry_type etyps) typs in
  let assoc = recompute_assoc typs in
  (* Declare the parsing and printing rules if not already done *)
  let (prec,notation) = make_symbolic n symbols typs in
  let (ppprec,ppn,pptyps,ppsymbols) =
    match omodv8 with
        Some(toks8,(a8,n8,typs8,_)) when Options.do_translate() ->
          let (_,symbols) = analyse_tokens toks8 in
          let typs =
            find_symbols
              (NumLevel n8,BorderProd(true,a8)) (NumLevel 200,InternalProd)
              (NumLevel n8,BorderProd(false,a8))
              symbols in
          let typs = List.map (set_entry_type typs8) typs in
          let (prec,notation) = make_symbolic n8 symbols typs in
          (prec, n8, typs, symbols)
    | _ -> (prec, n, typs, symbols) in
  let gram_rule = make_grammar_rule n assoc typs symbols notation in
  let pp_rule = make_pp_rule pptyps ppsymbols ppn in
  Lib.add_anonymous_leaf
    (inSyntaxExtension(local,ppprec,notation,Some gram_rule,pp_rule,Options.do_translate()));
  let old_pp_rule =
    if onlyparse then None
    else
      let r = interp_rawconstr_gen
          false Evd.empty (Global.env()) [] false (vars,[]) c in
      Some (make_old_pp_rule ppn ppsymbols pptyps r notation scope vars) in
  (* Declare the interpretation *)
  let vars = List.map (fun id -> id,[] (* insert the right scope *)) vars in
  Lib.add_anonymous_leaf
    (inNotation(local,old_pp_rule,notation,scope,a,onlyparse,false,df))

let add_notation_interpretation_core local vars symbs df (a,r) sc onlyparse 
  onlypp =
  let scope = match sc with None -> Symbols.default_scope | Some sc -> sc in
  let notation = make_anon_notation symbs in
  let prec = 
    try Symbols.level_of_notation notation
    with Not_found ->
      error "Parsing rule for this notation has to be previously declared" in
  let old_pp_rule =
    let typs = List.map2 
      (fun id n -> id,ETConstr (NumLevel n,InternalProd)) vars (snd prec) in
    Some (make_old_pp_rule (fst prec) symbs typs r notation scope vars) in
  Lib.add_anonymous_leaf
    (inNotation(local,old_pp_rule,notation,scope,a,onlyparse,onlypp,df))

let check_occur l id =
  if not (List.mem (Name id) l) then error ((string_of_id id)^"is unbound")

let add_notation_interpretation df (c,l) sc =
  let (vars,symbs) = analyse_tokens (split df) in
  List.iter (check_occur l) vars;
  let a_for_old =
    let c = match c with AVar id -> RVar (dummy_loc,id)
      | ARef c -> RRef (dummy_loc,c)
      | _ -> anomaly "add_notation_interpretation" in
    RApp (dummy_loc, c,
      List.map (function
	| Name id when List.mem id vars -> RVar (dummy_loc,id)
	| _ -> RHole (dummy_loc,QuestionMark)) l) in
  let a = AApp (c,List.map (function 
    | Name id when List.mem id vars -> AVar id
    | _ -> AHole QuestionMark) l) in
  let la = List.map (fun id -> id,(None,[])) vars in
  let onlyparse = false in
  let local = false in
  add_notation_interpretation_core local vars symbs df ((la,a),a_for_old) sc
    onlyparse false

let add_notation_v8only local c (df,modifiers) sc =
  let add_notation_in_scope local df c (assoc,n,etyps,onlyparse) sc toks =
    let onlyparse = false in
    let scope = match sc with None -> Symbols.default_scope | Some sc -> sc in
    let inner = (NumLevel 200,InternalProd) in
    let (vars,symbols) = analyse_tokens toks in
    let typs =
      find_symbols
	(NumLevel n,BorderProd(true,assoc)) inner 
	(NumLevel n,BorderProd(false,assoc)) symbols in
    (* To globalize... *)
    let a = interp_aconstr vars c in
    let typs = List.map (set_entry_type etyps) typs in
    let assoc = recompute_assoc typs in
    (* Declare the parsing and printing rules if not already done *)
    let (prec,notation) = make_symbolic n symbols typs in
    let pp_rule = make_pp_rule typs symbols n in
    Lib.add_anonymous_leaf
      (inSyntaxExtension(local,prec,notation,None,pp_rule,Options.do_translate()));
    (* Declare the interpretation *)
    let vars = List.map (fun id -> id,[] (* insert the right scope *)) vars in
    Lib.add_anonymous_leaf
      (inNotation(local,None,notation,scope,a,onlyparse,true,df))
  in
  let toks = split df in
  match toks with 
    | [String x] when (modifiers = [] or modifiers = [SetOnlyParsing]) ->
	(* This is a ident to be declared as a rule *)
        add_notation_in_scope local df c (None,0,[],modifiers=[SetOnlyParsing])
          sc toks
    | _ ->
	let (assoc,lev,typs,onlyparse) = interp_modifiers None None modifiers
	in
	match lev with
	  | None->
	      if modifiers <> [] & modifiers <> [SetOnlyParsing] then
		error "Parsing rule for this notation includes no level"
	      else
	        (* Declare only interpretation *)
		let (vars,symbs) = analyse_tokens toks in
		let onlyparse = modifiers = [SetOnlyParsing] in
		let a = interp_aconstr vars c in
		let a_for_old = interp_rawconstr_gen
		  false Evd.empty (Global.env()) [] false (vars,[]) c in
		add_notation_interpretation_core local vars symbs df
		  (a,a_for_old) sc onlyparse true
	  | Some n ->
	    (* Declare both syntax and interpretation *)
	    let assoc = match assoc with None -> Some Gramext.NonA | a -> a in
	    let mods = (assoc,n,typs,onlyparse)	in
            add_notation_in_scope local df c mods sc toks

let add_notation local c dfmod mv8 sc =
  match dfmod with
  | None -> add_notation_v8only local c (out_some mv8) sc
  | Some (df,modifiers) ->
  let toks = split df in
  match toks with 
    | [String x] when quote(strip x) = x
	(* This is an ident that can be qualified: a syntactic definition *)
	& (modifiers = [] or modifiers = [SetOnlyParsing]) ->
        (* Means a Syntactic Definition *)
        let ident = id_of_string (strip x) in
	let c = snd (interp_aconstr [] c) in
	let onlyparse = !Options.v7_only or modifiers = [SetOnlyParsing] in
        Syntax_def.declare_syntactic_definition local ident onlyparse c
    | [String x] when (modifiers = [] or modifiers = [SetOnlyParsing]) ->
	(* This is a ident to be declared as a rule *)
        add_notation_in_scope local df c (None,0,[],modifiers=[SetOnlyParsing])
          (option_app (fun (s8,ml8) ->
	    let toks8 = split s8 in 
	    let im8 = interp_notation_modifiers ml8 in
	    (toks8,im8)) mv8)
        sc toks
    | _ ->
	let (assoc,lev,typs,onlyparse) = interp_modifiers None None modifiers
	in
	match lev with
	  | None->
	      if modifiers <> [] & modifiers <> [SetOnlyParsing] then
		error "Parsing rule for this notation includes no level"
	      else
	        (* Declare only interpretation *)
		let (vars,symbs) = analyse_tokens toks in
		let onlyparse = modifiers = [SetOnlyParsing] in
		let a = interp_aconstr vars c in
		let a_for_old = interp_rawconstr_gen
		  false Evd.empty (Global.env()) [] false (vars,[]) c in
		add_notation_interpretation_core local vars symbs df
		  (a,a_for_old) sc onlyparse false
	  | Some n ->
	    (* Declare both syntax and interpretation *)
	    let assoc = match assoc with None -> Some Gramext.NonA | a -> a in
	    let mods = (assoc,n,typs,onlyparse)	in
            add_notation_in_scope local df c mods
              (option_app (fun (s8,ml8) ->
		let toks8 = split s8 in 
		let im8 = interp_notation_modifiers ml8 in
		(toks8,im8)) mv8)
              sc toks

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

let add_distfix local assoc n df r sc =
  (* "x" cannot clash since r is globalized (included section vars) *)
  let (vars,l) = rename "x" [] 1 (split df) in
  let df = String.concat " " l in
  let a = mkAppC (mkRefC r, vars) in
  let assoc = match assoc with None -> Gramext.LeftA | Some a -> a in
  add_notation_in_scope local df a (Some assoc,n,[],false) None sc (split df)

let add_infix local assoc n inf pr onlyparse mv8 sc =
(*  let pr = Astterm.globalize_qualid pr in*)
  (* check the precedence *)
  if !Options.v7 & (n<1 or n>10) then
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
  let mv8 = match mv8 with
      None -> Some(split df,(assoc,n*10,[],false))
    | Some(a8,n8,s8) ->
        Some(split ("x "^quote s8^" y"),(a8,n8,[],false)) in
  add_notation_in_scope local df a (assoc,n,[],onlyparse) mv8 sc (split df)

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
