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

let _ = define_ast_quotation true "constr" constr_parser_with_glob

let add_name r = function
  | Anonymous -> ()
  | Name id -> r := id :: !r

let make_aconstr vars a =
  let bound_vars = ref [] in
  let bound_binders = ref [] in
  let rec aux = function
  | RVar (_,id) ->
      if List.mem id vars then bound_vars := id::!bound_vars;
      AVar id
  | RApp (_,g,args) -> AApp (aux g, List.map aux args)
  | RLambda (_,na,ty,c) -> add_name bound_binders na; ALambda (na,aux ty,aux c)
  | RProd (_,na,ty,c) -> add_name bound_binders na; AProd (na,aux ty,aux c)
  | RLetIn (_,na,b,c) -> add_name bound_binders na; ALetIn (na,aux b,aux c)
  | ROrderedCase (_,b,tyopt,tm,bv) ->
      AOldCase (b,option_app aux tyopt,aux tm, Array.map aux bv)
  | RCast (_,c,t) -> ACast (aux c,aux t)
  | RSort (_,s) -> ASort s
  | RHole (_,w) -> AHole w
  | RRef (_,r) -> ARef r
  | RMeta (_,n) -> AMeta n
  | RDynamic _ | RRec _ | RCases _ | REvar _ ->
      error "Fixpoints, cofixpoints, existential variables and pattern-matching  not \
allowed in abbreviatable expressions"
  in
  let a = aux a in
  let find_type x =
    if List.mem x !bound_binders then (x,ETIdent) else
    if List.mem x !bound_vars then (x,ETConstr) else
      error ((string_of_id x)^" is unbound in the right-hand-side") in
  let typs = List.map find_type vars in
  (a, typs)

let _ = set_ast_to_rawconstr
  (fun etyps a ->
    let vl = List.map fst etyps in 
    let r =
      for_grammar (interp_rawconstr_gen Evd.empty (Global.env()) [] false vl) a
    in
    let a, typs = make_aconstr vl r in
(*
    List.iter2
      (fun (x,typ) (x',typ') ->
	assert (x=x');
	if typ = ETConstr & typ' = ETIdent then
	  error "cannot use a constr parser to parse an ident") etyps typs;
*)
    a)

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
let gram_define_entry (u,_ as univ) (nt,et,assoc,rl) =
  if u = "tactic" or u = "vernac" then error "tactic and vernac not supported";
  create_entry_if_new univ nt (entry_type_of_constr_entry_type et);
  (nt, et, assoc, rl)

let add_grammar_obj univ l =
  let u = create_univ_if_new univ in
  let entryl = List.map (gram_define_entry u) l in
  let g = interp_grammar_command univ get_entry_type entryl in
  Lib.add_anonymous_leaf (inGrammar (Egrammar.Grammar g))

let add_tactic_grammar g = 
  Lib.add_anonymous_leaf (inGrammar (Egrammar.TacticGrammar g))

(* printing grammar entries *)
let print_grammar univ entry =
  let u = get_univ univ in
  let te = get_entry u entry in
  Gram.Entry.print (object_of_typed_entry te)

(* Infix, distfix, notations *)

let split str =
  let rec loop beg i =
    if i < String.length str then
      if str.[i] == ' ' then
        if beg == i then 
	  loop (succ beg) (succ i)
        else 
	  String.sub str beg (i - beg) :: loop (succ i) (succ i)
      else 
	loop beg (succ i)
    else if beg == i then 
      []
    else
      [String.sub str beg (i - beg)]
  in
  loop 0 0

(* Build the syntax and grammar rules *)

type symbol =
  | Terminal of string
  | NonTerminal of (int * parenRelation) * identifier

let prec_assoc = function
  | Some(Gramext.RightA) -> (L,E)
  | Some(Gramext.LeftA) -> (E,L)
  | Some(Gramext.NonA) -> (L,L)
  | None -> (L,L)   (* NONA by default *)

let constr_tab =
  [| "constr0"; "constr1"; "constr2"; "constr3"; "lassoc_constr4";
     "constr5"; "constr6"; "constr7"; "constr"; "constr9"; "lconstr";
     "pattern" |]

let level_rule (n,p) = if p = E then n else max (n-1) 0

let constr_rule np = constr_tab.(level_rule np)

let nonterm_meta nt var x =
  match x with
  | ETIdent -> NonTerm(ProdPrimitive ("constr","ident"), Some (var,x))
  | ETConstr -> NonTerm(ProdPrimitive ("constr",nt), Some (var,x))
  | ETReference -> NonTerm(ProdPrimitive ("constr","global"), Some (var,x))

(* For old ast printer *)
let meta_pattern m = Pmeta(m,Tany)

(* For old ast printer *)
let make_hunks_ast symbols =
  List.fold_right
    (fun it l -> match it with
      | NonTerminal ((_,lp),m) -> PH (meta_pattern (string_of_id m), None, lp) :: l
      | Terminal s ->
	  let n,s =
	    if is_letter (s.[String.length s -1]) or is_letter (s.[0])
	    then 1,s^" " else 0,s
	  in
	  UNP_BRK (n, 1) :: RO s :: l)
    symbols []

open Symbols

type white_status = NextMaybeLetter | NextIsNotLetter | AddBrk of int

let make_hunks symbols =
  let (_,l) =
  List.fold_right
    (fun it (ws,l) -> match it with
      | NonTerminal (prec,m) ->
	  let u = UnpMetaVar (m,prec) in
	  let l' = match ws with
	    | AddBrk n -> UnpCut (PpBrk(n,1)) :: u :: l
	    | _ -> u :: l in
	  (NextMaybeLetter, l')
      | Terminal s ->
	  let n = if is_letter (s.[0]) then 1 else 0 in
	  let s = 
	    if (ws = NextMaybeLetter or ws = AddBrk 1)
	      & is_letter (s.[String.length s -1])
	    then s^" "
	    else s
	  in
	  (AddBrk n, UnpTerminal s :: l))
    symbols (NextMaybeLetter,[])
  in l

let string_of_prec (n,p) =
  (string_of_int n)^(match p with E -> "E" | L -> "L" | _ -> "")

let string_of_symbol = function
  | NonTerminal (lp,_) -> "_"
  | Terminal s -> s

let assoc_of_symbol s l = match s with
  | NonTerminal (lp,_) -> level_rule lp :: l
  | Terminal _ -> l

let string_of_assoc = function
  | Some(Gramext.RightA) -> "RIGHTA"
  | Some(Gramext.LeftA) | None -> "LEFTA"
  | Some(Gramext.NonA) -> "NONA"

let make_symbolic assoc n symbols =
  (n, List.fold_right assoc_of_symbol symbols []),
  (String.concat " " (List.map string_of_symbol symbols))

let make_production typs =
  List.map (function
    | NonTerminal (lp,m) -> nonterm_meta (constr_rule lp) m (List.assoc m typs)
    | Terminal s -> Term (Extend.terminal s))

(*
let create_meta n = "$e"^(string_of_int n)
*)

let strip s =
  let n = String.length s in
  if n > 2 & s.[0] = '\'' & s.[n-1] = '\'' then String.sub s 1 (n-2) else s

let is_symbol s = not (is_letter s.[0])

let rec find_symbols c_first c_next c_last vars varprecl = function
  | []    -> (vars, [])
  | x::sl when is_letter x.[0] ->
      let id = Names.id_of_string x in
      if List.mem id vars then error ("Variable "^x^" occurs more than once");
      let prec =
        try (List.assoc x varprecl,E)
        with Not_found ->
          if List.exists is_symbol sl then c_first else c_last in
      let (vars,l) =
        find_symbols c_next c_next c_last vars varprecl sl in
      (id::vars, NonTerminal (prec,id) :: l)
(*
  | "_"::sl ->
      warning "Found '_'";
      let prec = if List.exists is_symbols sl then c_first else c_last in
      let (vars,l) =
        find_symbols c_next c_next c_last vars (new_var+1) varprecl sl in
      let meta = create_meta new_var in
      (vars, NonTerminal (prec, meta) :: l)
*)
  | s :: sl ->
      let (vars,l) = find_symbols c_next c_next c_last vars varprecl sl in
      (vars, Terminal (strip s) :: l)

let make_grammar_rule n typs symbols ntn =
  let prod = make_production typs symbols in
  ((if n=8 then "constr8" else constr_rule (n,E)),ntn,prod)

(* For old ast printer *)
let metas_of sl =
  List.fold_right
    (fun it metatl -> match it with
      | NonTerminal (_,m) -> m::metatl
      | _ -> metatl)
    sl []

(* For old ast printer *)
let make_pattern symbols ast =
  let env = List.map (fun m -> (string_of_id m,ETast)) (metas_of symbols) in
  fst (to_pat env ast)

(* For old ast printer *)
let make_syntax_rule n name symbols ast ntn sc =
  [{syn_id = name;
    syn_prec = n;
    syn_astpat = make_pattern symbols ast;
    syn_hunks = [UNP_SYMBOLIC(sc,ntn,UNP_BOX (PpHOVB 1, make_hunks_ast symbols))]}]

let make_pp_rule symbols =
  [UnpBox (PpHOVB 1, make_hunks symbols)]


(**************************************************************************)
(* Syntax extenstion: common parsing/printing rules and no interpretation *)

let cache_syntax_extension (_,(prec,ntn,gr,se)) =
  if not (Symbols.exists_notation prec ntn) then begin
    Egrammar.extend_grammar (Egrammar.Notation gr);
    Symbols.declare_printing_rule ntn (se,fst prec)
  end

let subst_notation_grammar subst x = x

let subst_printing_rule subst x = x

let subst_syntax_extension (_,subst,(prec,ntn,gr,se)) =
  (prec,ntn,subst_notation_grammar subst gr,subst_printing_rule subst se)

let (inSyntaxExtension, outSyntaxExtension) =
  declare_object {(default_object "SYNTAX-EXTENSION") with
       open_function = (fun i o -> if i=1 then cache_syntax_extension o);
       cache_function = cache_syntax_extension;
       subst_function = subst_syntax_extension;
       classify_function = (fun (_,o) -> Substitute o);
       export_function = (fun x -> Some x)}

let interp_syntax_modifiers =
  let rec interp assoc precl level etyps = function
    | [] ->
	let n = match level with None -> 1 | Some n -> n in
	(assoc,precl,n,etyps)
    | SetItemLevel (id,n) :: l ->
	if List.mem_assoc id precl then error (id^"has already a precedence")
	else interp assoc ((id,n)::precl) level etyps l
    | SetLevel n :: l ->
	if level <> None then error "already a level"
	else interp assoc precl (Some n) etyps l
    | SetAssoc a :: l ->
	if assoc <> None then error "already an associativity"
	else interp (Some a) precl level etyps l
    | SetEntryType (s,typ) :: l ->
	let id = id_of_string s in
	if List.mem_assoc id etyps then error (s^"has already an entry type")
	else interp assoc precl level ((id,typ)::etyps) l
  in interp None [] None []

let add_syntax_extension df modifiers =
  let (assoc,varprecl,n,etyps) = interp_syntax_modifiers modifiers in
  let (lp,rp) = prec_assoc assoc in
  let (ids,symbs) = find_symbols (n,lp) (10,E) (n,rp) [] varprecl (split df) in
  let (prec,notation) = make_symbolic assoc n symbs in
  let gram_rule = make_grammar_rule n etyps symbs notation in
  let pp_rule = make_pp_rule symbs in
  Lib.add_anonymous_leaf (inSyntaxExtension(prec,notation,gram_rule,pp_rule))

(**********************************************************************)
(* Distfix, Infix, Notations *)

(* A notation comes with a grammar rule, a pretty-printing rule, an
   identifiying pattern called notation and an associated scope *)
let load_infix _ (_,(gr,_,se,prec,ntn,scope,pat)) =
  Symbols.declare_scope scope

let open_infix i (_,(gr,oldse,se,prec,ntn,scope,pat)) =
  if i=1 then begin
    let b = Symbols.exists_notation_in_scope scope prec ntn pat in
    (* Declare the printer rule and its interpretation *)
    if not b then Esyntax.add_ppobject {sc_univ="constr";sc_entries=oldse};
    (* Declare the grammar and printing rules ... *)
    if not (Symbols.exists_notation prec ntn) then begin
      Egrammar.extend_grammar (Egrammar.Notation gr);
      Symbols.declare_printing_rule ntn (se,fst prec)
    end;
    (* ... and their interpretation *)
    if not b then
      Symbols.declare_notation ntn scope (pat,prec);
  end

let cache_infix o =
  load_infix 1 o;
  open_infix 1 o

let subst_infix (_,subst,(gr,oldse,se,prec,ntn,scope,pat)) =
  (subst_notation_grammar subst gr,
   list_smartmap (Extend.subst_syntax_entry Ast.subst_astpat subst) oldse,
   subst_printing_rule subst se,
   prec,ntn,
   scope,
   subst_aconstr subst pat)

let (inInfix, outInfix) =
  declare_object {(default_object "INFIX") with
       open_function = open_infix;
       cache_function = cache_infix;
       subst_function = subst_infix;
       load_function = load_infix;
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
let make_old_pp_rule n symbols r ntn scope vars =
  let ast = Termast.ast_of_rawconstr r in
  let ast = reify_meta_ast vars ast in
  let rule_name = ntn^"_"^scope^"_notation" in
  make_syntax_rule n rule_name symbols ast ntn scope

let add_notation df ast modifiers sc =
  let (assoc,varprecl,n,_) = interp_syntax_modifiers modifiers in
  let scope = match sc with None -> Symbols.default_scope | Some sc -> sc in
  let (lp,rp) = prec_assoc assoc in
  let (vars,symbols) =
    find_symbols (n,lp) (10,E) (n,rp) [] varprecl (split df) in
  let (prec,notation) = make_symbolic assoc n symbols in
  (* To globalize... *)
  let r = interp_rawconstr_gen Evd.empty (Global.env()) [] false vars ast in
  let a,typs = make_aconstr vars r in
  let typs =
    List.map (fun (x,t) -> 
      (x,if List.mem_assoc (string_of_id x) varprecl then ETConstr else t))
      typs
  in
  let gram_rule = make_grammar_rule n typs symbols notation in
  let pp_rule = make_pp_rule symbols in
  let old_pp_rule = make_old_pp_rule n symbols r notation scope vars in
  Lib.add_anonymous_leaf (inInfix(gram_rule,old_pp_rule,pp_rule,prec,notation,scope,a))

(* TODO add boxes information in the expression *)

let inject_var x = CRef (Ident (dummy_loc, id_of_string x))

(* To protect alphabetic tokens from being seen as variables *)
let quote x = "\'"^x^"\'"

let rec rename x vars n = function
  | [] ->
      (vars,[])
  | "_"::l ->
      let (vars,l) = rename x vars (n+1) l in
      let xn = x^(string_of_int n) in
      ((inject_var xn)::vars,xn::l)
  | y::l ->
      let (vars,l) = rename x vars n l in (vars,(quote y)::l)

let add_distfix assoc n df r sc =
  (* "x" cannot clash since ast is globalized (included section vars) *)
  let (vars,l) = rename "x" [] 1 (split df) in
  let df = String.concat " " l in
  let ast = mkAppC (mkRefC r, vars) in
  let a = match assoc with None -> Gramext.LeftA | Some a -> a in
  add_notation df ast [SetAssoc a;SetLevel n] sc

let add_infix assoc n inf pr sc =
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
  let ast = mkAppC (mkRefC pr,metas) in
  let a = match assoc with None -> Gramext.LeftA | Some a -> a in
  add_notation ("x "^(quote inf)^" y") ast [SetAssoc a;SetLevel n] sc

(* Delimiters *)
let load_delimiters _ (_,(_,_,scope,dlm)) =
  Symbols.declare_scope scope

let open_delimiters i (_,(gram_rule,pat_gram_rule,scope,dlm)) =
  if i=1 then begin
    (* For parsing *)
    Egrammar.extend_grammar (Egrammar.Delimiters (scope,gram_rule,pat_gram_rule));
    (* For printing *)
    Symbols.declare_delimiters scope dlm
  end

let cache_delimiters o =
  load_delimiters 1 o;
  open_delimiters 1 o

let (inDelim,outDelim) = 
  declare_object {(default_object "DELIMITERS") with
      cache_function = cache_delimiters;
      open_function = open_delimiters;
      load_function = load_delimiters;
      export_function = (fun x -> Some x) }

let make_delimiter_rule (l,r) inlevel =
  let e = Nameops.make_ident "e" None in
  let symbols = [Terminal l; NonTerminal ((inlevel,E),e); Terminal r] in
  make_production [e,ETConstr] symbols

let add_delimiters scope (l,r as dlms) =
  if l = "" or r = "" then error "Delimiters cannot be empty";
  let gram_rule = make_delimiter_rule dlms 0 (* constr0 *) in
  let pat_gram_rule = make_delimiter_rule dlms 11 (* "pattern" *) in
  Lib.add_anonymous_leaf (inDelim(gram_rule,pat_gram_rule,scope,dlms))
