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
open Coqast
open Ast
open Extend
open Esyntax
open Libobject
open Library
open Summary
open Astterm
open Vernacexpr
open Pcoq

(*************************
 **** PRETTY-PRINTING ****
 *************************)

let globalize_typed_ast t =
  let sign = Global.named_context () in
  match t with
  | Ast.PureAstNode t -> Ast.PureAstNode (globalize_constr t)
  | _ -> (* TODO *) t

(* This updates default parsers for Grammar actions and Syntax *)
(* patterns by inserting globalization *)
(* Done here to get parsing/g_*.ml4 non dependent from kernel *)
let _ = Pcoq.set_globalizer globalize_typed_ast

(* This installs default quotations parsers to escape the ast parser *)
(* "constr" is used by default in quotations found in the ast parser *) 
let constr_parser_with_glob = Pcoq.map_entry Astterm.globalize_constr Constr.constr

let _ = define_quotation true "constr" constr_parser_with_glob

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


(************************
 ******* GRAMMAR ********
 ************************)

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

let gram_define_entry (u,_ as univ) ((ntl,nt),et,assoc,rl) =
  let etyp = match et with None -> entry_type_from_name u | Some e -> e in
  create_entry_if_new univ nt etyp;
  let etyp = match etyp with 
    | AstListType -> ETastl
    | GenAstType Genarg.ConstrArgType -> ETast
    | PureAstType -> ETast
    | _ -> error "Cannot arbitrarily extend non ast entries" in
  (nt, etyp, assoc, rl)

let add_grammar_obj univ l =
  let u = create_univ_if_new univ in
  let entryl = List.map (gram_define_entry u) l in
  let g = interp_grammar_command univ get_entry_type entryl in
  Lib.add_anonymous_leaf (inGrammar (Egrammar.AstGrammar g))

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


(* A notation comes with a grammar rule, a pretty-printing rule, an
   identifiying pattern called notation and an associated scope *)
let load_infix _ (_,(gr,se,ntn,scope,pat)) =
  Symbols.declare_scope scope

let open_infix i (_,(gr,se,ntn,scope,pat)) =
  if i=1 then begin
    let b = Symbols.exists_notation_in_scope scope ntn in
    (* Declare the printer rule and its interpretation *)
    if not b then Esyntax.add_ppobject {sc_univ="constr";sc_entries=se};
    (* Declare the grammar rule ... *)
    if not (Symbols.exists_notation ntn) then Egrammar.extend_grammar gr;
    (* ... and its interpretation *)
    if not b then Symbols.declare_notation ntn pat scope
  end

let cache_infix o =
  load_infix 1 o;
  open_infix 1 o

let subst_infix (_,subst,(gr,se,ntn,scope,pat)) =
  (Egrammar.subst_all_grammar_command subst gr,
   list_smartmap (Extend.subst_syntax_entry Ast.subst_astpat subst) se,
   ntn,
   scope,
   Rawterm.subst_raw subst pat)

let (inInfix, outInfix) =
  declare_object {(default_object "INFIX") with
       open_function = open_infix;
       cache_function = cache_infix;
       subst_function = subst_infix;
       load_function = load_infix;
       classify_function = (fun (_,o) -> Substitute o);
       export_function = (fun x -> Some x)}

(* Build the syntax and grammar rules *)

type symbol =
  | Terminal of string
  | NonTerminal of (int * parenRelation) * string

let prec_assoc = function
  | Some(Gramext.RightA) -> (L,E)
  | Some(Gramext.LeftA) -> (E,L)
  | Some(Gramext.NonA) -> (L,L)
  | None -> (E,L)  (* LEFTA by default *)

let constr_tab =
  [| "constr0"; "constr1"; "constr2"; "constr3"; "lassoc_constr4";
     "constr5"; "constr6"; "constr7"; "constr8"; "constr9"; "constr10" |]
  
let constr_rule (n,p) =
  if p = E then constr_tab.(n) else constr_tab.(max (n-1) 0)

let nonterm_meta nt var =
  NonTerm(ProdPrimitive ("constr",nt), Some (var,ETast))

let meta_pattern m = Pmeta(m,Tany)

let collect_metas sl =
  List.fold_right
    (fun it metatl -> match it with
      | NonTerminal (_,m) -> Pcons(meta_pattern m, metatl)
      | _ -> metatl)
    sl Pnil

let make_hunks symbols =
  List.fold_right
    (fun it l -> match it with
      | NonTerminal ((_,lp),m) -> PH (meta_pattern m, None, lp) :: l
      | Terminal s ->
	  let n,s =
	    if is_letter (s.[String.length s -1]) or is_letter (s.[0])
	    then 1,s^" " else 0,s
	  in
	  UNP_BRK (n, 1) :: RO s :: l)
    symbols []

let string_of_symbol = function
  | NonTerminal _ -> "_"
  | Terminal s -> s

let string_of_assoc = function
  | Some(Gramext.RightA) -> "RIGHTA"
  | Some(Gramext.LeftA) | None -> "LEFTA"
  | Some(Gramext.NonA) -> "NONA"

let make_symbolic assoc n symbols =
  (string_of_assoc assoc) ^ "-" ^ (string_of_int n) ^ ":" ^
  (String.concat " " (List.map string_of_symbol symbols))

let make_production =
  List.map (function
    | NonTerminal (lp,m) -> nonterm_meta (constr_rule lp) m
    | Terminal s -> Term ("",s))

let make_constr_grammar_rule n fname prod action =
  Egrammar.AstGrammar
  { gc_univ = "constr";
    gc_entries =
      [ { ge_name = constr_rule (n, E);
          ge_type = ETast;
          gl_assoc = None;
          gl_rules =
            [ { gr_name = fname;
                gr_production = prod;
                gr_action = action} ]
        }
      ]
  }

let rec translate_implicits n = function
  | [] -> []
  | q::l when q=n -> true::translate_implicits (n+1) l
  | impls -> false::translate_implicits (n+1) impls

let implicits_of_extended_reference = function
  | Libnames.TrueGlobal ref -> translate_implicits 1 (Impargs.implicits_of_global ref)
  | Libnames.SyntacticDef _ -> []

let create_meta n = "$e"^(string_of_int n)

(*
let rec find_symbols c_first c_next c_last new_var = function
  | []    -> []
  | ["_"] -> [NonTerminal (c_last, create_meta new_var)]
  | ("_"::sl) ->
      let symb = NonTerminal (c_first, create_meta new_var) in
      symb :: find_symbols c_next c_next c_last (new_var+1) sl
  | s :: sl ->
      let symb = Terminal s in
      symb :: find_symbols c_next c_next c_last new_var sl
*)
let rec find_symbols c_first c_next c_last vars new_var = function
  | []    -> (vars, [])
  | x::sl when is_letter x.[0] ->
      let id = Names.id_of_string x in
      if List.mem_assoc id vars then
        error ("Variable "^x^" occurs more than once");
      let prec = if sl = [] then c_last else c_first in
      let (vars,l) = find_symbols c_next c_next c_last vars (new_var+1) sl in
      let meta = create_meta new_var in
      ((id,ope ("META",[num new_var]))::vars, NonTerminal (prec, meta) :: l)
  | "_"::sl ->
      warning "Found '_'";
      let prec = if sl = [] then c_last else c_first in
      let (vars,l) = find_symbols c_next c_next c_last vars (new_var+1) sl in
      let meta = create_meta new_var in
      (vars, NonTerminal (prec, meta) :: l)
  | s :: sl ->
      let (vars,l) = find_symbols c_next c_next c_last vars new_var sl in
      (vars, Terminal s :: l)

let make_grammar_pattern symbols ntn =
  Pnode("NOTATION",Pcons(Pquote (Str (dummy_loc,ntn)), collect_metas symbols))

let make_grammar_rule n symbols ntn =
  let prod = make_production symbols in
  let action = Act (PureAstPat (make_grammar_pattern symbols ntn)) in
  make_constr_grammar_rule n ("notation "^ntn) prod action

let metas_of sl =
  List.fold_right
    (fun it metatl -> match it with
      | NonTerminal (_,m) -> m::metatl
      | _ -> metatl)
    sl []

let make_pattern symbols ast =
  let env = List.map (fun m -> (m,ETast)) (metas_of symbols) in
  fst (to_pat env ast)

let make_syntax_rule n name symbols ast ntn sc =
  [{syn_id = name;
    syn_prec = (n,0,0);
    syn_astpat = make_pattern symbols ast;
    syn_hunks = [UNP_SYMBOLIC(sc,ntn,UNP_BOX (PpHOVB 1, make_hunks symbols))]}]

let subst_meta_ast subst a =
  let found = ref [] in
  let rec subst_rec subst = function
  | Smetalam (loc,s,body) -> Smetalam (loc,s,subst_rec subst body)
  | Node(loc,"META",_) -> error "Unexpected metavariable in notation"
  | Node(_,"QUALID",[Nvar(_,id)]) as x ->
      (try let a = List.assoc id subst in found:=id::!found; a
       with Not_found -> x)
  | Node(loc,op,args) -> Node (loc,op, List.map (subst_rec subst) args)
  | Slam(loc,None,body) -> Slam(loc,None,subst_rec subst body)
  | Slam(loc,Some s,body) ->
      (* Prévenir que "s" peut forcer une capturer à l'instantiation de la *)
      (* règle de grammaire ?? *)
      Slam(loc,Some s,subst_rec (List.remove_assoc s subst) body)
  | Nmeta _ | Id _ | Nvar _ | Str _ | Num _ | Path _ as a -> a
  | Dynamic _ as a -> (* Hum... what to do here *) a
  in
  let a = subst_rec subst a in
  let l = List.filter (fun (x,_) -> not (List.mem x !found)) subst in
  if l <> [] then
    (let x = string_of_id (fst (List.hd l)) in
     error (x^" is unbound in the right-hand-side"));
  a

let rec reify_meta_ast = function
  | Smetalam (loc,s,body) -> Smetalam (loc,s,reify_meta_ast body)
  | Node(loc,"META",[Num (_,n)]) -> Nmeta (loc,create_meta n)
  | Node(loc,"ISEVAR",[]) -> Nmeta (loc,"$_")
  | Node(loc,op,args) -> Node (loc,op, List.map (reify_meta_ast) args)
  | Slam(loc,na,body) -> Slam(loc,na,reify_meta_ast body)
  | Nmeta _ | Id _ | Nvar _ | Str _ | Num _ | Path _ as a -> a
  | Dynamic _ as a -> (* Hum... what to do here *) a

(* Distfix, Infix, Notations *)

let add_notation assoc n df ast sc =
  let scope = match sc with None -> Symbols.default_scope | Some sc -> sc in
  let (lp,rp) = prec_assoc assoc in
  let (subst,symbols) = find_symbols (n,lp) (n,L) (n,rp) [] 1 (split df) in
  let notation = make_symbolic assoc n symbols in
  let rule_name = notation^"_"^scope^"_notation" in
  (* To globalize... *)
  let vars = List.map fst subst in
  let ast = subst_meta_ast subst ast in
  let r = interp_rawconstr_gen Evd.empty (Global.env()) [] false vars ast in
  let ast = Termast.ast_of_rawconstr r in
  let ast = reify_meta_ast ast in
  let gram_rule = make_grammar_rule n symbols notation in
  let syntax_rule = make_syntax_rule n rule_name symbols ast notation scope in
  Lib.add_anonymous_leaf (inInfix(gram_rule,syntax_rule,notation,scope,r))

(* TODO add boxes information in the expression *)

let inject_var x = ope ("QUALID", [nvar (id_of_string x)])

let rec rename x vars n = function
  | [] ->
      (vars,[])
  | "_"::l ->
      let (vars,l) = rename x vars (n+1) l in
      let xn = x^(string_of_int n) in
      ((inject_var xn)::vars,xn::l)
  | y::l ->
      let (vars,l) = rename x vars n l in (vars,y::l)

let add_distfix assoc n df astf sc =
  (* "x" cannot clash since ast is globalized (included section vars) *)
  let (vars,l) = rename "x" [] 1 (split df) in
  let df = String.concat " " l in
  let ast = ope("APPLIST",astf::vars) in
  add_notation assoc n df ast sc

let add_infix assoc n inf qid sc =
  let pr = Astterm.globalize_qualid qid in
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
  let ast = ope("APPLIST",pr::metas) in
  add_notation assoc n ("x "^inf^" y") ast sc

(* Delimiters *)
let load_delimiters _ (_,(gram_rule,scope,dlm)) =
  Symbols.declare_scope scope

let open_delimiters i (_,(gram_rule,scope,dlm)) =
  if i=1 then begin
    Egrammar.extend_grammar gram_rule;   (* For parsing *)
    Symbols.declare_delimiters scope dlm (* For printing *)
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

let add_delimiters scope (l,r as dlms) =
  if l = "" or r = "" then error "Delimiters cannot be empty";
  let fname = scope^"_delimiters" in
  let symbols = [Terminal l; NonTerminal ((8,E),"$e"); Terminal r] in
  let prod = make_production symbols in
  let args = Pcons(Pquote (string scope), Pcons (Pmeta ("$e",Tany), Pnil)) in
  let action = Act (PureAstPat (Pnode("DELIMITERS",args))) in
  let gram_rule = make_constr_grammar_rule 0 fname prod action in
  Lib.add_anonymous_leaf (inDelim(gram_rule,scope,dlms))
