(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


(*i $Id$ i*)

open Util
open Pp
open Gramext
open Names
open Ast
open Ppextend
open Topconstr
open Genarg

type entry_type = argument_type

type production_position =
  | BorderProd of bool * Gramext.g_assoc option  (* true=left; false=right *)
  | InternalProd

type production_level =
  | NextLevel
  | NumLevel of int

type ('lev,'pos) constr_entry_key =
  | ETIdent | ETReference | ETBigint
  | ETConstr of ('lev * 'pos)
  | ETPattern
  | ETOther of string * string
  | ETConstrList of ('lev * 'pos) * Token.pattern list

type constr_production_entry =
    (production_level,production_position) constr_entry_key
type constr_entry = (int,unit) constr_entry_key
type simple_constr_production_entry = (production_level,unit) constr_entry_key

type nonterm_prod =
  | ProdList0 of nonterm_prod
  | ProdList1 of nonterm_prod * Token.pattern list
  | ProdOpt of nonterm_prod
  | ProdPrimitive of constr_production_entry

type prod_item =
  | Term of Token.pattern
  | NonTerm of constr_production_entry *
      (Names.identifier * constr_production_entry) option

type grammar_rule = {
  gr_name : string; 
  gr_production : prod_item list; 
  gr_action : constr_expr }

type grammar_entry = { 
  ge_name : constr_entry;
  gl_assoc : Gramext.g_assoc option;
  gl_rules : grammar_rule list }

type grammar_command = { 
  gc_univ : string; 
  gc_entries : grammar_entry list }

type grammar_associativity = Gramext.g_assoc option

(**********************************************************************)
(* Globalisation and type-checking of Grammar actions *)

type entry_context = identifier list

open Rawterm
open Libnames

let globalizer = ref (fun _ _ -> CHole dummy_loc)
let set_constr_globalizer f = globalizer := f

let act_of_ast vars = function
  | SimpleAction (loc,ConstrNode a) -> !globalizer vars a
  | SimpleAction (loc,CasesPatternNode a) -> 
      failwith "TODO:act_of_ast: cases_pattern"
  | CaseAction _ -> failwith "case/let not supported"

let to_act_check_vars = act_of_ast

type syntax_modifier =
  | SetItemLevel of string list * production_level
  | SetLevel of int
  | SetAssoc of Gramext.g_assoc
  | SetEntryType of string * simple_constr_production_entry
  | SetOnlyParsing
  | SetFormat of string located

type nonterm =
  | NtShort of string
  | NtQual of string * string
type grammar_production =
  | VTerm of string
  | VNonTerm of loc * nonterm * Names.identifier option
type raw_grammar_rule = string * grammar_production list * grammar_action
type raw_grammar_entry = string * grammar_associativity * raw_grammar_rule list

(* No kernel names in Grammar's *)
let subst_constr_expr _ a = a

let subst_grammar_rule subst gr =
  { gr with gr_action = subst_constr_expr subst gr.gr_action }

let subst_grammar_entry subst ge =
  { ge with gl_rules = List.map (subst_grammar_rule subst) ge.gl_rules }

let subst_grammar_command subst gc =
  { gc with gc_entries = List.map (subst_grammar_entry subst) gc.gc_entries }


(*s Terminal symbols interpretation *)

let is_ident_not_keyword s =
  match s.[0] with
    | 'a'..'z' | 'A'..'Z' | '_' -> not (Lexer.is_keyword s)
    | _ -> false

let is_number s =
  match s.[0] with
    | '0'..'9' -> true
    | _ -> false

let strip s =
  let len =
    let rec loop i len =
      if i = String.length s then len
      else if s.[i] == ' ' then loop (i + 1) len
      else loop (i + 1) (len + 1)
    in
    loop 0 0
  in
  if len == String.length s then s
  else
    let s' = String.create len in
    let rec loop i i' =
      if i == String.length s then s'
      else if s.[i] == ' ' then loop (i + 1) i'
      else begin s'.[i'] <- s.[i]; loop (i + 1) (i' + 1) end
    in
    loop 0 0

let terminal s =
  let s = strip s in
  if s = "" then failwith "empty token";
  if is_ident_not_keyword s then ("IDENT", s)
  else if is_number s then ("INT", s)
  else ("", s)

(*s Non-terminal symbols interpretation *)

(* For compatibility *)
let warn nt nt' =
  warning ("'"^nt^"' grammar entry is obsolete; use name '"^nt'^"' instead");
  nt'

let rename_command_entry nt =
  if String.length nt >= 7 & String.sub nt 0 7 = "command"
  then warn nt ("constr"^(String.sub nt 7 (String.length nt - 7)))
  else if nt = "lcommand" then warn nt "lconstr"
  else if nt = "lassoc_command4" then warn nt "lassoc_constr4"
  else nt

(* This translates constr0, constr1, ... level into camlp4 levels of constr *)

let explicitize_prod_entry inj pos univ nt =
  if univ = "prim" & nt = "var" then ETIdent else
  if univ = "prim" & nt = "bigint" then ETBigint else
  if univ <> "constr" then ETOther (univ,nt) else
  match nt with
  | "constr0" -> ETConstr (inj 0,pos)
  | "constr1" -> ETConstr (inj 1,pos)
  | "constr2" -> ETConstr (inj 2,pos)
  | "constr3" -> ETConstr (inj 3,pos)
  | "lassoc_constr4" -> ETConstr (inj 4,pos)
  | "constr5" -> ETConstr (inj 5,pos)
  | "constr6" -> ETConstr (inj 6,pos)
  | "constr7" -> ETConstr (inj 7,pos)
  | "constr8" -> ETConstr (inj 8,pos)
  | "constr" when !Options.v7 -> ETConstr (inj 8,pos)
  | "constr9" -> ETConstr (inj 9,pos)
  | "constr10" | "lconstr" -> ETConstr (inj 10,pos)
  | "pattern" -> ETPattern
  | "ident" -> ETIdent
  | "global" -> ETReference
  | _ -> ETOther (univ,nt)

let explicitize_entry = explicitize_prod_entry (fun x -> x) ()

(* Express border sub entries in function of the from level and an assoc *)
(* We're cheating: not necessarily the same assoc on right and left *)
let clever_explicitize_prod_entry pos univ from en =
  let t = explicitize_prod_entry (fun x -> NumLevel x) pos univ en in
  match from with
    | ETConstr (from,()) ->
	(match t with
	  | ETConstr (n,BorderProd (left,None))
              when (n=NumLevel from & left) ->
	      ETConstr (n,BorderProd (left,Some Gramext.LeftA))
	  | ETConstr (NumLevel n,BorderProd (left,None))
              when (n=from-1 & not left) ->
	      ETConstr
                (NumLevel (n+1),BorderProd (left,Some Gramext.LeftA))
	  | ETConstr (NumLevel n,BorderProd (left,None))
              when (n=from-1 & left) ->
	      ETConstr
                (NumLevel (n+1),BorderProd (left,Some Gramext.RightA))
	  | ETConstr (n,BorderProd (left,None))
              when (n=NumLevel from & not left) ->
	      ETConstr (n,BorderProd (left,Some Gramext.RightA))
	  | t -> t)
    | _ -> t

let qualified_nterm current_univ pos from = function
  | NtQual (univ, en) ->
      clever_explicitize_prod_entry pos univ from en
  | NtShort en ->
      clever_explicitize_prod_entry pos current_univ from en

let check_entry check_entry_type = function
  | ETOther (u,n) -> check_entry_type (u,n)
  | _ -> ()

let nterm loc (((check_entry_type,univ),from),pos) nont =
  let typ = qualified_nterm univ pos from nont in
  check_entry check_entry_type typ;
  typ

let prod_item univ env = function
  | VTerm s -> env, Term (terminal s)
  | VNonTerm (loc, nt, Some p) ->
     let typ = nterm loc univ nt in
      (p :: env, NonTerm (typ, Some (p,typ)))
  | VNonTerm (loc, nt, None) ->
      let typ = nterm loc univ nt in 
      env, NonTerm (typ, None)

let rec prod_item_list univ penv pil current_pos =
  match pil with
    | [] -> [], penv
    | pi :: pitl ->
	let pos = if pitl=[] then (BorderProd (false,None)) else current_pos in
	let (env, pic) = prod_item (univ,pos) penv pi in
	let (pictl, act_env) = prod_item_list univ env pitl InternalProd in
        (pic :: pictl, act_env)

let gram_rule univ (name,pil,act) =
  let (pilc, act_env) = prod_item_list univ [] pil (BorderProd (true,None)) in
  let a = to_act_check_vars act_env act in
  { gr_name = name; gr_production = pilc; gr_action = a }

let border = function
  | NonTerm (ETConstr(_,BorderProd (_,a)),_) :: _ -> a
  | _ -> None

let clever_assoc ass g =
  if g.gr_production <> [] then
    (match border g.gr_production, border (List.rev g.gr_production) with
      | Some LeftA, Some RightA -> ass (* Untractable; we cheat *)
      | Some LeftA, _ -> Some LeftA
      | _, Some RightA -> Some RightA
      | _ -> Some NonA)
  else ass

let gram_entry univ (nt, ass, rl) =
  let from = explicitize_entry (snd univ) nt in
  let l = List.map (gram_rule (univ,from)) rl in
  let ass = List.fold_left clever_assoc ass l in
  { ge_name = from;
    gl_assoc = ass;
    gl_rules = l }

let interp_grammar_command univ ge entryl =
  { gc_univ = univ;
    gc_entries = List.map (gram_entry (ge,univ)) entryl }

(* unparsing objects *)

type 'pat unparsing_hunk = 
  | PH of 'pat * string option * parenRelation
  | RO of string
  | UNP_BOX of ppbox * 'pat unparsing_hunk list
  | UNP_BRK of int * int
  | UNP_TBRK of int * int
  | UNP_TAB
  | UNP_FNL
  | UNP_SYMBOLIC of string option * string * 'pat unparsing_hunk

let rec subst_hunk subst_pat subst hunk = match hunk with
  | PH (pat,so,pr) ->
      let pat' = subst_pat subst pat in
	if pat'==pat then hunk else
	  PH (pat',so,pr)
  | RO _ -> hunk
  | UNP_BOX (ppbox, hunkl) ->
      let hunkl' = list_smartmap (subst_hunk subst_pat subst) hunkl in
	if hunkl' == hunkl then hunk else
	  UNP_BOX (ppbox, hunkl')
  | UNP_BRK _
  | UNP_TBRK _
  | UNP_TAB
  | UNP_FNL -> hunk
  | UNP_SYMBOLIC (s1, s2, pat) ->
      let pat' = subst_hunk subst_pat subst pat in
	if pat' == pat then hunk else
	  UNP_SYMBOLIC (s1, s2, pat')

(* Checks if the precedence of the parent printer (None means the
   highest precedence), and the child's one, follow the given
   relation. *)

let tolerable_prec oparent_prec_reln child_prec =
  match oparent_prec_reln with
    | Some (pprec, L) -> child_prec < pprec
    | Some (pprec, E) -> child_prec <= pprec
    | Some (_, Prec level) -> child_prec <= level
    | _ -> true

type 'pat syntax_entry = {
  syn_id : string;
  syn_prec: precedence;
  syn_astpat : 'pat;
  syn_hunks : 'pat unparsing_hunk list }

let subst_syntax_entry subst_pat subst sentry = 
  let syn_astpat' = subst_pat subst sentry.syn_astpat in
  let syn_hunks' = list_smartmap (subst_hunk subst_pat subst) sentry.syn_hunks 
  in
    if syn_astpat' == sentry.syn_astpat 
      && syn_hunks' == sentry.syn_hunks then sentry 
    else
      { sentry with
	  syn_astpat = syn_astpat' ;
	  syn_hunks = syn_hunks' ;
      }
      
type 'pat syntax_command = { 
  sc_univ : string; 
  sc_entries : 'pat syntax_entry list }

let subst_syntax_command subst_pat subst scomm = 
  let sc_entries' = 
    list_smartmap (subst_syntax_entry subst_pat subst) scomm.sc_entries 
  in
    if sc_entries' == scomm.sc_entries then scomm else
      { scomm with sc_entries = sc_entries' }
      
type syntax_rule = string * Coqast.t * Coqast.t unparsing_hunk list
type raw_syntax_entry = precedence * syntax_rule list

let rec interp_unparsing env = function
  | PH (ast,ext,pr) -> PH (Ast.val_of_ast env ast,ext,pr)
  | UNP_BOX (b,ul) -> UNP_BOX (b,List.map (interp_unparsing env) ul)
  | UNP_BRK _ | RO _ | UNP_TBRK _ | UNP_TAB | UNP_FNL as x -> x
  | UNP_SYMBOLIC (x,y,u) -> UNP_SYMBOLIC (x,y,interp_unparsing env u)

let rule_of_ast univ prec (s,spat,unp) =
  let (astpat,meta_env) = Ast.to_pat [] spat in
  let hunks = List.map (interp_unparsing meta_env) unp in
  { syn_id = s;
    syn_prec = prec;
    syn_astpat = astpat;
    syn_hunks = hunks }

let level_of_ast univ (prec,rl) = List.map (rule_of_ast univ prec) rl

let interp_syntax_entry univ sel =
  { sc_univ = univ;
    sc_entries = List.flatten (List.map (level_of_ast univ) sel)}


