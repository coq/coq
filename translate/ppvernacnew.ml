(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)  

open Pp
open Names
open Nameops
open Nametab 
open Util
open Extend
open Vernacexpr
open Ppconstrnew
open Pptacticnew
open Rawterm
open Coqast
open Genarg
open Pcoq
open Ast
open Libnames
open Ppextend
open Topconstr

let sep = fun _ -> spc()
let sep_p = fun _ -> str"."
let sep_v = fun _ -> str","
let sep_pp = fun _ -> str":"
let sep_pv = fun _ -> str"; "

let pr_located pr (loc,x) = pr x

let pr_entry_prec = function
  | Some Gramext.LeftA -> spc() ++ str"LEFTA"
  | Some Gramext.RightA -> spc() ++ str"RIGHTA"
  | Some Gramext.NonA -> spc() ++ str"NONA"
  | None -> mt()

let pr_metaid _ = str"<TODO>"
let pr_metanum _ = str"<TODO>"

let pr_set_entry_type = function
  | ETIdent -> str"ident"
  | ETReference -> str"global"
  | ETPattern -> str"pattern"
  | ETConstr _ | ETOther (_,_) -> mt ()
  | ETBigint -> str"TODO"

let pr_non_terminal = function
  | NtQual (u,nt) -> str u ++ str" : " ++ str nt
  | NtShort nt -> str nt

let pr_production_item = function
  | VNonTerm (loc,nt,Some p) -> pr_non_terminal nt ++ str"(" ++ pr_metaid p ++ str")"
  | VNonTerm (loc,nt,None) -> pr_non_terminal nt
  | VTerm s -> str s

let pr_comment pr_c = function
  | CommentConstr c -> pr_c c
  | CommentString s -> str s
  | CommentInt n -> int n

let pr_in_out_modules = function
  | SearchInside l -> str"inside" ++ spc() ++ prlist_with_sep sep pr_reference l
  | SearchOutside [] -> str"outside"
  | SearchOutside l -> str"outside" ++ spc() ++ prlist_with_sep sep pr_reference l

let pr_search a b pr_c = match a with
  | SearchHead qid -> str"Search" ++ spc() ++ pr_reference qid ++ spc() ++ pr_in_out_modules b
  | SearchPattern c -> str"SearchPattern" ++ spc() ++ pr_c c ++ spc() ++ pr_in_out_modules b
  | SearchRewrite c -> str"SearchRewrite" ++ spc() ++ pr_c c ++ spc() ++ pr_in_out_modules b
  | SearchAbout _ -> str"TODO"

let pr_class_rawexpr = function
  | FunClass -> str"FUNCLASS"
  | SortClass -> str"SORTCLASS"
  | RefClass qid -> pr_reference qid

let pr_option_ref_value = function
  | QualidRefValue id -> pr_reference id
  | StringRefValue s -> qs s

let pr_printoption a b = match a with
  | Goptions.PrimaryTable table -> str table ++ pr_opt (prlist_with_sep sep pr_option_ref_value) b
  | Goptions.SecondaryTable (table,field) -> str table ++ spc() ++ str field ++ pr_opt (prlist_with_sep sep pr_option_ref_value) b

let pr_set_option a b = 
  let pr_opt_value = function 
    | IntValue n -> int n
    | StringValue s -> str s
    | BoolValue b -> mt()
  in pr_printoption a None ++ spc() ++ pr_opt_value b

let pr_topcmd _ = str"(* <Warning> : No printer for toplevel commands *)"

let pr_destruct_location = function
  | Tacexpr.ConclLocation ()  -> str"Conclusion"
  | Tacexpr.HypLocation b -> if b then str"Discardable Hypothesis" else str"Hypothesis"

let pr_opt_hintbases l = match l with
  | [] -> mt()
  | _ as z -> str":" ++ spc() ++ prlist_with_sep sep str z

let pr_hints db h pr_c = 
  let db_name = function
    | [] -> (false , mt())
    | c1::c2 -> match c1 with
      |	None,_ -> (false , mt())
      |	Some name,_ -> (true , pr_id name)
  in let opth = pr_opt_hintbases db 
  in let pr_aux = function
    | CRef qid -> pr_reference qid
    | _ -> mt ()
  in match h with
  | HintsResolve l -> let (f,dbn) = db_name l in if f then hov 1 (str"Hint" ++ spc() ++ dbn ++ spc() ++ opth ++ spc() ++ str":=" ++ spc() ++ str"Resolve" ++ spc() ++ prlist_with_sep sep pr_c (List.map (fun (_,y) -> y) l)) else hov 1 (str"Hints Resolve" ++ spc() ++ prlist_with_sep sep pr_aux (List.map (fun (_,y) -> y) l) ++ spc() ++ opth)
  | HintsImmediate l -> let (f,dbn) = db_name l in if f then hov 1 (str"Hint" ++ spc() ++ dbn ++ spc() ++ opth ++ spc() ++ str":=" ++ spc() ++ str"Immediate" ++ spc() ++ prlist_with_sep sep pr_c (List.map (fun (_,y) -> y) l)) else hov 1 (str"Hints Immediate" ++ spc() ++ prlist_with_sep sep pr_aux (List.map (fun (_,y) -> y) l) ++ spc() ++ opth)
  | HintsUnfold l -> let (f,dbn) = db_name l in if f then hov 1 (str"Hint" ++ spc() ++ dbn ++ spc() ++ opth ++ spc() ++ str":=" ++ spc() ++ str"Unfold" ++ spc() ++ prlist_with_sep sep pr_reference (List.map (fun (_,y) -> y) l)) else hov 1 (str"Hints Unfold" ++ spc() ++ prlist_with_sep sep pr_reference (List.map (fun (_,y) -> y) l) ++ spc() ++ opth)
  | HintsConstructors (n,c) -> hov 1 (str"Hint" ++ spc() ++ pr_id n ++ spc() ++ opth ++ spc() ++ str":=" ++ spc() ++ str"Constructors" ++ spc() ++ pr_reference c) 
  | HintsExtern (name,n,c,tac) -> hov 1 (str"Hint" ++ spc() ++ pr_id name ++ spc() ++ opth ++ spc() ++ str":=" ++ spc() ++ str"Extern" ++ spc() ++ int n ++ spc() ++ pr_c c ++ pr_raw_tactic tac)
 
let pr_with_declaration pr_c = function
  | CWith_Definition (id,c) -> str"Definition" ++ spc() ++ pr_id id ++ str" := " ++ pr_c c
  | CWith_Module (id,qid) -> str"Module" ++ spc() ++ pr_id id ++ str" := " ++ pr_located pr_qualid qid

let rec pr_module_type pr_c = function
  | CMTEident qid -> pr_located pr_qualid qid
  | CMTEwith (mty,decl) -> pr_module_type pr_c mty ++ spc() ++ str"with" ++ spc() ++ pr_with_declaration pr_c decl

let pr_module_vardecls pr_c (l,mty) = prlist_with_sep (fun _ -> str",") pr_id l ++ spc() ++ pr_module_type pr_c mty

let pr_module_binders l pr_c = str"[" ++ prlist_with_sep (fun _ -> str";") (pr_module_vardecls pr_c) l ++ str"]"

let pr_module_binders_list l pr_c = pr_module_binders l pr_c

let rec pr_module_expr = function
  | CMEident qid -> pr_located pr_qualid qid
  | CMEapply (me1,me2) -> pr_module_expr me1 ++ spc() ++ pr_module_expr me2

let pr_opt_casted_constr pr_c = function
  | CCast (loc,c,t) -> pr_c c ++ str":" ++ pr_c t
  | _ as c -> pr_c c

let pr_type_option pr_c = function
  | CHole loc -> mt()
  | _ as c -> str":" ++ pr_c c

let pr_valdecls pr_c = function
  | LocalRawAssum (na,c) -> prlist_with_sep (fun _ -> str",") (pr_located pr_name) na ++ spc() ++ pr_type_option pr_c c
  | LocalRawDef (na,c) -> pr_located pr_name na ++ spc() ++ str":=" ++ spc() ++ pr_opt_casted_constr pr_c c

let pr_binders pr_c l = match l with
| [] -> mt()
| _ as t -> str"(" ++ prlist_with_sep (fun _ -> str") (") (pr_valdecls pr_c) t ++ str")"

let pr_onescheme (id,dep,ind,s) = pr_id id ++ spc() ++ str":=" ++ spc() ++ if dep then str"Induction for" else str"Minimality for" ++ spc() ++ pr_reference ind ++ spc() ++ str"Sort" ++ spc() ++ pr_sort s

let pr_class_rawexpr = function
  | FunClass -> str"FUNCLASS"
  | SortClass -> str"SORTCLASS"
  | RefClass qid -> pr_reference qid

let pr_assumption_token = function
  | (Decl_kinds.Local,Decl_kinds.Logical) -> str"Hypothesis"
  | (Decl_kinds.Local,Decl_kinds.Definitional) -> str"Variable"
  | (Decl_kinds.Global,Decl_kinds.Logical) -> str"Axiom"
  | (Decl_kinds.Global,Decl_kinds.Definitional) -> str"Parameter"

let pr_params pr_c (a,(b,c)) = pr_id b ++ spc() ++ if a then str":>" else str":" ++ spc() ++ pr_c c

let pr_ne_params_list pr_c l = prlist_with_sep sep_pv (pr_params pr_c) l

let pr_thm_token = function
  | Decl_kinds.Theorem -> str"Theorem"
  | Decl_kinds.Lemma -> str"Lemma"
  | Decl_kinds.Fact -> str"Fact"
  | Decl_kinds.Remark -> str"Remark"

let pr_syntax_modifier = function
  | SetItemLevel (l,n) -> prlist_with_sep (fun _ -> str",") str l ++ spc() ++ str"at level" ++ spc() ++ int n
  | SetLevel n -> str"at level" ++ spc() ++ int n
  | SetAssoc Gramext.LeftA -> str"left associativity"
  | SetAssoc Gramext.RightA -> str"right associativity"
  | SetAssoc Gramext.NonA -> str"no associativity"
  | SetEntryType (x,typ) -> str x ++ spc() ++ pr_set_entry_type typ
  | SetOnlyParsing -> str"only parsing"

let pr_grammar_tactic_rule (name,(s,pil),t) = str name ++ spc() ++ str"[" ++ qs s ++ spc() ++ prlist_with_sep sep pr_production_item pil ++ str"]" ++ spc() ++ str"->" ++ spc() ++ str"[" ++ pr_raw_tactic t ++ str"]"

let pr_box b = let pr_boxkind = function
  | PpHB n -> str"h" ++ spc() ++ int n
  | PpVB n -> str"v" ++ spc() ++ int n
  | PpHVB n -> str"hv" ++ spc() ++ int n
  | PpHOVB n -> str"hov" ++ spc() ++ int n
  | PpTB -> str"t"
in str"<" ++ pr_boxkind b ++ str">"
 
let pr_paren_reln_or_extern = function
  | None,L -> str"L"
  | None,E -> str"E"
  | Some pprim,Any -> qs pprim
  | Some pprim,Prec p -> qs pprim ++ spc() ++ str":" ++ spc() ++ int p
  | _ -> mt()

let rec pr_next_hunks = function 
  | UNP_FNL -> str"FNL"
  | UNP_TAB -> str"TAB"
  | RO c -> qs c
  | UNP_BOX (b,ll) -> str"[" ++ pr_box b ++ prlist_with_sep sep pr_next_hunks ll ++ str"]"
  | UNP_BRK (n,m) -> str"[" ++ int n ++ spc() ++ int m ++ str"]"
  | UNP_TBRK (n,m) -> str"[ TBRK" ++ int n ++ spc() ++ int m ++ str"]"
  | PH (e,None,_) -> print_ast e
  | PH (e,Some ext,pr) -> print_ast e ++ spc() ++ str":" ++ spc() ++ pr_paren_reln_or_extern (Some ext,pr)
  | UNP_SYMBOLIC _ -> mt()

let pr_unparsing u = prlist_with_sep sep pr_next_hunks u

let pr_astpat a = str"<<" ++ print_ast a ++ str">>"

let pr_syntax_rule (nm,s,u) = str nm ++ spc() ++ str"[" ++ pr_astpat s ++ str"]" ++ spc() ++ str"->" ++ spc() ++ pr_unparsing u

let pr_syntax_entry (p,rl) = str"level" ++ spc() ++ int p ++ spc() ++ str":" ++ spc() ++ prlist_with_sep (fun _ -> brk(1,1) ++ str"|") pr_syntax_rule rl

let sep_end = str";"

(**************************************)
(* Pretty printer for vernac commands *)
(**************************************)
let make_pr_vernac pr_constr =

let pr_constrarg c = spc () ++ pr_constr c in
let pr_intarg n = spc () ++ int n in

let rec pr_vernac = function
  
  (* Proof management *)
  | VernacAbortAll -> str "Abort All"
  | VernacRestart -> str"Restart"
  | VernacSuspend -> str"Suspend"
  | VernacUnfocus -> str"Unfocus"
  | VernacGoal c -> str"Goal" ++ pr_constrarg c
  | VernacAbort id -> str"Abort" ++ pr_opt (pr_located pr_id) id
  | VernacResume id -> str"Resume" ++ pr_opt (pr_located pr_id) id
  | VernacUndo i -> if i=1 then str"Undo" else str"Undo" ++ pr_intarg i
  | VernacFocus i -> str"Focus" ++ pr_opt int i
  | VernacGo g -> 
      let pr_goable = function
	| GoTo i -> int i
	| GoTop -> str"top"
	| GoNext -> str"next"
	| GoPrev -> str"prev" 
      in str"Go" ++ spc() ++  pr_goable g
  | VernacShow s -> 
      let pr_showable = function
	| ShowGoal n -> str"Show" ++ pr_opt int n
	| ShowGoalImplicitly n -> str"Show Implicits" ++ pr_opt int n
	| ShowProof -> str"Show Proof"
	| ShowNode -> str"Show Node"
	| ShowScript -> str"Show Script"
	| ShowExistentials -> str"Show Existentials"
	| ShowTree -> str"Show Tree"
	| ShowProofNames -> str"Show Conjectures"
	| ShowIntros b -> str"Show " ++ (if b then str"Intros" else str"Intro")
	| ExplainProof l -> str"Explain Proof" ++ spc() ++ prlist_with_sep sep int l
	| ExplainTree l -> str"Explain Proof Tree" ++ spc() ++ prlist_with_sep sep int l 
      in pr_showable s
  | VernacCheckGuard -> str"Guarded"
  | VernacDebug b -> pr_topcmd b

  (* Resetting *)
  | VernacResetName id -> str"Reset" ++ spc() ++ pr_located pr_id id
  | VernacResetInitial -> str"Reset Initial"
  | VernacBack i -> if i=1 then str"Back" else str"Back" ++ pr_intarg i

  (* State management *)
  | VernacWriteState s -> str"Write State" ++ spc () ++ qs s
  | VernacRestoreState s -> str"Restore State" ++ spc() ++ qs s

  (* Control *)
  | VernacList l -> hov 2 (str"[" ++ spc() ++ prlist_with_sep (fun _ -> sep_end ++ fnl() ) (pr_located pr_vernac) l ++ spc() ++ str"]") 
  | VernacLoad (f,s) -> str"Load" ++ if f then (spc() ++ str"Verbose" ++ spc()) else spc()  ++ str s
  | VernacTime v -> str"Time" ++ spc() ++ pr_vernac v
  | VernacVar id -> pr_id id
  
  (* Syntax *) 
  | VernacGrammar _ -> str"(* <Warning> : Grammar is replaced by Notation *)"
  | VernacTacticGrammar l -> hov 1 (str"Grammar tactic simple_tactic :=" ++ spc() ++ prlist_with_sep (fun _ -> brk(1,1) ++ str"|") pr_grammar_tactic_rule l) (***)
  | VernacSyntax (u,el) -> hov 1 (str"Syntax" ++ str u ++ prlist_with_sep (fun _ -> str";") pr_syntax_entry el) (***)
  | VernacOpenScope sc -> str"Open Scope" ++ spc() ++ str sc
  | VernacDelimiters (sc,key) -> str"Delimits Scope" ++ spc () ++ str sc ++ spc () ++ str key
  | VernacArgumentsScope (q,scl) -> let pr_opt_scope = function 
      |	None -> str"_"
      |	Some sc -> str sc in 
    str"Arguments Scope" ++ spc() ++ pr_reference q ++ spc() ++ str"[" ++ prlist_with_sep sep pr_opt_scope scl ++ str"]"
  | VernacInfix (a,p,s,q,_,sn) -> (* A Verifier *)
      h 0 (str"Infix" ++ pr_entry_prec a ++ pr_intarg p ++ spc() ++ qs s ++ spc() ++ pr_reference q ++ (match sn with
    | None -> mt()
    | Some sc -> spc() ++ str":" ++ spc() ++ str sc))
  | VernacDistfix (a,p,s,q,sn) -> h 0 (str"Distfix" ++ pr_entry_prec a ++ pr_intarg p ++ spc() ++ qs s ++ spc() ++ pr_reference q ++ (match sn with
    | None -> mt()
    | Some sc -> spc() ++ str":" ++ spc() ++ str sc))
  | VernacNotation (s,c,l,opt) -> str"Notation" ++ spc() ++ qs s ++ pr_constrarg c ++ (match l with
    | [] -> mt()
    | _ as t -> spc() ++ str"(" ++ prlist_with_sep (fun _ -> str",") pr_syntax_modifier t ++ str")") ++ (match opt with
      |	None -> mt()
      |	Some sc -> spc() ++ str":" ++ spc() ++ str sc) (***)
  | VernacSyntaxExtension (a,b) -> str"Uninterpreted Notation" ++ spc() ++ qs a ++ (match b with | [] -> mt() | _ as l -> str"(" ++ prlist_with_sep (fun _ -> str",") pr_syntax_modifier l ++ str")")

  (* Gallina *)
  | VernacDefinition (d,id,b,f,e) -> (* A verifier... *)
      let pr_def_token = function
      |	Decl_kinds.LCoercion -> str"Coercion Local"
      |	Decl_kinds.GCoercion -> str"Coercion"
      |	Decl_kinds.LDefinition -> str"Local"
      |	Decl_kinds.GDefinition -> str"Definition"
      |	Decl_kinds.SCanonical -> str"Canonical Structure"
  in let pr_reduce = function
    | None -> mt()
    | Some r -> str"Eval" ++ spc() ++ pr_red_expr (pr_constr, fun _ -> str"TODO" (* pr_metanum pr_reference *)) r ++ spc() ++ str"in" ++ spc()
  in let pr_binders_def = function
    | [] -> mt ()
    | _ as l -> spc() ++ str"(" ++ prlist_with_sep (fun _ -> str") (") (pr_valdecls pr_constr) l ++ str")"
  in let pr_valloc (l,c) = match l with
  | [] -> mt ()
  | _ -> prlist_with_sep (fun _ -> str",") (pr_located pr_name) l ++ str":" ++ pr_constr c
  in let pr_binders_def2 = function
    | [] -> mt ()
    | _ as l -> spc() ++ str"(" ++ prlist_with_sep (fun _ -> str") (") pr_valloc l ++ str")"
  in let pr_def_body = function
    | DefineBody (bl,red,c,d) -> (match c with
      |	CLambdaN (_,bl2,a) -> (pr_binders_def bl ++ pr_binders_def2 bl2, (match d with
      |	None -> mt()
      |	Some t -> spc() ++ str":" ++ pr_constrarg t) , Some (pr_reduce red ++ pr_constr a))
      |	_ -> (pr_binders_def bl , (match d with
      |	None -> mt()
      |	Some t -> spc() ++ str":" ++ pr_constrarg t) , Some (pr_reduce red ++ pr_constr c)))
    | ProveBody (bl,t) -> (pr_binders_def bl , pr_constrarg t , None)
 in let (binds,typ,c) = pr_def_body b
 in h 0 (pr_def_token e ++ spc() ++ pr_id id ++ binds ++ typ ++ (match c with
 | None -> mt()
 | Some cc -> spc() ++ str":=" ++ spc() ++ cc))
  | VernacStartTheoremProof (ki,id,(bl,c),b,d) -> hov 1 (pr_thm_token ki ++ spc() ++ pr_id id ++ spc() ++ (match bl with | [] -> mt() | _ -> pr_binders pr_constr bl ++ spc()) ++ str":" ++ spc() ++ pr_constr c)
  | VernacEndProof (opac,o) -> (match o with
    | None -> if opac then str"Qed" else str"Defined"
    | Some (id,th) -> (match th with
      |	None -> (if opac then str"Save" else str"Defined") ++ spc() ++ pr_id id
      |	Some tok -> str"Save" ++ spc() ++ pr_thm_token tok ++ spc() ++ pr_id id)) 
  | VernacExactProof c -> str"Proof" ++ pr_constrarg c
  | VernacAssumption (stre,l) -> hov 1 (pr_assumption_token stre ++ spc() ++ pr_ne_params_list pr_constr l)
  | VernacInductive (f,l) -> let pr_constructor (coe,(id,c)) = pr_id id ++ spc() ++ (if coe then str":>" else str":") ++ pr_constrarg c in
    let pr_constructor_list l = match l with
    | [] -> mt()
    | _ -> fnl() ++ str"| " ++ prlist_with_sep (fun _ -> fnl() ++ str"| ") pr_constructor l in
    let pr_simple_binder (s,t) = pr_id s ++ str":" ++ pr_constr t in 
    let pr_ne_simple_binders = function
      |	[] -> mt()
      |	_ as l -> str"(" ++ prlist_with_sep (fun _ -> str") (") pr_simple_binder l ++ str")" ++ spc() in      
    let pr_oneind (id,indpar,s,lc) = pr_id id ++ spc() ++ pr_ne_simple_binders indpar ++ str":" ++ spc() ++ pr_constr s ++ spc() ++ str":=" ++ pr_constructor_list lc 
  in hov 1 ((if f then str"Inductive" else str"CoInductive") ++ spc() ++ prlist_with_sep (fun _ -> brk(1,1) ++ str"with ") pr_oneind l)
  | VernacFixpoint recs -> let pr_fixbinder (l,c) = prlist_with_sep (fun _ -> str",") (pr_located pr_name) l ++ str":" ++ pr_constr c in   
    let pr_fixbinders l = str"[" ++ prlist_with_sep (fun _ -> str";") pr_fixbinder l ++ str"]" in
    let pr_onerec = function
      |	(id,_,CProdN(_,bl,type_),CLambdaN(_,_,def)) -> pr_id id ++ spc() ++ pr_fixbinders bl ++ spc() ++ str":" ++ spc() ++ pr_constr type_ ++ spc() ++ str":=" ++ spc() ++ pr_constr def 
      |	_ -> mt()
    in hov 1 (str"Fixpoint" ++ spc() ++ prlist_with_sep (fun _ -> brk(1,1) ++ str"with ") pr_onerec recs)  
  | VernacCoFixpoint corecs -> let pr_onecorec (id,c,def) = pr_id id ++ spc() ++ str":" ++ pr_constrarg c ++ spc() ++ str":=" ++ pr_constrarg def      
    in hov 1 (str"CoFixpoint" ++ spc() ++ prlist_with_sep (fun _ -> brk(1,1) ++ str"with ") pr_onecorec corecs)  
  | VernacScheme l -> hov 1 (str"Scheme" ++ spc() ++ prlist_with_sep (fun _ -> brk(1,1) ++ str"with") pr_onescheme l)

  (* Gallina extensions *)
  | VernacRecord ((oc,name),ps,s,c,fs) -> let pr_simple_binder (s,t) = pr_id s ++ str":" ++ pr_constr t in 
    let pr_record_field = function
      |	(oc,AssumExpr (id,t)) -> pr_id id ++ spc() ++ if oc then str":>" else str":" ++ spc() ++ pr_constr t
      |	(oc,DefExpr(id,b,opt)) -> (match opt with
	| Some t -> pr_id id ++ spc() ++ if oc then str":>" else str":" ++ spc() ++ pr_constr t ++ spc() ++ str":=" ++ pr_constr b
	| None -> pr_id id ++ spc() ++ str":=" ++ pr_constr b) in
    hov 1 (str"Record" ++ if oc then str" > " else spc() ++ pr_id name ++ spc() ++ (match ps with
    | [] -> mt()
    | _ as l -> str"[" ++ prlist_with_sep (fun _ -> str";") pr_simple_binder l ++ str"]") ++ spc() ++ str":" ++ spc() ++ (* pr_sort s *) str"TODO" ++ spc() ++ str":=" ++ (match c with
      |	None -> mt()
      |	Some sc -> pr_id sc) ++ spc() ++ str"{" ++ cut() ++ prlist_with_sep (fun _ -> str";" ++ brk(1,1)) pr_record_field fs ++ str"}")
  | VernacBeginSection id -> h 0 (str"Section" ++ spc () ++ pr_id id)
  | VernacEndSegment id -> h 0 (str"End" ++ spc() ++ pr_id id)
  | VernacRequire (exp,spe,l) -> h 0 ((match exp with
    | None -> str"Read Module"
    | Some export -> str"Require" ++ if export then spc() ++ str"Export" else mt ()) ++ spc() ++  
      (match spe with
      |	None -> mt()
      |	Some flag -> (if flag then str"Specification" else str"Implementation") ++ spc ()) ++
	prlist_with_sep sep pr_reference l)
  | VernacImport (f,l) -> if f then str"Export" else str"Import" ++ spc() ++ prlist_with_sep sep pr_reference l
  | VernacCanonical q -> str"Canonical Structure" ++ spc() ++ pr_reference q
  | VernacCoercion (s,id,c1,c2) -> hov 1 (str"Coercion" ++ (match s with | Decl_kinds.Local -> spc() ++ str"Local" ++ spc() | Decl_kinds.Global -> spc()) ++ pr_reference id ++ spc() ++ str":" ++ spc() ++ pr_class_rawexpr c1 ++ spc() ++ str">->" ++ spc() ++ pr_class_rawexpr c2)
  | VernacIdentityCoercion (s,id,c1,c2) -> hov 1 (str"Identity Coercion" ++ (match s with | Decl_kinds.Local -> spc() ++ str"Local" ++ spc() | Decl_kinds.Global -> spc()) ++ pr_id id ++ spc() ++ str":" ++ spc() ++ pr_class_rawexpr c1 ++ spc() ++ str">->" ++ spc() ++ pr_class_rawexpr c2)

  (* Modules and Module Types *)
  | VernacDeclareModule (id,l,m1,m2) -> hov 1 (str"Module" ++ spc() ++ pr_id id ++ spc() ++ pr_module_binders_list l pr_constr ++ (match m1 with
    | None -> mt()
    | Some n1 -> str" : " ++ str"TODO" (* pr_module_type pr_constr n1 *) ) ++ (match m2 with
      | None -> mt()
      | Some n2 -> str" := " ++ pr_module_expr n2))
  | VernacDeclareModuleType (id,l,m) -> hov 1 (str"Module Type" ++ spc() ++ pr_id id ++ spc() ++ pr_module_binders_list l pr_constr ++ (match m with
    | None -> mt()
    | Some n -> str" := " ++ pr_module_type pr_constr n))

  (* Solving *)
  | VernacSolve (i,tac,_) -> pr_raw_tactic tac (* A Verifier *)
  | VernacSolveExistential (i,c) -> str"Existential" ++ spc() ++ int i ++ pr_constrarg c

  (* Auxiliary file and library management *)
  | VernacRequireFrom (exp,spe,f) -> h 0 (str"Require" ++ if exp then spc() ++ str"Export" ++ spc() else spc() ++ (match spe with
    | None -> mt()
    | Some false -> str"Implementation" ++ spc()
    | Some true -> str"Specification" ++ spc ()) ++ qs f)
  | VernacAddLoadPath (fl,s,d) -> hov 1 (str"Add" ++ if fl then str" Rec " else spc() ++ str"LoadPath" ++ spc() ++ qs s ++ (match d with 
    | None -> mt()
    | Some dir -> spc() ++ str"as" ++ spc() ++ pr_dirpath dir)) 
  | VernacRemoveLoadPath s -> str"Remove LoadPath" ++ qs s
  | VernacAddMLPath (fl,s) -> str"Add" ++ if fl then str" Rec " else spc() ++ str"ML Path" ++ qs s
  | VernacDeclareMLModule l -> hov 1 (str"Declare ML Module" ++ spc() ++ prlist_with_sep sep qs l)
  | VernacChdir s -> str"Cd" ++ pr_opt qs s

  (* Commands *)
  | VernacDeclareTacticDefinition (_,l) -> (match l with
    | [] -> mt()
    | [(id,b)] -> hov 1 (str"Tactic Definition" ++ spc() ++ pr_located pr_id id ++ spc() ++ str":=" ++ spc() ++ pr_raw_tactic b)
    | _ as t -> let pr_vrec_clause (id,b) = pr_located pr_id id ++ spc() ++ str":=" ++ spc() ++ pr_raw_tactic b in hov 1 (str"Recursive Tactic Definition" ++ spc() ++ prlist_with_sep (fun _ -> brk(1,1) ++ str"And") pr_vrec_clause t))
  | VernacHints (dbnames,h) -> pr_hints dbnames h pr_constr
  | VernacHintDestruct (id,loc,c,i,tac) -> hov 1 (str"HintDestruct" ++ spc() ++ pr_destruct_location loc ++ spc() ++ pr_id id ++ pr_constrarg c ++ pr_intarg i ++ spc() ++ str"[" ++ pr_raw_tactic tac ++ str"]")
  | VernacSyntacticDefinition (id,c,None) -> hov 1 (str"Syntactic Definition" ++ spc() ++ pr_id id ++ spc() ++ str":=" ++ pr_constrarg c)
  | VernacSyntacticDefinition (id,c,Some n) -> hov 1 (str"Syntactic Definition" ++ spc() ++ pr_id id ++ spc() ++ str":=" ++ pr_constrarg c ++ spc() ++ str"|" ++ int n)
  | VernacDeclareImplicits (q,None) -> hov 1 (str"Implicits" ++ spc() ++ pr_reference q)
  | VernacDeclareImplicits (q,Some l) -> hov 1 (str"Implicits" ++ spc() ++ pr_reference q ++ spc() ++ str"[" ++ prlist_with_sep sep int l ++ str"]")
  | VernacSetOpacity (fl,l) -> hov 1 (if fl then str"Opaque" else str"Transparent" ++ spc() ++ prlist_with_sep sep pr_reference l)
  | VernacUnsetOption na -> hov 1 (str"Unset" ++ spc() ++ pr_printoption na None)
  | VernacSetOption (Goptions.SecondaryTable ("Implicit","Arguments"),BoolValue true) -> str"Set Implicit Arguments"
  | VernacSetOption (Goptions.SecondaryTable ("Implicit","Arguments"),BoolValue false) -> str"Unset Implicit Arguments"
  | VernacSetOption (na,v) -> hov 1 (str"Set" ++ spc() ++ pr_set_option na v)
  | VernacAddOption (na,l) -> hov 1 (str"Add" ++ spc() ++ pr_printoption na (Some l))
  | VernacRemoveOption (na,l) -> hov 1 (str"Remove" ++ spc() ++ pr_printoption na (Some l))
  | VernacMemOption (na,l) -> hov 1 (str"Test" ++ spc() ++ pr_printoption na (Some l))
  | VernacPrintOption na -> hov 1 (str"Test" ++ spc() ++ pr_printoption na None)
  | VernacCheckMayEval (r,io,c) -> 
      let pr_mayeval r c = match r with 
      | Some r0 -> h 0 (str"Eval" ++ spc() ++ pr_red_expr (pr_constr,fun _ -> str"TODO" (*pr_metanum pr_reference *)) r0 ++ spc() ++ str"in" ++ spc () ++ pr_constr c)
      | None -> h 0 (str"Check" ++ spc() ++ pr_constr c) 
      in pr_mayeval r c
  | VernacGlobalCheck c -> hov 1 (str"Type" ++ pr_constrarg c)
  | VernacPrint p -> 
      let pr_printable = function
	| PrintFullContext -> str"Print All"
	| PrintSectionContext s -> str"Print Section" ++ spc() ++ pr_reference s
	| PrintGrammar (uni,ent) -> str"Print Grammar" ++ spc() ++ str uni ++ spc() ++ str ent
	| PrintLoadPath -> str"Print LoadPath"
	| PrintModules -> str"Print Modules"
	| PrintMLLoadPath -> str"Print ML Path"
	| PrintMLModules -> str"Print ML Modules"
	| PrintGraph -> str"Print Graph"
	| PrintClasses -> str"Print Classes"
	| PrintCoercions -> str"Print Coercions"
	| PrintCoercionPaths (s,t) -> str"Print Coercion Paths" ++ spc() ++ pr_class_rawexpr s ++ spc() ++ pr_class_rawexpr t
	| PrintTables -> str"Print Tables"
	| PrintOpaqueName qid -> str"Print Proof" ++ spc() ++ pr_reference qid
	| PrintHintGoal -> str"Print Hint"
	| PrintHint qid -> str"Print Hint" ++ spc() ++ pr_reference qid
	| PrintHintDb -> str"Print Hint *"
	| PrintHintDbName s -> str"Print HintDb" ++ spc() ++ str s
	| PrintUniverses fopt -> str"Dump Universes" ++ pr_opt str fopt
	| PrintName qid -> str"Print" ++ spc()  ++ pr_reference qid
	| PrintLocalContext -> str"Print"
	| PrintModuleType qid -> str"Print Module Type" ++ spc() ++ pr_reference qid
	| PrintModule qid -> str"Print Module" ++ spc() ++ pr_reference qid
	| PrintInspect n -> str"Inspect" ++ spc() ++ int n
	| PrintScope s -> str"Scope" ++ spc() ++ str s 
      in pr_printable p
  | VernacSearch (sea,sea_r) -> pr_search sea sea_r pr_constr
  | VernacLocate loc -> 
      let pr_locate =function
	| LocateTerm qid ->  pr_reference qid
	| LocateFile f -> str"File" ++ spc() ++ qs f
	| LocateLibrary qid -> str"Library" ++ spc () ++ pr_reference qid
      in str"Locate" ++ spc() ++ pr_locate loc
  | VernacComments l -> hov 1 (str"Comments" ++ spc() ++ prlist_with_sep sep (pr_comment pr_constr) l)
  | VernacNop -> str"Proof"
  
  (* Toplevel control *)
  | VernacToplevelControl exn -> pr_topcmd exn

  (* For extension *)
  | VernacExtend (s,c) -> hov 1 (str s ++ prlist_with_sep sep pr_constrarg (List.map (Genarg.out_gen Genarg.rawwit_constr) c))
  | VernacV7only _ | VernacV8only _ -> mt ()
  | VernacProof _ | VernacDefineModule _ -> str"TODO"
in pr_vernac

let pr_vernac = make_pr_vernac (Ppconstrnew.pr_constr)

