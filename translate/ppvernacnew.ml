(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
open Decl_kinds
open Tacinterp

let pr_spc_type = pr_sep_com spc pr_type

let pr_lident (b,_ as loc,id) =
  if loc <> dummy_loc then
    pr_located pr_id ((b,b+String.length(string_of_id id)),id)
  else pr_id id

let pr_lname = function
    (loc,Name id) -> pr_lident (loc,id)
  | lna -> pr_located pr_name lna

let pr_ltac_id id = Nameops.pr_id (id_of_ltac_v7_id id)

let pr_module r =
  let update_ref s = match r with
    | Ident (loc,_) ->
        Ident (loc,id_of_string s)
    | Qualid (loc,qid) ->
        Qualid (loc,make_qualid (fst (repr_qualid qid)) (id_of_string s)) in
  let (_,dir,_) =
    try
      Library.locate_qualified_library (snd (qualid_of_reference r))
    with _ -> 
      errorlabstrm "" (str"Translator cannot find " ++ Libnames.pr_reference r)
  in
  let r = match List.rev (List.map string_of_id (repr_dirpath dir)) with
    | [ "Coq"; "Lists"; "List" ] -> update_ref "MonoList"
    | [ "Coq"; "Lists"; "PolyList" ] -> update_ref "List"
    | _ -> r in
  Libnames.pr_reference r

let pr_import_module =
  (* We assume List is never imported with "Import" ... *)
  Libnames.pr_reference

let pr_reference = Ppconstrnew.pr_reference

let sep_end () = str"."

(* Warning: [pr_raw_tactic] globalises and fails if globalisation fails *)
(*
let pr_raw_tactic_env l env t = 
  Pptacticnew.pr_raw_tactic env t
*)
let pr_raw_tactic_env l env t = 
  Pptacticnew.pr_glob_tactic env (Tacinterp.glob_tactic_env l env t)

let pr_gen env t =
  Pptactic.pr_raw_generic (Ppconstrnew.pr_constr_env env)
    (Ppconstrnew.pr_lconstr_env env)
    (Pptacticnew.pr_raw_tactic env) pr_reference t

let pr_raw_tactic tac =
  pr_raw_tactic_env [] (Global.env()) tac

let rec extract_signature = function
  | [] -> []
  | Egrammar.TacNonTerm (_,(_,t),_) :: l -> t :: extract_signature l
  | _::l -> extract_signature l

let rec match_vernac_rule tys = function
    [] -> raise Not_found
  | (s,pargs)::rls ->
      if extract_signature pargs = tys then (s,pargs)
      else match_vernac_rule tys rls

let sep = fun _ -> spc()
let sep_p = fun _ -> str"."
let sep_v = fun _ -> str","
let sep_v2 = fun _ -> str"," ++ spc()
let sep_pp = fun _ -> str":"

let pr_ne_sep sep pr = function
    [] -> mt()
  | l -> sep() ++ pr l

let pr_entry_prec = function
  | Some Gramext.LeftA -> str"LEFTA "
  | Some Gramext.RightA -> str"RIGHTA "
  | Some Gramext.NonA -> str"NONA "
  | None -> mt()

let pr_prec = function
  | Some Gramext.LeftA -> str", left associativity"
  | Some Gramext.RightA -> str", right associativity"
  | Some Gramext.NonA -> str", no associativity"
  | None -> mt()

let pr_set_entry_type = function
  | ETIdent -> str"ident"
  | ETReference -> str"global"
  | ETPattern -> str"pattern"
  | ETConstr _ -> str"constr"
  | ETOther (_,e) -> str e
  | ETBigint -> str "bigint"
  | ETConstrList _ -> failwith "Internal entry type"

let pr_non_terminal = function
  | NtQual (u,nt) -> (* no more qualified entries *) str nt
  | NtShort "constrarg" -> str "constr"
  | NtShort nt -> str nt

let strip_meta id =
  let s = string_of_id id in
  if s.[0]='$' then id_of_string (String.sub s 1 (String.length s - 1))
  else id

let pr_production_item = function
  | VNonTerm (loc,nt,Some p) -> pr_non_terminal nt ++ str"(" ++ pr_id (strip_meta p) ++ str")"
  | VNonTerm (loc,nt,None) -> pr_non_terminal nt
  | VTerm s -> qsnew s

let pr_comment pr_c = function
  | CommentConstr c -> pr_c c
  | CommentString s -> qsnew s
  | CommentInt n -> int n

let pr_in_out_modules = function
  | SearchInside l -> spc() ++ str"inside" ++ spc() ++ prlist_with_sep sep pr_module l
  | SearchOutside [] -> mt()
  | SearchOutside l -> spc() ++ str"outside" ++ spc() ++ prlist_with_sep sep pr_module l

let pr_search_about = function
  | SearchRef r -> pr_reference r
  | SearchString s -> qsnew s

let pr_search a b pr_p = match a with
  | SearchHead qid -> str"Search" ++ spc() ++ pr_reference qid ++ pr_in_out_modules b
  | SearchPattern c -> str"SearchPattern" ++ spc() ++ pr_p c ++ pr_in_out_modules b
  | SearchRewrite c -> str"SearchRewrite" ++ spc() ++ pr_p c ++ pr_in_out_modules b
  | SearchAbout sl -> str"SearchAbout" ++ spc() ++ str "[" ++ prlist_with_sep spc pr_search_about sl ++ str "]" ++ pr_in_out_modules b

let pr_locality local = if local then str "Local " else str ""

let pr_explanation imps = function
  | ExplByPos n -> pr_id (Impargs.name_of_implicit (List.nth imps (n-1)))
  | ExplByName id -> pr_id id

let pr_class_rawexpr = function
  | FunClass -> str"Funclass"
  | SortClass -> str"Sortclass"
  | RefClass qid -> pr_reference qid

let pr_option_ref_value = function
  | QualidRefValue id -> pr_reference id
  | StringRefValue s -> qsnew s

let pr_printoption a b = match a with
  | Goptions.PrimaryTable table -> str table ++ pr_opt (prlist_with_sep sep pr_option_ref_value) b
  | Goptions.SecondaryTable (table,field) -> str table ++ spc() ++ str field ++ pr_opt (prlist_with_sep sep pr_option_ref_value) b

let pr_set_option a b = 
  let pr_opt_value = function 
    | IntValue n -> spc() ++ int n
    | StringValue s -> spc() ++ str s
    | BoolValue b -> mt()
  in pr_printoption a None ++ pr_opt_value b

let pr_topcmd _ = str"(* <Warning> : No printer for toplevel commands *)"

let pr_destruct_location = function
  | Tacexpr.ConclLocation ()  -> str"Conclusion"
  | Tacexpr.HypLocation b -> if b then str"Discardable Hypothesis" else str"Hypothesis"

let pr_opt_hintbases l = match l with
  | [] -> mt()
  | _ as z -> str":" ++ spc() ++ prlist_with_sep sep str z

let pr_hints local db h pr_c pr_pat = 
  let opth = pr_opt_hintbases db  in
  let pr_aux = function
    | CAppExpl (_,(_,qid),[]) -> pr_reference qid
    | _ -> mt () in
  let pph =
    match h with
    | HintsResolve l ->
        str "Resolve " ++
        prlist_with_sep sep pr_c (List.map snd l)
    | HintsImmediate l ->
        str"Immediate" ++ spc() ++
        prlist_with_sep sep pr_c (List.map snd l)
    | HintsUnfold l ->
        str "Unfold " ++
	prlist_with_sep sep pr_reference (List.map snd l)
    | HintsConstructors (n,c) ->
        str"Constructors" ++ spc() ++
        prlist_with_sep spc pr_reference c
    | HintsExtern (name,n,c,tac) ->
        str "Extern" ++ spc() ++ int n ++ spc() ++ pr_pat c ++ str" =>" ++
        spc() ++ pr_raw_tactic tac
    | HintsDestruct(name,i,loc,c,tac) ->
        str "Destruct " ++ pr_id name ++ str" :=" ++ spc() ++
        hov 0 (int i ++ spc() ++ pr_destruct_location loc ++ spc() ++
               pr_c c ++ str " =>") ++ spc() ++
        pr_raw_tactic tac in
  hov 2 (str"Hint "++pr_locality local ++ pph ++ opth)

let pr_with_declaration pr_c = function
  | CWith_Definition (id,c) ->
      let p = pr_c c in
      str"Definition" ++ spc() ++ pr_lident id ++ str" := " ++ p
  | CWith_Module (id,qid) ->
      str"Module" ++ spc() ++ pr_lident id ++ str" := " ++
      pr_located pr_qualid qid

let rec pr_module_type pr_c = function
  | CMTEident qid -> spc () ++ pr_located pr_qualid qid
  | CMTEwith (mty,decl) ->
      let m = pr_module_type pr_c mty in
      let p = pr_with_declaration pr_c decl in
      m ++ spc() ++ str"with" ++ spc() ++ p

let pr_of_module_type prc (mty,b) =
  str (if b then ":" else "<:") ++
  pr_module_type prc mty

let pr_module_vardecls pr_c (idl,mty) =
  let m = pr_module_type pr_c mty in
  (* Update the Nametab for interpreting the body of module/modtype *)
  let lib_dir = Lib.library_dp() in
  List.iter (fun (_,id) ->
    Declaremods.process_module_bindings [id]
      [make_mbid lib_dir (string_of_id id),
       Modintern.interp_modtype (Global.env()) mty]) idl;
  (* Builds the stream *)
  spc() ++
  hov 1 (str"(" ++ prlist_with_sep spc pr_lident idl ++ str":" ++ m ++ str")")

let pr_module_binders l pr_c = 
  (* Effet de bord complexe pour garantir la declaration des noms des
  modules parametres dans la Nametab des l'appel de pr_module_binders
  malgre l'aspect paresseux des streams *)
  let ml = List.map (pr_module_vardecls pr_c) l in
  prlist (fun id -> id) ml

let pr_module_binders_list l pr_c = pr_module_binders l pr_c

let rec pr_module_expr = function
  | CMEident qid -> pr_located pr_qualid qid
  | CMEapply (me1,(CMEident _ as me2)) ->
      pr_module_expr me1 ++ spc() ++ pr_module_expr me2
  | CMEapply (me1,me2) ->
      pr_module_expr me1 ++ spc() ++
      hov 1 (str"(" ++ pr_module_expr me2 ++ str")")

(*
let pr_opt_casted_constr pr_c = function
  | CCast (loc,c,t) -> pr_c c ++ str":" ++ pr_c t
  | _ as c -> pr_c c
*)

let pr_type_option pr_c = function
  | CHole loc -> mt()
  | _ as c -> brk(0,2) ++ str":" ++ pr_c c

let without_translation f x =
  let old = Options.do_translate () in
  let oldv7 = !Options.v7 in
  Options.make_translate false;
  try let r = f x in Options.make_translate old; Options.v7:=oldv7; r
  with e -> Options.make_translate old; Options.v7:=oldv7; raise e

let pr_decl_notation prc =
  pr_opt (fun (ntn,c,scopt) -> fnl () ++
    str "where " ++ qsnew ntn ++ str " := " ++ without_translation prc c ++
    pr_opt (fun sc -> str ": " ++ str sc) scopt)

let pr_vbinders l =
  hv 0 (pr_binders l)

let pr_binders_arg =
  pr_ne_sep spc pr_binders

let pr_and_type_binders_arg bl =
  let bl, _ = pr_lconstr_env_n (Global.env()) false bl (CHole dummy_loc) in
  pr_binders_arg bl

let pr_onescheme (id,dep,ind,s) =
  hov 0 (pr_lident id ++ str" :=") ++ spc() ++
  hov 0 ((if dep then str"Induction for" else str"Minimality for")
  ++ spc() ++ pr_reference ind) ++ spc() ++ 
  hov 0 (str"Sort" ++ spc() ++ pr_sort s)

let begin_of_inductive = function
    [] -> 0
  | (_,(((b,_),_),_))::_ -> b

let pr_class_rawexpr = function
  | FunClass -> str"Funclass"
  | SortClass -> str"Sortclass"
  | RefClass qid -> pr_reference qid

let pr_assumption_token many = function
  | (Local,Logical) ->
      str (if many then "Hypotheses" else "Hypothesis")
  | (Local,Definitional) ->
      str (if many then "Variables" else "Variable")
  | (Global,Logical) ->
      str (if many then "Axioms" else "Axiom")
  | (Global,Definitional) -> 
      str (if many then "Parameters" else "Parameter")
  | (Global,Conjectural) -> str"Conjecture"
  | (Local,Conjectural) -> 
      anomaly "Don't know how to translate a local conjecture"

let pr_params pr_c (xl,(c,t)) =
  hov 2 (prlist_with_sep sep pr_lident xl ++ spc() ++
         (if c then str":>" else str":" ++
         spc() ++ pr_c t))

let rec factorize = function
  | [] -> []
  | (c,(idl,t))::l ->
      match factorize l with
	| (xl,t')::l' when t' = (c,t) -> (idl@xl,t')::l'
	| l' -> (idl,(c,t))::l'

let pr_ne_params_list pr_c l =
  match factorize l with
    | [p] -> pr_params pr_c p
    | l ->
	prlist_with_sep spc
          (fun p -> hov 1 (str "(" ++ pr_params pr_c p ++ str ")")) l
(*
  prlist_with_sep pr_semicolon (pr_params pr_c)
*)

let pr_thm_token = function
  | Theorem -> str"Theorem"
  | Lemma -> str"Lemma"
  | Fact -> str"Fact"
  | Remark -> str"Remark"

let pr_require_token = function
  | Some true -> str " Export"
  | Some false -> str " Import"
  | None -> mt()

let pr_syntax_modifier = function
  | SetItemLevel (l,NextLevel) ->
      prlist_with_sep sep_v2 str l ++
      spc() ++ str"at next level"
  | SetItemLevel (l,NumLevel n) ->
      prlist_with_sep sep_v2 str l ++
      spc() ++ str"at level" ++ spc() ++ int n
  | SetLevel n -> str"at level" ++ spc() ++ int n
  | SetAssoc Gramext.LeftA -> str"left associativity"
  | SetAssoc Gramext.RightA -> str"right associativity"
  | SetAssoc Gramext.NonA -> str"no associativity"
  | SetEntryType (x,typ) -> str x ++ spc() ++ pr_set_entry_type typ
  | SetOnlyParsing -> str"only parsing"
  | SetFormat s -> str"format " ++ pr_located qsnew s

let pr_syntax_modifiers = function
  | [] -> mt()
  | l -> spc() ++ 
      hov 1 (str"(" ++ prlist_with_sep sep_v2 pr_syntax_modifier l ++ str")")

let pr_grammar_tactic_rule (name,(s,pil),t) =
(*
  hov 0 (
  (* str name ++ spc() ++ *)
  hov 0 (str"[" ++ qsnew s ++ spc() ++
  prlist_with_sep sep pr_production_item pil ++ str"]") ++
  spc() ++ hov 0 (str"->" ++ spc() ++ str"[" ++ pr_raw_tactic t ++ str"]"))
*)
  hov 2 (str "Tactic Notation" ++ spc() ++ 
    hov 0 (qsnew s ++ spc() ++ prlist_with_sep sep pr_production_item pil ++
    spc() ++ str":=" ++ spc() ++ pr_raw_tactic t))

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
  | Some pprim,Any -> qsnew pprim
  | Some pprim,Prec p -> qsnew pprim ++ spc() ++ str":" ++ spc() ++ int p
  | _ -> mt()

let rec pr_next_hunks = function 
  | UNP_FNL -> str"FNL"
  | UNP_TAB -> str"TAB"
  | RO c -> qsnew c
  | UNP_BOX (b,ll) -> str"[" ++ pr_box b ++ prlist_with_sep sep pr_next_hunks ll ++ str"]"
  | UNP_BRK (n,m) -> str"[" ++ int n ++ spc() ++ int m ++ str"]"
  | UNP_TBRK (n,m) -> str"[ TBRK" ++ int n ++ spc() ++ int m ++ str"]"
  | PH (e,None,_) -> print_ast e
  | PH (e,Some ext,pr) -> print_ast e ++ spc() ++ str":" ++ spc() ++ pr_paren_reln_or_extern (Some ext,pr)
  | UNP_SYMBOLIC _ -> mt()

let pr_unparsing u =
  str "[ " ++ prlist_with_sep sep pr_next_hunks u ++ str " ]"

let pr_astpat a = str"<<" ++ print_ast a ++ str">>"

let pr_syntax_rule (nm,s,u) = str nm ++ spc() ++ str"[" ++ pr_astpat s ++ str"]" ++ spc() ++ str"->" ++ spc() ++ pr_unparsing u

let pr_syntax_entry (p,rl) =
  str"level" ++ spc() ++ int p ++ str" :" ++ fnl() ++
  prlist_with_sep (fun _ -> fnl() ++ str"| ") pr_syntax_rule rl

let pr_vernac_solve (i,env,tac,deftac) =
  (if i = 1 then mt() else int i ++ str ": ") ++
  Pptacticnew.pr_glob_tactic env tac
  ++ (try if deftac & Pfedit.get_end_tac() <> None then str ".." else mt ()
      with UserError _|Stdpp.Exc_located _ -> mt())

(**************************************)
(* Pretty printer for vernac commands *)
(**************************************)
let make_pr_vernac pr_constr pr_lconstr =

let pr_constrarg c = spc () ++ pr_constr c in
let pr_lconstrarg c = spc () ++ pr_lconstr c in
let pr_intarg n = spc () ++ int n in

let rec pr_vernac = function
  
  (* Proof management *)
  | VernacAbortAll -> str "Abort All"
  | VernacRestart -> str"Restart"
  | VernacSuspend -> str"Suspend"
  | VernacUnfocus -> str"Unfocus"
  | VernacGoal c -> str"Goal" ++ pr_lconstrarg c
  | VernacAbort id -> str"Abort" ++ pr_opt pr_lident id
  | VernacResume id -> str"Resume" ++ pr_opt pr_lident id
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
	| ShowGoalImplicitly n -> str"Show Implicit Arguments" ++ pr_opt int n
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
  | VernacResetName id -> str"Reset" ++ spc() ++ pr_lident id
  | VernacResetInitial -> str"Reset Initial"
  | VernacBack i -> if i=1 then str"Back" else str"Back" ++ pr_intarg i

  (* State management *)
  | VernacWriteState s -> str"Write State" ++ spc () ++ qsnew s
  | VernacRestoreState s -> str"Restore State" ++ spc() ++ qsnew s

  (* Control *)
  | VernacList l ->
      hov 2 (str"[" ++ spc() ++
             prlist (fun v -> pr_located pr_vernac v ++ sep_end () ++ fnl()) l
             ++ spc() ++ str"]") 
  | VernacLoad (f,s) -> str"Load" ++ if f then (spc() ++ str"Verbose"
  ++ spc()) else spc()  ++ qsnew s
  | VernacTime v -> str"Time" ++ spc() ++ pr_vernac v
  | VernacVar id -> pr_lident id
  
  (* Syntax *) 
  | VernacGrammar _ -> 
      msgerrnl (str"Warning : constr Grammar is discontinued; use Notation");
      str"(* <Warning> : Grammar is replaced by Notation *)"
  | VernacTacticGrammar l ->
      prlist_with_sep (fun () -> sep_end() ++ fnl()) pr_grammar_tactic_rule l
(*
      hov 1 (str"Grammar tactic simple_tactic :=" ++ spc() ++ prlist_with_sep (fun _ -> brk(1,1) ++ str"|") pr_grammar_tactic_rule l) (***)
*)      
  | VernacSyntax (u,el) ->
      msgerrnl (str"Warning : Syntax is discontinued; use Notation");
      str"(* <Warning> : Syntax is discontinued" ++ 
(*
      fnl () ++
      hov 1 (str"Syntax " ++ str u ++ spc() ++
      prlist_with_sep sep_v2 pr_syntax_entry el) ++ 
*)
      str " *)"
  | VernacOpenCloseScope (local,opening,sc) ->
      str (if opening then "Open " else "Close ") ++ pr_locality local ++
      str "Scope" ++ spc() ++ str sc
  | VernacDelimiters (sc,key) ->
      str"Delimit Scope" ++ spc () ++ str sc ++
      spc() ++ str "with " ++ str key
  | VernacBindScope (sc,cll) ->
      str"Bind Scope" ++ spc () ++ str sc ++
      spc() ++ str "with " ++ prlist_with_sep spc pr_class_rawexpr cll
  | VernacArgumentsScope (q,scl) -> let pr_opt_scope = function 
      |	None -> str"_"
      |	Some sc -> str sc in 
    str"Arguments Scope" ++ spc() ++ pr_reference q ++ spc() ++ str"[" ++ prlist_with_sep sep pr_opt_scope scl ++ str"]"
  | VernacInfix (local,(s,_),q,ov8,sn) -> (* A Verifier *)
      let s,mv8 = match ov8 with Some smv8 -> smv8 | None -> (s,[]) in
      hov 0 (hov 0 (str"Infix " ++ pr_locality local
      ++ qsnew s ++ str " :=" ++ spc() ++ pr_reference q) ++
      pr_syntax_modifiers mv8 ++
      (match sn with
    | None -> mt()
    | Some sc -> spc() ++ str":" ++ spc() ++ str sc))
  | VernacDistfix (local,a,p,s,q,sn) ->
      hov 0 (str"Distfix " ++ pr_locality local ++ pr_entry_prec a ++ int p
        ++ spc() ++ qsnew s ++ spc() ++ pr_reference q ++ (match sn with
    | None -> mt()
    | Some sc -> spc() ++ str":" ++ spc() ++ str sc))
  | VernacNotation (local,c,sl,mv8,opt) ->
      let (s,l) = match mv8 with
          None -> fst (out_some sl), []
        | Some ml -> ml in
      let ps =
	let n = String.length s in
	if n > 2 & s.[0] = '\'' & s.[n-1] = '\'' 
	then
          let s' = String.sub s 1 (n-2) in
          if String.contains s' '\'' then qsnew s else str s'
	else qsnew s in
      hov 2( str"Notation" ++ spc() ++ pr_locality local ++ ps ++
      str " :=" ++ pr_constrarg c ++ pr_syntax_modifiers l ++
      (match opt with
        | None -> mt()
        | Some sc -> str" :" ++ spc() ++ str sc))
  | VernacSyntaxExtension (local,sl,mv8) ->
      let (s,l) = match mv8 with
          None -> out_some sl
        | Some ml -> ml in
      str"Reserved Notation" ++ spc() ++ pr_locality local ++ qsnew s ++
      pr_syntax_modifiers l

  (* Gallina *)
  | VernacDefinition (d,id,b,f) -> (* A verifier... *)
      let pr_def_token = function
        | Local, Coercion -> str"Coercion Local"
        | Global, Coercion -> str"Coercion"
        | Local, Definition -> str"Let"
        | Global, Definition -> str"Definition"
        | Local, SubClass -> str"Local SubClass"
        | Global, SubClass -> str"SubClass"
        | Global, CanonicalStructure -> str"Canonical Structure"
        | Local, CanonicalStructure ->
	   anomaly "Don't know how to translate a local canonical structure" in
      let pr_reduce = function
        | None -> mt()
        | Some r ->
            str"Eval" ++ spc() ++
            pr_red_expr (pr_constr, pr_lconstr, pr_reference) r ++
            str" in" ++ spc() in
      let mkLambdaCit = List.fold_right (fun (x,a) b -> mkLambdaC(x,a,b)) in
      let mkProdCit = List.fold_right (fun (x,a) b -> mkProdC(x,a,b)) in
      let pr_def_body = function
        | DefineBody (bl,red,c,d) ->
            let (bl2,body,ty) = match d with
              | None ->
                  let bl2,body = extract_lam_binders c in
                  (bl2,body,mt())
              | Some ty ->
                  let bl2,body,ty' = extract_def_binders c ty in
                  (bl2,CCast (dummy_loc,body,ty'),
                   spc() ++ str":" ++
                   pr_sep_com spc
                     (pr_type_env_n (Global.env()) (bl@bl2)) ty') in
	    let iscast = d <> None in
            let bindings,ppred =
	      pr_lconstr_env_n (Global.env()) iscast (bl@bl2) body in
            (pr_binders_arg bindings,ty,Some (pr_reduce red ++ ppred))
        | ProveBody (bl,t) ->
            (pr_and_type_binders_arg bl, str" :" ++ pr_spc_type t, None)
      in
      let (binds,typ,c) = pr_def_body b in
      hov 2 (pr_def_token d ++ spc() ++ pr_lident id ++ binds ++ typ ++
      (match c with
        | None -> mt()
        | Some cc -> str" :=" ++ spc() ++ cc))

  | VernacStartTheoremProof (ki,id,(bl,c),b,d) ->
      hov 1 (pr_thm_token ki ++ spc() ++ pr_lident id ++ spc() ++
      (match bl with
        | [] -> mt()
        | _ -> error "Statements with local binders no longer supported")
      ++ str":" ++ pr_spc_type (rename_bound_variables (snd id) c))
  | VernacEndProof Admitted -> str"Admitted"
  | VernacEndProof (Proved (opac,o)) -> (match o with
    | None -> if opac then str"Qed" else str"Defined"
    | Some (id,th) -> (match th with
      |	None -> (if opac then str"Save" else str"Defined") ++ spc() ++ pr_lident id
      |	Some tok -> str"Save" ++ spc() ++ pr_thm_token tok ++ spc() ++ pr_lident id)) 
  | VernacExactProof c ->
      hov 2 (str"Proof" ++ pr_lconstrarg c)
  | VernacAssumption (stre,l) ->
      hov 2
        (pr_assumption_token (List.length l > 1) stre ++ spc() ++ 
	 pr_ne_params_list pr_type l)
  | VernacInductive (f,l) ->

      (* Copie simplifiée de command.ml pour recalculer les implicites, *)
      (* les notations, et le contexte d'evaluation *)
      let lparams = match l with [] -> assert false | (_,_,la,_,_)::_ -> la in
      let nparams = local_binders_length lparams
      and sigma = Evd.empty 
      and env0 = Global.env() in
      let (env_params,params) =
	List.fold_left
	  (fun (env,params) d -> match d with
	    | LocalRawAssum (nal,t) ->
		let t = Constrintern.interp_type sigma env t in
		let ctx = list_map_i (fun i (_,na) -> (na,None,Term.lift i t)) 0 nal
		in let ctx = List.rev ctx in
		(Environ.push_rel_context ctx env, ctx@params)
	    | LocalRawDef ((_,na),c) ->
		let c = Constrintern.judgment_of_rawconstr sigma env c in
		let d = (na, Some c.Environ.uj_val, c.Environ.uj_type) in
		(Environ.push_rel d env,d::params))
	  (env0,[]) lparams in

      let (ind_env,ind_impls,arityl) =
        List.fold_left
          (fun (env, ind_impls, arl) ((_,recname), _, _, arityc, _) ->
            let arity = Constrintern.interp_type sigma env_params arityc in
	    let fullarity = Termops.it_mkProd_or_LetIn arity params in
	    let env' = Termops.push_rel_assum (Name recname,fullarity) env in
	    let impls = 
	      if Impargs.is_implicit_args()
	      then Impargs.compute_implicits false env_params fullarity
	      else [] in
	    (env', (recname,impls)::ind_impls, (arity::arl)))
          (env0, [], []) l
      in
      let lparnames = List.map (fun (na,_,_) -> na) params in
      let notations = 
	List.fold_right (fun (_,ntnopt,_,_,_) l ->option_cons ntnopt l) l [] in
      let ind_env_params = Environ.push_rel_context params ind_env in

      let lparnames = List.map (fun (na,_,_) -> na) params in
      let impl = List.map
	(fun ((_,recname),_,_,arityc,_) ->
	  let arity = Constrintern.interp_type sigma env_params arityc in
	  let fullarity =
            Termops.prod_it arity (List.map (fun (id,_,ty) -> (id,ty)) params)
	  in
	  let impl_in =
	    if Impargs.is_implicit_args()
	    then Impargs.compute_implicits false env_params fullarity
	    else [] in
	  let impl_out =
	    if Impargs.is_implicit_args_out()
	    then Impargs.compute_implicits true env_params fullarity
	    else [] in
	  (recname,impl_in,impl_out)) l in
      let impls_in = List.map (fun (id,a,_) -> (id,a)) impl in
      let impls_out = List.map (fun (id,_,a) -> (id,a)) impl in
      Constrintern.set_temporary_implicits_in impls_in;
      Constrextern.set_temporary_implicits_out impls_out;
      (* Fin calcul implicites *)

      let pr_constructor (coe,(id,c)) =
        hov 2 (pr_lident id ++ str" " ++
               (if coe then str":>" else str":") ++
                pr_sep_com spc (pr_type_env_n ind_env_params []) c) in
      let pr_constructor_list l = match l with
        | [] -> mt()
        | _ ->
            pr_com_at (begin_of_inductive l) ++
            fnl() ++
            str (if List.length l = 1 then "   " else " | ") ++
            prlist_with_sep (fun _ -> fnl() ++ str" | ") pr_constructor l in
      let pr_oneind key (id,ntn,indpar,s,lc) =
	hov 0 (
          str key ++ spc() ++
          pr_lident id ++ pr_and_type_binders_arg indpar ++ spc() ++ str":" ++ 
	  spc() ++ pr_type s ++ 
	  str" :=") ++ pr_constructor_list lc ++ 
	pr_decl_notation pr_constr ntn in

      (* Copie simplifiée de command.ml pour déclarer les notations locales *)
      List.iter (fun (df,c,scope) ->
 	Metasyntax.add_notation_interpretation df [] c scope) notations;

      hov 1 (pr_oneind (if f then "Inductive" else "CoInductive") (List.hd l))
      ++ 
      (prlist (fun ind -> fnl() ++ hov 1 (pr_oneind "with" ind)) (List.tl l))


  | VernacFixpoint recs ->

      (* Copie simplifiée de command.ml pour recalculer les implicites *)
      (* les notations, et le contexte d'evaluation *)
      let sigma = Evd.empty
      and env0 = Global.env() in
      let notations = 
	List.fold_right (fun (_,ntnopt) l -> option_cons ntnopt l) recs [] in
      let impl = List.map
        (fun ((recname,_, bl, arityc,_),_) -> 
          let arity =
            Constrintern.interp_type sigma env0
              (prod_constr_expr arityc bl) in
	  let impl_in =
	    if Impargs.is_implicit_args()
	    then Impargs.compute_implicits false env0 arity
	    else [] in
	  let impl_out =
	    if Impargs.is_implicit_args_out()
	    then Impargs.compute_implicits true env0 arity
	    else [] in
	  (recname,impl_in,impl_out)) recs in
      let impls_in = List.map (fun (id,a,_) -> (id,a)) impl in
      let impls_out = List.map (fun (id,_,a) -> (id,a)) impl in
      Constrintern.set_temporary_implicits_in impls_in;
      Constrextern.set_temporary_implicits_out impls_out;

      (* Copie simplifiée de command.ml pour déclarer les notations locales *)
      List.iter (fun (df,c,scope) ->
	Metasyntax.add_notation_interpretation df [] c None) notations;

      let rec_sign = 
        List.fold_left 
          (fun env ((recname,_,bl,arityc,_),_) -> 
            let arity =
              Constrintern.interp_type sigma env0
                (prod_constr_expr arityc bl) in
            Environ.push_named (recname,None,arity) env)
          (Global.env()) recs in
      
      let name_of_binder = function
        | LocalRawAssum (nal,_) -> nal
        | LocalRawDef (_,_) -> [] in
      let pr_onerec = function
        | (id,n,bl,type_,def),ntn ->
            let (bl',def,type_) =
              if Options.do_translate() then extract_def_binders def type_
              else ([],def,type_) in
            let bl = bl @ bl' in
            let ids = List.flatten (List.map name_of_binder bl) in
            let name =
              try snd (List.nth ids n)
              with Failure _ ->
                warn (str "non-printable fixpoint \""++pr_id id++str"\"");
                Anonymous in
            let annot =
              if List.length ids > 1 then 
                spc() ++ str "{struct " ++ pr_name name ++ str"}"
              else mt() in
	    let bl,ppc =
              pr_lconstr_env_n rec_sign true bl (CCast(dummy_loc,def,type_)) in
            pr_id id ++ pr_binders_arg bl ++ annot ++ spc()
            ++ pr_type_option (fun c -> spc() ++ pr_type c) type_
            ++ str" :=" ++ brk(1,1) ++ ppc ++ 
	    pr_decl_notation pr_constr ntn
      in
      hov 1 (str"Fixpoint" ++ spc() ++
        prlist_with_sep (fun _ -> fnl() ++ fnl() ++ str"with ") pr_onerec recs)

  | VernacCoFixpoint corecs ->
      let pr_onecorec (id,bl,c,def) =
        let (bl',def,c) =
              if Options.do_translate() then extract_def_binders def c
              else ([],def,c) in
        let bl = bl @ bl' in
        pr_id id ++ spc() ++ pr_binders bl ++ spc() ++ str":" ++
        spc() ++ pr_type c ++
        str" :=" ++ brk(1,1) ++ pr_lconstr def in
      hov 1 (str"CoFixpoint" ++ spc() ++
      prlist_with_sep (fun _ -> fnl() ++ str"with ") pr_onecorec corecs)  
  | VernacScheme l ->
      hov 2 (str"Scheme" ++ spc() ++
             prlist_with_sep (fun _ -> fnl() ++ str"with ") pr_onescheme l)

  (* Gallina extensions *)
  | VernacRecord (b,(oc,name),ps,s,c,fs) ->
      let pr_record_field = function
        | (oc,AssumExpr (id,t)) ->
            hov 1 (pr_lname id ++
            (if oc then str" :>" else str" :") ++ spc() ++
            pr_type t)
        | (oc,DefExpr(id,b,opt)) -> (match opt with
	    | Some t ->
                hov 1 (pr_lname id ++
                (if oc then str" :>" else str" :") ++ spc() ++
                pr_type t ++ str" :=" ++ pr_lconstr b)
	    | None ->
                hov 1 (pr_lname id ++ str" :=" ++ spc() ++
                pr_lconstr b)) in
      hov 2
        (str (if b then "Record" else "Structure") ++
         (if oc then str" > " else str" ") ++ pr_lident name ++ 
          pr_and_type_binders_arg ps ++ str" :" ++ spc() ++ pr_type s ++ 
	  str" := " ++
         (match c with
           | None -> mt()
           | Some sc -> pr_lident sc) ++
	spc() ++ str"{"  ++
        hv 0 (prlist_with_sep pr_semicolon pr_record_field fs ++ str"}"))
  | VernacBeginSection id -> hov 2 (str"Section" ++ spc () ++ pr_lident id)
  | VernacEndSegment id -> hov 2 (str"End" ++ spc() ++ pr_lident id)
  | VernacRequire (exp,spe,l) -> hov 2
      (str "Require" ++ pr_require_token exp ++ spc() ++
      (match spe with
      |	None -> mt()
      |	Some flag ->
          (if flag then str"Specification" else str"Implementation") ++
          spc ()) ++
      prlist_with_sep sep pr_module l)
  | VernacImport (f,l) ->
      (if f then str"Export" else str"Import") ++ spc() ++
      prlist_with_sep sep pr_import_module l
  | VernacCanonical q -> str"Canonical Structure" ++ spc() ++ pr_reference q
  | VernacCoercion (s,id,c1,c2) ->
      hov 1 (
	str"Coercion" ++ (match s with | Local -> spc() ++
	  str"Local" ++ spc() | Global -> spc()) ++
	pr_reference id ++ spc() ++ str":" ++ spc() ++ pr_class_rawexpr c1 ++
	spc() ++ str">->" ++ spc() ++ pr_class_rawexpr c2)
  | VernacIdentityCoercion (s,id,c1,c2) ->
      hov 1 (
	str"Identity Coercion" ++ (match s with | Local -> spc() ++
	  str"Local" ++ spc() | Global -> spc()) ++ pr_lident id ++ 
	spc() ++ str":" ++ spc() ++ pr_class_rawexpr c1 ++ spc() ++ str">->" ++
	spc() ++ pr_class_rawexpr c2)

  (* Modules and Module Types *)
  | VernacDefineModule (m,bl,ty,bd) ->
      let b = pr_module_binders_list bl pr_lconstr in 
      hov 2 (str"Module " ++ pr_lident m ++ b ++
             pr_opt (pr_of_module_type pr_lconstr) ty ++
             pr_opt (fun me -> str ":= " ++ pr_module_expr me) bd)
  | VernacDeclareModule (id,bl,m1,m2) ->
      let b = pr_module_binders_list bl pr_lconstr in 
      hov 2 (str"Declare Module " ++ pr_lident id ++ b ++
             pr_opt (pr_of_module_type pr_lconstr) m1 ++
             pr_opt (fun me -> str ":= " ++ pr_module_expr me) m2)
  | VernacDeclareModuleType (id,bl,m) ->
      let b = pr_module_binders_list bl pr_lconstr in 
      hov 2 (str"Module Type " ++ pr_lident id ++ b ++
             pr_opt (fun mt -> str ":= " ++ pr_module_type pr_lconstr mt) m)

  (* Solving *)
  | VernacSolve (i,tac,deftac) ->
      (* Normally shunted by vernac.ml *)
      let env =
        try snd (Pfedit.get_goal_context i)
        with UserError _ -> Global.env() in
      let tac = 
	Options.with_option Options.translate_syntax 
	  (Constrintern.for_grammar (Tacinterp.glob_tactic_env [] env)) tac in
      pr_vernac_solve (i,env,tac,deftac)

  | VernacSolveExistential (i,c) ->
      str"Existential " ++ int i ++ pr_lconstrarg c

  (* Auxiliary file and library management *)
  | VernacRequireFrom (exp,spe,f) -> hov 2
      (str"Require " ++ pr_require_token exp ++ spc() ++
      (match spe with
        | None -> mt()
        | Some false -> str"Implementation" ++ spc()
        | Some true -> str"Specification" ++ spc ()) ++
      qsnew f)
  | VernacAddLoadPath (fl,s,d) -> hov 2
      (str"Add" ++
       (if fl then str" Rec " else spc()) ++
       str"LoadPath" ++ spc() ++ qsnew s ++
       (match d with 
         | None -> mt()
         | Some dir -> spc() ++ str"as" ++ spc() ++ pr_dirpath dir)) 
  | VernacRemoveLoadPath s -> str"Remove LoadPath" ++ qsnew s
  | VernacAddMLPath (fl,s) ->
      str"Add" ++ (if fl then str" Rec " else spc()) ++ str"ML Path" ++ qsnew s
  | VernacDeclareMLModule l ->
      hov 2 (str"Declare ML Module" ++ spc() ++ prlist_with_sep sep qsnew l)
  | VernacChdir s -> str"Cd" ++ pr_opt qsnew s

  (* Commands *)
  | VernacDeclareTacticDefinition (rc,l) ->
      let pr_tac_body (id, body) =
        let idl, body =
          match body with
	    | Tacexpr.TacFun (idl,b) -> idl,b
            | _ -> [], body in
        pr_located pr_ltac_id id ++ 
	prlist (function None -> str " _"
                       | Some id -> spc () ++ pr_id id) idl
	++ str" :=" ++ brk(1,1) ++
	let idl = List.map out_some (List.filter (fun x -> not (x=None)) idl)in
        pr_raw_tactic_env 
	  (idl @ List.map snd (List.map fst l))
	  (Global.env())
	  body in
      hov 1
        (((*if !Options.p1 then
	  (if rc then str "Recursive " else mt()) ++
	  str "Tactic Definition " else*)
	    (* Rec by default *) str "Ltac ") ++
        prlist_with_sep (fun () -> fnl() ++ str"with ") pr_tac_body l)
  | VernacHints (local,dbnames,h) ->
      pr_hints local dbnames h pr_constr pr_pattern
  | VernacSyntacticDefinition (id,c,local,onlyparsing) ->
      hov 2
        (str"Notation " ++ pr_locality local ++ pr_id id ++ str" :=" ++
         pr_constrarg c ++
         pr_syntax_modifiers (if onlyparsing then [SetOnlyParsing] else []))
  | VernacDeclareImplicits (q,None) ->
      hov 2 (str"Implicit Arguments" ++ spc() ++ pr_reference q)
  | VernacDeclareImplicits (q,Some l) ->
      let r = Nametab.global q in
      Impargs.declare_manual_implicits r l;
      let imps = Impargs.implicits_of_global r in
      hov 1 (str"Implicit Arguments" ++ spc() ++ pr_reference q ++ spc() ++
             str"[" ++ prlist_with_sep sep (pr_explanation imps) l ++ str"]")
  | VernacReserve (idl,c) ->
      hov 1 (str"Implicit Type" ++
        str (if List.length idl > 1 then "s " else " ") ++
        prlist_with_sep spc pr_lident idl ++ str " :" ++ spc () ++ pr_type c)
  | VernacSetOpacity (fl,l) ->
      hov 1 ((if fl then str"Opaque" else str"Transparent") ++
             spc() ++ prlist_with_sep sep pr_reference l)

  | VernacSetOption (Goptions.SecondaryTable ("Implicit","Arguments"),BoolValue true) -> 
      str"Set Implicit Arguments" 
      ++
      (if !Options.translate_strict_impargs then
	sep_end () ++ fnl () ++ str"Unset Strict Implicit"
      else mt ())
  | VernacUnsetOption (Goptions.SecondaryTable ("Implicit","Arguments"))
  | VernacSetOption (Goptions.SecondaryTable ("Implicit","Arguments"),BoolValue false) -> 
      (if !Options.translate_strict_impargs then
	str"Set Strict Implicit" ++ sep_end () ++ fnl ()
      else mt ())
      ++
      str"Unset Implicit Arguments" 

  | VernacSetOption (Goptions.SecondaryTable (a,"Implicits"),BoolValue true) ->
      str("Set "^a^" Implicit")
  | VernacUnsetOption (Goptions.SecondaryTable (a,"Implicits")) -> 
      str("Unset "^a^" Implicit")

  | VernacUnsetOption na ->
      hov 1 (str"Unset" ++ spc() ++ pr_printoption na None)
  | VernacSetOption (na,v) -> hov 2 (str"Set" ++ spc() ++ pr_set_option na v)
  | VernacAddOption (na,l) -> hov 2 (str"Add" ++ spc() ++ pr_printoption na (Some l))
  | VernacRemoveOption (na,l) -> hov 2 (str"Remove" ++ spc() ++ pr_printoption na (Some l))
  | VernacMemOption (na,l) -> hov 2 (str"Test" ++ spc() ++ pr_printoption na (Some l))
  | VernacPrintOption na -> hov 2 (str"Test" ++ spc() ++ pr_printoption na None)
  | VernacCheckMayEval (r,io,c) -> 
      let pr_mayeval r c = match r with 
      | Some r0 ->
          hov 2 (str"Eval" ++ spc() ++
          pr_red_expr (pr_constr,pr_lconstr,pr_reference) r0 ++
          spc() ++ str"in" ++ spc () ++ pr_constr c)
      | None -> hov 2 (str"Check" ++ spc() ++ pr_constr c) 
      in 
      (if io = None then mt() else int (out_some io) ++ str ": ") ++ 
      pr_mayeval r c
  | VernacGlobalCheck c -> hov 2 (str"Type" ++ pr_constrarg c)
  | VernacPrint p -> 
      let pr_printable = function
	| PrintFullContext -> str"Print All"
	| PrintSectionContext s ->
            str"Print Section" ++ spc() ++ Libnames.pr_reference s
	| PrintGrammar (uni,ent) ->
            msgerrnl (str "warning: no direct translation of Print Grammar entry"); 
            str"Print Grammar" ++ spc() ++ str ent
	| PrintLoadPath -> str"Print LoadPath"
	| PrintModules -> str"Print Modules"
	| PrintMLLoadPath -> str"Print ML Path"
	| PrintMLModules -> str"Print ML Modules"
	| PrintGraph -> str"Print Graph"
	| PrintClasses -> str"Print Classes"
	| PrintCoercions -> str"Print Coercions"
	| PrintCoercionPaths (s,t) -> str"Print Coercion Paths" ++ spc() ++ pr_class_rawexpr s ++ spc() ++ pr_class_rawexpr t
	| PrintTables -> str"Print Tables"
	| PrintOpaqueName qid -> str"Print Term" ++ spc() ++ pr_reference qid
	| PrintHintGoal -> str"Print Hint"
	| PrintHint qid -> str"Print Hint" ++ spc() ++ pr_reference qid
	| PrintHintDb -> str"Print Hint *"
	| PrintHintDbName s -> str"Print HintDb" ++ spc() ++ str s
	| PrintUniverses fopt -> str"Dump Universes" ++ pr_opt str fopt
	| PrintName qid -> str"Print" ++ spc()  ++ pr_reference qid
	| PrintLocalContext -> assert false
            (* str"Print" *) 
	| PrintModuleType qid -> str"Print Module Type" ++ spc() ++ pr_reference qid
	| PrintModule qid -> str"Print Module" ++ spc() ++ pr_reference qid
	| PrintInspect n -> str"Inspect" ++ spc() ++ int n
	| PrintScopes -> str"Print Scopes"
	| PrintScope s -> str"Print Scope" ++ spc() ++ str s 
	| PrintVisibility s -> str"Print Visibility" ++ pr_opt str s 
	| PrintAbout qid -> str"About" ++ spc()  ++ pr_reference qid
	| PrintImplicit qid -> str"Print Implicit" ++ spc()  ++ pr_reference qid
      in pr_printable p
  | VernacSearch (sea,sea_r) -> pr_search sea sea_r pr_pattern
  | VernacLocate loc -> 
      let pr_locate =function
	| LocateTerm qid ->  pr_reference qid
	| LocateFile f -> str"File" ++ spc() ++ qsnew f
	| LocateLibrary qid -> str"Library" ++ spc () ++ pr_module qid
	| LocateNotation s -> qsnew s
      in str"Locate" ++ spc() ++ pr_locate loc
  | VernacComments l ->
      hov 2
        (str"Comments" ++ spc() ++ prlist_with_sep sep (pr_comment pr_constr) l)
  | VernacNop -> mt()
  
  (* Toplevel control *)
  | VernacToplevelControl exn -> pr_topcmd exn

  (* For extension *)
  | VernacExtend (s,c) -> pr_extend s c
  | VernacV7only _ -> mt()
  | VernacV8only com -> pr_vernac com
  | VernacProof Tacexpr.TacId _ -> str "Proof"
  | VernacProof te -> str "Proof with" ++ spc() ++ pr_raw_tactic te 

and pr_extend s cl =
  let pr_arg a =
    try pr_gen (Global.env()) a
    with Failure _ -> str ("<error in "^s^">") in
  try
    (* Hack pour les syntaxes changeant non uniformément en passant a la V8 *)
    let s =
      let n = String.length s in
      if Options.do_translate() & n > 2 & String.sub s (n-2) 2 = "V7"
      then String.sub s 0 (n-2) ^ "V8"
      else s in
    (* "Hint Rewrite in using" changes the order of its args in v8 !! *)
    let cl = match s, cl with
      | "HintRewriteV8", [a;b;c;d] -> [a;b;d;c]
      | _ -> cl in
    let rls = List.assoc s (Egrammar.get_extend_vernac_grammars()) in
    let (hd,rl) = match_vernac_rule (List.map Genarg.genarg_tag cl) rls in
    let (pp,_) =
      List.fold_left
        (fun (strm,args) pi ->
          match pi with
              Egrammar.TacNonTerm _ -> 
                (strm ++ pr_gen (Global.env()) (List.hd args),
                List.tl args)
            | Egrammar.TacTerm s -> (strm ++ spc() ++ str s, args))
        (str hd,cl) rl in
    hov 1 pp
    ++ (if s = "Correctness" then sep_end () ++ fnl() ++ str "Proof" else mt())
  with Not_found ->
    hov 1 (str ("TODO("^s) ++ prlist_with_sep sep pr_arg cl ++ str ")")

in pr_vernac

let pr_vernac = make_pr_vernac Ppconstrnew.pr_constr Ppconstrnew.pr_lconstr

let pr_vernac = function
  | VernacRequire (_,_,[Ident(_,r)]) when
      (* Obsolete modules *)
      List.mem (string_of_id r)
	["Refine"; "Inv"; "Equality"; "EAuto"; "AutoRewrite"; "EqDecide"; 
         "Xml"; "Extraction"; "Tauto"; "Setoid_replace";"Elimdep";
	 "DatatypesSyntax"; "LogicSyntax"; "Logic_TypeSyntax";
	 "SpecifSyntax"; "PeanoSyntax"; "TypeSyntax"; "PolyListSyntax";
	 "Zsyntax"] ->
      warning ("Forgetting obsolete module "^(string_of_id r));
      mt()
  | VernacRequire (exp,spe,[Ident(_,r)]) when
      (* Renamed modules *)
      List.mem (string_of_id r) ["zarith_aux";"fast_integer"] ->
      warning ("Replacing obsolete module "^(string_of_id r)^" with ZArith");
	(str "Require" ++ pr_require_token exp ++ spc() ++
	(match spe with
	  | None -> mt()
	  | Some flag ->
	      (if flag then str"Specification" else str"Implementation") ++
	      spc ()) ++
	str "ZArith.")
  | VernacImport (false,[Libnames.Ident (_,a)]) when
      (* Pour ceux qui ont utilisé la couche "Import *_scope" de compat *)
      let a = Names.string_of_id a in
      a = "nat_scope" or a = "Z_scope" or a = "R_scope" -> mt()
  | VernacSyntax _  | VernacGrammar _ as x -> pr_vernac x
  | VernacPrint PrintLocalContext -> 
      warning ("\"Print.\" is discontinued");
      mt ()
  | x -> pr_vernac x ++ sep_end ()

