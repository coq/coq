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
open Ppconstr
open Pptactic
open Rawterm
open Genarg
open Pcoq
open Libnames
open Ppextend
open Topconstr
open Decl_kinds
open Tacinterp

let pr_spc_lconstr = pr_sep_com spc pr_lconstr_expr

let pr_lident (loc,id) =
  if loc <> dummy_loc then
    let (b,_) = unloc loc in
    pr_located pr_id (make_loc (b,b+String.length(string_of_id id)),id)
  else pr_id id

let string_of_fqid fqid =
 String.concat "." (List.map string_of_id fqid)

let pr_fqid fqid = str (string_of_fqid fqid)

let pr_lfqid (loc,fqid) =
  if loc <> dummy_loc then
   let (b,_) = unloc loc in
    pr_located pr_fqid (make_loc (b,b+String.length(string_of_fqid fqid)),fqid)
  else
   pr_fqid fqid

let pr_lname = function
    (loc,Name id) -> pr_lident (loc,id)
  | lna -> pr_located pr_name lna

let pr_ltac_id = Nameops.pr_id

let pr_module = Libnames.pr_reference

let pr_import_module = Libnames.pr_reference

let sep_end () = str"."

(* Warning: [pr_raw_tactic] globalises and fails if globalisation fails *)

let pr_raw_tactic_env l env t = 
  pr_glob_tactic env (Tacinterp.glob_tactic_env l env t)

let pr_gen env t =
  pr_raw_generic 
    pr_constr_expr
    pr_lconstr_expr
    (pr_raw_tactic_level env) pr_reference t

let pr_raw_tactic tac = pr_raw_tactic (Global.env()) tac

let rec extract_signature = function
  | [] -> []
  | Egrammar.TacNonTerm (_,(_,t),_) :: l -> t :: extract_signature l
  | _::l -> extract_signature l

let rec match_vernac_rule tys = function
    [] -> raise Not_found
  | pargs::rls ->
      if extract_signature pargs = tys then pargs
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

let strip_meta id =
  let s = string_of_id id in
  if s.[0]='$' then id_of_string (String.sub s 1 (String.length s - 1))
  else id

let pr_production_item = function
  | VNonTerm (loc,nt,Some p) -> str nt ++ str"(" ++ pr_id (strip_meta p) ++ str")"
  | VNonTerm (loc,nt,None) -> str nt
  | VTerm s -> qs s

let pr_comment pr_c = function
  | CommentConstr c -> pr_c c
  | CommentString s -> qs s
  | CommentInt n -> int n

let pr_in_out_modules = function
  | SearchInside l -> spc() ++ str"inside" ++ spc() ++ prlist_with_sep sep pr_module l
  | SearchOutside [] -> mt()
  | SearchOutside l -> spc() ++ str"outside" ++ spc() ++ prlist_with_sep sep pr_module l

let pr_search_about = function
  | SearchRef r -> pr_reference r
  | SearchString s -> qs s

let pr_search a b pr_p = match a with
  | SearchHead qid -> str"Search" ++ spc() ++ pr_reference qid ++ pr_in_out_modules b
  | SearchPattern c -> str"SearchPattern" ++ spc() ++ pr_p c ++ pr_in_out_modules b
  | SearchRewrite c -> str"SearchRewrite" ++ spc() ++ pr_p c ++ pr_in_out_modules b
  | SearchAbout sl -> str"SearchAbout" ++ spc() ++ str "[" ++ prlist_with_sep spc pr_search_about sl ++ str "]" ++ pr_in_out_modules b

let pr_locality local = if local then str "Local " else str ""
let pr_non_globality local = if local then str "" else str "Global "

let pr_explanation (e,b) =
  let a = match e with
  | ExplByPos (n,_) -> anomaly "No more supported"
  | ExplByName id -> pr_id id in
  if b then str "[" ++ a ++ str "]" else a

let pr_class_rawexpr = function
  | FunClass -> str"Funclass"
  | SortClass -> str"Sortclass"
  | RefClass qid -> pr_reference qid

let pr_option_ref_value = function
  | QualidRefValue id -> pr_reference id
  | StringRefValue s -> qs s

let pr_printoption a b = match a with
  | Goptions.PrimaryTable table -> str table ++ pr_opt (prlist_with_sep sep pr_option_ref_value) b
  | Goptions.SecondaryTable (table,field) -> str table ++ spc() ++ str field ++ pr_opt (prlist_with_sep sep pr_option_ref_value) b
  | Goptions.TertiaryTable (table,field1,field2) -> str table ++ spc() ++
      str field1 ++ spc() ++ str field2 ++ 
      pr_opt (prlist_with_sep sep pr_option_ref_value) b

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
  let pph =
    match h with
    | HintsResolve l ->
        str "Resolve " ++ prlist_with_sep sep pr_c l
    | HintsImmediate l ->
        str"Immediate" ++ spc() ++ prlist_with_sep sep pr_c l
    | HintsUnfold l ->
        str "Unfold " ++ prlist_with_sep sep pr_reference l
    | HintsConstructors c ->
        str"Constructors" ++ spc() ++ prlist_with_sep spc pr_reference c
    | HintsExtern (n,c,tac) ->
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
      str"Definition" ++ spc() ++ pr_lfqid id ++ str" := " ++ p
  | CWith_Module (id,qid) ->
      str"Module" ++ spc() ++ pr_lfqid id ++ str" := " ++
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

let pr_require_token = function
  | Some true -> str "Export "
  | Some false -> str "Import "
  | None -> mt()

let pr_module_vardecls pr_c (export,idl,mty) =
  let m = pr_module_type pr_c mty in
  (* Update the Nametab for interpreting the body of module/modtype *)
  let lib_dir = Lib.library_dp() in
  List.iter (fun (_,id) ->
    Declaremods.process_module_bindings [id]
      [make_mbid lib_dir (string_of_id id),
       Modintern.interp_modtype (Global.env()) mty]) idl;
  (* Builds the stream *)
  spc() ++
  hov 1 (str"(" ++ pr_require_token export ++
   prlist_with_sep spc pr_lident idl ++ str":" ++ m ++ str")")

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

let pr_type_option pr_c = function
  | CHole loc -> mt()
  | _ as c -> brk(0,2) ++ str":" ++ pr_c c

let pr_decl_notation prc =
  pr_opt (fun (ntn,c,scopt) -> fnl () ++
    str "where " ++ qs ntn ++ str " := " ++ prc c ++
    pr_opt (fun sc -> str ": " ++ str sc) scopt)

let pr_vbinders l =
  hv 0 (pr_binders l)

let pr_binders_arg =
  pr_ne_sep spc pr_binders

let pr_and_type_binders_arg bl =
  pr_binders_arg bl

let pr_onescheme (idop,schem) =
  match schem with 
  | InductionScheme (dep,ind,s) ->
    (match idop with
      | Some id -> hov 0 (pr_lident id ++ str" :=") ++ spc()
      | None -> spc ()
    ) ++
    hov 0 ((if dep then str"Induction for" else str"Minimality for")
    ++ spc() ++ pr_reference ind) ++ spc() ++ 
    hov 0 (str"Sort" ++ spc() ++ pr_rawsort s)
  | EqualityScheme ind -> 
    (match idop with
      | Some id -> hov 0 (pr_lident id ++ str" :=") ++ spc()
      | None -> spc()
    ) ++
    hov 0 (str"Equality for")
    ++ spc() ++ pr_reference ind

let begin_of_inductive = function
    [] -> 0
  | (_,((loc,_),_))::_ -> fst (unloc loc)

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

let pr_thm_token k = str (string_of_theorem_kind k)

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
  | SetFormat s -> str"format " ++ pr_located qs s

let pr_syntax_modifiers = function
  | [] -> mt()
  | l -> spc() ++ 
      hov 1 (str"(" ++ prlist_with_sep sep_v2 pr_syntax_modifier l ++ str")")

let print_level n =
  if n <> 0 then str " (at level " ++ int n ++ str ")" else mt ()

let pr_grammar_tactic_rule n (_,pil,t) =
  hov 2 (str "Tactic Notation" ++ print_level n ++ spc() ++ 
    hov 0 (prlist_with_sep sep pr_production_item pil ++
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
  | Some pprim,Any -> qs pprim
  | Some pprim,Prec p -> qs pprim ++ spc() ++ str":" ++ spc() ++ int p
  | _ -> mt()

(**************************************)
(* Pretty printer for vernac commands *)
(**************************************)
let make_pr_vernac pr_constr pr_lconstr =

let pr_constrarg c = spc () ++ pr_constr c in
let pr_lconstrarg c = spc () ++ pr_lconstr c in
let pr_intarg n = spc () ++ int n in
let pr_lident_constr sep (i,c) = pr_lident i ++ sep ++ pr_constrarg c in
let pr_lname_lident_constr (oi,i,a) = 
  (match snd oi with Anonymous -> mt () | Name id -> pr_lident (fst oi, id) ++ spc () ++ str":" ++ spc ()) 
    ++ pr_lident i ++ spc () ++ prlist_with_sep spc pr_constrarg a in
let pr_typeclass_context l = 
  match l with
      [] -> mt ()
    | _ -> str"[" ++ spc () ++ prlist_with_sep (fun () -> str"," ++ spc()) pr_lname_lident_constr l
	++ spc () ++ str"]" ++ spc ()
in
let pr_instance_def sep (i,l,c) = pr_lident i ++ prlist_with_sep spc pr_lident l 
  ++ sep ++ pr_constrarg c in

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
  | VernacBacktrack (i,j,k) -> 
      str "Backtrack" ++  spc() ++ prlist_with_sep sep int [i;j;k]
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
	| ShowMatch id -> str"Show Match " ++ pr_lident id
	| ShowThesis -> str "Show Thesis"
	| ExplainProof l -> str"Explain Proof" ++ spc() ++ prlist_with_sep sep int l
	| ExplainTree l -> str"Explain Proof Tree" ++ spc() ++ prlist_with_sep sep int l 
      in pr_showable s
  | VernacCheckGuard -> str"Guarded"

  (* Resetting *)
  | VernacResetName id -> str"Reset" ++ spc() ++ pr_lident id
  | VernacResetInitial -> str"Reset Initial"
  | VernacBack i -> if i=1 then str"Back" else str"Back" ++ pr_intarg i
  | VernacBackTo i -> str"BackTo" ++ pr_intarg i

  (* State management *)
  | VernacWriteState s -> str"Write State" ++ spc () ++ qs s
  | VernacRestoreState s -> str"Restore State" ++ spc() ++ qs s

  (* Control *)
  | VernacList l ->
      hov 2 (str"[" ++ spc() ++
             prlist (fun v -> pr_located pr_vernac v ++ sep_end () ++ fnl()) l
             ++ spc() ++ str"]") 
  | VernacLoad (f,s) -> str"Load" ++ if f then (spc() ++ str"Verbose"
  ++ spc()) else spc()  ++ qs s
  | VernacTime v -> str"Time" ++ spc() ++ pr_vernac v
  | VernacVar id -> pr_lident id
  
  (* Syntax *) 
  | VernacTacticNotation (n,r,e) -> pr_grammar_tactic_rule n ("",r,e)
  | VernacOpenCloseScope (local,opening,sc) ->
      str (if opening then "Open " else "Close ") ++ pr_locality local ++
      str "Scope" ++ spc() ++ str sc
  | VernacDelimiters (sc,key) ->
      str"Delimit Scope" ++ spc () ++ str sc ++
      spc() ++ str "with " ++ str key
  | VernacBindScope (sc,cll) ->
      str"Bind Scope" ++ spc () ++ str sc ++
      spc() ++ str "with " ++ prlist_with_sep spc pr_class_rawexpr cll
  | VernacArgumentsScope (local,q,scl) -> let pr_opt_scope = function 
      |	None -> str"_"
      |	Some sc -> str sc in 
    str"Arguments Scope" ++ spc() ++ pr_non_globality local ++ pr_reference q 
    ++ spc() ++ str"[" ++ prlist_with_sep sep pr_opt_scope scl ++ str"]"
  | VernacInfix (local,(s,mv),q,sn) -> (* A Verifier *)
      hov 0 (hov 0 (str"Infix " ++ pr_locality local
      ++ qs s ++ str " :=" ++ spc() ++ pr_reference q) ++
      pr_syntax_modifiers mv ++
      (match sn with
    | None -> mt()
    | Some sc -> spc() ++ str":" ++ spc() ++ str sc))
  | VernacNotation (local,c,(s,l),opt) ->
      let ps =
	let n = String.length s in
	if n > 2 & s.[0] = '\'' & s.[n-1] = '\'' 
	then
          let s' = String.sub s 1 (n-2) in
          if String.contains s' '\'' then qs s else str s'
	else qs s in
      hov 2( str"Notation" ++ spc() ++ pr_locality local ++ ps ++
      str " :=" ++ pr_constrarg c ++ pr_syntax_modifiers l ++
      (match opt with
        | None -> mt()
        | Some sc -> str" :" ++ spc() ++ str sc))
  | VernacSyntaxExtension (local,(s,l)) ->
      str"Reserved Notation" ++ spc() ++ pr_locality local ++ qs s ++
      pr_syntax_modifiers l

  (* Gallina *)
  | VernacDefinition (d,id,b,f) -> (* A verifier... *)
      let pr_def_token dk = str (string_of_definition_kind dk) in
      let pr_reduce = function
        | None -> mt()
        | Some r ->
            str"Eval" ++ spc() ++
            pr_red_expr (pr_constr, pr_lconstr, pr_or_by_notation pr_reference) r ++
            str" in" ++ spc() in
      let pr_def_body = function
        | DefineBody (cbl,bl,red,body,d) ->
            let ty = match d with
              | None -> mt()
              | Some ty -> spc() ++ str":" ++ pr_spc_lconstr ty
	    in
            (pr_binders_arg bl,ty,Some (pr_reduce red ++ pr_lconstr body))
        | ProveBody (cbl,bl,t) ->
            (pr_binders_arg bl, str" :" ++ pr_spc_lconstr t, None) in
      let (binds,typ,c) = pr_def_body b in
      hov 2 (pr_def_token d ++ spc() ++ pr_lident id ++ binds ++ typ ++
      (match c with
        | None -> mt()
        | Some cc -> str" :=" ++ spc() ++ cc))

  | VernacStartTheoremProof (ki,id,(cbl,bl,c),b,d) ->
      hov 1 (pr_thm_token ki ++ spc() ++ pr_lident id ++ spc() ++
		pr_typeclass_context cbl ++
      (match bl with
        | [] -> mt()
        | _ -> pr_binders bl ++ spc())
      ++ str":" ++ pr_spc_lconstr c)
  | VernacEndProof Admitted -> str"Admitted"
  | VernacEndProof (Proved (opac,o)) -> (match o with
    | None -> if opac then str"Qed" else str"Defined"
    | Some (id,th) -> (match th with
      |	None -> (if opac then str"Save" else str"Defined") ++ spc() ++ pr_lident id
      |	Some tok -> str"Save" ++ spc() ++ pr_thm_token tok ++ spc() ++ pr_lident id)) 
  | VernacExactProof c ->
      hov 2 (str"Proof" ++ pr_lconstrarg c)
  | VernacAssumption (stre,_,l) ->
      let n = List.length (List.flatten (List.map fst (List.map snd l))) in
      hov 2
        (pr_assumption_token (n > 1) stre ++ spc() ++ 
	 pr_ne_params_list pr_lconstr_expr l)
  | VernacInductive (f,l) ->

      let pr_constructor (coe,(id,c)) =
        hov 2 (pr_lident id ++ str" " ++
               (if coe then str":>" else str":") ++
                pr_spc_lconstr c) in
      let pr_constructor_list l = match l with
        | [] -> mt()
        | _ ->
            pr_com_at (begin_of_inductive l) ++
            fnl() ++
            str (if List.length l = 1 then "   " else " | ") ++
            prlist_with_sep (fun _ -> fnl() ++ str" | ") pr_constructor l in
      let pr_oneind key ((id,indpar,s,lc),ntn) =
	hov 0 (
          str key ++ spc() ++
          pr_lident id ++ pr_and_type_binders_arg indpar ++ spc() ++ str":" ++ 
	  spc() ++ pr_lconstr_expr s ++ 
	  str" :=") ++ pr_constructor_list lc ++ 
	pr_decl_notation pr_constr ntn in

      hov 1 (pr_oneind (if f then "Inductive" else "CoInductive") (List.hd l))
      ++ 
      (prlist (fun ind -> fnl() ++ hov 1 (pr_oneind "with" ind)) (List.tl l))


  | VernacFixpoint (recs,b) ->
      let name_of_binder = function
        | LocalRawAssum (nal,_,_) -> nal
        | LocalRawDef (_,_,_) -> [] in
      let pr_onerec = function
        | (id,(n,ro),bl,type_,def),ntn ->
            let (bl',def,type_) =
              if Flags.do_translate() then extract_def_binders def type_
              else ([],def,type_) in
            let bl = bl @ bl' in
            let ids = List.flatten (List.map name_of_binder bl) in
            let annot =
	      match n with 
		| None -> mt () 
		| Some n -> 
		    let name =
		      try snd (List.nth ids n)
		      with Failure _ ->
			warn (str "non-printable fixpoint \""++pr_id id++str"\"");
			Anonymous in
		    match (ro : Topconstr.recursion_order_expr) with
			CStructRec -> 
			  if List.length ids > 1 then 
			    spc() ++ str "{struct " ++ pr_name name ++ str"}"
			  else mt()
		      | CWfRec c -> 
			  spc() ++ str "{wf " ++ pr_lconstr_expr c ++ spc() ++ 
			    pr_name name ++ str"}"
		      | CMeasureRec c -> 
			  spc() ++ str "{measure " ++ pr_lconstr_expr c ++ spc() ++ 
			    pr_name name ++ str"}"
	    in
            pr_id id ++ pr_binders_arg bl ++ annot ++ spc()
            ++ pr_type_option (fun c -> spc() ++ pr_lconstr_expr c) type_
            ++ str" :=" ++ brk(1,1) ++ pr_lconstr def ++ 
	    pr_decl_notation pr_constr ntn
      in
      let start = if b then "Boxed Fixpoint" else "Fixpoint" in
      hov 1 (str start ++ spc() ++
        prlist_with_sep (fun _ -> fnl() ++ fnl() ++ str"with ") pr_onerec recs)

  | VernacCoFixpoint (corecs,b) ->
      let pr_onecorec ((id,bl,c,def),ntn) =
        let (bl',def,c) =
              if Flags.do_translate() then extract_def_binders def c
              else ([],def,c) in
        let bl = bl @ bl' in
        pr_id id ++ spc() ++ pr_binders bl ++ spc() ++ str":" ++
        spc() ++ pr_lconstr_expr c ++
        str" :=" ++ brk(1,1) ++ pr_lconstr def  ++ 
	pr_decl_notation pr_constr ntn
      in
      let start = if b then "Boxed CoFixpoint" else "CoFixpoint" in
      hov 1 (str start ++ spc() ++
      prlist_with_sep (fun _ -> fnl() ++ str"with ") pr_onecorec corecs)  
  | VernacScheme l ->
      hov 2 (str"Scheme" ++ spc() ++
             prlist_with_sep (fun _ -> fnl() ++ str"with ") pr_onescheme l)
  | VernacCombinedScheme (id, l) ->
      hov 2 (str"Combined Scheme" ++ spc() ++
	       pr_lident id ++ spc() ++ str"from" ++ spc() ++
	       prlist_with_sep (fun _ -> fnl() ++ str", ") pr_lident l)
	

  (* Gallina extensions *)
  | VernacRecord (b,(oc,name),ps,s,c,fs) ->
      let pr_record_field = function
        | (oc,AssumExpr (id,t)) ->
            hov 1 (pr_lname id ++
            (if oc then str" :>" else str" :") ++ spc() ++
            pr_lconstr_expr t)
        | (oc,DefExpr(id,b,opt)) -> (match opt with
	    | Some t ->
                hov 1 (pr_lname id ++
                (if oc then str" :>" else str" :") ++ spc() ++
                pr_lconstr_expr t ++ str" :=" ++ pr_lconstr b)
	    | None ->
                hov 1 (pr_lname id ++ str" :=" ++ spc() ++
                pr_lconstr b)) in
      hov 2
        (str (if b then "Record" else "Structure") ++
         (if oc then str" > " else str" ") ++ pr_lident name ++ 
          pr_and_type_binders_arg ps ++ str" :" ++ spc() ++ 
	  pr_lconstr_expr s ++ str" := " ++
         (match c with
           | None -> mt()
           | Some sc -> pr_lident sc) ++
	spc() ++ str"{"  ++
        hv 0 (prlist_with_sep pr_semicolon pr_record_field fs ++ str"}"))
  | VernacBeginSection id -> hov 2 (str"Section" ++ spc () ++ pr_lident id)
  | VernacEndSegment id -> hov 2 (str"End" ++ spc() ++ pr_lident id)
  | VernacRequire (exp,spe,l) -> hov 2
      (str "Require" ++ spc() ++ pr_require_token exp ++
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


  | VernacClass (id, par, ar, sup, props) ->
      hov 1 (
	str"Class" ++ spc () ++ pr_lident id ++
	  prlist_with_sep (spc) (pr_lident_constr (spc() ++ str ":" ++ spc())) par ++ 
	  spc () ++ str":" ++ spc() ++ pr_rawsort (snd ar) ++
	  spc () ++ str"where" ++ spc () ++
	  prlist_with_sep (fun () -> str";" ++ spc()) (pr_lident_constr (spc () ++ str":" ++ spc())) props )
	  
	
 | VernacInstance (sup, instid, cid, par, props) -> 
     hov 1 (
       str"Instance" ++ spc () ++ 
	 pr_typeclass_context sup ++
	 str"=>" ++ spc () ++ 
	 (match instid with Some id -> pr_lident id ++ spc () ++ str":" ++ spc () | None -> mt ()) ++
	 pr_lident cid ++ prlist pr_constrarg par ++ spc () ++
	 spc () ++ str"where" ++ spc () ++
	 prlist_with_sep (fun () -> str";" ++ spc()) (pr_instance_def (spc () ++ str":=" ++ spc())) props)

 | VernacContext l ->
     hov 1 (
       str"Context" ++ spc () ++ str"[" ++ spc () ++
	 prlist_with_sep (fun () -> str"," ++ spc()) pr_lname_lident_constr l ++
	 spc () ++ str "]")
	      

 | VernacDeclareInstance id ->
     hov 1 (str"Instance" ++ spc () ++ pr_lident id)
       
 | VernacSetInstantiationTactic tac ->
     hov 1 (str"Instantiation Tactic :=" ++ spc () ++ pr_raw_tactic tac)

  (* Modules and Module Types *)
  | VernacDefineModule (export,m,bl,ty,bd) ->
      let b = pr_module_binders_list bl pr_lconstr in 
      hov 2 (str"Module" ++ spc() ++ pr_require_token export ++
             pr_lident m ++ b ++
             pr_opt (pr_of_module_type pr_lconstr) ty ++
             pr_opt (fun me -> str ":= " ++ pr_module_expr me) bd)
  | VernacDeclareModule (export,id,bl,m1) ->
      let b = pr_module_binders_list bl pr_lconstr in 
      hov 2 (str"Declare Module" ++ spc() ++ pr_require_token export ++
             pr_lident id ++ b ++
             pr_of_module_type pr_lconstr m1)
  | VernacDeclareModuleType (id,bl,m) ->
      let b = pr_module_binders_list bl pr_lconstr in 
      hov 2 (str"Module Type " ++ pr_lident id ++ b ++
             pr_opt (fun mt -> str ":= " ++ pr_module_type pr_lconstr mt) m)

  (* Solving *)
  | VernacSolve (i,tac,deftac) ->
      (if i = 1 then mt() else int i ++ str ": ") ++
      pr_raw_tactic tac
      ++ (try if deftac & Pfedit.get_end_tac() <> None then str ".." else mt ()
      with UserError _|Stdpp.Exc_located _ -> mt())

  | VernacSolveExistential (i,c) ->
      str"Existential " ++ int i ++ pr_lconstrarg c

  (* MMode *)
 
  | VernacProofInstr instr -> anomaly "Not implemented"
  | VernacDeclProof -> str "proof" 
  | VernacReturn -> str "return"

  (* /MMode *) 

  (* Auxiliary file and library management *)
  | VernacRequireFrom (exp,spe,f) -> hov 2
      (str"Require" ++ spc() ++ pr_require_token exp ++
      (match spe with
        | None -> mt()
        | Some false -> str"Implementation" ++ spc()
        | Some true -> str"Specification" ++ spc ()) ++
      qs f)
  | VernacAddLoadPath (fl,s,d) -> hov 2
      (str"Add" ++
       (if fl then str" Rec " else spc()) ++
       str"LoadPath" ++ spc() ++ qs s ++
       (match d with 
         | None -> mt()
         | Some dir -> spc() ++ str"as" ++ spc() ++ pr_dirpath dir)) 
  | VernacRemoveLoadPath s -> str"Remove LoadPath" ++ qs s
  | VernacAddMLPath (fl,s) ->
      str"Add" ++ (if fl then str" Rec " else spc()) ++ str"ML Path" ++ qs s
  | VernacDeclareMLModule l ->
      hov 2 (str"Declare ML Module" ++ spc() ++ prlist_with_sep sep qs l)
  | VernacChdir s -> str"Cd" ++ pr_opt qs s

  (* Commands *)
  | VernacDeclareTacticDefinition (rc,l) ->
      let pr_tac_body (id, redef, body) =
        let idl, body =
          match body with
	    | Tacexpr.TacFun (idl,b) -> idl,b
            | _ -> [], body in
        pr_located pr_ltac_id id ++ 
	prlist (function None -> str " _"
                       | Some id -> spc () ++ pr_id id) idl
	++ (if redef then str" ::=" else str" :=") ++ brk(1,1) ++
	let idl = List.map Option.get (List.filter (fun x -> not (x=None)) idl)in
        pr_raw_tactic_env 
	  (idl @ List.map snd (List.map (fun (x, _, _) -> x) l))
	  (Global.env())
	  body in
      hov 1
        (((*if !Flags.p1 then
	  (if rc then str "Recursive " else mt()) ++
	  str "Tactic Definition " else*)
	    (* Rec by default *) str "Ltac ") ++
        prlist_with_sep (fun () -> fnl() ++ str"with ") pr_tac_body l)
  | VernacHints (local,dbnames,h) ->
      pr_hints local dbnames h pr_constr pr_pattern_expr
  | VernacSyntacticDefinition (id,c,local,onlyparsing) ->
      hov 2
        (str"Notation " ++ pr_locality local ++ pr_id id ++ str" :=" ++
         pr_constrarg c ++
         pr_syntax_modifiers (if onlyparsing then [SetOnlyParsing] else []))
  | VernacDeclareImplicits (local,q,None) ->
      hov 2 (str"Implicit Arguments" ++ spc() ++ pr_reference q)
  | VernacDeclareImplicits (local,q,Some imps) ->
      hov 1 (str"Implicit Arguments" ++ pr_non_globality local ++
      spc() ++ pr_reference q ++ spc() ++
             str"[" ++ prlist_with_sep sep pr_explanation imps ++ str"]")
  | VernacReserve (idl,c) ->
      hov 1 (str"Implicit Type" ++
        str (if List.length idl > 1 then "s " else " ") ++
        prlist_with_sep spc pr_lident idl ++ str " :" ++ spc () ++
        pr_lconstr c)
  | VernacSetOpacity (fl,l) ->
      hov 1 ((if fl then str"Opaque" else str"Transparent") ++
             spc() ++ prlist_with_sep sep pr_reference l)
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
          pr_red_expr (pr_constr,pr_lconstr,pr_or_by_notation pr_reference) r0 ++
          spc() ++ str"in" ++ spc () ++ pr_constr c)
      | None -> hov 2 (str"Check" ++ spc() ++ pr_constr c) 
      in 
      (if io = None then mt() else int (Option.get io) ++ str ": ") ++ 
      pr_mayeval r c
  | VernacGlobalCheck c -> hov 2 (str"Type" ++ pr_constrarg c)
  | VernacPrint p -> 
      let pr_printable = function
	| PrintFullContext -> str"Print All"
	| PrintSectionContext s ->
            str"Print Section" ++ spc() ++ Libnames.pr_reference s
	| PrintGrammar ent ->
            str"Print Grammar" ++ spc() ++ str ent
	| PrintLoadPath -> str"Print LoadPath"
	| PrintModules -> str"Print Modules"
	| PrintMLLoadPath -> str"Print ML Path"
	| PrintMLModules -> str"Print ML Modules"
	| PrintGraph -> str"Print Graph"
	| PrintClasses -> str"Print Classes"
	| PrintTypeClasses -> str"Print TypeClasses"
	| PrintInstances qid -> str"Print Instances" ++ spc () ++ pr_reference qid
	| PrintLtac qid -> str"Print Ltac" ++ spc() ++ pr_reference qid
	| PrintCoercions -> str"Print Coercions"
	| PrintCoercionPaths (s,t) -> str"Print Coercion Paths" ++ spc() ++ pr_class_rawexpr s ++ spc() ++ pr_class_rawexpr t
	| PrintCanonicalConversions -> str"Print Canonical Structures"
	| PrintTables -> str"Print Tables"
	| PrintOpaqueName qid -> str"Print Term" ++ spc() ++ pr_reference qid
	| PrintHintGoal -> str"Print Hint"
	| PrintHint qid -> str"Print Hint" ++ spc() ++ pr_reference qid
	| PrintHintDb -> str"Print Hint *"
	| PrintHintDbName s -> str"Print HintDb" ++ spc() ++ str s
	| PrintRewriteHintDbName s -> str"Print Rewrite HintDb" ++ spc() ++ str s
	| PrintUniverses fopt -> str"Dump Universes" ++ pr_opt str fopt
	| PrintName qid -> str"Print" ++ spc()  ++ pr_reference qid
	| PrintModuleType qid -> str"Print Module Type" ++ spc() ++ pr_reference qid
	| PrintModule qid -> str"Print Module" ++ spc() ++ pr_reference qid
	| PrintInspect n -> str"Inspect" ++ spc() ++ int n
	| PrintSetoids -> str"Print Setoids"
	| PrintScopes -> str"Print Scopes"
	| PrintScope s -> str"Print Scope" ++ spc() ++ str s 
	| PrintVisibility s -> str"Print Visibility" ++ pr_opt str s 
	| PrintAbout qid -> str"About" ++ spc()  ++ pr_reference qid
	| PrintImplicit qid -> str"Print Implicit" ++ spc()  ++ pr_reference qid
(* spiwack: command printing all the axioms and section variables used in a 
         term *)
	| PrintAssumptions qid -> str"Print Assumptions"++spc()++pr_reference qid
      in pr_printable p
  | VernacSearch (sea,sea_r) -> pr_search sea sea_r pr_pattern_expr
  | VernacLocate loc -> 
      let pr_locate =function
	| LocateTerm qid ->  pr_reference qid
	| LocateFile f -> str"File" ++ spc() ++ qs f
	| LocateLibrary qid -> str"Library" ++ spc () ++ pr_module qid
	| LocateModule qid -> str"Module" ++ spc () ++ pr_module qid
	| LocateNotation s -> qs s
      in str"Locate" ++ spc() ++ pr_locate loc
  | VernacComments l ->
      hov 2
        (str"Comments" ++ spc() ++ prlist_with_sep sep (pr_comment pr_constr) l)
  | VernacNop -> mt()
  
  (* Toplevel control *)
  | VernacToplevelControl exn -> pr_topcmd exn

  (* For extension *)
  | VernacExtend (s,c) -> pr_extend s c
  | VernacProof (Tacexpr.TacId _) -> str "Proof"
  | VernacProof te -> str "Proof with" ++ spc() ++ pr_raw_tactic te 

and pr_extend s cl =
  let pr_arg a =
    try pr_gen (Global.env()) a
    with Failure _ -> str ("<error in "^s^">") in
  try
    let rls = List.assoc s (Egrammar.get_extend_vernac_grammars()) in
    let rl = match_vernac_rule (List.map Genarg.genarg_tag cl) rls in
    let start,rl,cl =
      match rl with
	| Egrammar.TacTerm s :: rl -> str s, rl, cl
	| Egrammar.TacNonTerm _ :: rl ->
	    (* Will put an unnecessary extra space in front *)
	    pr_gen (Global.env()) (List.hd cl), rl, List.tl cl 
	| [] -> anomaly "Empty entry" in
    let (pp,_) =
      List.fold_left
        (fun (strm,args) pi ->
          match pi with
              Egrammar.TacNonTerm _ -> 
                (strm ++ pr_gen (Global.env()) (List.hd args),
                List.tl args)
            | Egrammar.TacTerm s -> (strm ++ spc() ++ str s, args))
        (start,cl) rl in
    hov 1 pp
  with Not_found ->
    hov 1 (str ("TODO("^s) ++ prlist_with_sep sep pr_arg cl ++ str ")")

in pr_vernac

let pr_vernac v = make_pr_vernac pr_constr_expr pr_lconstr_expr v ++ sep_end ()
