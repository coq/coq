(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

let pr_smart_global = pr_or_by_notation pr_reference

let pr_ltac_id = Libnames.pr_reference

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
    (pr_raw_tactic_level env) pr_constr_expr pr_reference t

let pr_raw_tactic tac = pr_raw_tactic (Global.env()) tac

let rec extract_signature = function
  | [] -> []
  | Egrammar.GramNonTerminal (_,t,_,_) :: l -> t :: extract_signature l
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
  | ETName -> str"ident"
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
  | TacNonTerm (loc,nt,Some (p,sep)) ->
      let pp_sep = if sep <> "" then str "," ++ quote (str sep) else mt () in
      str nt ++ str"(" ++ pr_id (strip_meta p) ++ pp_sep ++ str")"
  | TacNonTerm (loc,nt,None) -> str nt
  | TacTerm s -> qs s

let pr_comment pr_c = function
  | CommentConstr c -> pr_c c
  | CommentString s -> qs s
  | CommentInt n -> int n

let pr_in_out_modules = function
  | SearchInside l -> spc() ++ str"inside" ++ spc() ++ prlist_with_sep sep pr_module l
  | SearchOutside [] -> mt()
  | SearchOutside l -> spc() ++ str"outside" ++ spc() ++ prlist_with_sep sep pr_module l

let pr_search_about (b,c) =
  (if b then str "-" else mt()) ++
  match c with
  | SearchSubPattern p -> pr_constr_pattern_expr p
  | SearchString (s,sc) -> qs s ++ pr_opt (fun sc -> str "%" ++ str sc) sc

let pr_search a b pr_p = match a with
  | SearchHead c -> str"Search" ++ spc() ++ pr_p c ++ pr_in_out_modules b
  | SearchPattern c -> str"SearchPattern" ++ spc() ++ pr_p c ++ pr_in_out_modules b
  | SearchRewrite c -> str"SearchRewrite" ++ spc() ++ pr_p c ++ pr_in_out_modules b
  | SearchAbout sl -> str"SearchAbout" ++ spc() ++ str "[" ++ prlist_with_sep spc pr_search_about sl ++ str "]" ++ pr_in_out_modules b

let pr_locality_full = function
  | None -> mt()
  | Some true -> str"Local "
  | Some false -> str"Global "
let pr_locality local = if local then str "Local " else str ""
let pr_non_locality local = if local then str "" else str "Global "
let pr_section_locality local =
  if Lib.sections_are_opened () && not local then str "Global "
  else if not (Lib.sections_are_opened ()) && local then str "Local "
  else mt ()

let pr_explanation (e,b,f) =
  let a = match e with
  | ExplByPos (n,_) -> anomaly "No more supported"
  | ExplByName id -> pr_id id in
  let a = if f then str"!" ++ a else a in
    if b then str "[" ++ a ++ str "]" else a

let pr_class_rawexpr = function
  | FunClass -> str"Funclass"
  | SortClass -> str"Sortclass"
  | RefClass qid -> pr_smart_global qid

let pr_option_ref_value = function
  | QualidRefValue id -> pr_reference id
  | StringRefValue s -> qs s

let pr_printoption table b =
  prlist_with_sep spc str table ++
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
        str "Resolve " ++ prlist_with_sep sep
	  (fun (pri, _, c) -> pr_c c ++
	    match pri with Some x -> spc () ++ str"(" ++ int x ++ str")" | None -> mt ())
	  l
    | HintsImmediate l ->
        str"Immediate" ++ spc() ++ prlist_with_sep sep pr_c l
    | HintsUnfold l ->
        str "Unfold " ++ prlist_with_sep sep pr_reference l
    | HintsTransparency (l, b) ->
        str (if b then "Transparent " else "Opaque ") ++ prlist_with_sep sep
	  pr_reference l
    | HintsConstructors c ->
        str"Constructors" ++ spc() ++ prlist_with_sep spc pr_reference c
    | HintsExtern (n,c,tac) ->
	let pat = match c with None -> mt () | Some pat -> pr_pat pat in
          str "Extern" ++ spc() ++ int n ++ spc() ++ pat ++ str" =>" ++
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

let rec pr_module_ast pr_c = function
  | CMident qid -> spc () ++ pr_located pr_qualid qid
  | CMwith (mty,decl) ->
      let m = pr_module_ast pr_c mty in
      let p = pr_with_declaration pr_c decl in
      m ++ spc() ++ str"with" ++ spc() ++ p
  | CMapply (me1,(CMident _ as me2)) ->
      pr_module_ast pr_c me1 ++ spc() ++ pr_module_ast pr_c me2
  | CMapply (me1,me2) ->
      pr_module_ast pr_c me1 ++ spc() ++
      hov 1 (str"(" ++ pr_module_ast pr_c me2 ++ str")")

let pr_module_ast_inl pr_c (mast,b) =
  (if b then mt () else str "!") ++ pr_module_ast pr_c mast

let pr_of_module_type prc = function
  | Enforce mty -> str ":" ++ pr_module_ast_inl prc mty
  | Check mtys ->
      prlist_strict (fun m -> str "<:" ++ pr_module_ast_inl prc m) mtys

let pr_require_token = function
  | Some true -> str "Export "
  | Some false -> str "Import "
  | None -> mt()

let pr_module_vardecls pr_c (export,idl,(mty,inl)) =
  let m = pr_module_ast pr_c mty in
  (* Update the Nametab for interpreting the body of module/modtype *)
  let lib_dir = Lib.library_dp() in
  List.iter (fun (_,id) ->
    Declaremods.process_module_bindings [id]
      [make_mbid lib_dir (string_of_id id),
       (Modintern.interp_modtype (Global.env()) mty, inl)]) idl;
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

let pr_type_option pr_c = function
  | CHole (loc, k) -> mt()
  | _ as c -> brk(0,2) ++ str":" ++ pr_c c

let pr_decl_notation prc ((loc,ntn),c,scopt) =
  fnl () ++ str "where " ++ qs ntn ++ str " := " ++ prc c ++
  pr_opt (fun sc -> str ": " ++ str sc) scopt

let pr_vbinders l =
  hv 0 (pr_binders l)

let pr_binders_arg =
  pr_ne_sep spc pr_binders

let pr_and_type_binders_arg bl =
  pr_binders_arg bl

let names_of_binder = function
  | LocalRawAssum (nal,_,_) -> nal
  | LocalRawDef (_,_) -> []

let pr_guard_annot bl (n,ro) =
  match n with
  | None -> mt ()
  | Some (loc, id) ->
      match (ro : Topconstr.recursion_order_expr) with
      | CStructRec ->
          let ids = List.flatten (List.map names_of_binder bl) in
	  if List.length ids > 1 then
	    spc() ++ str "{struct " ++ pr_id id ++ str"}"
	  else mt()
      | CWfRec c ->
	  spc() ++ str "{wf " ++ pr_lconstr_expr c ++ spc() ++
	  pr_id id ++ str"}"
      | CMeasureRec (m,r) ->
	  spc() ++ str "{measure " ++ pr_lconstr_expr m ++ spc() ++
	  pr_id id ++ (match r with None -> mt() | Some r -> str" on " ++
	    pr_lconstr_expr r) ++ str"}"

let pr_onescheme (idop,schem) =
  match schem with
  | InductionScheme (dep,ind,s) ->
    (match idop with
      | Some id -> hov 0 (pr_lident id ++ str" :=") ++ spc()
      | None -> spc ()
    ) ++
    hov 0 ((if dep then str"Induction for" else str"Minimality for")
    ++ spc() ++ pr_smart_global ind) ++ spc() ++
    hov 0 (str"Sort" ++ spc() ++ pr_rawsort s)
  | CaseScheme (dep,ind,s) ->
    (match idop with
      | Some id -> hov 0 (pr_lident id ++ str" :=") ++ spc()
      | None -> spc ()
    ) ++
    hov 0 ((if dep then str"Elimination for" else str"Case for")
    ++ spc() ++ pr_smart_global ind) ++ spc() ++
    hov 0 (str"Sort" ++ spc() ++ pr_rawsort s)
  | EqualityScheme ind ->
    (match idop with
      | Some id -> hov 0 (pr_lident id ++ str" :=") ++ spc()
      | None -> spc()
    ) ++
    hov 0 (str"Equality for")
    ++ spc() ++ pr_smart_global ind

let begin_of_inductive = function
    [] -> 0
  | (_,((loc,_),_))::_ -> fst (unloc loc)

let pr_class_rawexpr = function
  | FunClass -> str"Funclass"
  | SortClass -> str"Sortclass"
  | RefClass qid -> pr_smart_global qid

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
      anomaly "Don't know how to beautify a local conjecture"

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

let pr_statement head (id,(bl,c,guard)) =
  assert (id<>None);
  hov 0
    (head ++ pr_lident (Option.get id) ++ spc() ++
    (match bl with [] -> mt() | _ -> pr_binders bl ++ spc()) ++
    pr_opt (pr_guard_annot bl) guard ++
    str":" ++ pr_spc_lconstr c)

(**************************************)
(* Pretty printer for vernac commands *)
(**************************************)
let make_pr_vernac pr_constr pr_lconstr =

let pr_constrarg c = spc () ++ pr_constr c in
let pr_lconstrarg c = spc () ++ pr_lconstr c in
let pr_intarg n = spc () ++ int n in
(* let pr_lident_constr sep (i,c) = pr_lident i ++ sep ++ pr_constrarg c in *)
let pr_record_field (x, ntn) =
  let prx = match x with
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
    prx ++ prlist (pr_decl_notation pr_constr) ntn
in
let pr_record_decl b c fs =
    pr_opt pr_lident c ++ str"{"  ++
    hv 0 (prlist_with_sep pr_semicolon pr_record_field fs ++ str"}")
in

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
  | VernacUndoTo i -> str"Undo" ++ spc() ++ str"To" ++ pr_intarg i
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
  | VernacRemoveName id -> str"Remove" ++ spc() ++ pr_lident id
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
  | VernacTimeout(n,v) -> str"Timeout " ++ int n ++ spc() ++ pr_vernac v
  | VernacFail v -> str"Fail" ++ spc() ++ pr_vernac v

  (* Syntax *)
  | VernacTacticNotation (n,r,e) -> pr_grammar_tactic_rule n ("",r,e)
  | VernacOpenCloseScope (local,opening,sc) ->
      pr_section_locality local ++ 
      str (if opening then "Open " else "Close ") ++
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
    pr_section_locality local ++ str"Arguments Scope" ++ spc() ++ 
    pr_smart_global q
    ++ spc() ++ str"[" ++ prlist_with_sep sep pr_opt_scope scl ++ str"]"
  | VernacInfix (local,((_,s),mv),q,sn) -> (* A Verifier *)
      hov 0 (hov 0 (pr_locality local ++ str"Infix "
      ++ qs s ++ str " :=" ++ pr_constrarg q) ++
      pr_syntax_modifiers mv ++
      (match sn with
    | None -> mt()
    | Some sc -> spc() ++ str":" ++ spc() ++ str sc))
  | VernacNotation (local,c,((_,s),l),opt) ->
      let ps =
	let n = String.length s in
	if n > 2 & s.[0] = '\'' & s.[n-1] = '\''
	then
          let s' = String.sub s 1 (n-2) in
          if String.contains s' '\'' then qs s else str s'
	else qs s in
      hov 2 (pr_locality local ++ str"Notation" ++ spc() ++ ps ++
      str " :=" ++ pr_constrarg c ++ pr_syntax_modifiers l ++
      (match opt with
        | None -> mt()
        | Some sc -> str" :" ++ spc() ++ str sc))
  | VernacSyntaxExtension (local,(s,l)) ->
      pr_locality local ++ str"Reserved Notation" ++ spc() ++ pr_located qs s ++
      pr_syntax_modifiers l

  (* Gallina *)
  | VernacDefinition (d,id,b,f) -> (* A verifier... *)
      let pr_def_token dk = str (string_of_definition_kind dk) in
      let pr_reduce = function
        | None -> mt()
        | Some r ->
            str"Eval" ++ spc() ++
            pr_red_expr (pr_constr, pr_lconstr, pr_smart_global, pr_constr) r ++
            str" in" ++ spc() in
      let pr_def_body = function
        | DefineBody (bl,red,body,d) ->
            let ty = match d with
              | None -> mt()
              | Some ty -> spc() ++ str":" ++ pr_spc_lconstr ty
	    in
            (pr_binders_arg bl,ty,Some (pr_reduce red ++ pr_lconstr body))
        | ProveBody (bl,t) ->
            (pr_binders_arg bl, str" :" ++ pr_spc_lconstr t, None) in
      let (binds,typ,c) = pr_def_body b in
      hov 2 (pr_def_token d ++ spc() ++ pr_lident id ++ binds ++ typ ++
      (match c with
        | None -> mt()
        | Some cc -> str" :=" ++ spc() ++ cc))

  | VernacStartTheoremProof (ki,l,_,_) ->
      hov 1 (pr_statement (pr_thm_token ki) (List.hd l) ++
             prlist (pr_statement (spc () ++ str "with")) (List.tl l))

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
  | VernacInductive (f,i,l) ->

      let pr_constructor (coe,(id,c)) =
        hov 2 (pr_lident id ++ str" " ++
               (if coe then str":>" else str":") ++
                pr_spc_lconstr c) in
      let pr_constructor_list b l = match l with
        | Constructors [] -> mt()
        | Constructors l ->
            pr_com_at (begin_of_inductive l) ++
            fnl() ++
            str (if List.length l = 1 then "   " else " | ") ++
            prlist_with_sep (fun _ -> fnl() ++ str" | ") pr_constructor l
       | RecordDecl (c,fs) ->
	    spc() ++
	    pr_record_decl b c fs in
      let pr_oneind key (((coe,id),indpar,s,k,lc),ntn) =
	hov 0 (
	    str key ++ spc() ++
	      (if i then str"Infer " else str"") ++
              (if coe then str"> " else str"") ++ pr_lident id ++
              pr_and_type_binders_arg indpar ++ spc() ++
	      Option.cata (fun s -> str":" ++ spc() ++ pr_lconstr_expr s) (mt()) s ++
	      str" :=") ++ pr_constructor_list k lc ++
	    prlist (pr_decl_notation pr_constr) ntn
      in
      let key =
        let (_,_,_,k,_),_ = List.hd l in
	match k with Record -> "Record" | Structure -> "Structure"
	  | Inductive_kw -> "Inductive" | CoInductive -> "CoInductive"
	  | Class b -> if b then "Definitional Class" else "Class" in
      hov 1 (pr_oneind key (List.hd l)) ++
      (prlist (fun ind -> fnl() ++ hov 1 (pr_oneind "with" ind)) (List.tl l))


  | VernacFixpoint (recs,b) ->
      let pr_onerec = function
        | ((loc,id),ro,bl,type_,def),ntn ->
            let annot = pr_guard_annot bl ro in
            pr_id id ++ pr_binders_arg bl ++ annot ++ spc()
            ++ pr_type_option (fun c -> spc() ++ pr_lconstr_expr c) type_
            ++ pr_opt (fun def -> str" :=" ++ brk(1,2) ++ pr_lconstr def) def ++
	    prlist (pr_decl_notation pr_constr) ntn
      in
      let start = if b then "Boxed Fixpoint" else "Fixpoint" in
      hov 0 (str start ++ spc() ++
        prlist_with_sep (fun _ -> fnl() ++ str"with ") pr_onerec recs)

  | VernacCoFixpoint (corecs,b) ->
      let pr_onecorec (((loc,id),bl,c,def),ntn) =
        pr_id id ++ spc() ++ pr_binders bl ++ spc() ++ str":" ++
        spc() ++ pr_lconstr_expr c ++
        pr_opt (fun def -> str" :=" ++ brk(1,2) ++ pr_lconstr def) def ++
	prlist (pr_decl_notation pr_constr) ntn
      in
      let start = if b then "Boxed CoFixpoint" else "CoFixpoint" in
      hov 0 (str start ++ spc() ++
      prlist_with_sep (fun _ -> fnl() ++ str"with ") pr_onecorec corecs)
  | VernacScheme l ->
      hov 2 (str"Scheme" ++ spc() ++
             prlist_with_sep (fun _ -> fnl() ++ str"with ") pr_onescheme l)
  | VernacCombinedScheme (id, l) ->
      hov 2 (str"Combined Scheme" ++ spc() ++
	       pr_lident id ++ spc() ++ str"from" ++ spc() ++
	       prlist_with_sep (fun _ -> fnl() ++ str", ") pr_lident l)


  (* Gallina extensions *)
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
  | VernacCanonical q -> str"Canonical Structure" ++ spc() ++ pr_smart_global q
  | VernacCoercion (s,id,c1,c2) ->
      hov 1 (
	str"Coercion" ++ (match s with | Local -> spc() ++
	  str"Local" ++ spc() | Global -> spc()) ++
	pr_smart_global id ++ spc() ++ str":" ++ spc() ++ pr_class_rawexpr c1 ++
	spc() ++ str">->" ++ spc() ++ pr_class_rawexpr c2)
  | VernacIdentityCoercion (s,id,c1,c2) ->
      hov 1 (
	str"Identity Coercion" ++ (match s with | Local -> spc() ++
	  str"Local" ++ spc() | Global -> spc()) ++ pr_lident id ++
	spc() ++ str":" ++ spc() ++ pr_class_rawexpr c1 ++ spc() ++ str">->" ++
	spc() ++ pr_class_rawexpr c2)


(*   | VernacClass (id, par, ar, sup, props) -> *)
(*       hov 1 ( *)
(* 	str"Class" ++ spc () ++ pr_lident id ++ *)
(* (\* 	  prlist_with_sep (spc) (pr_lident_constr (spc() ++ str ":" ++ spc())) par ++  *\) *)
(* 	  pr_and_type_binders_arg par ++ *)
(* 	  (match ar with Some ar -> spc () ++ str":" ++ spc() ++ pr_rawsort (snd ar) | None -> mt()) ++ *)
(* 	  spc () ++ str":=" ++ spc () ++ *)
(* 	  prlist_with_sep (fun () -> str";" ++ spc())  *)
(* 	  (fun (lid,oc,c) -> pr_lident_constr ((if oc then str" :>" else str" :") ++ spc()) (lid,c)) props ) *)

 | VernacInstance (abst,glob, sup, (instid, bk, cl), props, pri) ->
     hov 1 (
       pr_non_locality (not glob) ++
       (if abst then str"Declare " else mt ()) ++
       str"Instance" ++ spc () ++
	 pr_and_type_binders_arg sup ++
	 str"=>" ++ spc () ++
	 (match snd instid with Name id -> pr_lident (fst instid, id) ++ spc () ++ str":" ++ spc () | Anonymous -> mt ()) ++
	 pr_constr_expr cl ++ spc () ++
	 spc () ++ str":=" ++ spc () ++
	 pr_constr_expr props)

 | VernacContext l ->
     hov 1 (
       str"Context" ++ spc () ++ str"[" ++ spc () ++
	 pr_and_type_binders_arg l ++ spc () ++ str "]")


 | VernacDeclareInstance (glob, id) ->
     hov 1 (pr_non_locality (not glob) ++
	       str"Existing" ++ spc () ++ str"Instance" ++ spc () ++ pr_reference id)

 | VernacDeclareClass id ->
     hov 1 (str"Existing" ++ spc () ++ str"Class" ++ spc () ++ pr_reference id)

  (* Modules and Module Types *)
  | VernacDefineModule (export,m,bl,tys,bd) ->
      let b = pr_module_binders_list bl pr_lconstr in
      hov 2 (str"Module" ++ spc() ++ pr_require_token export ++
               pr_lident m ++ b ++
               pr_of_module_type pr_lconstr tys ++
	       (if bd = [] then mt () else str ":= ") ++
	       prlist_with_sep (fun () -> str " <+ ")
	        (pr_module_ast_inl pr_lconstr) bd)
  | VernacDeclareModule (export,id,bl,m1) ->
      let b = pr_module_binders_list bl pr_lconstr in
	hov 2 (str"Declare Module" ++ spc() ++ pr_require_token export ++
             pr_lident id ++ b ++
             pr_module_ast_inl pr_lconstr m1)
  | VernacDeclareModuleType (id,bl,tyl,m) ->
      let b = pr_module_binders_list bl pr_lconstr in
      let pr_mt = pr_module_ast_inl pr_lconstr in
	hov 2 (str"Module Type " ++ pr_lident id ++ b ++
		 prlist_strict (fun m -> str " <: " ++ pr_mt m) tyl ++
		 (if m = [] then mt () else str ":= ") ++
		 prlist_with_sep (fun () -> str " <+ ") pr_mt m)
  | VernacInclude (mexprs) ->
      let pr_m = pr_module_ast_inl pr_lconstr in
      hov 2 (str"Include " ++
	     prlist_with_sep (fun () -> str " <+ ") pr_m mexprs)
  (* Solving *)
  | VernacSolve (i,b,tac,deftac) ->
      (if i = 1 then mt() else int i ++ str ": ") ++
      (match b with None -> mt () | Some Dash -> str"-" | Some Star -> str"*" | Some Plus -> str"+") ++
      pr_raw_tactic tac
      ++ (try if deftac then str ".." else mt ()
      with UserError _|Stdpp.Exc_located _ -> mt())

  | VernacSolveExistential (i,c) ->
      str"Existential " ++ int i ++ pr_lconstrarg c

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
  | VernacDeclareMLModule (local, l) ->
      pr_locality local ++
      hov 2 (str"Declare ML Module" ++ spc() ++ prlist_with_sep sep qs l)
  | VernacChdir s -> str"Cd" ++ pr_opt qs s

  (* Commands *)
  | VernacDeclareTacticDefinition (local,rc,l) ->
      let pr_tac_body (id, redef, body) =
        let idl, body =
          match body with
	    | Tacexpr.TacFun (idl,b) -> idl,b
            | _ -> [], body in
        pr_ltac_id id ++
	prlist (function None -> str " _"
                       | Some id -> spc () ++ pr_id id) idl
	++ (if redef then str" ::=" else str" :=") ++ brk(1,1) ++
	let idl = List.map Option.get (List.filter (fun x -> not (x=None)) idl)in
        pr_raw_tactic_env
	  (idl @ List.map coerce_reference_to_id
	    (List.map (fun (x, _, _) -> x) (List.filter (fun (_, redef, _) -> not redef) l)))
	  (Global.env())
	  body in
      hov 1
        (pr_locality local ++ str "Ltac " ++
        prlist_with_sep (fun () -> fnl() ++ str"with ") pr_tac_body l)
  | VernacCreateHintDb (local,dbname,b) ->
      hov 1 (pr_locality local ++ str "Create " ++ str "HintDb " ++ 
		str dbname ++ (if b then str" discriminated" else mt ()))
  | VernacHints (local,dbnames,h) ->
      pr_hints local dbnames h pr_constr pr_constr_pattern_expr
  | VernacSyntacticDefinition (id,(ids,c),local,onlyparsing) ->
      hov 2
        (pr_locality local ++ str"Notation " ++ pr_lident id ++
	 prlist_with_sep spc pr_id ids ++ str" :=" ++ pr_constrarg c ++
         pr_syntax_modifiers (if onlyparsing then [SetOnlyParsing] else []))
  | VernacDeclareImplicits (local,q,None) ->
      hov 2 (pr_section_locality local ++ str"Implicit Arguments" ++ spc() ++ 
	pr_smart_global q)
  | VernacDeclareImplicits (local,q,Some imps) ->
      hov 1 (pr_section_locality local ++ str"Implicit Arguments " ++ 
	spc() ++ pr_smart_global q ++ spc() ++
	str"[" ++ prlist_with_sep sep pr_explanation imps ++ str"]")
  | VernacReserve bl ->
      let n = List.length (List.flatten (List.map fst bl)) in
      hov 2 (str"Implicit Type" ++
        str (if n > 1 then "s " else " ") ++
        pr_ne_params_list pr_lconstr_expr (List.map (fun sb -> false,sb) bl))
  | VernacGeneralizable (local, g) ->
      hov 1 (pr_locality local ++ str"Generalizable Variable" ++
		match g with
		| None -> str "s none"
		| Some [] -> str "s all"
		| Some idl ->
		    str (if List.length idl > 1 then "s " else " ") ++
		      prlist_with_sep spc pr_lident idl)
  | VernacSetOpacity(b,[k,l]) when k=Conv_oracle.transparent ->
      hov 1 (str"Transparent" ++ pr_non_locality b ++
             spc() ++ prlist_with_sep sep pr_smart_global l)
  | VernacSetOpacity(b,[Conv_oracle.Opaque,l]) ->
      hov 1 (str"Opaque" ++ pr_non_locality b ++
             spc() ++ prlist_with_sep sep pr_smart_global l)
  | VernacSetOpacity (local,l) ->
      let pr_lev = function
          Conv_oracle.Opaque -> str"opaque"
        | Conv_oracle.Expand -> str"expand"
        | l when l = Conv_oracle.transparent -> str"transparent"
        | Conv_oracle.Level n -> int n in
      let pr_line (l,q) =
        hov 2 (pr_lev l ++ spc() ++
               str"[" ++ prlist_with_sep sep pr_smart_global q ++ str"]") in
      hov 1 (pr_non_locality local ++ str"Strategy" ++ spc() ++
             hv 0 (prlist_with_sep sep pr_line l))
  | VernacUnsetOption (l,na) ->
      hov 1 (pr_locality_full l ++ str"Unset" ++ spc() ++ pr_printoption na None)
  | VernacSetOption (l,na,v) ->
      hov 2 (pr_locality_full l ++ str"Set" ++ spc() ++ pr_set_option na v)
  | VernacAddOption (na,l) -> hov 2 (str"Add" ++ spc() ++ pr_printoption na (Some l))
  | VernacRemoveOption (na,l) -> hov 2 (str"Remove" ++ spc() ++ pr_printoption na (Some l))
  | VernacMemOption (na,l) -> hov 2 (str"Test" ++ spc() ++ pr_printoption na (Some l))
  | VernacPrintOption na -> hov 2 (str"Test" ++ spc() ++ pr_printoption na None)
  | VernacCheckMayEval (r,io,c) ->
      let pr_mayeval r c = match r with
      | Some r0 ->
          hov 2 (str"Eval" ++ spc() ++
          pr_red_expr (pr_constr,pr_lconstr,pr_smart_global, pr_constr) r0 ++
          spc() ++ str"in" ++ spc () ++ pr_constr c)
      | None -> hov 2 (str"Check" ++ spc() ++ pr_constr c)
      in
      (if io = None then mt() else int (Option.get io) ++ str ": ") ++
      pr_mayeval r c
  | VernacGlobalCheck c -> hov 2 (str"Type" ++ pr_constrarg c)
  | VernacDeclareReduction (b,s,r) ->
     pr_locality b ++ str "Declare Reduction " ++ str s ++ str " := " ++
     pr_red_expr (pr_constr,pr_lconstr,pr_smart_global, pr_constr) r
  | VernacPrint p ->
      let pr_printable = function
	| PrintFullContext -> str"Print All"
	| PrintSectionContext s ->
            str"Print Section" ++ spc() ++ Libnames.pr_reference s
	| PrintGrammar ent ->
            str"Print Grammar" ++ spc() ++ str ent
	| PrintLoadPath dir -> str"Print LoadPath" ++ pr_opt pr_dirpath dir
	| PrintModules -> str"Print Modules"
	| PrintMLLoadPath -> str"Print ML Path"
	| PrintMLModules -> str"Print ML Modules"
	| PrintGraph -> str"Print Graph"
	| PrintClasses -> str"Print Classes"
	| PrintTypeClasses -> str"Print TypeClasses"
	| PrintInstances qid -> str"Print Instances" ++ spc () ++ pr_smart_global qid
	| PrintLtac qid -> str"Print Ltac" ++ spc() ++ pr_reference qid
	| PrintCoercions -> str"Print Coercions"
	| PrintCoercionPaths (s,t) -> str"Print Coercion Paths" ++ spc() ++ pr_class_rawexpr s ++ spc() ++ pr_class_rawexpr t
	| PrintCanonicalConversions -> str"Print Canonical Structures"
	| PrintTables -> str"Print Tables"
	| PrintHintGoal -> str"Print Hint"
	| PrintHint qid -> str"Print Hint" ++ spc() ++ pr_smart_global qid
	| PrintHintDb -> str"Print Hint *"
	| PrintHintDbName s -> str"Print HintDb" ++ spc() ++ str s
	| PrintRewriteHintDbName s -> str"Print Rewrite HintDb" ++ spc() ++ str s
	| PrintUniverses fopt -> str"Dump Universes" ++ pr_opt str fopt
	| PrintName qid -> str"Print" ++ spc()  ++ pr_smart_global qid
	| PrintModuleType qid -> str"Print Module Type" ++ spc() ++ pr_reference qid
	| PrintModule qid -> str"Print Module" ++ spc() ++ pr_reference qid
	| PrintInspect n -> str"Inspect" ++ spc() ++ int n
	| PrintScopes -> str"Print Scopes"
	| PrintScope s -> str"Print Scope" ++ spc() ++ str s
	| PrintVisibility s -> str"Print Visibility" ++ pr_opt str s
	| PrintAbout qid -> str"About" ++ spc()  ++ pr_smart_global qid
	| PrintImplicit qid -> str"Print Implicit" ++ spc()  ++ pr_smart_global qid
(* spiwack: command printing all the axioms and section variables used in a
         term *)
	| PrintAssumptions (b,qid) -> (if b then str"Print Assumptions" else str"Print Opaque Dependencies")
	    ++ spc() ++ pr_smart_global qid
      in pr_printable p
  | VernacSearch (sea,sea_r) -> pr_search sea sea_r pr_constr_pattern_expr
  | VernacLocate loc ->
      let pr_locate =function
	| LocateTerm qid -> pr_smart_global qid
	| LocateFile f -> str"File" ++ spc() ++ qs f
	| LocateLibrary qid -> str"Library" ++ spc () ++ pr_module qid
	| LocateModule qid -> str"Module" ++ spc () ++ pr_module qid
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

  | VernacProofMode s -> str ("Proof Mode "^s)
  | VernacSubproof None -> str "BeginSubproof"
  | VernacSubproof (Some i) -> str "BeginSubproof " ++ pr_int i
  | VernacEndSubproof -> str "EndSubproof"

and pr_extend s cl =
  let pr_arg a =
    try pr_gen (Global.env()) a
    with Failure _ -> str ("<error in "^s^">") in
  try
    let rls = List.assoc s (Egrammar.get_extend_vernac_grammars()) in
    let rl = match_vernac_rule (List.map Genarg.genarg_tag cl) rls in
    let start,rl,cl =
      match rl with
      | Egrammar.GramTerminal s :: rl -> str s, rl, cl
      | Egrammar.GramNonTerminal _ :: rl -> pr_arg (List.hd cl), rl, List.tl cl
      | [] -> anomaly "Empty entry" in
    let (pp,_) =
      List.fold_left
        (fun (strm,args) pi ->
          let pp,args = match pi with
          | Egrammar.GramNonTerminal _ -> (pr_arg (List.hd args), List.tl args)
          | Egrammar.GramTerminal s -> (str s, args) in
          (strm ++ spc() ++ pp), args)
        (start,cl) rl in
    hov 1 pp
  with Not_found ->
    hov 1 (str ("TODO("^s) ++ prlist_with_sep sep pr_arg cl ++ str ")")

in pr_vernac

let pr_vernac v = make_pr_vernac pr_constr_expr pr_lconstr_expr v ++ sep_end ()
