(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Names

open Errors
open Util
open Extend
open Vernacexpr
open Pputils
open Ppconstr
open Pptactic
open Libnames
open Constrexpr
open Constrexpr_ops
open Decl_kinds

let pr_spc_lconstr = pr_sep_com spc pr_lconstr_expr

let pr_lident (loc,id) =
  if Loc.is_ghost loc then
    let (b,_) = Loc.unloc loc in
    pr_located pr_id (Loc.make_loc (b,b+String.length(Id.to_string id)),id)
  else pr_id id

let string_of_fqid fqid =
 String.concat "." (List.map Id.to_string fqid)

let pr_fqid fqid = str (string_of_fqid fqid)

let pr_lfqid (loc,fqid) =
  if Loc.is_ghost loc then
   let (b,_) = Loc.unloc loc in
    pr_located pr_fqid (Loc.make_loc (b,b+String.length(string_of_fqid fqid)),fqid)
  else
   pr_fqid fqid

let pr_lname = function
    (loc,Name id) -> pr_lident (loc,id)
  | lna -> pr_located pr_name lna

let pr_smart_global = pr_or_by_notation pr_reference

let pr_ltac_ref = Libnames.pr_reference

let pr_module = Libnames.pr_reference

let pr_import_module = Libnames.pr_reference

let sep_end = function
  | VernacBullet _
  | VernacSubproof None
  | VernacEndSubproof -> str""
  | _ -> str"."

let pr_gen t =
  pr_raw_generic
    pr_constr_expr
    pr_lconstr_expr
    pr_raw_tactic_level
    pr_constr_expr
    pr_reference t

let sep = fun _ -> spc()
let sep_v2 = fun _ -> str"," ++ spc()

let pr_ne_sep sep pr = function
    [] -> mt()
  | l -> sep() ++ pr l

let pr_set_entry_type = function
  | ETName -> str"ident"
  | ETReference -> str"global"
  | ETPattern -> str"pattern"
  | ETConstr _ -> str"constr"
  | ETOther (_,e) -> str e
  | ETBigint -> str "bigint"
  | ETBinder true -> str "binder"
  | ETBinder false -> str "closed binder"
  | ETBinderList _ | ETConstrList _ -> failwith "Internal entry type"

let strip_meta id =
  let s = Id.to_string id in
  if s.[0] == '$' then Id.of_string (String.sub s 1 (String.length s - 1))
  else id

let pr_production_item = function
  | TacNonTerm (loc,nt,Some (p,sep)) ->
      let pp_sep = if not (String.is_empty sep) then str "," ++ quote (str sep) else mt () in
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
  | SearchHead c -> str"SearchHead" ++ spc() ++ pr_p c ++ pr_in_out_modules b
  | SearchPattern c -> str"SearchPattern" ++ spc() ++ pr_p c ++ pr_in_out_modules b
  | SearchRewrite c -> str"SearchRewrite" ++ spc() ++ pr_p c ++ pr_in_out_modules b
  | SearchAbout sl -> str"Search" ++ spc() ++ prlist_with_sep spc pr_search_about sl ++ pr_in_out_modules b

let pr_locality local = if local then str "Local" else str "Global"

let pr_explanation (e,b,f) =
  let a = match e with
  | ExplByPos (n,_) -> anomaly (Pp.str "No more supported")
  | ExplByName id -> pr_id id in
  let a = if f then str"!" ++ a else a in
    if b then str "[" ++ a ++ str "]" else a

let pr_option_ref_value = function
  | QualidRefValue id -> pr_reference id
  | StringRefValue s -> qs s

let pr_printoption table b =
  prlist_with_sep spc str table ++
  pr_opt (prlist_with_sep sep pr_option_ref_value) b

let pr_set_option a b =
  let pr_opt_value = function
    | IntValue None -> assert false
    (* This should not happen because of the grammar *)
    | IntValue (Some n) -> spc() ++ int n
    | StringValue s -> spc() ++ str s
    | BoolValue b -> mt()
  in pr_printoption a None ++ pr_opt_value b

let pr_topcmd _ = str"(* <Warning> : No printer for toplevel commands *)"

let pr_opt_hintbases l = match l with
  | [] -> mt()
  | _ as z -> str":" ++ spc() ++ prlist_with_sep sep str z

let pr_reference_or_constr pr_c = function
  | HintsReference r -> pr_reference r
  | HintsConstr c -> pr_c c

let pr_hints db h pr_c pr_pat =
  let opth = pr_opt_hintbases db  in
  let pph =
    match h with
    | HintsResolve l ->
        str "Resolve " ++ prlist_with_sep sep
	  (fun (pri, _, c) -> pr_reference_or_constr pr_c c ++
	    match pri with Some x -> spc () ++ str"(" ++ int x ++ str")" | None -> mt ())
	  l
    | HintsImmediate l ->
        str"Immediate" ++ spc() ++ 
	  prlist_with_sep sep (fun c -> pr_reference_or_constr pr_c c) l
    | HintsUnfold l ->
        str "Unfold " ++ prlist_with_sep sep pr_reference l
    | HintsTransparency (l, b) ->
        str (if b then "Transparent " else "Opaque ") ++ prlist_with_sep sep
	  pr_reference l
    | HintsMode (m, l) ->
        str "Mode " ++ pr_reference m ++ spc() ++ prlist_with_sep spc 
	  (fun b -> if b then str"+" else str"-") l
    | HintsConstructors c ->
        str"Constructors" ++ spc() ++ prlist_with_sep spc pr_reference c
    | HintsExtern (n,c,tac) ->
	let pat = match c with None -> mt () | Some pat -> pr_pat pat in
          str "Extern" ++ spc() ++ int n ++ spc() ++ pat ++ str" =>" ++
          spc() ++ pr_raw_tactic tac
  in
  hov 2 (str"Hint "++ pph ++ opth)

let pr_with_declaration pr_c = function
  | CWith_Definition (id,c) ->
      let p = pr_c c in
      str"Definition" ++ spc() ++ pr_lfqid id ++ str" := " ++ p
  | CWith_Module (id,qid) ->
      str"Module" ++ spc() ++ pr_lfqid id ++ str" := " ++
      pr_located pr_qualid qid

let rec pr_module_ast leading_space pr_c = function
  | CMident qid ->
      if leading_space then
        spc () ++ pr_located pr_qualid qid
      else
        pr_located pr_qualid qid
  | CMwith (_,mty,decl) ->
      let m = pr_module_ast leading_space pr_c mty in
      let p = pr_with_declaration pr_c decl in
      m ++ spc() ++ str"with" ++ spc() ++ p
  | CMapply (_,me1,(CMident _ as me2)) ->
      pr_module_ast leading_space pr_c me1 ++ spc() ++ pr_module_ast false pr_c me2
  | CMapply (_,me1,me2) ->
      pr_module_ast leading_space pr_c me1 ++ spc() ++
      hov 1 (str"(" ++ pr_module_ast false pr_c me2 ++ str")")

let pr_inline = function
  | DefaultInline -> mt ()
  | NoInline -> str "[no inline]"
  | InlineAt i -> str "[inline at level " ++ int i ++ str "]"

let pr_module_ast_inl leading_space pr_c (mast,inl) =
  pr_module_ast leading_space pr_c mast ++ pr_inline inl

let pr_of_module_type prc = function
  | Enforce mty -> str ":" ++ pr_module_ast_inl true prc mty
  | Check mtys ->
      prlist_strict (fun m -> str "<:" ++ pr_module_ast_inl true prc m) mtys

let pr_require_token = function
  | Some true -> str "Export "
  | Some false -> str "Import "
  | None -> mt()

let pr_module_vardecls pr_c (export,idl,(mty,inl)) =
  let m = pr_module_ast true pr_c mty in
  spc() ++
  hov 1 (str"(" ++ pr_require_token export ++
  prlist_with_sep spc pr_lident idl ++ str":" ++ m ++ str")")

let pr_module_binders l pr_c =
  prlist_strict (pr_module_vardecls pr_c) l

let pr_type_option pr_c = function
  | CHole (loc, k, Misctypes.IntroAnonymous, _) -> mt()
  | _ as c -> brk(0,2) ++ str" :" ++ pr_c c

let pr_decl_notation prc ((loc,ntn),c,scopt) =
  fnl () ++ str "where " ++ qs ntn ++ str " := " ++ prc c ++
  pr_opt (fun sc -> str ": " ++ str sc) scopt

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
    ++ spc() ++ pr_smart_global ind) ++ spc() ++
    hov 0 (str"Sort" ++ spc() ++ pr_glob_sort s)
  | CaseScheme (dep,ind,s) ->
    (match idop with
      | Some id -> hov 0 (pr_lident id ++ str" :=") ++ spc()
      | None -> spc ()
    ) ++
    hov 0 ((if dep then str"Elimination for" else str"Case for")
    ++ spc() ++ pr_smart_global ind) ++ spc() ++
    hov 0 (str"Sort" ++ spc() ++ pr_glob_sort s)
  | EqualityScheme ind ->
    (match idop with
      | Some id -> hov 0 (pr_lident id ++ str" :=") ++ spc()
      | None -> spc()
    ) ++
    hov 0 (str"Equality for")
    ++ spc() ++ pr_smart_global ind

let begin_of_inductive = function
    [] -> 0
  | (_,((loc,_),_))::_ -> fst (Loc.unloc loc)

let pr_class_rawexpr = function
  | FunClass -> str"Funclass"
  | SortClass -> str"Sortclass"
  | RefClass qid -> pr_smart_global qid

let pr_assumption_token many (l,a) =
  let l = match l with Some x -> x | None -> Decl_kinds.Global in
  match l, a with
  | (Discharge,Logical) ->
      str (if many then "Hypotheses" else "Hypothesis")
  | (Discharge,Definitional) ->
      str (if many then "Variables" else "Variable")
  | (Global,Logical) ->
      str (if many then "Axioms" else "Axiom")
  | (Global,Definitional) ->
      str (if many then "Parameters" else "Parameter")
  | (Local, Logical) ->
      str (if many then "Local Axioms" else "Local Axiom")
  | (Local,Definitional) ->
      str (if many then "Local Parameters" else "Local Parameter")
  | (Global,Conjectural) -> str"Conjecture"
  | ((Discharge | Local),Conjectural) ->
      anomaly (Pp.str "Don't know how to beautify a local conjecture")

let pr_params pr_c (xl,(c,t)) =
  hov 2 (prlist_with_sep sep pr_lident xl ++ spc() ++
         (if c then str":>" else str":" ++
         spc() ++ pr_c t))

let rec factorize = function
  | [] -> []
  | (c,(idl,t))::l ->
      match factorize l with
        | (xl,((c', t') as r))::l'
          when (c : bool) == c' && Pervasives.(=) t t' ->
          (** FIXME: we need equality on constr_expr *)
          (idl@xl,r)::l'
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

let pr_thm_token k = str (Kindops.string_of_theorem_kind k)

let pr_syntax_modifier = function
  | SetItemLevel (l,NextLevel) ->
      prlist_with_sep sep_v2 str l ++
      spc() ++ str"at next level"
  | SetItemLevel (l,NumLevel n) ->
      prlist_with_sep sep_v2 str l ++
      spc() ++ str"at level" ++ spc() ++ int n
  | SetLevel n -> str"at level" ++ spc() ++ int n
  | SetAssoc LeftA -> str"left associativity"
  | SetAssoc RightA -> str"right associativity"
  | SetAssoc NonA -> str"no associativity"
  | SetEntryType (x,typ) -> str x ++ spc() ++ pr_set_entry_type typ
  | SetOnlyParsing Flags.Current -> str"only parsing"
  | SetOnlyParsing v -> str("compat \"" ^ Flags.pr_version v ^ "\"")
  | SetFormat("text",s) -> str"format " ++ pr_located qs s
  | SetFormat(k,s) -> str"format " ++ qs k ++ spc() ++ pr_located qs s

let pr_syntax_modifiers = function
  | [] -> mt()
  | l -> spc() ++
      hov 1 (str"(" ++ prlist_with_sep sep_v2 pr_syntax_modifier l ++ str")")

let print_level n =
  if not (Int.equal n 0) then str " (at level " ++ int n ++ str ")" else mt ()

let pr_grammar_tactic_rule n (_,pil,t) =
  hov 2 (str "Tactic Notation" ++ print_level n ++ spc() ++
    hov 0 (prlist_with_sep sep pr_production_item pil ++
    spc() ++ str":=" ++ spc() ++ pr_raw_tactic t))

let pr_statement head (id,(bl,c,guard)) =
  assert (not (Option.is_empty id));
  hov 2
    (head ++ spc() ++ pr_lident (Option.get id) ++ spc() ++
    (match bl with [] -> mt() | _ -> pr_binders bl ++ spc()) ++
    pr_opt (pr_guard_annot pr_lconstr_expr bl) guard ++
    str":" ++ pr_spc_lconstr c)

let pr_priority = function
| None -> mt ()
| Some i -> spc () ++ str "|" ++ spc () ++ int i

(**************************************)
(* Pretty printer for vernac commands *)
(**************************************)
let make_pr_vernac pr_constr pr_lconstr =
let pr_constrarg c = spc () ++ pr_constr c in
let pr_lconstrarg c = spc () ++ pr_lconstr c in
let pr_intarg n = spc () ++ int n in
let pr_oc = function
    None -> str" :"
  | Some true -> str" :>"
  | Some false -> str" :>>"
in
let pr_record_field ((x, pri), ntn) =
  let prx = match x with
    | (oc,AssumExpr (id,t)) ->
	hov 1 (pr_lname id ++
	       pr_oc oc ++ spc() ++
	       pr_lconstr_expr t)
    | (oc,DefExpr(id,b,opt)) -> (match opt with
      | Some t ->
          hov 1 (pr_lname id ++
                 pr_oc oc ++ spc() ++
                 pr_lconstr_expr t ++ str" :=" ++ pr_lconstr b)
      | None ->
          hov 1 (pr_lname id ++ str" :=" ++ spc() ++
                    pr_lconstr b)) in
  let prpri = match pri with None -> mt() | Some i -> str "| " ++ int i in
    prx ++ prpri ++ prlist (pr_decl_notation pr_constr) ntn
in
let pr_record_decl b c fs =
    pr_opt pr_lident c ++ (if c = None then str"{" else str" {") ++
    hv 0 (prlist_with_sep pr_semicolon pr_record_field fs ++ str"}")
in

let pr_printable = function
| PrintFullContext -> str "Print All"
| PrintSectionContext s ->
    str "Print Section" ++ spc() ++ Libnames.pr_reference s
| PrintGrammar ent ->
    str "Print Grammar" ++ spc() ++ str ent
| PrintLoadPath dir -> str "Print LoadPath" ++ pr_opt pr_dirpath dir
| PrintModules -> str "Print Modules"
| PrintMLLoadPath -> str "Print ML Path"
| PrintMLModules -> str "Print ML Modules"
| PrintDebugGC -> str "Print ML GC"
| PrintGraph -> str "Print Graph"
| PrintClasses -> str "Print Classes"
| PrintTypeClasses -> str "Print TypeClasses"
| PrintInstances qid -> str "Print Instances" ++ spc () ++ pr_smart_global qid
| PrintLtac qid -> str "Print Ltac" ++ spc() ++ pr_ltac_ref qid
| PrintCoercions -> str "Print Coercions"
| PrintCoercionPaths (s,t) -> str "Print Coercion Paths" ++ spc() ++ pr_class_rawexpr s ++ spc() ++ pr_class_rawexpr t
| PrintCanonicalConversions -> str "Print Canonical Structures"
| PrintTables -> str "Print Tables"
| PrintHintGoal -> str "Print Hint"
| PrintHint qid -> str "Print Hint" ++ spc() ++ pr_smart_global qid
| PrintHintDb -> str "Print Hint *"
| PrintHintDbName s -> str "Print HintDb" ++ spc() ++ str s
| PrintRewriteHintDbName s -> str "Print Rewrite HintDb" ++ spc() ++ str s
| PrintUniverses (b, fopt) ->
  let cmd =
    if b then "Print Sorted Universes"
    else "Print Universes"
  in
  str cmd ++ pr_opt str fopt
| PrintName qid -> str "Print" ++ spc()  ++ pr_smart_global qid
| PrintModuleType qid -> str "Print Module Type" ++ spc() ++ pr_reference qid
| PrintModule qid -> str "Print Module" ++ spc() ++ pr_reference qid
| PrintInspect n -> str "Inspect" ++ spc() ++ int n
| PrintScopes -> str "Print Scopes"
| PrintScope s -> str "Print Scope" ++ spc() ++ str s
| PrintVisibility s -> str "Print Visibility" ++ pr_opt str s
| PrintAbout qid -> str "About" ++ spc()  ++ pr_smart_global qid
| PrintImplicit qid -> str "Print Implicit" ++ spc()  ++ pr_smart_global qid
(* spiwack: command printing all the axioms and section variables used in a
  term *)
| PrintAssumptions (b, t, qid) ->
  let cmd = match b, t with
  | true, true -> "Print All Dependencies"
  | true, false -> "Print Opaque Dependencies"
  | false, true -> "Print Transparent Dependencies"
  | false, false -> "Print Assumptions"
  in
  str cmd ++ spc() ++ pr_smart_global qid
| PrintNamespace dp -> str "Print Namespace" ++ pr_dirpath dp
| PrintStrategy None -> str "Print Strategies"
| PrintStrategy (Some qid) -> str "Print Strategy" ++ pr_smart_global qid
in

let pr_using e = str (Proof_using.to_string e) in

let rec pr_vernac = function
  | VernacPolymorphic (poly, v) -> 
    let s = if poly then str"Polymorphic" else str"Monomorphic" in
      s ++ pr_vernac v
  | VernacProgram v -> str"Program" ++ spc() ++ pr_vernac v
  | VernacLocal (local, v) -> pr_locality local ++ spc() ++ pr_vernac v

  (* Stm *)
  | VernacStm JoinDocument -> str"Stm JoinDocument"
  | VernacStm PrintDag -> str"Stm PrintDag"
  | VernacStm Finish -> str"Stm Finish"
  | VernacStm Wait -> str"Stm Wait"
  | VernacStm (Observe id) ->
      str"Stm Observe " ++ str(Stateid.to_string id)
  | VernacStm (Command v) -> str"Stm Command " ++ pr_vernac v
  | VernacStm (PGLast v) -> str"Stm PGLast " ++ pr_vernac v

  (* Proof management *)
  | VernacAbortAll -> str "Abort All"
  | VernacRestart -> str"Restart"
  | VernacUnfocus -> str"Unfocus"
  | VernacUnfocused -> str"Unfocused"
  | VernacGoal c -> str"Goal" ++ pr_lconstrarg c
  | VernacAbort id -> str"Abort" ++ pr_opt pr_lident id
  | VernacUndo i -> if Int.equal i 1 then str"Undo" else str"Undo" ++ pr_intarg i
  | VernacUndoTo i -> str"Undo" ++ spc() ++ str"To" ++ pr_intarg i
  | VernacBacktrack (i,j,k) ->
      str "Backtrack" ++  spc() ++ prlist_with_sep sep int [i;j;k]
  | VernacFocus i -> str"Focus" ++ pr_opt int i
  | VernacShow s ->
      let pr_goal_reference = function
        | OpenSubgoals -> mt ()
        | NthGoal n -> spc () ++ int n
        | GoalId n -> spc () ++ str n in
      let pr_showable = function
	| ShowGoal n -> str"Show" ++ pr_goal_reference n
	| ShowGoalImplicitly n -> str"Show Implicit Arguments" ++ pr_opt int n
	| ShowProof -> str"Show Proof"
	| ShowNode -> str"Show Node"
	| ShowScript -> str"Show Script"
	| ShowExistentials -> str"Show Existentials"
	| ShowUniverses -> str"Show Universes"
	| ShowTree -> str"Show Tree"
	| ShowProofNames -> str"Show Conjectures"
	| ShowIntros b -> str"Show " ++ (if b then str"Intros" else str"Intro")
	| ShowMatch id -> str"Show Match " ++ pr_lident id
	| ShowThesis -> str "Show Thesis"
      in pr_showable s
  | VernacCheckGuard -> str"Guarded"

  (* Resetting *)
  | VernacResetName id -> str"Reset" ++ spc() ++ pr_lident id
  | VernacResetInitial -> str"Reset Initial"
  | VernacBack i -> if Int.equal i 1 then str"Back" else str"Back" ++ pr_intarg i
  | VernacBackTo i -> str"BackTo" ++ pr_intarg i

  (* State management *)
  | VernacWriteState s -> str"Write State" ++ spc () ++ qs s
  | VernacRestoreState s -> str"Restore State" ++ spc() ++ qs s

  (* Control *)
  | VernacLoad (f,s) -> str"Load" ++ if f then (spc() ++ str"Verbose"
  ++ spc()) else spc()  ++ qs s
  | VernacTime v -> str"Time" ++ spc() ++ pr_vernac_list v
  | VernacTimeout(n,v) -> str"Timeout " ++ int n ++ spc() ++ pr_vernac v
  | VernacFail v -> str"Fail" ++ spc() ++ pr_vernac v
  | VernacError _ -> str"No-parsing-rule for VernacError"

  (* Syntax *)
  | VernacTacticNotation (n,r,e) ->
      pr_grammar_tactic_rule n ("",r,e)
  | VernacOpenCloseScope (_,(opening,sc)) ->
      str (if opening then "Open " else "Close ") ++
      str "Scope" ++ spc() ++ str sc
  | VernacDelimiters (sc,key) ->
      str"Delimit Scope" ++ spc () ++ str sc ++
      spc() ++ str "with " ++ str key
  | VernacBindScope (sc,cll) ->
      str"Bind Scope" ++ spc () ++ str sc ++
      spc() ++ str "with " ++ prlist_with_sep spc pr_smart_global cll
  | VernacArgumentsScope (q,scl) -> let pr_opt_scope = function
      |	None -> str"_"
      |	Some sc -> str sc in
    str"Arguments Scope" ++ spc() ++
    pr_smart_global q
    ++ spc() ++ str"[" ++ prlist_with_sep sep pr_opt_scope scl ++ str"]"
  | VernacInfix (_,((_,s),mv),q,sn) -> (* A Verifier *)
      hov 0 (hov 0 (str"Infix "
      ++ qs s ++ str " :=" ++ pr_constrarg q) ++
      pr_syntax_modifiers mv ++
      (match sn with
    | None -> mt()
    | Some sc -> spc() ++ str":" ++ spc() ++ str sc))
  | VernacNotation (_,c,((_,s),l),opt) ->
      let ps =
	let n = String.length s in
	if n > 2 && s.[0] == '\'' && s.[n-1] == '\''
	then
          let s' = String.sub s 1 (n-2) in
          if String.contains s' '\'' then qs s else str s'
	else qs s in
      hov 2 (str"Notation" ++ spc() ++ ps ++
      str " :=" ++ pr_constrarg c ++ pr_syntax_modifiers l ++
      (match opt with
        | None -> mt()
        | Some sc -> str" :" ++ spc() ++ str sc))
  | VernacSyntaxExtension (_,(s,l)) ->
      str"Reserved Notation" ++ spc() ++ pr_located qs s ++
      pr_syntax_modifiers l
  | VernacNotationAddFormat(s,k,v) ->
      str"Format Notation " ++ qs s ++ spc () ++ qs k ++ spc() ++ qs v

  (* Gallina *)
  | VernacDefinition (d,id,b) -> (* A verifier... *)
      let pr_def_token (l,dk) =
        let l = match l with Some x -> x | None -> Decl_kinds.Global in
          str (Kindops.string_of_definition_kind (l,false,dk)) in
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

  | VernacStartTheoremProof (ki,l,_) ->
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
  | VernacInductive (p,f,l) ->
      let pr_constructor (coe,(id,c)) =
        hov 2 (pr_lident id ++ str" " ++
               (if coe then str":>" else str":") ++
                pr_spc_lconstr c) in
      let pr_constructor_list b l = match l with
        | Constructors [] -> mt()
        | Constructors l ->
            let fst_sep = match l with [_] -> "   " | _ -> " | " in
            pr_com_at (begin_of_inductive l) ++
            fnl() ++ str fst_sep ++
            prlist_with_sep (fun _ -> fnl() ++ str" | ") pr_constructor l
       | RecordDecl (c,fs) ->
	    pr_record_decl b c fs in
      let pr_oneind key (((coe,id),indpar,s,k,lc),ntn) =
	hov 0 (
	    str key ++ spc() ++
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
	  | Class _ -> "Class" | Variant -> "Variant" in
      hov 1 (pr_oneind key (List.hd l)) ++
      (prlist (fun ind -> fnl() ++ hov 1 (pr_oneind "with" ind)) (List.tl l))


  | VernacFixpoint (local, recs) ->
      let local = match local with
      | Some Discharge -> "Let "
      | Some Local -> "Local "
      | None | Some Global -> ""
      in
      let pr_onerec = function
        | ((loc,id),ro,bl,type_,def),ntn ->
            let annot = pr_guard_annot pr_lconstr_expr bl ro in
            pr_id id ++ pr_binders_arg bl ++ annot
            ++ pr_type_option (fun c -> spc() ++ pr_lconstr_expr c) type_
            ++ pr_opt (fun def -> str":=" ++ brk(1,2) ++ pr_lconstr def) def ++
	    prlist (pr_decl_notation pr_constr) ntn
      in
      hov 0 (str local ++ str "Fixpoint" ++ spc() ++
        prlist_with_sep (fun _ -> fnl() ++ str"with ") pr_onerec recs)

  | VernacCoFixpoint (local, corecs) ->
      let local = match local with
      | Some Discharge -> "Let "
      | Some Local -> "Local "
      | None | Some Global -> ""
      in
      let pr_onecorec (((loc,id),bl,c,def),ntn) =
        pr_id id ++ spc() ++ pr_binders bl ++ spc() ++ str":" ++
        spc() ++ pr_lconstr_expr c ++
        pr_opt (fun def -> str":=" ++ brk(1,2) ++ pr_lconstr def) def ++
	prlist (pr_decl_notation pr_constr) ntn
      in
      hov 0 (str local ++ str "CoFixpoint" ++ spc() ++
      prlist_with_sep (fun _ -> fnl() ++ str"with ") pr_onecorec corecs)
  | VernacScheme l ->
      hov 2 (str"Scheme" ++ spc() ++
             prlist_with_sep (fun _ -> fnl() ++ str"with ") pr_onescheme l)
  | VernacCombinedScheme (id, l) ->
      hov 2 (str"Combined Scheme" ++ spc() ++
	       pr_lident id ++ spc() ++ str"from" ++ spc() ++
	       prlist_with_sep (fun _ -> fnl() ++ str", ") pr_lident l)
  | VernacUniverse v ->
    hov 2 (str"Universe" ++ spc () ++
	     prlist_with_sep (fun _ -> str",") pr_lident v)
  | VernacConstraint v ->
    let pr_uconstraint (l, d, r) =
      pr_lident l ++ spc () ++ Univ.pr_constraint_type d ++ spc () ++ pr_lident r
    in
      hov 2 (str"Constraint" ++ spc () ++
	       prlist_with_sep (fun _ -> str",") pr_uconstraint v)

  (* Gallina extensions *)
  | VernacBeginSection id -> hov 2 (str"Section" ++ spc () ++ pr_lident id)
  | VernacEndSegment id -> hov 2 (str"End" ++ spc() ++ pr_lident id)
  | VernacRequire (exp, l) -> hov 2
      (str "Require" ++ spc() ++ pr_require_token exp ++
      prlist_with_sep sep pr_module l)
  | VernacImport (f,l) ->
      (if f then str"Export" else str"Import") ++ spc() ++
      prlist_with_sep sep pr_import_module l
  | VernacCanonical q -> str"Canonical Structure" ++ spc() ++ pr_smart_global q
  | VernacCoercion (_,id,c1,c2) ->
      hov 1 (
	str"Coercion" ++ spc() ++
	pr_smart_global id ++ spc() ++ str":" ++ spc() ++ pr_class_rawexpr c1 ++
	spc() ++ str">->" ++ spc() ++ pr_class_rawexpr c2)
  | VernacIdentityCoercion (_,id,c1,c2) ->
      hov 1 (
	str"Identity Coercion" ++ spc() ++ pr_lident id ++
	spc() ++ str":" ++ spc() ++ pr_class_rawexpr c1 ++ spc() ++ str">->" ++
	spc() ++ pr_class_rawexpr c2)

 | VernacInstance (abst, sup, (instid, bk, cl), props, pri) ->
     hov 1 (
       (if abst then str"Declare " else mt ()) ++
       str"Instance" ++
       (match snd instid with Name id -> spc () ++ pr_lident (fst instid, id) ++ spc () |
	Anonymous -> mt ()) ++
       pr_and_type_binders_arg sup ++
       str":" ++ spc () ++
       pr_constr cl ++ pr_priority pri ++
	 (match props with
	  | Some (_,p) -> spc () ++ str":=" ++ spc () ++ pr_constr p
	  | None -> mt()))

 | VernacContext l ->
     hov 1 (
       str"Context" ++ spc () ++ pr_and_type_binders_arg l)


 | VernacDeclareInstances (ids, pri) ->
     hov 1 ( str"Existing" ++ spc () ++ 
             str(String.plural (List.length ids) "Instance") ++
             spc () ++ prlist_with_sep spc pr_reference ids ++ pr_priority pri)

 | VernacDeclareClass id ->
     hov 1 (str"Existing" ++ spc () ++ str"Class" ++ spc () ++ pr_reference id)

  (* Modules and Module Types *)
  | VernacDefineModule (export,m,bl,tys,bd) ->
      let b = pr_module_binders bl pr_lconstr in
      hov 2 (str"Module" ++ spc() ++ pr_require_token export ++
               pr_lident m ++ b ++
               pr_of_module_type pr_lconstr tys ++
	       (if List.is_empty bd then mt () else str ":= ") ++
	       prlist_with_sep (fun () -> str " <+ ")
	        (pr_module_ast_inl true pr_lconstr) bd)
  | VernacDeclareModule (export,id,bl,m1) ->
      let b = pr_module_binders bl pr_lconstr in
	hov 2 (str"Declare Module" ++ spc() ++ pr_require_token export ++
             pr_lident id ++ b ++
             pr_module_ast_inl true pr_lconstr m1)
  | VernacDeclareModuleType (id,bl,tyl,m) ->
      let b = pr_module_binders bl pr_lconstr in
      let pr_mt = pr_module_ast_inl true pr_lconstr in
	hov 2 (str"Module Type " ++ pr_lident id ++ b ++
		 prlist_strict (fun m -> str " <: " ++ pr_mt m) tyl ++
		 (if List.is_empty m then mt () else str ":= ") ++
		 prlist_with_sep (fun () -> str " <+ ") pr_mt m)
  | VernacInclude (mexprs) ->
      let pr_m = pr_module_ast_inl false pr_lconstr in
      hov 2 (str"Include" ++ spc() ++
	     prlist_with_sep (fun () -> str " <+ ") pr_m mexprs)
  (* Solving *)
  | VernacSolve (i,tac,deftac) ->
      let pr_goal_selector = function
        | SelectNth i -> int i ++ str":"
        | SelectId id -> pr_id id ++ str":"
        | SelectAll -> str"all" ++ str":"
        | SelectAllParallel -> str"par"
      in
      (if i = Proof_global.get_default_goal_selector () then mt() else pr_goal_selector i) ++
      pr_raw_tactic tac
      ++ (if deftac then str ".." else mt ())
  | VernacSolveExistential (i,c) ->
      str"Existential " ++ int i ++ pr_lconstrarg c

  (* Auxiliary file and library management *)
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
  | VernacDeclareMLModule (l) ->
      hov 2 (str"Declare ML Module" ++ spc() ++ prlist_with_sep sep qs l)
  | VernacChdir s -> str"Cd" ++ pr_opt qs s

  (* Commands *)
  | VernacDeclareTacticDefinition (rc,l) ->
      let pr_tac_body (id, redef, body) =
        let idl, body =
          match body with
	    | Tacexpr.TacFun (idl,b) -> idl,b
            | _ -> [], body in
        pr_ltac_ref id ++
	prlist (function None -> str " _"
                       | Some id -> spc () ++ pr_id id) idl
	++ (if redef then str" ::=" else str" :=") ++ brk(1,1) ++
        pr_raw_tactic body
      in
      hov 1
        (str "Ltac " ++
        prlist_with_sep (fun () -> fnl() ++ str"with ") pr_tac_body l)
  | VernacCreateHintDb (dbname,b) ->
      hov 1 (str "Create HintDb " ++
		str dbname ++ (if b then str" discriminated" else mt ()))
  | VernacRemoveHints (dbnames, ids) ->
      hov 1 (str "Remove Hints " ++
	       prlist_with_sep spc (fun r -> pr_id (coerce_reference_to_id r)) ids ++
	       pr_opt_hintbases dbnames)
  | VernacHints (_, dbnames,h) ->
      pr_hints dbnames h pr_constr pr_constr_pattern_expr
  | VernacSyntacticDefinition (id,(ids,c),_,onlyparsing) ->
      hov 2
        (str"Notation " ++ pr_lident id ++ spc () ++
	 prlist (fun x -> spc() ++ pr_id x) ids ++ str":=" ++ pr_constrarg c ++
         pr_syntax_modifiers
	   (match onlyparsing with None -> [] | Some v -> [SetOnlyParsing v]))
  | VernacDeclareImplicits (q,[]) ->
      hov 2 (str"Implicit Arguments" ++ spc() ++ pr_smart_global q)
  | VernacDeclareImplicits (q,impls) ->
      hov 1 (str"Implicit Arguments " ++
	spc() ++ pr_smart_global q ++ spc() ++
	prlist_with_sep spc (fun imps ->
	  str"[" ++ prlist_with_sep sep pr_explanation imps ++ str"]")
	  impls)
  | VernacArguments (q, impl, nargs, mods) ->
      hov 2 (str"Arguments" ++ spc() ++
        pr_smart_global q ++
      let pr_s = function None -> str"" | Some (_,s) -> str "%" ++ str s in
      let pr_if b x = if b then x else str "" in
      let pr_br imp max x = match imp, max with
        | true, false -> str "[" ++ x ++ str "]"
        | true, true -> str "{" ++ x ++ str "}"
        | _ -> x in
      let rec aux n l =
        match n, l with
        | 0, l -> spc () ++ str"/" ++ aux ~-1 l
        | _, [] -> mt()
        | n, (id,k,s,imp,max) :: tl ->
            spc() ++ pr_br imp max (pr_if k (str"!") ++ pr_name id ++ pr_s s) ++
            aux (n-1) tl in
      prlist_with_sep (fun () -> str", ") (aux nargs) impl ++
      if not (List.is_empty mods) then str" : " else str"" ++
      prlist_with_sep (fun () -> str", " ++ spc()) (function
        | `ReductionDontExposeCase -> str "simpl nomatch"
        | `ReductionNeverUnfold -> str "simpl never"
        | `DefaultImplicits -> str "default implicits"
        | `Rename -> str "rename"
        | `ExtraScopes -> str "extra scopes"
        | `ClearImplicits -> str "clear implicits"
        | `ClearScopes -> str "clear scopes")
        mods)
  | VernacReserve bl ->
      let n = List.length (List.flatten (List.map fst bl)) in
      hov 2 (str"Implicit Type" ++
        str (if n > 1 then "s " else " ") ++
        pr_ne_params_list pr_lconstr_expr (List.map (fun sb -> false,sb) bl))
  | VernacGeneralizable g ->
      hov 1 (str"Generalizable Variable" ++
		match g with
		| None -> str "s none"
		| Some [] -> str "s all"
		| Some idl ->
		    str (if List.length idl > 1 then "s " else " ") ++
		      prlist_with_sep spc pr_lident idl)
  | VernacSetOpacity(k,l) when Conv_oracle.is_transparent k ->
      hov 1 (str "Transparent" ++
             spc() ++ prlist_with_sep sep pr_smart_global l)
  | VernacSetOpacity(Conv_oracle.Opaque,l) ->
      hov 1 (str "Opaque" ++
             spc() ++ prlist_with_sep sep pr_smart_global l)
  | VernacSetOpacity _ ->
      Errors.anomaly (str "VernacSetOpacity used to set something else")
  | VernacSetStrategy l ->
      let pr_lev = function
          Conv_oracle.Opaque -> str"opaque"
        | Conv_oracle.Expand -> str"expand"
        | l when Conv_oracle.is_transparent l -> str"transparent"
        | Conv_oracle.Level n -> int n in
      let pr_line (l,q) =
        hov 2 (pr_lev l ++ spc() ++
               str"[" ++ prlist_with_sep sep pr_smart_global q ++ str"]") in
      hov 1 (str "Strategy" ++ spc() ++
             hv 0 (prlist_with_sep sep pr_line l))
  | VernacUnsetOption (na) ->
      hov 1 (str"Unset" ++ spc() ++ pr_printoption na None)
  | VernacSetOption (na,v) ->
      hov 2 (str"Set" ++ spc() ++ pr_set_option na v)
  | VernacAddOption (na,l) -> hov 2 (str"Add" ++ spc() ++ pr_printoption na (Some l))
  | VernacRemoveOption (na,l) -> hov 2 (str"Remove" ++ spc() ++ pr_printoption na (Some l))
  | VernacMemOption (na,l) -> hov 2 (str"Test" ++ spc() ++ pr_printoption na (Some l))
  | VernacPrintOption na -> hov 2 (str"Test" ++ spc() ++ pr_printoption na None)
  | VernacCheckMayEval (r,io,c) ->
      let pr_mayeval r c = match r with
      | Some r0 ->
          hov 2 (str"Eval" ++ spc() ++
          pr_red_expr (pr_constr,pr_lconstr,pr_smart_global, pr_constr) r0 ++
          spc() ++ str"in" ++ spc () ++ pr_lconstr c)
      | None -> hov 2 (str"Check" ++ spc() ++ pr_lconstr c)
      in
      let pr_i = match io with None -> mt () | Some i -> int i ++ str ": " in
      pr_i ++ pr_mayeval r c
  | VernacGlobalCheck c -> hov 2 (str"Type" ++ pr_constrarg c)
  | VernacDeclareReduction (s,r) ->
     str "Declare Reduction " ++ str s ++ str " := " ++
     pr_red_expr (pr_constr,pr_lconstr,pr_smart_global, pr_constr) r
  | VernacPrint p -> pr_printable p
  | VernacSearch (sea,sea_r) -> pr_search sea sea_r pr_constr_pattern_expr
  | VernacLocate loc ->
      let pr_locate =function
        | LocateAny qid -> pr_smart_global qid
        | LocateTerm qid -> str "Term" ++ spc() ++ pr_smart_global qid
	| LocateFile f -> str"File" ++ spc() ++ qs f
	| LocateLibrary qid -> str"Library" ++ spc () ++ pr_module qid
	| LocateModule qid -> str"Module" ++ spc () ++ pr_module qid
	| LocateTactic qid -> str"Ltac" ++ spc () ++ pr_ltac_ref qid
      in str"Locate" ++ spc() ++ pr_locate loc
  | VernacRegister (id, RegisterInline) ->
      hov 2
        (str "Register Inline" ++ spc() ++ pr_lident id)
  | VernacComments l ->
      hov 2
        (str"Comments" ++ spc() ++ prlist_with_sep sep (pr_comment pr_constr) l)
  | VernacNop -> mt()

  (* Toplevel control *)
  | VernacToplevelControl exn -> pr_topcmd exn

  (* For extension *)
  | VernacExtend (s,c) -> pr_extend s c
  | VernacProof (None, None) -> str "Proof"
  | VernacProof (None, Some e) -> str "Proof " ++ pr_using e
  | VernacProof (Some te, None) -> str "Proof with" ++ spc() ++ pr_raw_tactic te
  | VernacProof (Some te, Some e) ->
      str "Proof " ++ pr_using e ++ spc() ++
      str "with" ++ spc() ++pr_raw_tactic te
  | VernacProofMode s -> str ("Proof Mode "^s)
  | VernacBullet b -> begin match b with
      | Dash n -> str (String.make n '-')
      | Star n -> str (String.make n '*')
      | Plus n -> str (String.make n '+')
  end ++ spc()
  | VernacSubproof None -> str "{"
  | VernacSubproof (Some i) -> str "BeginSubproof " ++ int i
  | VernacEndSubproof -> str "}"

and pr_vernac_list l =
      hov 2 (str"[" ++ spc() ++
             prlist (fun v -> pr_located pr_vernac v ++ sep_end (snd v) ++ fnl()) l
             ++ spc() ++ str"]")

and pr_extend s cl =
  let pr_arg a =
    try pr_gen a
    with Failure _ -> str ("<error in "^fst s^">") in
  try
    let rl = Egramml.get_extend_vernac_rule s in
    let start,rl,cl =
      match rl with
      | Egramml.GramTerminal s :: rl -> str s, rl, cl
      | Egramml.GramNonTerminal _ :: rl -> pr_arg (List.hd cl), rl, List.tl cl
      | [] -> anomaly (Pp.str "Empty entry") in
    let (pp,_) =
      List.fold_left
        (fun (strm,args) pi ->
          let pp,args = match pi with
          | Egramml.GramNonTerminal _ -> (pr_arg (List.hd args), List.tl args)
          | Egramml.GramTerminal s -> (str s, args) in
          (strm ++ spc() ++ pp), args)
        (start,cl) rl in
    hov 1 pp
  with Not_found ->
    hov 1 (str ("TODO("^fst s) ++ prlist_with_sep sep pr_arg cl ++ str ")")

in pr_vernac

let pr_vernac_body v = make_pr_vernac pr_constr_expr pr_lconstr_expr v

let pr_vernac v = make_pr_vernac pr_constr_expr pr_lconstr_expr v ++ sep_end v

let pr_vernac x =
  try pr_vernac x
  with e -> Errors.print e

