(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Constrintern
open Closure
open RedFlags
open Declarations
open Entries
open Dyn
open Libobject
open Pattern
open Pp
open Rawterm
open Sign
open Tacred
open Util
open Names
open Nameops
open Libnames
open Nametab
open Pfedit
open Proof_type
open Refiner
open Tacmach
open Tactic_debug
open Topconstr
open Ast
open Term
open Termops
open Declare
open Tacexpr
open Safe_typing
open Typing
open Hiddentac
open Genarg
open Decl_kinds

(*
let err_msg_tactic_not_found macro_loc macro =
  user_err_loc
    (macro_loc,"macro_expand",
     (str "Tactic macro " ++ str macro ++ spc () ++ str "not found"))
*)

let error_syntactic_metavariables_not_allowed loc =
  user_err_loc 
    (loc,"out_ident",
     str "Syntactic metavariables allowed only in quotations")

let skip_metaid = function
  | AI x -> x
  | MetaId (loc,_) -> error_syntactic_metavariables_not_allowed loc

type ltac_type =
  | LtacFun of ltac_type
  | LtacBasic
  | LtacTactic

(* Values for interpretation *)
type value =
  | VTactic of tactic  (* For mixed ML/Ltac tactics (e.g. Tauto) *)
  | VRTactic of (goal list sigma * validation) (* For Match results *)
                                               (* Not a true value *)
  | VFun of (identifier * value) list * identifier option list *raw_tactic_expr
  | VVoid
  | VInteger of int
  | VIdentifier of identifier (* idents which are not bound, as in "Intro H" *)
                              (* but which may be bound later, as in "tac" in*)
                              (* "Intro H; tac" *)
  | VConstr of constr         (* includes idents known bound and references *)
  | VConstr_context of constr
  | VRec of value ref

(* Signature for interpretation: val_interp and interpretation functions *)
and interp_sign =
  { lfun : (identifier * value) list;
    lmatch : (int * constr) list;
    debug : debug_info }

let check_is_value = function
  | VRTactic _ -> (* These are goals produced by Match *)
   error "Immediate Match producing tactics not allowed in local definitions"
  | _ -> ()

(* For tactic_of_value *)
exception NotTactic

(* Gives the constr corresponding to a Constr_context tactic_arg *)
let constr_of_VConstr_context = function
  | VConstr_context c -> c
  | _ ->
    anomalylabstrm "constr_of_VConstr_context" (str
      "Not a Constr_context tactic_arg")

(*
(* Gives identifiers and makes the possible injection constr -> ident *)
let make_ids ast = function
  | Identifier id -> id
  | Constr c ->
    (try destVar c with
    | Invalid_argument "destVar" ->
      anomalylabstrm "make_ids"
      (str "This term cannot be reduced to an identifier" ++ fnl () ++
        print_ast ast))
  | _ -> anomalylabstrm "make_ids" (str "Not an identifier")
*)

let pr_value env = function
  | VVoid -> str "()"
  | VInteger n -> int n
  | VIdentifier id -> pr_id id
  | VConstr c -> Printer.prterm_env env c
  | VConstr_context c -> Printer.prterm_env env c
  | (VTactic _ | VRTactic _ | VFun _ | VRec _) -> str "<fun>"

(* Transforms a named_context into a (string * constr) list *)
let make_hyps = List.map (fun (id,_,typ) -> (id, typ))

(* Transforms an id into a constr if possible, or fails *)
let constr_of_id env id = 
  construct_reference (Some (Environ.named_context env)) id

(* To embed several objects in Coqast.t *)
let ((tactic_in : (interp_sign -> raw_tactic_expr) -> Dyn.t),
     (tactic_out : Dyn.t -> (interp_sign -> raw_tactic_expr))) =
  create "tactic"

let ((value_in : value -> Dyn.t),
     (value_out : Dyn.t -> value)) = create "value"

let tacticIn t = TacArg (TacDynamic (dummy_loc,tactic_in t))
let tacticOut = function
  | TacArg (TacDynamic (_,d)) ->
    if (tag d) = "tactic" then
      tactic_out d
    else
      anomalylabstrm "tacticOut" (str "Dynamic tag should be tactic")
  | ast ->
    anomalylabstrm "tacticOut"
      (str "Not a Dynamic ast: " (* ++ print_ast ast*) )

let valueIn t = TacDynamic (dummy_loc,value_in t)
let valueOut = function
  | TacDynamic (_,d) ->
    if (tag d) = "value" then
      value_out d
    else
      anomalylabstrm "valueOut" (str "Dynamic tag should be value")
  | ast ->
    anomalylabstrm "valueOut" (str "Not a Dynamic ast: ")

(* To embed constr in Coqast.t *)
let constrIn t = CDynamic (dummy_loc,Pretyping.constr_in t)
let constrOut = function
  | CDynamic (_,d) ->
    if (Dyn.tag d) = "constr" then
      Pretyping.constr_out d
    else
      anomalylabstrm "constrOut" (str "Dynamic tag should be constr")
  | ast ->
    anomalylabstrm "constrOut" (str "Not a Dynamic ast")
let loc = dummy_loc

(* Table of interpretation functions *)
let interp_tab =
  (Hashtbl.create 17 : (string , interp_sign -> Coqast.t -> value) Hashtbl.t)

(* Adds an interpretation function *)
let interp_add (ast_typ,interp_fun) =
  try
    Hashtbl.add interp_tab ast_typ interp_fun
  with
      Failure _ ->
        errorlabstrm "interp_add"
          (str "Cannot add the interpretation function for " ++ str ast_typ ++            str " twice")

(* Adds a possible existing interpretation function *)
let overwriting_interp_add (ast_typ,interp_fun) =
  if Hashtbl.mem interp_tab ast_typ then
  begin
    Hashtbl.remove interp_tab ast_typ;
    warning ("Overwriting definition of tactic interpreter command " ^ ast_typ)
  end;
  Hashtbl.add interp_tab ast_typ interp_fun

(* Finds the interpretation function corresponding to a given ast type *)
let look_for_interp = Hashtbl.find interp_tab

(* Globalizes the identifier *)

let find_reference env qid =
  (* We first look for a variable of the current proof *)
  match repr_qualid qid with
    | (d,id) when repr_dirpath d = [] & List.mem id (ids_of_context env)
	-> VarRef id
    | _ -> Nametab.locate qid

let coerce_to_reference env = function
  | VConstr c ->
      (try reference_of_constr c
      with Not_found -> invalid_arg_loc (loc, "Not a reference"))
(*  | VIdentifier id -> VarRef id*)
  | v -> errorlabstrm "coerce_to_reference"
      (str "The value" ++ spc () ++ pr_value env v ++ 
       str "cannot be coerced to a reference")

(* turns a value into an evaluable reference *)
let error_not_evaluable s =
  errorlabstrm "evalref_of_ref" 
    (str "Cannot coerce" ++ spc ()  ++ s ++ spc () ++
     str "to an evaluable reference")

let coerce_to_evaluable_ref env c =
  let ev = match c with
    | VConstr c when isConst c -> EvalConstRef (destConst c)
    | VConstr c when isVar c -> EvalVarRef (destVar c)
(*    | VIdentifier id -> EvalVarRef id*)
    | _ -> error_not_evaluable (pr_value env c)
  in
  if not (Tacred.is_evaluable env ev) then
    error_not_evaluable (pr_value env c);
  ev

let coerce_to_inductive = function
  | VConstr c when isInd c -> destInd c
  | x ->
      try
	let r = match x with
	  | VConstr c -> reference_of_constr c
	  | _ -> failwith "" in
	errorlabstrm "coerce_to_inductive"
          (Printer.pr_global r ++ str " is not an inductive type")
      with _ ->
	errorlabstrm "coerce_to_inductive"
          (str "Found an argument which should be an inductive type")

(* Summary and Object declaration *)
let mactab = ref Gmap.empty

let lookup qid = Gmap.find (locate_tactic qid) !mactab

let _ =
  let init () = mactab := Gmap.empty in
  let freeze () = !mactab in
  let unfreeze fs = mactab := fs in
  Summary.declare_summary "tactic-definition"
    { Summary.freeze_function   = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function     = init;
      Summary.survive_section   = false }

(* Interpretation of extra generic arguments *)
type genarg_interp_type =
   interp_sign -> goal sigma -> raw_generic_argument -> closed_generic_argument
let extragenargtab = ref (Gmap.empty : (string,genarg_interp_type) Gmap.t)
let add_genarg_interp id f = extragenargtab := Gmap.add id f !extragenargtab
let lookup_genarg_interp id = 
  try Gmap.find id !extragenargtab
  with Not_found -> failwith ("No interpretation function found for entry "^id)


(* Unboxes VRec *)
let unrec = function
  | VRec v -> !v
  | a -> a

(************* GLOBALIZE ************)

(* We have identifier <| global_reference <| constr *)

let find_ident id (lfun,_,_,env) = 
  List.mem id lfun or 
  List.mem id (ids_of_named_context (Environ.named_context env))

(* Globalize a name which can be fresh *)
let glob_ident l ist id =
  (* We use identifier both for variables and new names; thus nothing to do *)
  if find_ident id ist then () else l:=id::!l;
  id

let glob_name l ist = function
  | Anonymous -> Anonymous
  | Name id -> Name (glob_ident l ist id)

let get_current_context () =
    try Pfedit.get_current_goal_context ()
    with e when Logic.catchable_exception e -> 
      (Evd.empty, Global.env())

let weak = ref true

(* Globalize a name which must be bound -- actually just check it is bound *)
let glob_hyp ist (loc,id) =
  let (_,env) = get_current_context () in
  if !weak or find_ident id ist then id
  else
(*
    try let _ = lookup (make_short_qualid id) in id
    with Not_found -> 
*)
    Pretype_errors.error_var_not_found_loc loc id

let glob_lochyp ist (_loc,_ as locid) = (loc,glob_hyp ist locid)

let error_unbound_metanum loc n =
  user_err_loc
    (loc,"glob_qualid_or_metanum", str "?" ++ int n ++ str " is unbound")

let glob_metanum (_,lmeta,_,_) loc n =
  if List.mem n lmeta then n else error_unbound_metanum loc n

let glob_hyp_or_metanum ist = function
  | AN id -> AN (glob_hyp ist (loc,id))
  | MetaNum (_loc,n) -> MetaNum (loc,glob_metanum ist loc n)

let glob_qualid_or_metanum ist = function
  | AN qid -> AN (Qualid(loc,qualid_of_sp (sp_of_global None (Nametab.global qid))))
  | MetaNum (_loc,n) -> MetaNum (loc,glob_metanum ist loc n)

let glob_reference ist = function
  | Ident (loc,id) as r when find_ident id ist -> r
  | r -> Qualid (loc,qualid_of_sp (sp_of_global None (Nametab.global r)))

let glob_ltac_qualid ist ref =
  let (loc,qid) = qualid_of_reference ref in
  try Qualid (loc,qualid_of_sp (locate_tactic qid))
  with Not_found -> glob_reference ist ref

let glob_ltac_reference ist = function
  | Ident (_loc,id) when !weak or find_ident id ist -> Ident (loc,id)
  | r -> glob_ltac_qualid ist r

let rec glob_intro_pattern lf ist = function
  | IntroOrAndPattern l ->
      IntroOrAndPattern (List.map (List.map (glob_intro_pattern lf ist)) l)
  | IntroWildcard ->
      IntroWildcard
  | IntroIdentifier id ->
      IntroIdentifier (glob_ident lf ist id)

let glob_quantified_hypothesis ist x =
  (* We use identifier both for variables and quantified hyps (no way to
     statically check the existence of a quantified hyp); thus nothing to do *)
  x

let glob_constr (lfun,_,sigma,env) c =
  let _ =
    Constrintern.for_grammar (Constrintern.interp_rawconstr_gen false
      sigma env [] false (lfun,[])) c
  in c

(* Globalize bindings *)
let glob_binding ist (loc,b,c) =
  (loc,glob_quantified_hypothesis ist b,glob_constr ist c)

let glob_bindings ist = function
  | NoBindings -> NoBindings
  | ImplicitBindings l -> ImplicitBindings (List.map (glob_constr ist) l)
  | ExplicitBindings l -> ExplicitBindings (List.map (glob_binding ist) l)

let glob_constr_with_bindings ist (c,bl) =
  (glob_constr ist c, glob_bindings ist bl)

let glob_clause_pattern ist (l,occl) =
  let rec check = function
    | (hyp,l) :: rest -> 
	let (_loc,_ as id) = skip_metaid hyp in
	(AI(loc,glob_hyp ist id),l)::(check rest)
    | [] -> []
  in (l,check occl)

let glob_induction_arg ist = function
  | ElimOnConstr c -> ElimOnConstr (glob_constr ist c)
  | ElimOnAnonHyp n as x -> x
  | ElimOnIdent (_loc,id) as x -> ElimOnIdent (loc,id)

(* Globalize a reduction expression *)
let glob_evaluable_or_metanum ist = function
  | AN qid -> AN (glob_reference ist qid)
  | MetaNum (_loc,n) -> MetaNum (loc,glob_metanum ist loc n)

let glob_unfold ist (l,qid) = (l,glob_evaluable_or_metanum ist qid)

let glob_flag ist red =
  { red with rConst = List.map (glob_evaluable_or_metanum ist) red.rConst }

let glob_constr_occurrence ist (l,c) = (l,glob_constr ist c)

let glob_redexp ist = function
  | Unfold l -> Unfold (List.map (glob_unfold ist) l)
  | Fold l -> Fold (List.map (glob_constr ist) l)
  | Cbv f -> Cbv (glob_flag ist f)
  | Lazy f -> Lazy (glob_flag ist f)
  | Pattern l -> Pattern (List.map (glob_constr_occurrence ist) l)
  | Simpl o -> Simpl (option_app (glob_constr_occurrence ist) o)
  | (Red _ | Hnf as r) -> r
  | ExtraRedExpr (s,c) -> ExtraRedExpr (s, glob_constr ist c)

(* Interprets an hypothesis name *)
let glob_hyp_location ist = function
  | InHyp id ->
      let (_loc,_ as id) = skip_metaid id in
      InHyp (AI(loc,glob_hyp ist id))
  | InHypType id -> 
      let (_loc,_ as id) = skip_metaid id in
      InHypType (AI(loc,glob_hyp ist id))

(* Reads a pattern *)
let glob_pattern evc env lfun = function
  | Subterm (ido,pc) ->
      let lfun = List.map (fun id -> (id, mkVar id)) lfun in
      let (metas,_) = interp_constrpattern_gen evc env (lfun,[]) pc  in
      metas, Subterm (ido,pc)
  | Term pc ->
      let lfun = List.map (fun id -> (id, mkVar id)) lfun in
      let (metas,_) = interp_constrpattern_gen evc env (lfun,[]) pc  in
      metas, Term pc

let glob_constr_may_eval ist = function
  | ConstrEval (r,c) -> ConstrEval (glob_redexp ist r,glob_constr ist c)
  | ConstrContext (locid,c) ->
      ConstrContext ((loc,glob_hyp ist locid),glob_constr ist c)
  | ConstrTypeOf c -> ConstrTypeOf (glob_constr ist c)
  | ConstrTerm c -> ConstrTerm (glob_constr ist c)

(* Reads the hypotheses of a Match Context rule *)
let rec glob_match_context_hyps evc env lfun = function
  | (NoHypId mp)::tl ->
      let metas1, pat = glob_pattern evc env lfun mp in
      let lfun, metas2, hyps = glob_match_context_hyps evc env lfun tl in
      lfun, metas1@metas2, (NoHypId pat)::hyps
  | (Hyp ((_,s) as locs,mp))::tl ->
      let metas1, pat = glob_pattern evc env lfun mp in
      let lfun, metas2, hyps = glob_match_context_hyps evc env lfun tl in
      s::lfun, metas1@metas2, Hyp (locs,pat)::hyps
  | [] -> lfun, [], []

(* Utilities *)
let rec filter_some = function
  | None :: l -> filter_some l
  | Some a :: l -> a :: filter_some l
  | [] -> []

let extract_names lrc =
  List.fold_right 
    (fun ((loc,name),_) l ->
      if List.mem name l then
	user_err_loc
	  (loc, "glob_tactic", str "This variable is bound several times");
      name::l)
    lrc []

let extract_let_names lrc =
  List.fold_right 
    (fun ((loc,name),_,_) l ->
      if List.mem name l then
	user_err_loc
	  (loc, "glob_tactic", str "This variable is bound several times");
      name::l)
    lrc []

(* Globalizes tactics *)
let rec glob_atomic lf (_,_,_,_ as ist) = function
  (* Basic tactics *)
  | TacIntroPattern l -> TacIntroPattern (List.map (glob_intro_pattern lf ist) l)
  | TacIntrosUntil hyp -> TacIntrosUntil (glob_quantified_hypothesis ist hyp)
  | TacIntroMove (ido,ido') ->
      TacIntroMove (option_app (glob_ident lf ist) ido,
          option_app (fun (_loc,_ as x) -> (loc,glob_hyp ist x)) ido')
  | TacAssumption -> TacAssumption
  | TacExact c -> TacExact (glob_constr ist c)
  | TacApply cb -> TacApply (glob_constr_with_bindings ist cb)
  | TacElim (cb,cbo) ->
      TacElim (glob_constr_with_bindings ist cb,
               option_app (glob_constr_with_bindings ist) cbo)
  | TacElimType c -> TacElimType (glob_constr ist c)
  | TacCase cb -> TacCase (glob_constr_with_bindings ist cb)
  | TacCaseType c -> TacCaseType (glob_constr ist c)
  | TacFix (idopt,n) -> TacFix (option_app (glob_ident lf ist) idopt,n)
  | TacMutualFix (id,n,l) ->
      let f (id,n,c) = (glob_ident lf ist id,n,glob_constr ist c) in
      TacMutualFix (glob_ident lf ist id, n, List.map f l)
  | TacCofix idopt -> TacCofix (option_app (glob_ident lf ist) idopt)
  | TacMutualCofix (id,l) ->
      let f (id,c) = (glob_ident lf ist id,glob_constr ist c) in
      TacMutualCofix (glob_ident lf ist id, List.map f l)
  | TacCut c -> TacCut (glob_constr ist c)
  | TacTrueCut (ido,c) ->
      TacTrueCut (option_app (glob_ident lf ist) ido, glob_constr ist c)
  | TacForward (b,na,c) -> TacForward (b,glob_name lf ist na,glob_constr ist c)
  | TacGeneralize cl -> TacGeneralize (List.map (glob_constr ist) cl)
  | TacGeneralizeDep c -> TacGeneralizeDep (glob_constr ist c)
  | TacLetTac (id,c,clp) ->
      TacLetTac (id,glob_constr ist c,glob_clause_pattern ist clp)
  | TacInstantiate (n,c) -> TacInstantiate (n,glob_constr ist c)

  (* Automation tactics *)
  | TacTrivial l -> TacTrivial l
  | TacAuto (n,l) -> TacAuto (n,l)
  | TacAutoTDB n -> TacAutoTDB n
  | TacDestructHyp (b,(_loc,_ as id)) -> TacDestructHyp(b,(loc,glob_hyp ist id))
  | TacDestructConcl -> TacDestructConcl
  | TacSuperAuto (n,l,b1,b2) -> TacSuperAuto (n,l,b1,b2)
  | TacDAuto (n,p) -> TacDAuto (n,p)

  (* Derived basic tactics *)
  | TacOldInduction h -> TacOldInduction (glob_quantified_hypothesis ist h)
  | TacNewInduction (c,cbo,ids) ->
      TacNewInduction (glob_induction_arg ist c,
               option_app (glob_constr_with_bindings ist) cbo,
               List.map (List.map (glob_ident lf ist)) ids)
  | TacOldDestruct h -> TacOldDestruct (glob_quantified_hypothesis ist h)
  | TacNewDestruct (c,cbo,ids) ->
      TacNewDestruct (glob_induction_arg ist c,
               option_app (glob_constr_with_bindings ist) cbo,
               List.map (List.map (glob_ident lf ist)) ids)
  | TacDoubleInduction (h1,h2) ->
      let h1 = glob_quantified_hypothesis ist h1 in
      let h2 = glob_quantified_hypothesis ist h2 in
      TacDoubleInduction (h1,h2)
  | TacDecomposeAnd c -> TacDecomposeAnd (glob_constr ist c)
  | TacDecomposeOr c -> TacDecomposeOr (glob_constr ist c)
  | TacDecompose (l,c) ->
      let l = List.map (glob_qualid_or_metanum ist) l in
      TacDecompose (l,glob_constr ist c)
  | TacSpecialize (n,l) -> TacSpecialize (n,glob_constr_with_bindings ist l)
  | TacLApply c -> TacLApply (glob_constr ist c)

  (* Context management *)
  | TacClear l -> TacClear (List.map (glob_hyp_or_metanum ist) l)
  | TacClearBody l -> TacClearBody (List.map (glob_hyp_or_metanum ist) l)
  | TacMove (dep,id1,id2) -> TacMove (dep,glob_lochyp ist id1,glob_lochyp ist id2)
  | TacRename (id1,id2) -> TacRename (glob_lochyp ist id1, glob_lochyp ist id2)

  (* Constructors *)
  | TacLeft bl -> TacLeft (glob_bindings ist bl)
  | TacRight bl -> TacRight (glob_bindings ist bl)
  | TacSplit bl -> TacSplit (glob_bindings ist bl)
  | TacAnyConstructor t -> TacAnyConstructor (option_app (glob_tactic ist) t)
  | TacConstructor (n,bl) -> TacConstructor (n, glob_bindings ist bl)

  (* Conversion *)
  | TacReduce (r,cl) ->
      TacReduce (glob_redexp ist r, List.map (glob_hyp_location ist) cl)
  | TacChange (occl,c,cl) ->
      TacChange (option_app (glob_constr_occurrence ist) occl,
        glob_constr ist c, List.map (glob_hyp_location ist) cl)

  (* Equivalence relations *)
  | TacReflexivity -> TacReflexivity
  | TacSymmetry -> TacSymmetry
  | TacTransitivity c -> TacTransitivity (glob_constr ist c)

  (* For extensions *)
  | TacExtend (_loc,opn,l) ->
      let _ = lookup_tactic opn in
      TacExtend (loc,opn,List.map (glob_genarg ist) l)
  | TacAlias (_,l,body) as t ->
      (* failwith "TacAlias globalisation: TODO" *)
      t

and glob_tactic ist tac = snd (glob_tactic_seq ist tac)

and glob_tactic_seq (lfun,lmeta,sigma,env as ist) = function
  | TacAtom (_loc,t) ->
      let lf = ref lfun in
      let t = glob_atomic lf ist t in
      !lf, TacAtom (loc, t)
  | TacFun tacfun -> lfun, TacFun (glob_tactic_fun ist tacfun)
  | TacLetRecIn (lrc,u) ->
      let names = extract_names lrc in
      let ist = (names@lfun,lmeta,sigma,env) in
      let lrc = List.map (fun (n,b) -> (n,glob_tactic_fun ist b)) lrc in
      lfun, TacLetRecIn (lrc,glob_tactic ist u)
  | TacLetIn (l,u) ->
      let l = List.map (fun (n,c,b) -> (n,option_app (glob_constr_may_eval ist) c,glob_tacarg ist b)) l in
      let ist' = ((extract_let_names l)@lfun,lmeta,sigma,env) in
      lfun, TacLetIn (l,glob_tactic ist' u)
  | TacLetCut l ->
      let f (n,c,t) = (n,glob_constr_may_eval ist c,glob_tacarg ist t) in
      lfun, TacLetCut (List.map f l)
  | TacMatchContext (lr,lmr) ->
      lfun, TacMatchContext(lr, glob_match_rule ist lmr)
  | TacMatch (c,lmr) ->
      lfun, TacMatch (glob_constr_may_eval ist c,glob_match_rule ist lmr)
  | TacId -> lfun, TacId
  | TacFail n as x -> lfun, x
  | TacProgress tac -> lfun, TacProgress (glob_tactic ist tac)
  | TacAbstract (tac,s) -> lfun, TacAbstract (glob_tactic ist tac,s)
  | TacThen (t1,t2) ->
      let lfun', t1 = glob_tactic_seq ist t1 in
      let lfun'', t2 = glob_tactic_seq (lfun',lmeta,sigma,env) t2 in
      lfun'', TacThen (t1,t2)
  | TacThens (t,tl) ->
      let lfun', t = glob_tactic_seq ist t in
      (* Que faire en cas de (tac complexe avec Match et Thens; tac2) ?? *)
      lfun', TacThens (t, List.map (glob_tactic (lfun',lmeta,sigma,env)) tl)
  | TacDo (n,tac) -> lfun, TacDo (n,glob_tactic ist tac)
  | TacTry tac -> lfun, TacTry (glob_tactic ist tac)
  | TacInfo tac -> lfun, TacInfo (glob_tactic ist tac)
  | TacRepeat tac -> lfun, TacRepeat (glob_tactic ist tac)
  | TacOrelse (tac1,tac2) ->
      lfun, TacOrelse (glob_tactic ist tac1,glob_tactic ist tac2)
  | TacFirst l -> lfun, TacFirst (List.map (glob_tactic ist) l)
  | TacSolve l -> lfun, TacSolve (List.map (glob_tactic ist) l)
  | TacArg a -> lfun, TacArg (glob_tacarg ist a)

and glob_tactic_fun (lfun,lmeta,sigma,env) (var,body) = 
  let lfun' = List.rev_append (filter_some var) lfun in
  (var,glob_tactic (lfun',lmeta,sigma,env) body)

and glob_tacarg ist = function
  | TacVoid -> TacVoid
  | Reference r -> Reference (glob_ltac_reference ist r)
  | Integer n -> Integer n
  | ConstrMayEval c -> ConstrMayEval (glob_constr_may_eval ist c)
  | MetaNumArg (_loc,n) -> MetaNumArg (loc,glob_metanum ist loc n)
  | MetaIdArg (_loc,_) -> error_syntactic_metavariables_not_allowed loc
  | TacCall (_loc,f,l) ->
      TacCall (_loc,glob_ltac_reference ist f,List.map (glob_tacarg ist) l)
  | Tacexp t -> Tacexp (glob_tactic ist t)
  | TacDynamic(_,t) as x ->
      (match tag t with
	| "tactic"|"value"|"constr" -> x
	| s -> anomaly_loc (loc, "Tacinterp.val_interp",
                 str "Unknown dynamic: <" ++ str s ++ str ">"))

(* Reads the rules of a Match Context or a Match *)
and glob_match_rule (lfun,lmeta,sigma,env as ist) = function
  | (All tc)::tl ->
      (All (glob_tactic ist tc))::(glob_match_rule ist tl)
  | (Pat (rl,mp,tc))::tl ->
      let lfun',metas1,hyps = glob_match_context_hyps Evd.empty env lfun rl in
      let metas2,pat = glob_pattern Evd.empty env lfun mp in
      let metas = list_uniquize (metas1@metas2@lmeta) in
      (Pat (hyps,pat,glob_tactic (lfun',metas,sigma,env) tc))
      ::(glob_match_rule ist tl)
  | [] -> []

and glob_genarg ist x =
  match genarg_tag x with
  | BoolArgType -> in_gen rawwit_bool (out_gen rawwit_bool x)
  | IntArgType -> in_gen rawwit_int (out_gen rawwit_int x)
  | IntOrVarArgType ->
      let f = function
	| ArgVar (_loc,id) -> ArgVar (loc,glob_hyp ist (loc,id))
	| ArgArg n as x -> x in
      in_gen rawwit_int_or_var (f (out_gen rawwit_int_or_var x))
  | StringArgType ->
      in_gen rawwit_string (out_gen rawwit_string x)
  | PreIdentArgType ->
      in_gen rawwit_pre_ident (out_gen rawwit_pre_ident x)
  | IdentArgType ->
      in_gen rawwit_ident (glob_hyp ist (dummy_loc,out_gen rawwit_ident x))
  | RefArgType ->
      in_gen rawwit_ref (glob_ltac_reference ist (out_gen rawwit_ref x))
  | SortArgType ->
      in_gen rawwit_sort (out_gen rawwit_sort x)
  | ConstrArgType ->
      in_gen rawwit_constr (glob_constr ist (out_gen rawwit_constr x))
  | ConstrMayEvalArgType ->
      in_gen rawwit_constr_may_eval (glob_constr_may_eval ist (out_gen rawwit_constr_may_eval x))
  | QuantHypArgType ->
      in_gen rawwit_quant_hyp
        (glob_quantified_hypothesis ist (out_gen rawwit_quant_hyp x))
  | RedExprArgType ->
      in_gen rawwit_red_expr (glob_redexp ist (out_gen rawwit_red_expr x))
  | TacticArgType ->
      in_gen rawwit_tactic (glob_tactic ist (out_gen rawwit_tactic x))
  | CastedOpenConstrArgType ->
      in_gen rawwit_casted_open_constr 
        (glob_constr ist (out_gen rawwit_casted_open_constr x))
  | ConstrWithBindingsArgType ->
      in_gen rawwit_constr_with_bindings
        (glob_constr_with_bindings ist (out_gen rawwit_constr_with_bindings x))
  | List0ArgType _ -> app_list0 (glob_genarg ist) x
  | List1ArgType _ -> app_list1 (glob_genarg ist) x
  | OptArgType _ -> app_opt (glob_genarg ist) x
  | PairArgType _ -> app_pair (glob_genarg ist) (glob_genarg ist) x
  | ExtraArgType s -> x


(************* END GLOBALIZE ************)

(* Associates variables with values and gives the remaining variables and
   values *)
let head_with_value (lvar,lval) =
  let rec head_with_value_rec lacc = function
    | ([],[]) -> (lacc,[],[])
    | (vr::tvr,ve::tve) ->
      (match vr with
      |	None -> head_with_value_rec lacc (tvr,tve)
      | Some v -> head_with_value_rec ((v,ve)::lacc) (tvr,tve))
    | (vr,[]) -> (lacc,vr,[])
    | ([],ve) -> (lacc,[],ve)
  in
    head_with_value_rec [] (lvar,lval)

(* Gives a context couple if there is a context identifier *)
let give_context ctxt = function
  | None -> []
  | Some id -> [id,VConstr_context ctxt]

(* Reads a pattern *)
let read_pattern evc env lfun = function
  | Subterm (ido,pc) ->
      Subterm (ido,snd (interp_constrpattern_gen evc env lfun pc))
  | Term pc ->
      Term (snd (interp_constrpattern_gen evc env lfun pc))

(* Reads the hypotheses of a Match Context rule *)
let rec read_match_context_hyps evc env lfun lidh = function
  | (NoHypId mp)::tl ->
    (NoHypId (read_pattern evc env lfun mp))::
      (read_match_context_hyps evc env lfun lidh tl)
  | (Hyp ((loc,id) as locid,mp))::tl ->
    if List.mem id lidh then
      user_err_loc (loc,"Tacinterp.read_match_context_hyps",
      str ("Hypothesis pattern-matching variable "^(string_of_id id)^
           " used twice in the same pattern"))
    else
    (Hyp (locid,read_pattern evc env lfun mp))::
      (read_match_context_hyps evc env lfun (id::lidh) tl)
  | [] -> []

(* Reads the rules of a Match Context or a Match *)
let rec read_match_rule evc env lfun = function
  | (All tc)::tl -> (All tc)::(read_match_rule evc env lfun tl)
  | (Pat (rl,mp,tc))::tl ->
      (Pat (read_match_context_hyps evc env lfun [] rl,
            read_pattern evc env lfun mp,tc))
       ::(read_match_rule evc env lfun tl)
  | [] -> []

(* For Match Context and Match *)
exception No_match
exception Not_coherent_metas

let is_match_catchable = function
  | No_match | FailError _ -> true
  | e -> Logic.catchable_exception e

(* Verifies if the matched list is coherent with respect to lcm *)
let rec verify_metas_coherence gl lcm = function
  | (num,csr)::tl ->
    if (List.for_all (fun (a,b) -> a<>num or pf_conv_x gl b csr) lcm) then
      (num,csr)::(verify_metas_coherence gl lcm tl)
    else
      raise Not_coherent_metas
  | [] -> []

(* Tries to match a pattern and a constr *)
let apply_matching pat csr =
  try
    (Pattern.matches pat csr)
  with
     PatternMatchingFailure -> raise No_match

(* Tries to match one hypothesis pattern with a list of hypotheses *)
let apply_one_mhyp_context gl lmatch mhyp lhyps noccopt =
  let get_pattern = function
    | Hyp (_,pat) -> pat
    | NoHypId pat -> pat
  and get_id_couple id = function
    | Hyp((_,idpat),_) -> [idpat,VConstr (mkVar id)]
    | NoHypId _ -> [] in
  let rec apply_one_mhyp_context_rec mhyp lhyps_acc nocc = function
    | (id,hyp)::tl ->
      (match (get_pattern mhyp) with
      | Term t ->
        (try
          let lmeta = 
            verify_metas_coherence gl lmatch (Pattern.matches t hyp) in
          (get_id_couple id mhyp,[],lmeta,tl,(id,hyp),None)
         with | PatternMatchingFailure | Not_coherent_metas ->
          apply_one_mhyp_context_rec mhyp (lhyps_acc@[id,hyp]) 0 tl)
      | Subterm (ic,t) ->
        (try
          let (lm,ctxt) = sub_match nocc t hyp in
          let lmeta = verify_metas_coherence gl lmatch lm in
          (get_id_couple id mhyp,give_context ctxt
            ic,lmeta,tl,(id,hyp),Some nocc)
         with
        | NextOccurrence _ ->
          apply_one_mhyp_context_rec mhyp (lhyps_acc@[id,hyp]) 0 tl
        | Not_coherent_metas ->
          apply_one_mhyp_context_rec mhyp lhyps_acc (nocc + 1) ((id,hyp)::tl)))
    | [] -> raise No_match in
  let nocc =
    match noccopt with
    | None -> 0
    | Some n -> n in
  apply_one_mhyp_context_rec mhyp [] nocc lhyps

let constr_to_id loc c =
  if isVar c then destVar c
  else invalid_arg_loc (loc, "Not an identifier")

let constr_to_qid loc c =
  try qualid_of_sp (sp_of_global None (reference_of_constr c))
  with _ -> invalid_arg_loc (loc, "Not a global reference")

(* Check for LetTac *)
let check_clause_pattern ist gl (l,occl) =
  let sign = pf_hyps gl in
  let rec check acc = function
    | (hyp,l) :: rest ->
	let _,hyp = skip_metaid hyp in
	if List.mem hyp acc then
	  error ("Hypothesis "^(string_of_id hyp)^" occurs twice");
	if not (mem_named_context hyp sign) then
	  error ("No such hypothesis: " ^ (string_of_id hyp));
	(hyp,l)::(check (hyp::acc) rest)
    | [] -> []
  in (l,check [] occl)

(* Debug reference *)
let debug = ref DebugOff

(* Sets the debugger mode *)
let set_debug pos = debug := pos

(* Gives the state of debug *)
let get_debug () = !debug

(* Interprets an identifier which must be fresh *)
let eval_ident ist id =
  try match List.assoc id ist.lfun with
  | VIdentifier id -> id
  | _ -> user_err_loc(loc,"eval_ident",str "should be bound to an identifier")
  with Not_found -> id

let eval_integer lfun (loc,id) =
  try match List.assoc id lfun with
  | VInteger n -> ArgArg n
  | _ -> user_err_loc(loc,"eval_integer",str "should be bound to an integer")
  with Not_found -> user_err_loc (loc,"eval_integer",str "Unbound variable")

let constr_of_value env = function
  | VConstr csr -> csr
  | VIdentifier id -> constr_of_id env id
  | _ -> raise Not_found

let is_variable env id =
  List.mem id (ids_of_named_context (Environ.named_context env))

let variable_of_value env = function
  | VConstr c as v when isVar c -> destVar c
  | VIdentifier id' when is_variable env id' -> id'
  | _ -> raise Not_found

(* Extract a variable from a value, if any *)
let id_of_Identifier = variable_of_value

(* Extract a constr from a value, if any *)
let constr_of_VConstr = constr_of_value

(* Interprets a variable *)
let eval_variable ist gl (loc,id) =
  (* Look first in lfun for a value coercible to a variable *)
  try 
    let v = List.assoc id ist.lfun in
    try variable_of_value (pf_env gl) v
    with Not_found ->
      errorlabstrm "coerce_to_variable"
      (str "Cannot coerce" ++ spc () ++ pr_value (pf_env gl) v ++ spc () ++
      str "to a variable")
  with Not_found -> 
  (* Then look if bound in the proof context at calling time *)
  if is_variable (pf_env gl) id then id
  else
    user_err_loc (loc,"eval_variable",pr_id id ++ str " not found")

let hyp_interp = eval_variable

let eval_name ist = function
  | Anonymous -> Anonymous
  | Name id -> Name (eval_ident ist id)

let hyp_or_metanum_interp ist gl = function
  | AN id -> eval_variable ist gl (dummy_loc,id)
  | MetaNum (loc,n) -> constr_to_id loc (List.assoc n ist.lmatch)

let interp_pure_qualid is_applied env (loc,qid) =
  try VConstr (constr_of_reference (find_reference env qid))
  with Not_found ->
    let (dir,id) = repr_qualid qid in
    if not is_applied & dir = empty_dirpath then VIdentifier id
    else user_err_loc (loc,"interp_pure_qualid",str "Unknown reference")

(* Interprets a qualified name *)
let eval_ref ist env = function
  | Qualid locqid -> interp_pure_qualid false env locqid
  | Ident (loc,id) ->
      try unrec (List.assoc id ist.lfun)
      with Not_found -> interp_pure_qualid false env (loc,make_short_qualid id)

let reference_interp ist env qid =
  let v = eval_ref ist env qid in
  coerce_to_reference env v

let pf_reference_interp ist gl = reference_interp ist (pf_env gl)

(* Interprets a qualified name. This can be a metavariable to be injected *)
let qualid_or_metanum_interp ist = function
  | AN qid -> qid
  | MetaNum (loc,n) -> constr_to_qid loc (List.assoc n ist.lmatch)

let eval_ref_or_metanum ist gl = function
  | AN qid -> eval_ref ist gl qid
  | MetaNum (loc,n) -> VConstr (List.assoc n ist.lmatch)

let interp_evaluable_or_metanum ist env c =
  let c = eval_ref_or_metanum ist env c in
  coerce_to_evaluable_ref env c

let interp_inductive_or_metanum ist gl c =
  let c = eval_ref_or_metanum ist (pf_env gl) c in
  coerce_to_inductive c

(* Interprets an hypothesis name *)
let interp_hyp_location ist gl = function
  | InHyp id -> InHyp (hyp_interp ist gl (skip_metaid id))
  | InHypType id -> InHypType (hyp_interp ist gl (skip_metaid id))

let eval_opt_ident ist = option_app (eval_ident ist)

(* Interpretation of constructions *)

(* Extracted the constr list from lfun *)
let rec constr_list_aux env = function
  | (id,v)::tl -> 
      let (l1,l2) = constr_list_aux env tl in
      (try ((id,constr_of_value env v)::l1,l2)
       with Not_found -> 
	 (l1,(id,match v with VIdentifier id0 -> Some id0 | _ -> None)::l2))
  | [] -> ([],[])

let constr_list ist env = constr_list_aux env ist.lfun

let interp_constr ocl ist sigma env c =
  interp_constr_gen sigma env (constr_list ist env) ist.lmatch c ocl

let interp_openconstr ist gl c ocl =
  interp_openconstr_gen (project gl) (pf_env gl)
    (constr_list ist (pf_env gl)) ist.lmatch c ocl

let pf_interp_constr ist gl =
  interp_constr None ist (project gl) (pf_env gl)

(* Interprets a constr expression *)
let constr_interp ist sigma env c =
  let csr = interp_constr None ist sigma env c in
  begin
    db_constr ist.debug env csr;
    csr
  end

let pf_constr_interp ist gl c = constr_interp ist (project gl) (pf_env gl) c

(* Interprets a constr expression casted by the current goal *)
let cast_constr_interp ist gl c =
  let csr = interp_constr (Some (pf_concl gl)) ist (project gl) (pf_env gl) c in
  db_constr ist.debug (pf_env gl) csr;
  csr

(* Interprets an open constr expression casted by the current goal *)
let cast_openconstr_interp ist gl c =
  interp_openconstr ist gl c (Some (pf_concl gl))

(* Interprets a reduction expression *)
let unfold_interp ist env (l,qid) =
  (l,interp_evaluable_or_metanum ist env qid)

let flag_interp ist env red =
  { red
    with rConst = List.map (interp_evaluable_or_metanum ist env) red.rConst }

let pattern_interp ist sigma env (l,c) = (l,constr_interp ist sigma env c)

let pf_pattern_interp ist gl = pattern_interp ist (project gl) (pf_env gl)

let redexp_interp ist sigma env = function
  | Unfold l -> Unfold (List.map (unfold_interp ist env) l)
  | Fold l -> Fold (List.map (constr_interp ist sigma env) l)
  | Cbv f -> Cbv (flag_interp ist env f)
  | Lazy f -> Lazy (flag_interp ist env f)
  | Pattern l -> Pattern (List.map (pattern_interp ist sigma env) l)
  | Simpl o -> Simpl (option_app (pattern_interp ist sigma env) o)
  | (Red _ |  Hnf as r) -> r
  | ExtraRedExpr (s,c) -> ExtraRedExpr (s,constr_interp ist sigma env c)

let pf_redexp_interp ist gl = redexp_interp ist (project gl) (pf_env gl)

let interp_may_eval f ist gl = function
  | ConstrEval (r,c) ->
      let redexp = pf_redexp_interp ist gl  r in
      pf_reduction_of_redexp gl redexp (f ist gl c)
  | ConstrContext ((loc,s),c) ->
      (try
	let ic = f ist gl c
	and ctxt = constr_of_VConstr_context (List.assoc s ist.lfun) in
	subst_meta [-1,ic] ctxt
      with
	| Not_found ->
	    user_err_loc (loc, "constr_interp",
	    str "Unbound context identifier" ++ pr_id s))
  | ConstrTypeOf c -> pf_type_of gl (f ist gl c)
  | ConstrTerm c -> f ist gl c

(* Interprets a constr expression possibly to first evaluate *)
let constr_interp_may_eval ist gl c =
  let csr = interp_may_eval pf_interp_constr ist gl c in
  begin
    db_constr ist.debug (pf_env gl) csr;
    csr
  end

let rec interp_intro_pattern ist = function
  | IntroOrAndPattern l ->
      IntroOrAndPattern (List.map (List.map (interp_intro_pattern ist)) l)
  | IntroWildcard ->
      IntroWildcard
  | IntroIdentifier id ->
      IntroIdentifier (eval_ident ist id)

(* Quantified named or numbered hypothesis or hypothesis in context *)
(* (as in Inversion) *)
let interp_quantified_hypothesis ist gl = function
  | AnonHyp n -> AnonHyp n
  | NamedHyp id ->
      try match List.assoc id ist.lfun with
	| VInteger n -> AnonHyp n
	| VIdentifier id -> NamedHyp id
	| v -> NamedHyp (variable_of_value (pf_env gl) v)
      with Not_found -> NamedHyp id

let interp_induction_arg ist gl = function
  | ElimOnConstr c -> ElimOnConstr (pf_constr_interp ist gl c)
  | ElimOnAnonHyp n as x -> x
  | ElimOnIdent (loc,id) ->
      if Tactics.is_quantified_hypothesis id gl then ElimOnIdent (loc,id)
      else ElimOnConstr	(pf_constr_interp ist gl (CRef (Ident (loc,id))))

let binding_interp ist gl (loc,b,c) =
  (loc,interp_quantified_hypothesis ist gl b,pf_constr_interp ist gl c)

let bindings_interp ist gl = function
| NoBindings -> NoBindings
| ImplicitBindings l -> ImplicitBindings (List.map (pf_constr_interp ist gl) l)
| ExplicitBindings l -> ExplicitBindings (List.map (binding_interp ist gl) l)

let interp_constr_with_bindings ist gl (c,bl) =
  (pf_constr_interp ist gl c, bindings_interp ist gl bl)

(* Interprets a l-tac expression into a value *)
let rec val_interp ist gl tac =

  let value_interp ist =
    match tac with
    (* Immediate evaluation *)
    | TacFun (it,body) -> VFun (ist.lfun,it,body)
    | TacLetRecIn (lrc,u) -> letrec_interp ist gl lrc u
    | TacLetIn (l,u) ->
        let addlfun = letin_interp ist gl l in
        val_interp { ist with lfun=addlfun@ist.lfun } gl u
    | TacMatchContext (lr,lmr) -> match_context_interp ist gl lr lmr
    | TacMatch (c,lmr) -> match_interp ist gl c lmr
    | TacArg a -> tacarg_interp ist gl a
    (* Delayed evaluation *)
    | t -> VTactic (eval_tactic ist t)

 in
  match ist.debug with
    | DebugOn n ->
	debug_prompt n (Some gl) tac
	(fun v -> value_interp {ist with debug=v})
	(fun () -> VTactic tclIDTAC)
    | _ -> value_interp ist

and eval_tactic ist = function
  | TacAtom (loc,t) -> fun gl ->
      (try (interp_atomic ist gl t) gl
       with e -> Stdpp.raise_with_loc loc e)
  | TacFun (it,body) -> assert false
  | TacLetRecIn (lrc,u) -> assert false
  | TacLetIn (l,u) -> assert false
  | TacLetCut l -> letcut_interp ist l
  | TacMatchContext _ -> assert false
  | TacMatch (c,lmr) -> assert false
  | TacId -> tclIDTAC
  | TacFail n -> tclFAIL n
  | TacProgress tac -> tclPROGRESS (tactic_interp ist tac)
  | TacAbstract (tac,s) -> Tactics.tclABSTRACT s (tactic_interp ist tac)
  | TacThen (t1,t2) -> tclTHEN (tactic_interp ist t1) (tactic_interp ist t2)
  | TacThens (t,tl) ->
      tclTHENS (tactic_interp ist t) (List.map (tactic_interp ist) tl)
  | TacDo (n,tac) -> tclDO n (tactic_interp ist tac)
  | TacTry tac -> tclTRY (tactic_interp ist tac)
  | TacInfo tac -> tclINFO (tactic_interp ist tac)
  | TacRepeat tac -> tclREPEAT (tactic_interp ist tac)
  | TacOrelse (tac1,tac2) ->
        tclORELSE (tactic_interp ist tac1) (tactic_interp ist tac2)
  | TacFirst l -> tclFIRST (List.map (tactic_interp ist) l)
  | TacSolve l -> tclSOLVE (List.map (tactic_interp ist) l)
  | TacArg a -> assert false

and interp_ltac_qualid is_applied ist gl (loc,qid as lqid) =
  try val_interp ist gl (lookup qid)
  with Not_found -> interp_pure_qualid is_applied (pf_env gl) lqid

and interp_ltac_reference isapplied ist gl = function
  | Ident (loc,id) -> 
      (try unrec (List.assoc id ist.lfun)
      with | Not_found ->
        interp_ltac_qualid isapplied ist gl (loc,make_short_qualid id))
  | Qualid qid -> interp_ltac_qualid isapplied ist gl qid

and tacarg_interp ist gl = function
  | TacVoid -> VVoid
  | Reference r -> interp_ltac_reference false ist gl r
  | Integer n -> VInteger n
  | ConstrMayEval c -> VConstr (constr_interp_may_eval ist gl c)
  | MetaNumArg (_,n) -> VConstr (List.assoc n ist.lmatch)
  | MetaIdArg (loc,id) ->
      (try (* $id can occur in Grammar tactic... *)
        (unrec (List.assoc (id_of_string id) ist.lfun))
      with
        | Not_found -> error_syntactic_metavariables_not_allowed loc)
  | TacCall (loc,f,l) ->
      let fv = interp_ltac_reference true ist gl f
      and largs = List.map (tacarg_interp ist gl) l in
      List.iter check_is_value largs;
      app_interp ist gl fv largs loc
  | Tacexp t -> val_interp ist gl t
  | TacDynamic(_,t) ->
      let tg = (tag t) in
      if tg = "tactic" then
        let f = (tactic_out t) in val_interp ist gl (f ist)
      else if tg = "value" then
        value_out t
      else if tg = "constr" then
        VConstr (Pretyping.constr_out t)
      else
        anomaly_loc (loc, "Tacinterp.val_interp",
          (str "Unknown dynamic: <" ++ str (Dyn.tag t) ++ str ">"))

(* Interprets an application node *)
and app_interp ist gl fv largs loc =
  match fv with
    | VFun(olfun,var,body) ->
      let (newlfun,lvar,lval)=head_with_value (var,largs) in
      if lvar=[] then
	let v = val_interp { ist with lfun=newlfun@olfun } gl body in
        if lval=[] then v else app_interp ist gl v lval loc
      else
        VFun(newlfun@olfun,lvar,body)
    | _ ->
	user_err_loc (loc, "Tacinterp.app_interp",
          (str"Illegal tactic application"))

(* Gives the tactic corresponding to the tactic value *)
and tactic_of_value vle g =
  match vle with
  | VRTactic res -> res
  | VTactic tac -> tac g
  | VFun _ -> error "A fully applied tactic is expected"
  | _ -> raise NotTactic

(* Evaluation with FailError catching *)
and eval_with_fail interp tac goal =
  try 
    (match interp goal tac with
    | VTactic tac -> VRTactic (tac goal)
    | a -> a)
  with | FailError lvl ->
    if lvl = 0 then
      raise No_match
    else
      raise (FailError (lvl - 1))

(* Interprets recursive expressions *)
and letrec_interp ist gl lrc u =
  let lref = Array.to_list (Array.make (List.length lrc) (ref VVoid)) in
  let lenv =
    List.fold_right2 (fun ((loc,name),_) vref l -> (name,VRec vref)::l)
      lrc lref [] in
  let lve = List.map (fun ((loc,name),(var,body)) ->
                          (name,VFun(lenv@ist.lfun,var,body))) lrc in
  begin
    List.iter2 (fun vref (_,ve) -> vref:=ve) lref lve;
    val_interp { ist with lfun=lve@ist.lfun } gl u
  end

(* Interprets the clauses of a LetIn *)
and letin_interp ist gl = function
  | [] -> []
  | ((loc,id),None,t)::tl -> 
      let v = tacarg_interp ist gl t in
      check_is_value v;
      (id,v):: (letin_interp ist gl tl)

  | ((loc,id),Some com,tce)::tl ->
    let typ = interp_may_eval pf_interp_constr ist gl com
    and v = tacarg_interp ist gl tce in
    let csr = 
      try
	constr_of_value (pf_env gl) v
      with Not_found ->
      try
	let t = tactic_of_value v in
	let ndc = Environ.named_context (pf_env gl) in
	start_proof id IsLocal ndc typ (fun _ _ -> ());
	by t;
	let (_,({const_entry_body = pft},_,_)) = cook_proof () in
	delete_proof (dummy_loc,id);
        pft
      with | NotTactic ->
	delete_proof (dummy_loc,id);
	errorlabstrm "Tacinterp.letin_interp"
          (str "Term or fully applied tactic expected in Let")
    in (id,VConstr (mkCast (csr,typ)))::(letin_interp ist gl tl)

(* Interprets the clauses of a LetCut *)
and letcut_interp ist = function 
  | [] -> tclIDTAC
  | (id,c,tce)::tl -> fun gl ->
    let typ = constr_interp_may_eval ist gl c
    and v = tacarg_interp ist gl tce in
    let csr = 
      try
	constr_of_value (pf_env gl) v
      with Not_found ->
      try
	let t = tactic_of_value v in
	start_proof id IsLocal (pf_hyps gl) typ (fun _ _ -> ());
	by t;
	let (_,({const_entry_body = pft},_,_)) = cook_proof () in
	delete_proof (dummy_loc,id);
        pft
      with | NotTactic ->
	delete_proof (dummy_loc,id);
	errorlabstrm "Tacinterp.letin_interp"
          (str "Term or fully applied tactic expected in Let")
    in
    let cutt = h_cut typ
    and exat = h_exact csr in
    tclTHENSV cutt [|tclTHEN (introduction id) (letcut_interp ist tl);exat|] gl

(*      let lic = mkLetIn (Name id,csr,typ,ccl) in
      let ntac = refine (mkCast (mkMeta (Logic.new_meta ()),lic)) in
      tclTHEN ntac (tclTHEN (introduction id)
      (letcut_interp ist tl))*)

(* Interprets the Match Context expressions *)
and match_context_interp ist goal lr lmr =
  let rec apply_goal_sub ist nocc (id,c) csr mt mhyps hyps =
    try
      let (lgoal,ctxt) = sub_match nocc c csr in
      let lctxt = give_context ctxt id in
      if mhyps = [] then
        eval_with_fail
          (val_interp {ist with lfun=lctxt@ist.lfun; lmatch=lgoal@ist.lmatch})
          mt goal
      else
        apply_hyps_context ist goal mt lgoal mhyps hyps
    with
    | (FailError _) as e -> raise e
    | NextOccurrence _ -> raise No_match
    | No_match | _ ->
      apply_goal_sub ist (nocc + 1) (id,c) csr mt mhyps hyps in
  let rec apply_match_context ist = function
    | (All t)::tl ->
      (try
         eval_with_fail (val_interp ist) t goal
       with No_match | FailError _ -> apply_match_context ist tl
	 | e when Logic.catchable_exception e -> apply_match_context ist tl)
    | (Pat (mhyps,mgoal,mt))::tl ->
      let hyps = make_hyps (pf_hyps goal) in
      let hyps = if lr then List.rev hyps else hyps in
      let mhyps = List.rev mhyps (* Sens naturel *) in
      let concl = pf_concl goal in
      (match mgoal with
      |	Term mg ->
        (try
           (let lgoal = apply_matching mg concl in
            begin
            db_matched_concl ist.debug (pf_env goal) concl;
            if mhyps = [] then
              eval_with_fail
		(val_interp {ist with lmatch=lgoal@ist.lmatch}) mt goal
            else
              apply_hyps_context ist goal mt lgoal mhyps hyps
            end)
        with e when is_match_catchable e -> apply_match_context ist tl)
      |	Subterm (id,mg) ->
        (try
          apply_goal_sub ist 0 (id,mg) concl mt mhyps hyps
        with e when is_match_catchable e ->
	  apply_match_context ist tl))
    | _ ->
      errorlabstrm "Tacinterp.apply_match_context" (str
        "No matching clauses for Match Context")

  in
  let env = pf_env goal in
  apply_match_context ist 
    (read_match_rule (project goal) env (constr_list ist env) lmr)

(* Tries to match the hypotheses in a Match Context *)
and apply_hyps_context ist goal mt lgmatch mhyps hyps =
  let rec apply_hyps_context_rec mt lfun lmatch mhyps lhyps_mhyp
    lhyps_rest noccopt =
    match mhyps with
      | hd::tl ->
        let (lid,lc,lm,newlhyps,hyp_match,noccopt) =
          apply_one_mhyp_context goal lmatch hd lhyps_mhyp noccopt in
        begin
        db_matched_hyp ist.debug (pf_env goal) hyp_match;
        (try
        if tl = [] then
            eval_with_fail
              (val_interp {ist with lfun=lfun@lid@lc@ist.lfun;
                                    lmatch=lmatch@lm@ist.lmatch})
              mt goal
        else
          let nextlhyps =
            List.fold_left (fun l e -> if e = hyp_match then l else l@[e]) []
              lhyps_rest in
          apply_hyps_context_rec mt
            (lfun@lid@lc) (lmatch@lm) tl nextlhyps nextlhyps None
         with
        | (FailError _) as e -> raise e
	|  e when is_match_catchable e -> 
          (match noccopt with
          | None ->
            apply_hyps_context_rec mt lfun
              lmatch mhyps newlhyps lhyps_rest None
          | Some nocc ->
            apply_hyps_context_rec mt ist.lfun ist.lmatch mhyps
              (hyp_match::newlhyps) lhyps_rest (Some (nocc + 1))))
        end
      |	[] ->
        anomalylabstrm "apply_hyps_context_rec" (str
          "Empty list should not occur") in
  apply_hyps_context_rec mt [] lgmatch mhyps hyps hyps None

  (* Interprets extended tactic generic arguments *)
and genarg_interp ist goal x =
  match genarg_tag x with
  | BoolArgType -> in_gen wit_bool (out_gen rawwit_bool x)
  | IntArgType -> in_gen wit_int (out_gen rawwit_int x)
  | IntOrVarArgType ->
      let f = function
	| ArgVar locid -> eval_integer ist.lfun locid
	| ArgArg n as x -> x in
      in_gen wit_int_or_var (f (out_gen rawwit_int_or_var x))
  | StringArgType ->
      in_gen wit_string (out_gen rawwit_string x)
  | PreIdentArgType ->
      in_gen wit_pre_ident (out_gen rawwit_pre_ident x)
  | IdentArgType ->
      in_gen wit_ident (out_gen rawwit_ident x)
  | RefArgType ->
      in_gen wit_ref (pf_reference_interp ist goal (out_gen rawwit_ref x))
  | SortArgType ->
      in_gen wit_sort
        (destSort 
	  (pf_constr_interp ist goal (CSort (dummy_loc,out_gen rawwit_sort x))))
  | ConstrArgType ->
      in_gen wit_constr (pf_constr_interp ist goal (out_gen rawwit_constr x))
  | ConstrMayEvalArgType ->
      in_gen wit_constr_may_eval (constr_interp_may_eval ist goal (out_gen rawwit_constr_may_eval x))
  | QuantHypArgType ->
      in_gen wit_quant_hyp
        (interp_quantified_hypothesis ist goal (out_gen rawwit_quant_hyp x))
  | RedExprArgType ->
      in_gen wit_red_expr (pf_redexp_interp ist goal (out_gen rawwit_red_expr x))
  | TacticArgType -> in_gen wit_tactic (out_gen rawwit_tactic x)
  | CastedOpenConstrArgType ->
      in_gen wit_casted_open_constr 
        (cast_openconstr_interp ist goal (out_gen rawwit_casted_open_constr x))
  | ConstrWithBindingsArgType ->
      in_gen wit_constr_with_bindings
        (interp_constr_with_bindings ist goal (out_gen rawwit_constr_with_bindings x))
  | List0ArgType _ -> app_list0 (genarg_interp ist goal) x
  | List1ArgType _ -> app_list1 (genarg_interp ist goal) x
  | OptArgType _ -> app_opt (genarg_interp ist goal) x
  | PairArgType _ -> app_pair (genarg_interp ist goal) (genarg_interp ist goal) x
  | ExtraArgType s -> lookup_genarg_interp s ist goal x

(* Interprets the Match expressions *)
and match_interp ist g constr lmr =
  let rec apply_sub_match ist nocc (id,c) csr mt =
    try
      let (lm,ctxt) = sub_match nocc c csr in
      let lctxt = give_context ctxt id in
      eval_with_fail 
	(val_interp { ist with lfun=lctxt@ist.lfun; lmatch=lm@ist.lmatch})
        mt g
    with
      | NextOccurrence n -> raise No_match
      | (FailError _) as e -> raise e
      | e when is_match_catchable e ->
	  apply_sub_match ist (nocc + 1) (id,c) csr mt
  in
  let rec apply_match ist csr = function
    | (All t)::_ ->
        (try
          eval_with_fail (val_interp ist) t g
        with
          | (FailError _) as e -> raise e
	  | e when is_match_catchable e -> apply_match ist csr [])
    | (Pat ([],Term c,mt))::tl ->
        (try
	  eval_with_fail (val_interp
	    { ist with lmatch=(apply_matching c csr)@ist.lmatch }) mt g
         with
	   | (FailError _) as e -> raise e
	   | e when is_match_catchable e -> apply_match ist csr tl)
    | (Pat ([],Subterm (id,c),mt))::tl ->
        (try
          apply_sub_match ist 0 (id,c) csr mt
         with | No_match ->
	   apply_match ist csr tl)
    | _ ->
      errorlabstrm "Tacinterp.apply_match" (str
        "No matching clauses for Match") in
  let csr = constr_interp_may_eval ist g constr in
  let env = pf_env g in
  let ilr = read_match_rule (project g) env (constr_list ist env) lmr in
  apply_match ist csr ilr

(* Interprets tactic expressions : returns a "tactic" *)
and tactic_interp ist tac g =
  try tactic_of_value (val_interp ist g tac) g
  with | NotTactic ->
    errorlabstrm "Tacinterp.tac_interp" (str
      "Must be a command or must give a tactic value")

(* Interprets a primitive tactic *)
and interp_atomic ist gl = function
  (* Basic tactics *)
  | TacIntroPattern l ->
      Elim.h_intro_patterns (List.map (interp_intro_pattern ist) l)
  | TacIntrosUntil hyp ->
      h_intros_until (interp_quantified_hypothesis ist gl hyp)
  | TacIntroMove (ido,ido') ->
      h_intro_move (option_app (eval_ident ist) ido)
      (option_app (fun x -> eval_variable ist gl x) ido')
  | TacAssumption -> h_assumption
  | TacExact c -> h_exact (cast_constr_interp ist gl c)
  | TacApply cb -> h_apply (interp_constr_with_bindings ist gl cb)
  | TacElim (cb,cbo) ->
      h_elim (interp_constr_with_bindings ist gl cb)
                (option_app (interp_constr_with_bindings ist gl) cbo)
  | TacElimType c -> h_elim_type (pf_constr_interp ist gl c)
  | TacCase cb -> h_case (interp_constr_with_bindings ist gl cb)
  | TacCaseType c -> h_case_type (pf_constr_interp ist gl c)
  | TacFix (idopt,n) -> h_fix (eval_opt_ident ist idopt) n
  | TacMutualFix (id,n,l) ->
      let f (id,n,c) = (eval_ident ist id,n,pf_constr_interp ist gl c) in
      h_mutual_fix (eval_ident ist id) n (List.map f l)
  | TacCofix idopt -> h_cofix (eval_opt_ident ist idopt)
  | TacMutualCofix (id,l) ->
      let f (id,c) = (eval_ident ist id,pf_constr_interp ist gl c) in
      h_mutual_cofix (eval_ident ist id) (List.map f l)
  | TacCut c -> h_cut (pf_constr_interp ist gl c)
  | TacTrueCut (ido,c) -> h_true_cut (eval_opt_ident ist ido) (pf_constr_interp ist gl c)
  | TacForward (b,na,c) -> h_forward b (eval_name ist na) (pf_constr_interp ist gl c)
  | TacGeneralize cl -> h_generalize (List.map (pf_constr_interp ist gl) cl)
  | TacGeneralizeDep c -> h_generalize_dep (pf_constr_interp ist gl c)
  | TacLetTac (id,c,clp) ->
      let clp = check_clause_pattern ist gl clp in
      h_let_tac (eval_ident ist id) (pf_constr_interp ist gl c) clp
  | TacInstantiate (n,c) -> h_instantiate n (pf_constr_interp ist gl c)

  (* Automation tactics *)
  | TacTrivial l -> Auto.h_trivial l
  | TacAuto (n, l) -> Auto.h_auto n l
  | TacAutoTDB n -> Dhyp.h_auto_tdb n
  | TacDestructHyp (b,id) -> Dhyp.h_destructHyp b (hyp_interp ist gl id)
  | TacDestructConcl -> Dhyp.h_destructConcl
  | TacSuperAuto (n,l,b1,b2) -> Auto.h_superauto n l b1 b2
  | TacDAuto (n,p) -> Auto.h_dauto (n,p)

  (* Derived basic tactics *)
  | TacOldInduction h -> h_old_induction (interp_quantified_hypothesis ist gl h)
  | TacNewInduction (c,cbo,ids) ->
      h_new_induction (interp_induction_arg ist gl c)
        (option_app (interp_constr_with_bindings ist gl) cbo)
        (List.map (List.map (eval_ident ist)) ids)
  | TacOldDestruct h -> h_old_destruct (interp_quantified_hypothesis ist gl h)
  | TacNewDestruct (c,cbo,ids) -> 
      h_new_destruct (interp_induction_arg ist gl c)
        (option_app (interp_constr_with_bindings ist gl) cbo)
        (List.map (List.map (eval_ident ist)) ids)
  | TacDoubleInduction (h1,h2) ->
      let h1 = interp_quantified_hypothesis ist gl h1 in
      let h2 = interp_quantified_hypothesis ist gl h2 in
      Elim.h_double_induction h1 h2
  | TacDecomposeAnd c -> Elim.h_decompose_and (pf_constr_interp ist gl c)
  | TacDecomposeOr c -> Elim.h_decompose_or (pf_constr_interp ist gl c)
  | TacDecompose (l,c) ->
      let l = List.map (interp_inductive_or_metanum ist gl) l in
      Elim.h_decompose l (pf_constr_interp ist gl c)
  | TacSpecialize (n,l) -> h_specialize n (interp_constr_with_bindings ist gl l)
  | TacLApply c -> h_lapply (pf_constr_interp ist gl c)

  (* Context management *)
  | TacClear l -> h_clear (List.map (hyp_or_metanum_interp ist gl) l)
  | TacClearBody l -> h_clear_body (List.map (hyp_or_metanum_interp ist gl) l)
  | TacMove (dep,id1,id2) ->
      h_move dep (hyp_interp ist gl id1) (hyp_interp ist gl id2)
  | TacRename (id1,id2) ->
      h_rename (hyp_interp ist gl id1) (eval_ident ist (snd id2))

  (* Constructors *)
  | TacLeft bl -> h_left (bindings_interp ist gl bl)
  | TacRight bl -> h_right (bindings_interp ist gl bl)
  | TacSplit bl -> h_split (bindings_interp ist gl bl)
  | TacAnyConstructor t ->
      abstract_tactic (TacAnyConstructor t)
        (Tactics.any_constructor (option_app (tactic_interp ist) t))
  | TacConstructor (n,bl) ->
      h_constructor (skip_metaid n) (bindings_interp ist gl bl)

  (* Conversion *)
  | TacReduce (r,cl) ->
      h_reduce (pf_redexp_interp ist gl r) (List.map (interp_hyp_location ist gl) cl)
  | TacChange (occl,c,cl) ->
      h_change (option_app (pf_pattern_interp ist gl) occl)
        (pf_constr_interp ist gl c) (List.map (interp_hyp_location ist gl) cl)

  (* Equivalence relations *)
  | TacReflexivity -> h_reflexivity
  | TacSymmetry -> h_symmetry
  | TacTransitivity c -> h_transitivity (pf_constr_interp ist gl c)

  (* For extensions *)
  | TacExtend (loc,opn,l) ->
      fun gl -> vernac_tactic (opn,List.map (genarg_interp ist gl) l) gl
  | TacAlias (_,l,body) -> fun gl ->
    let f x = match genarg_tag x with
    | IdentArgType -> 
	let id = out_gen rawwit_ident x in
	(try VConstr (mkVar (eval_variable ist gl (dummy_loc,id)))
	 with Not_found -> VIdentifier id)
    | RefArgType -> VConstr (constr_of_reference (pf_reference_interp ist gl (out_gen rawwit_ref x)))
    | ConstrArgType -> VConstr (pf_constr_interp ist gl (out_gen rawwit_constr x))
    | ConstrMayEvalArgType ->
      VConstr (constr_interp_may_eval ist gl (out_gen rawwit_constr_may_eval x))
    | _ -> failwith "This generic type is not supported in alias"
    in
    let lfun = (List.map (fun (x,c) -> (x,f c)) l)@ist.lfun in
    tactic_of_value (val_interp { ist with lfun=lfun } gl body) gl

(* Interprets tactic arguments *)
let interp_tacarg sign ast = (*unvarg*) (val_interp sign ast)

(* Initial call for interpretation *)
let tac_interp lfun lmatch debug t = 
  tactic_interp { lfun=lfun; lmatch=lmatch; debug=debug } t

let interp = tac_interp [] [] (get_debug())

(* Hides interpretation for pretty-print *)
let hide_interp t ot gl =
  let te = glob_tactic ([],[],project gl,pf_env gl) t in
  match ot with 
  | None -> abstract_tactic_expr (TacArg (Tacexp t)) (interp t) gl
  | Some t' ->
      abstract_tactic_expr (TacArg (Tacexp t)) (tclTHEN (interp t) t') gl

(* For bad tactic calls *)
let bad_tactic_args s =
  anomalylabstrm s
    (str "Tactic " ++ str s ++ str " called with bad arguments")

(* Declaration of the TAC-DEFINITION object *)
let add (sp,td) = mactab := Gmap.add sp td !mactab

let register_tacdef (sp,td) = sp,td

let cache_md (_,defs) =
  (* Needs a rollback if something goes wrong *)
  List.iter (fun (sp,_) -> Nametab.push_tactic (Until 1) sp) defs;
  List.iter add (List.map register_tacdef defs)

let (inMD,outMD) =
  declare_object {(default_object "TAC-DEFINITION") with
     cache_function  = cache_md;
     open_function   = (fun i o -> if i=1 then cache_md o);
     export_function = (fun x -> Some x)}

(* Adds a definition for tactics in the table *)
let make_absolute_name (loc,id) =
  let sp = Lib.make_path id in
  if Gmap.mem sp !mactab then
    errorlabstrm "Tacinterp.add_tacdef" 
      (str "There is already a Meta Definition or a Tactic Definition named "
       ++ pr_sp sp);
  sp

let add_tacdef isrec tacl =
  let lfun = List.map (fun ((loc,id),_) -> id) tacl in
  let ist = ((if isrec then lfun else []), [], Evd.empty, Global.env()) in
  let tacl = List.map (fun (id,tac) -> (make_absolute_name id,tac)) tacl in
  let tacl = List.map (fun (id,def) -> (id,glob_tactic ist def)) tacl in
  let _ = Lib.add_leaf (List.hd lfun) (inMD tacl) in
  List.iter
    (fun id -> Options.if_verbose msgnl (pr_id id ++ str " is defined")) lfun

let interp_redexp env evc r = 
  let ist = { lfun=[]; lmatch=[]; debug=get_debug () } in
  redexp_interp ist evc env r

let _ = Auto.set_extern_interp (fun l -> tac_interp [] l (get_debug()))
let _ = Dhyp.set_extern_interp interp
