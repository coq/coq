(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Constrintern
open Closure
open RedFlags
open Declarations
open Entries
open Dyn
open Libobject
open Pattern
open Matching
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
open Tacexpr
open Safe_typing
open Typing
open Hiddentac
open Genarg
open Decl_kinds

let strip_meta id = (* For Grammar v7 compatibility *)
  let s = string_of_id id in
  if s.[0]='$' then id_of_string (String.sub s 1 (String.length s - 1))
  else id

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
  | VTactic of loc * tactic  (* For mixed ML/Ltac tactics (e.g. Tauto) *)
  | VRTactic of (goal list sigma * validation) (* For Match results *)
                                               (* Not a true value *)
  | VFun of (identifier*value) list * identifier option list * glob_tactic_expr
  | VVoid
  | VInteger of int
  | VIntroPattern of intro_pattern_expr (* includes idents which are not *)
                        (* bound as in "Intro H" but which may be bound *)
                        (* later, as in "tac" in "Intro H; tac" *)
  | VConstr of constr   (* includes idents known bound and references *)
  | VConstr_context of constr
  | VRec of value ref

let locate_tactic_call loc = function
  | VTactic (_,t) -> VTactic (loc,t)
  | v -> v

let locate_error_in_file dir = function
  | Stdpp.Exc_located (loc,e) -> Error_in_file ("",(true,dir,loc),e)
  | e -> Error_in_file ("",(true,dir,dummy_loc),e)

let catch_error loc tac g =
  try tac g
  with e when loc <> dummy_loc ->
    match e with
      |	Stdpp.Exc_located (_,e) -> raise (Stdpp.Exc_located (loc,e))
      |	e -> raise (Stdpp.Exc_located (loc,e))

(* Signature for interpretation: val_interp and interpretation functions *)
type interp_sign =
  { lfun : (identifier * value) list;
    debug : debug_info }

let check_is_value = function
  | VRTactic _ -> (* These are goals produced by Match *)
   error "Immediate match producing tactics not allowed in local definitions"
  | _ -> ()

(* For tactic_of_value *)
exception NotTactic

(* Gives the constr corresponding to a Constr_context tactic_arg *)
let constr_of_VConstr_context = function
  | VConstr_context c -> c
  | _ ->
    errorlabstrm "constr_of_VConstr_context" (str "not a context variable")

(* Displays a value *)
let pr_value env = function
  | VVoid -> str "()"
  | VInteger n -> int n
  | VIntroPattern ipat -> pr_intro_pattern ipat
  | VConstr c -> Printer.prterm_env env c
  | VConstr_context c -> Printer.prterm_env env c
  | (VTactic _ | VRTactic _ | VFun _ | VRec _) -> str "<fun>"

(* Transforms a named_context into a (string * constr) list *)
let make_hyps = List.map (fun (id,_,typ) -> (id, typ))

(* Transforms an id into a constr if possible, or fails *)
let constr_of_id env id = 
  construct_reference (Environ.named_context env) id

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
    | VIntroPattern (IntroIdentifier id)
        when Environ.evaluable_named id env -> EvalVarRef id
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


(* Table of "pervasives" macros tactics (e.g. auto, simpl, etc.) *)
let atomic_mactab = ref Idmap.empty
let add_primitive_tactic s tac =
  (if not !Options.v7 then
    let id = id_of_string s in
    atomic_mactab := Idmap.add id tac !atomic_mactab)

let _ =
  if not !Options.v7 then
    (let nocl = {onhyps=Some[];onconcl=true; concl_occs=[]} in
    List.iter
      (fun (s,t) -> add_primitive_tactic s (TacAtom(dummy_loc,t)))
      [ "red", TacReduce(Red false,nocl);
        "hnf", TacReduce(Hnf,nocl);
        "simpl", TacReduce(Simpl None,nocl);
        "compute", TacReduce(Cbv all_flags,nocl);
        "intro", TacIntroMove(None,None);
        "intros", TacIntroPattern [];
        "assumption", TacAssumption;
        "cofix", TacCofix None;
        "trivial", TacTrivial None;
        "auto", TacAuto(None,None);
        "left", TacLeft NoBindings;
        "right", TacRight NoBindings;
        "split", TacSplit(false,NoBindings);
        "constructor", TacAnyConstructor None;
        "reflexivity", TacReflexivity;
        "symmetry", TacSymmetry nocl
      ];
    List.iter
      (fun (s,t) -> add_primitive_tactic s t)
      [ "idtac",TacId "";
        "fail", TacFail(ArgArg 0,"");
        "fresh", TacArg(TacFreshId None)
      ])
 
let lookup_atomic id = Idmap.find id !atomic_mactab
let is_atomic id = Idmap.mem id !atomic_mactab
let is_atomic_kn kn =
  let (_,_,l) = repr_kn kn in
  is_atomic (id_of_label l)

(* Summary and Object declaration *)
let mactab = ref Gmap.empty

let lookup r = Gmap.find r !mactab

let _ =
  let init () = mactab := Gmap.empty in
  let freeze () = !mactab in
  let unfreeze fs = mactab := fs in
  Summary.declare_summary "tactic-definition"
    { Summary.freeze_function   = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function     = init;
      Summary.survive_module = false;
      Summary.survive_section   = false }

(* Interpretation of extra generic arguments *)
type glob_sign = {
  ltacvars : identifier list * identifier list;
     (* ltac variables and the subset of vars introduced by Intro/Let/... *)
  ltacrecvars : (identifier * ltac_constant) list;
     (* ltac recursive names *)
  gsigma : Evd.evar_map;
  genv : Environ.env }

type interp_genarg_type =
  (glob_sign -> raw_generic_argument -> glob_generic_argument) *
  (interp_sign -> goal sigma -> glob_generic_argument -> 
    closed_generic_argument) *
  (Names.substitution -> glob_generic_argument -> glob_generic_argument)

let extragenargtab =
  ref (Gmap.empty : (string,interp_genarg_type) Gmap.t)
let add_interp_genarg id f =
  extragenargtab := Gmap.add id f !extragenargtab
let lookup_genarg id = 
  try Gmap.find id !extragenargtab
  with Not_found -> failwith ("No interpretation function found for entry "^id)

let lookup_genarg_glob   id = let (f,_,_) = lookup_genarg id in f
let lookup_interp_genarg id = let (_,f,_) = lookup_genarg id in f
let lookup_genarg_subst  id = let (_,_,f) = lookup_genarg id in f

(* Unboxes VRec *)
let unrec = function
  | VRec v -> !v
  | a -> a

(*****************)
(* Globalization *)
(*****************)

(* We have identifier <| global_reference <| constr *)

let find_ident id sign = 
  List.mem id (fst sign.ltacvars) or 
  List.mem id (ids_of_named_context (Environ.named_context sign.genv))

let find_recvar qid sign = List.assoc qid sign.ltacrecvars

(* a "var" is a ltac var or a var introduced by an intro tactic *)
let find_var id sign = List.mem id (fst sign.ltacvars)

(* a "ctxvar" is a var introduced by an intro tactic (Intro/LetTac/...) *)
let find_ctxvar id sign = List.mem id (snd sign.ltacvars)

(* a "ltacvar" is an ltac var (Let-In/Fun/...) *)
let find_ltacvar id sign = find_var id sign & not (find_ctxvar id sign)

let find_hyp id sign =
  List.mem id (ids_of_named_context (Environ.named_context sign.genv))

(* Globalize a name introduced by Intro/LetTac/... ; it is allowed to *)
(* be fresh in which case it is binding later on *)
let intern_ident l ist id =
  (* We use identifier both for variables and new names; thus nothing to do *)
  if not (find_ident id ist) then l:=(id::fst !l,id::snd !l);
  id

let intern_name l ist = function
  | Anonymous -> Anonymous
  | Name id -> Name (intern_ident l ist id)

let vars_of_ist (lfun,_,_,env) =
  List.fold_left (fun s id -> Idset.add id s)
    (vars_of_env env) lfun

let get_current_context () =
    try Pfedit.get_current_goal_context ()
    with e when Logic.catchable_exception e -> 
      (Evd.empty, Global.env())

let strict_check = ref false

let adjust_loc loc = if !strict_check then dummy_loc else loc

(* Globalize a name which must be bound -- actually just check it is bound *)
let intern_hyp ist (loc,id as locid) =
  let (_,env) = get_current_context () in
  if not !strict_check then
    locid
  else if find_ident id ist then
    (dummy_loc,id)
  else
    Pretype_errors.error_var_not_found_loc loc id

let intern_hyp_or_metaid ist id = intern_hyp ist (skip_metaid id)

let intern_int_or_var ist = function
  | ArgVar locid as x -> ArgVar (intern_hyp ist locid)
  | ArgArg n as x -> x

let intern_inductive ist = function
  | Ident (loc,id) when find_var id ist -> ArgVar (loc,id)
  | r -> ArgArg (Nametab.global_inductive r)

exception NotSyntacticRef

let locate_reference qid =
  match Nametab.extended_locate qid with
    | TrueGlobal ref -> ref
    | SyntacticDef kn -> 
	match Syntax_def.search_syntactic_definition loc kn with
	  | Rawterm.RRef (_,ref) -> ref
	  | _ -> raise NotSyntacticRef

let intern_global_reference ist = function
  | Ident (loc,id) as r when find_var id ist -> ArgVar (loc,id)
  | r -> 
      let loc,qid = qualid_of_reference r in
      try ArgArg (loc,locate_reference qid)
      with _ -> 
	error_global_not_found_loc loc qid

let intern_tac_ref ist = function
  | Ident (loc,id) when find_ltacvar id ist -> ArgVar (loc,id)
  | Ident (loc,id) ->
      ArgArg (loc,
         try find_recvar id ist 
         with Not_found -> locate_tactic (make_short_qualid id))
  | r -> 
      let (loc,qid) = qualid_of_reference r in
      ArgArg (loc,locate_tactic qid)

let intern_tactic_reference ist r =
  try intern_tac_ref ist r
  with Not_found -> 
    let (loc,qid) = qualid_of_reference r in
    error_global_not_found_loc loc qid

let intern_constr_reference strict ist = function
  | Ident (_,id) when (not strict & find_hyp id ist) or find_ctxvar id ist ->
      RVar (loc,id), None
  | r ->
      let loc,qid = qualid_of_reference r in
      RRef (loc,locate_reference qid), if strict then None else Some (CRef r)

let intern_reference strict ist r =
  (try Reference (intern_tac_ref ist r)
   with Not_found ->
     (try
       ConstrMayEval (ConstrTerm (intern_constr_reference strict ist r))
      with Not_found ->
        (match r with
          | Ident (loc,id) when is_atomic id -> Tacexp (lookup_atomic id)
          | Ident (loc,id) when not strict -> IntroPattern (IntroIdentifier id)
          | _ ->
              let (loc,qid) = qualid_of_reference r in
              error_global_not_found_loc loc qid)))

let rec intern_intro_pattern lf ist = function
  | IntroOrAndPattern l ->
      IntroOrAndPattern (intern_case_intro_pattern lf ist l)
  | IntroWildcard ->
      IntroWildcard
  | IntroIdentifier id ->
      IntroIdentifier (intern_ident lf ist id)

and intern_case_intro_pattern lf ist =
  List.map (List.map (intern_intro_pattern lf ist))

let intern_quantified_hypothesis ist x =
  (* We use identifier both for variables and quantified hyps (no way to
     statically check the existence of a quantified hyp); thus nothing to do *)
  x

let intern_constr {ltacvars=lfun; gsigma=sigma; genv=env} c =
  let warn = if !strict_check then fun x -> x else Constrintern.for_grammar in
  let c' = 
    warn (Constrintern.interp_rawconstr_gen false sigma env 
      false (fst lfun,[])) c in
  begin if Options.do_translate () then try
      (* Try to infer old case and type annotations *)
      let _ = Pretyping.understand_gen_tcc sigma env [] None c' in 
      (* msgerrnl (str "Typage tactique OK");*)
      ()
    with e -> (*msgerrnl (str "Warning: can't type tactic");*) () end;
  (c',if !strict_check then None else Some c)

(* Globalize bindings *)
let intern_binding ist (loc,b,c) =
  (loc,intern_quantified_hypothesis ist b,intern_constr ist c)

let intern_bindings ist = function
  | NoBindings -> NoBindings
  | ImplicitBindings l -> ImplicitBindings (List.map (intern_constr ist) l)
  | ExplicitBindings l -> ExplicitBindings (List.map (intern_binding ist) l)

let intern_constr_with_bindings ist (c,bl) =
  (intern_constr ist c, intern_bindings ist bl)

let intern_clause_pattern ist (l,occl) =
  let rec check = function
    | (hyp,l) :: rest -> (intern_hyp ist (skip_metaid hyp),l)::(check rest)
    | [] -> []
  in (l,check occl)

  (* TODO: catch ltac vars *)
let intern_induction_arg ist = function
  | ElimOnConstr c -> ElimOnConstr (intern_constr ist c)
  | ElimOnAnonHyp n as x -> x
  | ElimOnIdent (loc,id) as x ->
      if !strict_check then
	(* If in a defined tactic, no intros-until *)
	ElimOnConstr (intern_constr ist (CRef (Ident (dummy_loc,id))))
      else
	ElimOnIdent (loc,id)

(* Globalizes a reduction expression *)
let intern_evaluable ist = function
  | Ident (loc,id) as r when find_ltacvar id ist -> ArgVar (loc,id)
  | Ident (_,id) when
      (not !strict_check & find_hyp id ist) or find_ctxvar id ist ->
      ArgArg (EvalVarRef id, None)
  | r ->
      let loc,qid = qualid_of_reference r in
      try
	let e = match locate_reference qid with
	  | ConstRef c -> EvalConstRef c
	  | VarRef c -> EvalVarRef c
	  | _ -> error_not_evaluable (pr_reference r) in
        let short_name = match r with
	  | Ident (loc,id) when not !strict_check -> Some (loc,id)
	  | _ -> None in
        ArgArg (e,short_name)
      with
	| NotSyntacticRef -> error_not_evaluable (pr_reference r)
	| Not_found ->
	match r with 
	  | Ident (loc,id) when not !strict_check ->
	      ArgArg (EvalVarRef id, Some (loc,id))
	  | _ -> error_global_not_found_loc loc qid

let intern_unfold ist (l,qid) = (l,intern_evaluable ist qid)

let intern_flag ist red =
  { red with rConst = List.map (intern_evaluable ist) red.rConst }

let intern_constr_occurrence ist (l,c) = (l,intern_constr ist c)

let intern_redexp ist = function
  | Unfold l -> Unfold (List.map (intern_unfold ist) l)
  | Fold l -> Fold (List.map (intern_constr ist) l)
  | Cbv f -> Cbv (intern_flag ist f)
  | Lazy f -> Lazy (intern_flag ist f)
  | Pattern l -> Pattern (List.map (intern_constr_occurrence ist) l)
  | Simpl o -> Simpl (option_app (intern_constr_occurrence ist) o)
  | (Red _ | Hnf | ExtraRedExpr _ as r) -> r

let intern_inversion_strength lf ist = function
  | NonDepInversion (k,idl,ids) ->
      NonDepInversion (k,List.map (intern_hyp_or_metaid ist) idl,
      option_app (intern_intro_pattern lf ist) ids)
  | DepInversion (k,copt,ids) ->
      DepInversion (k, option_app (intern_constr ist) copt,
      option_app (intern_intro_pattern lf ist) ids)
  | InversionUsing (c,idl) ->
      InversionUsing (intern_constr ist c, List.map (intern_hyp_or_metaid ist) idl)

(* Interprets an hypothesis name *)
let intern_hyp_location ist (id,occs,hl) =
  (intern_hyp ist (skip_metaid id), occs, hl)

(* Reads a pattern *)
let intern_pattern evc env lfun = function
  | Subterm (ido,pc) ->
      let (metas,pat) = interp_constrpattern_gen evc env lfun pc  in
      ido, metas, Subterm (ido,pat)
  | Term pc ->
      let (metas,pat) = interp_constrpattern_gen evc env lfun pc  in
      None, metas, Term pat

let intern_constr_may_eval ist = function
  | ConstrEval (r,c) -> ConstrEval (intern_redexp ist r,intern_constr ist c)
  | ConstrContext (locid,c) ->
      ConstrContext (intern_hyp ist locid,intern_constr ist c)
  | ConstrTypeOf c -> ConstrTypeOf (intern_constr ist c)
  | ConstrTerm c -> ConstrTerm (intern_constr ist c)

(* Reads the hypotheses of a Match Context rule *)
let rec intern_match_context_hyps evc env lfun = function
  | (Hyp ((_,na) as locna,mp))::tl ->
      let ido, metas1, pat = intern_pattern evc env lfun mp in
      let lfun, metas2, hyps = intern_match_context_hyps evc env lfun tl in
      let lfun' = name_cons na (option_cons ido lfun) in
      lfun', metas1@metas2, Hyp (locna,pat)::hyps
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
	  (loc, "intern_tactic", str "This variable is bound several times");
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


let clause_app f = function
    { onhyps=None; onconcl=b;concl_occs=nl } ->
      { onhyps=None; onconcl=b; concl_occs=nl }
  | { onhyps=Some l; onconcl=b;concl_occs=nl } ->
      { onhyps=Some(List.map f l); onconcl=b;concl_occs=nl}

(* Globalizes tactics : raw_tactic_expr -> glob_tactic_expr *)
let rec intern_atomic lf ist x =
  match (x:raw_atomic_tactic_expr) with 
  (* Basic tactics *)
  | TacIntroPattern l ->
      TacIntroPattern (List.map (intern_intro_pattern lf ist) l)
  | TacIntrosUntil hyp -> TacIntrosUntil (intern_quantified_hypothesis ist hyp)
  | TacIntroMove (ido,ido') ->
      TacIntroMove (option_app (intern_ident lf ist) ido,
          option_app (intern_hyp ist) ido')
  | TacAssumption -> TacAssumption
  | TacExact c -> TacExact (intern_constr ist c)
  | TacApply cb -> TacApply (intern_constr_with_bindings ist cb)
  | TacElim (cb,cbo) ->
      TacElim (intern_constr_with_bindings ist cb,
               option_app (intern_constr_with_bindings ist) cbo)
  | TacElimType c -> TacElimType (intern_constr ist c)
  | TacCase cb -> TacCase (intern_constr_with_bindings ist cb)
  | TacCaseType c -> TacCaseType (intern_constr ist c)
  | TacFix (idopt,n) -> TacFix (option_app (intern_ident lf ist) idopt,n)
  | TacMutualFix (id,n,l) ->
      let f (id,n,c) = (intern_ident lf ist id,n,intern_constr ist c) in
      TacMutualFix (intern_ident lf ist id, n, List.map f l)
  | TacCofix idopt -> TacCofix (option_app (intern_ident lf ist) idopt)
  | TacMutualCofix (id,l) ->
      let f (id,c) = (intern_ident lf ist id,intern_constr ist c) in
      TacMutualCofix (intern_ident lf ist id, List.map f l)
  | TacCut c -> TacCut (intern_constr ist c)
  | TacTrueCut (na,c) ->
      TacTrueCut (intern_name lf ist na, intern_constr ist c)
  | TacForward (b,na,c) ->
      TacForward (b,intern_name lf ist na,intern_constr ist c)
  | TacGeneralize cl -> TacGeneralize (List.map (intern_constr ist) cl)
  | TacGeneralizeDep c -> TacGeneralizeDep (intern_constr ist c)
  | TacLetTac (na,c,cls) ->
      let na = intern_name lf ist na in
      TacLetTac (na,intern_constr ist c,
                 (clause_app (intern_hyp_location ist) cls))
  | TacInstantiate (n,c,cls) -> 
      TacInstantiate (n,intern_constr ist c,
		      (clause_app (intern_hyp_location ist) cls))

  (* Automation tactics *)
  | TacTrivial l -> TacTrivial l
  | TacAuto (n,l) -> TacAuto (option_app (intern_int_or_var ist) n,l)
  | TacAutoTDB n -> TacAutoTDB n
  | TacDestructHyp (b,id) -> TacDestructHyp(b,intern_hyp ist id)
  | TacDestructConcl -> TacDestructConcl
  | TacSuperAuto (n,l,b1,b2) -> TacSuperAuto (n,l,b1,b2)
  | TacDAuto (n,p) -> TacDAuto (option_app (intern_int_or_var ist) n,p)

  (* Derived basic tactics *)
  | TacSimpleInduction (h,ids) ->
      TacSimpleInduction (intern_quantified_hypothesis ist h,ids)
  | TacNewInduction (c,cbo,(ids,ids')) ->
      TacNewInduction (intern_induction_arg ist c,
               option_app (intern_constr_with_bindings ist) cbo,
               (option_app (intern_intro_pattern lf ist) ids,ids'))
  | TacSimpleDestruct h ->
      TacSimpleDestruct (intern_quantified_hypothesis ist h)
  | TacNewDestruct (c,cbo,(ids,ids')) ->
      TacNewDestruct (intern_induction_arg ist c,
               option_app (intern_constr_with_bindings ist) cbo,
	       (option_app (intern_intro_pattern lf ist) ids,ids'))
  | TacDoubleInduction (h1,h2) ->
      let h1 = intern_quantified_hypothesis ist h1 in
      let h2 = intern_quantified_hypothesis ist h2 in
      TacDoubleInduction (h1,h2)
  | TacDecomposeAnd c -> TacDecomposeAnd (intern_constr ist c)
  | TacDecomposeOr c -> TacDecomposeOr (intern_constr ist c)
  | TacDecompose (l,c) -> let l = List.map (intern_inductive ist) l in
      TacDecompose (l,intern_constr ist c)
  | TacSpecialize (n,l) -> TacSpecialize (n,intern_constr_with_bindings ist l)
  | TacLApply c -> TacLApply (intern_constr ist c)

  (* Context management *)
  | TacClear l -> TacClear (List.map (intern_hyp_or_metaid ist) l)
  | TacClearBody l -> TacClearBody (List.map (intern_hyp_or_metaid ist) l)
  | TacMove (dep,id1,id2) ->
    TacMove (dep,intern_hyp_or_metaid ist id1,intern_hyp_or_metaid ist id2)
  | TacRename (id1,id2) -> TacRename (intern_hyp_or_metaid ist id1, intern_hyp_or_metaid ist id2)

  (* Constructors *)
  | TacLeft bl -> TacLeft (intern_bindings ist bl)
  | TacRight bl -> TacRight (intern_bindings ist bl)
  | TacSplit (b,bl) -> TacSplit (b,intern_bindings ist bl)
  | TacAnyConstructor t -> TacAnyConstructor (option_app (intern_tactic ist) t)
  | TacConstructor (n,bl) -> TacConstructor (n, intern_bindings ist bl)

  (* Conversion *)
  | TacReduce (r,cl) ->
      TacReduce (intern_redexp ist r, clause_app (intern_hyp_location ist) cl)
  | TacChange (occl,c,cl) ->
      TacChange (option_app (intern_constr_occurrence ist) occl,
        intern_constr ist c, clause_app (intern_hyp_location ist) cl)

  (* Equivalence relations *)
  | TacReflexivity -> TacReflexivity
  | TacSymmetry idopt -> 
      TacSymmetry (clause_app (intern_hyp_location ist) idopt)
  | TacTransitivity c -> TacTransitivity (intern_constr ist c)

  (* Equality and inversion *)
  | TacInversion (inv,hyp) ->
      TacInversion (intern_inversion_strength lf ist inv,
        intern_quantified_hypothesis ist hyp)

  (* For extensions *)
  | TacExtend (loc,opn,l) ->
      let _ = lookup_tactic opn in
      TacExtend (adjust_loc loc,opn,List.map (intern_genarg ist) l)
  | TacAlias (loc,s,l,(dir,body)) ->
      let (l1,l2) = ist.ltacvars in
      let ist' = { ist with ltacvars = ((List.map fst l)@l1,l2) } in
      let l = List.map (fun (id,a) -> (strip_meta id,intern_genarg ist a)) l in
      try TacAlias (loc,s,l,(dir,intern_tactic ist' body))
      with e -> raise (locate_error_in_file (string_of_dirpath dir) e)

and intern_tactic ist tac = (snd (intern_tactic_seq ist tac) : glob_tactic_expr)

and intern_tactic_seq ist = function
  (* Traducteur v7->v8 *)
  | TacAtom (_,TacReduce (Unfold [_,Ident (_,id)],_))
      when string_of_id id = "INZ" & !Options.translate_syntax
        -> ist.ltacvars, (TacId "")
  (* Fin traducteur v7->v8 *)

  | TacAtom (loc,t) ->
      let lf = ref ist.ltacvars in
      let t = intern_atomic lf ist t in
      !lf, TacAtom (adjust_loc loc, t)
  | TacFun tacfun -> ist.ltacvars, TacFun (intern_tactic_fun ist tacfun)
  | TacLetRecIn (lrc,u) ->
      let names = extract_names lrc in
      let (l1,l2) = ist.ltacvars in
      let ist = { ist with ltacvars = (names@l1,l2) } in
      let lrc = List.map (fun (n,b) -> (n,intern_tactic_fun ist b)) lrc in
      ist.ltacvars, TacLetRecIn (lrc,intern_tactic ist u)
  | TacLetIn (l,u) ->
      let l = List.map
        (fun (n,c,b) ->
          (n,option_app (intern_tactic ist) c, intern_tacarg !strict_check ist b)) l in
      let (l1,l2) = ist.ltacvars in
      let ist' = { ist with ltacvars = ((extract_let_names l)@l1,l2) } in
      ist.ltacvars, TacLetIn (l,intern_tactic ist' u)
  | TacMatchContext (lr,lmr) ->
      ist.ltacvars, TacMatchContext(lr, intern_match_rule ist lmr)
  | TacMatch (c,lmr) ->
      ist.ltacvars, TacMatch (intern_tactic ist c,intern_match_rule ist lmr)
  | TacId _ as x -> ist.ltacvars, x
  | TacFail (n,x) -> ist.ltacvars, TacFail (intern_int_or_var ist n,x)
  | TacProgress tac -> ist.ltacvars, TacProgress (intern_tactic ist tac)
  | TacAbstract (tac,s) -> ist.ltacvars, TacAbstract (intern_tactic ist tac,s)
  | TacThen (t1,t2) ->
      let lfun', t1 = intern_tactic_seq ist t1 in
      let lfun'', t2 = intern_tactic_seq { ist with ltacvars = lfun' } t2 in
      lfun'', TacThen (t1,t2)
  | TacThens (t,tl) ->
      let lfun', t = intern_tactic_seq ist t in
      (* Que faire en cas de (tac complexe avec Match et Thens; tac2) ?? *)
      lfun',
      TacThens (t, List.map (intern_tactic { ist with ltacvars = lfun' }) tl)
  | TacDo (n,tac) -> 
      ist.ltacvars, TacDo (intern_int_or_var ist n,intern_tactic ist tac)
  | TacTry tac -> ist.ltacvars, TacTry (intern_tactic ist tac)
  | TacInfo tac -> ist.ltacvars, TacInfo (intern_tactic ist tac)
  | TacRepeat tac -> ist.ltacvars, TacRepeat (intern_tactic ist tac)
  | TacOrelse (tac1,tac2) ->
      ist.ltacvars, TacOrelse (intern_tactic ist tac1,intern_tactic ist tac2)
  | TacFirst l -> ist.ltacvars, TacFirst (List.map (intern_tactic ist) l)
  | TacSolve l -> ist.ltacvars, TacSolve (List.map (intern_tactic ist) l)
  | TacArg a -> ist.ltacvars, TacArg (intern_tacarg true ist a)

and intern_tactic_fun ist (var,body) = 
  let (l1,l2) = ist.ltacvars in
  let lfun' = List.rev_append (filter_some var) l1 in
  (var,intern_tactic { ist with ltacvars = (lfun',l2) } body)

and intern_tacarg strict ist = function
  | TacVoid -> TacVoid
  | Reference r -> intern_reference strict ist r
  | IntroPattern ipat -> 
      let lf = ref([],[]) in (*How to know what names the intropattern binds?*)
      IntroPattern (intern_intro_pattern lf ist ipat)
  | Integer n -> Integer n
  | ConstrMayEval c -> ConstrMayEval (intern_constr_may_eval ist c)
  | MetaIdArg (loc,s) ->
      (* $id can occur in Grammar tactic... *)
      let id = id_of_string s in
      if find_ltacvar id ist or Options.do_translate()
      then Reference (ArgVar (adjust_loc loc,strip_meta id))
      else error_syntactic_metavariables_not_allowed loc
  | TacCall (loc,f,l) ->
      TacCall (loc,
        intern_tactic_reference ist f,
        List.map (intern_tacarg !strict_check ist) l)
  | TacFreshId _ as x -> x
  | Tacexp t -> Tacexp (intern_tactic ist t)
  | TacDynamic(loc,t) as x ->
      (match tag t with
	| "tactic" | "value" | "constr" -> x
	| s -> anomaly_loc (loc, "",
                 str "Unknown dynamic: <" ++ str s ++ str ">"))

(* Reads the rules of a Match Context or a Match *)
and intern_match_rule ist = function
  | (All tc)::tl ->
      All (intern_tactic ist tc) :: (intern_match_rule ist tl)
  | (Pat (rl,mp,tc))::tl ->
      let {ltacvars=(lfun,l2); gsigma=sigma; genv=env} = ist in
      let lfun',metas1,hyps = intern_match_context_hyps sigma env lfun rl in
      let ido,metas2,pat = intern_pattern sigma env lfun mp in
      let metas = list_uniquize (metas1@metas2) in
      let ist' = { ist with ltacvars = (metas@(option_cons ido lfun'),l2) } in
      Pat (hyps,pat,intern_tactic ist' tc) :: (intern_match_rule ist tl)
  | [] -> []

and intern_genarg ist x =
  match genarg_tag x with
  | BoolArgType -> in_gen globwit_bool (out_gen rawwit_bool x)
  | IntArgType -> in_gen globwit_int (out_gen rawwit_int x)
  | IntOrVarArgType ->
      in_gen globwit_int_or_var
        (intern_int_or_var ist (out_gen rawwit_int_or_var x))
  | StringArgType ->
      in_gen globwit_string (out_gen rawwit_string x)
  | PreIdentArgType ->
      in_gen globwit_pre_ident (out_gen rawwit_pre_ident x)
  | IntroPatternArgType ->
      let lf = ref ([],[]) in
      (* how to know which names are bound by the intropattern *)
      in_gen globwit_intro_pattern
        (intern_intro_pattern lf ist (out_gen rawwit_intro_pattern x))
  | IdentArgType ->
      let lf = ref ([],[]) in
      in_gen globwit_ident(intern_ident lf ist (out_gen rawwit_ident x))
  | HypArgType ->
      in_gen globwit_var (intern_hyp ist (out_gen rawwit_var x))
  | RefArgType ->
      in_gen globwit_ref (intern_global_reference ist (out_gen rawwit_ref x))
  | SortArgType ->
      in_gen globwit_sort (out_gen rawwit_sort x)
  | ConstrArgType ->
      in_gen globwit_constr (intern_constr ist (out_gen rawwit_constr x))
  | ConstrMayEvalArgType ->
      in_gen globwit_constr_may_eval 
        (intern_constr_may_eval ist (out_gen rawwit_constr_may_eval x))
  | QuantHypArgType ->
      in_gen globwit_quant_hyp
        (intern_quantified_hypothesis ist (out_gen rawwit_quant_hyp x))
  | RedExprArgType ->
      in_gen globwit_red_expr (intern_redexp ist (out_gen rawwit_red_expr x))
  | TacticArgType ->
      in_gen globwit_tactic (intern_tactic ist (out_gen rawwit_tactic x))
  | OpenConstrArgType ->
      in_gen globwit_open_constr
      ((),intern_constr ist (snd (out_gen rawwit_open_constr x)))
  | CastedOpenConstrArgType ->
      in_gen globwit_casted_open_constr 
        ((),intern_constr ist (snd (out_gen rawwit_casted_open_constr x)))
  | ConstrWithBindingsArgType ->
      in_gen globwit_constr_with_bindings
        (intern_constr_with_bindings ist (out_gen rawwit_constr_with_bindings x))
  | BindingsArgType ->
      in_gen globwit_bindings
        (intern_bindings ist (out_gen rawwit_bindings x))
  | List0ArgType _ -> app_list0 (intern_genarg ist) x
  | List1ArgType _ -> app_list1 (intern_genarg ist) x
  | OptArgType _ -> app_opt (intern_genarg ist) x
  | PairArgType _ -> app_pair (intern_genarg ist) (intern_genarg ist) x
  | ExtraArgType s -> lookup_genarg_glob s ist x

(************* End globalization ************)

(***************************************************************************)
(* Evaluation/interpretation *)

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

(* Reads a pattern by substituing vars of lfun *)
let eval_pattern lfun c = 
  let lvar = List.map (fun (id,c) -> (id,pattern_of_constr c)) lfun in
  instantiate_pattern lvar c

let read_pattern evc env lfun = function
  | Subterm (ido,pc) -> Subterm (ido,eval_pattern lfun pc)
  | Term pc -> Term (eval_pattern lfun pc)

(* Reads the hypotheses of a Match Context rule *)
let cons_and_check_name id l =
  if List.mem id l then
    user_err_loc (loc,"read_match_context_hyps",
      str ("Hypothesis pattern-matching variable "^(string_of_id id)^
      " used twice in the same pattern"))
  else id::l

let rec read_match_context_hyps evc env lfun lidh = function
  | (Hyp ((loc,na) as locna,mp))::tl ->
      let lidh' = name_fold cons_and_check_name na lidh in
      Hyp (locna,read_pattern evc env lfun mp)::
	(read_match_context_hyps evc env lfun lidh' tl)
  | [] -> []

(* Reads the rules of a Match Context or a Match *)
let rec read_match_rule evc env lfun = function
  | (All tc)::tl -> (All tc)::(read_match_rule evc env lfun tl)
  | (Pat (rl,mp,tc))::tl ->
      Pat (read_match_context_hyps evc env lfun [] rl,
      read_pattern evc env lfun mp,tc)
       ::(read_match_rule evc env lfun tl)
  | [] -> []

(* For Match Context and Match *)
exception No_match
exception Not_coherent_metas
exception Eval_fail of string

let is_failure = function
  | FailError _ | Stdpp.Exc_located (_,FailError _) -> true
  | _ -> false

let is_match_catchable = function
  | No_match | Eval_fail _ -> true
  | e -> is_failure e or Logic.catchable_exception e

let hack_fail_level_shift = ref 0
let hack_fail_level n =
  if n >= !hack_fail_level_shift then n - !hack_fail_level_shift else 0

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
    (matches pat csr)
  with
     PatternMatchingFailure -> raise No_match

(* Tries to match one hypothesis pattern with a list of hypotheses *)
let apply_one_mhyp_context ist env gl lmatch (hypname,pat) (lhyps,nocc) =
  let get_id_couple id = function
(*    | Name idpat -> [idpat,VIdentifier id]*)
    | Name idpat -> [idpat,VConstr (mkVar id)]
    | Anonymous -> [] in
  let rec apply_one_mhyp_context_rec nocc = function
    | (id,hyp)::tl as hyps ->
      (match pat with
      | Term t ->
        (try
          let lmeta = verify_metas_coherence gl lmatch (matches t hyp) in
          (get_id_couple id hypname,lmeta,(id,hyp),(tl,0))
        with
	| PatternMatchingFailure | Not_coherent_metas ->
            apply_one_mhyp_context_rec 0 tl)
      | Subterm (ic,t) ->
        (try
          let (lm,ctxt) = sub_match nocc t hyp in
          let lmeta = verify_metas_coherence gl lmatch lm in
          ((get_id_couple id hypname)@(give_context ctxt ic),
	   lmeta,(id,hyp),(hyps,nocc + 1))
         with
         | NextOccurrence _ ->
             apply_one_mhyp_context_rec 0 tl
         | Not_coherent_metas ->
             apply_one_mhyp_context_rec (nocc + 1) hyps))
    | [] ->
        db_hyp_pattern_failure ist.debug env (hypname,pat);
        raise No_match
      in
  apply_one_mhyp_context_rec nocc lhyps

let constr_to_id loc = function
  | VConstr c when isVar c -> destVar c
  | _ -> invalid_arg_loc (loc, "Not an identifier")

let constr_to_qid loc c =
  try shortest_qualid_of_global Idset.empty (reference_of_constr c)
  with _ -> invalid_arg_loc (loc, "Not a global reference")

(* Debug reference *)
let debug = ref DebugOff

(* Sets the debugger mode *)
let set_debug pos = debug := pos

(* Gives the state of debug *)
let get_debug () = !debug

(* Interprets an identifier which must be fresh *)
let interp_ident ist id =
  try match List.assoc id ist.lfun with
  | VIntroPattern (IntroIdentifier id) -> id
  | VConstr c as v when isVar c ->
      (* This happends e.g. in definitions like "Tac H = Clear H; Intro H" *)
      (* c is then expected not to belong to the proof context *)
      (* would be checkable if env were known from interp_ident *)
      destVar c
  | _ -> user_err_loc(loc,"interp_ident", str "An ltac name (" ++ pr_id id ++ 
         str ") should have been bound to an identifier")
  with Not_found -> id

let interp_intro_pattern_var ist id =
  try match List.assoc id ist.lfun with
  | VIntroPattern ipat -> ipat
  | VConstr c as v when isVar c ->
      (* This happends e.g. in definitions like "Tac H = Clear H; Intro H" *)
      (* c is then expected not to belong to the proof context *)
      (* would be checkable if env were known from interp_ident *)
      IntroIdentifier (destVar c)
  | _ -> user_err_loc(loc,"interp_ident", str "An ltac name (" ++ pr_id id ++ 
         str ") should have been bound to an introduction pattern")
  with Not_found -> IntroIdentifier id

let interp_int lfun (loc,id) =
  try match List.assoc id lfun with
  | VInteger n -> n
  | _ -> user_err_loc(loc,"interp_int",str "should be bound to an integer")
  with Not_found -> user_err_loc (loc,"interp_int",str "Unbound variable")

let interp_int_or_var ist = function
  | ArgVar locid -> interp_int ist.lfun locid
  | ArgArg n -> n

let constr_of_value env = function
  | VConstr csr -> csr
  | VIntroPattern (IntroIdentifier id) -> constr_of_id env id
  | _ -> raise Not_found

let is_variable env id =
  List.mem id (ids_of_named_context (Environ.named_context env))

let variable_of_value env = function
  | VConstr c as v when isVar c -> destVar c
  | VIntroPattern (IntroIdentifier id) when is_variable env id -> id
  | _ -> raise Not_found

(* Extract a variable from a value, if any *)
let id_of_Identifier = variable_of_value

(* Extract a constr from a value, if any *)
let constr_of_VConstr = constr_of_value

(* Interprets an variable *)
let interp_var ist gl (loc,id) =
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

(* Interprets an existing hypothesis (i.e. a declared variable) *)
let interp_hyp = interp_var

let interp_name ist = function
  | Anonymous -> Anonymous
  | Name id -> Name (interp_ident ist id)

let interp_clause_pattern ist gl (l,occl) =
  let rec check acc = function
    | (hyp,l) :: rest ->
	let hyp = interp_hyp ist gl hyp in
	if List.mem hyp acc then
	  error ("Hypothesis "^(string_of_id hyp)^" occurs twice");
	(hyp,l)::(check (hyp::acc) rest)
    | [] -> []
  in (l,check [] occl)

(* Interprets a qualified name *)
let interp_reference ist env = function
  | ArgArg (_,r) -> r
  | ArgVar (loc,id) -> coerce_to_reference env (unrec (List.assoc id ist.lfun))

let pf_interp_reference ist gl = interp_reference ist (pf_env gl)

let interp_inductive ist = function
  | ArgArg r -> r
  | ArgVar (_,id) -> coerce_to_inductive (unrec (List.assoc id ist.lfun))

let interp_evaluable ist env = function
  | ArgArg (r,Some (loc,id)) ->
      (* Maybe [id] has been introduced by Intro-like tactics *)
      (try match Environ.lookup_named id env with
        | (_,Some _,_) -> EvalVarRef id
        | _ -> error_not_evaluable (pr_id id)
      with Not_found ->
	match r with
	  | EvalConstRef _ -> r
	  | _ -> Pretype_errors.error_var_not_found_loc loc id)
  | ArgArg (r,None) -> r
  | ArgVar (_,id) -> 
      coerce_to_evaluable_ref env (unrec (List.assoc id ist.lfun))

(* Interprets an hypothesis name *)
let interp_hyp_location ist gl (id,occs,hl) = (interp_hyp ist gl id,occs,hl)

let interp_clause ist gl { onhyps=ol; onconcl=b; concl_occs=occs } =
  { onhyps=option_app(List.map (interp_hyp_location ist gl)) ol;
    onconcl=b;
    concl_occs=occs }

(* Interpretation of constructions *)

(* Extract the constr list from lfun *)
let rec constr_list_aux env = function
  | (id,v)::tl -> 
      let (l1,l2) = constr_list_aux env tl in
      (try ((id,constr_of_value env v)::l1,l2)
       with Not_found -> 
	 let ido = match v with
	   | VIntroPattern (IntroIdentifier id0) -> Some id0
	   | _ -> None in
	 (l1,(id,ido)::l2))
  | [] -> ([],[])

let constr_list ist env = constr_list_aux env ist.lfun

(*Extract the identifier list from lfun: join all branches (what to do else?)*)
let rec intropattern_ids = function
  | IntroIdentifier id -> [id]
  | IntroOrAndPattern ll -> 
      List.flatten (List.map intropattern_ids (List.flatten ll))
  | IntroWildcard -> []

let rec extract_ids = function
  | (id,VIntroPattern ipat)::tl -> intropattern_ids ipat @ extract_ids tl
  | _::tl -> extract_ids tl
  | [] -> []

let retype_list sigma env lst =
  List.fold_right (fun (x,csr) a ->
    try (x,Retyping.get_judgment_of env sigma csr)::a with
    | Anomaly _ -> a) lst []

let interp_casted_constr ocl ist sigma env (c,ce) =
  let (l1,l2) = constr_list ist env in
  let tl1 = retype_list sigma env l1 in
  let csr = 
    match ce with
    | None ->
	Pretyping.understand_gen_ltac sigma env (tl1,l2) ocl c
      (* If at toplevel (ce<>None), the error can be due to an incorrect
         context at globalization time: we retype with the now known
         intros/lettac/inversion hypothesis names *)
    | Some c -> interp_constr_gen sigma env (l1,l2) c ocl
  in
  db_constr ist.debug env csr;
  csr

let interp_constr ist sigma env c =
  interp_casted_constr None ist sigma env c

(* Interprets an open constr expression casted by the current goal *)
let pf_interp_openconstr_gen casted ist gl (c,ce) =
  let sigma = project gl in
  let env = pf_env gl in
  let (ltacvars,l) = constr_list ist env in
  let typs = retype_list sigma env ltacvars in
  let ocl = if casted then Some (pf_concl gl) else None in
  match ce with
  | None ->
      Pretyping.understand_gen_tcc sigma env typs ocl c
    (* If at toplevel (ce<>None), the error can be due to an incorrect
       context at globalization time: we retype with the now known
       intros/lettac/inversion hypothesis names *)
  | Some c -> interp_openconstr_gen sigma env (ltacvars,l) c ocl

let pf_interp_casted_openconstr = pf_interp_openconstr_gen true
let pf_interp_openconstr = pf_interp_openconstr_gen false

(* Interprets a constr expression *)
let pf_interp_constr ist gl =
  interp_constr ist (project gl) (pf_env gl)

(* Interprets a constr expression casted by the current goal *)
let pf_interp_casted_constr ist gl c =
  interp_casted_constr (Some(pf_concl gl)) ist (project gl) (pf_env gl) c

(* Interprets a reduction expression *)
let interp_unfold ist env (l,qid) =
  (l,interp_evaluable ist env qid)

let interp_flag ist env red =
  { red with rConst = List.map (interp_evaluable ist env) red.rConst }

let interp_pattern ist sigma env (l,c) = (l,interp_constr ist sigma env c)

let pf_interp_pattern ist gl = interp_pattern ist (project gl) (pf_env gl)

let redexp_interp ist sigma env = function
  | Unfold l -> Unfold (List.map (interp_unfold ist env) l)
  | Fold l -> Fold (List.map (interp_constr ist sigma env) l)
  | Cbv f -> Cbv (interp_flag ist env f)
  | Lazy f -> Lazy (interp_flag ist env f)
  | Pattern l -> Pattern (List.map (interp_pattern ist sigma env) l)
  | Simpl o -> Simpl (option_app (interp_pattern ist sigma env) o)
  | (Red _ | Hnf | ExtraRedExpr _ as r) -> r

let pf_redexp_interp ist gl = redexp_interp ist (project gl) (pf_env gl)

let interp_may_eval f ist gl = function
  | ConstrEval (r,c) ->
      let redexp = pf_redexp_interp ist gl  r in
      pf_reduction_of_redexp gl redexp (f ist gl c)
  | ConstrContext ((loc,s),c) ->
      (try
	let ic = f ist gl c
	and ctxt = constr_of_VConstr_context (List.assoc s ist.lfun) in
	subst_meta [special_meta,ic] ctxt
      with
	| Not_found ->
	    user_err_loc (loc, "interp_may_eval",
	    str "Unbound context identifier" ++ pr_id s))
  | ConstrTypeOf c -> pf_type_of gl (f ist gl c)
  | ConstrTerm c -> f ist gl c

(* Interprets a constr expression possibly to first evaluate *)
let interp_constr_may_eval ist gl c =
  let csr = interp_may_eval pf_interp_constr ist gl c in
  begin
    db_constr ist.debug (pf_env gl) csr;
    csr
  end

let rec interp_intro_pattern ist = function
  | IntroOrAndPattern l -> IntroOrAndPattern (interp_case_intro_pattern ist l)
  | IntroWildcard -> IntroWildcard
  | IntroIdentifier id -> interp_intro_pattern_var ist id

and interp_case_intro_pattern ist =
  List.map (List.map (interp_intro_pattern ist))

(* Quantified named or numbered hypothesis or hypothesis in context *)
(* (as in Inversion) *)
let interp_quantified_hypothesis ist = function
  | AnonHyp n -> AnonHyp n
  | NamedHyp id ->
      try match List.assoc id ist.lfun with
	| VInteger n -> AnonHyp n
	| VIntroPattern (IntroIdentifier id) -> NamedHyp id
	| _ -> raise Not_found
      with Not_found -> NamedHyp id

(* Quantified named or numbered hypothesis or hypothesis in context *)
(* (as in Inversion) *)
let interp_declared_or_quantified_hypothesis ist gl = function
  | AnonHyp n -> AnonHyp n
  | NamedHyp id ->
      try match List.assoc id ist.lfun with
	| VInteger n -> AnonHyp n
	| v -> NamedHyp (variable_of_value (pf_env gl) v)
      with Not_found -> NamedHyp id

let interp_induction_arg ist gl = function
  | ElimOnConstr c -> ElimOnConstr (pf_interp_constr ist gl c)
  | ElimOnAnonHyp n as x -> x
  | ElimOnIdent (loc,id) ->
      if Tactics.is_quantified_hypothesis id gl then ElimOnIdent (loc,id)
      else ElimOnConstr
	(pf_interp_constr ist gl (RVar (loc,id),Some (CRef (Ident (loc,id)))))

let interp_binding ist gl (loc,b,c) =
  (loc,interp_quantified_hypothesis ist b,pf_interp_constr ist gl c)

let interp_bindings ist gl = function
| NoBindings -> NoBindings
| ImplicitBindings l -> ImplicitBindings (List.map (pf_interp_constr ist gl) l)
| ExplicitBindings l -> ExplicitBindings (List.map (interp_binding ist gl) l)

let interp_constr_with_bindings ist gl (c,bl) =
  (pf_interp_constr ist gl c, interp_bindings ist gl bl)

(* Interprets an l-tac expression into a value *)
let rec val_interp ist gl (tac:glob_tactic_expr) =

  let value_interp ist = match tac with
  (* Immediate evaluation *)
  | TacFun (it,body) -> VFun (ist.lfun,it,body)
  | TacLetRecIn (lrc,u) -> letrec_interp ist gl lrc u
  | TacLetIn (l,u) ->
      let addlfun = interp_letin ist gl l in
      val_interp { ist with lfun=addlfun@ist.lfun } gl u
  | TacMatchContext (lr,lmr) -> interp_match_context ist gl lr lmr 
  | TacMatch (c,lmr) -> interp_match ist gl c lmr
  | TacArg a -> interp_tacarg ist gl a
  (* Delayed evaluation *)
  | t -> VTactic (dummy_loc,eval_tactic ist t)

  in check_for_interrupt (); 
    match ist.debug with
    | DebugOn lev ->
	debug_prompt lev gl tac (fun v -> value_interp {ist with debug=v})
    | _ -> value_interp ist

and eval_tactic ist = function
  | TacAtom (loc,t) -> fun gl -> catch_error loc (interp_atomic ist gl t) gl
  | TacFun (it,body) -> assert false
  | TacLetRecIn (lrc,u) -> assert false
  | TacLetIn (l,u) -> assert false
  | TacMatchContext _ -> assert false
  | TacMatch (c,lmr) -> assert false
  | TacId s -> tclIDTAC_MESSAGE s
  | TacFail (n,s) -> tclFAIL (hack_fail_level (interp_int_or_var ist n)) s
  | TacProgress tac -> tclPROGRESS (interp_tactic ist tac)
  | TacAbstract (tac,s) -> Tactics.tclABSTRACT s (interp_tactic ist tac)
  | TacThen (t1,t2) -> tclTHEN (interp_tactic ist t1) (interp_tactic ist t2)
  | TacThens (t,tl) ->
      tclTHENS (interp_tactic ist t) (List.map (interp_tactic ist) tl)
  | TacDo (n,tac) -> tclDO (interp_int_or_var ist n) (interp_tactic ist tac)
  | TacTry tac -> tclTRY (interp_tactic ist tac)
  | TacInfo tac -> tclINFO (interp_tactic ist tac)
  | TacRepeat tac -> tclREPEAT (interp_tactic ist tac)
  | TacOrelse (tac1,tac2) ->
        tclORELSE (interp_tactic ist tac1) (interp_tactic ist tac2)
  | TacFirst l -> tclFIRST (List.map (interp_tactic ist) l)
  | TacSolve l -> tclSOLVE (List.map (interp_tactic ist) l)
  | TacArg a -> assert false

and interp_ltac_reference isapplied ist gl = function
  | ArgVar (loc,id) -> unrec (List.assoc id ist.lfun)
  | ArgArg (loc,r) ->
      let v = val_interp {lfun=[];debug=ist.debug} gl (lookup r) in
      if isapplied then v else locate_tactic_call loc v

and interp_tacarg ist gl = function
  | TacVoid -> VVoid
  | Reference r -> interp_ltac_reference false ist gl r
  | Integer n -> VInteger n
  | IntroPattern ipat -> VIntroPattern ipat
  | ConstrMayEval c -> VConstr (interp_constr_may_eval ist gl c)
  | MetaIdArg (loc,id) -> assert false
  | TacCall (loc,f,l) ->
      let fv = interp_ltac_reference true ist gl f
      and largs = List.map (interp_tacarg ist gl) l in
      List.iter check_is_value largs;
      interp_app ist gl fv largs loc
  | TacFreshId idopt -> 
      let s = match idopt with None -> "H" | Some s -> s in
      let id = Tactics.fresh_id (extract_ids ist.lfun) (id_of_string s) gl in
      VIntroPattern (IntroIdentifier id)
  | Tacexp t -> val_interp ist gl t
  | TacDynamic(_,t) ->
      let tg = (tag t) in
      if tg = "tactic" then
        let f = (tactic_out t) in 
        val_interp ist gl
          (intern_tactic {
            ltacvars = (List.map fst ist.lfun,[]); ltacrecvars = [];
            gsigma = project gl; genv = pf_env gl }
            (f ist))
      else if tg = "value" then
        value_out t
      else if tg = "constr" then
        VConstr (Pretyping.constr_out t)
      else
        anomaly_loc (loc, "Tacinterp.val_interp",
          (str "Unknown dynamic: <" ++ str (Dyn.tag t) ++ str ">"))

(* Interprets an application node *)
and interp_app ist gl fv largs loc =
  match fv with
    | VFun(olfun,var,body) ->
      let (newlfun,lvar,lval)=head_with_value (var,largs) in
      if lvar=[] then
	let v = val_interp { ist with lfun=newlfun@olfun } gl body in
        if lval=[] then locate_tactic_call loc v
	else interp_app ist gl v lval loc
      else
        VFun(newlfun@olfun,lvar,body)
    | _ ->
	user_err_loc (loc, "Tacinterp.interp_app",
          (str"Illegal tactic application"))

(* Gives the tactic corresponding to the tactic value *)
and tactic_of_value vle g =
  match vle with
  | VRTactic res -> res
  | VTactic (loc,tac) -> catch_error loc tac g
  | VFun _ -> error "A fully applied tactic is expected"
  | _ -> raise NotTactic

(* Evaluation with FailError catching *)
and eval_with_fail ist tac goal =
  try
    (match val_interp ist goal tac with
    | VTactic (loc,tac) -> VRTactic (catch_error loc tac goal)
    | a -> a)
  with
    | Stdpp.Exc_located (_,FailError (0,s)) | FailError (0,s) ->
	raise (Eval_fail s)
    | Stdpp.Exc_located (s',FailError (lvl,s)) ->
	raise (Stdpp.Exc_located (s',FailError (lvl - 1, s)))
    | FailError (lvl,s) ->
	raise (FailError (lvl - 1, s))

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
and interp_letin ist gl = function
  | [] -> []
  | ((loc,id),None,t)::tl -> 
      let v = interp_tacarg ist gl t in
      check_is_value v;
      (id,v):: (interp_letin ist gl tl)
  | ((loc,id),Some com,tce)::tl ->
    let env = pf_env gl in
    let typ = constr_of_value env (val_interp ist gl com)
    and v = interp_tacarg ist gl tce in
    let csr = 
      try
	constr_of_value env v
      with Not_found ->
      try
	let t = tactic_of_value v in
	let ndc = Environ.named_context env in
	start_proof id IsLocal ndc typ (fun _ _ -> ());
	by t;
	let (_,({const_entry_body = pft},_,_)) = cook_proof () in
	delete_proof (dummy_loc,id);
        pft
      with | NotTactic ->
	delete_proof (dummy_loc,id);
	errorlabstrm "Tacinterp.interp_letin"
          (str "Term or fully applied tactic expected in Let")
    in (id,VConstr (mkCast (csr,typ)))::(interp_letin ist gl tl)

(* Interprets the Match Context expressions *)
and interp_match_context ist g lr lmr =
  let rec apply_goal_sub ist env goal nocc (id,c) csr mt mhyps hyps =
    try
      let (lgoal,ctxt) = sub_match nocc c csr in
      let lctxt = give_context ctxt id in
      if mhyps = [] then
	let lgoal = List.map (fun (id,c) -> (id,VConstr c)) lgoal in
        eval_with_fail { ist with lfun=lgoal@lctxt@ist.lfun } mt goal
      else
        apply_hyps_context ist env goal mt lctxt lgoal mhyps hyps
    with
    | e when is_failure e -> raise e
    | NextOccurrence _ -> raise No_match
    | e when is_match_catchable e ->
      apply_goal_sub ist env goal (nocc + 1) (id,c) csr mt mhyps hyps in
  let rec apply_match_context ist env goal nrs lex lpt = 
    begin
    if lex<>[] then db_pattern_rule ist.debug nrs (List.hd lex);
    match lpt with
    | (All t)::tl ->
      begin
        db_mc_pattern_success ist.debug;
        try eval_with_fail ist t goal
         with
         | e when is_failure e -> raise e
         | e when is_match_catchable e ->
           apply_match_context ist env goal (nrs+1) (List.tl lex) tl
      end
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
            begin
              db_mc_pattern_success ist.debug;
	      let lgoal = List.map (fun (id,c) -> (id,VConstr c)) lgoal in
              eval_with_fail {ist with lfun=lgoal@ist.lfun} mt goal
            end
            else
              apply_hyps_context ist env goal mt [] lgoal mhyps hyps
            end)
        with 
        | e when is_failure e -> raise e
        | e when is_match_catchable e ->
          begin 
            (match e with
            | No_match -> db_matching_failure ist.debug
            | Eval_fail s -> db_eval_failure ist.debug s
            | _ -> db_logic_failure ist.debug e);
            apply_match_context ist env goal (nrs+1) (List.tl lex) tl
          end)
      |	Subterm (id,mg) ->
        (try apply_goal_sub ist env goal 0 (id,mg) concl mt mhyps hyps
         with 
         | e when is_failure e -> raise e
         | e when is_match_catchable e ->
           apply_match_context ist env goal (nrs+1) (List.tl lex) tl))
    | _ ->
      errorlabstrm "Tacinterp.apply_match_context"
        (v 0 (str "No matching clauses for match goal" ++
        (if ist.debug=DebugOff then
           fnl() ++ str "(use \"Debug On\" for more info)"
         else mt())))
    end in
  let env = pf_env g in
  apply_match_context ist env g 0 lmr
    (read_match_rule (project g) env (fst (constr_list ist env)) lmr)

(* Tries to match the hypotheses in a Match Context *)
and apply_hyps_context ist env goal mt lctxt lgmatch mhyps hyps =
  let rec apply_hyps_context_rec lfun lmatch lhyps_rest current = function
    | Hyp ((_,hypname),mhyp)::tl as mhyps ->
        let (lids,lm,hyp_match,next) =
          apply_one_mhyp_context ist env goal lmatch (hypname,mhyp) current in
        db_matched_hyp ist.debug (pf_env goal) hyp_match hypname;
        begin 
	  try
            let nextlhyps = list_except hyp_match lhyps_rest in
            apply_hyps_context_rec (lfun@lids) (lmatch@lm) nextlhyps
	      (nextlhyps,0) tl
          with
          | e when is_failure e -> raise e
	  | e when is_match_catchable e -> 
	      apply_hyps_context_rec lfun lmatch lhyps_rest next mhyps
        end
    | [] ->
	let lmatch = List.map (fun (id,c) -> (id,VConstr c)) lmatch in
        db_mc_pattern_success ist.debug;
        eval_with_fail {ist with lfun=lmatch@lfun@ist.lfun} mt goal
  in
  apply_hyps_context_rec lctxt lgmatch hyps (hyps,0) mhyps

  (* Interprets extended tactic generic arguments *)
and interp_genarg ist goal x =
  match genarg_tag x with
  | BoolArgType -> in_gen wit_bool (out_gen globwit_bool x)
  | IntArgType -> in_gen wit_int (out_gen globwit_int x)
  | IntOrVarArgType ->
      in_gen wit_int_or_var
        (ArgArg (interp_int_or_var ist (out_gen globwit_int_or_var x)))
  | StringArgType ->
      in_gen wit_string (out_gen globwit_string x)
  | PreIdentArgType ->
      in_gen wit_pre_ident (out_gen globwit_pre_ident x)
  | IntroPatternArgType ->
      in_gen wit_intro_pattern
        (interp_intro_pattern ist (out_gen globwit_intro_pattern x))
  | IdentArgType ->
      in_gen wit_ident (interp_ident ist (out_gen globwit_ident x))
  | HypArgType ->
      in_gen wit_var (mkVar (interp_hyp ist goal (out_gen globwit_var x)))
  | RefArgType ->
      in_gen wit_ref (pf_interp_reference ist goal (out_gen globwit_ref x))
  | SortArgType ->
      in_gen wit_sort
        (destSort 
	  (pf_interp_constr ist goal 
	    (RSort (dummy_loc,out_gen globwit_sort x), None)))
  | ConstrArgType ->
      in_gen wit_constr (pf_interp_constr ist goal (out_gen globwit_constr x))
  | ConstrMayEvalArgType ->
      in_gen wit_constr_may_eval (interp_constr_may_eval ist goal (out_gen globwit_constr_may_eval x))
  | QuantHypArgType ->
      in_gen wit_quant_hyp
        (interp_declared_or_quantified_hypothesis ist goal
          (out_gen globwit_quant_hyp x))
  | RedExprArgType ->
      in_gen wit_red_expr (pf_redexp_interp ist goal (out_gen globwit_red_expr x))
  | TacticArgType -> in_gen wit_tactic (out_gen globwit_tactic x)
  | OpenConstrArgType ->
      in_gen wit_open_constr 
        (pf_interp_openconstr ist goal (snd (out_gen globwit_open_constr x)))
  | CastedOpenConstrArgType ->
      in_gen wit_casted_open_constr 
        (pf_interp_casted_openconstr ist goal (snd (out_gen globwit_casted_open_constr x)))
  | ConstrWithBindingsArgType ->
      in_gen wit_constr_with_bindings
        (interp_constr_with_bindings ist goal (out_gen globwit_constr_with_bindings x))
  | BindingsArgType ->
      in_gen wit_bindings
        (interp_bindings ist goal (out_gen globwit_bindings x))
  | List0ArgType _ -> app_list0 (interp_genarg ist goal) x
  | List1ArgType _ -> app_list1 (interp_genarg ist goal) x
  | OptArgType _ -> app_opt (interp_genarg ist goal) x
  | PairArgType _ -> app_pair (interp_genarg ist goal) (interp_genarg ist goal) x
  | ExtraArgType s -> lookup_interp_genarg s ist goal x

(* Interprets the Match expressions *)
and interp_match ist g constr lmr =
  let rec apply_sub_match ist nocc (id,c) csr mt =
    try 
      let (lm,ctxt) = sub_match nocc c csr in
      let lctxt = give_context ctxt id in
      let lm = List.map (fun (id,c) -> (id,VConstr c)) lm in
      val_interp {ist with lfun=lm@lctxt@ist.lfun} g mt
    with | NextOccurrence _ -> raise No_match
         | e when is_match_catchable e -> 
             apply_sub_match ist (nocc + 1) (id,c) csr mt
  in
  let rec apply_match ist csr = function
    | (All t)::_ ->
        (try val_interp ist g t
         with e when is_match_catchable e -> apply_match ist csr [])
    | (Pat ([],Term c,mt))::tl ->
        (try
	  let lm = apply_matching c csr in
	  let lm = List.map (fun (id,c) -> (id,VConstr c)) lm in
          val_interp
            { ist with lfun=lm@ist.lfun } g mt
         with e when is_match_catchable e -> apply_match ist csr tl)
    | (Pat ([],Subterm (id,c),mt))::tl ->
        (try
          apply_sub_match ist 0 (id,c) csr mt
         with | No_match ->
	   apply_match ist csr tl)
    | _ ->
      errorlabstrm "Tacinterp.apply_match" (str
        "No matching clauses for match") in
  let env = pf_env g in
  let csr =
    try constr_of_value env (val_interp ist g constr)
    with Not_found ->
      errorlabstrm "Tacinterp.apply_match" 
        (str "Argument of match does not evaluate to a term") in
  let ilr = read_match_rule (project g) env (fst (constr_list ist env)) lmr in
  try
    incr hack_fail_level_shift;
    let x = apply_match ist csr ilr in
    decr hack_fail_level_shift;
    x
  with e ->
    decr hack_fail_level_shift;
    raise e

(* Interprets tactic expressions : returns a "tactic" *)
and interp_tactic ist tac gl =
  try tactic_of_value (val_interp ist gl tac) gl
  with | NotTactic ->
    errorlabstrm "Tacinterp.interp_tactic" (str
      "Must be a command or must give a tactic value")

(* Interprets a primitive tactic *)
and interp_atomic ist gl = function
  (* Basic tactics *)
  | TacIntroPattern l ->
      h_intro_patterns (List.map (interp_intro_pattern ist) l)
  | TacIntrosUntil hyp ->
      h_intros_until (interp_quantified_hypothesis ist hyp)
  | TacIntroMove (ido,ido') ->
      h_intro_move (option_app (interp_ident ist) ido)
      (option_app (interp_hyp ist gl) ido')
  | TacAssumption -> h_assumption
  | TacExact c -> h_exact (pf_interp_casted_constr ist gl c)
  | TacApply cb -> h_apply (interp_constr_with_bindings ist gl cb)
  | TacElim (cb,cbo) ->
      h_elim (interp_constr_with_bindings ist gl cb)
                (option_app (interp_constr_with_bindings ist gl) cbo)
  | TacElimType c -> h_elim_type (pf_interp_constr ist gl c)
  | TacCase cb -> h_case (interp_constr_with_bindings ist gl cb)
  | TacCaseType c -> h_case_type (pf_interp_constr ist gl c)
  | TacFix (idopt,n) -> h_fix (option_app (interp_ident ist) idopt) n
  | TacMutualFix (id,n,l) ->
      let f (id,n,c) = (interp_ident ist id,n,pf_interp_constr ist gl c) in
      h_mutual_fix (interp_ident ist id) n (List.map f l)
  | TacCofix idopt -> h_cofix (option_app (interp_ident ist) idopt)
  | TacMutualCofix (id,l) ->
      let f (id,c) = (interp_ident ist id,pf_interp_constr ist gl c) in
      h_mutual_cofix (interp_ident ist id) (List.map f l)
  | TacCut c -> h_cut (pf_interp_constr ist gl c)
  | TacTrueCut (na,c) ->
      h_true_cut (interp_name ist na) (pf_interp_constr ist gl c)
  | TacForward (b,na,c) ->
      h_forward b (interp_name ist na) (pf_interp_constr ist gl c)
  | TacGeneralize cl -> h_generalize (List.map (pf_interp_constr ist gl) cl)
  | TacGeneralizeDep c -> h_generalize_dep (pf_interp_constr ist gl c)
  | TacLetTac (na,c,clp) ->
      let clp = interp_clause ist gl clp in
      h_let_tac (interp_name ist na) (pf_interp_constr ist gl c) clp
  | TacInstantiate (n,c,ido) -> h_instantiate n (pf_interp_constr ist gl c)
      (clause_app (interp_hyp_location ist gl) ido)

  (* Automation tactics *)
  | TacTrivial l -> Auto.h_trivial l
  | TacAuto (n, l) -> Auto.h_auto (option_app (interp_int_or_var ist) n) l
  | TacAutoTDB n -> Dhyp.h_auto_tdb n
  | TacDestructHyp (b,id) -> Dhyp.h_destructHyp b (interp_hyp ist gl id)
  | TacDestructConcl -> Dhyp.h_destructConcl
  | TacSuperAuto (n,l,b1,b2) -> Auto.h_superauto n l b1 b2
  | TacDAuto (n,p) -> Auto.h_dauto (option_app (interp_int_or_var ist) n,p)

  (* Derived basic tactics *)
  | TacSimpleInduction (h,ids) ->
      let h =
        if !Options.v7 then interp_declared_or_quantified_hypothesis ist gl h
        else interp_quantified_hypothesis ist h in
      h_simple_induction (h,ids)
  | TacNewInduction (c,cbo,(ids,ids')) ->
      h_new_induction (interp_induction_arg ist gl c)
        (option_app (interp_constr_with_bindings ist gl) cbo)
        (option_app (interp_intro_pattern ist) ids,ids')
  | TacSimpleDestruct h ->
      h_simple_destruct (interp_quantified_hypothesis ist h)
  | TacNewDestruct (c,cbo,(ids,ids')) -> 
      h_new_destruct (interp_induction_arg ist gl c)
        (option_app (interp_constr_with_bindings ist gl) cbo)
        (option_app (interp_intro_pattern ist) ids,ids')
  | TacDoubleInduction (h1,h2) ->
      let h1 = interp_quantified_hypothesis ist h1 in
      let h2 = interp_quantified_hypothesis ist h2 in
      Elim.h_double_induction h1 h2
  | TacDecomposeAnd c -> Elim.h_decompose_and (pf_interp_constr ist gl c)
  | TacDecomposeOr c -> Elim.h_decompose_or (pf_interp_constr ist gl c)
  | TacDecompose (l,c) ->
      let l = List.map (interp_inductive ist) l in
      Elim.h_decompose l (pf_interp_constr ist gl c)
  | TacSpecialize (n,l) ->
      h_specialize n (interp_constr_with_bindings ist gl l)
  | TacLApply c -> h_lapply (pf_interp_constr ist gl c)

  (* Context management *)
  | TacClear l -> h_clear (List.map (interp_hyp ist gl) l)
  | TacClearBody l -> h_clear_body (List.map (interp_hyp ist gl) l)
  | TacMove (dep,id1,id2) ->
      h_move dep (interp_hyp ist gl id1) (interp_hyp ist gl id2)
  | TacRename (id1,id2) ->
      h_rename (interp_hyp ist gl id1) (interp_ident ist (snd id2))

  (* Constructors *)
  | TacLeft bl -> h_left (interp_bindings ist gl bl)
  | TacRight bl -> h_right (interp_bindings ist gl bl)
  | TacSplit (_,bl) -> h_split (interp_bindings ist gl bl)
  | TacAnyConstructor t ->
      abstract_tactic (TacAnyConstructor t)
        (Tactics.any_constructor (option_app (interp_tactic ist) t))
  | TacConstructor (n,bl) ->
      h_constructor (skip_metaid n) (interp_bindings ist gl bl)

  (* Conversion *)
  | TacReduce (r,cl) ->
      h_reduce (pf_redexp_interp ist gl r) (interp_clause ist gl cl)
  | TacChange (occl,c,cl) ->
      h_change (option_app (pf_interp_pattern ist gl) occl)
        (pf_interp_constr ist gl c) (interp_clause ist gl cl)

  (* Equivalence relations *)
  | TacReflexivity -> h_reflexivity
  | TacSymmetry c -> h_symmetry (interp_clause ist gl c)
  | TacTransitivity c -> h_transitivity (pf_interp_constr ist gl c)

  (* Equality and inversion *)
  | TacInversion (DepInversion (k,c,ids),hyp) ->
      Inv.dinv k (option_app (pf_interp_constr ist gl) c)
        (option_app (interp_intro_pattern ist) ids)
        (interp_declared_or_quantified_hypothesis ist gl hyp)
  | TacInversion (NonDepInversion (k,idl,ids),hyp) ->
      Inv.inv_clause k 
        (option_app (interp_intro_pattern ist) ids)
        (List.map (interp_hyp ist gl) idl)
        (interp_declared_or_quantified_hypothesis ist gl hyp)
  | TacInversion (InversionUsing (c,idl),hyp) ->
      Leminv.lemInv_clause (interp_declared_or_quantified_hypothesis ist gl hyp)
        (pf_interp_constr ist gl c)
        (List.map (interp_hyp ist gl) idl)

  (* For extensions *)
  | TacExtend (loc,opn,l) ->
      fun gl -> vernac_tactic (opn,List.map (interp_genarg ist gl) l) gl
  | TacAlias (loc,_,l,(_,body)) -> fun gl ->
    let rec f x = match genarg_tag x with
    | IntArgType -> VInteger (out_gen globwit_int x)
    | IntOrVarArgType -> 
	VInteger (interp_int_or_var ist (out_gen globwit_int_or_var x))
    | PreIdentArgType ->
	failwith "pre-identifiers cannot be bound"
    | IntroPatternArgType ->
	VIntroPattern (out_gen globwit_intro_pattern x)
    | IdentArgType -> 
        VIntroPattern (IntroIdentifier (out_gen globwit_ident x))
    | HypArgType ->
	VConstr (mkVar (interp_var ist gl (out_gen globwit_var x)))
    | RefArgType -> 
        VConstr (constr_of_reference 
          (pf_interp_reference ist gl (out_gen globwit_ref x)))
    | SortArgType ->
	VConstr (mkSort (Pretyping.interp_sort (out_gen globwit_sort x)))
    | ConstrArgType ->
        VConstr (pf_interp_constr ist gl (out_gen globwit_constr x))
    | ConstrMayEvalArgType ->
	VConstr
          (interp_constr_may_eval ist gl (out_gen globwit_constr_may_eval x))
    | TacticArgType -> 
	val_interp ist gl (out_gen globwit_tactic x)
    | StringArgType | BoolArgType
    | QuantHypArgType | RedExprArgType | OpenConstrArgType
    | CastedOpenConstrArgType | ConstrWithBindingsArgType | BindingsArgType 
    | ExtraArgType _ | List0ArgType _ | List1ArgType _ | OptArgType _ | PairArgType _ 
	-> error "This generic type is not supported in alias"
    in
    let lfun = (List.map (fun (x,c) -> (x,f c)) l)@ist.lfun in
    let v = locate_tactic_call loc (val_interp { ist with lfun=lfun } gl body)
    in tactic_of_value v gl

(* Initial call for interpretation *)
let interp_tac_gen lfun debug t gl = 
  interp_tactic { lfun=lfun; debug=debug } 
    (intern_tactic {
      ltacvars = (List.map fst lfun, []); ltacrecvars = [];
      gsigma = project gl; genv = pf_env gl } t) gl

let eval_tactic t = interp_tactic { lfun=[]; debug=get_debug() } t

let interp t = interp_tac_gen [] (get_debug()) t

(* Hides interpretation for pretty-print *)
let hide_interp t ot gl =
  let ist = { ltacvars = ([],[]); ltacrecvars = []; 
            gsigma = project gl; genv = pf_env gl } in
  let te = intern_tactic ist t in
  let t = eval_tactic te in
  match ot with 
  | None -> abstract_tactic_expr (TacArg (Tacexp te)) t gl
  | Some t' -> abstract_tactic_expr (TacArg (Tacexp te)) (tclTHEN t t') gl

(***************************************************************************)
(* Substitution at module closing time *)

let subst_quantified_hypothesis _ x = x

let subst_declared_or_quantified_hypothesis _ x = x

let subst_inductive subst (kn,i) = (subst_kn subst kn,i)

let subst_rawconstr subst (c,e) =
  assert (e=None); (* e<>None only for toplevel tactics *)
  (subst_raw subst c,None)

let subst_binding subst (loc,b,c) =
  (loc,subst_quantified_hypothesis subst b,subst_rawconstr subst c)

let subst_bindings subst = function
  | NoBindings -> NoBindings
  | ImplicitBindings l -> ImplicitBindings (List.map (subst_rawconstr subst) l)
  | ExplicitBindings l -> ExplicitBindings (List.map (subst_binding subst) l)

let subst_raw_with_bindings subst (c,bl) =
  (subst_rawconstr subst c, subst_bindings subst bl)

let subst_induction_arg subst = function
  | ElimOnConstr c -> ElimOnConstr (subst_rawconstr subst c)
  | ElimOnAnonHyp n as x -> x
  | ElimOnIdent id as x -> x

let subst_evaluable_reference subst = function
  | EvalVarRef id -> EvalVarRef id
  | EvalConstRef kn -> EvalConstRef (subst_kn subst kn)

let subst_and_short_name f (c,n) =
  assert (n=None); (* since tacdef are strictly globalized *)
  (f c,None)

let subst_or_var f =  function
  | ArgVar _ as x -> x
  | ArgArg (x) -> ArgArg (f x)

let subst_located f (_loc,id) = (loc,f id)

let subst_reference subst = 
  subst_or_var (subst_located (subst_kn subst))

let subst_global_reference subst = 
  subst_or_var (subst_located (subst_global subst))

let subst_evaluable subst =
  subst_or_var (subst_and_short_name (subst_evaluable_reference subst))

let subst_unfold subst (l,e) = 
  (l,subst_evaluable subst e)

let subst_flag subst red =
  { red with rConst = List.map (subst_evaluable subst) red.rConst }

let subst_constr_occurrence subst (l,c) = (l,subst_rawconstr subst c)

let subst_redexp subst = function
  | Unfold l -> Unfold (List.map (subst_unfold subst) l)
  | Fold l -> Fold (List.map (subst_rawconstr subst) l)
  | Cbv f -> Cbv (subst_flag subst f)
  | Lazy f -> Lazy (subst_flag subst f)
  | Pattern l -> Pattern (List.map (subst_constr_occurrence subst) l)
  | Simpl o -> Simpl (option_app (subst_constr_occurrence subst) o)
  | (Red _ | Hnf | ExtraRedExpr _ as r) -> r

let subst_raw_may_eval subst = function
  | ConstrEval (r,c) -> ConstrEval (subst_redexp subst r,subst_rawconstr subst c)
  | ConstrContext (locid,c) -> ConstrContext (locid,subst_rawconstr subst c)
  | ConstrTypeOf c -> ConstrTypeOf (subst_rawconstr subst c)
  | ConstrTerm c -> ConstrTerm (subst_rawconstr subst c)

let subst_match_pattern subst = function
  | Subterm (ido,pc) -> Subterm (ido,subst_pattern subst pc)
  | Term pc -> Term (subst_pattern subst pc)

let rec subst_match_context_hyps subst = function
  | Hyp (locs,mp) :: tl ->
      Hyp (locs,subst_match_pattern subst mp)
      :: subst_match_context_hyps subst tl
  | [] -> []

let rec subst_atomic subst (t:glob_atomic_tactic_expr) = match t with
  (* Basic tactics *)
  | TacIntroPattern _ | TacIntrosUntil _ | TacIntroMove _ as x -> x
  | TacAssumption as x -> x
  | TacExact c -> TacExact (subst_rawconstr subst c)
  | TacApply cb -> TacApply (subst_raw_with_bindings subst cb)
  | TacElim (cb,cbo) ->
      TacElim (subst_raw_with_bindings subst cb,
               option_app (subst_raw_with_bindings subst) cbo)
  | TacElimType c -> TacElimType (subst_rawconstr subst c)
  | TacCase cb -> TacCase (subst_raw_with_bindings subst cb)
  | TacCaseType c -> TacCaseType (subst_rawconstr subst c)
  | TacFix (idopt,n) as x -> x
  | TacMutualFix (id,n,l) ->
      TacMutualFix(id,n,List.map (fun (id,n,c) -> (id,n,subst_rawconstr subst c)) l)
  | TacCofix idopt as x -> x
  | TacMutualCofix (id,l) ->
      TacMutualCofix (id, List.map (fun (id,c) -> (id,subst_rawconstr subst c)) l)
  | TacCut c -> TacCut (subst_rawconstr subst c)
  | TacTrueCut (ido,c) -> TacTrueCut (ido, subst_rawconstr subst c)
  | TacForward (b,na,c) -> TacForward (b,na,subst_rawconstr subst c)
  | TacGeneralize cl -> TacGeneralize (List.map (subst_rawconstr subst) cl)
  | TacGeneralizeDep c -> TacGeneralizeDep (subst_rawconstr subst c)
  | TacLetTac (id,c,clp) -> TacLetTac (id,subst_rawconstr subst c,clp)
  | TacInstantiate (n,c,ido) -> TacInstantiate (n,subst_rawconstr subst c,ido)

  (* Automation tactics *)
  | TacTrivial l -> TacTrivial l
  | TacAuto (n,l) -> TacAuto (n,l)
  | TacAutoTDB n -> TacAutoTDB n
  | TacDestructHyp (b,id) -> TacDestructHyp(b,id)
  | TacDestructConcl -> TacDestructConcl
  | TacSuperAuto (n,l,b1,b2) -> TacSuperAuto (n,l,b1,b2)
  | TacDAuto (n,p) -> TacDAuto (n,p)

  (* Derived basic tactics *)
  | TacSimpleInduction h as x -> x
  | TacNewInduction (c,cbo,ids) ->
      TacNewInduction (subst_induction_arg subst c,
               option_app (subst_raw_with_bindings subst) cbo, ids)
  | TacSimpleDestruct h as x -> x
  | TacNewDestruct (c,cbo,ids) ->
      TacNewDestruct (subst_induction_arg subst c,
               option_app (subst_raw_with_bindings subst) cbo, ids)
  | TacDoubleInduction (h1,h2) as x -> x
  | TacDecomposeAnd c -> TacDecomposeAnd (subst_rawconstr subst c)
  | TacDecomposeOr c -> TacDecomposeOr (subst_rawconstr subst c)
  | TacDecompose (l,c) ->
      let l = List.map (subst_or_var (subst_inductive subst)) l in
      TacDecompose (l,subst_rawconstr subst c)
  | TacSpecialize (n,l) -> TacSpecialize (n,subst_raw_with_bindings subst l)
  | TacLApply c -> TacLApply (subst_rawconstr subst c)

  (* Context management *)
  | TacClear l as x -> x
  | TacClearBody l as x -> x
  | TacMove (dep,id1,id2) as x -> x
  | TacRename (id1,id2) as x -> x

  (* Constructors *)
  | TacLeft bl -> TacLeft (subst_bindings subst bl)
  | TacRight bl -> TacRight (subst_bindings subst bl)
  | TacSplit (b,bl) -> TacSplit (b,subst_bindings subst bl)
  | TacAnyConstructor t -> TacAnyConstructor (option_app (subst_tactic subst) t)
  | TacConstructor (n,bl) -> TacConstructor (n, subst_bindings subst bl)

  (* Conversion *)
  | TacReduce (r,cl) -> TacReduce (subst_redexp subst r, cl)
  | TacChange (occl,c,cl) ->
      TacChange (option_app (subst_constr_occurrence subst) occl,
        subst_rawconstr subst c, cl)

  (* Equivalence relations *)
  | TacReflexivity | TacSymmetry _ as x -> x
  | TacTransitivity c -> TacTransitivity (subst_rawconstr subst c)

  (* Equality and inversion *)
  | TacInversion (DepInversion (k,c,l),hyp) ->
     TacInversion (DepInversion (k,option_app (subst_rawconstr subst) c,l),hyp)
  | TacInversion (NonDepInversion _,_) as x -> x
  | TacInversion (InversionUsing (c,cl),hyp) ->
      TacInversion (InversionUsing (subst_rawconstr subst c,cl),hyp)

  (* For extensions *)
  | TacExtend (_loc,opn,l) ->
      TacExtend (loc,opn,List.map (subst_genarg subst) l)
  | TacAlias (_,s,l,(dir,body)) ->
      TacAlias (loc,s,List.map (fun (id,a) -> (id,subst_genarg subst a)) l,
        (dir,subst_tactic subst body))

and subst_tactic subst (t:glob_tactic_expr) = match t with
  | TacAtom (_loc,t) -> TacAtom (loc, subst_atomic subst t)
  | TacFun tacfun -> TacFun (subst_tactic_fun subst tacfun)
  | TacLetRecIn (lrc,u) ->
      let lrc = List.map (fun (n,b) -> (n,subst_tactic_fun subst b)) lrc in
      TacLetRecIn (lrc,(subst_tactic subst u:glob_tactic_expr))
  | TacLetIn (l,u) ->
      let l = List.map (fun (n,c,b) -> (n,option_app (subst_tactic subst) c,subst_tacarg subst b)) l in
      TacLetIn (l,subst_tactic subst u)
  | TacMatchContext (lr,lmr) ->
      TacMatchContext(lr, subst_match_rule subst lmr)
  | TacMatch (c,lmr) ->
      TacMatch (subst_tactic subst c,subst_match_rule subst lmr)
  | TacId _ | TacFail _ as x -> x
  | TacProgress tac -> TacProgress (subst_tactic subst tac:glob_tactic_expr)
  | TacAbstract (tac,s) -> TacAbstract (subst_tactic subst tac,s)
  | TacThen (t1,t2) ->
      TacThen (subst_tactic subst t1,subst_tactic subst t2)
  | TacThens (t,tl) ->
      TacThens (subst_tactic subst t, List.map (subst_tactic subst) tl)
  | TacDo (n,tac) -> TacDo (n,subst_tactic subst tac)
  | TacTry tac -> TacTry (subst_tactic subst tac)
  | TacInfo tac -> TacInfo (subst_tactic subst tac)
  | TacRepeat tac -> TacRepeat (subst_tactic subst tac)
  | TacOrelse (tac1,tac2) ->
      TacOrelse (subst_tactic subst tac1,subst_tactic subst tac2)
  | TacFirst l -> TacFirst (List.map (subst_tactic subst) l)
  | TacSolve l -> TacSolve (List.map (subst_tactic subst) l)
  | TacArg a -> TacArg (subst_tacarg subst a)

and subst_tactic_fun subst (var,body) = (var,subst_tactic subst body)

and subst_tacarg subst = function
  | Reference r -> Reference (subst_reference subst r)
  | ConstrMayEval c -> ConstrMayEval (subst_raw_may_eval subst c)
  | MetaIdArg (_loc,_) -> assert false
  | TacCall (_loc,f,l) ->
      TacCall (_loc, subst_reference subst f, List.map (subst_tacarg subst) l)
  | (TacVoid | IntroPattern _ | Integer _ | TacFreshId _) as x -> x
  | Tacexp t -> Tacexp (subst_tactic subst t)
  | TacDynamic(_,t) as x ->
      (match tag t with
	| "tactic" | "value" | "constr" -> x
	| s -> anomaly_loc (loc, "Tacinterp.val_interp",
                 str "Unknown dynamic: <" ++ str s ++ str ">"))

(* Reads the rules of a Match Context or a Match *)
and subst_match_rule subst = function
  | (All tc)::tl ->
      (All (subst_tactic subst tc))::(subst_match_rule subst tl)
  | (Pat (rl,mp,tc))::tl ->
      let hyps = subst_match_context_hyps subst rl in
      let pat = subst_match_pattern subst mp in
      Pat (hyps,pat,subst_tactic subst tc)
      ::(subst_match_rule subst tl)
  | [] -> []

and subst_genarg subst (x:glob_generic_argument) =
  match genarg_tag x with
  | BoolArgType -> in_gen globwit_bool (out_gen globwit_bool x)
  | IntArgType -> in_gen globwit_int (out_gen globwit_int x)
  | IntOrVarArgType -> in_gen globwit_int_or_var (out_gen globwit_int_or_var x)
  | StringArgType -> in_gen globwit_string (out_gen globwit_string x)
  | PreIdentArgType -> in_gen globwit_pre_ident (out_gen globwit_pre_ident x)
  | IntroPatternArgType ->
      in_gen globwit_intro_pattern (out_gen globwit_intro_pattern x)
  | IdentArgType -> in_gen globwit_ident (out_gen globwit_ident x)
  | HypArgType -> in_gen globwit_var (out_gen globwit_var x)
  | RefArgType ->
      in_gen globwit_ref (subst_global_reference subst 
	(out_gen globwit_ref x))
  | SortArgType ->
      in_gen globwit_sort (out_gen globwit_sort x)
  | ConstrArgType ->
      in_gen globwit_constr (subst_rawconstr subst (out_gen globwit_constr x))
  | ConstrMayEvalArgType ->
      in_gen globwit_constr_may_eval (subst_raw_may_eval subst (out_gen globwit_constr_may_eval x))
  | QuantHypArgType ->
      in_gen globwit_quant_hyp
        (subst_declared_or_quantified_hypothesis subst 
          (out_gen globwit_quant_hyp x))
  | RedExprArgType ->
      in_gen globwit_red_expr (subst_redexp subst (out_gen globwit_red_expr x))
  | TacticArgType ->
      in_gen globwit_tactic (subst_tactic subst (out_gen globwit_tactic x))
  | OpenConstrArgType ->
      in_gen globwit_open_constr 
        ((),subst_rawconstr subst (snd (out_gen globwit_open_constr x)))
  | CastedOpenConstrArgType ->
      in_gen globwit_casted_open_constr 
        ((),subst_rawconstr subst (snd (out_gen globwit_casted_open_constr x)))
  | ConstrWithBindingsArgType ->
      in_gen globwit_constr_with_bindings
        (subst_raw_with_bindings subst (out_gen globwit_constr_with_bindings x))
  | BindingsArgType ->
      in_gen globwit_bindings
        (subst_bindings subst (out_gen globwit_bindings x))
  | List0ArgType _ -> app_list0 (subst_genarg subst) x
  | List1ArgType _ -> app_list1 (subst_genarg subst) x
  | OptArgType _ -> app_opt (subst_genarg subst) x
  | PairArgType _ -> app_pair (subst_genarg subst) (subst_genarg subst) x
  | ExtraArgType s -> lookup_genarg_subst s subst x

(***************************************************************************)
(* Tactic registration *)

(* For bad tactic calls *)
let bad_tactic_args s =
  anomalylabstrm s
    (str "Tactic " ++ str s ++ str " called with bad arguments")

(* Declaration of the TAC-DEFINITION object *)
let add (kn,td) = mactab := Gmap.add kn td !mactab

let load_md i ((sp,kn),defs) =
  let dp,_ = repr_path sp in
  let mp,dir,_ = repr_kn kn in
  List.iter (fun (id,t) -> 
    let sp = Libnames.make_path dp id in
    let kn = Names.make_kn mp dir (label_of_id id) in
    Nametab.push_tactic (Until i) sp kn;
    add (kn,t)) defs

let open_md i((sp,kn),defs) =
  let dp,_ = repr_path sp in
  let mp,dir,_ = repr_kn kn in
  List.iter (fun (id,t) -> 
    let sp = Libnames.make_path dp id in
    let kn = Names.make_kn mp dir (label_of_id id) in
    Nametab.push_tactic (Exactly i) sp kn) defs

let cache_md x = load_md 1 x

let subst_md (_,subst,defs) =
  List.map (fun (id,t) -> (id,subst_tactic subst t)) defs

let (inMD,outMD) =
  declare_object {(default_object "TAC-DEFINITION") with
     cache_function  = cache_md;
     load_function   = load_md;
     open_function   = open_md;
     subst_function = subst_md;
     classify_function = (fun (_,o) -> Substitute o);       
     export_function = (fun x -> Some x)}

(* Adds a definition for tactics in the table *)
let make_absolute_name (loc,id) =
  let kn = Lib.make_kn id in
  if Gmap.mem kn !mactab or is_atomic_kn kn then
    user_err_loc (loc,"Tacinterp.add_tacdef",
      str "There is already an Ltac named " ++ pr_id id);
  kn

let make_empty_glob_sign () =
  { ltacvars = ([],[]); ltacrecvars = []; 
    gsigma = Evd.empty; genv = Global.env() }

let add_tacdef isrec tacl =
(*  let isrec = if !Options.p1 then isrec else true in*)
  let rfun = List.map (fun ((loc,id as locid),_) -> (id,make_absolute_name locid)) tacl in
  let ist =
    {(make_empty_glob_sign()) with ltacrecvars = if isrec then rfun else []} in
  let gtacl =
    List.map (fun ((_,id),def) ->
      (id,Options.with_option strict_check (intern_tactic ist) def))
      tacl in
  let id0 = fst (List.hd rfun) in
  let _ = Lib.add_leaf id0 (inMD gtacl) in
  List.iter
    (fun (id,_) -> Options.if_verbose msgnl (pr_id id ++ str " is defined"))
    rfun

(***************************************************************************)
(* Other entry points *)

let glob_tactic x = intern_tactic (make_empty_glob_sign ()) x

let glob_tactic_env l env x = 
  intern_tactic
    { ltacvars = (l,[]); ltacrecvars = []; gsigma = Evd.empty; genv = env }
    x

let interp_redexp env evc r = 
  let ist = { lfun=[]; debug=get_debug () } in
  let gist = {(make_empty_glob_sign ()) with genv = env; gsigma = evc } in
  redexp_interp ist evc env (intern_redexp gist r)

(***************************************************************************)
(* Backwarding recursive needs of tactic glob/interp/eval functions *)

let _ = Auto.set_extern_interp
  (fun l -> 
    let l = List.map (fun (id,c) -> (id,VConstr c)) l in
    interp_tactic {lfun=l;debug=get_debug()})
let _ = Auto.set_extern_intern_tac 
  (fun l ->
    Options.with_option strict_check
    (intern_tactic {(make_empty_glob_sign()) with ltacvars=(l,[])}))
let _ = Auto.set_extern_subst_tactic subst_tactic
let _ = Dhyp.set_extern_interp eval_tactic
let _ = Dhyp.set_extern_intern_tac
  (fun t -> intern_tactic (make_empty_glob_sign()) t)
