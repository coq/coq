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
open Topconstr
open Term
open Termops
open Tacexpr
open Safe_typing
open Typing
open Hiddentac
open Genarg
open Decl_kinds
open Mod_subst
open Printer
open Inductiveops
open Syntax_def
open Pretyping
open Pretyping.Default
open Pcoq

(* arnaud: trucs factices *)
type tactic = Tacticals.tactic
type 'a sigma = 'a Tacticals.sigma
type goal = Tacticals.goal
type validation = Tacticals.validation

module Pfedit =
  struct
    let get_current_goal_context _ = Util.anomaly "Tacinterp.Pfedit.get_current_goal_context: fantome"
  end
let pf_apply _ = Util.anomaly "Tacinterp.pf_apply: fantome"
let pf_conv_x _ = Util.anomaly "Tacinterp.pf_conv_x: fantome"
let db_hyp_pattern_failure _ = Util.anomaly "Tacinterp.db_hyp_pattern_failure: fantome"
let explain_logic_error = ref (fun _ -> Util.anomaly "Tacinterp.explain_logic_error: fantome")
let explain_logic_error_no_anomaly = ref (fun _ -> Util.anomaly "Tacinterp.explain_logic_error_no_anomaly: fantome")
let pf_env _ = Util.anomaly "Tacinterp.pf_env: fantome"
let start_proof _ = Util.anomaly "Tacinterp.start_proof: fantome"
let by _ = Util.anomaly "Tacinterp.by: fantome"
let tclCOMPLETE _ = Util.anomaly "Tacinterp.tclCOMPLETE: fantome"
let cook_proof  _ = Util.anomaly "Tacinterp.cook_proof: fantome"
let delete_current_proof _ = Util.anomaly "Tacinterp.delete_current_proof: fantome"
let db_constr _ = Util.anomaly "Tacinterp.db_constr: fantome"
let pf_concl _ = Util.anomaly "Tacinterp.pf_concl: fantome"
let project _ = Util.anomaly "Tacinterp.project: fantome"
let pf_reduction_of_red_expr _ = Util.anomaly "Tacinterp.pf_reduction_of_red_expr: fantome"
let pf_type_of _ = Util.anomaly "Tacinterp.pf_type_of: fantome"
let debug_prompt _ = Util.anomaly "Tacinterp.debug_prompt: fantome"
let tclIDTAC_MESSAGE _ = Util.anomaly "Tacinterp.tclIDTAC_MESSAGE: fantome"
let tclFAIL _ = Util.anomaly "Tacinterp.tclFAIL: fantome"
let tclPROGRESS _ = Util.anomaly "Tacinterp.tclPROGRESS: fantome"
let tclTHENS3PARTS _ = Util.anomaly "Tacinterp.tclTHENS3PARTS: fantome"
let tclTHENS _ = Util.anomaly "Tacinterp.tclTHENS: fantome"
let tclDO _ = Util.anomaly "Tacinterp.tclDO: fantome"
let tclTRY  _ = Util.anomaly "Tacinterp.tclTRY: fantome"
let tclINFO _ = Util.anomaly "Tacinterp.tclINFO: fantome"
let tclREPEAT _ = Util.anomaly "Tacinterp.tclREPEAT: fantome"
let tclORELSE _ = Util.anomaly "Tacinterp.tclORELSE: fantome"
let tclFIRST _ = Util.anomaly "Tacinterp.tclFIRST: fantome"
let tclSOLVE _ = Util.anomaly "Tacinterp.tclSOLVE: fantome"
let delete_proof _ = Util.anomaly "Tacinterp.delete_proof: fantome"
let db_pattern_rule _ = Util.anomaly "Tacinterp.db_pattern_rule: fantome"
let db_mc_pattern_success  _ = Util.anomaly "Tacinterp.db_mc_pattern_success: fantome"
let pf_hyps _ = Util.anomaly "Tacinterp.pf_hyps: fantome"
let db_matched_concl _ = Util.anomaly "Tacinterp.db_matched_concl: fantome"
let db_matching_failure _ = Util.anomaly "Tacinterp.db_matching_failure: fantome"
let db_eval_failure _ = Util.anomaly "Tacinterp.db_eval_failure: fantome"
let db_logic_failure _ = Util.anomaly "Tacinterp.db_logic_failure: fantome"
let db_matched_hyp _ = Util.anomaly "Tacinterp.db_matched_hyp: fantome"
let abstract_tactic  _ = Util.anomaly "Tacinterp.abstract_tactic: fantome"
let abstract_extended_tactic _ = Util.anomaly "Tacinterp.abstract_extended_tactic: fantome"
let abstract_tactic_expr _ = Util.anomaly "Tacinterp.abstract_tactic_expr: fantome"
let tclTHEN _ = Util.anomaly "Tacinterp.tclTHEN: fantome"

type debug_info = Tactic_debug.debug_info
open Tactic_debug
exception FailError of (int * Pp.std_ppcmds)
(* arnaud: /trucs factices *)

let safe_msgnl s =
    try msgnl s with e -> 
      msgnl 
	(str "bug in the debugger : " ++
         str "an exception is raised while printing debug information")

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
  | VConstr of constr   (* includes idents known to be bound and references *)
  | VConstr_context of constr
  | VList of value list
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
      avoid_ids : identifier list; (* ids inherited from the call context
				      (needed to get fresh ids) *)
      debug : debug_info;
      last_loc : loc }

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
let rec pr_value env = function
  | VVoid -> str "()"
  | VInteger n -> int n
  | VIntroPattern ipat -> pr_intro_pattern ipat
  | VConstr c | VConstr_context c ->
      (match env with Some env -> pr_lconstr_env env c | _ -> str "a term")
  | (VTactic _ | VRTactic _ | VFun _ | VRec _) -> str "a tactic"
  | VList [] -> str "an empty list"
  | VList (a::_) ->
      str "a list (first element is " ++ pr_value env a ++ str")"

(* Transforms a named_context into a (string * constr) list *)
let make_hyps = List.map (fun (id,_,typ) -> (id, typ))

(* Transforms an id into a constr if possible, or fails *)
let constr_of_id env id = 
  construct_reference (Environ.named_context env) id

(* To embed tactics *)
let ((tactic_in : (interp_sign -> raw_tactic_expr) -> Dyn.t),
     (tactic_out : Dyn.t -> (interp_sign -> raw_tactic_expr))) =
  create "old_legacy_tactic"

let ((value_in : value -> Dyn.t),
     (value_out : Dyn.t -> value)) = create "old_legacy_value"

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

(* To embed constr *)
let constrIn t = CDynamic (dummy_loc,constr_in t)
let constrOut = function
  | CDynamic (_,d) ->
    if (Dyn.tag d) = "constr" then
      constr_out d
    else
      anomalylabstrm "constrOut" (str "Dynamic tag should be constr")
  | ast ->
    anomalylabstrm "constrOut" (str "Not a Dynamic ast")

let dloc = dummy_loc

(* Globalizes the identifier *)
let find_reference env qid =
  (* We first look for a variable of the current proof *)
  match repr_qualid qid with
    | (d,id) when repr_dirpath d = [] & List.mem id (ids_of_context env)
	-> VarRef id
    | _ -> Nametab.locate qid

let error_not_evaluable s =
  errorlabstrm "evalref_of_ref" 
    (str "Cannot coerce" ++ spc ()  ++ s ++ spc () ++
     str "to an evaluable reference")

(* Table of "pervasives" macros tactics (e.g. auto, simpl, etc.) *)
let atomic_mactab = ref Idmap.empty
let add_primitive_tactic s tac =
  let id = id_of_string s in
  atomic_mactab := Idmap.add id tac !atomic_mactab

let _ =
  let nocl = {onhyps=Some[];onconcl=true; concl_occs=[]} in
  List.iter
      (fun (s,t) -> add_primitive_tactic s (TacAtom(dloc,t)))
      [ "red", TacReduce(Red false,nocl);
        "hnf", TacReduce(Hnf,nocl);
        "simpl", TacReduce(Simpl None,nocl);
        "compute", TacReduce(Cbv all_flags,nocl);
        "intro", TacIntroMove(None,None);
        "intros", TacIntroPattern [];
        "assumption", TacAssumption;
        "cofix", TacCofix None;
        "trivial", TacTrivial ([],None);
        "auto", TacAuto(None,[],None);
        "left", TacLeft NoBindings;
        "right", TacRight NoBindings;
        "split", TacSplit(false,NoBindings);
        "constructor", TacAnyConstructor None;
        "reflexivity", TacReflexivity;
        "symmetry", TacSymmetry nocl
      ];
  List.iter
      (fun (s,t) -> add_primitive_tactic s t)
      [ "idtac",TacId [];
        "fail", TacFail(ArgArg 0,[]);
        "fresh", TacArg(TacFreshId [])
      ]
 
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

(* Tactics table (TacExtend). *)

let tac_tab = Hashtbl.create 17

let add_tactic s t =
  if Hashtbl.mem tac_tab s then
    errorlabstrm ("Refiner.add_tactic: ") 
      (str ("Cannot redeclare tactic "^s));
  Hashtbl.add tac_tab s t

let overwriting_add_tactic s t =
  if Hashtbl.mem tac_tab s then begin
    Hashtbl.remove tac_tab s;
    warning ("Overwriting definition of tactic "^s)
  end;
  Hashtbl.add tac_tab s t

let lookup_tactic s =
  try 
    Hashtbl.find tac_tab s
  with Not_found -> 
    errorlabstrm "Refiner.lookup_tactic"
      (str"The tactic " ++ str s ++ str" is not installed")
(*
let vernac_tactic (s,args) =
  let tacfun = lookup_tactic s args in
  abstract_extended_tactic s args tacfun
*)
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
    typed_generic_argument) *
  (substitution -> glob_generic_argument -> glob_generic_argument)

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

(* Dynamically check that an argument is a tactic, possibly unboxing VRec *)
let coerce_to_tactic loc id = function
  | VRec v -> !v
  | VTactic _ | VFun _ | VRTactic _ as a -> a
  | _ -> user_err_loc 
  (loc, "", str "variable " ++  pr_id id ++ str " should be bound to a tactic")

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
    with e when Proofview.catchable_exception e -> 
      (Evd.empty, Global.env())

let strict_check = ref false

let adjust_loc loc = if !strict_check then dloc else loc

(* Globalize a name which must be bound -- actually just check it is bound *)
let intern_hyp ist (loc,id as locid) =
  if not !strict_check then
    locid
  else if find_ident id ist then
    (dloc,id)
  else
    Pretype_errors.error_var_not_found_loc loc id

let intern_hyp_or_metaid ist id = intern_hyp ist (skip_metaid id)

let intern_or_var ist = function
  | ArgVar locid -> ArgVar (intern_hyp ist locid)
  | ArgArg _ as x -> x

let loc_of_by_notation f = function
  | AN c -> f c
  | ByNotation (loc,s) -> loc

let destIndRef = function IndRef ind -> ind | _ -> failwith "destIndRef"

let intern_inductive_or_by_notation = function
  | AN r -> Nametab.inductive_of_reference r
  | ByNotation (loc,ntn) ->
      destIndRef (Notation.interp_notation_as_global_reference loc
        (function IndRef ind -> true | _ -> false) ntn)

let intern_inductive ist = function
  | AN (Ident (loc,id)) when find_var id ist -> ArgVar (loc,id)
  | r -> ArgArg (intern_inductive_or_by_notation r)

let intern_global_reference ist = function
  | Ident (loc,id) when find_var id ist -> ArgVar (loc,id)
  | r -> 
      let loc,qid as lqid = qualid_of_reference r in
      try ArgArg (loc,locate_global_with_alias lqid)
      with Not_found -> 
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
      RVar (dloc,id), None
  | r ->
      let loc,_ as lqid = qualid_of_reference r in
      RRef (loc,locate_global_with_alias lqid), if strict then None else Some (CRef r)

let intern_reference strict ist r =
  (try Reference (intern_tac_ref ist r)
   with Not_found ->
     (try ConstrMayEval (ConstrTerm (intern_constr_reference strict ist r))
      with Not_found ->
        (match r with
          | Ident (loc,id) when is_atomic id -> Tacexp (lookup_atomic id)
          | Ident (loc,id) when not strict -> IntroPattern (IntroIdentifier id)
          | _ ->
              let (loc,qid) = qualid_of_reference r in
              error_global_not_found_loc loc qid)))

let intern_message_token ist = function
  | (MsgString _ | MsgInt _ as x) -> x
  | MsgIdent id -> MsgIdent (intern_hyp_or_metaid ist id)

let intern_message ist = List.map (intern_message_token ist)

let rec intern_intro_pattern lf ist = function
  | IntroOrAndPattern l ->
      IntroOrAndPattern (intern_case_intro_pattern lf ist l)
  | IntroIdentifier id ->
      IntroIdentifier (intern_ident lf ist id)
  | IntroWildcard | IntroAnonymous | IntroFresh _ as x -> x

and intern_case_intro_pattern lf ist =
  List.map (List.map (intern_intro_pattern lf ist))

let intern_quantified_hypothesis ist = function
  | AnonHyp n -> AnonHyp n
  | NamedHyp id ->
      (* Uncomment to disallow "intros until n" in ltac when n is not bound *)
      NamedHyp ((*snd (intern_hyp ist (dloc,*)id(* ))*))
      
let intern_binding_name ist x =
  (* We use identifier both for variables and binding names *)
  (* Todo: consider the body of the lemma to which the binding refer 
     and if a term w/o ltac vars, check the name is indeed quantified *)
  x

let intern_constr_gen isarity {ltacvars=lfun; gsigma=sigma; genv=env} c =
  let warn = if !strict_check then fun x -> x else Constrintern.for_grammar in
  let c' = 
    warn (Constrintern.intern_gen isarity ~ltacvars:(fst lfun,[]) sigma env) c
  in
  (c',if !strict_check then None else Some c)

let intern_constr = intern_constr_gen false
let intern_type = intern_constr_gen true

(* Globalize bindings *)
let intern_binding ist (loc,b,c) =
  (loc,intern_binding_name ist b,intern_constr ist c)

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
  | ElimOnConstr c -> ElimOnConstr (intern_constr_with_bindings ist c)
  | ElimOnAnonHyp n as x -> x
  | ElimOnIdent (loc,id) ->
      if !strict_check then
	(* If in a defined tactic, no intros-until *)
	ElimOnConstr (intern_constr ist (CRef (Ident (dloc,id))),NoBindings)
      else
	ElimOnIdent (loc,id)

let evaluable_of_global_reference = function
  | ConstRef c -> EvalConstRef c
  | VarRef c -> EvalVarRef c
  | r -> error_not_evaluable (pr_global r)

let short_name = function
  | AN (Ident (loc,id)) when not !strict_check -> Some (loc,id)
  | _ -> None

let interp_global_reference r =
  let loc,qid as lqid = qualid_of_reference r in
  try locate_global_with_alias lqid
  with Not_found ->
  match r with 
  | Ident (loc,id) when not !strict_check -> VarRef id
  | _ -> error_global_not_found_loc loc qid

let intern_evaluable_reference_or_by_notation = function
  | AN r -> evaluable_of_global_reference (interp_global_reference r)
  | ByNotation (loc,ntn) ->
      evaluable_of_global_reference
      (Notation.interp_notation_as_global_reference loc
        (function ConstRef _ | VarRef _ -> true | _ -> false) ntn)

(* Globalizes a reduction expression *)
let intern_evaluable ist = function
  | AN (Ident (loc,id)) when find_ltacvar id ist -> ArgVar (loc,id)
  | AN (Ident (_,id)) when
      (not !strict_check & find_hyp id ist) or find_ctxvar id ist ->
      ArgArg (EvalVarRef id, None)
  | r ->
      let e = intern_evaluable_reference_or_by_notation r in
      let na = short_name r in
      ArgArg (e,na)

let intern_unfold ist (l,qid) = (l,intern_evaluable ist qid)

let intern_flag ist red =
  { red with rConst = List.map (intern_evaluable ist) red.rConst }

let intern_constr_occurrence ist (l,c) = (l,intern_constr ist c)

let intern_red_expr ist = function
  | Unfold l -> Unfold (List.map (intern_unfold ist) l)
  | Fold l -> Fold (List.map (intern_constr ist) l)
  | Cbv f -> Cbv (intern_flag ist f)
  | Lazy f -> Lazy (intern_flag ist f)
  | Pattern l -> Pattern (List.map (intern_constr_occurrence ist) l)
  | Simpl o -> Simpl (Option.map (intern_constr_occurrence ist) o)
  | (Red _ | Hnf | ExtraRedExpr _ | CbvVm as r ) -> r
  

let intern_inversion_strength lf ist = function
  | NonDepInversion (k,idl,ids) ->
      NonDepInversion (k,List.map (intern_hyp_or_metaid ist) idl,
      intern_intro_pattern lf ist ids)
  | DepInversion (k,copt,ids) ->
      DepInversion (k, Option.map (intern_constr ist) copt,
      intern_intro_pattern lf ist ids)
  | InversionUsing (c,idl) ->
      InversionUsing (intern_constr ist c, List.map (intern_hyp_or_metaid ist) idl)

(* Interprets an hypothesis name *)
let intern_hyp_location ist ((occs,id),hl) =
  ((List.map (intern_or_var ist) occs,intern_hyp ist (skip_metaid id)), hl)

let interp_constrpattern_gen sigma env ltacvar c =
  let c = intern_gen false ~allow_patvar:true ~ltacvars:(ltacvar,[])
                     sigma env c in
  pattern_of_rawconstr c

(* Reads a pattern *)
let intern_pattern sigma env lfun = function
  | Subterm (ido,pc) ->
      let (metas,pat) = interp_constrpattern_gen sigma env lfun pc in
      ido, metas, Subterm (ido,pat)
  | Term pc ->
      let (metas,pat) = interp_constrpattern_gen sigma env lfun pc  in
      None, metas, Term pat

let intern_constr_may_eval ist = function
  | ConstrEval (r,c) -> ConstrEval (intern_red_expr ist r,intern_constr ist c)
  | ConstrContext (locid,c) ->
      ConstrContext (intern_hyp ist locid,intern_constr ist c)
  | ConstrTypeOf c -> ConstrTypeOf (intern_constr ist c)
  | ConstrTerm c -> ConstrTerm (intern_constr ist c)

(* External tactics *)
let print_xml_term = ref (fun _ -> failwith "print_xml_term unset")
let declare_xml_printer f = print_xml_term := f

let internalise_tacarg ch = G_xml.parse_tactic_arg ch

let extern_tacarg ch env sigma = function
  | VConstr c -> !print_xml_term ch env sigma c
  | VTactic _ | VRTactic _ | VFun _ | VVoid | VInteger _ | VConstr_context _
  | VIntroPattern _  | VRec _ | VList _ ->
      error "Only externing of terms is implemented"

let extern_request ch req gl la =
  output_string ch "<REQUEST req=\""; output_string ch req;
  output_string ch "\">\n";
  List.iter (pf_apply (extern_tacarg ch) gl) la;
  output_string ch "</REQUEST>\n"

(* Reads the hypotheses of a Match Context rule *)
let rec intern_match_context_hyps sigma env lfun = function
  | (Hyp ((_,na) as locna,mp))::tl ->
      let ido, metas1, pat = intern_pattern sigma env lfun mp in
      let lfun, metas2, hyps = intern_match_context_hyps sigma env lfun tl in
      let lfun' = name_cons na (Option.List.cons ido lfun) in
      lfun', metas1@metas2, Hyp (locna,pat)::hyps
  | [] -> lfun, [], []

(* Utilities *)
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
      TacIntroMove (Option.map (intern_ident lf ist) ido,
          Option.map (intern_hyp ist) ido')
  | TacAssumption -> TacAssumption
  | TacExact c -> TacExact (intern_constr ist c)
  | TacExactNoCheck c -> TacExactNoCheck (intern_constr ist c)
  | TacVmCastNoCheck c -> TacVmCastNoCheck (intern_constr ist c)
  | TacApply (ev,cb) -> TacApply (ev,intern_constr_with_bindings ist cb)
  | TacElim (ev,cb,cbo) ->
      TacElim (ev,intern_constr_with_bindings ist cb,
               Option.map (intern_constr_with_bindings ist) cbo)
  | TacElimType c -> TacElimType (intern_type ist c)
  | TacCase (ev,cb) -> TacCase (ev,intern_constr_with_bindings ist cb)
  | TacCaseType c -> TacCaseType (intern_type ist c)
  | TacFix (idopt,n) -> TacFix (Option.map (intern_ident lf ist) idopt,n)
  | TacMutualFix (id,n,l) ->
      let f (id,n,c) = (intern_ident lf ist id,n,intern_type ist c) in
      TacMutualFix (intern_ident lf ist id, n, List.map f l)
  | TacCofix idopt -> TacCofix (Option.map (intern_ident lf ist) idopt)
  | TacMutualCofix (id,l) ->
      let f (id,c) = (intern_ident lf ist id,intern_type ist c) in
      TacMutualCofix (intern_ident lf ist id, List.map f l)
  | TacCut c -> TacCut (intern_type ist c)
  | TacAssert (otac,ipat,c) ->
      TacAssert (Option.map (intern_tactic ist) otac,
                 intern_intro_pattern lf ist ipat,
                 intern_constr_gen (otac<>None) ist c)
  | TacGeneralize cl -> TacGeneralize (List.map (intern_constr ist) cl)
  | TacGeneralizeDep c -> TacGeneralizeDep (intern_constr ist c)
  | TacLetTac (na,c,cls) ->
      let na = intern_name lf ist na in
      TacLetTac (na,intern_constr ist c,
                 (clause_app (intern_hyp_location ist) cls))

  (* Automation tactics *)
  | TacTrivial (lems,l) -> TacTrivial (List.map (intern_constr ist) lems,l)
  | TacAuto (n,lems,l) ->
      TacAuto (Option.map (intern_or_var ist) n,
        List.map (intern_constr ist) lems,l)
  | TacAutoTDB n -> TacAutoTDB n
  | TacDestructHyp (b,id) -> TacDestructHyp(b,intern_hyp ist id)
  | TacDestructConcl -> TacDestructConcl
  | TacSuperAuto (n,l,b1,b2) -> TacSuperAuto (n,l,b1,b2)
  | TacDAuto (n,p,lems) ->
      TacDAuto (Option.map (intern_or_var ist) n,p,
        List.map (intern_constr ist) lems)

  (* Derived basic tactics *)
  | TacSimpleInduction h ->
      TacSimpleInduction (intern_quantified_hypothesis ist h)
  | TacNewInduction (ev,lc,cbo,ids) ->
      TacNewInduction (ev,List.map (intern_induction_arg ist) lc,
               Option.map (intern_constr_with_bindings ist) cbo,
               (intern_intro_pattern lf ist ids))
  | TacSimpleDestruct h ->
      TacSimpleDestruct (intern_quantified_hypothesis ist h)
  | TacNewDestruct (ev,c,cbo,ids) ->
      TacNewDestruct (ev,List.map (intern_induction_arg ist) c,
               Option.map (intern_constr_with_bindings ist) cbo,
	       (intern_intro_pattern lf ist ids))
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
  | TacClear (b,l) -> TacClear (b,List.map (intern_hyp_or_metaid ist) l)
  | TacClearBody l -> TacClearBody (List.map (intern_hyp_or_metaid ist) l)
  | TacMove (dep,id1,id2) ->
    TacMove (dep,intern_hyp_or_metaid ist id1,intern_hyp_or_metaid ist id2)
  | TacRename l -> 
      TacRename (List.map (fun (id1,id2) -> 
			     intern_hyp_or_metaid ist id1, 
			     intern_hyp_or_metaid ist id2) l)
	
  (* Constructors *)
  | TacLeft bl -> TacLeft (intern_bindings ist bl)
  | TacRight bl -> TacRight (intern_bindings ist bl)
  | TacSplit (b,bl) -> TacSplit (b,intern_bindings ist bl)
  | TacAnyConstructor t -> TacAnyConstructor (Option.map (intern_tactic ist) t)
  | TacConstructor (n,bl) -> TacConstructor (n, intern_bindings ist bl)

  (* Conversion *)
  | TacReduce (r,cl) ->
      TacReduce (intern_red_expr ist r, clause_app (intern_hyp_location ist) cl)
  | TacChange (occl,c,cl) ->
      TacChange (Option.map (intern_constr_occurrence ist) occl,
        (if occl = None then intern_type ist c else intern_constr ist c),
	clause_app (intern_hyp_location ist) cl)

  (* Equivalence relations *)
  | TacReflexivity -> TacReflexivity
  | TacSymmetry idopt -> 
      TacSymmetry (clause_app (intern_hyp_location ist) idopt)
  | TacTransitivity c -> TacTransitivity (intern_constr ist c)

  (* Equality and inversion *)
  | TacRewrite (ev,l,cl) -> 
      TacRewrite 
	(ev, 
	 List.map (fun (b,c) -> (b,intern_constr_with_bindings ist c)) l,
	 clause_app (intern_hyp_location ist) cl)
  | TacInversion (inv,hyp) ->
      TacInversion (intern_inversion_strength lf ist inv,
        intern_quantified_hypothesis ist hyp)

  (* For extensions *)
  | TacExtend (loc,opn,l) ->
      let _ = lookup_tactic opn in
      TacExtend (adjust_loc loc,opn,List.map (intern_genarg ist) l)
  | TacAlias (loc,s,l,(dir,body)) ->
      let l = List.map (fun (id,a) -> (id,intern_genarg ist a)) l in
      try TacAlias (loc,s,l,(dir,body))
      with e -> raise (locate_error_in_file (string_of_dirpath dir) e)

and intern_tactic ist tac = (snd (intern_tactic_seq ist tac) : glob_tactic_expr)

and intern_tactic_seq ist = function
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
          (n,Option.map (intern_tactic ist) c, intern_tacarg !strict_check ist b)) l in
      let (l1,l2) = ist.ltacvars in
      let ist' = { ist with ltacvars = ((extract_let_names l)@l1,l2) } in
      ist.ltacvars, TacLetIn (l,intern_tactic ist' u)
  | TacMatchContext (lz,lr,lmr) ->
      ist.ltacvars, TacMatchContext(lz,lr, intern_match_rule ist lmr)
  | TacMatch (lz,c,lmr) ->
      ist.ltacvars, TacMatch (lz,intern_tactic ist c,intern_match_rule ist lmr)
  | TacId l -> ist.ltacvars, TacId (intern_message ist l)
  | TacFail (n,l) -> 
      ist.ltacvars, TacFail (intern_or_var ist n,intern_message ist l)
  | TacProgress tac -> ist.ltacvars, TacProgress (intern_tactic ist tac)
  | TacAbstract (tac,s) -> ist.ltacvars, TacAbstract (intern_tactic ist tac,s)
  | TacThen (t1,[||],t2,[||]) ->
      let lfun', t1 = intern_tactic_seq ist t1 in
      let lfun'', t2 = intern_tactic_seq { ist with ltacvars = lfun' } t2 in
      lfun'', TacThen (t1,[||],t2,[||])
  | TacThen (t1,tf,t2,tl) ->
      let lfun', t1 = intern_tactic_seq ist t1 in
      let ist' = { ist with ltacvars = lfun' } in
      (* Que faire en cas de (tac complexe avec Match et Thens; tac2) ?? *)
      lfun', TacThen (t1,Array.map (intern_tactic ist') tf,intern_tactic ist' t2,
		       Array.map (intern_tactic ist') tl)
  | TacThens (t,tl) ->
      let lfun', t = intern_tactic_seq ist t in
      let ist' = { ist with ltacvars = lfun' } in
      (* Que faire en cas de (tac complexe avec Match et Thens; tac2) ?? *)
      lfun', TacThens (t, List.map (intern_tactic ist') tl)
  | TacDo (n,tac) -> 
      ist.ltacvars, TacDo (intern_or_var ist n,intern_tactic ist tac)
  | TacTry tac -> ist.ltacvars, TacTry (intern_tactic ist tac)
  | TacInfo tac -> ist.ltacvars, TacInfo (intern_tactic ist tac)
  | TacRepeat tac -> ist.ltacvars, TacRepeat (intern_tactic ist tac)
  | TacOrelse (tac1,tac2) ->
      ist.ltacvars, TacOrelse (intern_tactic ist tac1,intern_tactic ist tac2)
  | TacFirst l -> ist.ltacvars, TacFirst (List.map (intern_tactic ist) l)
  | TacSolve l -> ist.ltacvars, TacSolve (List.map (intern_tactic ist) l)
  | TacComplete tac -> ist.ltacvars, TacComplete (intern_tactic ist tac)
  | TacArg a -> ist.ltacvars, TacArg (intern_tacarg true ist a)

and intern_tactic_fun ist (var,body) = 
  let (l1,l2) = ist.ltacvars in
  let lfun' = List.rev_append (Option.List.flatten var) l1 in
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
      if find_ltacvar id ist then Reference (ArgVar (adjust_loc loc,id))
      else error_syntactic_metavariables_not_allowed loc
  | TacCall (loc,f,l) ->
      TacCall (loc,
        intern_tactic_reference ist f,
        List.map (intern_tacarg !strict_check ist) l)
  | TacExternal (loc,com,req,la) -> 
      TacExternal (loc,com,req,List.map (intern_tacarg !strict_check ist) la)
  | TacFreshId x -> TacFreshId (List.map (intern_or_var ist) x)
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
      let ist' = { ist with ltacvars = (metas@(Option.List.cons ido lfun'),l2) } in
      Pat (hyps,pat,intern_tactic ist' tc) :: (intern_match_rule ist tl)
  | [] -> []

and intern_genarg ist x =
  match genarg_tag x with
  | BoolArgType -> in_gen globwit_bool (out_gen rawwit_bool x)
  | IntArgType -> in_gen globwit_int (out_gen rawwit_int x)
  | IntOrVarArgType ->
      in_gen globwit_int_or_var
        (intern_or_var ist (out_gen rawwit_int_or_var x))
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
  | VarArgType ->
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
      in_gen globwit_red_expr (intern_red_expr ist (out_gen rawwit_red_expr x))
  | OpenConstrArgType b ->
      in_gen (globwit_open_constr_gen b)
        ((),intern_constr ist (snd (out_gen (rawwit_open_constr_gen b) x)))
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
  | ExtraArgType s ->
      match tactic_genarg_level s with
      | Some n -> 
          (* Special treatment of tactic arguments *)
          in_gen (globwit_tactic n) (intern_tactic ist
	    (out_gen (rawwit_tactic n) x))
      | None ->
          lookup_genarg_glob s ist x

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

(* Reads a pattern by substituting vars of lfun *)
let eval_pattern lfun c = 
  let lvar = List.map (fun (id,c) -> (id,lazy(pattern_of_constr c))) lfun in
  instantiate_pattern lvar c

let read_pattern lfun = function
  | Subterm (ido,pc) -> Subterm (ido,eval_pattern lfun pc)
  | Term pc -> Term (eval_pattern lfun pc)

(* Reads the hypotheses of a Match Context rule *)
let cons_and_check_name id l =
  if List.mem id l then
    user_err_loc (dloc,"read_match_context_hyps",
      str ("Hypothesis pattern-matching variable "^(string_of_id id)^
      " used twice in the same pattern"))
  else id::l

let rec read_match_context_hyps lfun lidh = function
  | (Hyp ((loc,na) as locna,mp))::tl ->
      let lidh' = name_fold cons_and_check_name na lidh in
      Hyp (locna,read_pattern lfun mp)::
	(read_match_context_hyps lfun lidh' tl)
  | [] -> []

(* Reads the rules of a Match Context or a Match *)
let rec read_match_rule lfun = function
  | (All tc)::tl -> (All tc)::(read_match_rule lfun tl)
  | (Pat (rl,mp,tc))::tl ->
      Pat (read_match_context_hyps lfun [] rl, read_pattern lfun mp,tc)
      :: read_match_rule lfun tl
  | [] -> []

(* For Match Context and Match *)
exception Not_coherent_metas
exception Eval_fail of std_ppcmds

let is_match_catchable = function
  | PatternMatchingFailure | Eval_fail _ -> true
  | e -> Proofview.catchable_exception e

(* Verifies if the matched list is coherent with respect to lcm *)
let rec verify_metas_coherence gl lcm = function
  | (num,csr)::tl ->
    if (List.for_all (fun (a,b) -> a<>num or pf_conv_x gl b csr) lcm) then
      (num,csr)::(verify_metas_coherence gl lcm tl)
    else
      raise Not_coherent_metas
  | [] -> []

(* Tries to match one hypothesis pattern with a list of hypotheses *)
let apply_one_mhyp_context ist env gl lmatch (hypname,pat) (lhyps,nocc) =
  let get_id_couple id = function
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
          let (lm,ctxt) = match_subterm nocc t hyp in
          let lmeta = verify_metas_coherence gl lmatch lm in
          ((get_id_couple id hypname)@(give_context ctxt ic),
	   lmeta,(id,hyp),(hyps,nocc + 1))
         with
         | PatternMatchingFailure ->
             apply_one_mhyp_context_rec 0 tl
         | Not_coherent_metas ->
             apply_one_mhyp_context_rec (nocc + 1) hyps))
    | [] ->
        db_hyp_pattern_failure ist.debug env (hypname,pat);
        raise PatternMatchingFailure
      in
  apply_one_mhyp_context_rec nocc lhyps

let constr_to_id loc = function
  | VConstr c when isVar c -> destVar c
  | _ -> invalid_arg_loc (loc, "Not an identifier")

let constr_to_qid loc c =
  try shortest_qualid_of_global Idset.empty (global_of_constr c)
  with _ -> invalid_arg_loc (loc, "Not a global reference")

let is_variable env id =
  List.mem id (ids_of_named_context (Environ.named_context env))

(* Debug reference *)
let debug = ref DebugOff

(* Sets the debugger mode *)
let set_debug pos = debug := pos

(* Gives the state of debug *)
let get_debug () = !debug

let debugging_step ist pp =
  match ist.debug with
  | DebugOn lev ->
      safe_msgnl (str "Level " ++ int lev ++ str": " ++ pp () ++ fnl())
  | _ -> ()

let debugging_exception_step ist signal_anomaly e pp =
  let explain_exc =
    if signal_anomaly then explain_logic_error
    else explain_logic_error_no_anomaly in
  debugging_step ist (fun () -> 
    pp() ++ spc() ++ str "raised the exception" ++ fnl() ++ !explain_exc e)

let error_ltac_variable loc id env v s =
   user_err_loc (loc, "", str "Ltac variable " ++ pr_id id ++ 
   str " is bound to" ++ spc () ++ pr_value env v ++ spc () ++ 
   str "which cannot be coerced to " ++ str s)

exception CannotCoerceTo of string

(* Raise Not_found if not in interpretation sign *)
let try_interp_ltac_var coerce ist env (loc,id) =
  let v = List.assoc id ist.lfun in
  try coerce v with CannotCoerceTo s -> error_ltac_variable loc id env v s

let interp_ltac_var coerce ist env locid =
  try try_interp_ltac_var coerce ist env locid
  with Not_found -> anomaly "Detected as ltac var at interning time"

(* Interprets an identifier which must be fresh *)
let coerce_to_ident fresh env = function
  | VIntroPattern (IntroIdentifier id) -> id
  | VConstr c when isVar c & not (fresh & is_variable env (destVar c)) ->
      (* We need it fresh for intro e.g. in "Tac H = clear H; intro H" *)
      destVar c
  | v -> raise (CannotCoerceTo "a fresh identifier")

let interp_ident_gen fresh ist gl id =
  let env = pf_env gl in
  try try_interp_ltac_var (coerce_to_ident fresh env) ist (Some env) (dloc,id)
  with Not_found -> id

let interp_ident = interp_ident_gen false 
let interp_fresh_ident = interp_ident_gen true

(* Interprets an optional identifier which must be fresh *)
let interp_fresh_name ist gl = function
  | Anonymous -> Anonymous
  | Name id -> Name (interp_fresh_ident ist gl id)

let coerce_to_intro_pattern env = function
  | VIntroPattern ipat -> ipat
  | VConstr c when isVar c ->
      (* This happens e.g. in definitions like "Tac H = clear H; intro H" *)
      (* but also in "destruct H as (H,H')" *)
      IntroIdentifier (destVar c)
  | v -> raise (CannotCoerceTo "an introduction pattern")

let interp_intro_pattern_var ist env id =
  try try_interp_ltac_var (coerce_to_intro_pattern env) ist (Some env)(dloc,id)
  with Not_found -> IntroIdentifier id

let coerce_to_hint_base = function
  | VIntroPattern (IntroIdentifier id) -> string_of_id id
  | _ -> raise (CannotCoerceTo "a hint base name")

let interp_hint_base ist s =
  try try_interp_ltac_var coerce_to_hint_base ist None (dloc,id_of_string s)
  with Not_found -> s

let coerce_to_int = function
  | VInteger n -> n
  | v -> raise (CannotCoerceTo "an integer")

let interp_int ist locid =
  try try_interp_ltac_var coerce_to_int ist None locid
  with Not_found -> user_err_loc(fst locid,"interp_int",str "Unbound variable")

let interp_int_or_var ist = function
  | ArgVar locid -> interp_int ist locid
  | ArgArg n -> n

let int_or_var_list_of_VList = function
  | VList l -> List.map (fun n -> ArgArg (coerce_to_int n)) l
  | _ -> raise Not_found

let interp_int_or_var_as_list ist = function
  | ArgVar (_,id as locid) -> 
      (try int_or_var_list_of_VList (List.assoc id ist.lfun)
       with Not_found | CannotCoerceTo _ -> [ArgArg (interp_int ist locid)])
  | ArgArg n as x -> [x]

let interp_int_or_var_list ist l =
  List.flatten (List.map (interp_int_or_var_as_list ist) l)

let constr_of_value env = function
  | VConstr csr -> csr
  | VIntroPattern (IntroIdentifier id) -> constr_of_id env id
  | _ -> raise Not_found

let coerce_to_hyp env = function
  | VConstr c when isVar c -> destVar c
  | VIntroPattern (IntroIdentifier id) when is_variable env id -> id
  | _ -> raise (CannotCoerceTo "a variable")

(* Interprets a bound variable (especially an existing hypothesis) *)
let interp_hyp ist gl (loc,id as locid) =
  let env = pf_env gl in
  (* Look first in lfun for a value coercible to a variable *)
  try try_interp_ltac_var (coerce_to_hyp env) ist (Some env) locid
  with Not_found -> 
  (* Then look if bound in the proof context at calling time *)
  if is_variable env id then id
  else user_err_loc (loc,"eval_variable",pr_id id ++ str " not found")

let hyp_list_of_VList env = function
  | VList l -> List.map (coerce_to_hyp env) l
  | _ -> raise Not_found

let interp_hyp_list_as_list ist gl (loc,id as x) =
  try hyp_list_of_VList (pf_env gl) (List.assoc id ist.lfun)
  with Not_found | CannotCoerceTo _ -> [interp_hyp ist gl x]

let interp_hyp_list ist gl l =
  List.flatten (List.map (interp_hyp_list_as_list ist gl) l)

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
let coerce_to_reference env v =
  try match v with
  | VConstr c -> global_of_constr c (* may raise Not_found *)
  | _ -> raise Not_found
  with Not_found -> raise (CannotCoerceTo "a reference")

let interp_reference ist env = function
  | ArgArg (_,r) -> r
  | ArgVar locid -> 
      interp_ltac_var (coerce_to_reference env) ist (Some env) locid

let pf_interp_reference ist gl = interp_reference ist (pf_env gl)

let coerce_to_inductive = function
  | VConstr c when isInd c -> destInd c
  | _ -> raise (CannotCoerceTo "an inductive type")

let interp_inductive ist = function
  | ArgArg r -> r
  | ArgVar locid -> interp_ltac_var coerce_to_inductive ist None locid

let coerce_to_evaluable_ref env v =
  let ev = match v with
    | VConstr c when isConst c -> EvalConstRef (destConst c)
    | VConstr c when isVar c -> EvalVarRef (destVar c)
    | VIntroPattern (IntroIdentifier id) when List.mem id (ids_of_context env) 
	-> EvalVarRef id
    | _ -> raise (CannotCoerceTo "an evaluable reference")
  in
  if not (Tacred.is_evaluable env ev) then
    raise (CannotCoerceTo "an evaluable reference")
  else
    ev

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
  | ArgVar locid -> 
      interp_ltac_var (coerce_to_evaluable_ref env) ist (Some env) locid

(* Interprets an hypothesis name *)
let interp_hyp_location ist gl ((occs,id),hl) =
  ((interp_int_or_var_list ist occs,interp_hyp ist gl id),hl)

let interp_clause ist gl { onhyps=ol; onconcl=b; concl_occs=occs } =
  { onhyps=Option.map(List.map (interp_hyp_location ist gl)) ol;
    onconcl=b;
    concl_occs= interp_int_or_var_list ist occs }

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

(* Extract the identifier list from lfun: join all branches (what to do else?)*)
let rec intropattern_ids = function
  | IntroIdentifier id -> [id]
  | IntroOrAndPattern ll -> 
      List.flatten (List.map intropattern_ids (List.flatten ll))
  | IntroWildcard | IntroAnonymous | IntroFresh _ -> []

let rec extract_ids ids = function
  | (id,VIntroPattern ipat)::tl when not (List.mem id ids) ->
      intropattern_ids ipat @ extract_ids ids tl
  | _::tl -> extract_ids ids tl
  | [] -> []

let default_fresh_id = id_of_string "H"

let interp_fresh_id ist gl l =
  let ids = map_succeed (function ArgVar(_,id) -> id | _ -> failwith "") l in
  let avoid = (extract_ids ids ist.lfun) @ ist.avoid_ids in
  let id = 
    if l = [] then default_fresh_id 
    else
      let s =
	String.concat "" (List.map (function
	  | ArgArg s -> s
	  | ArgVar (_,id) -> string_of_id (interp_ident ist gl id)) l) in
      let s = if Lexer.is_keyword s then s^"0" else s in
      id_of_string s in
  Tactics.fresh_id avoid id gl

(* To retype a list of key*constr with undefined key *)
let retype_list sigma env lst =
  List.fold_right (fun (x,csr) a ->
    try (x,Retyping.get_judgment_of env sigma csr)::a with
    | Anomaly _ -> a) lst []

let implicit_tactic = ref None

let declare_implicit_tactic tac = implicit_tactic := Some tac

open Evd

let solvable_by_tactic env evi (ev,args) src = 
  match (!implicit_tactic, src) with
  | Some tac, (ImplicitArg _ | QuestionMark _)
      when 
	Environ.named_context_of_val evi.evar_hyps = 
	Environ.named_context env ->
      let id = id_of_string "H" in
      start_proof id (Local,Proof Lemma) evi.evar_hyps evi.evar_concl
	(fun _ _ -> ());
      begin
	try
	  by (tclCOMPLETE tac);
	  let _,(const,_,_) = cook_proof () in 
	  delete_current_proof (); const.const_entry_body
	with e when Proofview.catchable_exception e -> 
	  delete_current_proof();
	  raise Exit
      end
  | _ -> raise Exit

let solve_remaining_evars env initial_sigma evd c =
  let evdref = ref evd in
  let rec proc_rec c =
    match kind_of_term (Reductionops.whd_evar (evars_of !evdref) c) with
      | Evar (ev,args as k) when not (Evd.mem initial_sigma ev) ->
            let (loc,src) = evar_source ev !evdref in
	    let sigma = evars_of !evdref in
	    (try 
	      let evi = Evd.find sigma ev in
	      let c = solvable_by_tactic env evi k src in
	      evdref := Evd.evar_define ev c !evdref;
	      c
	    with Exit ->
	      Pretype_errors.error_unsolvable_implicit loc env sigma src)
      | _ -> map_constr proc_rec c      
  in
  proc_rec c

let interp_gen kind ist sigma env (c,ce) =
  let (ltacvars,unbndltacvars) = constr_list ist env in
  let typs = retype_list sigma env ltacvars in
  let c = match ce with
  | None -> c
    (* If at toplevel (ce<>None), the error can be due to an incorrect
       context at globalization time: we retype with the now known
       intros/lettac/inversion hypothesis names *)
  | Some c ->
      let ltacdata = (List.map fst ltacvars,unbndltacvars) in
      intern_gen (kind = IsType) ~ltacvars:ltacdata sigma env c in
  understand_ltac sigma env (typs,unbndltacvars) kind c

(* Interprets a constr and solve remaining evars with default tactic *)
let interp_econstr kind ist sigma env cc =
  let evars,c = interp_gen kind ist sigma env cc in
  let csr = solve_remaining_evars env sigma evars c in
  db_constr ist.debug env csr;
  csr

(* Interprets an open constr *)
let interp_open_constr ccl ist sigma env cc =
  let evd,c = interp_gen (OfType ccl) ist sigma env cc in
  (evars_of evd,c)

let interp_constr = interp_econstr (OfType None)

let interp_type = interp_econstr IsType

(* Interprets a constr expression casted by the current goal *)
let pf_interp_casted_constr ist gl cc =
  interp_econstr (OfType (Some (pf_concl gl))) ist (project gl) (pf_env gl) cc

(* Interprets an open constr expression *)
let pf_interp_open_constr casted ist gl cc =
  let cl = if casted then Some (pf_concl gl) else None in
  interp_open_constr cl ist (project gl) (pf_env gl) cc

(* Interprets a constr expression *)
let pf_interp_constr ist gl =
  interp_constr ist (project gl) (pf_env gl)

let constr_list_of_VList env = function
  | VList l -> List.map (constr_of_value env) l
  | _ -> raise Not_found
      
let pf_interp_constr_list_as_list ist gl (c,_ as x) =
  match c with
    | RVar (_,id) ->
        (try constr_list_of_VList (pf_env gl) (List.assoc id ist.lfun)
        with Not_found -> [interp_constr ist (project gl) (pf_env gl) x])
    | _ -> [interp_constr ist (project gl) (pf_env gl) x]

let pf_interp_constr_list ist gl l =
  List.flatten (List.map (pf_interp_constr_list_as_list ist gl) l)

let inj_open c = Util.anomaly "Tacinterp.inj_open: deprecated"(* arnaud: (Evd.empty,c)*)

let pf_interp_open_constr_list_as_list ist gl (c,_ as x) =
  match c with
    | RVar (_,id) ->
        (try List.map inj_open 
	       (constr_list_of_VList (pf_env gl) (List.assoc id ist.lfun))
        with Not_found ->
	  [interp_open_constr None ist (project gl) (pf_env gl) x])
    | _ ->
	[interp_open_constr None ist (project gl) (pf_env gl) x]

let pf_interp_open_constr_list ist gl l =
  List.flatten (List.map (pf_interp_open_constr_list_as_list ist gl) l)

(* Interprets a type expression *)
let pf_interp_type ist gl =
  interp_type ist (project gl) (pf_env gl)

(* Interprets a reduction expression *)
let interp_unfold ist env (l,qid) =
  (interp_int_or_var_list ist l,interp_evaluable ist env qid)

let interp_flag ist env red =
  { red with rConst = List.map (interp_evaluable ist env) red.rConst }

let interp_pattern ist sigma env (l,c) = 
  (interp_int_or_var_list ist l, interp_constr ist sigma env c)

let pf_interp_pattern ist gl = interp_pattern ist (project gl) (pf_env gl)

let interp_red_expr ist sigma env = function
  | Unfold l -> Unfold (List.map (interp_unfold ist env) l)
  | Fold l -> Fold (List.map (interp_constr ist sigma env) l)
  | Cbv f -> Cbv (interp_flag ist env f)
  | Lazy f -> Lazy (interp_flag ist env f)
  | Pattern l -> Pattern (List.map (interp_pattern ist sigma env) l)
  | Simpl o -> Simpl (Option.map (interp_pattern ist sigma env) o)
  | (Red _ |  Hnf | ExtraRedExpr _ | CbvVm as r) -> r

let pf_interp_red_expr ist gl = interp_red_expr ist (project gl) (pf_env gl)

let interp_may_eval f ist gl = function
  | ConstrEval (r,c) ->
      let redexp = pf_interp_red_expr ist gl  r in
      pf_reduction_of_red_expr gl redexp (f ist gl c)
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
  | ConstrTerm c -> 
     try 
	f ist gl c
     with e ->
       debugging_exception_step ist false e (fun () ->
         str"interpretation of term " ++ pr_rawconstr_env (pf_env gl) (fst c));
       raise e  

(* Interprets a constr expression possibly to first evaluate *)
let interp_constr_may_eval ist gl c =
  let csr = 
    try
      interp_may_eval pf_interp_constr ist gl c
    with e ->
      debugging_exception_step ist false e (fun () -> str"evaluation of term");
      raise e
  in
  begin
    db_constr ist.debug (pf_env gl) csr;
    csr
  end

let inj_may_eval = function
  | ConstrTerm c -> ConstrTerm (inj_open c)
  | ConstrEval (r,c) -> ConstrEval (Tactics.inj_red_expr r,inj_open c)
  | ConstrContext (id,c) -> ConstrContext (id,inj_open c)
  | ConstrTypeOf c -> ConstrTypeOf (inj_open c)

let message_of_value = function
  | VVoid -> str "()"
  | VInteger n -> int n
  | VIntroPattern ipat -> pr_intro_pattern ipat
  | VConstr_context c | VConstr c -> pr_constr c
  | VRec _ | VTactic _ | VRTactic _ | VFun _ -> str "<tactic>"
  | VList _ -> str "<list>"

let rec interp_message ist = function
  | [] -> mt()
  | MsgString s :: l -> pr_arg str s ++ interp_message ist l
  | MsgInt n :: l -> pr_arg int n ++ interp_message ist l
  | MsgIdent (loc,id) :: l ->
      let v =
	try List.assoc id ist.lfun
	with Not_found -> user_err_loc (loc,"",pr_id id ++ str" not found") in
      pr_arg message_of_value v ++ interp_message ist l

let rec interp_message_nl ist = function
  | [] -> mt()
  | l -> interp_message ist l ++ fnl()

let rec interp_intro_pattern ist gl = function
  | IntroOrAndPattern l -> IntroOrAndPattern (interp_case_intro_pattern ist gl l)
  | IntroIdentifier id -> interp_intro_pattern_var ist (pf_env gl) id
  | IntroWildcard | IntroAnonymous | IntroFresh _ as x -> x

and interp_case_intro_pattern ist gl =
  List.map (List.map (interp_intro_pattern ist gl))

(* Quantified named or numbered hypothesis or hypothesis in context *)
(* (as in Inversion) *)
let coerce_to_quantified_hypothesis = function
  | VInteger n -> AnonHyp n
  | VIntroPattern (IntroIdentifier id) -> NamedHyp id
  | v -> raise (CannotCoerceTo "a quantified hypothesis")

let interp_quantified_hypothesis ist = function
  | AnonHyp n -> AnonHyp n
  | NamedHyp id ->
      try try_interp_ltac_var coerce_to_quantified_hypothesis ist None(dloc,id)
      with Not_found -> NamedHyp id

let interp_binding_name ist = function
  | AnonHyp n -> AnonHyp n
  | NamedHyp id ->
      (* If a name is bound, it has to be a quantified hypothesis *)
      (* user has to use other names for variables if these ones clash with *)
      (* a name intented to be used as a (non-variable) identifier *)
      try try_interp_ltac_var coerce_to_quantified_hypothesis ist None(dloc,id)
      with Not_found -> NamedHyp id

(* Quantified named or numbered hypothesis or hypothesis in context *)
(* (as in Inversion) *)
let coerce_to_decl_or_quant_hyp env = function
  | VInteger n -> AnonHyp n
  | v -> 
      try NamedHyp (coerce_to_hyp env v)
      with CannotCoerceTo _ -> 
	raise (CannotCoerceTo "a declared or quantified hypothesis")

let interp_declared_or_quantified_hypothesis ist gl = function
  | AnonHyp n -> AnonHyp n
  | NamedHyp id ->
      let env = pf_env gl in
      try try_interp_ltac_var 
	    (coerce_to_decl_or_quant_hyp env) ist (Some env) (dloc,id)
      with Not_found -> NamedHyp id

let interp_binding ist gl (loc,b,c) =
  (loc,interp_binding_name ist b,pf_interp_open_constr false ist gl c)

let interp_bindings ist gl = function
| NoBindings -> NoBindings
| ImplicitBindings l -> ImplicitBindings (pf_interp_open_constr_list ist gl l)
| ExplicitBindings l -> ExplicitBindings (List.map (interp_binding ist gl) l)

let interp_constr_with_bindings ist gl (c,bl) =
  (pf_interp_constr ist gl c, interp_bindings ist gl bl)

let interp_open_constr_with_bindings ist gl (c,bl) =
  (pf_interp_open_constr false ist gl c, interp_bindings ist gl bl)

let interp_induction_arg ist gl = function
  | ElimOnConstr c -> ElimOnConstr (interp_constr_with_bindings ist gl c)
  | ElimOnAnonHyp n as x -> x
  | ElimOnIdent (loc,id) ->
      if Tactics.is_quantified_hypothesis id gl then ElimOnIdent (loc,id)
      else ElimOnConstr
	(pf_interp_constr ist gl (RVar (loc,id),Some (CRef (Ident (loc,id)))),
	 NoBindings)

let mk_constr_value ist gl c = VConstr (pf_interp_constr ist gl c)
let mk_hyp_value ist gl c = VConstr (mkVar (interp_hyp ist gl c))
let mk_int_or_var_value ist c = VInteger (interp_int_or_var ist c)

(* Interprets an l-tac expression into a value *)
let rec val_interp ist gl (tac:glob_tactic_expr) =

  let value_interp ist = match tac with
  (* Immediate evaluation *)
  | TacFun (it,body) -> VFun (ist.lfun,it,body)
  | TacLetRecIn (lrc,u) -> letrec_interp ist gl lrc u
  | TacLetIn (l,u) ->
      let addlfun = interp_letin ist gl l in
      val_interp { ist with lfun=addlfun@ist.lfun } gl u
  | TacMatchContext (lz,lr,lmr) -> interp_match_context ist gl lz lr lmr 
  | TacMatch (lz,c,lmr) -> interp_match ist gl lz c lmr
  | TacArg a -> interp_tacarg ist gl a
  (* Delayed evaluation *)
  | t -> VTactic (ist.last_loc,eval_tactic ist t)

  in check_for_interrupt (); 
    match ist.debug with
    | DebugOn lev ->
	debug_prompt lev gl tac (fun v -> value_interp {ist with debug=v})
    | _ -> value_interp ist

and eval_tactic ist = function
  | TacAtom (loc,t) -> fun gl -> catch_error loc (interp_atomic ist gl t) gl
  | TacFun _ | TacLetRecIn _ | TacLetIn _ -> assert false
  | TacMatchContext _ | TacMatch _ -> assert false
  | TacId s -> tclIDTAC_MESSAGE (interp_message_nl ist s)
  | TacFail (n,s) -> tclFAIL (interp_int_or_var ist n) (interp_message ist s)
  | TacProgress tac -> tclPROGRESS (interp_tactic ist tac)
  | TacAbstract (tac,s) -> Tactics.tclABSTRACT s (interp_tactic ist tac)
  | TacThen (t1,tf,t,tl) -> 
      tclTHENS3PARTS (interp_tactic ist t1)
	(Array.map (interp_tactic ist) tf) (interp_tactic ist t) (Array.map (interp_tactic ist) tl)
  | TacThens (t1,tl) -> tclTHENS (interp_tactic ist t1) (List.map (interp_tactic ist) tl)
  | TacDo (n,tac) -> tclDO (interp_int_or_var ist n) (interp_tactic ist tac)
  | TacTry tac -> tclTRY (interp_tactic ist tac)
  | TacInfo tac -> tclINFO (interp_tactic ist tac)
  | TacRepeat tac -> tclREPEAT (interp_tactic ist tac)
  | TacOrelse (tac1,tac2) ->
        tclORELSE (interp_tactic ist tac1) (interp_tactic ist tac2)
  | TacFirst l -> tclFIRST (List.map (interp_tactic ist) l)
  | TacSolve l -> tclSOLVE (List.map (interp_tactic ist) l)
  | TacComplete tac -> tclCOMPLETE (interp_tactic ist tac)
  | TacArg a -> assert false

and interp_ltac_reference isapplied mustbetac ist gl = function
  | ArgVar (loc,id) ->
      let v = List.assoc id ist.lfun in
      if mustbetac then coerce_to_tactic loc id v else v
  | ArgArg (loc,r) ->
      let ids = extract_ids [] ist.lfun in
      let ist = 
        { lfun=[]; debug=ist.debug; avoid_ids=ids;
          last_loc = if isapplied then ist.last_loc else loc } in
      val_interp ist gl (lookup r)

and interp_tacarg ist gl = function
  | TacVoid -> VVoid
  | Reference r -> interp_ltac_reference false false ist gl r
  | Integer n -> VInteger n
  | IntroPattern ipat -> VIntroPattern (interp_intro_pattern ist gl ipat)
  | ConstrMayEval c -> VConstr (interp_constr_may_eval ist gl c)
  | MetaIdArg (loc,id) -> assert false
  | TacCall (loc,r,[]) -> interp_ltac_reference false true ist gl r
  | TacCall (loc,f,l) ->
      let fv = interp_ltac_reference true true ist gl f
      and largs = List.map (interp_tacarg ist gl) l in
      List.iter check_is_value largs;
      interp_app ist gl fv largs loc
  | TacExternal (loc,com,req,la) ->
      interp_external loc ist gl com req (List.map (interp_tacarg ist gl) la)
  | TacFreshId l -> 
      let id = interp_fresh_id ist gl l in
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
        VConstr (constr_out t)
      else
        anomaly_loc (dloc, "Tacinterp.val_interp",
          (str "Unknown dynamic: <" ++ str (Dyn.tag t) ++ str ">"))

(* Interprets an application node *)
and interp_app ist gl fv largs loc =
  match fv with
    | VFun(olfun,var,body) ->
      let (newlfun,lvar,lval)=head_with_value (var,largs) in
      if lvar=[] then
	let v = 
	  try
            let lloc = if lval=[] then loc else ist.last_loc in
	    val_interp { ist with lfun=newlfun@olfun; last_loc=lloc } gl body
	  with e ->
            debugging_exception_step ist false e (fun () -> str "evaluation");
	    raise e in
        debugging_step ist (fun () ->
	  str "evaluation returns" ++ fnl() ++ pr_value (Some (pf_env gl)) v);
        if lval=[] then v else interp_app ist gl v lval loc
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
and eval_with_fail ist is_lazy goal tac =
  try
    (match val_interp ist goal tac with
    | VTactic (loc,tac) when not is_lazy -> VRTactic (catch_error loc tac goal)
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
	let ndc = Environ.named_context_val env in
	start_proof id (Local,Proof Lemma) ndc typ (fun _ _ -> ());
	by t;
	let (_,({const_entry_body = pft},_,_)) = cook_proof () in
	delete_proof (dloc,id);
        pft
      with | NotTactic ->
	delete_proof (dloc,id);
	errorlabstrm "Tacinterp.interp_letin"
          (str "Term or fully applied tactic expected in Let")
    in (id,VConstr (mkCast (csr,DEFAULTcast, typ)))::(interp_letin ist gl tl)

(* Interprets the Match Context expressions *)
and interp_match_context ist g lz lr lmr =
  let rec apply_goal_sub ist env goal nocc (id,c) csr mt mhyps hyps =
    let (lgoal,ctxt) = match_subterm nocc c csr in
    let lctxt = give_context ctxt id in
      try apply_hyps_context ist env lz goal mt lctxt lgoal mhyps hyps
      with e when is_match_catchable e ->
	apply_goal_sub ist env goal (nocc + 1) (id,c) csr mt mhyps hyps in
  let rec apply_match_context ist env goal nrs lex lpt = 
    begin
      if lex<>[] then db_pattern_rule ist.debug nrs (List.hd lex);
      match lpt with
	| (All t)::tl ->
	    begin
              db_mc_pattern_success ist.debug;
              try eval_with_fail ist lz goal t
              with e when is_match_catchable e ->
		apply_match_context ist env goal (nrs+1) (List.tl lex) tl
	    end
	| (Pat (mhyps,mgoal,mt))::tl ->
	    let hyps = make_hyps (pf_hyps goal) in
	    let hyps = if lr then List.rev hyps else hyps in
	    let mhyps = List.rev mhyps (* Sens naturel *) in
	    let concl = pf_concl goal in
	      (match mgoal with
		 | Term mg ->
		     (try
			let lgoal = matches mg concl in
			  db_matched_concl ist.debug (pf_env goal) concl;
			  apply_hyps_context ist env lz goal mt [] lgoal mhyps hyps
		      with e when is_match_catchable e ->
			(match e with
			   | PatternMatchingFailure -> db_matching_failure ist.debug
			   | Eval_fail s -> db_eval_failure ist.debug s
			   | _ -> db_logic_failure ist.debug e);
			apply_match_context ist env goal (nrs+1) (List.tl lex) tl)
		 | Subterm (id,mg) ->
		     (try apply_goal_sub ist env goal 0 (id,mg) concl mt mhyps hyps
		      with
			| PatternMatchingFailure ->
			    apply_match_context ist env goal (nrs+1) (List.tl lex) tl))
	| _ ->
	    errorlabstrm "Tacinterp.apply_match_context"
              (v 0 (str "No matching clauses for match goal" ++
		      (if ist.debug=DebugOff then
			 fnl() ++ str "(use \"Set Ltac Debug\" for more info)"
		       else mt())))
    end in
  let env = pf_env g in
    apply_match_context ist env g 0 lmr
      (read_match_rule (fst (constr_list ist env)) lmr)

(* Tries to match the hypotheses in a Match Context *)
and apply_hyps_context ist env lz goal mt lctxt lgmatch mhyps hyps =
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
          with e when is_match_catchable e -> 
	      apply_hyps_context_rec lfun lmatch lhyps_rest next mhyps
        end
    | [] ->
	let lmatch = List.map (fun (id,c) -> (id,VConstr c)) lmatch in
        db_mc_pattern_success ist.debug;
        eval_with_fail {ist with lfun=lmatch@lfun@ist.lfun} lz goal mt
  in
  apply_hyps_context_rec lctxt lgmatch hyps (hyps,0) mhyps

and interp_external loc ist gl com req la =
  let f ch = extern_request ch req gl la in
  let g ch = internalise_tacarg ch in
  interp_tacarg ist gl (System.connect f g com)

  (* Interprets extended tactic generic arguments *)
and interp_genarg ist gl x =
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
        (interp_intro_pattern ist gl (out_gen globwit_intro_pattern x))
  | IdentArgType ->
      in_gen wit_ident
        (interp_fresh_ident ist gl (out_gen globwit_ident x))
  | VarArgType ->
      in_gen wit_var (interp_hyp ist gl (out_gen globwit_var x))
  | RefArgType ->
      in_gen wit_ref (pf_interp_reference ist gl (out_gen globwit_ref x))
  | SortArgType ->
      in_gen wit_sort
        (destSort 
	  (pf_interp_constr ist gl 
	    (RSort (dloc,out_gen globwit_sort x), None)))
  | ConstrArgType ->
      in_gen wit_constr (pf_interp_constr ist gl (out_gen globwit_constr x))
  | ConstrMayEvalArgType ->
      in_gen wit_constr_may_eval (interp_constr_may_eval ist gl (out_gen globwit_constr_may_eval x))
  | QuantHypArgType ->
      in_gen wit_quant_hyp
        (interp_declared_or_quantified_hypothesis ist gl
          (out_gen globwit_quant_hyp x))
  | RedExprArgType ->
      in_gen wit_red_expr (pf_interp_red_expr ist gl (out_gen globwit_red_expr x))
  | OpenConstrArgType casted ->
      Util.anomaly "Tacinterp.interp_genarg: OpenConstrArgType: obsolete"
      (* arnaud: obsolète:
      in_gen (wit_open_constr_gen casted) 
        (pf_interp_open_constr casted ist gl 
          (snd (out_gen (globwit_open_constr_gen casted) x))) *)
  | ConstrWithBindingsArgType ->
      Util.anomaly "Tacinterp.interp_genarg: WithBindingsArgType: obsolete"
      (* arnaud: obsolète:
      in_gen wit_constr_with_bindings
        (interp_constr_with_bindings ist gl (out_gen globwit_constr_with_bindings x)) *)
  | BindingsArgType ->
      Util.anomaly "Tacinterp.interp_genarg: BindingsArgType: obsolete"
      (* arnaud: obsolète:
      in_gen wit_bindings
        (interp_bindings ist gl (out_gen globwit_bindings x)) *)
  | List0ArgType ConstrArgType -> interp_genarg_constr_list0 ist gl x
  | List1ArgType ConstrArgType -> interp_genarg_constr_list1 ist gl x
  | List0ArgType VarArgType -> interp_genarg_var_list0 ist gl x
  | List1ArgType VarArgType -> interp_genarg_var_list1 ist gl x
  | List0ArgType _ -> app_list0 (interp_genarg ist gl) x
  | List1ArgType _ -> app_list1 (interp_genarg ist gl) x
  | OptArgType _ -> app_opt (interp_genarg ist gl) x
  | PairArgType _ -> app_pair (interp_genarg ist gl) (interp_genarg ist gl) x
  | ExtraArgType s -> 
      match tactic_genarg_level s with
      | Some n -> 
          (* Special treatment of tactic arguments *)
          in_gen (wit_tactic n) (out_gen (globwit_tactic n) x)
      | None -> 
          lookup_interp_genarg s ist gl x

and interp_genarg_constr_list0 ist gl x =
  let lc = out_gen (wit_list0 globwit_constr) x in
  let lc = pf_interp_constr_list ist gl lc in
  in_gen (wit_list0 wit_constr) lc

and interp_genarg_constr_list1 ist gl x =
  let lc = out_gen (wit_list1 globwit_constr) x in
  let lc = pf_interp_constr_list ist gl lc in
  in_gen (wit_list1 wit_constr) lc

and interp_genarg_var_list0 ist gl x =
  let lc = out_gen (wit_list0 globwit_var) x in
  let lc = interp_hyp_list ist gl lc in
  in_gen (wit_list0 wit_var) lc

and interp_genarg_var_list1 ist gl x =
  let lc = out_gen (wit_list1 globwit_var) x in
  let lc = interp_hyp_list ist gl lc in
  in_gen (wit_list1 wit_var) lc

(* Interprets the Match expressions *)
and interp_match ist g lz constr lmr =
  let rec apply_match_subterm ist nocc (id,c) csr mt =
    let (lm,ctxt) = match_subterm nocc c csr in
    let lctxt = give_context ctxt id in
    let lm = List.map (fun (id,c) -> (id,VConstr c)) lm in
    try eval_with_fail {ist with lfun=lm@lctxt@ist.lfun} lz g mt
    with e when is_match_catchable e ->
      apply_match_subterm ist (nocc + 1) (id,c) csr mt
  in
  let rec apply_match ist csr = function
    | (All t)::_ ->
        (try eval_with_fail ist lz g t
         with e when is_match_catchable e -> apply_match ist csr [])
    | (Pat ([],Term c,mt))::tl ->
        (try
            let lm = 
              try matches c csr
              with e ->
                debugging_exception_step ist false e (fun () ->
                  str "matching with pattern" ++ fnl () ++
                  pr_constr_pattern_env (pf_env g) c);
                raise e in
            try
              let lm = List.map (fun (id,c) -> (id,VConstr c)) lm in
              eval_with_fail { ist with lfun=lm@ist.lfun } lz g mt
            with e ->
              debugging_exception_step ist false e (fun () ->
                str "rule body for pattern" ++
                pr_constr_pattern_env (pf_env g) c);
              raise e
         with e when is_match_catchable e ->
           debugging_step ist (fun () -> str "switching to the next rule");
           apply_match ist csr tl)

    | (Pat ([],Subterm (id,c),mt))::tl ->
        (try apply_match_subterm ist 0 (id,c) csr mt
         with PatternMatchingFailure -> apply_match ist csr tl)
    | _ ->
      errorlabstrm "Tacinterp.apply_match" (str
        "No matching clauses for match") in
  let csr = 
      try interp_ltac_constr ist g constr with e ->
        debugging_exception_step ist true e
          (fun () -> str "evaluation of the matched expression");
        raise e in
  let ilr = read_match_rule (fst (constr_list ist (pf_env g))) lmr in
  let res = 
     try apply_match ist csr ilr with e -> 
       debugging_exception_step ist true e (fun () -> str "match expression");
       raise e in
  debugging_step ist (fun () ->
    str "match expression returns " ++ pr_value (Some (pf_env g)) res);
  res

(* Interprets tactic expressions : returns a "constr" *)
and interp_ltac_constr ist gl e =
  let result = 
  try val_interp ist gl e with Not_found -> 
    debugging_step ist (fun () ->
      str "evaluation failed for" ++ fnl() ++
      Pptactic.pr_glob_tactic (pf_env gl) e);
    raise Not_found in
  try
    let cresult = constr_of_value (pf_env gl) result in
    debugging_step ist (fun () ->
      Pptactic.pr_glob_tactic (pf_env gl) e ++ fnl() ++
      str " has value " ++ fnl() ++ print_constr_env (pf_env gl) cresult);
    cresult
  with Not_found ->
    errorlabstrm ""
      (str "Must evaluate to a term" ++ fnl() ++ 
	  str "offending expression: " ++ fnl() ++
          Pptactic.pr_glob_tactic (pf_env gl) e ++ fnl() ++ str "this is a " ++
          (match result with
              VTactic _ -> str "VTactic"
            | VRTactic _ -> str "VRTactic"
            | VFun (il,ul,b) ->
                (str "VFun with body " ++ fnl() ++
                    Pptactic.pr_glob_tactic (pf_env gl) b ++ fnl() ++
		    str "instantiated arguments " ++ fnl() ++
                    List.fold_right 
                    (fun p s ->
                      let (i,v) = p in str (string_of_id i) ++ str ", " ++ s)
                    il (str "") ++
                    str "uninstantiated arguments " ++ fnl() ++
                    List.fold_right
                    (fun opt_id s ->
                      (match opt_id with
                          Some id -> str (string_of_id id)
                        | None -> str "_") ++ str ", " ++ s)
                    ul (str ""))
            | VVoid -> str "VVoid"
            | VInteger _ -> str "VInteger"
            | VConstr _ -> str "VConstr"
            | VIntroPattern _ -> str "VIntroPattern"
            | VConstr_context _ -> str "VConstrr_context"
            | VRec _ -> str "VRec"
            | VList _ -> str "VList"))

(* Interprets tactic expressions : returns a "tactic" *)
and interp_tactic ist tac gl =
  try tactic_of_value (val_interp ist gl tac) gl
  with NotTactic ->
    errorlabstrm "" (str "Must be a command or must give a tactic value")

(* Interprets a primitive tactic *)
and interp_atomic ist gl = function
  (* Basic tactics *)
  | TacIntroPattern l ->
      h_intro_patterns (List.map (interp_intro_pattern ist gl) l)
  | TacIntrosUntil hyp ->
      h_intros_until (interp_quantified_hypothesis ist hyp)
  | TacIntroMove (ido,ido') ->
      h_intro_move (Option.map (interp_fresh_ident ist gl) ido)
      (Option.map (interp_hyp ist gl) ido')
  | TacAssumption -> h_assumption
  | TacExact c -> h_exact (pf_interp_casted_constr ist gl c)
  | TacExactNoCheck c -> h_exact_no_check (pf_interp_constr ist gl c)
  | TacVmCastNoCheck c -> h_vm_cast_no_check (pf_interp_constr ist gl c)
  | TacApply (ev,cb) -> Util.anomaly "Tacinterp.interp_atomic: deprecated" (* arnaud: obsolète: h_apply ev (interp_constr_with_bindings ist gl cb)*)
  | TacElim (ev,cb,cbo) ->
      Util.anomaly "Tacinterp.interp_atomic: deprecated" (* arnaud: obsolète: h_elim ev (interp_constr_with_bindings ist gl cb)
                (Option.map (interp_constr_with_bindings ist gl) cbo) *)
  | TacElimType c -> h_elim_type (pf_interp_type ist gl c)
  | TacCase (ev,cb) -> Util.anomaly "Tacinterp.interp_atomic: deprecated" (* arnaud: obsolète: h_case ev (interp_constr_with_bindings ist gl cb)*)
  | TacCaseType c -> h_case_type (pf_interp_type ist gl c)
  | TacFix (idopt,n) -> h_fix (Option.map (interp_fresh_ident ist gl) idopt) n
  | TacMutualFix (id,n,l) ->
      let f (id,n,c) = (interp_fresh_ident ist gl id,n,pf_interp_type ist gl c)
      in h_mutual_fix (interp_fresh_ident ist gl id) n (List.map f l)
  | TacCofix idopt -> h_cofix (Option.map (interp_fresh_ident ist gl) idopt)
  | TacMutualCofix (id,l) ->
      let f (id,c) = (interp_fresh_ident ist gl id,pf_interp_type ist gl c) in
      h_mutual_cofix (interp_fresh_ident ist gl id) (List.map f l)
  | TacCut c -> h_cut (pf_interp_type ist gl c)
  | TacAssert (t,ipat,c) ->
      let c = (if t=None then pf_interp_constr else pf_interp_type) ist gl c in
      abstract_tactic (TacAssert (t,ipat,inj_open c))
        (Tactics.forward (Option.map (interp_tactic ist) t)
	  (interp_intro_pattern ist gl ipat) c)
  | TacGeneralize cl -> h_generalize (pf_interp_constr_list ist gl cl)
  | TacGeneralizeDep c -> h_generalize_dep (pf_interp_constr ist gl c)
  | TacLetTac (na,c,clp) ->
      let clp = interp_clause ist gl clp in
      h_let_tac (interp_fresh_name ist gl na) (pf_interp_constr ist gl c) clp

  (* Automation tactics *)
  | TacTrivial (lems,l) -> 
      Util.anomaly "Tacinterp.interp_atomic: TacTrivial: obsolète"
      (* arnaud: obsolète:
      Auto.h_trivial (pf_interp_constr_list ist gl lems)
	(Option.map (List.map (interp_hint_base ist)) l)\
      *)
  | TacAuto (n,lems,l) ->
      Util.anomaly "Tacinterp.interp_atomic: TacAuto: obsolète"
      (* arnaud: obsolète:
      Auto.h_auto (Option.map (interp_int_or_var ist) n)
      (pf_interp_constr_list ist gl lems)
      (Option.map (List.map (interp_hint_base ist)) l)
      *)
  | TacAutoTDB n -> Dhyp.h_auto_tdb n
  | TacDestructHyp (b,id) -> Dhyp.h_destructHyp b (interp_hyp ist gl id)
  | TacDestructConcl -> Dhyp.h_destructConcl
  | TacSuperAuto (n,l,b1,b2) -> Util.anomaly "Tacinterp.interp_atomic: TacSuperAuto"(* Auto.h_superauto n l b1 b2 *)
  | TacDAuto (n,p,lems) ->
      Util.anomaly "Tacinterp.interp_atomic: TacDAuto: obsolète"
      (* arnaud: obsolète:
      Auto.h_dauto (Option.map (interp_int_or_var ist) n,p)
      (pf_interp_constr_list ist gl lems)
      *)

  (* Derived basic tactics *)
  | TacSimpleInduction h ->
      h_simple_induction (interp_quantified_hypothesis ist h)
  | TacNewInduction (ev,lc,cbo,ids) ->
      Util.anomaly "Tacinterp.interp_atomic: deprecated" (* arnaud: obsolète          h_new_induction ev (List.map (interp_induction_arg ist gl) lc)
        (Option.map (interp_constr_with_bindings ist gl) cbo)
        (interp_intro_pattern ist gl ids) *)
  | TacSimpleDestruct h ->
      h_simple_destruct (interp_quantified_hypothesis ist h)
  | TacNewDestruct (ev,c,cbo,ids) -> 
      Util.anomaly "Tacinterp.interp_atomic: deprecated" (* arnaud: obsolète
      h_new_destruct ev (List.map (interp_induction_arg ist gl) c)
        (Option.map (interp_constr_with_bindings ist gl) cbo)
        (interp_intro_pattern ist gl ids) *)
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
      Util.anomaly "Tacinterp.interp_atomic: deprecated" (* arnaud: obsolète          h_specialize n (interp_constr_with_bindings ist gl l) *)
  | TacLApply c -> h_lapply (pf_interp_constr ist gl c)

  (* Context management *)
  | TacClear (b,l) -> h_clear b (interp_hyp_list ist gl l)
  | TacClearBody l -> h_clear_body (interp_hyp_list ist gl l)
  | TacMove (dep,id1,id2) ->
      h_move dep (interp_hyp ist gl id1) (interp_hyp ist gl id2)
  | TacRename l ->
      h_rename (List.map (fun (id1,id2) -> 
			    interp_hyp ist gl id1, 
			    interp_fresh_ident ist gl (snd id2)) l)

  (* Constructors *)
  | TacLeft bl -> Util.anomaly "Tacinterp.interp_atomic: deprecated" (* arnaud: obsolète h_left (interp_bindings ist gl bl) *)
  | TacRight bl -> Util.anomaly "Tacinterp.interp_atomic: deprecated" (* arnaud: obsolète h_right (interp_bindings ist gl bl) *)
  | TacSplit (_,bl) -> Util.anomaly "Tacinterp.interp_atomic: deprecated" (* arnaud: obsolète h_split (interp_bindings ist gl bl) *)
  | TacAnyConstructor t ->
      abstract_tactic (TacAnyConstructor t)
        (Tactics.any_constructor (Option.map (interp_tactic ist) t))
  | TacConstructor (n,bl) ->
      Util.anomaly "Tacinterp.interp_atomic: deprecated" (* arnaud: obsolète h_constructor (skip_metaid n) (interp_bindings ist gl bl) *)

  (* Conversion *)
  | TacReduce (r,cl) ->
      h_reduce (pf_interp_red_expr ist gl r) (interp_clause ist gl cl)
  | TacChange (occl,c,cl) ->
      h_change (Option.map (pf_interp_pattern ist gl) occl)
        (if occl = None then pf_interp_type ist gl c 
	 else pf_interp_constr ist gl c)
        (interp_clause ist gl cl)

  (* Equivalence relations *)
  | TacReflexivity -> h_reflexivity
  | TacSymmetry c -> h_symmetry (interp_clause ist gl c)
  | TacTransitivity c -> h_transitivity (pf_interp_constr ist gl c)

  (* Equality and inversion *)
  | TacRewrite (ev,l,cl) -> Util.anomaly "Tacinterp.interp_atomic: deprecated" (* arnaud: obsolète 
      Equality.general_multi_multi_rewrite ev
	(List.map (fun (b,c) -> (b, interp_constr_with_bindings ist gl c)) l)
	(interp_clause ist gl cl) *)
  | TacInversion (DepInversion (k,c,ids),hyp) ->
      Inv.dinv k (Option.map (pf_interp_constr ist gl) c)
        (interp_intro_pattern ist gl ids)
        (interp_declared_or_quantified_hypothesis ist gl hyp)
  | TacInversion (NonDepInversion (k,idl,ids),hyp) ->
      Inv.inv_clause k 
        (interp_intro_pattern ist gl ids)
        (interp_hyp_list ist gl idl)
        (interp_declared_or_quantified_hypothesis ist gl hyp)
  | TacInversion (InversionUsing (c,idl),hyp) ->
      Leminv.lemInv_clause (interp_declared_or_quantified_hypothesis ist gl hyp)
        (pf_interp_constr ist gl c)
        (interp_hyp_list ist gl idl)

  (* For extensions *)
  | TacExtend (loc,opn,l) ->
      let tac = lookup_tactic opn in
      fun gl ->
        let args = List.map (interp_genarg ist gl) l in
        abstract_extended_tactic opn args (tac args) gl
  | TacAlias (loc,_,l,(_,body)) -> fun gl ->
    let rec f x = match genarg_tag x with
    | IntArgType -> 
        VInteger (out_gen globwit_int x)
    | IntOrVarArgType ->
        mk_int_or_var_value ist (out_gen globwit_int_or_var x)
    | PreIdentArgType ->
	failwith "pre-identifiers cannot be bound"
    | IntroPatternArgType ->
	VIntroPattern 
	  (interp_intro_pattern ist gl (out_gen globwit_intro_pattern x))
    | IdentArgType -> 
        VIntroPattern 
	  (IntroIdentifier
              (interp_fresh_ident ist gl (out_gen globwit_ident x)))
    | VarArgType ->
        mk_hyp_value ist gl (out_gen globwit_var x)
    | RefArgType -> 
        VConstr (constr_of_global 
          (pf_interp_reference ist gl (out_gen globwit_ref x)))
    | SortArgType -> 
        VConstr (mkSort (interp_sort (out_gen globwit_sort x)))
    | ConstrArgType ->
        mk_constr_value ist gl (out_gen globwit_constr x)
    | ConstrMayEvalArgType ->
	VConstr
          (interp_constr_may_eval ist gl (out_gen globwit_constr_may_eval x))
    | ExtraArgType s when tactic_genarg_level s <> None ->
          (* Special treatment of tactic arguments *)
	val_interp ist gl 
          (out_gen (globwit_tactic (Option.get (tactic_genarg_level s))) x)
    | List0ArgType ConstrArgType -> 
        let wit = wit_list0 globwit_constr in
        VList (List.map (mk_constr_value ist gl) (out_gen wit x))
    | List0ArgType VarArgType -> 
        let wit = wit_list0 globwit_var in
        VList (List.map (mk_hyp_value ist gl) (out_gen wit x))
    | List0ArgType IntArgType -> 
        let wit = wit_list0 globwit_int in
        VList (List.map (fun x -> VInteger x) (out_gen wit x))
    | List0ArgType IntOrVarArgType -> 
        let wit = wit_list0 globwit_int_or_var in
        VList (List.map (mk_int_or_var_value ist) (out_gen wit x))
    | List1ArgType ConstrArgType -> 
        let wit = wit_list1 globwit_constr in
        VList (List.map (mk_constr_value ist gl) (out_gen wit x))
    | List1ArgType VarArgType -> 
        let wit = wit_list1 globwit_var in
        VList (List.map (mk_hyp_value ist gl) (out_gen wit x))
    | List1ArgType IntArgType -> 
        let wit = wit_list1 globwit_int in
        VList (List.map (fun x -> VInteger x) (out_gen wit x))
    | List1ArgType IntOrVarArgType -> 
        let wit = wit_list1 globwit_int_or_var in
        VList (List.map (mk_int_or_var_value ist) (out_gen wit x))
    | StringArgType | BoolArgType
    | QuantHypArgType | RedExprArgType 
    | OpenConstrArgType _ | ConstrWithBindingsArgType 
    | ExtraArgType _ | BindingsArgType 
    | OptArgType _ | PairArgType _ 
    | List0ArgType _ | List1ArgType _ 
	-> error "This generic type is not supported in alias"
        
    in
    let lfun = (List.map (fun (x,c) -> (x,f c)) l)@ist.lfun in
    let v = locate_tactic_call loc (val_interp { ist with lfun=lfun } gl body)
    in 
    try tactic_of_value v gl 
    with NotTactic -> user_err_loc (loc,"",str "not a tactic")

let make_empty_glob_sign () =
  { ltacvars = ([],[]); ltacrecvars = []; 
    gsigma = Evd.empty; genv = Global.env() }

(* Initial call for interpretation *)
let interp_tac_gen lfun avoid_ids debug t gl = 
  interp_tactic { lfun=lfun; avoid_ids=avoid_ids; debug=debug; last_loc=dloc } 
    (intern_tactic {
      ltacvars = (List.map fst lfun, []); ltacrecvars = [];
      gsigma = project gl; genv = pf_env gl } t) gl

let eval_tactic t gls =
  interp_tactic { lfun=[]; avoid_ids=[]; debug=get_debug(); last_loc=dloc }
    t gls

let interp t = interp_tac_gen [] [] (get_debug()) t

let eval_ltac_constr gl t =
  interp_ltac_constr 
    { lfun=[]; avoid_ids=[]; debug=get_debug(); last_loc=dloc } gl
    (intern_tactic (make_empty_glob_sign ()) t )

(* Hides interpretation for pretty-print *)
let hide_interp t ot gl =
  let ist = { ltacvars = ([],[]); ltacrecvars = []; 
            gsigma = project gl; genv = pf_env gl } in
  let te = intern_tactic ist t in
  let t = eval_tactic te in
  match ot with 
  | None -> abstract_tactic_expr (TacArg (Tacexp te)) t gl
  | Some t' ->
      abstract_tactic_expr ~dflt:true (TacArg (Tacexp te)) (tclTHEN t t') gl

(***************************************************************************)
(* Substitution at module closing time *)

let subst_quantified_hypothesis _ x = x

let subst_declared_or_quantified_hypothesis _ x = x

let subst_rawconstr_and_expr subst (c,e) =
  assert (e=None); (* e<>None only for toplevel tactics *)
  (Detyping.subst_rawconstr subst c,None)

let subst_rawconstr = subst_rawconstr_and_expr (* shortening *)

let subst_binding subst (loc,b,c) =
  (loc,subst_quantified_hypothesis subst b,subst_rawconstr subst c)

let subst_bindings subst = function
  | NoBindings -> NoBindings
  | ImplicitBindings l -> ImplicitBindings (List.map (subst_rawconstr subst) l)
  | ExplicitBindings l -> ExplicitBindings (List.map (subst_binding subst) l)

let subst_raw_with_bindings subst (c,bl) =
  (subst_rawconstr subst c, subst_bindings subst bl)

let subst_induction_arg subst = function
  | ElimOnConstr c -> ElimOnConstr (subst_raw_with_bindings subst c)
  | ElimOnAnonHyp n as x -> x
  | ElimOnIdent id as x -> x

let subst_and_short_name f (c,n) =
(*  assert (n=None); *)(* since tacdef are strictly globalized *)
  (f c,None)

let subst_or_var f =  function
  | ArgVar _ as x -> x
  | ArgArg x -> ArgArg (f x)

let subst_located f (_loc,id) = (dloc,f id)

let subst_reference subst = 
  subst_or_var (subst_located (subst_kn subst))

(*CSC: subst_global_reference is used "only" for RefArgType, that propagates
  to the syntactic non-terminals "global", used in commands such as
  Print. It is also used for non-evaluable references. *) 
let subst_global_reference subst = 
 let subst_global ref =
  let ref',t' = subst_global subst ref in
   if not (eq_constr (constr_of_global ref') t') then
    ppnl (str "Warning: the reference " ++ pr_global ref ++ str " is not " ++
          str " expanded to \"" ++ pr_lconstr t' ++ str "\", but to " ++
          pr_global ref') ;
   ref'
 in
  subst_or_var (subst_located subst_global)

let subst_evaluable subst =
  let subst_eval_ref = subst_evaluable_reference subst in
    subst_or_var (subst_and_short_name subst_eval_ref)

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
  | Simpl o -> Simpl (Option.map (subst_constr_occurrence subst) o)
  | (Red _ | Hnf | ExtraRedExpr _ | CbvVm as r) -> r

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
  | TacExactNoCheck c -> TacExactNoCheck (subst_rawconstr subst c)
  | TacVmCastNoCheck c -> TacVmCastNoCheck (subst_rawconstr subst c)
  | TacApply (ev,cb) -> TacApply (ev,subst_raw_with_bindings subst cb)
  | TacElim (ev,cb,cbo) ->
      TacElim (ev,subst_raw_with_bindings subst cb,
               Option.map (subst_raw_with_bindings subst) cbo)
  | TacElimType c -> TacElimType (subst_rawconstr subst c)
  | TacCase (ev,cb) -> TacCase (ev,subst_raw_with_bindings subst cb)
  | TacCaseType c -> TacCaseType (subst_rawconstr subst c)
  | TacFix (idopt,n) as x -> x
  | TacMutualFix (id,n,l) ->
      TacMutualFix(id,n,List.map (fun (id,n,c) -> (id,n,subst_rawconstr subst c)) l)
  | TacCofix idopt as x -> x
  | TacMutualCofix (id,l) ->
      TacMutualCofix (id, List.map (fun (id,c) -> (id,subst_rawconstr subst c)) l)
  | TacCut c -> TacCut (subst_rawconstr subst c)
  | TacAssert (b,na,c) ->
      TacAssert (Option.map (subst_tactic subst) b,na,subst_rawconstr subst c)
  | TacGeneralize cl -> TacGeneralize (List.map (subst_rawconstr subst) cl)
  | TacGeneralizeDep c -> TacGeneralizeDep (subst_rawconstr subst c)
  | TacLetTac (id,c,clp) -> TacLetTac (id,subst_rawconstr subst c,clp)

  (* Automation tactics *)
  | TacTrivial (lems,l) -> TacTrivial (List.map (subst_rawconstr subst) lems,l)
  | TacAuto (n,lems,l) -> TacAuto (n,List.map (subst_rawconstr subst) lems,l)
  | TacAutoTDB n -> TacAutoTDB n
  | TacDestructHyp (b,id) -> TacDestructHyp(b,id)
  | TacDestructConcl -> TacDestructConcl
  | TacSuperAuto (n,l,b1,b2) -> TacSuperAuto (n,l,b1,b2)
  | TacDAuto (n,p,lems) -> TacDAuto (n,p,List.map (subst_rawconstr subst) lems)

  (* Derived basic tactics *)
  | TacSimpleInduction h as x -> x
  | TacNewInduction (ev,lc,cbo,ids) ->
      TacNewInduction (ev,List.map (subst_induction_arg subst) lc,
               Option.map (subst_raw_with_bindings subst) cbo, ids)
  | TacSimpleDestruct h as x -> x
  | TacNewDestruct (ev,c,cbo,ids) ->
      TacNewDestruct (ev,List.map (subst_induction_arg subst) c,
               Option.map (subst_raw_with_bindings subst) cbo, ids)
  | TacDoubleInduction (h1,h2) as x -> x
  | TacDecomposeAnd c -> TacDecomposeAnd (subst_rawconstr subst c)
  | TacDecomposeOr c -> TacDecomposeOr (subst_rawconstr subst c)
  | TacDecompose (l,c) ->
      let l = List.map (subst_or_var (subst_inductive subst)) l in
      TacDecompose (l,subst_rawconstr subst c)
  | TacSpecialize (n,l) -> TacSpecialize (n,subst_raw_with_bindings subst l)
  | TacLApply c -> TacLApply (subst_rawconstr subst c)

  (* Context management *)
  | TacClear _ as x -> x
  | TacClearBody l as x -> x
  | TacMove (dep,id1,id2) as x -> x
  | TacRename l as x -> x

  (* Constructors *)
  | TacLeft bl -> TacLeft (subst_bindings subst bl)
  | TacRight bl -> TacRight (subst_bindings subst bl)
  | TacSplit (b,bl) -> TacSplit (b,subst_bindings subst bl)
  | TacAnyConstructor t -> TacAnyConstructor (Option.map (subst_tactic subst) t)
  | TacConstructor (n,bl) -> TacConstructor (n, subst_bindings subst bl)

  (* Conversion *)
  | TacReduce (r,cl) -> TacReduce (subst_redexp subst r, cl)
  | TacChange (occl,c,cl) ->
      TacChange (Option.map (subst_constr_occurrence subst) occl,
        subst_rawconstr subst c, cl)

  (* Equivalence relations *)
  | TacReflexivity | TacSymmetry _ as x -> x
  | TacTransitivity c -> TacTransitivity (subst_rawconstr subst c)

  (* Equality and inversion *)
  | TacRewrite (ev,l,cl) -> 
      TacRewrite (ev, 
		  List.map (fun (b,c) ->b,subst_raw_with_bindings subst c) l,
		  cl)
  | TacInversion (DepInversion (k,c,l),hyp) ->
     TacInversion (DepInversion (k,Option.map (subst_rawconstr subst) c,l),hyp)
  | TacInversion (NonDepInversion _,_) as x -> x
  | TacInversion (InversionUsing (c,cl),hyp) ->
      TacInversion (InversionUsing (subst_rawconstr subst c,cl),hyp)

  (* For extensions *)
  | TacExtend (_loc,opn,l) ->
      TacExtend (dloc,opn,List.map (subst_genarg subst) l)
  | TacAlias (_,s,l,(dir,body)) ->
      TacAlias (dloc,s,List.map (fun (id,a) -> (id,subst_genarg subst a)) l,
        (dir,subst_tactic subst body))

and subst_tactic subst (t:glob_tactic_expr) = match t with
  | TacAtom (_loc,t) -> TacAtom (dloc, subst_atomic subst t)
  | TacFun tacfun -> TacFun (subst_tactic_fun subst tacfun)
  | TacLetRecIn (lrc,u) ->
      let lrc = List.map (fun (n,b) -> (n,subst_tactic_fun subst b)) lrc in
      TacLetRecIn (lrc,(subst_tactic subst u:glob_tactic_expr))
  | TacLetIn (l,u) ->
      let l = List.map (fun (n,c,b) -> (n,Option.map (subst_tactic subst) c,subst_tacarg subst b)) l in
      TacLetIn (l,subst_tactic subst u)
  | TacMatchContext (lz,lr,lmr) ->
      TacMatchContext(lz,lr, subst_match_rule subst lmr)
  | TacMatch (lz,c,lmr) ->
      TacMatch (lz,subst_tactic subst c,subst_match_rule subst lmr)
  | TacId _ | TacFail _ as x -> x
  | TacProgress tac -> TacProgress (subst_tactic subst tac:glob_tactic_expr)
  | TacAbstract (tac,s) -> TacAbstract (subst_tactic subst tac,s)
  | TacThen (t1,tf,t2,tl) ->
      TacThen (subst_tactic subst t1,Array.map (subst_tactic subst) tf,
	       subst_tactic subst t2,Array.map (subst_tactic subst) tl)
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
  | TacComplete tac -> TacComplete (subst_tactic subst tac)
  | TacArg a -> TacArg (subst_tacarg subst a)

and subst_tactic_fun subst (var,body) = (var,subst_tactic subst body)

and subst_tacarg subst = function
  | Reference r -> Reference (subst_reference subst r)
  | ConstrMayEval c -> ConstrMayEval (subst_raw_may_eval subst c)
  | MetaIdArg (_loc,_) -> assert false
  | TacCall (_loc,f,l) ->
      TacCall (_loc, subst_reference subst f, List.map (subst_tacarg subst) l)
  | TacExternal (_loc,com,req,la) -> 
      TacExternal (_loc,com,req,List.map (subst_tacarg subst) la)
  | (TacVoid | IntroPattern _ | Integer _ | TacFreshId _) as x -> x
  | Tacexp t -> Tacexp (subst_tactic subst t)
  | TacDynamic(the_loc,t) as x ->
      (match tag t with
	| "tactic" | "value" -> x
        | "constr" -> 
          TacDynamic(the_loc, constr_in (subst_mps subst (constr_out t)))
	| s -> anomaly_loc (dloc, "Tacinterp.val_interp",
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
  | VarArgType -> in_gen globwit_var (out_gen globwit_var x)
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
  | OpenConstrArgType b ->
      in_gen (globwit_open_constr_gen b)
        ((),subst_rawconstr subst (snd (out_gen (globwit_open_constr_gen b) x)))
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
  | ExtraArgType s ->
      match tactic_genarg_level s with
      | Some n -> 
          (* Special treatment of tactic arguments *)
          in_gen (globwit_tactic n)
            (subst_tactic subst (out_gen (globwit_tactic n) x))
      | None -> 
          lookup_genarg_subst s subst x

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

let print_ltac id =
 try
  let kn = Nametab.locate_tactic id in
  let t = lookup kn in
   str "Ltac" ++ spc() ++ pr_qualid id ++ str ":=" ++ spc() ++
    Pptactic.pr_glob_tactic (Global.env ()) t
 with
  Not_found ->
   errorlabstrm "print_ltac"
    (pr_qualid id ++ spc() ++ str "is not a user defined tactic")

(* Adds a definition for tactics in the table *)
let make_absolute_name (loc,id) =
  let kn = Lib.make_kn id in
  if Gmap.mem kn !mactab or is_atomic_kn kn then
    user_err_loc (loc,"Tacinterp.add_tacdef",
      str "There is already an Ltac named " ++ pr_id id);
  kn

let add_tacdef isrec tacl =
(*  let isrec = if !Flags.p1 then isrec else true in*)
  let rfun = List.map (fun ((loc,id as locid),_) -> (id,make_absolute_name locid)) tacl in
  let ist =
    {(make_empty_glob_sign()) with ltacrecvars = if isrec then rfun else []} in
  let gtacl =
    List.map (fun ((_,id),def) ->
      (id,Flags.with_option strict_check (intern_tactic ist) def))
      tacl in
  let id0 = fst (List.hd rfun) in
  let _ = Lib.add_leaf id0 (inMD gtacl) in
  List.iter
    (fun (id,_) -> Flags.if_verbose msgnl (pr_id id ++ str " is defined"))
    rfun

(***************************************************************************)
(* Other entry points *)

let glob_tactic x = intern_tactic (make_empty_glob_sign ()) x

let glob_tactic_env l env x = 
  Flags.with_option strict_check
  (intern_tactic
    { ltacvars = (l,[]); ltacrecvars = []; gsigma = Evd.empty; genv = env })
    x

let interp_redexp env sigma r = 
  let ist = { lfun=[]; avoid_ids=[]; debug=get_debug (); last_loc=dloc } in
  let gist = {(make_empty_glob_sign ()) with genv = env; gsigma = sigma } in
  interp_red_expr ist sigma env (intern_red_expr gist r)

(***************************************************************************)
(* Backwarding recursive needs of tactic glob/interp/eval functions *)

(* arnaud: à porter sans doute.
let _ = Auto.set_extern_interp
  (fun l -> 
    let l = List.map (fun (id,c) -> (id,VConstr c)) l in
    interp_tactic {lfun=l;avoid_ids=[];debug=get_debug(); last_loc=dloc})
let _ = Auto.set_extern_intern_tac 
  (fun l ->
    Flags.with_option strict_check
    (intern_tactic {(make_empty_glob_sign()) with ltacvars=(l,[])}))
let _ = Auto.set_extern_subst_tactic subst_tactic
let _ = Dhyp.set_extern_interp eval_tactic
let _ = Dhyp.set_extern_intern_tac
  (fun t -> intern_tactic (make_empty_glob_sign()) t)

*)
