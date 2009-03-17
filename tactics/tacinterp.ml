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

let safe_msgnl s =
    try msgnl s with e -> 
      msgnl 
	(str "bug in the debugger: " ++
         str "an exception is raised while printing debug information")

let error_syntactic_metavariables_not_allowed loc =
  user_err_loc 
    (loc,"out_ident",
     str "Syntactic metavariables allowed only in quotations.")

let error_global_not_found_loc (loc,qid) = error_global_not_found_loc loc qid

let skip_metaid = function
  | AI x -> x
  | MetaId (loc,_) -> error_syntactic_metavariables_not_allowed loc

type ltac_type =
  | LtacFun of ltac_type
  | LtacBasic
  | LtacTactic

(* Values for interpretation *)
type value =
  | VRTactic of (goal list sigma * validation) (* For Match results *)
                                               (* Not a true value *)
  | VFun of ltac_trace * (identifier*value) list * 
      identifier option list * glob_tactic_expr
  | VVoid
  | VInteger of int
  | VIntroPattern of intro_pattern_expr (* includes idents which are not *)
                        (* bound as in "Intro H" but which may be bound *)
                        (* later, as in "tac" in "Intro H; tac" *)
  | VConstr of constr   (* includes idents known to be bound and references *)
  | VConstr_context of constr
  | VList of value list
  | VRec of (identifier*value) list ref * glob_tactic_expr

let dloc = dummy_loc

let catch_error call_trace tac g =
  if call_trace = [] then tac g else try tac g with
  | LtacLocated _ as e -> raise e
  | Stdpp.Exc_located (_,LtacLocated _) as e -> raise e
  | e ->
    let (nrep,loc',c),tail = list_sep_last call_trace in
    let loc,e' = match e with Stdpp.Exc_located(loc,e) -> loc,e | _ ->dloc,e in
    if tail = [] then
      let loc = if loc = dloc then loc' else loc in
      raise (Stdpp.Exc_located(loc,e'))
    else
      raise (Stdpp.Exc_located(loc',LtacLocated((nrep,c,tail,loc),e')))

(* Signature for interpretation: val_interp and interpretation functions *)
type interp_sign =
    { lfun : (identifier * value) list;
      avoid_ids : identifier list; (* ids inherited from the call context
				      (needed to get fresh ids) *)
      debug : debug_info;
      trace : ltac_trace }

let check_is_value = function
  | VRTactic _ -> (* These are goals produced by Match *)
   error "Immediate match producing tactics not allowed in local definitions."
  | _ -> ()

(* For tactic_of_value *)
exception NotTactic

(* Gives the constr corresponding to a Constr_context tactic_arg *)
let constr_of_VConstr_context = function
  | VConstr_context c -> c
  | _ ->
    errorlabstrm "constr_of_VConstr_context" (str "Not a context variable.")

(* Displays a value *)
let rec pr_value env = function
  | VVoid -> str "()"
  | VInteger n -> int n
  | VIntroPattern ipat -> pr_intro_pattern (dloc,ipat)
  | VConstr c | VConstr_context c ->
      (match env with Some env -> pr_lconstr_env env c | _ -> str "a term")
  | (VRTactic _ | VFun _ | VRec _) -> str "a tactic"
  | VList [] -> str "an empty list"
  | VList (a::_) ->
      str "a list (first element is " ++ pr_value env a ++ str")"

(* Transforms an id into a constr if possible, or fails *)
let constr_of_id env id = 
  construct_reference (Environ.named_context env) id

(* To embed tactics *)
let ((tactic_in : (interp_sign -> glob_tactic_expr) -> Dyn.t),
     (tactic_out : Dyn.t -> (interp_sign -> glob_tactic_expr))) =
  create "tactic"

let ((value_in : value -> Dyn.t),
     (value_out : Dyn.t -> value)) = create "value"

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
     str "to an evaluable reference.")

(* Table of "pervasives" macros tactics (e.g. auto, simpl, etc.) *)
let atomic_mactab = ref Idmap.empty
let add_primitive_tactic s tac =
  let id = id_of_string s in
  atomic_mactab := Idmap.add id tac !atomic_mactab

let _ =
  let nocl = {onhyps=Some[];concl_occs=all_occurrences_expr} in
  List.iter
      (fun (s,t) -> add_primitive_tactic s (TacAtom(dloc,t)))
      [ "red", TacReduce(Red false,nocl);
        "hnf", TacReduce(Hnf,nocl);
        "simpl", TacReduce(Simpl None,nocl);
        "compute", TacReduce(Cbv all_flags,nocl);
        "intro", TacIntroMove(None,no_move);
        "intros", TacIntroPattern [];
        "assumption", TacAssumption;
        "cofix", TacCofix None;
        "trivial", TacTrivial ([],None);
        "auto", TacAuto(None,[],None);
        "left", TacLeft(false,NoBindings);
        "eleft", TacLeft(true,NoBindings);
        "right", TacRight(false,NoBindings);
        "eright", TacRight(true,NoBindings);
        "split", TacSplit(false,false,NoBindings);
        "esplit", TacSplit(true,false,NoBindings);
        "constructor", TacAnyConstructor (false,None);
        "econstructor", TacAnyConstructor (true,None);
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
let is_atomic_kn kn =
  let (_,_,l) = repr_kn kn in
  Idmap.mem (id_of_label l) !atomic_mactab

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
      (str ("Cannot redeclare tactic "^s^"."));
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
      (str"The tactic " ++ str s ++ str" is not installed.")
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

let push_trace (loc,ck) = function
  | (n,loc',ck')::trl when ck=ck' -> (n+1,loc,ck)::trl
  | trl -> (1,loc,ck)::trl

let propagate_trace ist loc id = function
  | VFun (_,lfun,it,b) ->
      let t = if it=[] then b else TacFun (it,b) in
      VFun (push_trace(loc,LtacVarCall (id,t)) ist.trace,lfun,it,b)
  | x -> x

(* Dynamically check that an argument is a tactic *)
let coerce_to_tactic loc id = function
  | VFun _ | VRTactic _ as a -> a
  | _ -> user_err_loc 
  (loc, "", str "Variable " ++ pr_id id ++ str " should be bound to a tactic.")

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
  | ByNotation (loc,s,_) -> loc

let destIndRef = function IndRef ind -> ind | _ -> failwith "destIndRef"

let intern_inductive_or_by_notation = function
  | AN r -> Nametab.inductive_of_reference r
  | ByNotation (loc,ntn,sc) ->
      destIndRef (Notation.interp_notation_as_global_reference loc
        (function IndRef ind -> true | _ -> false) ntn sc)

let intern_inductive ist = function
  | AN (Ident (loc,id)) when find_var id ist -> ArgVar (loc,id)
  | r -> ArgArg (intern_inductive_or_by_notation r)

let intern_global_reference ist = function
  | Ident (loc,id) when find_var id ist -> ArgVar (loc,id)
  | r -> 
      let loc,_ as lqid = qualid_of_reference r in
      try ArgArg (loc,locate_global_with_alias lqid)
      with Not_found -> 
	error_global_not_found_loc lqid

let intern_ltac_variable ist = function
  | Ident (loc,id) ->
      if find_ltacvar id ist then
	(* A local variable of any type *)
	ArgVar (loc,id)
      else
      (* A recursive variable *)
      ArgArg (loc,find_recvar id ist)
  | _ ->
      raise Not_found

let intern_constr_reference strict ist = function
  | Ident (_,id) when (not strict & find_hyp id ist) or find_ctxvar id ist ->
      RVar (dloc,id), None
  | r ->
      let loc,_ as lqid = qualid_of_reference r in
      RRef (loc,locate_global_with_alias lqid), if strict then None else Some (CRef r)

let intern_move_location ist = function
  | MoveAfter id -> MoveAfter (intern_hyp_or_metaid ist id)
  | MoveBefore id -> MoveBefore (intern_hyp_or_metaid ist id)
  | MoveToEnd toleft as x -> x

(* Internalize an isolated reference in position of tactic *)

let intern_isolated_global_tactic_reference r =
  let (loc,qid) = qualid_of_reference r in
  try TacCall (loc,ArgArg (loc,locate_tactic qid),[])
  with Not_found ->
  match r with
  | Ident (_,id) -> Tacexp (lookup_atomic id)
  | _ -> raise Not_found

let intern_isolated_tactic_reference strict ist r =
  (* An ltac reference *)
  try Reference (intern_ltac_variable ist r)
  with Not_found ->
  (* A global tactic *)
  try intern_isolated_global_tactic_reference r
  with Not_found ->
  (* Tolerance for compatibility, allow not to use "constr:" *)
  try ConstrMayEval (ConstrTerm (intern_constr_reference strict ist r))
  with Not_found ->
  (* Reference not found *)
  error_global_not_found_loc (qualid_of_reference r)

(* Internalize an applied tactic reference *)

let intern_applied_global_tactic_reference r =
  let (loc,qid) = qualid_of_reference r in
  ArgArg (loc,locate_tactic qid)

let intern_applied_tactic_reference ist r =
  (* An ltac reference *)
  try intern_ltac_variable ist r
  with Not_found ->
  (* A global tactic *)
  try intern_applied_global_tactic_reference r
  with Not_found ->
  (* Reference not found *)
  error_global_not_found_loc (qualid_of_reference r)

(* Intern a reference parsed in a non-tactic entry *)

let intern_non_tactic_reference strict ist r =
  (* An ltac reference *)
  try Reference (intern_ltac_variable ist r)
  with Not_found ->
  (* A constr reference *)
  try ConstrMayEval (ConstrTerm (intern_constr_reference strict ist r))
  with Not_found ->
  (* Tolerance for compatibility, allow not to use "ltac:" *)
  try intern_isolated_global_tactic_reference r
  with Not_found ->
  (* By convention, use IntroIdentifier for unbound ident, when not in a def *)
  match r with
  | Ident (loc,id) when not strict -> IntroPattern (loc,IntroIdentifier id)
  | _ ->
  (* Reference not found *)
  error_global_not_found_loc (qualid_of_reference r)

let intern_message_token ist = function
  | (MsgString _ | MsgInt _ as x) -> x
  | MsgIdent id -> MsgIdent (intern_hyp_or_metaid ist id)

let intern_message ist = List.map (intern_message_token ist)

let rec intern_intro_pattern lf ist = function
  | loc, IntroOrAndPattern l ->
      loc, IntroOrAndPattern (intern_or_and_intro_pattern lf ist l)
  | loc, IntroIdentifier id ->
      loc, IntroIdentifier (intern_ident lf ist id)
  | loc, IntroFresh id ->
      loc, IntroFresh (intern_ident lf ist id)
  | loc, (IntroWildcard | IntroAnonymous | IntroRewrite _)
      as x -> x

and intern_or_and_intro_pattern lf ist =
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
  let lqid = qualid_of_reference r in
  try locate_global_with_alias lqid
  with Not_found ->
  match r with 
  | Ident (loc,id) when not !strict_check -> VarRef id
  | _ -> error_global_not_found_loc lqid

let intern_evaluable_reference_or_by_notation = function
  | AN r -> evaluable_of_global_reference (interp_global_reference r)
  | ByNotation (loc,ntn,sc) ->
      evaluable_of_global_reference
      (Notation.interp_notation_as_global_reference loc
        (function ConstRef _ | VarRef _ -> true | _ -> false) ntn sc)

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

let intern_constr_with_occurrences ist (l,c) = (l,intern_constr ist c)

let intern_red_expr ist = function
  | Unfold l -> Unfold (List.map (intern_unfold ist) l)
  | Fold l -> Fold (List.map (intern_constr ist) l)
  | Cbv f -> Cbv (intern_flag ist f)
  | Lazy f -> Lazy (intern_flag ist f)
  | Pattern l -> Pattern (List.map (intern_constr_with_occurrences ist) l)
  | Simpl o -> Simpl (Option.map (intern_constr_with_occurrences ist) o)
  | (Red _ | Hnf | ExtraRedExpr _ | CbvVm as r ) -> r
  
let intern_in_hyp_as ist lf (id,ipat) =
  (intern_hyp_or_metaid ist id, Option.map (intern_intro_pattern lf ist) ipat)

let intern_hyp_list ist = List.map (intern_hyp_or_metaid ist)

let intern_inversion_strength lf ist = function
  | NonDepInversion (k,idl,ids) ->
      NonDepInversion (k,intern_hyp_list ist idl,
      Option.map (intern_intro_pattern lf ist) ids)
  | DepInversion (k,copt,ids) ->
      DepInversion (k, Option.map (intern_constr ist) copt,
      Option.map (intern_intro_pattern lf ist) ids)
  | InversionUsing (c,idl) ->
      InversionUsing (intern_constr ist c, intern_hyp_list ist idl)

(* Interprets an hypothesis name *)
let intern_hyp_location ist (((b,occs),id),hl) =
  (((b,List.map (intern_or_var ist) occs),intern_hyp_or_metaid ist id), hl)

(* Reads a pattern *)
let intern_pattern sigma env ?(as_type=false) lfun = function
  | Subterm (b,ido,pc) ->
      let ltacvars = (lfun,[]) in
      let (metas,pat) = intern_constr_pattern sigma env ~ltacvars pc in
      ido, metas, Subterm (b,ido,pat)
  | Term pc ->
      let ltacvars = (lfun,[]) in
      let (metas,pat) = intern_constr_pattern sigma env ~as_type ~ltacvars pc in
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
  | VRTactic _ | VFun _ | VVoid | VInteger _ | VConstr_context _
  | VIntroPattern _  | VRec _ | VList _ ->
      error "Only externing of terms is implemented."

let extern_request ch req gl la =
  output_string ch "<REQUEST req=\""; output_string ch req;
  output_string ch "\">\n";
  List.iter (pf_apply (extern_tacarg ch) gl) la;
  output_string ch "</REQUEST>\n"

let value_of_ident id = VIntroPattern (IntroIdentifier id)

let extend_values_with_bindings (ln,lm) lfun =
  let lnames = List.map (fun (id,id') ->(id,value_of_ident id')) ln in
  let lmatch = List.map (fun (id,c) -> (id,VConstr c)) lm in
  (* For compatibility, bound variables are visible only if no other
     binding of the same name exists *)
  lmatch@lfun@lnames

(* Reads the hypotheses of a "match goal" rule *)
let rec intern_match_goal_hyps sigma env lfun = function
  | (Hyp ((_,na) as locna,mp))::tl ->
      let ido, metas1, pat = intern_pattern sigma env ~as_type:true lfun mp in
      let lfun, metas2, hyps = intern_match_goal_hyps sigma env lfun tl in
      let lfun' = name_cons na (Option.List.cons ido lfun) in
      lfun', metas1@metas2, Hyp (locna,pat)::hyps
  | (Def ((_,na) as locna,mv,mp))::tl ->
      let ido, metas1, patv = intern_pattern sigma env ~as_type:false lfun mv in
      let ido', metas2, patt = intern_pattern sigma env ~as_type:true lfun mp in
      let lfun, metas3, hyps = intern_match_goal_hyps sigma env lfun tl in
      let lfun' = name_cons na (Option.List.cons ido' (Option.List.cons ido lfun)) in
      lfun', metas1@metas2@metas3, Def (locna,patv,patt)::hyps
  | [] -> lfun, [], []

(* Utilities *)
let extract_let_names lrc =
  List.fold_right 
    (fun ((loc,name),_) l ->
      if List.mem name l then
	user_err_loc
	  (loc, "glob_tactic", str "This variable is bound several times.");
      name::l)
    lrc []

let clause_app f = function
    { onhyps=None; concl_occs=nl } ->
      { onhyps=None; concl_occs=nl }
  | { onhyps=Some l; concl_occs=nl } ->
      { onhyps=Some(List.map f l); concl_occs=nl}

(* Globalizes tactics : raw_tactic_expr -> glob_tactic_expr *)
let rec intern_atomic lf ist x =
  match (x:raw_atomic_tactic_expr) with 
  (* Basic tactics *)
  | TacIntroPattern l ->
      TacIntroPattern (List.map (intern_intro_pattern lf ist) l)
  | TacIntrosUntil hyp -> TacIntrosUntil (intern_quantified_hypothesis ist hyp)
  | TacIntroMove (ido,hto) ->
      TacIntroMove (Option.map (intern_ident lf ist) ido,
                    intern_move_location ist hto)
  | TacAssumption -> TacAssumption
  | TacExact c -> TacExact (intern_constr ist c)
  | TacExactNoCheck c -> TacExactNoCheck (intern_constr ist c)
  | TacVmCastNoCheck c -> TacVmCastNoCheck (intern_constr ist c)
  | TacApply (a,ev,cb,inhyp) ->
      TacApply (a,ev,List.map (intern_constr_with_bindings ist) cb,
                Option.map (intern_in_hyp_as ist lf) inhyp)
  | TacElim (ev,cb,cbo) ->
      TacElim (ev,intern_constr_with_bindings ist cb,
               Option.map (intern_constr_with_bindings ist) cbo)
  | TacElimType c -> TacElimType (intern_type ist c)
  | TacCase (ev,cb) -> TacCase (ev,intern_constr_with_bindings ist cb)
  | TacCaseType c -> TacCaseType (intern_type ist c)
  | TacFix (idopt,n) -> TacFix (Option.map (intern_ident lf ist) idopt,n)
  | TacMutualFix (b,id,n,l) ->
      let f (id,n,c) = (intern_ident lf ist id,n,intern_type ist c) in
      TacMutualFix (b,intern_ident lf ist id, n, List.map f l)
  | TacCofix idopt -> TacCofix (Option.map (intern_ident lf ist) idopt)
  | TacMutualCofix (b,id,l) ->
      let f (id,c) = (intern_ident lf ist id,intern_type ist c) in
      TacMutualCofix (b,intern_ident lf ist id, List.map f l)
  | TacCut c -> TacCut (intern_type ist c)
  | TacAssert (otac,ipat,c) ->
      TacAssert (Option.map (intern_tactic ist) otac,
                 Option.map (intern_intro_pattern lf ist) ipat,
                 intern_constr_gen (otac<>None) ist c)
  | TacGeneralize cl ->
      TacGeneralize (List.map (fun (c,na) ->
	               intern_constr_with_occurrences ist c,
                       intern_name lf ist na) cl)
  | TacGeneralizeDep c -> TacGeneralizeDep (intern_constr ist c)
  | TacLetTac (na,c,cls,b) ->
      let na = intern_name lf ist na in
      TacLetTac (na,intern_constr ist c,
                 (clause_app (intern_hyp_location ist) cls),b)

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
  | TacSimpleInductionDestruct (isrec,h) ->
      TacSimpleInductionDestruct (isrec,intern_quantified_hypothesis ist h)
  | TacInductionDestruct (ev,isrec,l) ->
      TacInductionDestruct (ev,isrec,List.map (fun (lc,cbo,(ipato,ipats),cls) ->
	      (List.map (intern_induction_arg ist) lc,
               Option.map (intern_constr_with_bindings ist) cbo,
               (Option.map (intern_intro_pattern lf ist) ipato,
	        Option.map (intern_intro_pattern lf ist) ipats),
               Option.map (clause_app (intern_hyp_location ist)) cls)) l)
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
    TacMove (dep,intern_hyp_or_metaid ist id1,intern_move_location ist id2)
  | TacRename l -> 
      TacRename (List.map (fun (id1,id2) -> 
			     intern_hyp_or_metaid ist id1, 
			     intern_hyp_or_metaid ist id2) l)
  | TacRevert l -> TacRevert (List.map (intern_hyp_or_metaid ist) l)
	
  (* Constructors *)
  | TacLeft (ev,bl) -> TacLeft (ev,intern_bindings ist bl)
  | TacRight (ev,bl) -> TacRight (ev,intern_bindings ist bl)
  | TacSplit (ev,b,bl) -> TacSplit (ev,b,intern_bindings ist bl)
  | TacAnyConstructor (ev,t) -> TacAnyConstructor (ev,Option.map (intern_tactic ist) t)
  | TacConstructor (ev,n,bl) -> TacConstructor (ev,n,intern_bindings ist bl)

  (* Conversion *)
  | TacReduce (r,cl) ->
      TacReduce (intern_red_expr ist r, clause_app (intern_hyp_location ist) cl)
  | TacChange (occl,c,cl) ->
      TacChange (Option.map (intern_constr_with_occurrences ist) occl,
        (if occl = None & (cl.onhyps = None or cl.onhyps = Some []) &
	    (cl.concl_occs = all_occurrences_expr or
	     cl.concl_occs = no_occurrences_expr)
         then intern_type ist c else intern_constr ist c),
	clause_app (intern_hyp_location ist) cl)

  (* Equivalence relations *)
  | TacReflexivity -> TacReflexivity
  | TacSymmetry idopt -> 
      TacSymmetry (clause_app (intern_hyp_location ist) idopt)
  | TacTransitivity c -> TacTransitivity (intern_constr ist c)

  (* Equality and inversion *)
  | TacRewrite (ev,l,cl,by) -> 
      TacRewrite 
	(ev, 
	List.map (fun (b,m,c) -> (b,m,intern_constr_with_bindings ist c)) l,
	clause_app (intern_hyp_location ist) cl,
	Option.map (intern_tactic ist) by)
  | TacInversion (inv,hyp) ->
      TacInversion (intern_inversion_strength lf ist inv,
        intern_quantified_hypothesis ist hyp)

  (* For extensions *)
  | TacExtend (loc,opn,l) ->
      let _ = lookup_tactic opn in
      TacExtend (adjust_loc loc,opn,List.map (intern_genarg ist) l)
  | TacAlias (loc,s,l,(dir,body)) ->
      let l = List.map (fun (id,a) -> (id,intern_genarg ist a)) l in
      TacAlias (loc,s,l,(dir,body))

and intern_tactic ist tac = (snd (intern_tactic_seq ist tac) : glob_tactic_expr)

and intern_tactic_seq ist = function
  | TacAtom (loc,t) ->
      let lf = ref ist.ltacvars in
      let t = intern_atomic lf ist t in
      !lf, TacAtom (adjust_loc loc, t)
  | TacFun tacfun -> ist.ltacvars, TacFun (intern_tactic_fun ist tacfun)
  | TacLetIn (isrec,l,u) ->
      let (l1,l2) = ist.ltacvars in
      let ist' = { ist with ltacvars = (extract_let_names l @ l1, l2) } in
      let l = List.map (fun (n,b) -> 
	  (n,intern_tacarg !strict_check (if isrec then ist' else ist) b)) l in
      ist.ltacvars, TacLetIn (isrec,l,intern_tactic ist' u)
  | TacMatchGoal (lz,lr,lmr) ->
      ist.ltacvars, TacMatchGoal(lz,lr, intern_match_rule ist lmr)
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
  | Reference r -> intern_non_tactic_reference strict ist r
  | IntroPattern ipat -> 
      let lf = ref([],[]) in (*How to know what names the intropattern binds?*)
      IntroPattern (intern_intro_pattern lf ist ipat)
  | Integer n -> Integer n
  | ConstrMayEval c -> ConstrMayEval (intern_constr_may_eval ist c)
  | MetaIdArg (loc,istac,s) ->
      (* $id can occur in Grammar tactic... *)
      let id = id_of_string s in
      if find_ltacvar id ist then
	if istac then Reference (ArgVar (adjust_loc loc,id))
	else ConstrMayEval (ConstrTerm (RVar (adjust_loc loc,id), None))
      else error_syntactic_metavariables_not_allowed loc
  | TacCall (loc,f,[]) -> intern_isolated_tactic_reference strict ist f
  | TacCall (loc,f,l) ->
      TacCall (loc,
        intern_applied_tactic_reference ist f,
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
      let lfun',metas1,hyps = intern_match_goal_hyps sigma env lfun rl in
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
  | IdentArgType b ->
      let lf = ref ([],[]) in
      in_gen (globwit_ident_gen b) 
	(intern_ident lf ist (out_gen (rawwit_ident_gen b) x))
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
  | Subterm (b,ido,pc) -> Subterm (b,ido,eval_pattern lfun pc)
  | Term pc -> Term (eval_pattern lfun pc)

(* Reads the hypotheses of a Match Context rule *)
let cons_and_check_name id l =
  if List.mem id l then
    user_err_loc (dloc,"read_match_goal_hyps",
      strbrk ("Hypothesis pattern-matching variable "^(string_of_id id)^
      " used twice in the same pattern."))
  else id::l

let rec read_match_goal_hyps lfun lidh = function
  | (Hyp ((loc,na) as locna,mp))::tl ->
      let lidh' = name_fold cons_and_check_name na lidh in
      Hyp (locna,read_pattern lfun mp)::
	(read_match_goal_hyps lfun lidh' tl)
  | (Def ((loc,na) as locna,mv,mp))::tl ->
      let lidh' = name_fold cons_and_check_name na lidh in
      Def (locna,read_pattern lfun mv, read_pattern lfun mp)::
	(read_match_goal_hyps lfun lidh' tl)
  | [] -> []

(* Reads the rules of a Match Context or a Match *)
let rec read_match_rule lfun = function
  | (All tc)::tl -> (All tc)::(read_match_rule lfun tl)
  | (Pat (rl,mp,tc))::tl ->
      Pat (read_match_goal_hyps lfun [] rl, read_pattern lfun mp,tc)
      :: read_match_rule lfun tl
  | [] -> []

(* For Match Context and Match *)
exception Not_coherent_metas
exception Eval_fail of std_ppcmds

let is_match_catchable = function
  | PatternMatchingFailure | Eval_fail _ -> true
  | e -> Logic.catchable_exception e

(* Verifies if the matched list is coherent with respect to lcm *)
(* While non-linear matching is modulo eq_constr in matches, merge of *)
(* different instances of the same metavars is here modulo conversion... *)
let verify_metas_coherence gl (ln1,lcm) (ln,lm) =
  let rec aux = function
  | (num,csr)::tl ->
    if (List.for_all (fun (a,b) -> a<>num or pf_conv_x gl b csr) lcm) then
      (num,csr)::aux tl
    else
      raise Not_coherent_metas
  | [] -> lcm in
  (ln@ln1,aux lm)

(* Tries to match one hypothesis pattern with a list of hypotheses *)
let apply_one_mhyp_context ist env gl lmatch (hypname,patv,pat) lhyps =
  let get_id_couple id = function
    | Name idpat -> [idpat,VConstr (mkVar id)]
    | Anonymous -> [] in
  let match_pat lmatch hyp pat =
    match pat with
    | Term t ->
        let lmeta = extended_matches t hyp in
        (try
            let lmeta = verify_metas_coherence gl lmatch lmeta in
            ([],lmeta,(fun () -> raise PatternMatchingFailure))
          with
            | Not_coherent_metas -> raise PatternMatchingFailure);
    | Subterm (b,ic,t) ->
        let rec match_next_pattern find_next () =
          let (lmeta,ctxt,find_next') = find_next () in
          try 
            let lmeta = verify_metas_coherence gl lmatch lmeta in
            (give_context ctxt ic,lmeta,match_next_pattern find_next')
          with
            | Not_coherent_metas -> match_next_pattern find_next' () in
        match_next_pattern(fun () -> match_subterm_gen b t hyp) () in
  let rec apply_one_mhyp_context_rec = function
    | (id,b,hyp as hd)::tl ->
	(match patv with
	| None ->
            let rec match_next_pattern find_next () =
              try
                let (ids, lmeta, find_next') = find_next () in
		(get_id_couple id hypname@ids, lmeta, hd, 
                 match_next_pattern find_next')
              with
                | PatternMatchingFailure -> apply_one_mhyp_context_rec tl in
            match_next_pattern (fun () -> match_pat lmatch hyp pat) ()
	| Some patv -> 
	    match b with
	    | Some body -> 
                let rec match_next_pattern_in_body next_in_body () =
                  try
                    let (ids,lmeta,next_in_body') = next_in_body() in
                    let rec match_next_pattern_in_typ next_in_typ () =
                      try
                        let (ids',lmeta',next_in_typ') = next_in_typ() in
		        (get_id_couple id hypname@ids@ids', lmeta', hd, 
                         match_next_pattern_in_typ next_in_typ')
                      with
                        | PatternMatchingFailure ->
                            match_next_pattern_in_body next_in_body' () in
                    match_next_pattern_in_typ 
                      (fun () -> match_pat lmeta hyp pat) ()
                  with PatternMatchingFailure -> apply_one_mhyp_context_rec tl
                in
                match_next_pattern_in_body 
                  (fun () -> match_pat lmatch body patv) ()
            | None -> apply_one_mhyp_context_rec tl)
    | [] ->
        db_hyp_pattern_failure ist.debug env (hypname,pat);
        raise PatternMatchingFailure
  in
    apply_one_mhyp_context_rec lhyps

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
   strbrk " is bound to" ++ spc () ++ pr_value env v ++ spc () ++ 
   strbrk "which cannot be coerced to " ++ str s ++ str".")

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

let interp_intro_pattern_var loc ist env id =
  try try_interp_ltac_var (coerce_to_intro_pattern env) ist (Some env) (loc,id)
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
  with Not_found ->
    user_err_loc(fst locid,"interp_int",
      str "Unbound variable "  ++ pr_id (snd locid) ++ str".")

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
  else user_err_loc (loc,"eval_variable",pr_id id ++ str " not found.")

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
	  error ("Hypothesis "^(string_of_id hyp)^" occurs twice.");
	(hyp,l)::(check (hyp::acc) rest)
    | [] -> []
  in (l,check [] occl)

let interp_move_location ist gl = function
  | MoveAfter id -> MoveAfter (interp_hyp ist gl id)
  | MoveBefore id -> MoveBefore (interp_hyp ist gl id)
  | MoveToEnd toleft as x -> x

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
let interp_occurrences ist (b,occs) =
  (b,interp_int_or_var_list ist occs)

let interp_hyp_location ist gl ((occs,id),hl) =
  ((interp_occurrences ist occs,interp_hyp ist gl id),hl)

let interp_clause ist gl { onhyps=ol; concl_occs=occs } =
  { onhyps=Option.map(List.map (interp_hyp_location ist gl)) ol;
    concl_occs=interp_occurrences ist occs }

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
let rec intropattern_ids (loc,pat) = match pat with
  | IntroIdentifier id -> [id]
  | IntroOrAndPattern ll -> 
      List.flatten (List.map intropattern_ids (List.flatten ll))
  | IntroWildcard | IntroAnonymous | IntroFresh _ | IntroRewrite _ -> []

let rec extract_ids ids = function
  | (id,VIntroPattern ipat)::tl when not (List.mem id ids) ->
      intropattern_ids (dloc,ipat) @ extract_ids ids tl
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
	  let _,(const,_,_,_) = cook_proof ignore in 
	  delete_current_proof (); const.const_entry_body
	with e when Logic.catchable_exception e -> 
	  delete_current_proof();
	  raise Exit
      end
  | _ -> raise Exit

let solve_remaining_evars env initial_sigma evd c =
  let evdref = ref (Typeclasses.resolve_typeclasses ~fail:true env evd) in
  let rec proc_rec c =
    match kind_of_term (Reductionops.whd_evar ( !evdref) c) with
      | Evar (ev,args as k) when not (Evd.mem initial_sigma ev) ->
            let (loc,src) = evar_source ev !evdref in
	    let sigma =  !evdref in
	    let evi = Evd.find sigma ev in
	    (try 
	      let c = solvable_by_tactic env evi k src in
	      evdref := Evd.define ev c !evdref;
	      c
	    with Exit ->
	      Pretype_errors.error_unsolvable_implicit loc env sigma evi src None)
      | _ -> map_constr proc_rec c      
  in
  proc_rec (Evarutil.nf_isevar !evdref c)

let interp_gen kind ist sigma env (c,ce) =
  let (ltacvars,unbndltacvars as vars) = constr_list ist env in
  let typs = retype_list sigma env ltacvars in
  let c = match ce with
  | None -> c
    (* If at toplevel (ce<>None), the error can be due to an incorrect
       context at globalization time: we retype with the now known
       intros/lettac/inversion hypothesis names *)
  | Some c ->
      let ltacdata = (List.map fst ltacvars,unbndltacvars) in
      intern_gen (kind = IsType) ~ltacvars:ltacdata sigma env c in
  let trace = push_trace (dloc,LtacConstrInterp (c,vars)) ist.trace in
  catch_error trace (understand_ltac sigma env (typs,unbndltacvars) kind) c

(* Interprets a constr and solve remaining evars with default tactic *)
let interp_econstr kind ist sigma env cc =
  let evars,c = interp_gen kind ist sigma env cc in
  let csr = solve_remaining_evars env sigma evars c in
  db_constr ist.debug env csr;
  csr

(* Interprets an open constr *)
let interp_open_constr ccl ist sigma env cc =
  let evd,c = interp_gen (OfType ccl) ist sigma env cc in
  ( evd,c)

let interp_open_type ccl ist sigma env cc =
  let evd,c = interp_gen IsType ist sigma env cc in
  ( evd,c)

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

let pf_interp_constr_in_compound_list inj_fun dest_fun interp_fun ist gl l =
  let env = pf_env gl in
  let try_expand_ltac_var x =
    try match dest_fun x with
    | RVar (_,id), _ ->
	List.map inj_fun (constr_list_of_VList env (List.assoc id ist.lfun))
    | _ ->
	raise Not_found
    with Not_found ->
      (*all of dest_fun, List.assoc, constr_list_of_VList may raise Not_found*)
      [interp_fun ist gl x] in
  List.flatten (List.map try_expand_ltac_var l)

let pf_interp_constr_list =
  pf_interp_constr_in_compound_list (fun x -> x) (fun x -> x)
    (fun ist gl -> interp_constr ist (project gl) (pf_env gl))

(*
let pf_interp_constr_list_as_list ist gl (c,_ as x) =
  match c with
    | RVar (_,id) ->
        (try constr_list_of_VList (pf_env gl) (List.assoc id ist.lfun)
        with Not_found -> [])
    | _ -> [interp_constr ist (project gl) (pf_env gl) x]

let pf_interp_constr_list ist gl l =
  List.flatten (List.map (pf_interp_constr_list_as_list ist gl) l)
*)

let inj_open c = (Evd.empty,c)

let pf_interp_open_constr_list =
  pf_interp_constr_in_compound_list inj_open (fun x -> x)
    (fun ist gl -> interp_open_constr None ist (project gl) (pf_env gl))

(*
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
*)

(* Interprets a type expression *)
let pf_interp_type ist gl =
  interp_type ist (project gl) (pf_env gl)

(* Interprets a reduction expression *)
let interp_unfold ist env (occs,qid) =
  (interp_occurrences ist occs,interp_evaluable ist env qid)

let interp_flag ist env red =
  { red with rConst = List.map (interp_evaluable ist env) red.rConst }

let interp_pattern ist sigma env (occs,c) = 
  (interp_occurrences ist occs, interp_constr ist sigma env c)

let pf_interp_constr_with_occurrences ist gl =
  interp_pattern ist (project gl) (pf_env gl)

let pf_interp_constr_with_occurrences_and_name_as_list = 
  pf_interp_constr_in_compound_list
    (fun c -> ((all_occurrences_expr,c),Anonymous))
    (function ((occs,c),Anonymous) when occs = all_occurrences_expr -> c 
      | _ -> raise Not_found)
    (fun ist gl (occ_c,na) ->
      (interp_pattern ist (project gl) (pf_env gl) occ_c,
       interp_fresh_name ist gl na))

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
	    str "Unbound context identifier" ++ pr_id s ++ str"."))
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
  | VIntroPattern ipat -> pr_intro_pattern (dloc,ipat)
  | VConstr_context c | VConstr c -> pr_constr c
  | VRec _ | VRTactic _ | VFun _ -> str "<tactic>"
  | VList _ -> str "<list>"

let rec interp_message_token ist = function
  | MsgString s -> str s
  | MsgInt n -> int n
  | MsgIdent (loc,id) ->
      let v =
	try List.assoc id ist.lfun
	with Not_found -> user_err_loc (loc,"",pr_id id ++ str" not found.") in
      message_of_value v

let rec interp_message_nl ist = function
  | [] -> mt()
  | l -> prlist_with_sep spc (interp_message_token ist) l ++ fnl()

let interp_message ist l =
  (* Force evaluation of interp_message_token so that potential errors 
     are raised now and not at printing time *)
  prlist (fun x -> spc () ++ x) (List.map (interp_message_token ist) l)

let rec interp_intro_pattern ist gl = function
  | loc, IntroOrAndPattern l ->
      loc, IntroOrAndPattern (interp_or_and_intro_pattern ist gl l)
  | loc, IntroIdentifier id ->
      loc, interp_intro_pattern_var loc ist (pf_env gl) id
  | loc, IntroFresh id ->
      loc, IntroFresh (interp_fresh_ident ist gl id)
  | loc, (IntroWildcard | IntroAnonymous | IntroRewrite _)
      as x -> x

and interp_or_and_intro_pattern ist gl =
  List.map (List.map (interp_intro_pattern ist gl))

let interp_in_hyp_as ist gl (id,ipat) =
  (interp_hyp ist gl id,Option.map (interp_intro_pattern ist gl) ipat)

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
  | TacFun (it,body) -> VFun (ist.trace,ist.lfun,it,body)
  | TacLetIn (true,l,u) -> interp_letrec ist gl l u
  | TacLetIn (false,l,u) -> interp_letin ist gl l u
  | TacMatchGoal (lz,lr,lmr) -> interp_match_goal ist gl lz lr lmr 
  | TacMatch (lz,c,lmr) -> interp_match ist gl lz c lmr
  | TacArg a -> interp_tacarg ist gl a
  (* Delayed evaluation *)
  | t -> VFun (ist.trace,ist.lfun,[],t)

  in check_for_interrupt (); 
    match ist.debug with
    | DebugOn lev ->
	debug_prompt lev gl tac (fun v -> value_interp {ist with debug=v})
    | _ -> value_interp ist

and eval_tactic ist = function
  | TacAtom (loc,t) ->
      fun gl ->
	let box = ref None in abstract_tactic_box := box;
	let call = LtacAtomCall (t,box) in
	let tac = (* catch error in the interpretation *)
	  catch_error (push_trace(dloc,call)ist.trace)
	    (interp_atomic ist gl) t	in
	(* catch error in the evaluation *)
	catch_error (push_trace(loc,call)ist.trace) tac gl
  | TacFun _ | TacLetIn _ -> assert false
  | TacMatchGoal _ | TacMatch _ -> assert false
  | TacId s -> tclIDTAC_MESSAGE (interp_message_nl ist s)
  | TacFail (n,s) -> tclFAIL (interp_int_or_var ist n) (interp_message ist s)
  | TacProgress tac -> tclPROGRESS (interp_tactic ist tac)
  | TacAbstract (tac,ido) ->
      fun gl -> Tactics.tclABSTRACT
        (Option.map (interp_ident ist gl) ido) (interp_tactic ist tac) gl
  | TacThen (t1,tf,t,tl) -> 
      tclTHENS3PARTS (interp_tactic ist t1)
	(Array.map (interp_tactic ist) tf) (interp_tactic ist t) (Array.map (interp_tactic ist) tl)
  | TacThens (t1,tl) -> tclTHENS (interp_tactic ist t1) (List.map (interp_tactic ist) tl)
  | TacDo (n,tac) -> tclDO (interp_int_or_var ist n) (interp_tactic ist tac)
  | TacTry tac -> tclTRY (interp_tactic ist tac)
  | TacInfo tac -> 
      let t = (interp_tactic ist tac) in
	tclINFO 
	  begin
	    match tac with
		TacAtom (_,_) -> t
	      | _ -> abstract_tactic_expr (TacArg (Tacexp tac)) t
	  end
  | TacRepeat tac -> tclREPEAT (interp_tactic ist tac)
  | TacOrelse (tac1,tac2) ->
        tclORELSE (interp_tactic ist tac1) (interp_tactic ist tac2)
  | TacFirst l -> tclFIRST (List.map (interp_tactic ist) l)
  | TacSolve l -> tclSOLVE (List.map (interp_tactic ist) l)
  | TacComplete tac -> tclCOMPLETE (interp_tactic ist tac)
  | TacArg a -> assert false

and force_vrec ist gl = function
  | VRec (lfun,body) -> val_interp {ist with lfun = !lfun} gl body
  | v -> v

and interp_ltac_reference loc' mustbetac ist gl = function
  | ArgVar (loc,id) ->
      let v = List.assoc id ist.lfun in
      let v = force_vrec ist gl v in
      let v = propagate_trace ist loc id v in
      if mustbetac then coerce_to_tactic loc id v else v
  | ArgArg (loc,r) ->
      let ids = extract_ids [] ist.lfun in
      let loc_info = ((if loc' = dloc then loc else loc'),LtacNameCall r) in
      let ist = 
        { lfun=[]; debug=ist.debug; avoid_ids=ids;
          trace = push_trace loc_info ist.trace } in
      val_interp ist gl (lookup r)

and interp_tacarg ist gl = function
  | TacVoid -> VVoid
  | Reference r -> interp_ltac_reference dloc false ist gl r
  | Integer n -> VInteger n
  | IntroPattern ipat -> VIntroPattern (snd (interp_intro_pattern ist gl ipat))
  | ConstrMayEval c -> VConstr (interp_constr_may_eval ist gl c)
  | MetaIdArg (loc,_,id) -> assert false
  | TacCall (loc,r,[]) -> interp_ltac_reference loc true ist gl r
  | TacCall (loc,f,l) ->
      let fv = interp_ltac_reference loc true ist gl f
      and largs = List.map (interp_tacarg ist gl) l in
      List.iter check_is_value largs;
      interp_app loc ist gl fv largs
  | TacExternal (loc,com,req,la) ->
      interp_external loc ist gl com req (List.map (interp_tacarg ist gl) la)
  | TacFreshId l -> 
      let id = interp_fresh_id ist gl l in
      VIntroPattern (IntroIdentifier id)
  | Tacexp t -> val_interp ist gl t
  | TacDynamic(_,t) ->
      let tg = (tag t) in
      if tg = "tactic" then
        val_interp ist gl (tactic_out t ist)
      else if tg = "value" then
        value_out t
      else if tg = "constr" then
        VConstr (constr_out t)
      else
        anomaly_loc (dloc, "Tacinterp.val_interp",
          (str "Unknown dynamic: <" ++ str (Dyn.tag t) ++ str ">"))

(* Interprets an application node *)
and interp_app loc ist gl fv largs =
  match fv with
      (* if var=[] this means that evaluation of body has been delayed
         by val_interp, so it is not a tactic that expects arguments.
         Otherwise Ltac goes into an infinite loop (val_interp puts
         a VFun back on body, and then interp_app is called again...) *)
    | VFun(trace,olfun,(_::_ as var),body) ->
      let (newlfun,lvar,lval)=head_with_value (var,largs) in
      if lvar=[] then
	let v = 
	  try
	    catch_error trace
	      (val_interp { ist with lfun=newlfun@olfun; trace=trace } gl) body
	  with e ->
            debugging_exception_step ist false e (fun () -> str "evaluation");
	    raise e in
        debugging_step ist (fun () ->
	  str "evaluation returns" ++ fnl() ++ pr_value (Some (pf_env gl)) v);
        if lval=[] then v else interp_app loc ist gl v lval
      else
        VFun(trace,newlfun@olfun,lvar,body)
    | _ ->
	user_err_loc (loc, "Tacinterp.interp_app",
          (str"Illegal tactic application."))

(* Gives the tactic corresponding to the tactic value *)
and tactic_of_value ist vle g =
  match vle with
  | VRTactic res -> res
  | VFun (trace,lfun,[],t) ->
      let tac = eval_tactic {ist with lfun=lfun; trace=trace} t in
      catch_error trace tac g
  | VFun _ -> error "A fully applied tactic is expected."
  | _ -> raise NotTactic

(* Evaluation with FailError catching *)
and eval_with_fail ist is_lazy goal tac =
  try
    (match val_interp ist goal tac with
    | VFun (trace,lfun,[],t) when not is_lazy ->
	let tac = eval_tactic {ist with lfun=lfun; trace=trace} t in
	VRTactic (catch_error trace tac goal)
    | a -> a)
  with
    | FailError (0,s) | Stdpp.Exc_located(_, FailError (0,s)) 
    | Stdpp.Exc_located(_,LtacLocated (_,FailError (0,s))) ->
	raise (Eval_fail s)
    | FailError (lvl,s) -> raise (FailError (lvl - 1, s))
    | Stdpp.Exc_located(s,FailError (lvl,s')) ->
	raise (Stdpp.Exc_located(s,FailError (lvl - 1, s')))
    | Stdpp.Exc_located(s,LtacLocated (s'',FailError (lvl,s'))) ->
	raise (Stdpp.Exc_located(s,LtacLocated (s'',FailError (lvl - 1, s'))))

(* Interprets the clauses of a recursive LetIn *)
and interp_letrec ist gl llc u =
  let lref = ref ist.lfun in
  let lve = list_map_left (fun ((_,id),b) -> (id,VRec (lref,TacArg b))) llc in
  lref := lve@ist.lfun;
  let ist = { ist with lfun = lve@ist.lfun } in
  val_interp ist gl u

(* Interprets the clauses of a LetIn *)
and interp_letin ist gl llc u =
  let lve = list_map_left (fun ((_,id),body) ->
    let v = interp_tacarg ist gl body in check_is_value v; (id,v)) llc in
  let ist = { ist with lfun = lve@ist.lfun } in
  val_interp ist gl u

(* Interprets the Match Context expressions *)
and interp_match_goal ist goal lz lr lmr =
  let hyps = pf_hyps goal in
  let hyps = if lr then List.rev hyps else hyps in
  let concl = pf_concl goal in
  let env = pf_env goal in
  let rec apply_goal_sub app ist (id,c) csr mt mhyps hyps =
    let rec match_next_pattern find_next () =
      let (lgoal,ctxt,find_next') = find_next () in
      let lctxt = give_context ctxt id in
      try apply_hyps_context ist env lz goal mt lctxt lgoal mhyps hyps
      with e when is_match_catchable e -> match_next_pattern find_next' () in
    match_next_pattern (fun () -> match_subterm_gen app c csr) () in
  let rec apply_match_goal ist env goal nrs lex lpt = 
    begin
      if lex<>[] then db_pattern_rule ist.debug nrs (List.hd lex);
      match lpt with
	| (All t)::tl ->
	    begin
              db_mc_pattern_success ist.debug;
              try eval_with_fail ist lz goal t
              with e when is_match_catchable e ->
		apply_match_goal ist env goal (nrs+1) (List.tl lex) tl
	    end
	| (Pat (mhyps,mgoal,mt))::tl ->
            let mhyps = List.rev mhyps (* Sens naturel *) in
	    (match mgoal with
             | Term mg ->
		 (try
		     let lmatch = extended_matches mg concl in
		     db_matched_concl ist.debug env concl;
		     apply_hyps_context ist env lz goal mt [] lmatch mhyps hyps
		   with e when is_match_catchable e ->
		     (match e with
		       | PatternMatchingFailure -> db_matching_failure ist.debug
		       | Eval_fail s -> db_eval_failure ist.debug s
		       | _ -> db_logic_failure ist.debug e);
		     apply_match_goal ist env goal (nrs+1) (List.tl lex) tl)
	     | Subterm (b,id,mg) ->
		 (try apply_goal_sub b ist (id,mg) concl mt mhyps hyps
		   with
		     | PatternMatchingFailure ->
			 apply_match_goal ist env goal (nrs+1) (List.tl lex) tl))
	| _ ->
	    errorlabstrm "Tacinterp.apply_match_goal"
              (v 0 (str "No matching clauses for match goal" ++
		      (if ist.debug=DebugOff then
			 fnl() ++ str "(use \"Set Ltac Debug\" for more info)"
		       else mt()) ++ str"."))
    end in
    apply_match_goal ist env goal 0 lmr
      (read_match_rule (fst (constr_list ist env)) lmr)

(* Tries to match the hypotheses in a Match Context *)
and apply_hyps_context ist env lz goal mt lctxt lgmatch mhyps hyps =
  let rec apply_hyps_context_rec lfun lmatch lhyps_rest = function
    | hyp_pat::tl ->
	let (hypname, _, _ as hyp_pat) =
	  match hyp_pat with
	  | Hyp ((_,hypname),mhyp) -> hypname,  None, mhyp
	  | Def ((_,hypname),mbod,mhyp) -> hypname, Some mbod, mhyp
	in
        let rec match_next_pattern find_next =
          let (lids,lm,hyp_match,find_next') = find_next () in
          db_matched_hyp ist.debug (pf_env goal) hyp_match hypname;
	  try
            let id_match = pi1 hyp_match in
            let nextlhyps = list_remove_assoc_in_triple id_match lhyps_rest in
            apply_hyps_context_rec (lfun@lids) lm nextlhyps tl
          with e when is_match_catchable e -> 
	    match_next_pattern find_next' in
        let init_match_pattern () =
          apply_one_mhyp_context ist env goal lmatch hyp_pat lhyps_rest in
        match_next_pattern init_match_pattern
    | [] ->
        let lfun = extend_values_with_bindings lmatch (lfun@ist.lfun) in
        db_mc_pattern_success ist.debug;
        eval_with_fail {ist with lfun=lfun} lz goal mt
  in
  apply_hyps_context_rec lctxt lgmatch hyps mhyps

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
  | IdentArgType b ->
      in_gen (wit_ident_gen b)
        (interp_fresh_ident ist gl (out_gen (globwit_ident_gen b) x))
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
      in_gen (wit_open_constr_gen casted) 
        (pf_interp_open_constr casted ist gl 
          (snd (out_gen (globwit_open_constr_gen casted) x)))
  | ConstrWithBindingsArgType ->
      in_gen wit_constr_with_bindings
        (interp_constr_with_bindings ist gl (out_gen globwit_constr_with_bindings x))
  | BindingsArgType ->
      in_gen wit_bindings
        (interp_bindings ist gl (out_gen globwit_bindings x))
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
          in_gen (wit_tactic n)
	    (TacArg(valueIn(val_interp ist gl (out_gen (globwit_tactic n) x))))
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
  let rec apply_match_subterm app ist (id,c) csr mt =
    let rec match_next_pattern find_next () =
      let (lmatch,ctxt,find_next') = find_next () in
      let lctxt = give_context ctxt id in
      let lfun = extend_values_with_bindings lmatch (lctxt@ist.lfun) in
      try eval_with_fail {ist with lfun=lfun} lz g mt
      with e when is_match_catchable e ->
        match_next_pattern find_next' () in
    match_next_pattern (fun () -> match_subterm_gen app c csr) () in
  let rec apply_match ist csr = function
    | (All t)::_ ->
        (try eval_with_fail ist lz g t
         with e when is_match_catchable e -> apply_match ist csr [])
    | (Pat ([],Term c,mt))::tl ->
        (try
            let lmatch = 
              try extended_matches c csr
              with e ->
                debugging_exception_step ist false e (fun () ->
                  str "matching with pattern" ++ fnl () ++
                  pr_constr_pattern_env (pf_env g) c);
                raise e in
            try
              let lfun = extend_values_with_bindings lmatch ist.lfun in
              eval_with_fail { ist with lfun=lfun } lz g mt
            with e ->
              debugging_exception_step ist false e (fun () ->
                str "rule body for pattern" ++
                pr_constr_pattern_env (pf_env g) c);
              raise e
         with e when is_match_catchable e ->
           debugging_step ist (fun () -> str "switching to the next rule");
           apply_match ist csr tl)

    | (Pat ([],Subterm (b,id,c),mt))::tl ->
        (try apply_match_subterm b ist (id,c) csr mt
         with PatternMatchingFailure -> apply_match ist csr tl)
    | _ ->
      errorlabstrm "Tacinterp.apply_match" (str
        "No matching clauses for match.") in
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
            | VRTactic _ -> str "VRTactic"
            | VFun (_,il,ul,b) ->
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
                    ul (mt()))
            | VVoid -> str "VVoid"
            | VInteger _ -> str "VInteger"
            | VConstr _ -> str "VConstr"
            | VIntroPattern _ -> str "VIntroPattern"
            | VConstr_context _ -> str "VConstrr_context"
            | VRec _ -> str "VRec"
            | VList _ -> str "VList") ++ str".")

(* Interprets tactic expressions : returns a "tactic" *)
and interp_tactic ist tac gl =
  try tactic_of_value ist (val_interp ist gl tac) gl
  with NotTactic -> errorlabstrm "" (str "Not a tactic.")

(* Interprets a primitive tactic *)
and interp_atomic ist gl = function
  (* Basic tactics *)
  | TacIntroPattern l ->
      h_intro_patterns (List.map (interp_intro_pattern ist gl) l)
  | TacIntrosUntil hyp ->
      h_intros_until (interp_quantified_hypothesis ist hyp)
  | TacIntroMove (ido,hto) ->
      h_intro_move (Option.map (interp_fresh_ident ist gl) ido)
                   (interp_move_location ist gl hto)
  | TacAssumption -> h_assumption
  | TacExact c -> h_exact (pf_interp_casted_constr ist gl c)
  | TacExactNoCheck c -> h_exact_no_check (pf_interp_constr ist gl c)
  | TacVmCastNoCheck c -> h_vm_cast_no_check (pf_interp_constr ist gl c)
  | TacApply (a,ev,cb,None) ->
      h_apply a ev (List.map (interp_open_constr_with_bindings ist gl) cb)
  | TacApply (a,ev,cb,Some cl) ->
      h_apply_in a ev (List.map (interp_open_constr_with_bindings ist gl) cb)
        (interp_in_hyp_as ist gl cl)
  | TacElim (ev,cb,cbo) ->
      h_elim ev (interp_constr_with_bindings ist gl cb)
                (Option.map (interp_constr_with_bindings ist gl) cbo)
  | TacElimType c -> h_elim_type (pf_interp_type ist gl c)
  | TacCase (ev,cb) -> h_case ev (interp_constr_with_bindings ist gl cb)
  | TacCaseType c -> h_case_type (pf_interp_type ist gl c)
  | TacFix (idopt,n) -> h_fix (Option.map (interp_fresh_ident ist gl) idopt) n
  | TacMutualFix (b,id,n,l) ->
      let f (id,n,c) = (interp_fresh_ident ist gl id,n,pf_interp_type ist gl c)
      in h_mutual_fix b (interp_fresh_ident ist gl id) n (List.map f l)
  | TacCofix idopt -> h_cofix (Option.map (interp_fresh_ident ist gl) idopt)
  | TacMutualCofix (b,id,l) ->
      let f (id,c) = (interp_fresh_ident ist gl id,pf_interp_type ist gl c) in
      h_mutual_cofix b (interp_fresh_ident ist gl id) (List.map f l)
  | TacCut c -> h_cut (pf_interp_type ist gl c)
  | TacAssert (t,ipat,c) ->
      let c = (if t=None then interp_constr else interp_type) ist (project gl) (pf_env gl) c in
      abstract_tactic (TacAssert (t,ipat,inj_open c))
        (Tactics.forward (Option.map (interp_tactic ist) t)
	  (Option.map (interp_intro_pattern ist gl) ipat) c)
  | TacGeneralize cl ->
      h_generalize_gen
        (pf_interp_constr_with_occurrences_and_name_as_list ist gl cl)
  | TacGeneralizeDep c -> h_generalize_dep (pf_interp_constr ist gl c)
  | TacLetTac (na,c,clp,b) ->
      let clp = interp_clause ist gl clp in
      h_let_tac b (interp_fresh_name ist gl na) (pf_interp_constr ist gl c) clp

  (* Automation tactics *)
  | TacTrivial (lems,l) -> 
      Auto.h_trivial (pf_interp_constr_list ist gl lems)
	(Option.map (List.map (interp_hint_base ist)) l)
  | TacAuto (n,lems,l) ->
      Auto.h_auto (Option.map (interp_int_or_var ist) n)
      (pf_interp_constr_list ist gl lems)
      (Option.map (List.map (interp_hint_base ist)) l)
  | TacAutoTDB n -> Dhyp.h_auto_tdb n
  | TacDestructHyp (b,id) -> Dhyp.h_destructHyp b (interp_hyp ist gl id)
  | TacDestructConcl -> Dhyp.h_destructConcl
  | TacSuperAuto (n,l,b1,b2) -> Auto.h_superauto n l b1 b2
  | TacDAuto (n,p,lems) ->
      Auto.h_dauto (Option.map (interp_int_or_var ist) n,p)
      (pf_interp_constr_list ist gl lems)

  (* Derived basic tactics *)
  | TacSimpleInductionDestruct (isrec,h) ->
      h_simple_induction_destruct isrec (interp_quantified_hypothesis ist h)
  | TacInductionDestruct (isrec,ev,l) ->
      h_induction_destruct ev isrec
      (List.map (fun (lc,cbo,(ipato,ipats),cls) ->
	(List.map (interp_induction_arg ist gl) lc,
         Option.map (interp_constr_with_bindings ist gl) cbo,
         (Option.map (interp_intro_pattern ist gl) ipato,
	  Option.map (interp_intro_pattern ist gl) ipats),
         Option.map (interp_clause ist gl) cls)) l)
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
  | TacClear (b,l) -> h_clear b (interp_hyp_list ist gl l)
  | TacClearBody l -> h_clear_body (interp_hyp_list ist gl l)
  | TacMove (dep,id1,id2) ->
      h_move dep (interp_hyp ist gl id1) (interp_move_location ist gl id2)
  | TacRename l ->
      h_rename (List.map (fun (id1,id2) -> 
			    interp_hyp ist gl id1, 
			    interp_fresh_ident ist gl (snd id2)) l)
  | TacRevert l -> h_revert (interp_hyp_list ist gl l)

  (* Constructors *)
  | TacLeft (ev,bl) -> h_left ev (interp_bindings ist gl bl)
  | TacRight (ev,bl) -> h_right ev (interp_bindings ist gl bl)
  | TacSplit (ev,_,bl) -> h_split ev (interp_bindings ist gl bl)
  | TacAnyConstructor (ev,t) ->
      abstract_tactic (TacAnyConstructor (ev,t))
        (Tactics.any_constructor ev (Option.map (interp_tactic ist) t))
  | TacConstructor (ev,n,bl) ->
      h_constructor ev (skip_metaid n) (interp_bindings ist gl bl)

  (* Conversion *)
  | TacReduce (r,cl) ->
      h_reduce (pf_interp_red_expr ist gl r) (interp_clause ist gl cl)
  | TacChange (occl,c,cl) ->
      h_change (Option.map (pf_interp_constr_with_occurrences ist gl) occl)
        (if occl = None & (cl.onhyps = None or cl.onhyps = Some []) &
	    (cl.concl_occs = all_occurrences_expr or
	     cl.concl_occs = no_occurrences_expr)
	 then pf_interp_type ist gl c 
	 else pf_interp_constr ist gl c)
        (interp_clause ist gl cl)

  (* Equivalence relations *)
  | TacReflexivity -> h_reflexivity
  | TacSymmetry c -> h_symmetry (interp_clause ist gl c)
  | TacTransitivity c -> h_transitivity (pf_interp_constr ist gl c)

  (* Equality and inversion *)
  | TacRewrite (ev,l,cl,by) -> 
      Equality.general_multi_multi_rewrite ev
	(List.map (fun (b,m,c) -> (b,m,interp_open_constr_with_bindings ist gl c)) l)
	(interp_clause ist gl cl)
	(Option.map (interp_tactic ist) by)
  | TacInversion (DepInversion (k,c,ids),hyp) ->
      Inv.dinv k (Option.map (pf_interp_constr ist gl) c)
        (Option.map (interp_intro_pattern ist gl) ids)
        (interp_declared_or_quantified_hypothesis ist gl hyp)
  | TacInversion (NonDepInversion (k,idl,ids),hyp) ->
      Inv.inv_clause k 
        (Option.map (interp_intro_pattern ist gl) ids)
        (interp_hyp_list ist gl idl)
        (interp_declared_or_quantified_hypothesis ist gl hyp)
  | TacInversion (InversionUsing (c,idl),hyp) ->
      Leminv.lemInv_clause (interp_declared_or_quantified_hypothesis ist gl hyp)
        (pf_interp_constr ist gl c)
        (interp_hyp_list ist gl idl)

  (* For extensions *)
  | TacExtend (loc,opn,l) ->
      let tac = lookup_tactic opn in
      let args = List.map (interp_genarg ist gl) l in
      abstract_extended_tactic opn args (tac args)
  | TacAlias (loc,s,l,(_,body)) -> fun gl ->
    let rec f x = match genarg_tag x with
    | IntArgType -> 
        VInteger (out_gen globwit_int x)
    | IntOrVarArgType ->
        mk_int_or_var_value ist (out_gen globwit_int_or_var x)
    | PreIdentArgType ->
	failwith "pre-identifiers cannot be bound"
    | IntroPatternArgType ->
	VIntroPattern 
	  (snd (interp_intro_pattern ist gl (out_gen globwit_intro_pattern x)))
    | IdentArgType b ->
        VIntroPattern 
	  (IntroIdentifier
              (interp_fresh_ident ist gl (out_gen (globwit_ident_gen b) x)))
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
	-> error "This generic type is not supported in alias."
        
    in
    let lfun = (List.map (fun (x,c) -> (x,f c)) l)@ist.lfun in
    let trace = push_trace (loc,LtacNotationCall s) ist.trace in
    interp_tactic { ist with lfun=lfun; trace=trace } body gl

let make_empty_glob_sign () =
  { ltacvars = ([],[]); ltacrecvars = []; 
    gsigma = Evd.empty; genv = Global.env() }

(* Initial call for interpretation *)
let interp_tac_gen lfun avoid_ids debug t gl = 
  interp_tactic { lfun=lfun; avoid_ids=avoid_ids; debug=debug; trace=[] } 
    (intern_tactic {
      ltacvars = (List.map fst lfun, []); ltacrecvars = [];
      gsigma = project gl; genv = pf_env gl } t) gl

let eval_tactic t gls =
  interp_tactic { lfun=[]; avoid_ids=[]; debug=get_debug(); trace=[] }
    t gls

let interp t = interp_tac_gen [] [] (get_debug()) t

let eval_ltac_constr gl t =
  interp_ltac_constr 
    { lfun=[]; avoid_ids=[]; debug=get_debug(); trace=[] } gl
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
    ppnl (str "Warning: The reference " ++ pr_global ref ++ str " is not " ++
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

let subst_constr_with_occurrences subst (l,c) = (l,subst_rawconstr subst c)

let subst_redexp subst = function
  | Unfold l -> Unfold (List.map (subst_unfold subst) l)
  | Fold l -> Fold (List.map (subst_rawconstr subst) l)
  | Cbv f -> Cbv (subst_flag subst f)
  | Lazy f -> Lazy (subst_flag subst f)
  | Pattern l -> Pattern (List.map (subst_constr_with_occurrences subst) l)
  | Simpl o -> Simpl (Option.map (subst_constr_with_occurrences subst) o)
  | (Red _ | Hnf | ExtraRedExpr _ | CbvVm as r) -> r

let subst_raw_may_eval subst = function
  | ConstrEval (r,c) -> ConstrEval (subst_redexp subst r,subst_rawconstr subst c)
  | ConstrContext (locid,c) -> ConstrContext (locid,subst_rawconstr subst c)
  | ConstrTypeOf c -> ConstrTypeOf (subst_rawconstr subst c)
  | ConstrTerm c -> ConstrTerm (subst_rawconstr subst c)

let subst_match_pattern subst = function
  | Subterm (b,ido,pc) -> Subterm (b,ido,subst_pattern subst pc)
  | Term pc -> Term (subst_pattern subst pc)

let rec subst_match_goal_hyps subst = function
  | Hyp (locs,mp) :: tl ->
      Hyp (locs,subst_match_pattern subst mp)
      :: subst_match_goal_hyps subst tl
  | Def (locs,mv,mp) :: tl ->
      Def (locs,subst_match_pattern subst mv, subst_match_pattern subst mp)
      :: subst_match_goal_hyps subst tl
  | [] -> []

let rec subst_atomic subst (t:glob_atomic_tactic_expr) = match t with
  (* Basic tactics *)
  | TacIntroPattern _ | TacIntrosUntil _ | TacIntroMove _ as x -> x
  | TacAssumption as x -> x
  | TacExact c -> TacExact (subst_rawconstr subst c)
  | TacExactNoCheck c -> TacExactNoCheck (subst_rawconstr subst c)
  | TacVmCastNoCheck c -> TacVmCastNoCheck (subst_rawconstr subst c)
  | TacApply (a,ev,cb,cl) ->
      TacApply (a,ev,List.map (subst_raw_with_bindings subst) cb,cl)
  | TacElim (ev,cb,cbo) ->
      TacElim (ev,subst_raw_with_bindings subst cb,
               Option.map (subst_raw_with_bindings subst) cbo)
  | TacElimType c -> TacElimType (subst_rawconstr subst c)
  | TacCase (ev,cb) -> TacCase (ev,subst_raw_with_bindings subst cb)
  | TacCaseType c -> TacCaseType (subst_rawconstr subst c)
  | TacFix (idopt,n) as x -> x
  | TacMutualFix (b,id,n,l) ->
      TacMutualFix(b,id,n,List.map (fun (id,n,c) -> (id,n,subst_rawconstr subst c)) l)
  | TacCofix idopt as x -> x
  | TacMutualCofix (b,id,l) ->
      TacMutualCofix (b,id, List.map (fun (id,c) -> (id,subst_rawconstr subst c)) l)
  | TacCut c -> TacCut (subst_rawconstr subst c)
  | TacAssert (b,na,c) ->
      TacAssert (Option.map (subst_tactic subst) b,na,subst_rawconstr subst c)
  | TacGeneralize cl ->
      TacGeneralize (List.map (on_fst (subst_constr_with_occurrences subst))cl)
  | TacGeneralizeDep c -> TacGeneralizeDep (subst_rawconstr subst c)
  | TacLetTac (id,c,clp,b) -> TacLetTac (id,subst_rawconstr subst c,clp,b)

  (* Automation tactics *)
  | TacTrivial (lems,l) -> TacTrivial (List.map (subst_rawconstr subst) lems,l)
  | TacAuto (n,lems,l) -> TacAuto (n,List.map (subst_rawconstr subst) lems,l)
  | TacAutoTDB n -> TacAutoTDB n
  | TacDestructHyp (b,id) -> TacDestructHyp(b,id)
  | TacDestructConcl -> TacDestructConcl
  | TacSuperAuto (n,l,b1,b2) -> TacSuperAuto (n,l,b1,b2)
  | TacDAuto (n,p,lems) -> TacDAuto (n,p,List.map (subst_rawconstr subst) lems)

  (* Derived basic tactics *)
  | TacSimpleInductionDestruct (isrec,h) as x -> x
  | TacInductionDestruct (isrec,ev,l) ->
      TacInductionDestruct (isrec,ev,List.map (fun (lc,cbo,ids,cls) ->
	List.map (subst_induction_arg subst) lc,
        Option.map (subst_raw_with_bindings subst) cbo, ids, cls) l)
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
  | TacRevert _ as x -> x

  (* Constructors *)
  | TacLeft (ev,bl) -> TacLeft (ev,subst_bindings subst bl)
  | TacRight (ev,bl) -> TacRight (ev,subst_bindings subst bl)
  | TacSplit (ev,b,bl) -> TacSplit (ev,b,subst_bindings subst bl)
  | TacAnyConstructor (ev,t) -> TacAnyConstructor (ev,Option.map (subst_tactic subst) t)
  | TacConstructor (ev,n,bl) -> TacConstructor (ev,n,subst_bindings subst bl)

  (* Conversion *)
  | TacReduce (r,cl) -> TacReduce (subst_redexp subst r, cl)
  | TacChange (occl,c,cl) ->
      TacChange (Option.map (subst_constr_with_occurrences subst) occl,
        subst_rawconstr subst c, cl)

  (* Equivalence relations *)
  | TacReflexivity | TacSymmetry _ as x -> x
  | TacTransitivity c -> TacTransitivity (subst_rawconstr subst c)

  (* Equality and inversion *)
  | TacRewrite (ev,l,cl,by) -> 
      TacRewrite (ev, 
		  List.map (fun (b,m,c) ->
			      b,m,subst_raw_with_bindings subst c) l,
		 cl,Option.map (subst_tactic subst) by)
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
  | TacLetIn (r,l,u) ->
      let l = List.map (fun (n,b) -> (n,subst_tacarg subst b)) l in
      TacLetIn (r,l,subst_tactic subst u)
  | TacMatchGoal (lz,lr,lmr) ->
      TacMatchGoal(lz,lr, subst_match_rule subst lmr)
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
  | MetaIdArg (_loc,_,_) -> assert false
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
      let hyps = subst_match_goal_hyps subst rl in
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
  | IdentArgType b -> 
      in_gen (globwit_ident_gen b) (out_gen (globwit_ident_gen b) x)
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

type tacdef_kind = | NewTac of identifier
		   | UpdateTac of ltac_constant

let load_md i ((sp,kn),defs) =
  let dp,_ = repr_path sp in
  let mp,dir,_ = repr_kn kn in
  List.iter (fun (id,t) -> 
    match id with
	NewTac id ->
	  let sp = Libnames.make_path dp id in
	  let kn = Names.make_kn mp dir (label_of_id id) in
	    Nametab.push_tactic (Until i) sp kn;
	    add (kn,t)
      | UpdateTac kn ->
	  mactab := Gmap.remove kn !mactab;
	  add (kn,t)) defs
    
let open_md i((sp,kn),defs) =
  let dp,_ = repr_path sp in
  let mp,dir,_ = repr_kn kn in
  List.iter (fun (id,t) -> 
    match id with
	NewTac id ->
	  let sp = Libnames.make_path dp id in
	  let kn = Names.make_kn mp dir (label_of_id id) in
	    Nametab.push_tactic (Exactly i) sp kn
      | UpdateTac kn -> 
	  let (path, id) = decode_kn kn in
	  let sp = Libnames.make_path path id in
	  Nametab.push_tactic (Exactly i) sp kn) defs

let cache_md x = load_md 1 x

let subst_kind subst id = 
  match id with
    | NewTac _ -> id
    | UpdateTac kn -> UpdateTac (Mod_subst.subst_kn subst kn)

let subst_md (_,subst,defs) =
  List.map (fun (id,t) -> (subst_kind subst id,subst_tactic subst t)) defs

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
   str "Ltac" ++ spc() ++ pr_qualid id ++ str " :=" ++ spc() ++
    Pptactic.pr_glob_tactic (Global.env ()) t
 with
  Not_found ->
   errorlabstrm "print_ltac"
    (pr_qualid id ++ spc() ++ str "is not a user defined tactic.")

open Libnames

(* Adds a definition for tactics in the table *)
let make_absolute_name ident repl =
  let loc = loc_of_reference ident in
  try 
    let id, kn = 
      if repl then None, Nametab.locate_tactic (snd (qualid_of_reference ident))
      else let id = Pcoq.coerce_global_to_id ident in
	     Some id, Lib.make_kn id 
    in
      if Gmap.mem kn !mactab then
	if repl then id, kn
	else
	  user_err_loc (loc,"Tacinterp.add_tacdef",
		       str "There is already an Ltac named " ++ pr_reference ident ++ str".")
      else if is_atomic_kn kn then 
	user_err_loc (loc,"Tacinterp.add_tacdef",
		     str "Reserved Ltac name " ++ pr_reference ident ++ str".")
      else id, kn
  with Not_found ->
    user_err_loc (loc,"Tacinterp.add_tacdef",
		 str "There is no Ltac named " ++ pr_reference ident ++ str".")

let add_tacdef isrec tacl =
  let rfun = List.map (fun (ident, b, _) -> make_absolute_name ident b) tacl in
  let ist =
    {(make_empty_glob_sign()) with ltacrecvars = 
	if isrec then list_map_filter
	  (function (Some id, qid) -> Some (id, qid) | (None, _) -> None) rfun 
	else []} in
  let gtacl =
    List.map2 (fun (_,b,def) (id, qid) ->
      let k = if b then UpdateTac qid else NewTac (Option.get id) in
      let t = Flags.with_option strict_check (intern_tactic ist) def in
	(k, t))
      tacl rfun in
  let id0 = fst (List.hd rfun) in
  let _ = match id0 with Some id0 -> ignore(Lib.add_leaf id0 (inMD gtacl))
    | _ -> Lib.add_anonymous_leaf (inMD gtacl) in
  List.iter
    (fun (id,b,_) -> 
      Flags.if_verbose msgnl (Libnames.pr_reference id ++ 
				 (if b then str " is redefined"
				   else str " is defined")))
    tacl

(***************************************************************************)
(* Other entry points *)

let glob_tactic x = intern_tactic (make_empty_glob_sign ()) x

let glob_tactic_env l env x = 
  Flags.with_option strict_check
  (intern_tactic
    { ltacvars = (l,[]); ltacrecvars = []; gsigma = Evd.empty; genv = env })
    x

let interp_redexp env sigma r = 
  let ist = { lfun=[]; avoid_ids=[]; debug=get_debug (); trace=[] } in
  let gist = {(make_empty_glob_sign ()) with genv = env; gsigma = sigma } in
  interp_red_expr ist sigma env (intern_red_expr gist r)

(***************************************************************************)
(* Embed tactics in raw or glob tactic expr *)

let globTacticIn t = TacArg (TacDynamic (dummy_loc,tactic_in t))
let tacticIn t = globTacticIn (fun ist -> glob_tactic (t ist))

let tacticOut = function
  | TacArg (TacDynamic (_,d)) ->
    if (tag d) = "tactic" then
      tactic_out d
    else
      anomalylabstrm "tacticOut" (str "Dynamic tag should be tactic")
  | ast ->
    anomalylabstrm "tacticOut"
      (str "Not a Dynamic ast: " (* ++ print_ast ast*) )

(***************************************************************************)
(* Backwarding recursive needs of tactic glob/interp/eval functions *)

let _ = Auto.set_extern_interp
  (fun l -> 
    let l = List.map (fun (id,c) -> (id,VConstr c)) l in
    interp_tactic {lfun=l;avoid_ids=[];debug=get_debug(); trace=[]})
let _ = Auto.set_extern_intern_tac 
  (fun l ->
    Flags.with_option strict_check
    (intern_tactic {(make_empty_glob_sign()) with ltacvars=(l,[])}))
let _ = Auto.set_extern_subst_tactic subst_tactic
let _ = Dhyp.set_extern_interp eval_tactic
let _ = Dhyp.set_extern_intern_tac
  (fun t -> intern_tactic (make_empty_glob_sign()) t)
