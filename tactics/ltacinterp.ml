(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(*arnaud: commenter le module en général aussi *)

open Tacexpr (*arnaud: probablement enlever les références à tacexpr qui restent*)
open Genarg
open Names
open Libnames (* arnaud: probablement garder comme ça et enlever les Libnames. *)
open Rawterm (* arnaud: probablement garder comme ça et enlever les Rawterm. *)
open Pp

(* Infix notation for Goal.bind *)
let (>>=) = Goal.bind

(* arnaud: à commenter un peu plus dans le sens de ce que c'est vraiment. A savoir les valeurs qui peuvent être dans des variables de tactique *)
(* Values for interpretation *)
type value =
  | VTactic of Util.loc * unit Proofview.tactic  (* For mixed ML/Ltac tactics (e.g. Tauto) *)
  | VFun of (Names.identifier * value) list * Names.identifier option list * Tacexpr.glob_tactic_expr
  | VVoid
  | VInteger of int
  | VIntroPattern of Genarg.intro_pattern_expr
  | VConstr of Term.constr (* arnaud: constr ou rawconstr ? *)
  | VConstr_context of Term.constr (* arnaud: contr ou rawconstr ? *)
  | VList of value list
  | VRec of value ref





(*** ***)
(* arnaud: partie pas certaine, probablement souvent temporaire *)

(* arnaud: très temporaire *)
(* Gives the state of debug *)
let get_debug () = Tactic_debug.DebugOff

let locate_error_in_file dir = function
  | Stdpp.Exc_located (loc,e) -> Util.Error_in_file ("",(true,dir,loc),e)
  | e -> Util.Error_in_file ("",(true,dir,Util.dummy_loc),e)

let error_syntactic_metavariables_not_allowed loc =
  Util.user_err_loc 
    (loc,"out_ident",
     str "Syntactic metavariables allowed only in quotations")

let skip_metaid = function
  | AI x -> x
  | MetaId (loc,_) -> error_syntactic_metavariables_not_allowed loc

(* Tactics table (TacExtend). *)

let tac_tab = Hashtbl.create 17

let add_tactic s t =
  if Hashtbl.mem tac_tab s then
    Util.errorlabstrm ("Refiner.add_tactic: ") 
      (str ("Cannot redeclare tactic "^s));
  Hashtbl.add tac_tab s t

let lookup_tactic s =
  try 
    Hashtbl.find tac_tab s
  with Not_found -> 
    Util.errorlabstrm "Refiner.lookup_tactic"
      (str"The tactic " ++ str s ++ str" is not installed")

let out_gen_expr tag ge = 
  ge >>= fun g ->
  Goal.return (Genarg.out_gen tag g)

(* arnaud: plutôt "contexte de généralisation je suppose" *)
(* Interpretation of extra generic arguments *)
type glob_sign = { 
  ltacvars : Names.identifier list * Names.identifier list;
     (* ltac variables and the subset of vars introduced by Intro/Let/... *)
  ltacrecvars : (Names.identifier * Nametab.ltac_constant) list;
     (* ltac recursive names *)
  gsigma : Evd.evar_map;
     (* arnaud: environnement pour typer les evars, pourquoi pas un defs ? *)
  genv : Environ.env }
     (* environement pour typer le reste, normal *)


(* arnaud: je comprends pas ça :( *)
(* Table of "pervasives" macros tactics (e.g. auto, simpl, etc.) *)
let atomic_mactab = ref Idmap.empty
let add_primitive_tactic s tac =
  let id = id_of_string s in
  atomic_mactab := Idmap.add id tac !atomic_mactab

let _ =
  let nocl = {onhyps=Some[];onconcl=true; concl_occs=[]} in
  List.iter
      (fun (s,t) -> add_primitive_tactic s (TacAtom(Util.dummy_loc,t)))
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

(* arnaud: / je comprends pas ça *)

let error_not_evaluable s =
  Util.errorlabstrm "evalref_of_ref" 
    (str "Cannot coerce" ++ spc ()  ++ s ++ spc () ++
     str "to an evaluable reference")



(* arnaud: recommenter peut-être ? *)
(* Signature for interpretation: val_interp and interpretation functions *)
type interp_sign =
    { lfun : (Names.identifier * value) list;
      avoid_ids : Names.identifier list; (* ids inherited from the call context
				      (needed to get fresh ids) *)
      debug : Tactic_debug.debug_info;
      last_loc : Util.loc }



type interp_genarg_type =
  (glob_sign -> raw_generic_argument -> glob_generic_argument) *
  (interp_sign -> glob_generic_argument -> 
    typed_generic_argument) *
  (Mod_subst.substitution -> glob_generic_argument -> glob_generic_argument)

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


(* To embed tactics *)
let ((tactic_in : (interp_sign -> raw_tactic_expr) -> Dyn.t),
     (tactic_out : Dyn.t -> (interp_sign -> raw_tactic_expr))) =
  Dyn.create "tactic"

let ((value_in : value -> Dyn.t),
     (value_out : Dyn.t -> value)) = Dyn.create "value"

let tacticIn t = TacArg (TacDynamic (Util.dummy_loc,tactic_in t))
let tacticOut = function
  | TacArg (TacDynamic (_,d)) ->
    if (Dyn.tag d) = "tactic" then
      tactic_out d
    else
      Util.anomalylabstrm "tacticOut" (str "Dynamic tag should be tactic")
  | ast ->
    Util.anomalylabstrm "tacticOut"
      (str "Not a Dynamic ast: " (* ++ print_ast ast*) )

let valueIn t = TacDynamic (Util.dummy_loc,value_in t)
let valueOut = function
  | TacDynamic (_,d) ->
    if (Dyn.tag d) = "value" then
      value_out d
    else
      Util.anomalylabstrm "valueOut" (str "Dynamic tag should be value")
  | ast ->
      Util.anomalylabstrm "valueOut" (str "Not a Dynamic ast: ")

(* To embed constr *)
let constrIn t = Topconstr.CDynamic (Util.dummy_loc,Pretyping.constr_in t)
let constrOut = function
  | Topconstr.CDynamic (_,d) ->
    if (Dyn.tag d) = "constr" then
      Pretyping.constr_out d
    else
      Util.anomalylabstrm "constrOut" (str "Dynamic tag should be constr")
  | ast ->
    Util.anomalylabstrm "constrOut" (str "Not a Dynamic ast")




(*****************)
(* Globalization *)
(*****************)
(* arnaud: globalization = jouer au binder ? *)

(* arnaud: Que veut dire ce truc ? *)
(* We have identifier <| global_reference <| constr *)








let find_ident id sign = 
  List.mem id (fst sign.ltacvars) or 
  List.mem id (Termops.ids_of_named_context (Environ.named_context sign.genv))

let find_recvar qid sign = List.assoc qid sign.ltacrecvars

(* a "var" is a ltac var or a var introduced by an intro tactic *)
let find_var id sign = List.mem id (fst sign.ltacvars)

(* a "ctxvar" is a var introduced by an intro tactic (Intro/LetTac/...) *)
let find_ctxvar id sign = List.mem id (snd sign.ltacvars)

(* a "ltacvar" is an ltac var (Let-In/Fun/...) *)
let find_ltacvar id sign = find_var id sign & not (find_ctxvar id sign)

let find_hyp id sign =
  List.mem id (Termops.ids_of_named_context (Environ.named_context sign.genv))

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
    (Termops.vars_of_env env) lfun

(* arnaud:
let get_current_context () =
    try Pfedit.get_current_goal_context ()
    with e when Logic.catchable_exception e -> 
      (Evd.empty, Global.env())
*)

let strict_check = ref false

let adjust_loc loc = if !strict_check then Util.dummy_loc else loc

(* Globalize a name which must be bound -- actually just check it is bound *)
let intern_hyp ist (loc,id as locid) =
  if not !strict_check then
    locid
  else if find_ident id ist then
    (Util.dummy_loc,id)
  else
    Pretype_errors.error_var_not_found_loc loc id

let intern_hyp_or_metaid ist id = intern_hyp ist (skip_metaid id)

let intern_or_var ist = function
  | Rawterm.ArgVar locid -> Rawterm.ArgVar (intern_hyp ist locid)
  | Rawterm.ArgArg _ as x -> x

let loc_of_by_notation f = function
  | AN c -> f c
  | ByNotation (loc,s) -> loc

let destIndRef = function Libnames.IndRef ind -> ind | _ -> failwith "destIndRef"

let intern_inductive_or_by_notation = function
  | AN r -> Nametab.inductive_of_reference r
  | ByNotation (loc,ntn) ->
      destIndRef (Notation.interp_notation_as_global_reference loc
        (function Libnames.IndRef ind -> true | _ -> false) ntn)

let intern_inductive ist = function
  | AN (Libnames.Ident (loc,id)) when find_var id ist -> Rawterm.ArgVar (loc,id)
  | r -> Rawterm.ArgArg (intern_inductive_or_by_notation r)

let intern_global_reference ist = function
  | Libnames.Ident (loc,id) when find_var id ist -> Rawterm.ArgVar (loc,id)
  | r -> 
      let loc,qid as lqid = Libnames.qualid_of_reference r in
      try Rawterm.ArgArg (loc,Syntax_def.locate_global_with_alias lqid)
      with Not_found -> 
	Nametab.error_global_not_found_loc loc qid

let intern_tac_ref ist = function
  | Libnames.Ident (loc,id) when find_ltacvar id ist -> Rawterm.ArgVar (loc,id)
  | Libnames.Ident (loc,id) ->
      Rawterm.ArgArg (loc,
         try find_recvar id ist 
         with Not_found -> Nametab.locate_tactic (Libnames.make_short_qualid id))
  | r -> 
      let (loc,qid) = Libnames.qualid_of_reference r in
      Rawterm.ArgArg (loc,Nametab.locate_tactic qid)

let intern_tactic_reference ist r =
  try intern_tac_ref ist r
  with Not_found -> 
    let (loc,qid) = qualid_of_reference r in
    Nametab.error_global_not_found_loc loc qid

let intern_constr_reference strict ist = function
  | Ident (_,id) when (not strict & find_hyp id ist) or find_ctxvar id ist ->
      RVar (Util.dummy_loc,id), None
  | r ->
      let loc,_ as lqid = qualid_of_reference r in
      RRef (loc,Syntax_def.locate_global_with_alias lqid), if strict then None else Some (Topconstr.CRef r)

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
              Nametab.error_global_not_found_loc loc qid)))

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
      NamedHyp ((*snd (intern_hyp ist (Util.dummy_loc,*)id(* ))*))
      
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
	ElimOnConstr (intern_constr ist (Topconstr.CRef (Ident (Util.dummy_loc,id))),NoBindings)
      else
	ElimOnIdent (loc,id)

let evaluable_of_global_reference = function
  | ConstRef c -> EvalConstRef c
  | VarRef c -> EvalVarRef c
  | r -> error_not_evaluable (Printer.pr_global r)

let short_name = function
  | AN (Ident (loc,id)) when not !strict_check -> Some (loc,id)
  | _ -> None

let interp_global_reference r =
  let loc,qid as lqid = qualid_of_reference r in
  try Syntax_def.locate_global_with_alias lqid
  with Not_found ->
  match r with 
  | Ident (loc,id) when not !strict_check -> VarRef id
  | _ -> Nametab.error_global_not_found_loc loc qid

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
  let c = Constrintern.intern_gen false ~allow_patvar:true ~ltacvars:(ltacvar,[])
                     sigma env c in
  Pattern.pattern_of_rawconstr c

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
  | VTactic _ | VFun _ | VVoid | VInteger _ | VConstr_context _
  | VIntroPattern _  | VRec _ | VList _ ->
     Util. error "Only externing of terms is implemented"

(* arnaud: à restaurer 
let extern_request ch req gl la =
  output_string ch "<REQUEST req=\""; output_string ch req;
  output_string ch "\">\n";
  List.iter (pf_apply (extern_tacarg ch) gl) la;
  output_string ch "</REQUEST>\n"
*)

(* Reads the hypotheses of a Match Context rule *)
let rec intern_match_context_hyps sigma env lfun = function
  | (Hyp ((_,na) as locna,mp))::tl ->
      let ido, metas1, pat = intern_pattern sigma env lfun mp in
      let lfun, metas2, hyps = intern_match_context_hyps sigma env lfun tl in
      let lfun' = Nameops.name_cons na (Option.List.cons ido lfun) in
      lfun', metas1@metas2, Hyp (locna,pat)::hyps
  | [] -> lfun, [], []

(* Utilities *)
let extract_names lrc =
  List.fold_right 
    (fun ((loc,name),_) l ->
      if List.mem name l then
	Util.user_err_loc
	  (loc, "intern_tactic", str "This variable is bound several times");
      name::l)
    lrc []

let extract_let_names lrc =
  List.fold_right 
    (fun ((loc,name),_,_) l ->
      if List.mem name l then
	Util.user_err_loc
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
      (match Dyn.tag t with
	| "tactic" | "value" | "constr" -> x
	| s -> Util.anomaly_loc (loc, "",
                 str "Unknown dynamic: <" ++ str s ++ str ">"))

(* Reads the rules of a Match Context or a Match *)
and intern_match_rule ist = function
  | (All tc)::tl ->
      All (intern_tactic ist tc) :: (intern_match_rule ist tl)
  | (Pat (rl,mp,tc))::tl ->
      let {ltacvars=(lfun,l2); gsigma=sigma; genv=env} = ist in
      let lfun',metas1,hyps = intern_match_context_hyps sigma env lfun rl in
      let ido,metas2,pat = intern_pattern sigma env lfun mp in
      let metas = Util.list_uniquize (metas1@metas2) in
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
      match Pcoq.tactic_genarg_level s with
      | Some n -> 
          (* Special treatment of tactic arguments *)
          in_gen (Pcoq.globwit_tactic n) (intern_tactic ist
	    (out_gen (Pcoq.rawwit_tactic n) x))
      | None ->
	  Util.anomaly "Ltacinterp.intern_genarg: ExtraArgType: todo: None"
          (* arnaud: cette primitive fait appel à un goal sigma dans ses
	     dépendences, je comprends pas bien ce que ça veut dire
	     lookup_genarg_glob s ist x *)





(* arnaud: à nettoyer, mais il faut probablement reporter les commentaires
           d'abord
(* arnaud: commenter il y a deux lignes il faut les piger *)
let find_ident id sign = 
    (* Has the name been introduced by a tactic function, or and intro
       (or similar) tactic. *)
  List.mem id (fst sign.ltacvars) or 
    (* or has it been introduced earlier, like as an hypothesis of the
       current goal (if the tactic is a single_tactic) *)
    (* arnaud: single_tactic changera sûrement de nom *)
  List.mem id (Termops.ids_of_named_context (Environ.named_context sign.genv))

(* arnaud: commenter plus clairement. C'est probablement le seul endroit
   où lf est utilisé, ist aussi peut-être ? Probablement pas pour ist*)
(* Globalize a name introduced by Intro/LetTac/... ; it is allowed to *)
(* be fresh in which case it is binding later on *)
let intern_ident lf ist id =
  (* We use identifier both for variables and new names; thus nothing to do *)
  if not (find_ident id ist) then lf:=(id::fst !lf,id::snd !lf);
  id

(* arnaud: à commenter *)
let rec intern_intro_pattern lf ist = function
  | IntroOrAndPattern l ->
      IntroOrAndPattern (intern_case_intro_pattern lf ist l)
  | IntroIdentifier id ->
      IntroIdentifier (intern_ident lf ist id)
  | IntroWildcard | IntroAnonymous | IntroFresh _ as x -> x

(*arnaud: à commenter *)
and intern_case_intro_pattern lf ist =
  List.map (List.map (intern_intro_pattern lf ist))

(* Globalizes tactics : raw_tactic_expr -> glob_tactic_expr *)
let rec intern_atomic lf ist x =
  match (x:raw_atomic_tactic_expr) with 
  | TacIntroPattern l ->
      TacIntroPattern (List.map (intern_intro_pattern lf ist) l)
  | TacIntroMove _ -> Util.anomaly "Ltacinterp.intern_atomic: todo:TacIntroMove"
  | _ -> Util.anomaly "Ltacinterp.intern_atomic: todo"

(* arnaud: à déplacer et restaurer, pas encore compris ce que c'était ce
   truc strict_check. *)
let adjust_loc loc = loc (*was: if !strict_check then Util.dummy_loc else loc*)

(* arnaud: à commenter *)
let intern_tactic_seq ist = function
  | TacAtom (loc,t) ->
      let lf = ref ist.ltacvars in
      let t = intern_atomic lf ist t in
      !lf, TacAtom (adjust_loc loc, t)
  | _ -> Util.anomaly "Ltacinterp.intern_tactic_seq: todo"

let intern_tactic ist tac = (snd (intern_tactic_seq ist tac) : glob_tactic_expr)

arnaud: /à nettoyer *)









(************* End globalization ************)











(******************)
(* Interpretation *)
(******************)

(* arnaud: déplacer ? *)
(* Displays a value *)
let rec pr_value env = function
  | VVoid -> str "()"
  | VInteger n -> int n
  | VIntroPattern ipat -> pr_intro_pattern ipat
  | VConstr c | VConstr_context c ->
      (match env with Some env -> Printer.pr_lconstr_env env c | _ -> str "a term")
  | (VTactic _ | VFun _ | VRec _) -> str "a tactic"
  | VList [] -> str "an empty list"
  | VList (a::_) ->
      str "a list (first element is " ++ pr_value env a ++ str")"
let error_ltac_variable loc id env v s =
   Util.user_err_loc (loc, "", str "Ltac variable " ++ Ppconstr.pr_id id ++ 
   str " is bound to" ++ spc () ++ pr_value env v ++ spc () ++ 
   str "which cannot be coerced to " ++ str s)

exception CannotCoerceTo of string

(* Raise Not_found if not in interpretation sign *)
let try_interp_ltac_var coerce ist env (loc,id) =
  let v = List.assoc id ist.lfun in
  try coerce v with CannotCoerceTo s -> error_ltac_variable loc id env v s

let interp_ltac_var coerce ist env locid =
  try try_interp_ltac_var coerce ist env locid
  with Not_found -> Util.anomaly "Detected as ltac var at interning time"


(* arnaud: à déplacer ?*)
(* For tactic_of_value *)
exception NotTactic

(* Gives the tactic corresponding to the tactic value *)
let tactic_of_value vle =
  match vle with
  | VTactic (loc,tac) -> tac (* arnaud:remettre les infos de location ?*)
  | VFun _ -> Util.error "A fully applied tactic is expected"
  | _ -> raise NotTactic

let is_variable env id =
  List.mem id (Termops.ids_of_named_context (Environ.named_context env))

(* Interprets an identifier which must be fresh *)
let coerce_to_ident fresh env = function
  | VIntroPattern (IntroIdentifier id) -> id
  | VConstr c when Term.isVar c & not (fresh & is_variable env (Term.destVar c)) ->
      (* We need it fresh for intro e.g. in "Tac H = clear H; intro H" *)
      Term.destVar c
  | v -> raise (CannotCoerceTo "a fresh identifier")

let interp_ident_gen fresh ist id =
  Goal.env >>= fun env ->
  Goal.return (
    try try_interp_ltac_var (coerce_to_ident fresh env) ist (Some env) (Util.dummy_loc,id)
  with Not_found -> id
  )

let interp_ident = interp_ident_gen false 
let interp_fresh_ident = interp_ident_gen true


let coerce_to_int = function
  | VInteger n -> n
  | v -> raise (CannotCoerceTo "an integer")

let interp_int ist locid =
  try try_interp_ltac_var coerce_to_int ist None locid
  with Not_found -> Util.user_err_loc(fst locid,"interp_int",str "Unbound variable")

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

let coerce_to_hyp env = function
  | VConstr c when Term.isVar c -> Term.destVar c
  | VIntroPattern (IntroIdentifier id) when is_variable env id -> id
  | _ -> raise (CannotCoerceTo "a variable")

(* Interprets a bound variable (especially an existing hypothesis) *)
let interp_hyp ist (loc,id as locid) =
  Goal.env >>= fun env ->
  Goal.return (
    (* Look first in lfun for a value coercible to a variable *)
    try try_interp_ltac_var (coerce_to_hyp env) ist (Some env) locid
    with Not_found -> 
      (* Then look if bound in the proof context at calling time *)
      if is_variable env id then id
      else Util.user_err_loc (loc,"eval_variable",Nameops.pr_id id ++ str " not found")
  )

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

let pf_interp_reference ist ov = (* arnaud: renommer avec "goal" à la place de "proof" ?*)
  Goal.env >>= fun env ->
  Goal.return (interp_reference ist env ov)


(* Quantified named or numbered hypothesis or hypothesis in context *)
(* (as in Inversion) *)
let coerce_to_decl_or_quant_hyp env = function
  | VInteger n -> AnonHyp n
  | v -> 
      try NamedHyp (coerce_to_hyp env v)
      with CannotCoerceTo _ -> 
	raise (CannotCoerceTo "a declared or quantified hypothesis")

let interp_declared_or_quantified_hypothesis ist = 
    function
  | AnonHyp n -> Goal.return (AnonHyp n)
  | NamedHyp id ->
      (* arnaud:let env = pf_env gl in *)
      Goal.env >>= fun env ->
      Goal.return (
	try try_interp_ltac_var 
	  (coerce_to_decl_or_quant_hyp env) ist (Some env) (Util.dummy_loc,id)
	with Not_found -> NamedHyp id
      )

let coerce_to_evaluable_ref env v =
  let ev = match v with
    | VConstr c when Term.isConst c -> EvalConstRef (Term.destConst c)
    | VConstr c when Term.isVar c -> EvalVarRef (Term.destVar c)
    | VIntroPattern (IntroIdentifier id) when List.mem id (Termops.ids_of_context env) 
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
       | _ -> error_not_evaluable (Nameops.pr_id id)
       with Not_found ->
       match r with
       | EvalConstRef _ -> r
       | _ -> Pretype_errors.error_var_not_found_loc loc id)
  | ArgArg (r,None) -> r
  | ArgVar locid -> 
      interp_ltac_var (coerce_to_evaluable_ref env) ist (Some env) locid


(* Interprets a reduction expression *)
let interp_unfold ist env (l,qid) =
  (interp_int_or_var_list ist l,interp_evaluable ist env qid)

let interp_flag ist env red =
  { red with rConst = List.map (interp_evaluable ist env) red.rConst }



let implicit_tactic = ref None

let declare_implicit_tactic tac = implicit_tactic := Some tac



let solvable_by_tactic env evi (ev,args) src = 
  match (!implicit_tactic, src) with
  | Some tac, (Evd.ImplicitArg _ | Evd.QuestionMark _)
      when 
	Environ.named_context_of_val evi.Evd.evar_hyps = 
	Environ.named_context env ->
      let id = id_of_string "H" in
	Util.anomaly "Ltacinterp.solvable_by_tactic: à restaurer"
	(* arnaud: à restaurer ?
      start_proof id (Local,Proof Lemma) evi.evar_hyps evi.evar_concl
	(fun _ _ -> ());
      begin
	try
	  by (tclCOMPLETE tac);
	  let _,(const,_,_) = cook_proof () in 
	  delete_current_proof (); const.const_entry_body
	with e when Logic.catchable_exception e -> 
	  delete_current_proof();
	  raise Exit
      end
	*)
  | _ -> raise Exit

let solve_remaining_evars env initial_sigma evd c =
  let evdref = ref evd in
  let rec proc_rec c =
    match Term.kind_of_term (Reductionops.whd_evar (Evd.evars_of !evdref) c) with
      | Term.Evar (ev,args as k) when not (Evd.mem initial_sigma ev) ->
            let (loc,src) = Evd.evar_source ev !evdref in
	    let sigma = Evd.evars_of !evdref in
	    (try 
	      let evi = Evd.find sigma ev in
	      let c = solvable_by_tactic env evi k src in
	      evdref := Evd.evar_define ev c !evdref;
	      c
	    with Exit ->
	      Pretype_errors.error_unsolvable_implicit loc env sigma src)
      | _ -> Term.map_constr proc_rec c      
  in
  proc_rec c

(* Transforms an id into a constr if possible, or fails *)
let constr_of_id env id = 
  Constrintern.construct_reference (Environ.named_context env) id

let constr_of_value env = function
  | VConstr csr -> csr
  | VIntroPattern (IntroIdentifier id) -> constr_of_id env id
  | _ -> raise Not_found

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

(* To retype a list of key*constr with undefined key *)
let retype_list sigma env lst =
  List.fold_right (fun (x,csr) a ->
    try (x,Retyping.get_judgment_of env sigma csr)::a with
    | Util.Anomaly _ -> a) lst []

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
      Constrintern.intern_gen (kind = Pretyping.IsType) ~ltacvars:ltacdata sigma env c in
  Pretyping.Default.understand_ltac sigma env (typs,unbndltacvars) kind c

(* Interprets a constr and solve remaining evars with default tactic *)
let interp_econstr kind ist sigma env cc =
  let evars,c = interp_gen kind ist sigma env cc in
  let csr = solve_remaining_evars env sigma evars c in
  Tactic_debug.db_constr ist.debug env csr;
  csr



(* arnaud: il faut sans doute revoir le mécanisme de with check/no check.
           A terme il a des chances d'être enfermé dans la monade, ce
           qui sera plus simple *)

(* Interprets an open constr *)
let interp_open_constr check_type ist cc =
  (* arnaud: à quoi sert "ist" déjà ? *)
  (* arnaud: cette fonction va changer de place... peut-être sera-t-elle
     simplement ici ? *)
  Goal.open_constr_of_raw check_type cc

(* arnaud: à nettoyer 
(* Interprets an open constr *)
let interp_open_constr ccl ist sigma env cc =
  let evd,c = interp_gen (Pretyping.OfType ccl) ist sigma env cc in
  (Evd.evars_of evd,c)
*)

let interp_constr = interp_econstr (Pretyping.OfType None)

let interp_type = interp_econstr Pretyping.IsType

(* Interprets a constr expression casted by the current goal *)
let pf_interp_casted_constr ist cc =

  Goal.concl >>= fun concl ->
  Goal.defs >>= fun defs ->
  Goal.env >>= fun env ->
  Goal.return (
    interp_econstr (Pretyping.OfType (Some concl)) ist (Evd.evars_of defs) env cc
  )

(* Interprets an open constr expression *)
let pf_interp_open_constr casted ist cc =
  interp_open_constr casted ist cc
(* arnaud: à nettoyer...
  Goal.concl >>= fun concl ->
  Goal.defs >>= fun defs ->
  Goal.env >>= fun env ->
  Goal.return (
    let cl = if casted then Some concl else None in
    interp_open_constr cl ist (Evd.evars_of defs) env cc
  )
*)

(* Interprets a constr expression *)
let pf_interp_constr ist c =
  Goal.defs >>= fun defs ->
  Goal.env >>= fun env ->
  Goal.return (interp_constr ist (Evd.evars_of defs) env c)

let constr_list_of_VList env = function
  | VList l -> List.map (constr_of_value env) l
  | _ -> raise Not_found
      
let pf_interp_constr_list_as_list ist (c,_ as x) =
  Goal.env >>= fun env ->
  Goal.defs >>= fun defs ->
  match c with
    | RVar (_,id) ->
	Goal.return (
          try 
	    constr_list_of_VList env (List.assoc id ist.lfun)
          with Not_found -> 
	    [interp_constr ist (Evd.evars_of defs) env x]
	)
    | _ -> 
	Goal.return 
	  [interp_constr ist (Evd.evars_of defs) env x]

let pf_interp_constr_list ist l =
  Goal.sensitive_list (List.map (pf_interp_constr_list_as_list ist) l) 
    >>= fun l ->
  Goal.return (List.flatten l)

let inj_open c = Util.anomaly "Tacinterp.inj_open: deprecated"(* arnaud: (Evd.empty,c)*)

let pf_interp_open_constr_list_as_list ist (c,_) =
  Goal.env >>= fun env ->
  Goal.defs >>= fun defs ->
  let sigma = Evd.evars_of defs in
  Goal.sensitive_list (
    match c with
    | RVar (_,id) ->
	(try List.map inj_open 
	   (constr_list_of_VList env (List.assoc id ist.lfun))
	 with Not_found ->
	   [interp_open_constr false ist c])
    | _ ->
	[interp_open_constr false ist c]
  )

let pf_interp_open_constr_list ist l =
  Goal.sensitive_list (List.map (pf_interp_open_constr_list_as_list ist) l) 
    >>= fun l ->
  Goal.return (List.flatten l)


let interp_pattern ist sigma env (l,c) = 
  Util.anomaly "Ltacinterp.interp_pattern: à restaurer"
  (*arnaud: à restaurer 
  (interp_int_or_var_list ist l, interp_constr ist sigma env c)
  *)

let interp_red_expr ist sigma env = function
  | Unfold l -> Unfold (List.map (interp_unfold ist env) l)
  | Fold l -> Util.anomaly "Ltacinterp.interp_red_expr: Fold: à restaurer"(*arnaud:à restaurer: Fold (List.map (interp_constr ist sigma env) l)*)
  | Cbv f -> Cbv (interp_flag ist env f)
  | Lazy f -> Lazy (interp_flag ist env f)
  | Pattern l -> Pattern (List.map (interp_pattern ist sigma env) l)
  | Simpl o -> Simpl (Option.map (interp_pattern ist sigma env) o)
  | (Red _ |  Hnf | ExtraRedExpr _ | CbvVm as r) -> r

let pf_interp_red_expr ist re = 
  Goal.env >>= fun env ->
  Goal.defs >>= fun defs ->
  Goal.return (interp_red_expr ist (Evd.evars_of defs) env re)




let coerce_to_hyp env = function
  | VConstr c when Term.isVar c -> Term.destVar c
  | VIntroPattern (IntroIdentifier id) when is_variable env id -> id
  | _ -> raise (CannotCoerceTo "a variable")

(* Interprets a bound variable (especially an existing hypothesis) *)
let interp_hyp ist (loc,id as locid) =
  Goal.env >>= fun env ->
  Goal.return (
    (* Look first in lfun for a value coercible to a variable *)
    try try_interp_ltac_var (coerce_to_hyp env) ist (Some env) locid
    with Not_found -> 
      (* Then look if bound in the proof context at calling time *)
      if is_variable env id then id
      else Util.user_err_loc (loc,"eval_variable",Nameops.pr_id id ++ str " not found")
  )

let hyp_list_of_VList env = function
  | VList l -> List.map (coerce_to_hyp env) l
  | _ -> raise Not_found

let interp_hyp_list_as_list ist (loc,id as x) =
  Goal.env >>= fun env ->
  try Goal.return (hyp_list_of_VList env (List.assoc id ist.lfun))
  with Not_found | CannotCoerceTo _ -> 
    interp_hyp ist x >>= fun hyp_x ->
    Goal.return [hyp_x]

let interp_hyp_list ist l =
  Goal.sensitive_list (List.map (interp_hyp_list_as_list ist) l) >>= fun hyps ->
  Goal.return (List.flatten hyps) 


(* Quantified named or numbered hypothesis or hypothesis in context *)
(* (as in Inversion) *)
let coerce_to_quantified_hypothesis = function
  | VInteger n -> AnonHyp n
  | VIntroPattern (IntroIdentifier id) -> NamedHyp id
  | v -> raise (CannotCoerceTo "a quantified hypothesis")

let interp_quantified_hypothesis ist = function
  | AnonHyp n -> AnonHyp n
  | NamedHyp id ->
      try 
	try_interp_ltac_var coerce_to_quantified_hypothesis 
	                    ist 
	                    None
	                    (Util.dummy_loc,id)
      with Not_found -> 
	NamedHyp id

let interp_binding_name ist = function
  | AnonHyp n -> AnonHyp n
  | NamedHyp id ->
      (* If a name is bound, it has to be a quantified hypothesis *)
      (* user has to use other names for variables if these ones clash with *)
      (* a name intented to be used as a (non-variable) identifier *)
      try 
	try_interp_ltac_var coerce_to_quantified_hypothesis 
	                    ist 
	                    None
	                    (Util.dummy_loc,id)
      with Not_found -> 
	NamedHyp id

(* Quantified named or numbered hypothesis or hypothesis in context *)
(* (as in Inversion) *)
let coerce_to_decl_or_quant_hyp env = function
  | VInteger n -> AnonHyp n
  | v -> 
      try NamedHyp (coerce_to_hyp env v)
      with CannotCoerceTo _ -> 
	raise (CannotCoerceTo "a declared or quantified hypothesis")

let interp_declared_or_quantified_hypothesis ist = function
  | AnonHyp n -> Goal.return (AnonHyp n)
  | NamedHyp id ->
      Goal.env >>= fun env ->
      Goal.return (
	try try_interp_ltac_var 
	  (coerce_to_decl_or_quant_hyp env) ist (Some env) (Util.dummy_loc,id)
	with Not_found -> NamedHyp id
      )

let interp_binding ist (loc,b,c) =
  pf_interp_open_constr false ist c >>= fun ioconstr ->
  Goal.return (loc,interp_binding_name ist b,ioconstr)

let interp_bindings ist = function
| NoBindings -> Goal.return NoBindings
| ImplicitBindings l -> 
    pf_interp_open_constr_list ist l >>= fun cl ->
    Goal.return (ImplicitBindings cl)
| ExplicitBindings l ->
    let interp_binding ist (l,qh,(c,_)) = interp_binding ist (l,qh,c) in
    Goal.sensitive_list (List.map (interp_binding ist) l) >>= fun bindings ->
    Goal.return (ExplicitBindings bindings)

let interp_constr_with_bindings ist (c,bl) =
  pf_interp_constr ist c >>= fun iconstr ->
  interp_bindings ist bl >>= fun ibindings ->
  Goal.return (iconstr, ibindings)

let interp_open_constr_with_bindings ist (c,bl) =
  pf_interp_open_constr false ist c >>= fun ioconstr ->
  interp_bindings ist bl >>= fun ibindings ->
  Goal.return (ioconstr, ibindings)

let coerce_to_hint_base = function
  | VIntroPattern (IntroIdentifier id) -> string_of_id id
  | _ -> raise (CannotCoerceTo "a hint base name")

let interp_hint_base ist s =
  try try_interp_ltac_var coerce_to_hint_base ist None (Util.dummy_loc,id_of_string s)
  with Not_found -> s

let coerce_to_intro_pattern env = function
  | VIntroPattern ipat -> ipat
  | VConstr c when Term.isVar c ->
      (* This happens e.g. in definitions like "Tac H = clear H; intro H" *)
      (* but also in "destruct H as (H,H')" *)
      IntroIdentifier (Term.destVar c)
  | v -> raise (CannotCoerceTo "an introduction pattern")

let interp_intro_pattern_var ist env id =
  try 
    try_interp_ltac_var (coerce_to_intro_pattern env) ist (Some env) 
                                                          (Util.dummy_loc,id)
  with Not_found -> IntroIdentifier id

let rec interp_intro_pattern ist = function
  | IntroOrAndPattern l -> 
      interp_case_intro_pattern ist l >>= fun patt ->
      Goal.return (IntroOrAndPattern patt)
  | IntroIdentifier id -> 
      Goal.env >>= fun env ->
      Goal.return (interp_intro_pattern_var ist env id)
  | IntroWildcard | IntroAnonymous | IntroFresh _ as x -> Goal.return x

and interp_case_intro_pattern ist l=
  let s_l_l = (List.map (List.map (interp_intro_pattern ist)) l) in
  let l_s_l = List.map Goal.sensitive_list s_l_l in
  Goal.sensitive_list l_s_l


(* arnaud: peut-être ne faut-il pas toujours renvoyer un Goal.sensitive,
   certaines tactiques ne dépendente pas des buts, ce qui change largement
   l'interprétation des arguments. Donc peut-être faut il un type de retourn
   somme, où seuls les trucs qui sont nécessairement des Goal.sensitive 
   typent ainsi. *)
let rec interp_genarg ist x =
  match genarg_tag x with
  | BoolArgType -> Goal.return (in_gen wit_bool (out_gen globwit_bool x))
  | IntArgType -> Goal. return (in_gen wit_int (out_gen globwit_int x))
  | IntOrVarArgType ->
      Goal.return (
	in_gen wit_int_or_var
          (ArgArg (interp_int_or_var ist (out_gen globwit_int_or_var x)))
      )
  | StringArgType ->
      Goal.return (in_gen wit_string (out_gen globwit_string x))
  | PreIdentArgType ->
      Goal.return (in_gen wit_pre_ident (out_gen globwit_pre_ident x))
  | IntroPatternArgType ->
      interp_intro_pattern ist (out_gen globwit_intro_pattern x) >>= fun patt ->
      Goal.return (in_gen wit_intro_pattern patt)
  | IdentArgType ->
      interp_fresh_ident ist (out_gen globwit_ident x) >>= fun id ->
      Goal.return (in_gen wit_ident id)
  | VarArgType ->
      interp_hyp ist (out_gen globwit_var x) >>= fun hyp ->
      Goal.return (in_gen wit_var hyp)
  | RefArgType ->
      pf_interp_reference ist (out_gen globwit_ref x) >>= fun r ->
      Goal.return (in_gen wit_ref r)
  | SortArgType -> Util.anomaly "Ltacinterp.interp_genarg: SortArgType: à restaurer"(*arnaud: à restaurer:
      in_gen wit_sort
        (Term.destSort 
	  (pf_interp_constr ist 
	    (RSort (dloc,out_gen globwit_sort x), None)))*)
  | ConstrArgType -> Util.anomaly "Ltacinterp.interp_genarg: ConstrArgType: à restaurer"(*arnaud: à restaurer:
      in_gen wit_constr (pf_interp_constr ist (out_gen globwit_constr x))
		     *)
  | ConstrMayEvalArgType ->Util.anomaly "Ltacinterp.interp_genarg: ConstrMayEvalArgType: à restaurer"(*arnaud: à restaurer:
      in_gen wit_constr_may_eval (interp_constr_may_eval ist (out_gen globwit_constr_may_eval x))
*)
  | QuantHypArgType ->
      interp_declared_or_quantified_hypothesis ist 
	(out_gen globwit_quant_hyp x) >>= fun qhyp ->
      Goal.return (in_gen wit_quant_hyp qhyp)
  | RedExprArgType ->
      pf_interp_red_expr ist (out_gen globwit_red_expr x) >>= fun red ->
      Goal.return (in_gen wit_red_expr red)
  | OpenConstrArgType casted -> 
      (interp_open_constr casted ist 
         (fst (snd (out_gen (globwit_open_constr_gen casted) x)))) >>= fun oc ->
      Goal.return (in_gen (wit_open_constr_gen casted) oc)
  | ConstrWithBindingsArgType -> Util.anomaly "Ltacinterp.interp gen_arg: ConstrWithBindingArgType: à restaurer" (* arnaud: à restaurer:
      in_gen wit_constr_with_bindings
        (interp_constr_with_bindings ist (out_gen globwit_constr_with_bindings x))
													  *)
  | BindingsArgType -> Util.anomaly "Ltacinterp.interp gen_arg: BindingsArgType: à restaurer" (* arnaud: à restaurer:
      in_gen wit_bindings
        (interp_bindings ist (out_gen globwit_bindings x))
												      *)
  | List0ArgType ConstrArgType ->  Util.anomaly "Ltacinterp.interp gen_arg: List0ArgType ConstrArgType: à restaurer" (* arnaud: à restaurer: interp_genarg_constr_list0 ist x*)
  | List1ArgType ConstrArgType ->  Util.anomaly "Ltacinterp.interp gen_arg: List1ArgType ConstrArgType: à restaurer" (* arnaud: à restaurer: interp_genarg_constr_list1 ist x*)
  | List0ArgType VarArgType -> Goal.return (interp_genarg_var_list0 ist  x)
  | List1ArgType VarArgType -> Goal.return (interp_genarg_var_list1 ist  x)
  (* arnaud:binder "intern_genarg" fonctionnera très bien. *)
  | List0ArgType _ -> Util.anomaly "Ltacinterp.interp gen_arg: List0ArgType _: à restaurer" (* arnaud: à restaurer:Goal.return (app_list0 (interp_genarg ist ) x)*)
  | List1ArgType _ -> Util.anomaly "Ltacinterp.interp gen_arg: List1ArgType _: à restaurer" (* arnaud: à restaurer:Goal.return (app_list1 (interp_genarg ist ) x)*)
  | OptArgType _ -> Util.anomaly "Ltacinterp.interp gen_arg: OptArgType: à restaurer" (* arnaud: à restaurer:Goal.return (app_opt (interp_genarg ist ) x)*)
  | PairArgType _ -> Util.anomaly "Ltacinterp.interp gen_arg: PairArgType: à restaurer" (* arnaud: à restaurer:Goal.return (app_pair (interp_genarg ist ) (interp_genarg ist ) x)*)
  | ExtraArgType s -> 
      Goal.return (
	match Pcoq.tactic_genarg_level s with
        | Some n -> 
            (* Special treatment of tactic arguments *)
            in_gen (Pcoq.wit_tactic n) (out_gen (Pcoq.globwit_tactic n) x)
	| None -> 
            lookup_interp_genarg s ist x
      )

and interp_genarg_var_list0 ist x = Util.anomaly "" (*arnaud:
  let lc = out_gen (wit_list0 globwit_var) x in
  let lc = interp_hyp_list ist lc in
  in_gen (wit_list0 wit_var) lc *)

and interp_genarg_var_list1 ist x = Util.anomaly "" (*arnaud:
  let lc = out_gen (wit_list1 globwit_var) x in
  let lc = interp_hyp_list ist lc in
  in_gen (wit_list1 wit_var) lc*)

(*arnaud: très temporary function *)
let unintro_pattern = function
  | IntroIdentifier id -> id
  | _ -> Util.anomaly "Ltacinterp.TacIntroPattern: pour l'instant on ne sait faire que des intro simples"

(* arnaud: très temporary function *)
let do_intro = function
  [x] -> Logic.intro x
  | _ -> Util.anomaly "Ltacinterp.TacIntroPattern: pour l'instant on ne sait faire que des intro simples (bis)"

let interp_induction_arg ist = function
  | ElimOnConstr c -> 
      interp_constr_with_bindings ist c >>= fun i_c ->
      Goal.return (ElimOnConstr i_c)
  | ElimOnAnonHyp n as x -> 
      Goal.return x
  | ElimOnIdent (loc,id) ->
      Goal.cond (Intros.is_quantified_hypothesis id) ~thn: 
       (Goal.return (ElimOnIdent (loc,id)))
      ~els: 
       (pf_interp_constr ist 
	  (RVar (loc,id),Some (Topconstr.CRef (Ident (loc,id)))) >>= fun i_c ->
	Goal.return (
	  ElimOnConstr (i_c, NoBindings)
	)
       )



(* Interprets an hypothesis name *)
let interp_hyp_location ist ((occs,id),hl) =
  interp_hyp ist id >>= fun hyp ->
  Goal.return ((interp_int_or_var_list ist occs,hyp),hl)

let interp_clause ist { onhyps=ol; onconcl=b; concl_occs=occs } =
  begin match ol with
  | None -> Goal.sNone
  | Some l -> 
      Goal.sensitive_list (List.map (interp_hyp_location ist) l) >>= fun i_l ->
      Goal.return (Some i_l)
  end >>= fun i_ol ->
  Goal.return
  { onhyps=i_ol;
    onconcl=b;
    concl_occs= interp_int_or_var_list ist occs }


let interp_atomic ist = function
  (* Basic tactics *)
  | TacIntroPattern l ->
      let i_l = Goal.sensitive_list (List.map (interp_intro_pattern ist) l) in
      Ntactics.intro_patterns i_l
  | TacIntrosUntil hyp -> let i_hyp = interp_quantified_hypothesis ist hyp in
                          (* arnaud: intros_until n'a pas besoin de sensitive *)
                          Intros.intros_until (Goal.return i_hyp)
  | TacIntroMove (ido,ido') ->
      begin
      match ido with
      | None -> Util.anomaly "Ltacinterp.inter_atomic: todo: TacIntroMove: None"
      | Some id -> Logic.intro (Goal.return id)
      end
  | TacClear (b,l) -> 
      if b then
	Util.anomaly "Ltacinterp.interp_atomic: TacClear: \"clear -\": à restaurer"
      else
	Logic.clear (interp_hyp_list ist l)
  | TacClearBody l ->
	 Logic.clear_body (interp_hyp_list ist l)
  | TacExtend (loc,opn,l) ->
      (* arnaud: peut-être bouger ?*)
      let interp_and_tag ist g =
	Genarg.genarg_tag g , interp_genarg ist g
      in
      let tac = lookup_tactic opn in
      tac (List.map (interp_and_tag ist) l)
      (* arnaud: à nettoyer dès que ça marche :)
      let tac = lookup_tactic opn in
      Proofview.tactic_of_sensitive_proof_step (
	Goal.sensitive_list (List.map (interp_genarg ist) l) >>= fun args ->
	tac args
      )
      *)
  | TacAssumption -> 
	Logic.assumption
  | TacExact c ->
	Logic.exact (pf_interp_casted_constr ist c)
  | TacExactNoCheck c -> 
      Util.anomaly "Ltacinterp.interp_atomic: ExactNoCheck: à restaurer"
  | TacVmCastNoCheck c ->
      Util.anomaly "Ltacinterp.interp_atomic: VmCastNoCheck: à restaurer"
  | TacApply (ev,cb) ->
      Logic.apply_with_ebindings_gen ev (interp_constr_with_bindings ist cb)
  | TacElim (ev,cb,cbo) ->
      let i_cbo =
	match cbo with
	| None -> Goal.sNone
	| Some cb -> 
	    interp_constr_with_bindings ist cb >>= fun i_cb ->
	    Goal.return (Some i_cb)
      in
      Ntactics.elim ev (interp_constr_with_bindings ist cb) i_cbo      
  | TacElimType c ->
      Util.anomaly "Ltacinterp.interp_atomic: ElimType: à restaurer"
  | TacCase (ev,cb) ->
      Util.anomaly "Ltacinterp.interp_atomic: Case: à restaurer"
  | TacCaseType c -> 
      Util.anomaly "Ltacinterp.interp_atomic: Case: à restaurer"
  | TacFix (idot,n) ->
      Util.anomaly "Ltacinterp.interp_atomic: Fix: à virer ?"
  | TacMutualFix (id,n,l) ->
      Util.anomaly "Ltacinterp.interp_atomic: MutualFix: à virer ?"
  | TacCofix idopt ->
      Util.anomaly "Ltacinterp.interp_atomic: Cofix: à virer ?"
  | TacMutualCofix (id,l) ->
       Util.anomaly "Ltacinterp.interp_atomic: MutualCofix: à virer ?"
  | TacCut c ->
      Logic.cut (pf_interp_constr ist c)
  | TacAssert (t,ipat,c) ->
      Util.anomaly "Ltacinterp.interp_atomic: Assert: à faire en ltac"
  | TacGeneralize cl ->
      Util.anomaly "Ltacinterp.interp_atomic:Generalize: à restaurer"
  |  TacGeneralizeDep c -> 
        Util.anomaly "Ltacinterp.interp_atomic:GeneralizeDep: à restaurer"
  | TacLetTac (na,c,clp) -> 
      Util.anomaly "Ltacinterp.interp_atomic:LetTac: à restaurer"
 
  (* Automation tactics *)
  | TacTrivial (lems,l) -> 
      let i_lems = pf_interp_constr_list ist lems in
      let i_l = (Option.map (List.map (interp_hint_base ist)) l) in
      Auto.gen_trivial i_lems i_l
  | TacAuto (n,lems,l) ->
      let i_n = Option.map (interp_int_or_var ist) n in
      let i_lems = pf_interp_constr_list ist lems in
      let i_l = Option.map (List.map (interp_hint_base ist)) l in
      Auto.gen_auto i_n i_lems i_l
  | TacAutoTDB n -> 
      Util.anomaly "Ltacinterp.interp_atomic:LetAutoTDB: à restaurer"
  | TacDestructHyp (b,id) -> 
      Util.anomaly "Ltacinterp.interp_atomic:LetDestructHyp: à restaurer"
  | TacDestructConcl -> 
      Util.anomaly "Ltacinterp.interp_atomic:LetDestructConcl: à restaurer"
  | TacSuperAuto (n,l,b1,b2) -> 
      Util.anomaly "Ltacinterp.interp_atomic:SuperAuto: à restaurer"
  | TacDAuto (n,p,lems) ->
      Util.anomaly "Ltacinterp.interp_atomic:DAuto: à restaurer"

  (* Derived basic tactics *)
  | TacSimpleInduction h -> 
      Util.anomaly "Ltacinterp.interp_atomic:SimpleInduction: à restaurer"
  | TacNewInduction (ev,lc,cbo,ids) ->
      Util.anomaly "Ltacinterp.interp_atomic:NewInduction: à restaurer"
  | TacSimpleDestruct h ->
      Util.anomaly "Ltacinterp.interp_atomic:SimpleDestruct: à restaurer"
  | TacNewDestruct (ev,c,cbo,ids) -> 
      let i_c =
	Goal.sensitive_list (
	  List.map (interp_induction_arg ist) c
	)
      in 
      let i_cbo =
	match cbo with
	| None -> Goal.sNone
	| Some cb -> 
	    interp_constr_with_bindings ist cb  >>= fun i_cb ->
	    Goal.return (Some i_cb)
      in
      let i_ids =
	interp_intro_pattern ist ids
      in
      Ntactics.new_destruct (Goal.return ev) i_c i_cbo i_ids
  | TacSplit ( _ , bl ) -> Ntactics.split_with_ebindings(interp_bindings ist bl)
  | TacAnyConstructor t ->
      Util.anomaly "Ltacinterp.interp_atomic:AnyConstructor:à restaurer"
  | TacConstructor (n,bl) ->
      Util.anomaly "Ltacinterp.interp_atomic:Constructor:à restaurer"

  (* Conversion *)
  | TacReduce (r,cl) ->
      let i_r = pf_interp_red_expr ist r in
      let i_cl = interp_clause ist cl in
      Ntactics.reduce i_r i_cl
  | TacChange (occl,c,cl) ->
      Util.anomaly "Ltacinterp.interp_atomic:Change:à restaurer"
  | _ -> Util.anomaly "Ltacinterp.interp_atomic: todo"

(* arnaud: commenter et renommer *)
let rec other_eval_tactic ist = function
  | TacAtom (loc,t) -> interp_atomic ist t (* il manque un catch_error ?*)
  (* arnaud: temporairement, je ne fais pas de nouvelles syntaxe,
     ça aidera à rebrancher tout ça plus conservativement. *)
  | TacThen (t1,a,t2,b) -> let a = Array.to_list a in
                           let b = Array.to_list b in
		           let i_t1 = other_eval_tactic ist t1 in
			   let i_a = List.map (other_eval_tactic ist) a in
			   let i_t2 = other_eval_tactic ist t2 in
			   let i_b = List.map (other_eval_tactic ist) b in
			   Logic.tclTHEN i_t1
			                (Logic.tclEXTEND i_a i_t2 i_b)
  | TacThens (t1,tl) -> 
      Logic.tclTHEN (other_eval_tactic ist t1) 
	      (Logic.tclLIST (List.map (other_eval_tactic ist) tl))
  | TacFirst l -> let i_l = List.map (other_eval_tactic ist) l in
                  Logic.tclFIRST i_l
  | TacComplete _ -> Util.anomaly "Ltacinterp.other_eval_tactic: TacComplete: todo"
  | TacSolve _ -> Util.anomaly "Ltacinterp.other_eval_tactics: TacSolve: todo"
  | TacTry _ -> Util.anomaly "Ltacinterp.other_eval_tactics: TacTry: todo"
  | TacOrelse (t1, t2) -> let i_t1 = other_eval_tactic ist t1 in
                          let i_t2 = other_eval_tactic ist t2 in
		          Logic.tclORELSE i_t1 i_t2
  | TacDo (n,t) -> let i_n = interp_int_or_var ist n in
                   let i_t = other_eval_tactic ist t in
		   Logic.tclDO i_n i_t
  | TacRepeat t -> let i_t = other_eval_tactic ist t in
                   Logic.tclREPEAT i_t
  | TacProgress _ -> Util.anomaly "Ltacinterp.other_eval_tactics: TacProgress: todo"
  | TacAbstract _ -> Util.anomaly "Ltacinterp.other_eval_tactics: TacAbstract: todo"
  | TacId _ (* arnaud: rebrancher le message *) -> Proofview.tclIDTAC ()
  | _ -> Util.anomaly "Ltacinterp.other_eval_tactic: todo"

let rec val_interp ist (tac:glob_tactic_expr) =

  let value_interp ist = match tac with
  (* Immediate evaluation *)
  | TacFun (it,body) -> VFun (ist.lfun,it,body)
  (* arnaud: todo? : TacArg, TacLet(Rec)In*)
  (* Delayed_evaluation *)
  | t -> VTactic (ist.last_loc,other_eval_tactic ist t)
  in
  Util.check_for_interrupt ();
    match ist.debug with
    | Tactic_debug.DebugOn lev -> Util.anomaly "Ltacinterp.tactic_of_value: todo"
	(* arnaud:was: debug_prompt lev gl tac (fun v -> value_interp {ist with debug=v})*)
    | _ -> value_interp ist 

(* arnaud: commenter ? *)
let interp_tactic ist tac  =
  try tactic_of_value (val_interp ist tac) 
  with NotTactic ->
    Util.errorlabstrm "" (str "Must be a command or must give a tactic value")

(* arnaud: commenter/renommer *)
let eval_tactic t =
  interp_tactic { lfun=[]; avoid_ids=[]; debug=get_debug(); last_loc=Util.dummy_loc } t

(* Initial call for interpretation *)
let interp_tac_gen lfun avoid_ids debug t =
  interp_tactic { lfun=lfun; avoid_ids=avoid_ids; debug=debug; last_loc=Util.dummy_loc } 
    (intern_tactic {
      ltacvars = (List.map fst lfun, []); ltacrecvars = [];
     (* arnaud: source d'erreur peut-être *) 
      gsigma = Evd.empty(* project gl *); genv = Global.env () (* pf_env gl *) } t)

let interp t =
  interp_tac_gen [] [] (get_debug()) t


(* arnaud: fonction très temporaire *)
let hide_interp p t ot =
  let ist = { ltacvars = ([],[]); 
	      ltacrecvars = []; 
              gsigma = Evd.evars_of (Proofview.defs_of (Proof.proofview_of p));
              genv = Global.env () } in
  let te = intern_tactic ist t in
  let t = eval_tactic te in
  match ot with 
  | None -> t
      (* arnaud: was: abstract_tactic_expr (TacArg (Tacexp te)) t*)
  | Some t' -> Util.anomaly "Logic.hide_interp: todo: end tactic"
      (* arnaud: original: abstract_tactic_expr ~dflt:true (TacArg (Tacexp te)) (tclTHEN t t') gl*)
