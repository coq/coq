(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Nameops
open Namegen
open Libnames
open Globnames
open Impargs
open Glob_term
open Glob_ops
open Patternops
open Pretyping
open Cases
open Constrexpr
open Constrexpr_ops
open Notation_term
open Notation_ops
open Topconstr
open Nametab
open Notation
open Inductiveops
open Misctypes
open Decl_kinds

(** constr_expr -> glob_constr translation:
    - it adds holes for implicit arguments
    - it remplaces notations by their value (scopes stuff are here)
    - it recognizes global vars from local ones
    - it prepares pattern maching problems (a pattern becomes a tree where nodes
    are constructor/variable pairs and leafs are variables)

    All that at once, fasten your seatbelt!
*)

(* To interpret implicits and arg scopes of variables in inductive
   types and recursive definitions and of projection names in records *)

type var_internalization_type =
  | Inductive of Id.t list (* list of params *)
  | Recursive
  | Method
  | Variable

type var_internalization_data =
    (* type of the "free" variable, for coqdoc, e.g. while typing the
       constructor of JMeq, "JMeq" behaves as a variable of type Inductive *)
    var_internalization_type *
    (* impargs to automatically add to the variable, e.g. for "JMeq A a B b"
       in implicit mode, this is [A;B] and this adds (A:=A) and (B:=B) *)
    Id.t list *
    (* signature of impargs of the variable *)
    Impargs.implicit_status list *
    (* subscopes of the args of the variable *)
    scope_name option list

type internalization_env =
    (var_internalization_data) Id.Map.t

type glob_binder = (Name.t * binding_kind * glob_constr option * glob_constr)

let interning_grammar = ref false

(* Historically for parsing grammar rules, but in fact used only for
   translator, v7 parsing, and unstrict tactic internalization *)
let for_grammar f x =
  interning_grammar := true;
  let a = f x in
    interning_grammar := false;
    a

(**********************************************************************)
(* Locating reference, possibly via an abbreviation *)

let locate_reference qid =
  Smartlocate.global_of_extended_global (Nametab.locate_extended qid)

let is_global id =
  try
    let _ = locate_reference (qualid_of_ident id) in true
  with Not_found ->
    false

let global_reference_of_reference ref =
  locate_reference (snd (qualid_of_reference ref))

let global_reference id =
  constr_of_global (locate_reference (qualid_of_ident id))

let construct_reference ctx id =
  try
    Term.mkVar (let _ = Context.lookup_named id ctx in id)
  with Not_found ->
    global_reference id

let global_reference_in_absolute_module dir id =
  constr_of_global (Nametab.global_of_path (Libnames.make_path dir id))

(**********************************************************************)
(* Internalization errors                                             *)

type internalization_error =
  | VariableCapture of Id.t * Id.t
  | IllegalMetavariable
  | NotAConstructor of reference
  | UnboundFixName of bool * Id.t
  | NonLinearPattern of Id.t
  | BadPatternsNumber of int * int

exception InternalizationError of Loc.t * internalization_error

let explain_variable_capture id id' =
  pr_id id ++ str " is dependent in the type of " ++ pr_id id' ++
  strbrk ": cannot interpret both of them with the same type"

let explain_illegal_metavariable =
  str "Metavariables allowed only in patterns"

let explain_not_a_constructor ref =
  str "Unknown constructor: " ++ pr_reference ref

let explain_unbound_fix_name is_cofix id =
  str "The name" ++ spc () ++ pr_id id ++
  spc () ++ str "is not bound in the corresponding" ++ spc () ++
  str (if is_cofix then "co" else "") ++ str "fixpoint definition"

let explain_non_linear_pattern id =
  str "The variable " ++ pr_id id ++ str " is bound several times in pattern"

let explain_bad_patterns_number n1 n2 =
  str "Expecting " ++ int n1 ++ str (String.plural n1 " pattern") ++
  str " but found " ++ int n2

let explain_internalization_error e =
  let pp = match e with
  | VariableCapture (id,id') -> explain_variable_capture id id'
  | IllegalMetavariable -> explain_illegal_metavariable
  | NotAConstructor ref -> explain_not_a_constructor ref
  | UnboundFixName (iscofix,id) -> explain_unbound_fix_name iscofix id
  | NonLinearPattern id -> explain_non_linear_pattern id
  | BadPatternsNumber (n1,n2) -> explain_bad_patterns_number n1 n2
  in pp ++ str "."

let error_bad_inductive_type loc =
  user_err_loc (loc,"",str
    "This should be an inductive type applied to patterns.")

let error_parameter_not_implicit loc =
  user_err_loc (loc,"", str
   "The parameters do not bind in patterns;" ++ spc () ++ str
    "they must be replaced by '_'.")

let error_ldots_var loc =
  user_err_loc (loc,"",str "Special token " ++ pr_id ldots_var ++
    str " is for use in the Notation command.")

(**********************************************************************)
(* Pre-computing the implicit arguments and arguments scopes needed   *)
(* for interpretation *)

let parsing_explicit = ref false

let empty_internalization_env = Id.Map.empty

let compute_explicitable_implicit imps = function
  | Inductive params ->
      (* In inductive types, the parameters are fixed implicit arguments *)
      let sub_impl,_ = List.chop (List.length params) imps in
      let sub_impl' = List.filter is_status_implicit sub_impl in
      List.map name_of_implicit sub_impl'
  | Recursive | Method | Variable ->
      (* Unable to know in advance what the implicit arguments will be *)
      []

let compute_internalization_data env ty typ impl =
  let impl = compute_implicits_with_manual env typ (is_implicit_args()) impl in
  let expls_impl = compute_explicitable_implicit impl ty in
  (ty, expls_impl, impl, compute_arguments_scope typ)

let compute_internalization_env env ty =
  List.fold_left3
    (fun map id typ impl -> Id.Map.add id (compute_internalization_data env ty typ impl) map)
    empty_internalization_env

(**********************************************************************)
(* Contracting "{ _ }" in notations *)

let rec wildcards ntn n =
  if Int.equal n (String.length ntn) then []
  else let l = spaces ntn (n+1) in if ntn.[n] == '_' then n::l else l
and spaces ntn n =
  if Int.equal n (String.length ntn) then []
  else if ntn.[n] == ' ' then wildcards ntn (n+1) else spaces ntn (n+1)

let expand_notation_string ntn n =
  let pos = List.nth (wildcards ntn 0) n in
  let hd = if Int.equal pos 0 then "" else String.sub ntn 0 pos in
  let tl =
    if Int.equal pos (String.length ntn) then ""
    else String.sub ntn (pos+1) (String.length ntn - pos -1) in
  hd ^ "{ _ }" ^ tl

(* This contracts the special case of "{ _ }" for sumbool, sumor notations *)
(* Remark: expansion of squash at definition is done in metasyntax.ml *)
let contract_notation ntn (l,ll,bll) =
  let ntn' = ref ntn in
  let rec contract_squash n = function
    | [] -> []
    | CNotation (_,"{ _ }",([a],[],[])) :: l ->
        ntn' := expand_notation_string !ntn' n;
        contract_squash n (a::l)
    | a :: l ->
        a::contract_squash (n+1) l in
  let l = contract_squash 0 l in
  (* side effect; don't inline *)
  !ntn',(l,ll,bll)

let contract_pat_notation ntn (l,ll) =
  let ntn' = ref ntn in
  let rec contract_squash n = function
    | [] -> []
    | CPatNotation (_,"{ _ }",([a],[]),[]) :: l ->
        ntn' := expand_notation_string !ntn' n;
        contract_squash n (a::l)
    | a :: l ->
        a::contract_squash (n+1) l in
  let l = contract_squash 0 l in
  (* side effect; don't inline *)
  !ntn',(l,ll)

type intern_env = {
  ids: Names.Id.Set.t;
  unb: bool;
  tmp_scope: Notation_term.tmp_scope_name option;
  scopes: Notation_term.scope_name list;
  impls: internalization_env }

(**********************************************************************)
(* Remembering the parsing scope of variables in notations            *)

let make_current_scope tmp scopes = match tmp, scopes with
| Some tmp_scope, (sc :: _) when String.equal sc tmp_scope -> scopes
| Some tmp_scope, scopes -> tmp_scope :: scopes
| None, scopes -> scopes

let pr_scope_stack = function
  | [] -> str "the empty scope stack"
  | [a] -> str "scope " ++ str a
  | l -> str "scope stack " ++
      str "[" ++ prlist_with_sep pr_comma str l ++ str "]"

let error_inconsistent_scope loc id scopes1 scopes2 =
  user_err_loc (loc,"set_var_scope",
    pr_id id ++ str " is here used in " ++
    pr_scope_stack scopes2 ++ strbrk " while it was elsewhere used in " ++
    pr_scope_stack scopes1)

let error_expect_binder_notation_type loc id =
  user_err_loc (loc,"",
    pr_id id ++
    str " is expected to occur in binding position in the right-hand side.")

let set_var_scope loc id istermvar env ntnvars =
  try
    let idscopes,typ = Id.Map.find id ntnvars in
    let () = if istermvar then
      (* scopes have no effect on the interpretation of identifiers *)
      begin match !idscopes with
      | None -> idscopes := Some (env.tmp_scope, env.scopes)
      | Some (tmp, scope) ->
        let s1 = make_current_scope tmp scope in
        let s2 = make_current_scope env.tmp_scope env.scopes in
        if not (List.equal String.equal s1 s2) then error_inconsistent_scope loc id s1 s2
      end
    in
    match typ with
    | NtnInternTypeBinder ->
	if istermvar then error_expect_binder_notation_type loc id
    | NtnInternTypeConstr ->
	(* We need sometimes to parse idents at a constr level for
	   factorization and we cannot enforce this constraint:
	   if not istermvar then error_expect_constr_notation_type loc id *)
	()
    | NtnInternTypeIdent -> ()
  with Not_found ->
    (* Not in a notation *)
    ()

let set_type_scope env = {env with tmp_scope = Some Notation.type_scope}

let reset_tmp_scope env = {env with tmp_scope = None}

let set_scope env = function
  | CastConv (GSort _) -> set_type_scope env
  | CastConv (GRef (_,ref) | GApp (_,GRef (_,ref),_)) ->
      {env with tmp_scope = compute_scope_of_global ref}
  | _ -> env

let rec it_mkGProd loc2 env body =
  match env with
      (loc1, (na, bk, _, t)) :: tl -> it_mkGProd loc2 tl (GProd (Loc.merge loc1 loc2, na, bk, t, body))
    | [] -> body

let rec it_mkGLambda loc2 env body =
  match env with
      (loc1, (na, bk, _, t)) :: tl -> it_mkGLambda loc2 tl (GLambda (Loc.merge loc1 loc2, na, bk, t, body))
    | [] -> body

(**********************************************************************)
(* Utilities for binders                                              *)
let build_impls = function
  |Implicit -> (function
		  |Name id ->  Some (id, Impargs.Manual, (true,true))
		  |Anonymous -> anomaly (Pp.str "Anonymous implicit argument"))
  |Explicit -> fun _ -> None

let impls_type_list ?(args = []) =
  let rec aux acc = function
    |GProd (_,na,bk,_,c) -> aux ((build_impls bk na)::acc) c
    |_ -> (Variable,[],List.append args (List.rev acc),[])
  in aux []

let impls_term_list ?(args = []) =
  let rec aux acc = function
    |GLambda (_,na,bk,_,c) -> aux ((build_impls bk na)::acc) c
    |GRec (_, fix_kind, nas, args, tys, bds) ->
       let nb = match fix_kind with |GFix (_, n) -> n | GCoFix n -> n in
       let acc' = List.fold_left (fun a (na, bk, _, _) -> (build_impls bk na)::a) acc args.(nb) in
	 aux acc' bds.(nb)
    |_ -> (Variable,[],List.append args (List.rev acc),[])
  in aux []

(* Check if in binder "(x1 x2 .. xn : t)", none of x1 .. xn-1 occurs in t *)
let rec check_capture ty = function
  | (loc,Name id)::(_,Name id')::_ when occur_glob_constr id ty ->
      raise (InternalizationError (loc,VariableCapture (id,id')))
  | _::nal ->
      check_capture ty nal
  | [] ->
      ()

let locate_if_isevar loc na = function
  | GHole _ ->
      (try match na with
	| Name id -> glob_constr_of_notation_constr loc
	               (Reserve.find_reserved_type id)
	| Anonymous -> raise Not_found
      with Not_found -> GHole (loc, Evar_kinds.BinderType na, None))
  | x -> x

let reset_hidden_inductive_implicit_test env =
  { env with impls = Id.Map.map (function
         | (Inductive _,b,c,d) -> (Inductive [],b,c,d)
         | x -> x) env.impls }

let check_hidden_implicit_parameters id impls =
  if Id.Map.exists (fun _ -> function
    | (Inductive indparams,_,_,_) -> Id.List.mem id indparams
    | _ -> false) impls
  then
    errorlabstrm "" (strbrk "A parameter of an inductive type " ++
    pr_id id ++ strbrk " is not allowed to be used as a bound variable in the type of its constructor.")

let push_name_env ?(global_level=false) lvar implargs env =
  function
  | loc,Anonymous ->
      if global_level then
	user_err_loc (loc,"", str "Anonymous variables not allowed");
      env
  | loc,Name id ->
      check_hidden_implicit_parameters id env.impls ;
      let (_,ntnvars) = lvar in
      if Id.Map.is_empty ntnvars && Id.equal id ldots_var
        then error_ldots_var loc;
      set_var_scope loc id false env ntnvars;
      if global_level then Dumpglob.dump_definition (loc,id) true "var"
      else Dumpglob.dump_binding loc id;
      {env with ids = Id.Set.add id env.ids; impls = Id.Map.add id implargs env.impls}

let intern_generalized_binder ?(global_level=false) intern_type lvar
    env (loc, na) b b' t ty =
  let ids = (match na with Anonymous -> fun x -> x | Name na -> Id.Set.add na) env.ids in
  let ty, ids' =
    if t then ty, ids else
      Implicit_quantifiers.implicit_application ids
	Implicit_quantifiers.combine_params_freevar ty
  in
  let ty' = intern_type {env with ids = ids; unb = true} ty in
  let fvs = Implicit_quantifiers.generalizable_vars_of_glob_constr ~bound:ids ~allowed:ids' ty' in
  let env' = List.fold_left
    (fun env (x, l) -> push_name_env ~global_level lvar (Variable,[],[],[])(*?*) env (l, Name x))
    env fvs in
  let bl = List.map
    (fun (id, loc) ->
      (loc, (Name id, b, None, GHole (loc, Evar_kinds.BinderType (Name id), None))))
    fvs
  in
  let na = match na with
    | Anonymous ->
	if global_level then na
	else
	  let name =
	    let id =
	      match ty with
	      | CApp (_, (_, CRef (Ident (loc,id))), _) -> id
	      | _ -> Id.of_string "H"
	    in Implicit_quantifiers.make_fresh ids' (Global.env ()) id
	  in Name name
    | _ -> na
  in (push_name_env ~global_level lvar (impls_type_list ty')(*?*) env' (loc,na)), (loc,(na,b',None,ty')) :: List.rev bl

let intern_assumption intern lvar env nal bk ty =
  let intern_type env = intern (set_type_scope env) in
  match bk with
  | Default k ->
      let ty = intern_type env ty in
      check_capture ty nal;
      let impls = impls_type_list ty in
      List.fold_left
	(fun (env, bl) (loc, na as locna) ->
          (push_name_env lvar impls env locna,
           (loc,(na,k,None,locate_if_isevar loc na ty))::bl))
	(env, []) nal
  | Generalized (b,b',t) ->
     let env, b = intern_generalized_binder intern_type lvar env (List.hd nal) b b' t ty in
     env, b

let intern_local_binder_aux ?(global_level=false) intern lvar (env,bl) = function
  | LocalRawAssum(nal,bk,ty) ->
      let env, bl' = intern_assumption intern lvar env nal bk ty in
      env, bl' @ bl
  | LocalRawDef((loc,na as locna),def) ->
      let indef = intern env def in
      (push_name_env lvar (impls_term_list indef) env locna,
      (loc,(na,Explicit,Some(indef),GHole(loc,Evar_kinds.BinderType na,None)))::bl)

let intern_generalization intern env lvar loc bk ak c =
  let c = intern {env with unb = true} c in
  let fvs = Implicit_quantifiers.generalizable_vars_of_glob_constr ~bound:env.ids c in
  let env', c' =
    let abs =
      let pi = match ak with
	| Some AbsPi -> true
        | Some _ -> false
	| None ->
          let is_type_scope = match env.tmp_scope with
          | None -> false
          | Some sc -> String.equal sc Notation.type_scope
          in
          is_type_scope ||
          String.List.mem Notation.type_scope env.scopes
      in
	if pi then
	  (fun (id, loc') acc ->
	    GProd (Loc.merge loc' loc, Name id, bk, GHole (loc', Evar_kinds.BinderType (Name id), None), acc))
	else
	  (fun (id, loc') acc ->
	    GLambda (Loc.merge loc' loc, Name id, bk, GHole (loc', Evar_kinds.BinderType (Name id), None), acc))
    in
      List.fold_right (fun (id, loc as lid) (env, acc) ->
	let env' = push_name_env lvar (Variable,[],[],[]) env (loc, Name id) in
	  (env', abs lid acc)) fvs (env,c)
  in c'

(**********************************************************************)
(* Syntax extensions                                                  *)

let option_mem_assoc id = function
  | Some (id',c) -> Id.equal id id'
  | None -> false

let find_fresh_name renaming (terms,termlists,binders) id =
  let fold1 _ (c, _) accu = Id.Set.union (free_vars_of_constr_expr c) accu in
  let fold2 _ (l, _) accu =
    let fold accu c = Id.Set.union (free_vars_of_constr_expr c) accu in
    List.fold_left fold accu l
  in
  let fold3 _ x accu = Id.Set.add x accu in
  let fvs1 = Id.Map.fold fold1 terms Id.Set.empty in
  let fvs2 = Id.Map.fold fold2 termlists fvs1 in
  let fvs3 = Id.Map.fold fold3 renaming fvs2 in
  (* TODO binders *)
  next_ident_away_from id (fun id -> Id.Set.mem id fvs3)

let traverse_binder (terms,_,_ as subst)
    (renaming,env)=
 function
 | Anonymous -> (renaming,env),Anonymous
 | Name id ->
  try
    (* Binders bound in the notation are considered first-order objects *)
    let _,na = coerce_to_name (fst (Id.Map.find id terms)) in
    (renaming,{env with ids = name_fold Id.Set.add na env.ids}), na
  with Not_found ->
    (* Binders not bound in the notation do not capture variables *)
    (* outside the notation (i.e. in the substitution) *)
    let id' = find_fresh_name renaming subst id in
    let renaming' =
      if Id.equal id id' then renaming else Id.Map.add id id' renaming
    in
    (renaming',env), Name id'

let make_letins = List.fold_right (fun (loc,(na,b,t)) c -> GLetIn (loc,na,b,c))

let rec subordinate_letins letins = function
  (* binders come in reverse order; the non-let are returned in reverse order together *)
  (* with the subordinated let-in in writing order *)
  | (loc,(na,_,Some b,t))::l ->
      subordinate_letins ((loc,(na,b,t))::letins) l
  | (loc,(na,bk,None,t))::l ->
      let letins',rest = subordinate_letins [] l in
      letins',((loc,(na,bk,t)),letins)::rest
  | [] ->
      letins,[]

let rec subst_iterator y t = function
  | GVar (_,id) as x -> if Id.equal id y then t else x
  | x -> map_glob_constr (subst_iterator y t) x

let subst_aconstr_in_glob_constr loc intern lvar subst infos c =
  let (terms,termlists,binders) = subst in
  let rec aux (terms,binderopt as subst') (renaming,env) c =
    let subinfos = renaming,{env with tmp_scope = None} in
    match c with
    | NVar id -> subst_var subst' (renaming, env) id
    | NList (x,_,iter,terminator,lassoc) ->
      (try
        (* All elements of the list are in scopes (scopt,subscopes) *)
	let (l,(scopt,subscopes)) = Id.Map.find x termlists in
        let termin = aux subst' subinfos terminator in
        let fold a t =
          let nterms = Id.Map.add x (a, (scopt, subscopes)) terms in
          subst_iterator ldots_var t (aux (nterms, binderopt) subinfos iter)
        in
	List.fold_right fold (if lassoc then List.rev l else l) termin
      with Not_found ->
          anomaly (Pp.str "Inconsistent substitution of recursive notation"))
    | NHole (knd, arg) ->
      let knd = match knd with
      | Evar_kinds.BinderType (Name id as na) ->
        let na =
          try snd (coerce_to_name (fst (Id.Map.find id terms)))
          with Not_found -> na
        in
        Evar_kinds.BinderType na
      | _ -> knd
      in
      let arg = match arg with
      | None -> None
      | Some arg ->
        let open Tacexpr in
        let open Genarg in
        let wit = glbwit Constrarg.wit_tactic in
        let body =
          if has_type arg wit then out_gen wit arg
          else assert false (** FIXME *)
        in
        let mk_env id (c, (tmp_scope, subscopes)) accu =
          let nenv = {env with tmp_scope; scopes = subscopes @ env.scopes} in
          let gc = intern nenv c in
          let c = ConstrMayEval (Genredexpr.ConstrTerm (gc, Some c)) in
          ((loc, id), c) :: accu
        in
        let bindings = Id.Map.fold mk_env terms [] in
        let tac = TacLetIn (false, bindings, body) in
        let arg = in_gen wit tac in
        Some arg
      in
      GHole (loc, knd, arg)
    | NBinderList (x,_,iter,terminator) ->
      (try
        (* All elements of the list are in scopes (scopt,subscopes) *)
	let (bl,(scopt,subscopes)) = Id.Map.find x binders in
	let env,bl = List.fold_left (intern_local_binder_aux intern lvar) (env,[]) bl in
	let letins,bl = subordinate_letins [] bl in
        let termin = aux subst' (renaming,env) terminator in
	let res = List.fold_left (fun t binder ->
          subst_iterator ldots_var t
	    (aux (terms,Some(x,binder)) subinfos iter))
	  termin bl in
	make_letins letins res
      with Not_found ->
          anomaly (Pp.str "Inconsistent substitution of recursive notation"))
    | NProd (Name id, NHole _, c') when option_mem_assoc id binderopt ->
        let (loc,(na,bk,t)),letins = snd (Option.get binderopt) in
	GProd (loc,na,bk,t,make_letins letins (aux subst' infos c'))
    | NLambda (Name id,NHole _,c') when option_mem_assoc id binderopt ->
        let (loc,(na,bk,t)),letins = snd (Option.get binderopt) in
	GLambda (loc,na,bk,t,make_letins letins (aux subst' infos c'))
    | t ->
      glob_constr_of_notation_constr_with_binders loc
        (traverse_binder subst) (aux subst') subinfos t
  and subst_var (terms, binderopt) (renaming, env) id =
    (* subst remembers the delimiters stack in the interpretation *)
    (* of the notations *)
    try
      let (a,(scopt,subscopes)) = Id.Map.find id terms in
      intern {env with tmp_scope = scopt;
                scopes = subscopes @ env.scopes} a
    with Not_found ->
    try
      GVar (loc, Id.Map.find id renaming)
    with Not_found ->
      (* Happens for local notation joint with inductive/fixpoint defs *)
      GVar (loc,id)
  in aux (terms,None) infos c

let split_by_type ids =
  List.fold_right (fun (x,(scl,typ)) (l1,l2,l3) ->
    match typ with
    | NtnTypeConstr -> ((x,scl)::l1,l2,l3)
    | NtnTypeConstrList -> (l1,(x,scl)::l2,l3)
    | NtnTypeBinderList -> (l1,l2,(x,scl)::l3)) ids ([],[],[])

let make_subst ids l =
  let fold accu (id, scl) a = Id.Map.add id (a, scl) accu in
  List.fold_left2 fold Id.Map.empty ids l

let intern_notation intern env lvar loc ntn fullargs =
  let ntn,(args,argslist,bll as fullargs) = contract_notation ntn fullargs in
  let ((ids,c),df) = interp_notation loc ntn (env.tmp_scope,env.scopes) in
  Dumpglob.dump_notation_location (ntn_loc loc fullargs ntn) ntn df;
  let ids,idsl,idsbl = split_by_type ids in
  let terms = make_subst ids args in
  let termlists = make_subst idsl argslist in
  let binders = make_subst idsbl bll in
  subst_aconstr_in_glob_constr loc intern lvar
    (terms, termlists, binders) (Id.Map.empty, env) c

(**********************************************************************)
(* Discriminating between bound variables and global references       *)

let string_of_ty = function
  | Inductive _ -> "ind"
  | Recursive -> "def"
  | Method -> "meth"
  | Variable -> "var"

let intern_var genv (ltacvars,ntnvars) namedctx loc id =
  let (ltacvars,unbndltacvars) = ltacvars in
  (* Is [id] an inductive type potentially with implicit *)
  try
    let ty,expl_impls,impls,argsc = Id.Map.find id genv.impls in
    let expl_impls = List.map
      (fun id -> CRef (Ident (loc,id)), Some (loc,ExplByName id)) expl_impls in
    let tys = string_of_ty ty in
    Dumpglob.dump_reference loc "<>" (Id.to_string id) tys;
    GVar (loc,id), make_implicits_list impls, argsc, expl_impls
  with Not_found ->
  (* Is [id] bound in current term or is an ltac var bound to constr *)
  if Id.Set.mem id genv.ids || Id.Set.mem id ltacvars
  then
    GVar (loc,id), [], [], []
  (* Is [id] a notation variable *)
  else if Id.Map.mem id ntnvars
  then
    (set_var_scope loc id true genv ntnvars; GVar (loc,id), [], [], [])
  (* Is [id] the special variable for recursive notations *)
  else if Id.equal id ldots_var
  then if Id.Map.is_empty ntnvars
    then error_ldots_var loc
    else GVar (loc,id), [], [], []
  else if Id.Set.mem id unbndltacvars then
    (* Is [id] bound to a free name in ltac (this is an ltac error message) *)
    user_err_loc (loc,"intern_var",
      str "variable " ++ pr_id id ++ str " should be bound to a term.")
  else
    (* Is [id] a goal or section variable *)
    let _ = Context.lookup_named id namedctx in
      try
	(* [id] a section variable *)
	(* Redundant: could be done in intern_qualid *)
	let ref = VarRef id in
	let impls = implicits_of_global ref in
	let scopes = find_arguments_scope ref in
	Dumpglob.dump_reference loc "<>" (string_of_qualid (Decls.variable_secpath id)) "var";
	GRef (loc, ref), impls, scopes, []
      with e when Errors.noncritical e ->
	(* [id] a goal variable *)
	GVar (loc,id), [], [], []

let find_appl_head_data = function
  | GRef (_,ref) as x -> x,implicits_of_global ref,find_arguments_scope ref,[]
  | GApp (_,GRef (_,ref),l) as x
      when l != [] && Flags.version_strictly_greater Flags.V8_2 ->
      let n = List.length l in
      x,List.map (drop_first_implicits n) (implicits_of_global ref),
      List.skipn_at_least n (find_arguments_scope ref),[]
  | x -> x,[],[],[]

let error_not_enough_arguments loc =
  user_err_loc (loc,"",str "Abbreviation is not applied enough.")

let check_no_explicitation l =
  let is_unset (a, b) = match b with None -> false | Some _ -> true in
  let l = List.filter is_unset l in
  match l with
  | [] -> ()
  | (_, None) :: _ -> assert false
  | (_, Some (loc, _)) :: _ ->
    user_err_loc (loc,"",str"Unexpected explicitation of the argument of an abbreviation.")

let dump_extended_global loc = function
  | TrueGlobal ref -> (*feedback_global loc ref;*) Dumpglob.add_glob loc ref
  | SynDef sp -> Dumpglob.add_glob_kn loc sp

let intern_extended_global_of_qualid (loc,qid) =
  let r = Nametab.locate_extended qid in dump_extended_global loc r; r

let intern_reference ref =
  let qid = qualid_of_reference ref in
  let r =
    try intern_extended_global_of_qualid qid
    with Not_found -> error_global_not_found_loc (fst qid) (snd qid)
  in
  Smartlocate.global_of_extended_global r

(* Is it a global reference or a syntactic definition? *)
let intern_qualid loc qid intern env lvar args =
  match intern_extended_global_of_qualid (loc,qid) with
  | TrueGlobal ref ->
      GRef (loc, ref), args
  | SynDef sp ->
      let (ids,c) = Syntax_def.search_syntactic_definition sp in
      let nids = List.length ids in
      if List.length args < nids then error_not_enough_arguments loc;
      let args1,args2 = List.chop nids args in
      check_no_explicitation args1;
      let terms = make_subst ids (List.map fst args1) in
      let subst = (terms, Id.Map.empty, Id.Map.empty) in
      let infos = (Id.Map.empty, env) in
      subst_aconstr_in_glob_constr loc intern lvar subst infos c, args2

(* Rule out section vars since these should have been found by intern_var *)
let intern_non_secvar_qualid loc qid intern env lvar args =
  match intern_qualid loc qid intern env lvar args with
    | GRef (_, VarRef _),_ -> raise Not_found
    | r -> r

let intern_applied_reference intern env namedctx lvar args = function
  | Qualid (loc, qid) ->
      let r,args2 =
	try intern_qualid loc qid intern env lvar args
	with Not_found -> error_global_not_found_loc loc qid
      in
      find_appl_head_data r, args2
  | Ident (loc, id) ->
      try intern_var env lvar namedctx loc id, args
      with Not_found ->
      let qid = qualid_of_ident id in
      try
	let r,args2 = intern_non_secvar_qualid loc qid intern env lvar args in
	find_appl_head_data r, args2
      with Not_found ->
	(* Extra allowance for non globalizing functions *)
	if !interning_grammar || env.unb then
	  (GVar (loc,id), [], [], []),args
	else error_global_not_found_loc loc qid

let interp_reference vars r =
  let (r,_,_,_),_ =
    intern_applied_reference (fun _ -> error_not_enough_arguments Loc.ghost)
      {ids = Id.Set.empty; unb = false ;
       tmp_scope = None; scopes = []; impls = empty_internalization_env} []
      (vars, Id.Map.empty) [] r
  in r

(**********************************************************************)
(** {5 Cases }                                                        *)

(** {6 Elemtary bricks } *)
let apply_scope_env env = function
  | [] -> {env with tmp_scope = None}, []
  | sc::scl -> {env with tmp_scope = sc}, scl

let rec simple_adjust_scopes n scopes =
  (* Note: they can be less scopes than arguments but also more scopes *)
  (* than arguments because extra scopes are used in the presence of *)
  (* coercions to funclass *)
  if Int.equal n 0 then [] else match scopes with
  | [] -> None :: simple_adjust_scopes (n-1) []
  | sc::scopes -> sc :: simple_adjust_scopes (n-1) scopes

let find_remaining_scopes pl1 pl2 ref =
  let impls_st = implicits_of_global ref in
  let len_pl1 = List.length pl1 in
  let len_pl2 = List.length pl2 in
  let impl_list = if Int.equal len_pl1 0
    then select_impargs_size len_pl2 impls_st
    else List.skipn_at_least len_pl1 (select_stronger_impargs impls_st) in
  let allscs = find_arguments_scope ref in
  let scope_list = List.skipn_at_least len_pl1 allscs in
  let rec aux = function
    |[],l -> l
    |_,[] -> []
    |h::t,_::tt when is_status_implicit h -> aux (t,tt)
    |_::t,h::tt -> h :: aux (t,tt)
  in ((try List.firstn len_pl1 allscs with Failure _ -> simple_adjust_scopes len_pl1 allscs),
      simple_adjust_scopes len_pl2 (aux (impl_list,scope_list)))

let merge_subst s1 s2 = Id.Map.fold Id.Map.add s1 s2

let product_of_cases_patterns ids idspl =
  List.fold_right (fun (ids,pl) (ids',ptaill) ->
    (ids @ ids',
     (* Cartesian prod of the or-pats for the nth arg and the tail args *)
     List.flatten (
       List.map (fun (subst,p) ->
	 List.map (fun (subst',ptail) -> (merge_subst subst subst',p::ptail)) ptaill) pl)))
    idspl (ids,[Id.Map.empty,[]])

(* @return the first variable that occurs twice in a pattern

naive n^2 algo *)
let rec has_duplicate = function
  | [] -> None
  | x::l -> if Id.List.mem x l then (Some x) else has_duplicate l

let loc_of_lhs lhs =
 Loc.merge (fst (List.hd lhs)) (fst (List.last lhs))

let check_linearity lhs ids =
  match has_duplicate ids with
    | Some id ->
	raise (InternalizationError (loc_of_lhs lhs,NonLinearPattern id))
    | None ->
	()

(* Match the number of pattern against the number of matched args *)
let check_number_of_pattern loc n l =
  let p = List.length l in
  if not (Int.equal n p) then raise (InternalizationError (loc,BadPatternsNumber (n,p)))

let check_or_pat_variables loc ids idsl =
  if List.exists (fun ids' -> not (List.eq_set Id.equal ids ids')) idsl then
    user_err_loc (loc, "", str
    "The components of this disjunctive pattern must bind the same variables.")

(** Use only when params were NOT asked to the user.
    @return if letin are included *)
let check_constructor_length env loc cstr len_pl pl0 =
  let nargs = Inductiveops.mis_constructor_nargs cstr in
  let n = len_pl + List.length pl0 in
  if Int.equal n nargs then false else
    (Int.equal n ((fst (Inductiveops.inductive_nargs (fst cstr))) + Inductiveops.constructor_nrealhyps cstr)) ||
      (error_wrong_numarg_constructor_loc loc env cstr
        (nargs - (Inductiveops.inductive_nparams (fst cstr))))

let add_implicits_check_length fail nargs nargs_with_letin impls_st len_pl1 pl2 =
  let impl_list = if Int.equal len_pl1 0
    then select_impargs_size (List.length pl2) impls_st
    else List.skipn_at_least len_pl1 (select_stronger_impargs impls_st) in
  let remaining_args = List.fold_left (fun i x -> if is_status_implicit x then i else succ i) in
  let rec aux i = function
    |[],l -> let args_len = List.length l + List.length impl_list + len_pl1 in
	     ((if Int.equal args_len nargs then false
	      else Int.equal args_len nargs_with_letin || (fst (fail (nargs - List.length impl_list + i))))
	       ,l)
    |imp::q as il,[] -> if is_status_implicit imp && maximal_insertion_of imp
      then let (b,out) = aux i (q,[]) in (b,RCPatAtom(Loc.ghost,None)::out)
      else fail (remaining_args (len_pl1+i) il)
    |imp::q,(hh::tt as l) -> if is_status_implicit imp
      then let (b,out) = aux i (q,l) in (b,RCPatAtom(Loc.ghost,None)::out)
      else let (b,out) = aux (succ i) (q,tt) in (b,hh::out)
  in aux 0 (impl_list,pl2)

let add_implicits_check_constructor_length env loc c len_pl1 pl2 =
  let nargs = Inductiveops.mis_constructor_nargs c in
  let nargs' = (fst (Inductiveops.inductive_nargs (fst c)))
    + Inductiveops.constructor_nrealhyps c in
  let impls_st = implicits_of_global (ConstructRef c) in
  add_implicits_check_length (error_wrong_numarg_constructor_loc loc env c)
    nargs nargs' impls_st len_pl1 pl2

let add_implicits_check_ind_length env loc c len_pl1 pl2 =
  let (mib,mip) = Global.lookup_inductive c in
  let nparams = mib.Declarations.mind_nparams in
  let nargs = mip.Declarations.mind_nrealargs + nparams in
  let nparams', nrealargs' = inductive_nargs_env env c in
  let impls_st = implicits_of_global (IndRef c) in
  add_implicits_check_length (error_wrong_numarg_inductive_loc loc env c)
    nargs (nrealargs' + nparams') impls_st len_pl1 pl2

(** Do not raise NotEnoughArguments thanks to preconditions*)
let chop_params_pattern loc ind args with_letin =
  let nparams = if with_letin
    then fst (Inductiveops.inductive_nargs ind)
    else Inductiveops.inductive_nparams ind in
  assert (nparams <= List.length args);
  let params,args = List.chop nparams args in
  List.iter (function PatVar(_,Anonymous) -> ()
    | PatVar (loc',_) | PatCstr(loc',_,_,_) -> error_parameter_not_implicit loc') params;
  args

let find_constructor loc add_params ref =
  let cstr = match ref with
  | ConstructRef cstr -> cstr
  | IndRef _ ->
    let error = str "There is an inductive name deep in a \"in\" clause." in
    user_err_loc (loc, "find_constructor", error)
  | ConstRef _ | VarRef _ ->
    let error = str "This reference is not a constructor." in
    user_err_loc (loc, "find_constructor", error)
  in
  cstr, (function (ind,_ as c) -> match add_params with
    |Some nb_args ->
      let nb =
        if Int.equal nb_args (Inductiveops.constructor_nrealhyps c)
          then fst (Inductiveops.inductive_nargs ind)
          else Inductiveops.inductive_nparams ind
      in
      List.make nb ([], [(Id.Map.empty, PatVar(Loc.ghost,Anonymous))])
    |None -> []) cstr

let find_pattern_variable = function
  | Ident (loc,id) -> id
  | Qualid (loc,_) as x -> raise (InternalizationError(loc,NotAConstructor x))

let sort_fields mode loc l completer =
(*mode=false if pattern and true if constructor*)
  match l with
    | [] -> None
    | (refer, value)::rem ->
	let (nparams,          (* the number of parameters *)
	     base_constructor, (* the reference constructor of the record *)
	     (max,             (* number of params *)
	      (first_index,    (* index of the first field of the record *)
	       list_proj)))    (* list of projections *)
	  =
	  let record =
	    try Recordops.find_projection
	      (global_reference_of_reference refer)
	    with Not_found ->
	      user_err_loc (loc_of_reference refer, "intern", pr_reference refer ++ str": Not a projection")
	    in
	  (* elimination of the first field from the projections *)
	  let rec build_patt l m i acc =
	    match l with
	      | [] -> (i, acc)
	      | (Some name) :: b->
		 (match m with
		    | [] -> anomaly (Pp.str "Number of projections mismatch")
		    | (_, regular)::tm ->
		       let boolean = not regular in
                       begin match global_reference_of_reference refer with
		       | ConstRef name' when eq_constant name name' ->
			 if boolean && mode then
			   user_err_loc (loc, "", str"No local fields allowed in a record construction.")
			 else build_patt b tm (i + 1) (i, snd acc) (* we found it *)
                       | _ ->
			  build_patt b tm (if boolean&&mode then i else i + 1)
			    (if boolean && mode then acc
			     else fst acc, (i, ConstRef name) :: snd acc)
                       end)
	      | None :: b-> (* we don't want anonymous fields *)
		 if mode then
		   user_err_loc (loc, "", str "This record contains anonymous fields.")
		 else build_patt b m (i+1) acc
		   (* anonymous arguments don't appear in m *)
	    in
	  let ind = record.Recordops.s_CONST in
	  try (* insertion of Constextern.reference_global *)
	    (record.Recordops.s_EXPECTEDPARAM,
	     Qualid (loc, shortest_qualid_of_global Id.Set.empty (ConstructRef ind)),
	     build_patt record.Recordops.s_PROJ record.Recordops.s_PROJKIND 1 (0,[]))
	  with Not_found -> anomaly (Pp.str "Environment corruption for records.")
	  in
	(* now we want to have all fields of the pattern indexed by their place in
	   the constructor *)
	let rec sf patts accpatt =
	  match patts with
	    | [] -> accpatt
	    | p::q->
	       let refer, patt = p in
	       let glob_refer = try global_reference_of_reference refer
	       with |Not_found ->
		 user_err_loc (loc_of_reference refer, "intern",
			       str "The field \"" ++ pr_reference refer ++ str "\" does not exist.") in
	       let rec add_patt l acc =
		 match l with
		   | [] ->
		       user_err_loc
			 (loc, "",
			  str "This record contains fields of different records.")
		   | (i, a) :: b->
		       if eq_gr glob_refer a
		       then (i,List.rev_append acc l)
		       else add_patt b ((i,a)::acc)
	         in
	       let (index, projs) = add_patt (snd accpatt) [] in
		 sf q ((index, patt)::fst accpatt, projs) in
	let (unsorted_indexed_pattern, remainings) =
	  sf rem ([first_index, value], list_proj) in
	(* we sort them *)
	let sorted_indexed_pattern =
	  List.sort (fun (i, _) (j, _) -> compare i j) unsorted_indexed_pattern in
	(* a function to complete with wildcards *)
	let rec complete_list n l =
	  if n <= 1 then l else complete_list (n-1) (completer n l) in
	(* a function to remove indice *)
	let rec clean_list l i acc =
	  match l with
	    | [] -> complete_list (max - i) acc
	    | (k, p)::q-> clean_list q k (p::(complete_list (k - i) acc))
	  in
	Some (nparams, base_constructor,
	  List.rev (clean_list sorted_indexed_pattern 0 []))

(** {6 Manage multiple aliases} *)

type alias = {
  alias_ids : Id.t list;
  alias_map : Id.t Id.Map.t;
}

let empty_alias = {
  alias_ids = [];
  alias_map = Id.Map.empty;
}

  (* [merge_aliases] returns the sets of all aliases encountered at this
     point and a substitution mapping extra aliases to the first one *)
let merge_aliases aliases id =
  let alias_ids = aliases.alias_ids @ [id] in
  let alias_map = match aliases.alias_ids with
  | [] -> aliases.alias_map
  | id' :: _ -> Id.Map.add id id' aliases.alias_map
  in
  { alias_ids; alias_map; }

let alias_of als = match als.alias_ids with
| [] -> Anonymous
| id :: _ -> Name id

let message_redundant_alias id1 id2 =
  msg_warning
    (str "Alias variable " ++ pr_id id1 ++ str " is merged with " ++ pr_id id2)

(** {6 Expanding notations }

    @returns a raw_case_pattern_expr :
    - no notations and syntactic definition
    - global reference and identifeir instead of reference

*)

let rec subst_pat_iterator y t p = match p with
  | RCPatAtom (_,id) ->
    begin match id with Some x when Id.equal x y -> t | _ -> p end
  | RCPatCstr (loc,id,l1,l2) ->
     RCPatCstr (loc,id,List.map (subst_pat_iterator y t) l1,
	       List.map (subst_pat_iterator y t) l2)
  | RCPatAlias (l,p,a) -> RCPatAlias (l,subst_pat_iterator y t p,a)
  | RCPatOr (l,pl) -> RCPatOr (l,List.map (subst_pat_iterator y t) pl)

let drop_notations_pattern looked_for =
  (* At toplevel, Constructors and Inductives are accepted, in trecursive calls
     only constructor are allowed *)
  let ensure_kind top =
    if top then looked_for else
      function  ConstructRef _ -> () |_ -> raise Not_found in
  let rec drop_syndef top env re pats =
    let (loc,qid) = qualid_of_reference re in
    try
      match locate_extended qid with
      |SynDef sp ->
	let (vars,a) = Syntax_def.search_syntactic_definition sp in
	(match a with
	| NRef g ->
	  ensure_kind top g;
	  let () = assert (List.is_empty vars) in
	  let (_,argscs) = find_remaining_scopes [] pats g in
	  Some (g, [], List.map2 (in_pat_sc env) argscs pats)
	| NApp (NRef g,[]) -> (* special case : Syndef for @Cstr *)
	      ensure_kind top g;
              let () = assert (List.is_empty vars) in
	      let (argscs,_) = find_remaining_scopes pats [] g in
	      Some (g, List.map2 (in_pat_sc env) argscs pats, [])
	    | NApp (NRef g,args) ->
	      ensure_kind top g;
	      let nvars = List.length vars in
	      if List.length pats < nvars then error_not_enough_arguments loc;
	      let pats1,pats2 = List.chop nvars pats in
	      let subst = make_subst vars pats1 in
	      let idspl1 = List.map (in_not false loc env (subst, Id.Map.empty) []) args in
	      let (_,argscs) = find_remaining_scopes pats1 pats2 g in
	      Some (g, idspl1, List.map2 (in_pat_sc env) argscs pats2)
	    | _ -> raise Not_found)
	|TrueGlobal g ->
	  ensure_kind top g;
	  Dumpglob.add_glob loc g;
	  let (_,argscs) = find_remaining_scopes [] pats g in
	  Some (g,[],List.map2 (fun x -> in_pat false {env with tmp_scope = x}) argscs pats)
    with Not_found -> None
  and in_pat top env = function
    | CPatAlias (loc, p, id) -> RCPatAlias (loc, in_pat top env p, id)
    | CPatRecord (loc, l) ->
      let sorted_fields =
	sort_fields false loc l (fun _ l -> (CPatAtom (loc, None))::l) in
      begin match sorted_fields with
	| None -> RCPatAtom (loc, None)
	| Some (_, head, pl) ->
	  match drop_syndef top env head pl with
	    |Some (a,b,c) -> RCPatCstr(loc, a, b, c)
	    |None -> raise (InternalizationError (loc,NotAConstructor head))
      end
    | CPatCstr (loc, head, [], pl) ->
      begin
	match drop_syndef top env head pl with
	  | Some (a,b,c) -> RCPatCstr(loc, a, b, c)
	  | None -> raise (InternalizationError (loc,NotAConstructor head))
      end
    | CPatCstr (loc, r, expl_pl, pl) ->
      let g = try
		      (locate (snd (qualid_of_reference r)))
	    with Not_found ->
 	      raise (InternalizationError (loc,NotAConstructor r)) in
      let (argscs1,argscs2) = find_remaining_scopes expl_pl pl g in
      RCPatCstr (loc, g, List.map2 (in_pat_sc env) argscs1 expl_pl, List.map2 (in_pat_sc env) argscs2 pl)
    | CPatNotation (loc,"- _",([CPatPrim(_,Numeral p)],[]),[])
	when Bigint.is_strictly_pos p ->
      fst (Notation.interp_prim_token_cases_pattern_expr loc (ensure_kind false) (Numeral (Bigint.neg p))
	     (env.tmp_scope,env.scopes))
    | CPatNotation (_,"( _ )",([a],[]),[]) ->
      in_pat top env a
    | CPatNotation (loc, ntn, fullargs,extrargs) ->
      let ntn,(args,argsl as fullargs) = contract_pat_notation ntn fullargs in
      let ((ids',c),df) = Notation.interp_notation loc ntn (env.tmp_scope,env.scopes) in
      let (ids',idsl',_) = split_by_type ids' in
      Dumpglob.dump_notation_location (patntn_loc loc fullargs ntn) ntn df;
      let substlist = make_subst idsl' argsl in
      let subst = make_subst ids' args in
      in_not top loc env (subst,substlist) extrargs c
    | CPatDelimiters (loc, key, e) ->
      in_pat top {env with scopes=find_delimiters_scope loc key::env.scopes;
	tmp_scope = None} e
    | CPatPrim (loc,p) -> fst (Notation.interp_prim_token_cases_pattern_expr loc (ensure_kind false) p
				 (env.tmp_scope,env.scopes))
    | CPatAtom (loc, Some id) ->
      begin
	match drop_syndef top env id [] with
	  |Some (a,b,c) -> RCPatCstr (loc, a, b, c)
	  |None -> RCPatAtom (loc, Some (find_pattern_variable id))
      end
    | CPatAtom (loc,None) -> RCPatAtom (loc,None)
    | CPatOr (loc, pl) ->
      RCPatOr (loc,List.map (in_pat top env) pl)
  and in_pat_sc env x = in_pat false {env with tmp_scope = x}
  and in_not top loc env (subst,substlist as fullsubst) args = function
    | NVar id ->
      let () = assert (List.is_empty args) in
      begin
	(* subst remembers the delimiters stack in the interpretation *)
	(* of the notations *)
	try
	  let (a,(scopt,subscopes)) = Id.Map.find id subst in
	  in_pat top {env with scopes=subscopes@env.scopes;
	    tmp_scope = scopt} a
	with Not_found ->
	  if Id.equal id ldots_var then RCPatAtom (loc,Some id) else
	    anomaly (str "Unbound pattern notation variable: " ++ Id.print id)
      end
    | NRef g ->
      ensure_kind top g;
      let (_,argscs) = find_remaining_scopes [] args g in
      RCPatCstr (loc, g, [], List.map2 (in_pat_sc env) argscs args)
    | NApp (NRef g,pl) ->
      ensure_kind top g;
      let (argscs1,argscs2) = find_remaining_scopes pl args g in
      RCPatCstr (loc, g,
		 List.map2 (fun x -> in_not false loc {env with tmp_scope = x} fullsubst []) argscs1 pl,
		 List.map2 (in_pat_sc env) argscs2 args)
    | NList (x,_,iter,terminator,lassoc) ->
      let () = assert (List.is_empty args) in
      (try
         (* All elements of the list are in scopes (scopt,subscopes) *)
	 let (l,(scopt,subscopes)) = Id.Map.find x substlist in
         let termin = in_not top loc env fullsubst [] terminator in
	 List.fold_right (fun a t ->
           let nsubst = Id.Map.add x (a, (scopt, subscopes)) subst in
           let u = in_not false loc env (nsubst, substlist) [] iter in
           subst_pat_iterator ldots_var t u)
           (if lassoc then List.rev l else l) termin
       with Not_found ->
         anomaly (Pp.str "Inconsistent substitution of recursive notation"))
    | NHole _ ->
      let () = assert (List.is_empty args) in
      RCPatAtom (loc, None)
    | t -> error_invalid_pattern_notation loc
  in in_pat true

let rec intern_pat genv aliases pat =
  let intern_cstr_with_all_args loc c with_letin idslpl1 pl2 =
    let idslpl2 = List.map (intern_pat genv empty_alias) pl2 in
    let (ids',pll) = product_of_cases_patterns aliases.alias_ids (idslpl1@idslpl2) in
    let pl' = List.map (fun (asubst,pl) ->
      (asubst, PatCstr (loc,c,chop_params_pattern loc (fst c) pl with_letin,alias_of aliases))) pll in
    ids',pl' in
  match pat with
    | RCPatAlias (loc, p, id) ->
      let aliases' = merge_aliases aliases id in
      intern_pat genv aliases' p
    | RCPatCstr (loc, head, expl_pl, pl) ->
      if !oldfashion_patterns then
        let len = if List.is_empty expl_pl then Some (List.length pl) else None in
	let c,idslpl1 = find_constructor loc len head in
	let with_letin =
	  check_constructor_length genv loc c (List.length idslpl1 + List.length expl_pl) pl in
	intern_cstr_with_all_args loc c with_letin idslpl1 (expl_pl@pl)
      else
	let c,idslpl1 = find_constructor loc None head in
	let with_letin, pl2 =
	  add_implicits_check_constructor_length genv loc c (List.length idslpl1 + List.length expl_pl) pl in
	intern_cstr_with_all_args loc c with_letin idslpl1 (expl_pl@pl2)
    | RCPatAtom (loc, Some id) ->
      let aliases = merge_aliases aliases id in
      (aliases.alias_ids,[aliases.alias_map, PatVar (loc, alias_of aliases)])
    | RCPatAtom (loc, None) ->
      let { alias_ids = ids; alias_map = asubst; } = aliases in
      (ids, [asubst, PatVar (loc, alias_of aliases)])
    | RCPatOr (loc, pl) ->
      assert (not (List.is_empty pl));
      let pl' = List.map (intern_pat genv aliases) pl in
      let (idsl,pl') = List.split pl' in
      let ids = List.hd idsl in
      check_or_pat_variables loc ids (List.tl idsl);
      (ids,List.flatten pl')

let intern_cases_pattern genv env aliases pat =
  intern_pat genv aliases
    (drop_notations_pattern (function  ConstructRef _ -> () |_ -> raise Not_found) env pat)

let intern_ind_pattern genv env pat =
  let no_not =
    try
      drop_notations_pattern (function  (IndRef _ | ConstructRef _) -> () |_ -> raise Not_found) env pat
    with InternalizationError(loc,NotAConstructor _) -> error_bad_inductive_type loc
 in
  match no_not with
    | RCPatCstr (loc, head,expl_pl, pl) ->
      let c = (function IndRef ind -> ind
	|_ -> error_bad_inductive_type loc) head in
      let with_letin, pl2 = add_implicits_check_ind_length genv loc c
	(List.length expl_pl) pl in
      let idslpl1 = List.rev_map (intern_pat genv empty_alias) expl_pl in
      let idslpl2 = List.map (intern_pat genv empty_alias) pl2 in
      (with_letin,
       match product_of_cases_patterns [] (List.rev_append idslpl1 idslpl2) with
	 |_,[_,pl] ->
	   (c,chop_params_pattern loc c pl with_letin)
	 |_ -> error_bad_inductive_type loc)
    | x -> error_bad_inductive_type (raw_cases_pattern_expr_loc x)

(**********************************************************************)
(* Utilities for application                                          *)

let merge_impargs l args =
  let test x = function
  | (_, Some (_, y)) -> explicitation_eq x y
  | _ -> false
  in
  List.fold_right (fun a l ->
    match a with
      | (_,Some (_,(ExplByName id as x))) when
	  List.exists (test x) args -> l
      | _ -> a::l)
    l args

let check_projection isproj nargs r =
  match (r,isproj) with
  | GRef (loc, ref), Some _ ->
      (try
	let n = Recordops.find_projection_nparams ref + 1 in
	if not (Int.equal nargs n) then
	  user_err_loc (loc,"",str "Projection does not have the right number of explicit parameters.");
      with Not_found ->
	user_err_loc
	(loc,"",pr_global_env Id.Set.empty ref ++ str " is not a registered projection."))
  | _, Some _ -> user_err_loc (loc_of_glob_constr r, "", str "Not a projection.")
  | _, None -> ()

let get_implicit_name n imps =
  Some (Impargs.name_of_implicit (List.nth imps (n-1)))

let set_hole_implicit i b = function
  | GRef (loc,r) | GApp (_,GRef (loc,r),_) -> (loc,Evar_kinds.ImplicitArg (r,i,b),None)
  | GVar (loc,id) -> (loc,Evar_kinds.ImplicitArg (VarRef id,i,b),None)
  | _ -> anomaly (Pp.str "Only refs have implicits")

let exists_implicit_name id =
  List.exists (fun imp -> is_status_implicit imp && Id.equal id (name_of_implicit imp))

let extract_explicit_arg imps args =
  let rec aux = function
  | [] -> Id.Map.empty, []
  | (a,e)::l ->
      let (eargs,rargs) = aux l in
      match e with
      | None -> (eargs,a::rargs)
      | Some (loc,pos) ->
	  let id = match pos with
	  | ExplByName id ->
	      if not (exists_implicit_name id imps) then
		user_err_loc
		  (loc,"",str "Wrong argument name: " ++ pr_id id ++ str ".");
	      if Id.Map.mem id eargs then
		user_err_loc (loc,"",str "Argument name " ++ pr_id id
		++ str " occurs more than once.");
	      id
	  | ExplByPos (p,_id) ->
	      let id =
		try
		  let imp = List.nth imps (p-1) in
		  if not (is_status_implicit imp) then failwith "imp";
		  name_of_implicit imp
		with Failure _ (* "nth" | "imp" *) ->
		  user_err_loc
		    (loc,"",str"Wrong argument position: " ++ int p ++ str ".")
	      in
	      if Id.Map.mem id eargs then
		user_err_loc (loc,"",str"Argument at position " ++ int p ++
		  str " is mentioned more than once.");
	      id in
	  (Id.Map.add id (loc, a) eargs, rargs)
  in aux args

(**********************************************************************)
(* Main loop                                                          *)

let internalize globalenv env allow_patvar lvar c =
  let rec intern env = function
    | CRef ref as x ->
	let (c,imp,subscopes,l),_ =
	  intern_applied_reference intern env (Environ.named_context globalenv) lvar [] ref in
	(match intern_impargs c env imp subscopes l with
           | [] -> c
           | l -> GApp (constr_loc x, c, l))
    | CFix (loc, (locid,iddef), dl) ->
        let lf = List.map (fun ((_, id),_,_,_,_) -> id) dl in
        let dl = Array.of_list dl in
	let n =
	  try List.index0 Id.equal iddef lf
          with Not_found ->
	    raise (InternalizationError (locid,UnboundFixName (false,iddef)))
	in
	let idl_temp = Array.map
          (fun (id,(n,order),bl,ty,_) ->
	     let intern_ro_arg f =
	       let before, after = split_at_annot bl n in
	       let (env',rbefore) =
		 List.fold_left intern_local_binder (env,[]) before in
	       let ro = f (intern env') in
	       let n' = Option.map (fun _ -> List.length rbefore) n in
		 n', ro, List.fold_left intern_local_binder (env',rbefore) after
	     in
	     let n, ro, (env',rbl) =
	       match order with
	       | CStructRec ->
		   intern_ro_arg (fun _ -> GStructRec)
	       | CWfRec c ->
		   intern_ro_arg (fun f -> GWfRec (f c))
	       | CMeasureRec (m,r) ->
		   intern_ro_arg (fun f -> GMeasureRec (f m, Option.map f r))
	     in
	       ((n, ro), List.rev rbl, intern_type env' ty, env')) dl in
        let idl = Array.map2 (fun (_,_,_,_,bd) (a,b,c,env') ->
	     let env'' = List.fold_left_i (fun i en name -> 
					     let (_,bli,tyi,_) = idl_temp.(i) in
					     let fix_args = (List.map (fun (_,(na, bk, _, _)) -> (build_impls bk na)) bli) in
					       push_name_env lvar (impls_type_list ~args:fix_args tyi)
					    en (Loc.ghost, Name name)) 0 env' lf in
             (a,b,c,intern {env'' with tmp_scope = None} bd)) dl idl_temp in
	GRec (loc,GFix
	      (Array.map (fun (ro,_,_,_) -> ro) idl,n),
              Array.of_list lf,
              Array.map (fun (_,bl,_,_) -> List.map snd bl) idl,
              Array.map (fun (_,_,ty,_) -> ty) idl,
              Array.map (fun (_,_,_,bd) -> bd) idl)
    | CCoFix (loc, (locid,iddef), dl) ->
        let lf = List.map (fun ((_, id),_,_,_) -> id) dl in
        let dl = Array.of_list dl in
	let n =
          try List.index0 Id.equal iddef lf
          with Not_found ->
	    raise (InternalizationError (locid,UnboundFixName (true,iddef)))
	in
        let idl_tmp = Array.map
          (fun ((loc,id),bl,ty,_) ->
            let (env',rbl) =
              List.fold_left intern_local_binder (env,[]) bl in
            (List.rev rbl,
             intern_type env' ty,env')) dl in
	let idl = Array.map2 (fun (_,_,_,bd) (b,c,env') ->
	     let env'' = List.fold_left_i (fun i en name ->
					     let (bli,tyi,_) = idl_tmp.(i) in
					     let cofix_args =  List.map (fun (_, (na, bk, _, _)) -> (build_impls bk na)) bli in
	       push_name_env lvar (impls_type_list ~args:cofix_args tyi)
					    en (Loc.ghost, Name name)) 0 env' lf in
             (b,c,intern {env'' with tmp_scope = None} bd)) dl idl_tmp in
	GRec (loc,GCoFix n,
              Array.of_list lf,
              Array.map (fun (bl,_,_) -> List.map snd bl) idl,
              Array.map (fun (_,ty,_) -> ty) idl,
              Array.map (fun (_,_,bd) -> bd) idl)
    | CProdN (loc,[],c2) ->
        intern_type env c2
    | CProdN (loc,(nal,bk,ty)::bll,c2) ->
        iterate_prod loc env bk ty (CProdN (loc, bll, c2)) nal
    | CLambdaN (loc,[],c2) ->
        intern env c2
    | CLambdaN (loc,(nal,bk,ty)::bll,c2) ->
	iterate_lam loc (reset_tmp_scope env) bk ty (CLambdaN (loc, bll, c2)) nal
    | CLetIn (loc,na,c1,c2) ->
	let inc1 = intern (reset_tmp_scope env) c1 in
	GLetIn (loc, snd na, inc1,
          intern (push_name_env lvar (impls_term_list inc1) env na) c2)
    | CNotation (loc,"- _",([CPrim (_,Numeral p)],[],[]))
	when Bigint.is_strictly_pos p ->
	intern env (CPrim (loc,Numeral (Bigint.neg p)))
    | CNotation (_,"( _ )",([a],[],[])) -> intern env a
    | CNotation (loc,ntn,args) ->
        intern_notation intern env lvar loc ntn args
    | CGeneralization (loc,b,a,c) ->
        intern_generalization intern env lvar loc b a c
    | CPrim (loc, p) ->
	fst (Notation.interp_prim_token loc p (env.tmp_scope,env.scopes))
    | CDelimiters (loc, key, e) ->
	intern {env with tmp_scope = None;
		  scopes = find_delimiters_scope loc key :: env.scopes} e
    | CAppExpl (loc, (isproj,ref), args) ->
        let (f,_,args_scopes,_),args =
	  let args = List.map (fun a -> (a,None)) args in
	  intern_applied_reference intern env (Environ.named_context globalenv) lvar args ref in
	check_projection isproj (List.length args) f;
	(* Rem: GApp(_,f,[]) stands for @f *)
	GApp (loc, f, intern_args env args_scopes (List.map fst args))
    | CApp (loc, (isproj,f), args) ->
        let isproj,f,args = match f with
          (* Compact notations like "t.(f args') args" *)
          | CApp (_,(Some _,f), args') when not (Option.has_some isproj) -> isproj,f,args'@args
          (* Don't compact "(f args') args" to resolve implicits separately *)
          | _ -> isproj,f,args in
	let (c,impargs,args_scopes,l),args =
          match f with
            | CRef ref -> intern_applied_reference intern env (Environ.named_context globalenv) lvar args ref
            | CNotation (loc,ntn,([],[],[])) ->
                let c = intern_notation intern env lvar loc ntn ([],[],[]) in
                find_appl_head_data c, args
            | x -> (intern env f,[],[],[]), args in
	let args =
          intern_impargs c env impargs args_scopes (merge_impargs l args) in
	check_projection isproj (List.length args) c;
	(match c with
          (* Now compact "(f args') args" *)
	  | GApp (loc', f', args') -> GApp (Loc.merge loc' loc, f',args'@args)
	  | _ -> GApp (loc, c, args))
    | CRecord (loc, _, fs) ->
	let cargs =
	  sort_fields true loc fs
	    (fun k l -> CHole (loc, Some (Evar_kinds.QuestionMark (Evar_kinds.Define true)), None) :: l)
	  in
	begin
	  match cargs with
	    | None -> user_err_loc (loc, "intern", str"No constructor inference.")
	    | Some (n, constrname, args) ->
		let pars = List.make n (CHole (loc, None, None)) in
		let app = CAppExpl (loc, (None, constrname), List.rev_append pars args) in
	  intern env app
	end
    | CCases (loc, sty, rtnpo, tms, eqns) ->
      let as_in_vars = List.fold_left (fun acc (_,(na,inb)) ->
	Option.fold_left (fun x tt -> List.fold_right Id.Set.add (ids_of_cases_indtype tt) x)
	  (Option.fold_left (fun x (_,y) -> match y with | Name y' -> Id.Set.add y' x |_ -> x) acc na)
	  inb) Id.Set.empty tms in
      (* as, in & return vars *)
      let forbidden_vars = Option.cata free_vars_of_constr_expr as_in_vars rtnpo in
      let tms,ex_ids,match_from_in = List.fold_right
	(fun citm (inds,ex_ids,matchs) ->
	  let ((tm,ind),extra_id,match_td) = intern_case_item env forbidden_vars citm in
	  (tm,ind)::inds, Option.fold_right Id.Set.add extra_id ex_ids, List.rev_append match_td matchs)
	    tms ([],Id.Set.empty,[]) in
      let env' = Id.Set.fold
	(fun var bli -> push_name_env lvar (Variable,[],[],[]) bli (Loc.ghost,Name var))
	(Id.Set.union ex_ids as_in_vars) (reset_hidden_inductive_implicit_test env) in
      (* PatVars before a real pattern do not need to be matched *)
      let stripped_match_from_in = let rec aux = function
	|[] -> []
	|(_,PatVar _) :: q -> aux q
	|l -> l
				   in aux match_from_in in
        let rtnpo = match stripped_match_from_in with
	  | [] -> Option.map (intern_type env') rtnpo (* Only PatVar in "in" clauses *)
	  | l -> let thevars,thepats=List.split l in
		 Some (
		   GCases(Loc.ghost,Term.RegularStyle,Some (GSort (Loc.ghost,GType None)), (* "return Type" *)
			  List.map (fun id -> GVar (Loc.ghost,id),(Name id,None)) thevars, (* "match v1,..,vn" *)
			  [Loc.ghost,[],thepats, (* "|p1,..,pn" *)
			   Option.cata (intern_type env') (GHole(Loc.ghost,Evar_kinds.CasesType,None)) rtnpo; (* "=> P" is there were a P "=> _" else *)
			   Loc.ghost,[],List.make (List.length thepats) (PatVar(Loc.ghost,Anonymous)), (* "|_,..,_" *)
			   GHole(Loc.ghost,Evar_kinds.ImpossibleCase,None) (* "=> _" *)]))
	in
        let eqns' = List.map (intern_eqn (List.length tms) env) eqns in
	GCases (loc, sty, rtnpo, tms, List.flatten eqns')
    | CLetTuple (loc, nal, (na,po), b, c) ->
	let env' = reset_tmp_scope env in
	(* "in" is None so no match to add *)
        let ((b',(na',_)),_,_) = intern_case_item env' Id.Set.empty (b,(na,None)) in
        let p' = Option.map (fun u ->
	  let env'' = push_name_env lvar (Variable,[],[],[]) (reset_hidden_inductive_implicit_test env')
	    (Loc.ghost,na') in
	  intern_type env'' u) po in
        GLetTuple (loc, List.map snd nal, (na', p'), b',
                   intern (List.fold_left (push_name_env lvar (Variable,[],[],[])) (reset_hidden_inductive_implicit_test env) nal) c)
    | CIf (loc, c, (na,po), b1, b2) ->
      let env' = reset_tmp_scope env in
      let ((c',(na',_)),_,_) = intern_case_item env' Id.Set.empty (c,(na,None)) in (* no "in" no match to ad too *)
      let p' = Option.map (fun p ->
          let env'' = push_name_env lvar (Variable,[],[],[]) (reset_hidden_inductive_implicit_test env)
	    (Loc.ghost,na') in
	  intern_type env'' p) po in
        GIf (loc, c', (na', p'), intern env b1, intern env b2)
    | CHole (loc, k, solve) ->
        let k = match k with
        | None -> Evar_kinds.QuestionMark (Evar_kinds.Define true)
        | Some k -> k
        in
        let solve = match solve with
        | None -> None
        | Some gen ->
          let ((cvars, lvars), ntnvars) = lvar in
          let ntnvars = Id.Map.domain ntnvars in
          let lvars = Id.Set.union lvars cvars in
          let lvars = Id.Set.union lvars ntnvars in
          let lvars = Id.Set.union lvars env.ids in
          let ist = {
            Genintern.ltacvars = lvars;
            ltacrecvars = Id.Map.empty;
            genv = globalenv;
          } in
          let (_, glb) = Genintern.generic_intern ist gen in
          Some glb
        in
	GHole (loc, k, solve)
    | CPatVar (loc, n) when allow_patvar ->
	GPatVar (loc, n)
    | CPatVar (loc, _) ->
	raise (InternalizationError (loc,IllegalMetavariable))
    | CEvar (loc, n, l) ->
	GEvar (loc, n, Option.map (List.map (intern env)) l)
    | CSort (loc, s) ->
	GSort(loc,s)
    | CCast (loc, c1, c2) ->
        GCast (loc,intern env c1, Miscops.map_cast_type (intern_type env) c2)

  and intern_type env = intern (set_type_scope env)

  and intern_local_binder env bind =
    intern_local_binder_aux intern lvar env bind

  (* Expands a multiple pattern into a disjunction of multiple patterns *)
  and intern_multiple_pattern env n (loc,pl) =
    let idsl_pll =
      List.map (intern_cases_pattern globalenv {env with tmp_scope = None} empty_alias) pl in
    check_number_of_pattern loc n pl;
    product_of_cases_patterns [] idsl_pll

  (* Expands a disjunction of multiple pattern *)
  and intern_disjunctive_multiple_pattern env loc n mpl =
    assert (not (List.is_empty mpl));
    let mpl' = List.map (intern_multiple_pattern env n) mpl in
    let (idsl,mpl') = List.split mpl' in
    let ids = List.hd idsl in
    check_or_pat_variables loc ids (List.tl idsl);
    (ids,List.flatten mpl')

  (* Expands a pattern-matching clause [lhs => rhs] *)
  and intern_eqn n env (loc,lhs,rhs) =
    let eqn_ids,pll = intern_disjunctive_multiple_pattern env loc n lhs in
    (* Linearity implies the order in ids is irrelevant *)
    check_linearity lhs eqn_ids;
    let env_ids = List.fold_right Id.Set.add eqn_ids env.ids in
    List.map (fun (asubst,pl) ->
      let rhs = replace_vars_constr_expr asubst rhs in
      Id.Map.iter message_redundant_alias asubst;
      let rhs' = intern {env with ids = env_ids} rhs in
      (loc,eqn_ids,pl,rhs')) pll

  and intern_case_item env forbidden_names_for_gen (tm,(na,t)) =
    (*the "match" part *)
    let tm' = intern env tm in
    (* the "as" part *)
    let extra_id,na = match tm', na with
      | GVar (loc,id), None when not (Id.Map.mem id (snd lvar)) -> Some id,(loc,Name id)
      | GRef (loc, VarRef id), None -> Some id,(loc,Name id)
      | _, None -> None,(Loc.ghost,Anonymous)
      | _, Some (loc,na) -> None,(loc,na) in
    (* the "in" part *)
    let match_td,typ = match t with
    | Some t ->
	let tids = ids_of_cases_indtype t in
	let tids = List.fold_right Id.Set.add tids Id.Set.empty in
	let with_letin,(ind,l) = intern_ind_pattern globalenv {env with ids = tids; tmp_scope = None} t in
	let (mib,mip) = Inductive.lookup_mind_specif globalenv ind in
	let nparams = (List.length (mib.Declarations.mind_params_ctxt)) in
	(* for "in Vect n", we answer (["n","n"],[(loc,"n")])

	   for "in Vect (S n)", we answer ((match over "m", relevant branch is "S
	   n"), abstract over "m") = ([("m","S n")],[(loc,"m")]) where "m" is
	   generated from the canonical name of the inductive and outside of
	   {forbidden_names_for_gen} *)
	let (match_to_do,nal) =
	  let rec canonize_args case_rel_ctxt arg_pats forbidden_names match_acc var_acc =
	    let add_name l = function
	      |_,Anonymous -> l
	      |loc,(Name y as x) -> (y,PatVar(loc,x)) :: l in
	    match case_rel_ctxt,arg_pats with
	      (* LetIn in the rel_context *)
	      |(_,Some _,_)::t, l when not with_letin ->
		canonize_args t l forbidden_names match_acc ((Loc.ghost,Anonymous)::var_acc)
	      |[],[] ->
		(add_name match_acc na, var_acc)
	      |_::t,PatVar (loc,x)::tt ->
		canonize_args t tt forbidden_names
		  (add_name match_acc (loc,x)) ((loc,x)::var_acc)
	      |(cano_name,_,ty)::t,c::tt ->
		let fresh =
		  Namegen.next_name_away_with_default_using_types "iV" cano_name forbidden_names ty in
		canonize_args t tt (fresh::forbidden_names)
		  ((fresh,c)::match_acc) ((cases_pattern_loc c,Name fresh)::var_acc)
	      |_ -> assert false in
	  let _,args_rel =
	    List.chop nparams (List.rev mip.Declarations.mind_arity_ctxt) in
	  canonize_args args_rel l (Id.Set.elements forbidden_names_for_gen) [] [] in
	match_to_do, Some (cases_pattern_expr_loc t,ind,List.rev_map snd nal)
    | None ->
      [], None in
    (tm',(snd na,typ)), extra_id, match_td

  and iterate_prod loc2 env bk ty body nal =
    let env, bl = intern_assumption intern lvar env nal bk ty in
    it_mkGProd loc2 bl (intern_type env body)

  and iterate_lam loc2 env bk ty body nal =
    let env, bl = intern_assumption intern lvar env nal bk ty in
    it_mkGLambda loc2 bl (intern env body)

  and intern_impargs c env l subscopes args =
    let l = select_impargs_size (List.length args) l in
    let eargs, rargs = extract_explicit_arg l args in
    if !parsing_explicit then
      if Id.Map.is_empty eargs then intern_args env subscopes rargs
      else error "Arguments given by name or position not supported in explicit mode."
    else
    let rec aux n impl subscopes eargs rargs =
      let (enva,subscopes') = apply_scope_env env subscopes in
      match (impl,rargs) with
      | (imp::impl', rargs) when is_status_implicit imp ->
	  begin try
	    let id = name_of_implicit imp in
	    let (_,a) = Id.Map.find id eargs in
	    let eargs' = Id.Map.remove id eargs in
	    intern enva a :: aux (n+1) impl' subscopes' eargs' rargs
	  with Not_found ->
	  if List.is_empty rargs && Id.Map.is_empty eargs && not (maximal_insertion_of imp) then
            (* Less regular arguments than expected: complete *)
            (* with implicit arguments if maximal insertion is set *)
	    []
	  else
	    GHole (set_hole_implicit (n,get_implicit_name n l) (force_inference_of imp) c) ::
	      aux (n+1) impl' subscopes' eargs rargs
	  end
      | (imp::impl', a::rargs') ->
	  intern enva a :: aux (n+1) impl' subscopes' eargs rargs'
      | (imp::impl', []) ->
	  if not (Id.Map.is_empty eargs) then
	    (let (id,(loc,_)) = Id.Map.choose eargs in
	       user_err_loc (loc,"",str "Not enough non implicit \
	    arguments to accept the argument bound to " ++
		 pr_id id ++ str"."));
	  []
      | ([], rargs) ->
	  assert (Id.Map.is_empty eargs);
	  intern_args env subscopes rargs
    in aux 1 l subscopes eargs rargs

  and intern_args env subscopes = function
    | [] -> []
    | a::args ->
        let (enva,subscopes) = apply_scope_env env subscopes in
        (intern enva a) :: (intern_args env subscopes args)

  in
  try
    intern env c
  with
      InternalizationError (loc,e) ->
	user_err_loc (loc,"internalize",
	  explain_internalization_error e)

(**************************************************************************)
(* Functions to translate constr_expr into glob_constr                    *)
(**************************************************************************)

let extract_ids env =
  List.fold_right Id.Set.add
    (Termops.ids_of_rel_context (Environ.rel_context env))
    Id.Set.empty

let scope_of_type_kind = function
  | IsType -> Some Notation.type_scope
  | OfType typ -> compute_type_scope typ
  | WithoutTypeConstraint -> None

type ltac_sign = Id.Set.t * Id.Set.t

let empty_ltac_sign = (Id.Set.empty, Id.Set.empty)

let intern_gen kind env
               ?(impls=empty_internalization_env) ?(allow_patvar=false) ?(ltacvars=empty_ltac_sign)
               c =
  let tmp_scope = scope_of_type_kind kind in
  internalize env {ids = extract_ids env; unb = false;
		         tmp_scope = tmp_scope; scopes = [];
			 impls = impls}
    allow_patvar (ltacvars, Id.Map.empty) c

let intern_constr env c = intern_gen WithoutTypeConstraint env c

let intern_type env c = intern_gen IsType env c

let intern_pattern globalenv patt =
  try
    intern_cases_pattern globalenv {ids = extract_ids globalenv; unb = false;
				    tmp_scope = None; scopes = [];
				    impls = empty_internalization_env} empty_alias patt
  with
      InternalizationError (loc,e) ->
	user_err_loc (loc,"internalize",explain_internalization_error e)


(*********************************************************************)
(* Functions to parse and interpret constructions *)

(* All evars resolved *)

let interp_gen kind sigma env ?(impls=empty_internalization_env) c =
  let c = intern_gen kind ~impls env c in
  understand ~expected_type:kind sigma env c

let interp_constr sigma env ?(impls=empty_internalization_env) c =
  interp_gen WithoutTypeConstraint sigma env c

let interp_type sigma env ?(impls=empty_internalization_env) c =
  interp_gen IsType sigma env ~impls c

let interp_casted_constr sigma env ?(impls=empty_internalization_env) c typ =
  interp_gen (OfType typ) sigma env ~impls c

(* Not all evars expected to be resolved *)

let interp_open_constr sigma env c =
  understand_tcc sigma env (intern_constr env c)

(* Not all evars expected to be resolved and computation of implicit args *)

let interp_constr_evars_gen_impls evdref
    env ?(impls=empty_internalization_env) expected_type c =
  let c = intern_gen expected_type ~impls env c in
  let imps = Implicit_quantifiers.implicits_of_glob_constr ~with_products:(expected_type == IsType) c in
    understand_tcc_evars evdref env ~expected_type c, imps

let interp_constr_evars_impls evdref env ?(impls=empty_internalization_env) c =
  interp_constr_evars_gen_impls evdref env ~impls WithoutTypeConstraint c

let interp_casted_constr_evars_impls evdref env ?(impls=empty_internalization_env) c typ =
  interp_constr_evars_gen_impls evdref env ~impls (OfType typ) c

let interp_type_evars_impls evdref env ?(impls=empty_internalization_env) c =
  interp_constr_evars_gen_impls evdref env ~impls IsType c

(* Not all evars expected to be resolved, with side-effect on evars *)

let interp_constr_evars_gen evdref env ?(impls=empty_internalization_env) expected_type c =
  let c = intern_gen expected_type ~impls env c in
  understand_tcc_evars evdref env ~expected_type c

let interp_constr_evars evdref env ?(impls=empty_internalization_env) c =
  interp_constr_evars_gen evdref env WithoutTypeConstraint ~impls c

let interp_casted_constr_evars evdref env ?(impls=empty_internalization_env) c typ =
  interp_constr_evars_gen evdref env ~impls (OfType typ) c

let interp_type_evars evdref env ?(impls=empty_internalization_env) c =
  interp_constr_evars_gen evdref env IsType ~impls c

(* Miscellaneous *)

let intern_constr_pattern env ?(as_type=false) ?(ltacvars=empty_ltac_sign) c =
  let c = intern_gen (if as_type then IsType else WithoutTypeConstraint)
            ~allow_patvar:true ~ltacvars env c in
  pattern_of_glob_constr c

let interp_notation_constr ?(impls=empty_internalization_env) nenv a =
  let env = Global.env () in
  (* [vl] is intended to remember the scope of the free variables of [a] *)
  let vl = Id.Map.map (fun typ -> (ref None, typ)) nenv.ninterp_var_type in
  let c = internalize (Global.env()) {ids = extract_ids env; unb = false;
						tmp_scope = None; scopes = []; impls = impls}
    false (empty_ltac_sign, vl) a in
  (* Translate and check that [c] has all its free variables bound in [vars] *)
  let a = notation_constr_of_glob_constr nenv c in
  (* Splits variables into those that are binding, bound, or both *)
  (* binding and bound *)
  let out_scope = function None -> None,[] | Some (a,l) -> a,l in
  let vars = Id.Map.map (fun (sc, typ) -> (out_scope !sc, typ)) vl in
  (* Returns [a] and the ordered list of variables with their scopes *)
  vars, a

(* Interpret binders and contexts  *)

let interp_binder sigma env na t =
  let t = intern_gen IsType env t in
  let t' = locate_if_isevar (loc_of_glob_constr t) na t in
  understand ~expected_type:IsType sigma env t'

let interp_binder_evars evdref env na t =
  let t = intern_gen IsType env t in
  let t' = locate_if_isevar (loc_of_glob_constr t) na t in
  understand_tcc_evars evdref env ~expected_type:IsType t'

open Environ

let my_intern_constr env lvar acc c =
  internalize env acc false lvar c

let intern_context global_level env impl_env binders =
  try
  let lvar = (empty_ltac_sign, Id.Map.empty) in
  let lenv, bl = List.fold_left
	    (intern_local_binder_aux ~global_level (my_intern_constr env lvar) lvar)
	    ({ids = extract_ids env; unb = false;
	      tmp_scope = None; scopes = []; impls = impl_env}, []) binders in
  (lenv.impls, List.map snd bl)
  with InternalizationError (loc,e) ->
    user_err_loc (loc,"internalize", explain_internalization_error e)

let interp_rawcontext_evars evdref env bl =
  let (env, par, _, impls) =
    List.fold_left
      (fun (env,params,n,impls) (na, k, b, t) ->
	match b with
	    None ->
	      let t' = locate_if_isevar (loc_of_glob_constr t) na t in
	      let t =
                understand_tcc_evars evdref env ~expected_type:IsType t' in
	      let d = (na,None,t) in
	      let impls =
		if k == Implicit then
		  let na = match na with Name n -> Some n | Anonymous -> None in
		    (ExplByPos (n, na), (true, true, true)) :: impls
		else impls
	      in
		(push_rel d env, d::params, succ n, impls)
	  | Some b ->
	      let c = understand_judgment_tcc evdref env b in
	      let d = (na, Some c.uj_val, Termops.refresh_universes c.uj_type) in
		(push_rel d env, d::params, succ n, impls))
      (env,[],1,[]) (List.rev bl)
  in (env, par), impls

let interp_context_evars ?(global_level=false) ?(impl_env=empty_internalization_env) evdref env params =
  let int_env,bl = intern_context global_level env impl_env params in
  let x = interp_rawcontext_evars evdref env bl in
  int_env, x

