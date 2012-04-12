(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Flags
open Names
open Nameops
open Namegen
open Libnames
open Impargs
open Glob_term
open Pattern
open Pretyping
open Cases
open Topconstr
open Nametab
open Notation
open Inductiveops

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
  | Inductive of identifier list (* list of params *)
  | Recursive
  | Method
  | Variable

type var_internalization_data =
    (* type of the "free" variable, for coqdoc, e.g. while typing the
       constructor of JMeq, "JMeq" behaves as a variable of type Inductive *)
    var_internalization_type *
    (* impargs to automatically add to the variable, e.g. for "JMeq A a B b"
       in implicit mode, this is [A;B] and this adds (A:=A) and (B:=B) *)
    identifier list *
    (* signature of impargs of the variable *)
    Impargs.implicit_status list *
    (* subscopes of the args of the variable *)
    scope_name option list

type internalization_env =
    (var_internalization_data) Idmap.t

type glob_binder = (name * binding_kind * glob_constr option * glob_constr)

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
    Term.mkVar (let _ = Sign.lookup_named id ctx in id)
  with Not_found ->
    global_reference id

let global_reference_in_absolute_module dir id =
  constr_of_global (Nametab.global_of_path (Libnames.make_path dir id))

(**********************************************************************)
(* Internalization errors                                             *)

type internalization_error =
  | VariableCapture of identifier * identifier
  | WrongExplicitImplicit
  | IllegalMetavariable
  | NotAConstructor of reference
  | UnboundFixName of bool * identifier
  | NonLinearPattern of identifier
  | BadPatternsNumber of int * int
  | BadExplicitationNumber of explicitation * int option

exception InternalizationError of loc * internalization_error

let explain_variable_capture id id' =
  pr_id id ++ str " is dependent in the type of " ++ pr_id id' ++
  strbrk ": cannot interpret both of them with the same type"

let explain_wrong_explicit_implicit =
  str "Found an explicitly given implicit argument but was expecting" ++
  fnl () ++ str "a regular one"

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
  str "Expecting " ++ int n1 ++ str (plural n1 " pattern") ++
  str " but found " ++ int n2

let explain_bad_explicitation_number n po =
  match n with
  | ExplByPos (n,_id) ->
      let s = match po with
	| None -> str "a regular argument"
	| Some p -> int p in
      str "Bad explicitation number: found " ++ int n ++
      str" but was expecting " ++ s
  | ExplByName id ->
      let s = match po with
	| None -> str "a regular argument"
	| Some p -> (*pr_id (name_of_position p) in*) failwith "" in
      str "Bad explicitation name: found " ++ pr_id id ++
      str" but was expecting " ++ s

let explain_internalization_error e =
  let pp = match e with
  | VariableCapture (id,id') -> explain_variable_capture id id'
  | WrongExplicitImplicit -> explain_wrong_explicit_implicit
  | IllegalMetavariable -> explain_illegal_metavariable
  | NotAConstructor ref -> explain_not_a_constructor ref
  | UnboundFixName (iscofix,id) -> explain_unbound_fix_name iscofix id
  | NonLinearPattern id -> explain_non_linear_pattern id
  | BadPatternsNumber (n1,n2) -> explain_bad_patterns_number n1 n2
  | BadExplicitationNumber (n,po) -> explain_bad_explicitation_number n po in
  pp ++ str "."

let error_bad_inductive_type loc =
  user_err_loc (loc,"",str
    "This should be an inductive type applied to names or \"_\".")

let error_parameter_not_implicit loc =
  user_err_loc (loc,"", str
   "The parameters do not bind in patterns;" ++ spc () ++ str
    "they must be replaced by '_'.")

(**********************************************************************)
(* Pre-computing the implicit arguments and arguments scopes needed   *)
(* for interpretation *)

let parsing_explicit = ref false

let empty_internalization_env = Idmap.empty

let compute_explicitable_implicit imps = function
  | Inductive params ->
      (* In inductive types, the parameters are fixed implicit arguments *)
      let sub_impl,_ = list_chop (List.length params) imps in
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
  list_fold_left3
    (fun map id typ impl -> Idmap.add id (compute_internalization_data env ty typ impl) map)
    empty_internalization_env

(**********************************************************************)
(* Contracting "{ _ }" in notations *)

let rec wildcards ntn n =
  if n = String.length ntn then []
  else let l = spaces ntn (n+1) in if ntn.[n] = '_' then n::l else l
and spaces ntn n =
  if n = String.length ntn then []
  else if ntn.[n] = ' ' then wildcards ntn (n+1) else spaces ntn (n+1)

let expand_notation_string ntn n =
  let pos = List.nth (wildcards ntn 0) n in
  let hd = if pos = 0 then "" else String.sub ntn 0 pos in
  let tl =
    if pos = String.length ntn then ""
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
    | CPatNotation (_,"{ _ }",([a],[])) :: l ->
        ntn' := expand_notation_string !ntn' n;
        contract_squash n (a::l)
    | a :: l ->
        a::contract_squash (n+1) l in
  let l = contract_squash 0 l in
  (* side effect; don't inline *)
  !ntn',(l,ll)

type intern_env = {
  ids: Names.Idset.t;
  unb: bool;
  tmp_scope: Topconstr.tmp_scope_name option;
  scopes: Topconstr.scope_name list;
  impls: internalization_env }

(**********************************************************************)
(* Remembering the parsing scope of variables in notations            *)

let make_current_scope = function
  | (Some tmp_scope,(sc::_ as scopes)) when sc = tmp_scope -> scopes
  | (Some tmp_scope,scopes) -> tmp_scope::scopes
  | None,scopes -> scopes

let pr_scope_stack = function
  | [] -> str "the empty scope stack"
  | [a] -> str "scope " ++ str a
  | l -> str "scope stack " ++
      str "[" ++ prlist_with_sep pr_comma str l ++ str "]"

let error_inconsistent_scope loc id scopes1 scopes2 =
  user_err_loc (loc,"set_var_scope",
    pr_id id ++ str " is used both in " ++
    pr_scope_stack scopes1 ++ strbrk " and in " ++ pr_scope_stack scopes2)

let error_expect_constr_notation_type loc id =
  user_err_loc (loc,"",
    pr_id id ++ str " is bound in the notation to a term variable.")

let error_expect_binder_notation_type loc id =
  user_err_loc (loc,"",
    pr_id id ++
    str " is expected to occur in binding position in the right-hand side.")

let set_var_scope loc id istermvar env ntnvars =
  try
    let idscopes,typ = List.assoc id ntnvars in
    if !idscopes <> None &
      (* scopes have no effect on the interpretation of identifiers, hence
         we can tolerate having a variable occurring several times in
         different scopes: *) typ <> NtnInternTypeIdent &
      make_current_scope (Option.get !idscopes)
      <> make_current_scope (env.tmp_scope,env.scopes) then
	error_inconsistent_scope loc id
	  (make_current_scope (Option.get !idscopes))
	  (make_current_scope (env.tmp_scope,env.scopes))
    else
      idscopes := Some (env.tmp_scope,env.scopes);
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

let rec it_mkGProd loc2 env body =
  match env with
      (loc1, (na, bk, _, t)) :: tl -> it_mkGProd loc2 tl (GProd (join_loc loc1 loc2, na, bk, t, body))
    | [] -> body

let rec it_mkGLambda loc2 env body =
  match env with
      (loc1, (na, bk, _, t)) :: tl -> it_mkGLambda loc2 tl (GLambda (join_loc loc1 loc2, na, bk, t, body))
    | [] -> body

(**********************************************************************)
(* Utilities for binders                                              *)
let build_impls = function
  |Implicit -> (function
		  |Name id ->  Some (id, Impargs.Manual, (true,true))
		  |Anonymous -> anomaly "Anonymous implicit argument")
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
	| Name id -> glob_constr_of_aconstr loc (Reserve.find_reserved_type id)
	| Anonymous -> raise Not_found
      with Not_found -> GHole (loc, Evd.BinderType na))
  | x -> x

let reset_hidden_inductive_implicit_test env =
  { env with impls = Idmap.fold (fun id x ->
       let x = match x with
         | (Inductive _,b,c,d) -> (Inductive [],b,c,d)
         | x -> x
       in Idmap.add id x) env.impls Idmap.empty }

let check_hidden_implicit_parameters id impls =
  if Idmap.exists (fun _ -> function
    | (Inductive indparams,_,_,_) -> List.mem id indparams
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
      set_var_scope loc id false env (let (_,ntnvars) = lvar in ntnvars);
      if global_level then Dumpglob.dump_definition (loc,id) true "var"
      else Dumpglob.dump_binding loc id;
      {env with ids = Idset.add id env.ids; impls = Idmap.add id implargs env.impls}

let intern_generalized_binder ?(global_level=false) intern_type lvar
    env (loc, na) b b' t ty =
  let ids = (match na with Anonymous -> fun x -> x | Name na -> Idset.add na) env.ids in
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
  let bl = List.map (fun (id, loc) -> (loc, (Name id, b, None, GHole (loc, Evd.BinderType (Name id))))) fvs in
  let na = match na with
    | Anonymous ->
	if global_level then na
	else
	  let name =
	    let id =
	      match ty with
	      | CApp (_, (_, CRef (Ident (loc,id))), _) -> id
	      | _ -> id_of_string "H"
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
      (loc,(na,Explicit,Some(indef),GHole(loc,Evd.BinderType na)))::bl)

let intern_generalization intern env lvar loc bk ak c =
  let c = intern {env with unb = true} c in
  let fvs = Implicit_quantifiers.generalizable_vars_of_glob_constr ~bound:env.ids c in
  let env', c' =
    let abs =
      let pi =
	match ak with
	| Some AbsPi -> true
	| None when env.tmp_scope = Some Notation.type_scope
	    || List.mem Notation.type_scope env.scopes -> true
	| _ -> false
      in
	if pi then
	  (fun (id, loc') acc ->
	    GProd (join_loc loc' loc, Name id, bk, GHole (loc', Evd.BinderType (Name id)), acc))
	else
	  (fun (id, loc') acc ->
	    GLambda (join_loc loc' loc, Name id, bk, GHole (loc', Evd.BinderType (Name id)), acc))
    in
      List.fold_right (fun (id, loc as lid) (env, acc) ->
	let env' = push_name_env lvar (Variable,[],[],[]) env (loc, Name id) in
	  (env', abs lid acc)) fvs (env,c)
  in c'

(**********************************************************************)
(* Syntax extensions                                                  *)

let option_mem_assoc id = function
  | Some (id',c) -> id = id'
  | None -> false

let find_fresh_name renaming (terms,termlists,binders) id =
  let fvs1 = List.map (fun (_,(c,_)) -> free_vars_of_constr_expr c) terms in
  let fvs2 = List.flatten (List.map (fun (_,(l,_)) -> List.map free_vars_of_constr_expr l) termlists) in
  let fvs3 = List.map snd renaming in
  (* TODO binders *)
  let fvs = List.flatten (List.map Idset.elements (fvs1@fvs2)) @ fvs3 in
  next_ident_away id fvs

let traverse_binder (terms,_,_ as subst)
    (renaming,env)=
 function
 | Anonymous -> (renaming,env),Anonymous
 | Name id ->
  try
    (* Binders bound in the notation are considered first-order objects *)
    let _,na = coerce_to_name (fst (List.assoc id terms)) in
    (renaming,{env with ids = name_fold Idset.add na env.ids}), na
  with Not_found ->
    (* Binders not bound in the notation do not capture variables *)
    (* outside the notation (i.e. in the substitution) *)
    let id' = find_fresh_name renaming subst id in
    let renaming' = if id=id' then renaming else (id,id')::renaming in
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
  | GVar (_,id) as x -> if id = y then t else x
  | x -> map_glob_constr (subst_iterator y t) x

let subst_aconstr_in_glob_constr loc intern lvar subst infos c =
  let (terms,termlists,binders) = subst in
  let rec aux (terms,binderopt as subst') (renaming,env) c =
    let subinfos = renaming,{env with tmp_scope = None} in
    match c with
    | AVar id ->
      begin
	(* subst remembers the delimiters stack in the interpretation *)
	(* of the notations *)
	try
	  let (a,(scopt,subscopes)) = List.assoc id terms in
	  intern {env with tmp_scope = scopt;
		    scopes = subscopes @ env.scopes} a
	with Not_found ->
	try
	  GVar (loc,List.assoc id renaming)
	with Not_found ->
	  (* Happens for local notation joint with inductive/fixpoint defs *)
	  GVar (loc,id)
      end
    | AList (x,_,iter,terminator,lassoc) ->
      (try
        (* All elements of the list are in scopes (scopt,subscopes) *)
	let (l,(scopt,subscopes)) = List.assoc x termlists in
        let termin = aux subst' subinfos terminator in
	List.fold_right (fun a t ->
          subst_iterator ldots_var t
            (aux ((x,(a,(scopt,subscopes)))::terms,binderopt) subinfos iter))
            (if lassoc then List.rev l else l) termin
      with Not_found ->
          anomaly "Inconsistent substitution of recursive notation")
    | AHole (Evd.BinderType (Name id as na)) ->
      let na =
        try snd (coerce_to_name (fst (List.assoc id terms)))
        with Not_found -> na in
      GHole (loc,Evd.BinderType na)
    | ABinderList (x,_,iter,terminator) ->
      (try
        (* All elements of the list are in scopes (scopt,subscopes) *)
	let (bl,(scopt,subscopes)) = List.assoc x binders in
	let env,bl = List.fold_left (intern_local_binder_aux intern lvar) (env,[]) bl in
	let letins,bl = subordinate_letins [] bl in
        let termin = aux subst' (renaming,env) terminator in
	let res = List.fold_left (fun t binder ->
          subst_iterator ldots_var t
	    (aux (terms,Some(x,binder)) subinfos iter))
	  termin bl in
	make_letins letins res
      with Not_found ->
          anomaly "Inconsistent substitution of recursive notation")
    | AProd (Name id, AHole _, c') when option_mem_assoc id binderopt ->
        let (loc,(na,bk,t)),letins = snd (Option.get binderopt) in
	GProd (loc,na,bk,t,make_letins letins (aux subst' infos c'))
    | ALambda (Name id,AHole _,c') when option_mem_assoc id binderopt ->
        let (loc,(na,bk,t)),letins = snd (Option.get binderopt) in
	GLambda (loc,na,bk,t,make_letins letins (aux subst' infos c'))
    | t ->
      glob_constr_of_aconstr_with_binders loc (traverse_binder subst)
	(aux subst') subinfos t
  in aux (terms,None) infos c

let split_by_type ids =
  List.fold_right (fun (x,(scl,typ)) (l1,l2,l3) ->
    match typ with
    | NtnTypeConstr -> ((x,scl)::l1,l2,l3)
    | NtnTypeConstrList -> (l1,(x,scl)::l2,l3)
    | NtnTypeBinderList -> (l1,l2,(x,scl)::l3)) ids ([],[],[])

let make_subst ids l = List.map2 (fun (id,scl) a -> (id,(a,scl))) ids l

let intern_notation intern env lvar loc ntn fullargs =
  let ntn,(args,argslist,bll as fullargs) = contract_notation ntn fullargs in
  let ((ids,c),df) = interp_notation loc ntn (env.tmp_scope,env.scopes) in
  Dumpglob.dump_notation_location (ntn_loc loc fullargs ntn) ntn df;
  let ids,idsl,idsbl = split_by_type ids in
  let terms = make_subst ids args in
  let termlists = make_subst idsl argslist in
  let binders = make_subst idsbl bll in
  subst_aconstr_in_glob_constr loc intern lvar
    (terms,termlists,binders) ([],env) c

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
    let ty,expl_impls,impls,argsc = Idmap.find id genv.impls in
    let expl_impls = List.map
      (fun id -> CRef (Ident (loc,id)), Some (loc,ExplByName id)) expl_impls in
    let tys = string_of_ty ty in
    Dumpglob.dump_reference loc "<>" (string_of_id id) tys;
    GVar (loc,id), make_implicits_list impls, argsc, expl_impls
  with Not_found ->
  (* Is [id] bound in current term or is an ltac var bound to constr *)
  if Idset.mem id genv.ids or List.mem id ltacvars
  then
    GVar (loc,id), [], [], []
  (* Is [id] a notation variable *)

  else if List.mem_assoc id ntnvars
  then
    (set_var_scope loc id true genv ntnvars; GVar (loc,id), [], [], [])
  (* Is [id] the special variable for recursive notations *)
  else if ntnvars <> [] && id = ldots_var
  then
    GVar (loc,id), [], [], []
  else
  (* Is [id] bound to a free name in ltac (this is an ltac error message) *)
  try
    match List.assoc id unbndltacvars with
      | None -> user_err_loc (loc,"intern_var",
	  str "variable " ++ pr_id id ++ str " should be bound to a term.")
      | Some id0 -> Pretype_errors.error_var_not_found_loc loc id0
  with Not_found ->
    (* Is [id] a goal or section variable *)
    let _ = Sign.lookup_named id namedctx in
      try
	(* [id] a section variable *)
	(* Redundant: could be done in intern_qualid *)
	let ref = VarRef id in
	let impls = implicits_of_global ref in
	let scopes = find_arguments_scope ref in
	Dumpglob.dump_reference loc "<>" (string_of_qualid (Decls.variable_secpath id)) "var";
	GRef (loc, ref), impls, scopes, []
      with _ ->
	(* [id] a goal variable *)
	GVar (loc,id), [], [], []

let find_appl_head_data = function
  | GRef (_,ref) as x -> x,implicits_of_global ref,find_arguments_scope ref,[]
  | GApp (_,GRef (_,ref),l) as x
      when l <> [] & Flags.version_strictly_greater Flags.V8_2 ->
      let n = List.length l in
      x,List.map (drop_first_implicits n) (implicits_of_global ref),
      list_skipn_at_least n (find_arguments_scope ref),[]
  | x -> x,[],[],[]

let error_not_enough_arguments loc =
  user_err_loc (loc,"",str "Abbreviation is not applied enough.")

let check_no_explicitation l =
  let l = List.filter (fun (a,b) -> b <> None) l in
  if l <> [] then
    let loc = fst (Option.get (snd (List.hd l))) in
    user_err_loc
     (loc,"",str"Unexpected explicitation of the argument of an abbreviation.")

let dump_extended_global loc = function
  | TrueGlobal ref -> Dumpglob.add_glob loc ref
  | SynDef sp -> Dumpglob.add_glob_kn loc sp

let intern_extended_global_of_qualid (loc,qid) =
  try let r = Nametab.locate_extended qid in dump_extended_global loc r; r
  with Not_found -> error_global_not_found_loc loc qid

let intern_reference ref =
  Smartlocate.global_of_extended_global
    (intern_extended_global_of_qualid (qualid_of_reference ref))

(* Is it a global reference or a syntactic definition? *)
let intern_qualid loc qid intern env lvar args =
  match intern_extended_global_of_qualid (loc,qid) with
  | TrueGlobal ref ->
      GRef (loc, ref), args
  | SynDef sp ->
      let (ids,c) = Syntax_def.search_syntactic_definition sp in
      let nids = List.length ids in
      if List.length args < nids then error_not_enough_arguments loc;
      let args1,args2 = list_chop nids args in
      check_no_explicitation args1;
      let subst = make_subst ids (List.map fst args1) in
      subst_aconstr_in_glob_constr loc intern lvar (subst,[],[]) ([],env) c, args2

(* Rule out section vars since these should have been found by intern_var *)
let intern_non_secvar_qualid loc qid intern env lvar args =
  match intern_qualid loc qid intern env lvar args with
    | GRef (loc, VarRef id),_ -> error_global_not_found_loc loc qid
    | r -> r

let intern_applied_reference intern env namedctx lvar args = function
  | Qualid (loc, qid) ->
      let r,args2 = intern_qualid loc qid intern env lvar args in
      find_appl_head_data r, args2
  | Ident (loc, id) ->
      try intern_var env lvar namedctx loc id, args
      with Not_found ->
      let qid = qualid_of_ident id in
      try
	let r,args2 = intern_non_secvar_qualid loc qid intern env lvar args in
	find_appl_head_data r, args2
      with e ->
	(* Extra allowance for non globalizing functions *)
	if !interning_grammar || env.unb then
	  (GVar (loc,id), [], [], []),args
	else raise e

let interp_reference vars r =
  let (r,_,_,_),_ =
    intern_applied_reference (fun _ -> error_not_enough_arguments dummy_loc)
      {ids = Idset.empty; unb = false ;
       tmp_scope = None; scopes = []; impls = empty_internalization_env} []
      (vars,[]) [] r
  in r

let apply_scope_env env = function
  | [] -> {env with tmp_scope = None}, []
  | sc::scl -> {env with tmp_scope = sc}, scl

let rec simple_adjust_scopes n scopes =
  (* Note: they can be less scopes than arguments but also more scopes *)
  (* than arguments because extra scopes are used in the presence of *)
  (* coercions to funclass *)
  if n=0 then [] else match scopes with
  | [] -> None :: simple_adjust_scopes (n-1) []
  | sc::scopes -> sc :: simple_adjust_scopes (n-1) scopes

let find_remaining_scopes pl1 pl2 ref =
  snd (list_chop (List.length pl1)
    (simple_adjust_scopes (List.length pl1 + List.length pl2)
      (find_arguments_scope ref)))

(**********************************************************************)
(* Cases                                                              *)

let product_of_cases_patterns ids idspl =
  List.fold_right (fun (ids,pl) (ids',ptaill) ->
    (ids@ids',
     (* Cartesian prod of the or-pats for the nth arg and the tail args *)
     List.flatten (
       List.map (fun (subst,p) ->
	 List.map (fun (subst',ptail) -> (subst@subst',p::ptail)) ptaill) pl)))
    idspl (ids,[[],[]])

let simple_product_of_cases_patterns pl =
  List.fold_right (fun pl ptaill ->
    List.flatten (List.map (fun (subst,p) ->
      List.map (fun (subst',ptail) -> (subst@subst',p::ptail)) ptaill) pl))
    pl [[],[]]

(* Check linearity of pattern-matching *)
let rec has_duplicate = function
  | [] -> None
  | x::l -> if List.mem x l then (Some x) else has_duplicate l

let loc_of_lhs lhs =
 join_loc (fst (List.hd lhs)) (fst (list_last lhs))

let check_linearity lhs ids =
  match has_duplicate ids with
    | Some id ->
	raise (InternalizationError (loc_of_lhs lhs,NonLinearPattern id))
    | None ->
	()

(* Match the number of pattern against the number of matched args *)
let check_number_of_pattern loc n l =
  let p = List.length l in
  if n<>p then raise (InternalizationError (loc,BadPatternsNumber (n,p)))

let check_or_pat_variables loc ids idsl =
  if List.exists (fun ids' -> not (list_eq_set ids ids')) idsl then
    user_err_loc (loc, "", str
    "The components of this disjunctive pattern must bind the same variables.")

(** @param with_params says if _ for params were asked to the user.
    @return if letin are included *)
let check_constructor_length env loc cstr with_params pl pl0 =
  let nargs = Inductiveops.mis_constructor_nargs cstr in
  let n = List.length pl + List.length pl0 in
  if n = nargs then false else
    (n = (fst (Inductiveops.inductive_nargs (fst cstr))) + Inductiveops.constructor_nrealhyps cstr) ||
      (error_wrong_numarg_constructor_loc loc env cstr
	 (if with_params then nargs else nargs - (Inductiveops.inductive_nparams (fst cstr))))

let add_implicits_check_length nargs impls_st len_pl1 pl2 fail =
  let impl_list = if len_pl1 = 0
    then select_impargs_size (List.length pl2) impls_st
    else snd (list_chop len_pl1 (select_stronger_impargs impls_st)) in
  let remaining_args = List.fold_left (fun i x -> if is_status_implicit x then i else succ i) in
  let rec aux i = function
    |[],l -> let args_len = List.length l + List.length impl_list + len_pl1 in
	     if args_len = nargs then l
	     else fail (nargs - List.length impl_list + i)
    |imp::q,l when is_status_implicit imp -> CPatAtom(dummy_loc,None):: aux i (q,l)
    |il,[] -> fail (remaining_args (len_pl1+i) il)
    |_::q,hh::tt -> hh::aux (succ i) (q,tt)
  in aux 0 (impl_list,pl2)

let add_implicits_check_constructor_length env loc c idslpl1 pl2 =
  let nargs = Inductiveops.mis_constructor_nargs c in
  let len_pl1 = List.length idslpl1 in
  let impls_st = implicits_of_global (ConstructRef c) in
  add_implicits_check_length nargs impls_st len_pl1 pl2
    (error_wrong_numarg_constructor_loc loc env c)

(** @return if the letin are include *)
let check_ind_length env loc ind pl pl0 =
  let (mib,mip) = Global.lookup_inductive ind in
  let nparams = mib.Declarations.mind_nparams in
  let nargs = mip.Declarations.mind_nrealargs + nparams in
  let n = List.length pl + List.length pl0 in
  if n = nargs then false else
    let nparams', nrealargs' = inductive_nargs_env env ind in
    let nargs' = nrealargs' + nparams' in
    n = nargs' ||
      (error_wrong_numarg_inductive_loc loc env ind nargs)

let add_implicits_check_ind_length env loc c idslpl1 pl2 =
  let (mib,mip) = Global.lookup_inductive c in
  let nparams = mib.Declarations.mind_nparams in
  let nargs = mip.Declarations.mind_nrealargs + nparams in
  let len_pl1 = List.length idslpl1 in
  let impls_st = implicits_of_global (IndRef c) in
  add_implicits_check_length nargs impls_st len_pl1 pl2
    (error_wrong_numarg_inductive_loc loc env c)
(* Manage multiple aliases *)

  (* [merge_aliases] returns the sets of all aliases encountered at this
     point and a substitution mapping extra aliases to the first one *)
let merge_aliases (ids,asubst as _aliases) id =
  ids@[id], if ids=[] then asubst else (id, List.hd ids)::asubst

let alias_of = function
  | ([],_) -> Anonymous
  | (id::_,_) -> Name id

let message_redundant_alias (id1,id2) =
  if_warn msg_warning
    (str "Alias variable " ++ pr_id id1 ++ str " is merged with " ++ pr_id id2)

(* Expanding notations *)

let rec subst_pat_iterator y t (subst,p) = match p with
  | PatVar (_,id) as x ->
      if id = Name y then t else [subst,x]
  | PatCstr (loc,id,l,alias) ->
      let l' = List.map (fun a -> (subst_pat_iterator y t ([],a))) l in
      let pl = simple_product_of_cases_patterns l' in
      List.map (fun (subst',pl) -> subst'@subst,PatCstr (loc,id,pl,alias)) pl

(** @raise NotEnoughArguments only in the case of [subst_cases_pattern] thanks to
    preconditions in other cases. *)
let chop_params_pattern loc ind args with_letin =
  let nparams = if with_letin
    then fst (Inductiveops.inductive_nargs ind)
    else Inductiveops.inductive_nparams ind in
  if nparams > List.length args then error_not_enough_arguments loc;
  let params,args = list_chop nparams args in
  List.iter (function PatVar(_,Anonymous) -> ()
    | PatVar (loc',_) | PatCstr(loc',_,_,_) -> error_parameter_not_implicit loc') params;
  args

let subst_cases_pattern loc alias intern fullsubst env a =
  let rec aux alias (subst,substlist as fullsubst) = function
  | AVar id ->
      begin
	(* subst remembers the delimiters stack in the interpretation *)
	(* of the notations *)
	try
	  let (a,(scopt,subscopes)) = List.assoc id subst in
	    intern {env with scopes=subscopes@env.scopes;
		      tmp_scope = scopt} ([],[]) a
	with Not_found ->
	  if id = ldots_var then [], [[], PatVar (loc,Name id)] else
	  anomaly ("Unbound pattern notation variable: "^(string_of_id id))
	  (*
	  (* Happens for local notation joint with inductive/fixpoint defs *)
	  if aliases <> ([],[]) then
	    anomaly "Pattern notation without constructors";
	  [[id],[]], PatVar (loc,Name id)
	  *)
      end
  | ARef (ConstructRef c) ->
      ([],[[], PatCstr (loc,c, [], alias)])
  | AApp (ARef (ConstructRef cstr),args) ->
      let idslpll = List.map (aux Anonymous fullsubst) args in
      let ids',pll = product_of_cases_patterns [] idslpll in
      let pl' = List.map (fun (asubst,pl) ->
        asubst,PatCstr (loc,cstr,chop_params_pattern loc (fst cstr) pl false,alias)) pll in
	ids', pl'
  | AList (x,_,iter,terminator,lassoc) ->
      (try
        (* All elements of the list are in scopes (scopt,subscopes) *)
	let (l,(scopt,subscopes)) = List.assoc x substlist in
        let termin = aux Anonymous fullsubst terminator in
        let idsl,v =
	  List.fold_right (fun a (tids,t) ->
            let uids,u = aux Anonymous ((x,(a,(scopt,subscopes)))::subst,substlist) iter in
            let pll = List.map (subst_pat_iterator ldots_var t) u in
            tids@uids, List.flatten pll)
            (if lassoc then List.rev l else l) termin in
        idsl, List.map (fun ((asubst, pl) as x) ->
	  match pl with PatCstr (loc, c, pl, Anonymous) -> (asubst, PatCstr (loc, c, pl, alias)) | _ -> x) v
      with Not_found ->
          anomaly "Inconsistent substitution of recursive notation")
  | AHole _ -> ([],[[], PatVar (loc,Anonymous)])
  | t -> error_invalid_pattern_notation loc
  in aux alias fullsubst a

let subst_ind_pattern loc intern_ind_patt intern (subst,_ as fullsubst) env = function
  | AVar id ->
      begin
	(* subst remembers the delimiters stack in the interpretation *)
	(* of the notations *)
	try
	  let (a,(scopt,subscopes)) = List.assoc id subst in
	    intern_ind_patt {env with scopes=subscopes@env.scopes;
		      tmp_scope = scopt} a
	with Not_found ->
	  anomaly ("Unbound pattern notation variable: "^(string_of_id id))
      end
  | ARef (IndRef c) ->
      false, (c, [])
  | AApp (ARef (IndRef ind),args) ->
      let idslpll = List.map (subst_cases_pattern loc Anonymous intern fullsubst env) args in
      begin
	match product_of_cases_patterns [] idslpll with
	  |_,[_,pl]->
	    let pl' = chop_params_pattern loc ind pl false in
            false, (ind,pl')
	  |_ ->  error_invalid_pattern_notation loc
      end
  | t -> error_invalid_pattern_notation loc


(* Differentiating between constructors and matching variables *)
type pattern_qualid_kind =
  | ConstrPat of constructor * (identifier list *
      ((identifier * identifier) list * cases_pattern) list) list
  | VarPat of identifier

let find_at_head looked_for add_params ref f pats env =
  let (loc,qid) = qualid_of_reference ref in
  let gref =
    try locate_extended qid
    with Not_found -> raise (InternalizationError (loc,NotAConstructor ref)) in
  match gref with
    | SynDef sp ->
      let (vars,a) = Syntax_def.search_syntactic_definition sp in
      (match a with
	| ARef g ->
	  let cstr = looked_for g in
	  assert (vars=[]);
	  cstr,add_params cstr, pats
	| AApp (ARef g,args) ->
	  let cstr = looked_for g in
	  let nvars = List.length vars in
	  if List.length pats < nvars then error_not_enough_arguments loc;
	  let pats1,pats2 = list_chop nvars pats in
	  let subst = List.map2 (fun (id,scl) a -> (id,(a,scl))) vars pats1 in
	  let idspl1 = List.map (subst_cases_pattern loc Anonymous f (subst,[]) env) args in
	  cstr, idspl1, pats2
	| _ -> raise Not_found)

    | TrueGlobal r ->
      let rec unf = function
        | ConstRef cst ->
	  let v = Environ.constant_value (Global.env()) cst in
	  unf (global_of_constr v)
        | g ->
	  let cstr = looked_for g in
	  Dumpglob.add_glob loc r;
	  cstr, add_params cstr, pats
      in unf r

let find_constructor add_params =
  find_at_head (function ConstructRef cstr -> cstr |_ -> raise Not_found)
    (function (ind,_ as c) -> match add_params with
      |Some nb_args -> let nb = if nb_args = Inductiveops.constructor_nrealhyps c
	then fst (Inductiveops.inductive_nargs ind)
	else Inductiveops.inductive_nparams ind in
		       Util.list_make nb ([],[([],PatVar(dummy_loc,Anonymous))])
      |None -> [])


let find_pattern_variable = function
  | Ident (loc,id) -> id
  | Qualid (loc,_) as x -> raise (InternalizationError(loc,NotAConstructor x))

let maybe_constructor add_params ref f env =
  try
    let c,idspl1,pl2 = find_constructor add_params ref f [] env in
    assert (pl2 = []);
    ConstrPat (c,idspl1)
  with
    (* patt var does not exists globally *)
    | InternalizationError _ -> VarPat (find_pattern_variable ref)
    (* patt var also exists globally but does not satisfy preconditions *)
    | (Environ.NotEvaluableConst _ | Not_found) ->
      if_warn msg_warning (str "pattern " ++ pr_reference ref ++
			     str " is understood as a pattern variable");
      VarPat (find_pattern_variable ref)

let mustbe_constructor loc add_params ref f patl env =
  try find_constructor add_params ref f patl env
  with (Environ.NotEvaluableConst _ | Not_found) ->
    raise (InternalizationError (loc,NotAConstructor ref))

let mustbe_inductive loc ref f patl env =
  try find_at_head (function IndRef ind -> ind|_ -> raise Not_found) (function _ -> []) ref f patl env
  with (Environ.NotEvaluableConst _ | Not_found|
      InternalizationError (_,NotAConstructor _)) ->
    error_bad_inductive_type loc

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
		    | [] -> anomaly "Number of projections mismatch"
		    | (_, regular)::tm ->
		       let boolean = not regular in
		       if ConstRef name = global_reference_of_reference refer
		       then
			 if boolean && mode then
			   user_err_loc (loc, "", str"No local fields allowed in a record construction.")
			 else build_patt b tm (i + 1) (i, snd acc) (* we found it *)
		       else
			  build_patt b tm (if boolean&&mode then i else i + 1)
			    (if boolean && mode then acc
			     else fst acc, (i, ConstRef name) :: snd acc))
	      | None :: b-> (* we don't want anonymous fields *)
		 if mode then
		   user_err_loc (loc, "", str "This record contains anonymous fields.")
		 else build_patt b m (i+1) acc
		   (* anonymous arguments don't appear in m *)
	    in
	  let ind = record.Recordops.s_CONST in
	  try (* insertion of Constextern.reference_global *)
	    (record.Recordops.s_EXPECTEDPARAM,
	     Qualid (loc, shortest_qualid_of_global Idset.empty (ConstructRef ind)),
	     build_patt record.Recordops.s_PROJ record.Recordops.s_PROJKIND 1 (0,[]))
	  with Not_found -> anomaly "Environment corruption for records."
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
		       if glob_refer = a
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

let rec intern_cases_pattern genv env (ids,asubst as aliases) pat =
  let intern_pat = intern_cases_pattern genv in
  let intern_cstr_with_all_args loc c with_letin idslpl1 pl2 =
    let argscs2 = find_remaining_scopes idslpl1 pl2 (ConstructRef c) in
    let idslpl2 = List.map2 (fun x -> intern_pat {env with tmp_scope = x} ([],[])) argscs2 pl2 in
    let (ids',pll) = product_of_cases_patterns ids (idslpl1@idslpl2) in
    let pl' = List.map (fun (asubst,pl) ->
      (asubst, PatCstr (loc,c,chop_params_pattern loc (fst c) pl with_letin,alias_of aliases))) pll in
    ids',pl' in
  match pat with
  | CPatAlias (loc, p, id) ->
      let aliases' = merge_aliases aliases id in
      intern_pat env aliases' p
    | CPatRecord (loc, l) ->
	let sorted_fields = sort_fields false loc l (fun _ l -> (CPatAtom (loc, None))::l) in
	let self_patt =
	  match sorted_fields with
	    | None -> CPatAtom (loc, None)
	    | Some (_, head, pl) -> CPatCstr(loc, head, pl)
	  in
	intern_pat env aliases self_patt
  | CPatCstr (loc, head, pl) ->
      if !Topconstr.oldfashion_patterns then
	let c,idslpl1,pl2 = mustbe_constructor loc (Some (List.length pl)) head intern_pat pl env in
	let with_letin = check_constructor_length genv loc c false idslpl1 pl2 in
	intern_cstr_with_all_args loc c with_letin idslpl1 pl2
      else
	let c,idslpl1,pl2 = mustbe_constructor loc None head intern_pat pl env in
	let pl2' = add_implicits_check_constructor_length genv loc c idslpl1 pl2 in
	intern_cstr_with_all_args loc c false idslpl1 pl2'
  | CPatCstrExpl (loc, head, pl) ->
      let c,idslpl1,pl2 = mustbe_constructor loc None head intern_pat pl env in
      let with_letin = check_constructor_length genv loc c true idslpl1 pl2 in
      intern_cstr_with_all_args loc c with_letin idslpl1 pl2
  | CPatNotation (loc,"- _",([CPatPrim(_,Numeral p)],[]))
      when Bigint.is_strictly_pos p ->
      intern_pat env aliases (CPatPrim(loc,Numeral(Bigint.neg p)))
  | CPatNotation (_,"( _ )",([a],[])) ->
      intern_pat env aliases a
  | CPatNotation (loc, ntn, fullargs) ->
      let ntn,(args,argsl as fullargs) = contract_pat_notation ntn fullargs in
      let ((ids',c),df) = Notation.interp_notation loc ntn (env.tmp_scope,env.scopes) in
      let (ids',idsl',_) = split_by_type ids' in
      Dumpglob.dump_notation_location (patntn_loc loc fullargs ntn) ntn df;
      let subst = List.map2 (fun (id,scl) a -> (id,(a,scl))) ids' args in
      let substlist = List.map2 (fun (id,scl) a -> (id,(a,scl))) idsl' argsl in
      let ids'',pl =
	subst_cases_pattern loc (alias_of aliases) intern_pat (subst,substlist)
	  env c
      in ids@ids'', pl
  | CPatPrim (loc, p) ->
      let a = alias_of aliases in
      let (c,_) = Notation.interp_prim_token_cases_pattern loc p a
	(env.tmp_scope,env.scopes) in
      (ids,[asubst,c])
  | CPatDelimiters (loc, key, e) ->
      intern_pat {env with scopes=find_delimiters_scope loc key::env.scopes;
		    tmp_scope = None} aliases e
  | CPatAtom (loc, Some head) ->
      (match maybe_constructor (if !Topconstr.oldfashion_patterns then Some 0 else None)
	  head intern_pat env with
	 | ConstrPat (c,idspl) ->
	   if !Topconstr.oldfashion_patterns then
	     let with_letin = check_constructor_length genv loc c false idspl [] in
	     intern_cstr_with_all_args loc c with_letin idspl []
	   else
	     let pl2 = add_implicits_check_constructor_length genv loc c idspl [] in
	     intern_cstr_with_all_args loc c false idspl pl2
	 | VarPat id ->
	     let ids,asubst = merge_aliases aliases id in
	     (ids,[asubst, PatVar (loc,alias_of (ids,asubst))]))
  | CPatAtom (loc, None) ->
      (ids,[asubst, PatVar (loc,alias_of aliases)])
  | CPatOr (loc, pl) ->
      assert (pl <> []);
      let pl' = List.map (intern_pat env aliases) pl in
      let (idsl,pl') = List.split pl' in
      let ids = List.hd idsl in
      check_or_pat_variables loc ids (List.tl idsl);
      (ids,List.flatten pl')

let rec intern_ind_pattern genv env pat =
  let intern_ind_with_all_args loc c idslpl1 pl2 =
    let argscs2 = find_remaining_scopes idslpl1 pl2 (IndRef c) in
    let idslpl2 = List.map2 (fun x -> intern_cases_pattern genv {env with tmp_scope = x} ([],[])) argscs2 pl2 in
    match product_of_cases_patterns [] (idslpl1@idslpl2) with
      |_,[_,pl] ->
	(c,chop_params_pattern loc c pl false)
      |_ -> error_bad_inductive_type loc
  in
  match pat with
    | CPatCstr (loc, head, pl) ->
      let c,idslpl1,pl2 = mustbe_inductive loc head (intern_cases_pattern genv) pl env in
      let pl2' = add_implicits_check_ind_length genv loc c idslpl1 pl2 in
      false,intern_ind_with_all_args loc c idslpl1 pl2'
    | CPatCstrExpl (loc, head, pl) ->
      let c,idslpl1,pl2 = mustbe_inductive loc head (intern_cases_pattern genv) pl env in
      let with_letin = check_ind_length genv loc c idslpl1 pl2 in
      with_letin,intern_ind_with_all_args loc c idslpl1 pl2
    | CPatNotation (_,"( _ )",([a],[])) ->
      intern_ind_pattern genv env a
    | CPatNotation (loc, ntn, fullargs) ->
      let ntn,(args,argsl as fullargs) = contract_pat_notation ntn fullargs in
      let ((ids',c),df) = Notation.interp_notation loc ntn (env.tmp_scope,env.scopes) in
      let (ids',idsl',_) = split_by_type ids' in
      Dumpglob.dump_notation_location (patntn_loc loc fullargs ntn) ntn df;
      let subst = List.map2 (fun (id,scl) a -> (id,(a,scl))) ids' args in
      let substlist = List.map2 (fun (id,scl) a -> (id,(a,scl))) idsl' argsl in
	subst_ind_pattern loc (intern_ind_pattern genv) (intern_cases_pattern genv) (subst,substlist)
	  env c
    | CPatDelimiters (loc, key, e) ->
      intern_ind_pattern genv {env with scopes=find_delimiters_scope loc key::env.scopes;
	tmp_scope = None} e
    | CPatAtom (loc, Some head) ->
      let c,idslpl1,pl2 = mustbe_inductive loc head (intern_cases_pattern genv) [] env in
      let with_letin = check_ind_length genv loc c idslpl1 pl2 in
      with_letin,intern_ind_with_all_args loc c idslpl1 pl2
    | x -> error_bad_inductive_type (cases_pattern_expr_loc x)

(**********************************************************************)
(* Utilities for application                                          *)

let merge_impargs l args =
  List.fold_right (fun a l ->
    match a with
      | (_,Some (_,(ExplByName id as x))) when
	  List.exists (function (_,Some (_,y)) -> x=y | _ -> false) args -> l
      | _ -> a::l)
    l args

let check_projection isproj nargs r =
  match (r,isproj) with
  | GRef (loc, ref), Some _ ->
      (try
	let n = Recordops.find_projection_nparams ref + 1 in
	if nargs <> n then
	  user_err_loc (loc,"",str "Projection has not the right number of explicit parameters.");
      with Not_found ->
	user_err_loc
	(loc,"",pr_global_env Idset.empty ref ++ str " is not a registered projection."))
  | _, Some _ -> user_err_loc (loc_of_glob_constr r, "", str "Not a projection.")
  | _, None -> ()

let get_implicit_name n imps =
  Some (Impargs.name_of_implicit (List.nth imps (n-1)))

let set_hole_implicit i b = function
  | GRef (loc,r) | GApp (_,GRef (loc,r),_) -> (loc,Evd.ImplicitArg (r,i,b))
  | GVar (loc,id) -> (loc,Evd.ImplicitArg (VarRef id,i,b))
  | _ -> anomaly "Only refs have implicits"

let exists_implicit_name id =
  List.exists (fun imp -> is_status_implicit imp & id = name_of_implicit imp)

let extract_explicit_arg imps args =
  let rec aux = function
  | [] -> [],[]
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
	      if List.mem_assoc id eargs then
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
	      if List.mem_assoc id eargs then
		user_err_loc (loc,"",str"Argument at position " ++ int p ++
		  str " is mentioned more than once.");
	      id in
	  ((id,(loc,a))::eargs,rargs)
  in aux args

(**********************************************************************)
(* Main loop                                                          *)

let internalize sigma globalenv env allow_patvar lvar c =
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
	  try list_index0 iddef lf
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
        let idl = array_map2 (fun (_,_,_,_,bd) (a,b,c,env') ->
	     let env'' = list_fold_left_i (fun i en name -> 
					     let (_,bli,tyi,_) = idl_temp.(i) in
					     let fix_args = (List.map (fun (_,(na, bk, _, _)) -> (build_impls bk na)) bli) in
					       push_name_env lvar (impls_type_list ~args:fix_args tyi)
					    en (dummy_loc, Name name)) 0 env' lf in
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
          try list_index0 iddef lf
          with Not_found ->
	    raise (InternalizationError (locid,UnboundFixName (true,iddef)))
	in
        let idl_tmp = Array.map
          (fun ((loc,id),bl,ty,_) ->
            let (env',rbl) =
              List.fold_left intern_local_binder (env,[]) bl in
            (List.rev rbl,
             intern_type env' ty,env')) dl in
	let idl = array_map2 (fun (_,_,_,bd) (b,c,env') ->
	     let env'' = list_fold_left_i (fun i en name ->
					     let (bli,tyi,_) = idl_tmp.(i) in
					     let cofix_args =  List.map (fun (_, (na, bk, _, _)) -> (build_impls bk na)) bli in
	       push_name_env lvar (impls_type_list ~args:cofix_args tyi)
					    en (dummy_loc, Name name)) 0 env' lf in
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
          | CApp (_,(Some _,f), args') when isproj=None -> isproj,f,args'@args
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
	  | GApp (loc', f', args') -> GApp (join_loc loc' loc, f',args'@args)
	  | _ -> GApp (loc, c, args))
    | CRecord (loc, _, fs) ->
	let cargs =
	  sort_fields true loc fs
	    (fun k l -> CHole (loc, Some (Evd.QuestionMark (Evd.Define true))) :: l)
	  in
	begin
	  match cargs with
	    | None -> user_err_loc (loc, "intern", str"No constructor inference.")
	    | Some (n, constrname, args) ->
		let pars = list_make n (CHole (loc, None)) in
		let app = CAppExpl (loc, (None, constrname), List.rev_append pars args) in
	  intern env app
	end
    | CCases (loc, sty, rtnpo, tms, eqns) ->
      let as_in_vars = List.fold_left (fun acc (_,(na,inb)) ->
	Option.fold_left (fun x tt -> List.fold_right Idset.add (ids_of_cases_indtype tt) x)
	  (Option.fold_left (fun x (_,y) -> match y with | Name y' -> Idset.add y' x |_ -> x) acc na)
	  inb) Idset.empty tms in
      (* as, in & return vars *)
      let forbidden_vars = Option.cata Topconstr.free_vars_of_constr_expr as_in_vars rtnpo in
      let tms,ex_ids,match_from_in = List.fold_right
	(fun citm (inds,ex_ids,matchs) ->
	  let ((tm,ind),extra_id,match_td) = intern_case_item env forbidden_vars citm in
	  (tm,ind)::inds, Option.fold_right Idset.add extra_id ex_ids, List.rev_append match_td matchs)
	    tms ([],Idset.empty,[]) in
      let env' = Idset.fold
	(fun var bli -> push_name_env lvar (Variable,[],[],[]) bli (dummy_loc,Name var))
	(Idset.union ex_ids as_in_vars) (reset_hidden_inductive_implicit_test env) in
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
		   GCases(dummy_loc,Term.RegularStyle,Some (GSort (dummy_loc,GType None)), (* "return Type" *)
			  List.map (fun id -> GVar (dummy_loc,id),(Name id,None)) thevars, (* "match v1,..,vn" *)
			  [dummy_loc,[],thepats, (* "|p1,..,pn" *)
			   Option.cata (intern_type env') (GHole(dummy_loc,Evd.CasesType)) rtnpo; (* "=> P" is there were a P "=> _" else *)
			   dummy_loc,[],list_make (List.length thepats) (PatVar(dummy_loc,Anonymous)), (* "|_,..,_" *)
			   GHole(dummy_loc,Evd.CasesType) (* "=> _" *)]))
	in
        let eqns' = List.map (intern_eqn (List.length tms) env) eqns in
	GCases (loc, sty, rtnpo, tms, List.flatten eqns')
    | CLetTuple (loc, nal, (na,po), b, c) ->
	let env' = reset_tmp_scope env in
	(* "in" is None so no match to add *)
        let ((b',(na',_)),_,_) = intern_case_item env' Idset.empty (b,(na,None)) in
        let p' = Option.map (fun u ->
	  let env'' = push_name_env lvar (Variable,[],[],[]) (reset_hidden_inductive_implicit_test env')
	    (dummy_loc,na') in
	  intern_type env'' u) po in
        GLetTuple (loc, List.map snd nal, (na', p'), b',
                   intern (List.fold_left (push_name_env lvar (Variable,[],[],[])) (reset_hidden_inductive_implicit_test env) nal) c)
    | CIf (loc, c, (na,po), b1, b2) ->
      let env' = reset_tmp_scope env in
      let ((c',(na',_)),_,_) = intern_case_item env' Idset.empty (c,(na,None)) in (* no "in" no match to ad too *)
      let p' = Option.map (fun p ->
          let env'' = push_name_env lvar (Variable,[],[],[]) (reset_hidden_inductive_implicit_test env)
	    (dummy_loc,na') in
	  intern_type env'' p) po in
        GIf (loc, c', (na', p'), intern env b1, intern env b2)
    | CHole (loc, k) ->
	GHole (loc, match k with Some k -> k | None -> Evd.QuestionMark (Evd.Define true))
    | CPatVar (loc, n) when allow_patvar ->
	GPatVar (loc, n)
    | CPatVar (loc, _) ->
	raise (InternalizationError (loc,IllegalMetavariable))
    | CEvar (loc, n, l) ->
	GEvar (loc, n, Option.map (List.map (intern env)) l)
    | CSort (loc, s) ->
	GSort(loc,s)
    | CCast (loc, c1, CastConv (k, c2)) ->
	GCast (loc,intern env c1, CastConv (k, intern_type env c2))
    | CCast (loc, c1, CastCoerce) ->
	GCast (loc,intern env c1, CastCoerce)

  and intern_type env = intern (set_type_scope env)

  and intern_local_binder env bind =
    intern_local_binder_aux intern lvar env bind

  (* Expands a multiple pattern into a disjunction of multiple patterns *)
  and intern_multiple_pattern env n (loc,pl) =
    let idsl_pll =
      List.map (intern_cases_pattern globalenv {env with tmp_scope = None} ([],[])) pl in
    check_number_of_pattern loc n pl;
    product_of_cases_patterns [] idsl_pll

  (* Expands a disjunction of multiple pattern *)
  and intern_disjunctive_multiple_pattern env loc n mpl =
    assert (mpl <> []);
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
    let env_ids = List.fold_right Idset.add eqn_ids env.ids in
    List.map (fun (asubst,pl) ->
      let rhs = replace_vars_constr_expr asubst rhs in
      List.iter message_redundant_alias asubst;
      let rhs' = intern {env with ids = env_ids} rhs in
      (loc,eqn_ids,pl,rhs')) pll

  and intern_case_item env forbidden_names_for_gen (tm,(na,t)) =
    (*the "match" part *)
    let tm' = intern env tm in
    (* the "as" part *)
    let extra_id,na = match tm', na with
      | GVar (loc,id), None when Idset.mem id env.ids -> Some id,(loc,Name id)
      | GRef (loc, VarRef id), None -> Some id,(loc,Name id)
      | _, None -> None,(dummy_loc,Anonymous)
      | _, Some (loc,na) -> None,(loc,na) in
    (* the "in" part *)
    let match_td,typ = match t with
    | Some t ->
	let tids = ids_of_cases_indtype t in
	let tids = List.fold_right Idset.add tids Idset.empty in
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
		canonize_args t l forbidden_names match_acc ((dummy_loc,Anonymous)::var_acc)
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
	    list_chop nparams (List.rev mip.Declarations.mind_arity_ctxt) in
	  canonize_args args_rel l (Idset.elements forbidden_names_for_gen) [] [] in
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
      if eargs <> [] then
        error "Arguments given by name or position not supported in explicit mode."
      else
        intern_args env subscopes rargs
    else
    let rec aux n impl subscopes eargs rargs =
      let (enva,subscopes') = apply_scope_env env subscopes in
      match (impl,rargs) with
      | (imp::impl', rargs) when is_status_implicit imp ->
	  begin try
	    let id = name_of_implicit imp in
	    let (_,a) = List.assoc id eargs in
	    let eargs' = List.remove_assoc id eargs in
	    intern enva a :: aux (n+1) impl' subscopes' eargs' rargs
	  with Not_found ->
	  if rargs=[] & eargs=[] & not (maximal_insertion_of imp) then
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
	  if eargs <> [] then
	    (let (id,(loc,_)) = List.hd eargs in
	       user_err_loc (loc,"",str "Not enough non implicit \
	    arguments to accept the argument bound to " ++
		 pr_id id ++ str"."));
	  []
      | ([], rargs) ->
	  assert (eargs = []);
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
  List.fold_right Idset.add
    (Termops.ids_of_rel_context (Environ.rel_context env))
    Idset.empty

let intern_gen isarity sigma env
               ?(impls=empty_internalization_env) ?(allow_patvar=false) ?(ltacvars=([],[]))
               c =
  let tmp_scope =
    if isarity then Some Notation.type_scope else None in
    internalize sigma env {ids = extract_ids env; unb = false;
			   tmp_scope = tmp_scope; scopes = [];
			  impls = impls}
      allow_patvar (ltacvars, []) c

let intern_constr sigma env c = intern_gen false sigma env c

let intern_type sigma env c = intern_gen true sigma env c

let intern_pattern globalenv patt =
  try
    intern_cases_pattern globalenv {ids = extract_ids globalenv; unb = false;
				    tmp_scope = None; scopes = [];
				    impls = empty_internalization_env} ([],[]) patt
  with
      InternalizationError (loc,e) ->
	user_err_loc (loc,"internalize",explain_internalization_error e)


(*********************************************************************)
(* Functions to parse and interpret constructions *)

let interp_gen kind sigma env
               ?(impls=empty_internalization_env) ?(allow_patvar=false) ?(ltacvars=([],[]))
               c =
  let c = intern_gen (kind=IsType) ~impls ~allow_patvar ~ltacvars sigma env c in
    understand_gen kind sigma env c

let interp_constr sigma env c =
  interp_gen (OfType None) sigma env c

let interp_type sigma env ?(impls=empty_internalization_env) c =
  interp_gen IsType sigma env ~impls c

let interp_casted_constr sigma env ?(impls=empty_internalization_env) c typ =
  interp_gen (OfType (Some typ)) sigma env ~impls c

let interp_open_constr sigma env c =
  understand_tcc sigma env (intern_constr sigma env c)

let interp_open_constr_patvar sigma env c =
  let raw = intern_gen false sigma env c ~allow_patvar:true in
  let sigma = ref sigma in
  let evars = ref (Gmap.empty : (identifier,glob_constr) Gmap.t) in
  let rec patvar_to_evar r = match r with
    | GPatVar (loc,(_,id)) ->
	( try Gmap.find id !evars
	  with Not_found ->
	    let ev = Evarutil.e_new_evar sigma env (Termops.new_Type()) in
	    let ev = Evarutil.e_new_evar sigma env ev in
	    let rev = GEvar (loc,(fst (Term.destEvar ev)),None) (*TODO*) in
	    evars := Gmap.add id rev !evars;
	    rev
	)
    | _ -> map_glob_constr patvar_to_evar r in
  let raw = patvar_to_evar raw in
    understand_tcc !sigma env raw

let interp_constr_judgment sigma env c =
  understand_judgment sigma env (intern_constr sigma env c)

let interp_constr_evars_gen_impls ?evdref ?(fail_evar=true)
    env ?(impls=empty_internalization_env) kind c =
  let evdref =
    match evdref with
    | None -> ref Evd.empty
    | Some evdref -> evdref
  in
  let istype = kind = IsType in
  let c = intern_gen istype ~impls !evdref env c in
  let imps = Implicit_quantifiers.implicits_of_glob_constr ~with_products:istype c in
    understand_tcc_evars ~fail_evar evdref env kind c, imps

let interp_casted_constr_evars_impls ?evdref ?(fail_evar=true)
    env ?(impls=empty_internalization_env) c typ =
  interp_constr_evars_gen_impls ?evdref ~fail_evar env ~impls (OfType (Some typ)) c

let interp_type_evars_impls ?evdref ?(fail_evar=true) env ?(impls=empty_internalization_env) c =
  interp_constr_evars_gen_impls ?evdref ~fail_evar env IsType ~impls c

let interp_constr_evars_impls ?evdref ?(fail_evar=true) env ?(impls=empty_internalization_env) c =
  interp_constr_evars_gen_impls ?evdref ~fail_evar env (OfType None) ~impls c

let interp_constr_evars_gen evdref env ?(impls=empty_internalization_env) kind c =
  let c = intern_gen (kind=IsType) ~impls !evdref env c in
    understand_tcc_evars evdref env kind c

let interp_casted_constr_evars evdref env ?(impls=empty_internalization_env) c typ =
  interp_constr_evars_gen evdref env ~impls (OfType (Some typ)) c

let interp_type_evars evdref env ?(impls=empty_internalization_env) c =
  interp_constr_evars_gen evdref env IsType ~impls c

type ltac_sign = identifier list * unbound_ltac_var_map

let intern_constr_pattern sigma env ?(as_type=false) ?(ltacvars=([],[])) c =
  let c = intern_gen as_type ~allow_patvar:true ~ltacvars sigma env c in
  pattern_of_glob_constr c

let interp_aconstr ?(impls=empty_internalization_env) vars recvars a =
  let env = Global.env () in
  (* [vl] is intended to remember the scope of the free variables of [a] *)
  let vl = List.map (fun (id,typ) -> (id,(ref None,typ))) vars in
  let c = internalize Evd.empty (Global.env()) {ids = extract_ids env; unb = false;
						tmp_scope = None; scopes = []; impls = impls}
    false (([],[]),vl) a in
  (* Translate and check that [c] has all its free variables bound in [vars] *)
  let a = aconstr_of_glob_constr vars recvars c in
  (* Splits variables into those that are binding, bound, or both *)
  (* binding and bound *)
  let out_scope = function None -> None,[] | Some (a,l) -> a,l in
  let vars = List.map (fun (id,(sc,typ)) -> (id,(out_scope !sc,typ))) vl in
  (* Returns [a] and the ordered list of variables with their scopes *)
  vars, a

(* Interpret binders and contexts  *)

let interp_binder sigma env na t =
  let t = intern_gen true sigma env t in
  let t' = locate_if_isevar (loc_of_glob_constr t) na t in
  understand_type sigma env t'

let interp_binder_evars evdref env na t =
  let t = intern_gen true !evdref env t in
  let t' = locate_if_isevar (loc_of_glob_constr t) na t in
  understand_tcc_evars evdref env IsType t'

open Environ
open Term

let my_intern_constr sigma env lvar acc c =
  internalize sigma env acc false lvar c

let my_intern_type sigma env lvar acc c = my_intern_constr sigma env lvar (set_type_scope acc) c

let intern_context global_level sigma env impl_env params =
  try
  let lvar = (([],[]), []) in
  let lenv, bl = List.fold_left
	    (intern_local_binder_aux ~global_level (my_intern_constr sigma env lvar) lvar)
	    ({ids = extract_ids env; unb = false;
	      tmp_scope = None; scopes = []; impls = impl_env}, []) params in
  (lenv.impls, List.map snd bl)
  with InternalizationError (loc,e) ->
    user_err_loc (loc,"internalize", explain_internalization_error e)

let interp_rawcontext_gen understand_type understand_judgment env bl =
  let (env, par, _, impls) =
    List.fold_left
      (fun (env,params,n,impls) (na, k, b, t) ->
	match b with
	    None ->
	      let t' = locate_if_isevar (loc_of_glob_constr t) na t in
	      let t = understand_type env t' in
	      let d = (na,None,t) in
	      let impls =
		if k = Implicit then
		  let na = match na with Name n -> Some n | Anonymous -> None in
		    (ExplByPos (n, na), (true, true, true)) :: impls
		else impls
	      in
		(push_rel d env, d::params, succ n, impls)
	  | Some b ->
	      let c = understand_judgment env b in
	      let d = (na, Some c.uj_val, c.uj_type) in
		(push_rel d env, d::params, succ n, impls))
      (env,[],1,[]) (List.rev bl)
  in (env, par), impls

let interp_context_gen understand_type understand_judgment ?(global_level=false) ?(impl_env=empty_internalization_env) sigma env params =
  let int_env,bl = intern_context global_level sigma env impl_env params in
    int_env, interp_rawcontext_gen understand_type understand_judgment env bl

let interp_context ?(global_level=false) ?(impl_env=empty_internalization_env) sigma env params =
  interp_context_gen (understand_type sigma)
    (understand_judgment sigma) ~global_level ~impl_env sigma env params

let interp_context_evars ?(global_level=false) ?(impl_env=empty_internalization_env) evdref env params =
  interp_context_gen (fun env t -> understand_tcc_evars evdref env IsType t)
    (understand_judgment_tcc evdref) ~global_level ~impl_env !evdref env params

