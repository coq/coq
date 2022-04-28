(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open CAst
open Names
open Nameops
open Namegen
open Constr
open Context
open Libnames
open Globnames
open Impargs
open Glob_term
open Glob_ops
open Patternops
open Pretyping
open Structures
open Cases
open Constrexpr
open Constrexpr_ops
open Notation_term
open Notation_ops
open Notation
open Inductiveops
open Context.Rel.Declaration
open NumTok


(** constr_expr -> glob_constr translation:
    - it adds holes for implicit arguments
    - it replaces notations by their value (scopes stuff are here)
    - it recognizes global vars from local ones
    - it prepares pattern matching problems (a pattern becomes a tree
      where nodes are constructor/variable pairs and leafs are variables)

    All that at once, fasten your seatbelt!
*)

(* To interpret implicits and arg scopes of variables in inductive
   types and recursive definitions and of projection names in records *)

type var_internalization_type =
  | Inductive
  | Recursive
  | Method
  | Variable

type var_unique_id = string

let var_uid =
  let count = ref 0 in
  fun id -> incr count; Id.to_string id ^ ":" ^ string_of_int !count

type var_internalization_data =
    (* type of the "free" variable, for coqdoc, e.g. while typing the
       constructor of JMeq, "JMeq" behaves as a variable of type Inductive *)
    var_internalization_type *
    (* signature of impargs of the variable *)
    Impargs.implicit_status list *
    (* subscopes of the args of the variable *)
    scope_name option list *
    (* unique ID for coqdoc links *)
    var_unique_id

type internalization_env =
    (var_internalization_data) Id.Map.t

type ltac_sign = {
  ltac_vars : Id.Set.t;
  ltac_bound : Id.Set.t;
  ltac_extra : Genintern.Store.t;
}

let interning_grammar = ref false

(* Historically for parsing grammar rules, but in fact used only for
   translator, v7 parsing, and unstrict tactic internalization *)
let for_grammar f x =
  interning_grammar := true;
  let a = f x in
    interning_grammar := false;
    a

(**********************************************************************)
(* Internalization errors                                             *)

type internalization_error =
  | VariableCapture of Id.t * Id.t
  | IllegalMetavariable
  | NotAConstructor of qualid
  | UnboundFixName of bool * Id.t
  | NonLinearPattern of Id.t
  | BadPatternsNumber of int * int
  | NotAProjection of qualid
  | ProjectionsOfDifferentRecords of Structure.t * Structure.t

exception InternalizationError of internalization_error

let explain_variable_capture id id' =
  Id.print id ++ str " is dependent in the type of " ++ Id.print id' ++
  strbrk ": cannot interpret both of them with the same type"

let explain_illegal_metavariable =
  str "Metavariables allowed only in patterns"

let explain_not_a_constructor qid =
  str "Unknown constructor: " ++ pr_qualid qid

let explain_unbound_fix_name is_cofix id =
  str "The name" ++ spc () ++ Id.print id ++
  spc () ++ str "is not bound in the corresponding" ++ spc () ++
  str (if is_cofix then "co" else "") ++ str "fixpoint definition"

let explain_non_linear_pattern id =
  str "The variable " ++ Id.print id ++ str " is bound several times in pattern"

let explain_bad_patterns_number n1 n2 =
  str "Expecting " ++ int n1 ++ str (String.plural n1 " pattern") ++
  str " but found " ++ int n2

let inductive_of_record s =
  let inductive = GlobRef.IndRef (s.Structure.name) in
  Nametab.shortest_qualid_of_global Id.Set.empty inductive

let explain_field_not_a_projection field_id =
  pr_qualid field_id ++ str ": Not a projection"

let explain_projections_of_diff_records record1 record2 =
  let inductive1_id = inductive_of_record record1 in
  let inductive2_id = inductive_of_record record2 in
  str "This record contains fields of both " ++ pr_qualid inductive1_id ++
  str " and " ++ pr_qualid inductive2_id

let explain_internalization_error e =
  let pp = match e with
  | VariableCapture (id,id') -> explain_variable_capture id id'
  | IllegalMetavariable -> explain_illegal_metavariable
  | NotAConstructor ref -> explain_not_a_constructor ref
  | UnboundFixName (iscofix,id) -> explain_unbound_fix_name iscofix id
  | NonLinearPattern id -> explain_non_linear_pattern id
  | BadPatternsNumber (n1,n2) -> explain_bad_patterns_number n1 n2
  | NotAProjection field_id -> explain_field_not_a_projection field_id
  | ProjectionsOfDifferentRecords (inductive1_id, inductive2_id) ->
    explain_projections_of_diff_records inductive1_id inductive2_id
  in pp ++ str "."

let _ = CErrors.register_handler (function
    | InternalizationError e ->
      Some (explain_internalization_error e)
    | _ -> None)

let error_bad_inductive_type ?loc ?info () =
  user_err ?loc ?info (str
    "This should be an inductive type applied to patterns.")

let error_parameter_not_implicit ?loc =
  user_err ?loc  (str
   "The parameters do not bind in patterns;" ++ spc () ++ str
    "they must be replaced by '_'.")

let error_ldots_var ?loc =
  user_err ?loc  (str "Special token " ++ Id.print ldots_var ++
    str " is for use in the Notation command.")

(**********************************************************************)
(* Pre-computing the implicit arguments and arguments scopes needed   *)
(* for interpretation *)

let parsing_explicit = ref false

let empty_internalization_env = Id.Map.empty

let compute_internalization_data env sigma id ty typ impl =
  let impl = compute_implicits_with_manual env sigma typ (is_implicit_args()) impl in
  (ty, impl, compute_arguments_scope env sigma typ, var_uid id)

let compute_internalization_env env sigma ?(impls=empty_internalization_env) ty =
  List.fold_left3
    (fun map id typ impl -> Id.Map.add id (compute_internalization_data env sigma id ty typ impl) map)
    impls

let extend_internalization_data (r, impls, scopes, uid) impl scope =
  (r, impls@[impl], scopes@[scope], uid)

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
let contract_curly_brackets ntn (l,ll,bl,bll) =
  match ntn with
  | InCustomEntry _,_ -> ntn,(l,ll,bl,bll)
  | InConstrEntry, ntn ->
  let ntn' = ref ntn in
  let rec contract_squash n = function
    | [] -> []
    | { CAst.v = CNotation (None,(InConstrEntry,"{ _ }"),([a],[],[],[])) } :: l ->
        ntn' := expand_notation_string !ntn' n;
        contract_squash n (a::l)
    | a :: l ->
        a::contract_squash (n+1) l in
  let l = contract_squash 0 l in
  (* side effect; don't inline *)
  (InConstrEntry,!ntn'),(l,ll,bl,bll)

let contract_curly_brackets_pat ntn (l,ll) =
  match ntn with
  | InCustomEntry _,_ -> ntn,(l,ll)
  | InConstrEntry, ntn ->
  let ntn' = ref ntn in
  let rec contract_squash n = function
    | [] -> []
    | { CAst.v = CPatNotation (None,(InConstrEntry,"{ _ }"),([a],[]),[]) } :: l ->
        ntn' := expand_notation_string !ntn' n;
        contract_squash n (a::l)
    | a :: l ->
        a::contract_squash (n+1) l in
  let l = contract_squash 0 l in
  (* side effect; don't inline *)
  (InConstrEntry,!ntn'),(l,ll)

type local_univs = { bound : Univ.Level.t Id.Map.t; unb_univs : bool }

let empty_local_univs = { bound = Id.Map.empty; unb_univs = false }

type abstraction_kind = AbsLambda | AbsPi

type intern_env = {
  ids: Id.Set.t;
  unb: bool;
  local_univs: local_univs;
  tmp_scope: Notation_term.tmp_scope_name option;
  scopes: Notation_term.scope_name list;
  impls: internalization_env;
  binder_block_names: abstraction_kind option (* None = unknown *) option;
}

type pattern_intern_env = {
  pat_scopes: Notation_term.subscopes;
  (* ids = Some means accept local variables; this is useful for
     terms as patterns parsed as patterns in notations *)
  pat_ids: Id.Set.t option;
}

(**********************************************************************)
(* Remembering the parsing scope of variables in notations            *)

let make_current_scope tmp scopes = match tmp, scopes with
  | Some tmp_scope, (sc :: _) when String.equal sc tmp_scope -> scopes
  | Some tmp_scope, scopes -> tmp_scope :: scopes
  | None, scopes -> scopes

let pr_scope_stack begin_of_sentence l =
  let bstr x =
    if begin_of_sentence then str (CString.capitalize_ascii x) else str x in
  match l with
  | [] -> bstr "the empty scope stack"
  | [a] -> bstr "scope " ++ str a
  | l -> bstr "scope stack " ++
      str "[" ++ prlist_with_sep pr_comma str l ++ str "]"

let warn_inconsistent_scope =
  CWarnings.create ~name:"inconsistent-scopes" ~category:"syntax"
    (fun (id,scopes1,scopes2) ->
      (str "Argument " ++ Id.print id ++
       strbrk " was previously inferred to be in " ++
       pr_scope_stack false scopes1 ++
       strbrk " but is here used in " ++
       pr_scope_stack false scopes2 ++
       strbrk ". " ++
       pr_scope_stack true scopes1 ++
       strbrk " will be used at parsing time unless you override it by" ++
       strbrk " annotating the argument with an explicit scope of choice."))

let error_expect_binder_notation_type ?loc id =
  user_err ?loc
   (Id.print id ++
    str " is expected to occur in binding position in the right-hand side.")

let set_notation_var_scope ?loc id (tmp_scope,subscopes as scopes) ntnvars =
  try
    let _,idscopes,typ = Id.Map.find id ntnvars in
    match typ with
    | Notation_term.NtnInternTypeOnlyBinder -> error_expect_binder_notation_type ?loc id
    | Notation_term.NtnInternTypeAny principal ->
      match !idscopes with
      | None -> idscopes := Some scopes
      | Some (tmp_scope', subscopes') ->
        let s' = make_current_scope tmp_scope' subscopes' in
        let s = make_current_scope tmp_scope subscopes in
        if Option.is_empty principal && not (List.equal String.equal s' s) then
          warn_inconsistent_scope ?loc (id,s',s)
 with Not_found ->
    (* Not in a notation *)
    ()

let set_var_is_binder ?loc id ntnvars =
  try
    let used_as_binder,_,_ = Id.Map.find id ntnvars in
    used_as_binder := true
  with Not_found ->
    (* Not in a notation *)
    ()

let set_type_scope env = {env with tmp_scope = Notation.current_type_scope_name ()}

let reset_tmp_scope env = {env with tmp_scope = None}

let set_env_scopes env (scopt,subscopes) =
  {env with tmp_scope = scopt; scopes = subscopes @ env.scopes}

let env_for_pattern env =
  {pat_scopes = (env.tmp_scope, env.scopes); pat_ids = Some env.ids}

let mkGProd ?loc (na,bk,t) body = DAst.make ?loc @@ GProd (na, bk, t, body)
let mkGLambda ?loc (na,bk,t) body = DAst.make ?loc @@ GLambda (na, bk, t, body)

(**********************************************************************)
(* Utilities for binders                                              *)

let warn_shadowed_implicit_name =
  CWarnings.create ~name:"shadowed-implicit-name" ~category:"syntax"
    Pp.(fun na -> str "Making shadowed name of implicit argument accessible by position.")

let exists_name na l =
  match na with
  | Name id -> List.exists (function Some ((Name id',_,_),_,_) -> Id.equal id id' | _ -> false) l
  | _ -> false

let build_impls ?loc n bk na acc =
  let impl_status max =
    let na =
      if exists_name na acc then begin warn_shadowed_implicit_name ?loc na; Anonymous end
      else na in
    Some ((na,n,(*TODO, enhancement: compute dependency*)None),Manual,(max,true))
  in
  match bk with
  | NonMaxImplicit -> impl_status false :: acc
  | MaxImplicit -> impl_status true :: acc
  | Explicit -> None :: acc

let impls_binder_list =
  let rec aux acc n = function
    | (na,bk,None,_) :: binders -> aux (build_impls n bk na acc) (n+1) binders
    | (na,bk,Some _,_) :: binders -> aux acc n binders
    | [] -> (n,acc)
  in aux []

let impls_type_list n ?(args = []) =
  let rec aux acc n c = match DAst.get c with
    | GProd (na,bk,_,c) -> aux (build_impls n bk na acc) (n+1) c
    | _ -> List.rev acc
  in aux args n

let impls_term_list n ?(args = []) =
  let rec aux acc n c = match DAst.get c with
    | GLambda (na,bk,_,c) -> aux (build_impls n bk na acc) (n+1) c
    | GRec (fix_kind, nas, args, tys, bds) ->
       let nb = match fix_kind with |GFix (_, n) -> n | GCoFix n -> n in
       let n,acc' = List.fold_left (fun (n,acc) (na, bk, _, _) -> (n+1,build_impls n bk na acc)) (n,acc) args.(nb) in
       aux acc' n bds.(nb)
    |_ -> List.rev acc
  in aux args n

(* Check if in binder "(x1 x2 .. xn : t)", none of x1 .. xn-1 occurs in t *)
let rec check_capture ty = let open CAst in function
  | { loc; v = Name id } :: { v = Name id' } :: _ when occur_glob_constr id ty ->
    Loc.raise ?loc (InternalizationError (VariableCapture (id,id')))
  | _::nal ->
      check_capture ty nal
  | [] ->
      ()

(** Status of the internalizer wrt "Arguments" of names *)

let restart_no_binders env =
  { env with binder_block_names = None}
  (* Not in relation with the "Arguments" of a name *)

let restart_prod_binders env =
  { env with binder_block_names = Some (Some AbsPi) }
  (* In a position binding a type to a name *)

let restart_lambda_binders env =
  { env with binder_block_names = Some (Some AbsLambda) }
  (* In a position binding a body to a name *)

let switch_prod_binders env =
  match env.binder_block_names with
  | Some o when o <> Some AbsLambda -> restart_prod_binders env
  | _ -> restart_no_binders env
  (* In a position switching to a type *)

let switch_lambda_binders env =
  match env.binder_block_names with
  | Some o when o <> Some AbsPi -> restart_lambda_binders env
  | _ -> restart_no_binders env
  (* In a position switching to a term *)

let slide_binders env =
  match env.binder_block_names with
  | Some o when o <> Some AbsPi -> restart_prod_binders env
  | _ -> restart_no_binders env
  (* In a position of cast *)

let binder_status_fun = {
  no = (fun x -> x);
  restart_prod = on_snd restart_prod_binders;
  restart_lambda = on_snd restart_lambda_binders;
  switch_prod = on_snd switch_prod_binders;
  switch_lambda = on_snd switch_lambda_binders;
  slide = on_snd slide_binders;
}

(* [test_kind_strict] rules out pattern which refers to global other
   than constructors or variables; It is used in instances of notations *)

let test_kind_pattern_in_notation ?loc = function
  | GlobRef.ConstructRef _ -> ()
    (* We do not accept non constructors to be used as variables in
       patterns *)
  | GlobRef.ConstRef _ ->
    user_err ?loc (str "Found a constant while a pattern was expected.")
  | GlobRef.IndRef _ ->
    user_err ?loc (str "Found an inductive type while a pattern was expected.")
  | GlobRef.VarRef _ ->
    (* we accept a section variable name to be used as pattern variable *)
    raise Not_found

let test_kind_ident_in_notation ?loc = function
  | GlobRef.ConstructRef _ ->
    user_err ?loc (str "Found a constructor while a variable name was expected.")
  | GlobRef.ConstRef _ ->
    user_err ?loc (str "Found a constant while a variable name was expected.")
  | GlobRef.IndRef _ ->
    user_err ?loc (str "Found an inductive type while a variable name was expected.")
  | GlobRef.VarRef _ ->
    (* we accept a section variable name to be used as pattern variable *)
    raise Not_found

(* [test_kind_tolerant] allow global reference names to be used as pattern variables *)

let test_kind_tolerant ?loc = function
  | GlobRef.ConstructRef _ -> ()
  | GlobRef.ConstRef _ | GlobRef.IndRef _ | GlobRef.VarRef _ ->
    (* A non-constructor global reference in a pattern is seen as a variable *)
    raise Not_found

(**)

let locate_if_hole ?loc na c = match DAst.get c with
  | GHole (_,naming,arg) ->
      (try match na with
        | Name id -> glob_constr_of_notation_constr ?loc
                       (Reserve.find_reserved_type id)
        | Anonymous -> raise Not_found
      with Not_found -> DAst.make ?loc @@ GHole (Evar_kinds.BinderType na, naming, arg))
  | _ -> c

let pure_push_name_env (id,implargs) env =
  {env with
    ids = Id.Set.add id env.ids;
    impls = Id.Map.add id implargs env.impls;
  }

let push_name_env ntnvars implargs env =
  let open CAst in
  function
  | { loc; v = Anonymous } ->
      env
  | { loc; v = Name id } ->
      if Id.Map.is_empty ntnvars && Id.equal id ldots_var
        then error_ldots_var ?loc;
      set_var_is_binder ?loc id ntnvars;
      let uid = var_uid id in
      Dumpglob.dump_binding ?loc uid;
      pure_push_name_env (id,(Variable,implargs,[],uid)) env

let remember_binders_impargs env bl =
  List.map_filter (fun (na,_,_,_) ->
      match na with
      | Anonymous -> None
      | Name id -> Some (id,Id.Map.find id env.impls)) bl

let restore_binders_impargs env l =
  List.fold_right pure_push_name_env l env

let warn_ignoring_unexpected_implicit_binder_declaration =
  CWarnings.create ~name:"unexpected-implicit-declaration" ~category:"syntax"
    Pp.(fun () -> str "Ignoring implicit binder declaration in unexpected position.")

let check_implicit_meaningful ?loc k env =
  if k <> Explicit && env.binder_block_names = None then
    (warn_ignoring_unexpected_implicit_binder_declaration ?loc (); Explicit)
  else
    k

let intern_generalized_binder intern_type ntnvars
    env {loc;v=na} b' t ty =
  let ids = (match na with Anonymous -> fun x -> x | Name na -> Id.Set.add na) env.ids in
  let ty, ids' =
    if t then ty, ids
    else Implicit_quantifiers.implicit_application ids ty
  in
  let ty' = intern_type {env with ids = ids; unb = true} ty in
  let fvs = Implicit_quantifiers.generalizable_vars_of_glob_constr ~bound:ids ~allowed:ids' ty' in
  let env' = List.fold_left
    (fun env {loc;v=x} -> push_name_env ntnvars [](*?*) env (make ?loc @@ Name x))
    env fvs in
  let b' = check_implicit_meaningful ?loc b' env in
  let bl = List.map
    CAst.(map (fun id ->
      (Name id, MaxImplicit, DAst.make ?loc @@ GHole (Evar_kinds.BinderType (Name id), IntroAnonymous, None))))
    fvs
  in
  let na = match na with
    | Anonymous ->
      let id =
        match ty with
        | { v = CApp ({ v = CRef (qid,_) }, _) } when qualid_is_ident qid ->
          qualid_basename qid
        | _ -> default_non_dependent_ident
      in
      let ids' = List.fold_left (fun ids' lid -> Id.Set.add lid.CAst.v ids') ids' fvs in
      let id =
        Implicit_quantifiers.make_fresh ids' (Global.env ()) id
      in
      Name id
    | _ -> na
  in
  let impls = impls_type_list 1 ty' in
  (push_name_env ntnvars impls env' (make ?loc na),
   (make ?loc (na,b',ty')) :: List.rev bl)

let intern_assumption intern ntnvars env nal bk ty =
  let intern_type env = intern (restart_prod_binders (set_type_scope env)) in
  match bk with
  | Default k ->
      let ty = intern_type env ty in
      check_capture ty nal;
      let impls = impls_type_list 1 ty in
      List.fold_left
        (fun (env, bl) ({loc;v=na} as locna) ->
          let k = check_implicit_meaningful ?loc k env in
          (push_name_env ntnvars impls env locna,
           (make ?loc (na,k,locate_if_hole ?loc na ty))::bl))
        (env, []) nal
  | Generalized (b',t) ->
     let env, b = intern_generalized_binder intern_type ntnvars env (List.hd nal) b' t ty in
     env, b

let glob_local_binder_of_extended = DAst.with_loc_val (fun ?loc -> function
  | GLocalAssum (na,bk,t) -> (na,bk,None,t)
  | GLocalDef (na,c,Some t) -> (na,Explicit,Some c,t)
  | GLocalDef (na,c,None) ->
      let t = DAst.make ?loc @@ GHole(Evar_kinds.BinderType na,IntroAnonymous,None) in
      (na,Explicit,Some c,t)
  | GLocalPattern (_,_,_,_) ->
      Loc.raise ?loc (Stream.Error "pattern with quote not allowed here")
  )

let intern_cases_pattern_fwd = ref (fun _ -> failwith "intern_cases_pattern_fwd")

let intern_letin_binder intern ntnvars env (({loc;v=na} as locna),def,ty) =
  let term = intern (reset_tmp_scope (restart_lambda_binders env)) def in
  let ty = Option.map (intern (set_type_scope (restart_prod_binders env))) ty in
  let impls = impls_term_list 1 term in
  (push_name_env ntnvars impls env locna,
   (na,term,ty))

let intern_cases_pattern_as_binder intern test_kind ntnvars env bk (CAst.{v=p;loc} as pv) =
  let p,t = match p with
  | CPatCast (p, t) -> (p, Some t)
  | _ -> (pv, None) in
  let il,disjpat =
    let (il, subst_disjpat) = !intern_cases_pattern_fwd test_kind ntnvars (env_for_pattern (reset_tmp_scope env)) p in
    let substl,disjpat = List.split subst_disjpat in
    if not (List.for_all (fun subst -> Id.Map.equal Id.equal subst Id.Map.empty) substl) then
      user_err ?loc (str "Unsupported nested \"as\" clause.");
    il,disjpat
  in
  let na = alias_of_pat (List.hd disjpat) in
  let env = List.fold_right (fun {loc;v=id} env -> push_name_env ntnvars [] env (make ?loc @@ Name id)) il env in
  let ienv = Name.fold_right Id.Set.remove na env.ids in
  let id = Namegen.next_name_away_with_default "pat" na ienv in
  let na = make ?loc @@ Name id in
  let t = match t with
    | Some t -> t
    | None -> CAst.make ?loc @@ CHole(Some (Evar_kinds.BinderType na.v),IntroAnonymous,None) in
  let _, bl' = intern_assumption intern ntnvars env [na] (Default bk) t in
  let {v=(_,bk,t)} = List.hd bl' in
  env,((disjpat,il),id),na,bk,t

let intern_local_binder_aux intern ntnvars (env,bl) = function
  | CLocalAssum(nal,bk,ty) ->
      let env, bl' = intern_assumption intern ntnvars env nal bk ty in
      let bl' = List.map (fun {loc;v=(na,c,t)} -> DAst.make ?loc @@ GLocalAssum (na,c,t)) bl' in
      env, bl' @ bl
  | CLocalDef( {loc; v=na} as locna,def,ty) ->
     let env,(na,def,ty) = intern_letin_binder intern ntnvars env (locna,def,ty) in
     env, (DAst.make ?loc @@ GLocalDef (na,def,ty)) :: bl
  | CLocalPattern p ->
      let env, ((disjpat,il),id),na,bk,t = intern_cases_pattern_as_binder intern test_kind_tolerant ntnvars env Explicit p in
      (env, (DAst.make ?loc:p.CAst.loc @@ GLocalPattern((disjpat,List.map (fun x -> x.v) il),id,bk,t)) :: bl)

let intern_generalization intern env ntnvars loc bk c =
  let c = intern {env with unb = true} c in
  let fvs = Implicit_quantifiers.generalizable_vars_of_glob_constr ~bound:env.ids c in
  let env', c' =
    let abs =
      let pi =
        match Notation.current_type_scope_name () with
        | Some type_scope ->
          let is_type_scope = match env.tmp_scope with
            | None -> false
            | Some sc -> String.equal sc type_scope
          in
          is_type_scope ||
          String.List.mem type_scope env.scopes
        | None -> false
      in
        if pi then
          (fun {loc=loc';v=id} acc ->
            DAst.make ?loc:(Loc.merge_opt loc' loc) @@
            GProd (Name id, bk, DAst.make ?loc:loc' @@ GHole (Evar_kinds.BinderType (Name id), IntroAnonymous, None), acc))
        else
          (fun {loc=loc';v=id} acc ->
            DAst.make ?loc:(Loc.merge_opt loc' loc) @@
            GLambda (Name id, bk, DAst.make ?loc:loc' @@ GHole (Evar_kinds.BinderType (Name id), IntroAnonymous, None), acc))
    in
      List.fold_right (fun ({loc;v=id} as lid) (env, acc) ->
        let env' = push_name_env ntnvars [] env CAst.(make @@ Name id) in
          (env', abs lid acc)) fvs (env,c)
  in c'

let rec expand_binders ?loc mk bl c =
  match bl with
  | [] -> c
  | b :: bl ->
     match DAst.get b with
     | GLocalDef (n, b, oty) ->
        expand_binders ?loc mk bl (DAst.make ?loc @@ GLetIn (n, b, oty, c))
     | GLocalAssum (n, bk, t) ->
        expand_binders ?loc mk bl (mk ?loc (n,bk,t) c)
     | GLocalPattern ((disjpat,ids), id, bk, ty) ->
        let tm = DAst.make ?loc (GVar id) in
        (* Distribute the disjunctive patterns over the shared right-hand side *)
        let eqnl = List.map (fun pat -> CAst.make ?loc (ids,[pat],c)) disjpat in
        let c = DAst.make ?loc @@ GCases (LetPatternStyle, None, [tm,(Anonymous,None)], eqnl) in
        expand_binders ?loc mk bl (mk ?loc (Name id,Explicit,ty) c)

(**********************************************************************)
(* Syntax extensions                                                  *)

let check_not_notation_variable f ntnvars =
  (* Check bug #4690 *)
  match DAst.get f with
  | GVar id when Id.Map.mem id ntnvars ->
    user_err (str "Prefix @ is not applicable to notation variables.")
  | _ ->
     ()

let option_mem_assoc id = function
  | Some (id',c) -> Id.equal id id'
  | None -> false

let find_fresh_name renaming (terms,termlists,binders,binderlists) avoid id =
  let fold1 _ (c, _) accu = Id.Set.union (free_vars_of_constr_expr c) accu in
  let fold2 _ (l, _) accu =
    let fold accu c = Id.Set.union (free_vars_of_constr_expr c) accu in
    List.fold_left fold accu l
  in
  let fold3 _ x accu = Id.Set.add x accu in
  let fvs1 = Id.Map.fold fold1 terms avoid in
  let fvs2 = Id.Map.fold fold2 termlists fvs1 in
  let fvs3 = Id.Map.fold fold3 renaming fvs2 in
  (* TODO binders *)
  next_ident_away_from id (fun id -> Id.Set.mem id fvs3)

let is_patvar c =
  match DAst.get c with
  | PatVar _ -> true
  | _ -> false

let is_patvar_store store pat =
  match DAst.get pat with
  | PatVar na -> ignore(store (CAst.make ?loc:pat.loc na)); true
  | _ -> false

let out_patvar = CAst.map_with_loc (fun ?loc -> function
  | CPatAtom (Some qid) when qualid_is_ident qid ->
    Name (qualid_basename qid)
  | CPatAtom None -> Anonymous
  | _ -> assert false)

let canonize_type = function
  | None -> None
  | Some t as t' ->
    match DAst.get t with
    | GHole (Evar_kinds.BinderType _,IntroAnonymous,None) -> None
    | _ -> t'

let set_type ty1 ty2 =
  match canonize_type ty1, canonize_type ty2 with
  (* Not a meta-binding binder, we use the type given in the notation *)
  | _, None -> ty1
  (* A meta-binding binder meta-bound to a possibly-typed pattern *)
  (* the binder is supposed to come w/o an explicit type in the notation *)
  | None, Some _ -> ty2
  | Some ty1, Some t2 ->
    (* An explicitly typed meta-binding binder, not supposed to be a pattern; checked in interp_notation *)
    user_err ?loc:t2.CAst.loc Pp.(str "Unexpected type constraint in notation already providing a type constraint.")

let traverse_binder intern_pat ntnvars (terms,_,binders,_ as subst) avoid (renaming,env) na ty =
  match na with
  | Anonymous -> (renaming,env), None, Anonymous, Explicit, set_type ty None
  | Name id ->
  let store,get = set_temporary_memory () in
  let test_kind = test_kind_tolerant in
  try
    (* We instantiate binder name with patterns which may be parsed as terms *)
    let pat = coerce_to_cases_pattern_expr (fst (Id.Map.find id terms)) in
    let env,((disjpat,ids),id),na,bk,t = intern_pat test_kind ntnvars env Explicit pat in
    let pat, na = match disjpat with
    | [pat] when is_patvar_store store pat -> let na = get () in None, na
    | _ -> Some ((List.map (fun x -> x.v) ids,disjpat),id), na in
    (renaming,env), pat, na.v, bk, set_type ty (Some t)
  with Not_found ->
  try
    (* Trying to associate a pattern *)
    let (pat,bk),(onlyident,scopes) = Id.Map.find id binders in
    let env = set_env_scopes env scopes in
    if onlyident then
      (* Do not try to interpret a variable as a constructor *)
      let na = out_patvar pat in
      let env = push_name_env ntnvars [] env na in
      let ty' = DAst.make @@ GHole (Evar_kinds.BinderType na.CAst.v,IntroAnonymous,None) in
      (renaming,env), None, na.v, bk, set_type ty (Some ty')
    else
      (* Interpret as a pattern *)
      let env,((disjpat,ids),id),na,bk,t = intern_pat test_kind ntnvars env bk pat in
      let pat, na =
        match disjpat with
        | [pat] when is_patvar_store store pat -> let na = get () in None, na
        | _ -> Some ((List.map (fun x -> x.v) ids,disjpat),id), na in
      (renaming,env), pat, na.v, bk, set_type ty (Some t)
  with Not_found ->
    (* Binders not bound in the notation do not capture variables *)
    (* outside the notation (i.e. in the substitution) *)
    let id' = find_fresh_name renaming subst avoid id in
    let renaming = Id.Map.add id id' renaming in
    (renaming,env), None, Name id', Explicit, set_type ty None

type binder_action =
  | AddLetIn of lname * constr_expr * constr_expr option
  | AddTermIter of (constr_expr * subscopes) Names.Id.Map.t
  | AddPreBinderIter of Id.t * local_binder_expr (* A binder to be internalized *)
  | AddBinderIter of Id.t * extended_glob_local_binder (* A binder already internalized - used for generalized binders *)
  | AddNList (* Insert a ".. term .." block *)

let dmap_with_loc f n =
  CAst.map_with_loc (fun ?loc c -> f ?loc (DAst.get_thunk c)) n

let error_cannot_coerce_wildcard_term ?loc () =
  user_err ?loc Pp.(str "Cannot turn \"_\" into a term.")

let error_cannot_coerce_disjunctive_pattern_term ?loc () =
  user_err ?loc Pp.(str "Cannot turn a disjunctive pattern into a term.")

let terms_of_binders bl =
  let rec term_of_pat pt = dmap_with_loc (fun ?loc -> function
    | PatVar (Name id)   -> CRef (qualid_of_ident id, None)
    | PatVar (Anonymous) -> error_cannot_coerce_wildcard_term ?loc ()
    | PatCstr (c,l,_) ->
       let qid = qualid_of_path ?loc (Nametab.path_of_global (GlobRef.ConstructRef c)) in
       let hole = CAst.make ?loc @@ CHole (None,IntroAnonymous,None) in
       let params = List.make (Inductiveops.inductive_nparams (Global.env()) (fst c)) hole in
       CAppExpl ((qid,None),params @ List.map term_of_pat l)) pt in
  let rec extract_variables l = match l with
    | bnd :: l ->
      let loc = bnd.loc in
      begin match DAst.get bnd with
      | GLocalAssum (Name id,_,_) -> (CAst.make ?loc @@ CRef (qualid_of_ident ?loc id, None)) :: extract_variables l
      | GLocalDef (Name id,_,_) -> extract_variables l
      | GLocalDef (Anonymous,_,_)
      | GLocalAssum (Anonymous,_,_) -> user_err Pp.(str "Cannot turn \"_\" into a term.")
      | GLocalPattern (([u],_),_,_,_) -> term_of_pat u :: extract_variables l
      | GLocalPattern ((_,_),_,_,_) -> error_cannot_coerce_disjunctive_pattern_term ?loc ()
      end
    | [] -> [] in
  extract_variables bl

let flatten_generalized_binders_if_any y l =
  match List.rev l with
  | [] -> assert false
  | l ->
     (* if l not empty, this means we had a generalized binder *)
     let select_iter a =
       match DAst.get a with
       | GLocalAssum (Name id,_,_) when Id.equal id ldots_var -> AddNList
       | _ -> AddBinderIter (y,a) in
     List.map select_iter l

let flatten_binders bl =
  let dispatch = function
    | CLocalAssum (nal,bk,t) -> List.map (fun na -> CLocalAssum ([na],bk,t)) nal
    | a -> [a] in
  List.flatten (List.map dispatch bl)

let rec adjust_env env = function
  (* We need to adjust scopes, binder blocks ... to the env expected
     at the recursive occurrence; We do an underapproximation... *)
  | NProd (_,_,c) -> adjust_env (switch_prod_binders env) c
  | NLambda (_,_,c) -> adjust_env (switch_lambda_binders env) c
  | NLetIn (_,_,_,c) -> adjust_env env c
  | NVar id when Id.equal id ldots_var -> env
  | NCast (c,_,_) -> adjust_env env c
  | NApp _ -> restart_no_binders env
  | NVar _ | NRef _ | NHole _ | NCases _ | NLetTuple _ | NIf _
  | NRec _ | NSort _ | NProj _ | NInt _ | NFloat _ | NArray _
  | NList _ | NBinderList _ -> env (* to be safe, but restart should be ok *)

let instantiate_notation_constr loc intern intern_pat ntnvars subst infos c =
  let (terms,termlists,binders,binderlists) = subst in
  (* when called while defining a notation, avoid capturing the private binders
     of the expression by variables bound by the notation (see #3892) *)
  let avoid = Id.Map.domain ntnvars in
  let rec aux (terms,binderopt,iteropt as subst') (renaming,env) c =
    let subinfos = renaming,{env with tmp_scope = None} in
    match c with
    | NVar id when Id.equal id ldots_var ->
        let rec aux_letin env = function
        | [],terminator,_ -> aux (terms,None,None) (renaming,env) terminator
        | AddPreBinderIter (y,binder)::rest,terminator,iter ->
           let env,binders = intern_local_binder_aux intern ntnvars (adjust_env env iter,[]) binder in
           let binders = flatten_generalized_binders_if_any y binders in
           aux_letin env (binders@rest,terminator,iter)
        | AddBinderIter (y,binder)::rest,terminator,iter ->
           aux (terms,Some (y,binder),Some (rest,terminator,iter)) (renaming,env) iter
        | AddTermIter nterms::rest,terminator,iter ->
           aux (nterms,None,Some (rest,terminator,iter)) (renaming,env) iter
        | AddLetIn (na,c,t)::rest,terminator,iter ->
           let env,(na,c,t) = intern_letin_binder intern ntnvars (adjust_env env iter) (na,c,t) in
           DAst.make ?loc (GLetIn (na,c,t,aux_letin env (rest,terminator,iter)))
        | AddNList::rest,terminator,iter ->
           DAst.make ?loc (GApp (DAst.make ?loc (GVar ldots_var), [aux_letin env (rest,terminator,iter)]))
        in
        aux_letin env (Option.get iteropt)
    | NVar id -> subst_var subst' (renaming, env) id
    | NList (x,y,iter,terminator,revert) ->
      let l,(scopt,subscopes) =
        (* All elements of the list are in scopes (scopt,subscopes) *)
        try
          let l,scopes = Id.Map.find x termlists in
          (if revert then List.rev l else l),scopes
        with Not_found ->
        try
          let (bl,(scopt,subscopes)) = Id.Map.find x binderlists in
          let env,bl' = List.fold_left (intern_local_binder_aux intern ntnvars) (env,[]) bl in
          terms_of_binders (if revert then bl' else List.rev bl'),(None,[])
        with Not_found ->
          anomaly (Pp.str "Inconsistent substitution of recursive notation.") in
      let l = List.map (fun a -> AddTermIter ((Id.Map.add y (a,(scopt,subscopes)) terms))) l in
      aux (terms,None,Some (l,terminator,iter)) subinfos (NVar ldots_var)
    | NHole (knd, naming, arg) ->
      let knd = match knd with
      | Evar_kinds.BinderType (Name id as na) ->
        let na =
          try (coerce_to_name (fst (Id.Map.find id terms))).v
          with Not_found ->
          try Name (Id.Map.find id renaming)
          with Not_found -> na
        in
        Evar_kinds.BinderType na
      | _ -> knd
      in
      let arg = match arg with
      | None -> None
      | Some arg ->
        let mk_env id (c, scopes) map =
          let nenv = set_env_scopes env scopes in
          try
            let gc = intern nenv c in
            Id.Map.add id (gc, None) map
          with Nametab.GlobalizationError _ -> map
        in
        let mk_env' ((c,_bk), (onlyident,(tmp_scope,subscopes))) =
          let nenv = {env with tmp_scope; scopes = subscopes @ env.scopes} in
          let test_kind =
            if onlyident then test_kind_ident_in_notation
            else test_kind_pattern_in_notation in
          let _,((disjpat,_),_),_,_,_ty = intern_pat test_kind ntnvars nenv Explicit c in
          (* TODO: use cast? *)
          match disjpat with
          | [pat] -> (glob_constr_of_cases_pattern (Global.env()) pat, None)
          | _ -> error_cannot_coerce_disjunctive_pattern_term ?loc:c.loc ()
        in
        let terms = Id.Map.fold mk_env terms Id.Map.empty in
        let binders = Id.Map.map mk_env' binders in
        let bindings = Id.Map.fold Id.Map.add terms binders in
        Some (Genintern.generic_substitute_notation bindings arg)
      in
      DAst.make ?loc @@ GHole (knd, naming, arg)
    | NBinderList (x,y,iter,terminator,revert) ->
      (try
        (* All elements of the list are in scopes (scopt,subscopes) *)
        let (bl,(scopt,subscopes)) = Id.Map.find x binderlists in
        (* We flatten binders so that we can interpret them at substitution time *)
        let bl = flatten_binders bl in
        let bl = if revert then List.rev bl else bl in
        (* We isolate let-ins which do not contribute to the repeated pattern *)
        let l = List.map (function | CLocalDef (na,c,t) -> AddLetIn (na,c,t)
                                   | binder -> AddPreBinderIter (y,binder)) bl in
        (* We stack the binders to iterate or let-ins to insert *)
        aux (terms,None,Some (l,terminator,iter)) subinfos (NVar ldots_var)
      with Not_found ->
          anomaly (Pp.str "Inconsistent substitution of recursive notation."))
    | NProd (Name id, None, c') when option_mem_assoc id binderopt ->
        let binder = snd (Option.get binderopt) in
        expand_binders ?loc mkGProd [binder] (aux subst' (renaming,env) c')
    | NLambda (Name id, None, c') when option_mem_assoc id binderopt ->
        let binder = snd (Option.get binderopt) in
        expand_binders ?loc mkGLambda [binder] (aux subst' (renaming,env) c')
    | t ->
      glob_constr_of_notation_constr_with_binders ?loc
        (traverse_binder intern_pat ntnvars subst avoid) (aux subst') ~h:binder_status_fun subinfos t
  and subst_var (terms, binderopt, _terminopt) (renaming, env) id =
    (* subst remembers the delimiters stack in the interpretation *)
    (* of the notations *)
    try
      let (a,scopes) = Id.Map.find id terms in
      intern (set_env_scopes env scopes) a
    with Not_found ->
    try
      let (pat,bk),(onlyident,scopes) = Id.Map.find id binders in
      let env = set_env_scopes env scopes in
      let test_kind =
        if onlyident then test_kind_ident_in_notation
        else test_kind_pattern_in_notation in
      let env,((disjpat,ids),id),na,bk,_ty = intern_pat test_kind ntnvars env bk pat in
      (* TODO: use cast? *)
      match disjpat with
      | [pat] -> glob_constr_of_cases_pattern (Global.env()) pat
      | _ -> user_err Pp.(str "Cannot turn a disjunctive pattern into a term.")
    with Not_found ->
    try
      match binderopt with
      | Some (x,binder) when Id.equal x id ->
         let terms = terms_of_binders [binder] in
         assert (List.length terms = 1);
         intern env (List.hd terms)
      | _ -> raise Not_found
    with Not_found ->
    DAst.make ?loc (
    try
      GVar (Id.Map.find id renaming)
    with Not_found ->
      (* Happens for local notation joint with inductive/fixpoint defs *)
      GVar id)
  in aux (terms,None,None) infos c

(* Turning substitution coming from parsing and based on production
   into a substitution for interpretation and based on binding/constr
   distinction *)

let cases_pattern_of_id {loc;v=id} =
  CAst.make ?loc (CPatAtom (Some (qualid_of_ident ?loc id)))

let cases_pattern_of_name {loc;v=na} =
  let atom = match na with Name id -> Some (qualid_of_ident ?loc id) | Anonymous -> None in
  CAst.make ?loc (CPatAtom atom)

let split_by_type ids subst =
  let bind id scl l s =
    match l with
    | [] -> assert false
    | a::l -> l, Id.Map.add id (a,scl) s in
  let (terms,termlists,binders,binderlists),subst =
    List.fold_left (fun ((terms,termlists,binders,binderlists),(terms',termlists',binders',binderlists')) (id,((_,scl),typ)) ->
    match typ with
    | NtnTypeConstr ->
       let terms,terms' = bind id scl terms terms' in
       (terms,termlists,binders,binderlists),(terms',termlists',binders',binderlists')
    | NtnTypeBinder NtnBinderParsedAsConstr (AsNameOrPattern | AsStrictPattern) ->
       let a,terms = match terms with a::terms -> a,terms | _ -> assert false in
       let binders' = Id.Map.add id ((coerce_to_cases_pattern_expr a,Explicit),(false,scl)) binders' in
       (terms,termlists,binders,binderlists),(terms',termlists',binders',binderlists')
    | NtnTypeBinder NtnBinderParsedAsConstr AsIdent ->
       let a,terms = match terms with a::terms -> a,terms | _ -> assert false in
       let binders' = Id.Map.add id ((cases_pattern_of_id (coerce_to_id a),Explicit),(true,scl)) binders' in
       (terms,termlists,binders,binderlists),(terms',termlists',binders',binderlists')
    | NtnTypeBinder NtnBinderParsedAsConstr AsName ->
       let a,terms = match terms with a::terms -> a,terms | _ -> assert false in
       let binders' = Id.Map.add id ((cases_pattern_of_name (coerce_to_name a),Explicit),(true,scl)) binders' in
       (terms,termlists,binders,binderlists),(terms',termlists',binders',binderlists')
    | NtnTypeBinder (NtnParsedAsIdent | NtnParsedAsName | NtnParsedAsPattern _ | NtnParsedAsBinder as x) ->
       let onlyident = (x = NtnParsedAsIdent || x = NtnParsedAsName) in
       let binders,binders' = bind id (onlyident,scl) binders binders' in
       (terms,termlists,binders,binderlists),(terms',termlists',binders',binderlists')
    | NtnTypeConstrList ->
       let termlists,termlists' = bind id scl termlists termlists' in
       (terms,termlists,binders,binderlists),(terms',termlists',binders',binderlists')
    | NtnTypeBinderList ->
       let binderlists,binderlists' = bind id scl binderlists binderlists' in
       (terms,termlists,binders,binderlists),(terms',termlists',binders',binderlists'))
                   (subst,(Id.Map.empty,Id.Map.empty,Id.Map.empty,Id.Map.empty)) ids in
  assert (terms = [] && termlists = [] && binders = [] && binderlists = []);
  subst

let split_by_type_pat ?loc ids subst =
  let bind id (_,scopes) l s =
    match l with
    | [] -> assert false
    | a::l -> l, Id.Map.add id (a,scopes) s in
  let (terms,termlists),subst =
    List.fold_left (fun ((terms,termlists),(terms',termlists')) (id,(scl,typ)) ->
    match typ with
    | NtnTypeConstr | NtnTypeBinder _ ->
       let terms,terms' = bind id scl terms terms' in
       (terms,termlists),(terms',termlists')
    | NtnTypeConstrList ->
       let termlists,termlists' = bind id scl termlists termlists' in
       (terms,termlists),(terms',termlists')
    | NtnTypeBinderList -> error_invalid_pattern_notation ?loc ())
                   (subst,(Id.Map.empty,Id.Map.empty)) ids in
  assert (terms = [] && termlists = []);
  subst

let intern_notation intern env ntnvars loc ntn fullargs =
  (* Adjust to parsing of { } *)
  let ntn,fullargs = contract_curly_brackets ntn fullargs in
  (* Recover interpretation { } *)
  let ((ids,c),df) = interp_notation ?loc ntn (env.tmp_scope,env.scopes) in
  Dumpglob.dump_notation_location (ntn_loc ?loc fullargs ntn) ntn df;
  (* Dispatch parsing substitution to an interpretation substitution *)
  let subst = split_by_type ids fullargs in
  (* Instantiate the notation *)
  instantiate_notation_constr loc intern (intern_cases_pattern_as_binder intern) ntnvars subst (Id.Map.empty, env) c

(**********************************************************************)
(* Discriminating between bound variables and global references       *)

let string_of_ty = function
  | Inductive -> "ind"
  | Recursive -> "def"
  | Method -> "meth"
  | Variable -> "var"

let gvar (loc, id) us = match us with
  | None | Some [] -> DAst.make ?loc @@ GVar id
  | Some _ ->
    user_err ?loc  (str "Variable " ++ Id.print id ++
      str " cannot have a universe instance")

let intern_var env (ltacvars,ntnvars) namedctx loc id us =
  (* Is [id] a notation variable *)
  if Id.Map.mem id ntnvars then
    begin
      if not (Id.Map.mem id env.impls) then set_notation_var_scope ?loc id (env.tmp_scope,env.scopes) ntnvars;
      gvar (loc,id) us
    end
  else
  (* Is [id] registered with implicit arguments *)
  try
    let ty,_,_,uid = Id.Map.find id env.impls in
    let tys = string_of_ty ty in
    Dumpglob.dump_reference ?loc "<>" uid tys;
    gvar (loc,id) us
  with Not_found ->
  (* Is [id] bound in current term or is an ltac var bound to constr *)
  if Id.Set.mem id env.ids || Id.Set.mem id ltacvars.ltac_vars
  then
    gvar (loc,id) us
  else if Id.equal id ldots_var
  (* Is [id] the special variable for recursive notations? *)
  then if Id.Map.is_empty ntnvars
    then error_ldots_var ?loc
    else gvar (loc,id) us
  else if Id.Set.mem id ltacvars.ltac_bound then
    (* Is [id] bound to a free name in ltac (this is an ltac error message) *)
    user_err ?loc
     (str "variable " ++ Id.print id ++ str " should be bound to a term.")
  else
    (* Is [id] a goal or section variable *)
    let _ = Environ.lookup_named_ctxt id namedctx in
      try
        (* [id] a section variable *)
        (* Redundant: could be done in intern_qualid *)
        let ref = GlobRef.VarRef id in
        Dumpglob.dump_secvar ?loc id; (* this raises Not_found when not a section variable *)
        (* Someday we should stop relying on Dumglob raising exceptions *)
        DAst.make ?loc @@ GRef (ref, us)
      with e when CErrors.noncritical e ->
        (* [id] a goal variable *)
        gvar (loc,id) us

(**********************************************************************)
(* Locating reference, possibly via an abbreviation *)

let locate_reference qid =
  Smartlocate.global_of_extended_global (Nametab.locate_extended qid)

let is_global id =
  try
    let _ = locate_reference (qualid_of_ident id) in true
  with Not_found ->
    false

let dump_extended_global loc = function
  | TrueGlobal ref -> (*feedback_global loc ref;*) Dumpglob.add_glob ?loc ref
  | Abbrev sp -> Dumpglob.add_glob_kn ?loc sp

let intern_extended_global_of_qualid qid =
  let r = Nametab.locate_extended qid in dump_extended_global qid.CAst.loc r; r

let intern_reference qid =
  let r =
    try intern_extended_global_of_qualid qid
    with Not_found as exn ->
      let _, info = Exninfo.capture exn in
      Nametab.error_global_not_found ~info qid
  in
  Smartlocate.global_of_extended_global r

let intern_sort_name ~local_univs = function
  | CSProp -> GSProp
  | CProp -> GProp
  | CSet -> GSet
  | CRawType u -> GRawUniv u
  | CType qid ->
    let is_id = qualid_is_ident qid in
    let local = if not is_id then None
      else Id.Map.find_opt (qualid_basename qid) local_univs.bound
    in
    match local with
    | Some u -> GUniv u
    | None ->
      try GUniv (Univ.Level.make (Nametab.locate_universe qid))
      with Not_found ->
        if is_id && local_univs.unb_univs
        then GLocalUniv (CAst.make ?loc:qid.loc (qualid_basename qid))
        else
          CErrors.user_err Pp.(str "Undeclared universe " ++ pr_qualid qid ++ str".")

let intern_sort ~local_univs s =
  map_glob_sort_gen (List.map (on_fst (intern_sort_name ~local_univs))) s

let intern_instance ~local_univs us =
  Option.map (List.map (map_glob_sort_gen (intern_sort_name ~local_univs))) us

let intern_name_alias = function
  | { CAst.v = CRef(qid,u) } ->
      let r =
        try Some (intern_extended_global_of_qualid qid)
        with Not_found -> None
      in
      Option.bind r Smartlocate.global_of_extended_global |>
      Option.map (fun r -> r, intern_instance ~local_univs:empty_local_univs u)
  | _ -> None

let intern_field_ref qid =
  match
    Smartlocate.global_of_extended_global (intern_extended_global_of_qualid qid) |>
    Option.map (function
     | GlobRef.ConstRef c as x -> x, Structure.find_from_projection c
     | _ -> raise Not_found)
  with
  | exception Not_found ->
     Loc.raise ?loc:qid.loc (InternalizationError (NotAProjection qid))
  | None ->
     Loc.raise ?loc:qid.loc (InternalizationError (NotAProjection qid))
  | Some x -> x

(**********************************************************************)
(* Interpreting references                                            *)

let find_appl_head_data env (_,ntnvars) c =
  match DAst.get c with
  | GVar id when not (Id.Map.mem id ntnvars) ->
    (try
      let _,impls,argsc,_ = Id.Map.find id env.impls in
      make_implicits_list impls, argsc
     with Not_found -> [], [])
  | GRef (ref,_) ->
    let impls = implicits_of_global ref in
    let scopes = find_arguments_scope ref in
    impls, scopes
  | GApp (r, l) ->
    begin match DAst.get r with
    | GRef (ref,_) ->
      let n = List.length l in
      let impls = implicits_of_global ref in
      let scopes = find_arguments_scope ref in
      (if n = 0 then [] else List.map (drop_first_implicits n) impls),
       List.skipn_at_least n scopes
    | _ -> [],[]
    end
  | GProj ((cst,_), l, c) ->
      let ref = GlobRef.ConstRef cst in
      let n = List.length l + 1 in
      let impls = implicits_of_global ref in
      let scopes = find_arguments_scope ref in
      List.map (drop_first_implicits n) impls,
      List.skipn_at_least n scopes
  | _ -> [],[]

let error_not_enough_arguments ?loc =
  user_err ?loc  (str "Abbreviation is not applied enough.")

let check_no_explicitation l =
  let is_unset (a, b) = match b with None -> false | Some _ -> true in
  let l = List.filter is_unset l in
  match l with
  | [] -> ()
  | (_, None) :: _ -> assert false
  | (_, Some {loc}) :: _ ->
    user_err ?loc  (str"Unexpected explicitation of the argument of an abbreviation.")

let find_projection_data c =
  match DAst.get c with
  | GApp (r, l) ->
    begin match DAst.get r with
    | GRef (GlobRef.ConstRef cst,us) -> Some (cst, us, l, Structure.projection_nparams cst - List.length l)
    | _ -> None
    end
  | GRef (GlobRef.ConstRef cst,us) -> Some (cst, us, [], Structure.projection_nparams cst)
  | _ -> None

let glob_sort_of_level (level: glob_level) : glob_sort =
  match level with
  | UAnonymous {rigid} -> UAnonymous {rigid}
  | UNamed id -> UNamed [id,0]

(* Is it a global reference or a syntactic definition? *)
let intern_qualid ?(no_secvar=false) qid intern env ntnvars us args =
  let loc = qid.loc in
  match intern_extended_global_of_qualid qid with
  | TrueGlobal (GlobRef.VarRef _) when no_secvar ->
      (* Rule out section vars since these should have been found by intern_var *)
      raise Not_found
  | TrueGlobal ref -> (DAst.make ?loc @@ GRef (ref, us)), Some ref, args
  | Abbrev sp ->
      let (ids,c) = Abbreviation.search_abbreviation ?loc sp in
      let nids = List.length ids in
      if List.length args < nids then error_not_enough_arguments ?loc;
      let args1,args2 = List.chop nids args in
      check_no_explicitation args1;
      let subst = split_by_type ids (List.map fst args1,[],[],[]) in
      let infos = (Id.Map.empty, env) in
      let c = instantiate_notation_constr loc intern (intern_cases_pattern_as_binder intern) ntnvars subst infos c in
      let loc = c.loc in
      let err () =
        user_err ?loc  (str "Notation " ++ pr_qualid qid
                  ++ str " cannot have a universe instance,"
                  ++ str " its expanded head does not start with a reference")
      in
      let c = match us, DAst.get c with
      | None, _ -> c
      | Some _, GRef (ref, None) -> DAst.make ?loc @@ GRef (ref, us)
      | Some _, GApp (r, arg) ->
        let loc' = r.CAst.loc in
        begin match DAst.get r with
        | GRef (ref, None) ->
          DAst.make ?loc @@ GApp (DAst.make ?loc:loc' @@ GRef (ref, us), arg)
        | _ -> err ()
        end
      | Some [s], GSort (UAnonymous {rigid=true}) -> DAst.make ?loc @@ GSort (glob_sort_of_level s)
      | Some [_old_level], GSort _new_sort ->
        (* TODO: add old_level and new_sort to the error message *)
        user_err ?loc (str "Cannot change universe level of notation " ++ pr_qualid qid)
      | Some _, _ -> err ()
      in
      c, None, args2

let intern_qualid_for_pattern test_global intern_not qid pats =
  match intern_extended_global_of_qualid qid with
  | TrueGlobal g ->
    test_global g;
    (g, false, Some [], pats)
  | Abbrev kn ->
    let filter (vars,a) =
      match a with
      | NRef (g,_) ->
        (* Convention: do not deactivate implicit arguments and scopes for further arguments *)
        test_global g;
        let () = assert (List.is_empty vars) in
        Some (g, Some [], pats)
      | NApp (NRef (g,_),[]) -> (* special case: abbreviation for @Cstr deactivates implicit arguments *)
        test_global g;
        let () = assert (List.is_empty vars) in
        Some (g, None, pats)
      | NApp (NRef (g,_),args) ->
        (* Convention: do not deactivate implicit arguments and scopes for further arguments *)
        test_global g;
        let nvars = List.length vars in
        if List.length pats < nvars then error_not_enough_arguments ?loc:qid.loc;
        let pats1,pats2 = List.chop nvars pats in
        let subst = split_by_type_pat vars (pats1,[]) in
        let args = List.map (intern_not subst) args in
        Some (g, Some args, pats2)
      | _ -> None in
    match Abbreviation.search_filtered_abbreviation filter kn with
    | Some (g, pats1, pats2) -> (g, true, pats1, pats2)
    | None -> raise Not_found

let warn_nonprimitive_projection =
  CWarnings.create ~name:"nonprimitive-projection-syntax" ~category:"syntax" ~default:CWarnings.Disabled
    Pp.(fun f -> pr_qualid f ++ str " used as a primitive projection but is not one.")

let error_nonprojection_syntax ?loc qid =
  CErrors.user_err ?loc Pp.(pr_qualid qid ++ str" is not a projection.")

let check_applied_projection isproj realref qid =
  if isproj then
    let open GlobRef in
    let is_prim = match realref with
      | None | Some (IndRef _ | ConstructRef _ | VarRef _) -> false
      | Some (ConstRef c) ->
        if PrimitiveProjections.mem c then true
        else if Structure.is_projection c then false
        else error_nonprojection_syntax ?loc:qid.loc qid
        (* TODO check projargs, note we will need implicit argument info *)
    in
    if not is_prim then warn_nonprimitive_projection ?loc:qid.loc qid

let intern_applied_reference ~isproj intern env namedctx (_, ntnvars as lvar) us args qid =
  let loc = qid.CAst.loc in
  let us = intern_instance ~local_univs:env.local_univs us in
  if qualid_is_ident qid then
    try
      let res = intern_var env lvar namedctx loc (qualid_basename qid) us in
      check_applied_projection isproj None qid;
      res, args
    with Not_found ->
    try
      let res, realref, args2 = intern_qualid ~no_secvar:true qid intern env ntnvars us args in
      check_applied_projection isproj realref qid;
      res, args2
    with Not_found as exn ->
      (* Extra allowance for non globalizing functions *)
      if !interning_grammar || env.unb then
        (* check_applied_projection ?? *)
        gvar (loc,qualid_basename qid) us, args
      else
        let _, info = Exninfo.capture exn in
        Nametab.error_global_not_found ~info qid
  else
    try
      let res, realref, args2 = intern_qualid qid intern env ntnvars us args in
      check_applied_projection isproj realref qid;
      res, args2
    with Not_found as exn ->
        let _, info = Exninfo.capture exn in
        Nametab.error_global_not_found ~info qid

let interp_reference vars r =
  let r,_ =
    intern_applied_reference ~isproj:false (fun _ -> error_not_enough_arguments ?loc:None)
      {ids = Id.Set.empty; unb = false;
       local_univs = empty_local_univs;(* <- doesn't matter here *)
       tmp_scope = None; scopes = []; impls = empty_internalization_env;
       binder_block_names = None}
      Environ.empty_named_context_val
      (vars, Id.Map.empty) None [] r
  in r

(**********************************************************************)
(** {5 Cases }                                                        *)

(** Intermediate type common to the patterns of the "in" and of the
    "with" clause of "match" *)

type 'a raw_cases_pattern_expr_r =
  | RCPatAlias of 'a raw_cases_pattern_expr * lname
  | RCPatCstr  of GlobRef.t * 'a raw_cases_pattern_expr list
  | RCPatAtom  of (lident * (Notation_term.tmp_scope_name option * Notation_term.scope_name list)) option
  | RCPatOr    of 'a raw_cases_pattern_expr list
and 'a raw_cases_pattern_expr = ('a raw_cases_pattern_expr_r, 'a) DAst.t

(** {6 Elementary bricks } *)

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

let rec adjust_to_up l l' default =
  match l, l' with
  | l, [] -> []
  | [], l -> l
  | true::l, l' -> default :: adjust_to_up l l' default
  | false::l, y::l' -> y :: adjust_to_up l l' default

let rec adjust_to_down l l' default =
  match l, l' with
  | [], l -> []
  | true::l, l' -> adjust_to_down l l' default
  | false::l, [] -> default :: adjust_to_down l [] default
  | false::l, y::l' -> y :: adjust_to_down l l' default

(* @return the first variable that occurs twice in a pattern

naive n^2 algo *)
let rec has_duplicate = function
  | [] -> None
  | x::l -> if Id.List.mem x l then (Some x) else has_duplicate l

let loc_of_multiple_pattern pl =
 Loc.merge_opt (cases_pattern_expr_loc (List.hd pl)) (cases_pattern_expr_loc (List.last pl))

let loc_of_lhs lhs =
 Loc.merge_opt (loc_of_multiple_pattern (List.hd lhs)) (loc_of_multiple_pattern (List.last lhs))

let check_linearity lhs ids =
  match has_duplicate ids with
    | Some id ->
      let loc = loc_of_lhs lhs in
      Loc.raise ?loc (InternalizationError (NonLinearPattern id))
    | None ->
        ()

(* Match the number of pattern against the number of matched args *)
let check_number_of_pattern loc n l =
  let p = List.length l in
  if not (Int.equal n p) then
    Loc.raise ?loc (InternalizationError (BadPatternsNumber (n,p)))

let check_or_pat_variables loc ids idsl =
  let eq_id {v=id} {v=id'} = Id.equal id id' in
  (* Collect remaining patterns which do not have the same variables as the first pattern *)
  let idsl = List.filter (fun ids' -> not (List.eq_set eq_id ids ids')) idsl in
  match idsl with
  | ids'::_ ->
    (* Look for an [id] which is either in [ids] and not in [ids'] or in [ids'] and not in [ids] *)
    let ids'' = List.subtract eq_id ids ids' in
    let ids'' = if ids'' = [] then List.subtract eq_id ids' ids else ids'' in
    user_err ?loc
      (strbrk "The components of this disjunctive pattern must bind the same variables (" ++
       Id.print (List.hd ids'').v ++ strbrk " is not bound in all patterns).")
  | [] -> ()

let check_has_letin ?loc g expanded nargs nimps tags =
  let expected_ndecls = List.length tags - nimps in
  let expected_nassums = List.count (fun x -> not x) tags - nimps in
  if nargs = expected_nassums then false
  else if nargs = expected_ndecls then true else
    let env = Global.env() in
    match g with
    | GlobRef.ConstructRef cstr -> error_wrong_numarg_constructor ?loc env ~cstr ~expanded ~nargs ~expected_nassums ~expected_ndecls
    | GlobRef.IndRef ind -> error_wrong_numarg_inductive ?loc env ~ind ~expanded ~nargs ~expected_nassums ~expected_ndecls
    | _ -> assert false

(** Do not raise NotEnoughArguments thanks to preconditions*)
let chop_params_pattern loc ind args with_letin =
  let nparams = if with_letin
    then Inductiveops.inductive_nparamdecls (Global.env()) ind
    else Inductiveops.inductive_nparams (Global.env()) ind in
  assert (nparams <= List.length args);
  let params,args = List.chop nparams args in
  List.iter (fun c -> match DAst.get c with
    | PatVar Anonymous -> ()
    | PatVar _ | PatCstr(_,_,_) -> error_parameter_not_implicit ?loc:c.CAst.loc) params;
  args

let find_constructor_head ?loc ref =
  let open GlobRef in
  match ref with
  | ConstructRef cstr -> cstr
  | IndRef _ ->
    let error = str "There is an inductive name deep in a \"in\" clause." in
    user_err ?loc error
  | ConstRef _ | VarRef _ ->
    let error = str "This reference is not a constructor." in
    user_err ?loc error

let find_inductive_head ?loc ref =
  let open GlobRef in
  match ref with
  | IndRef ind -> ind
  | _ -> error_bad_inductive_type ?loc ()

let find_pattern_variable qid =
  if qualid_is_ident qid then qualid_basename qid
  else Loc.raise ?loc:qid.CAst.loc (InternalizationError(NotAConstructor qid))

let check_duplicate ?loc fields =
  let eq (ref1, _) (ref2, _) = qualid_eq ref1 ref2 in
  let dups = List.duplicates eq fields in
  match dups with
  | [] -> ()
  | (r, _) :: _ ->
    user_err ?loc (str "This record defines several times the field " ++
      pr_qualid r ++ str ".")

(** [sort_fields ~complete loc fields completer] expects a list
    [fields] of field assignments [f = e1; g = e2; ...], where [f, g]
    are fields of a record and [e1] are "values" (either terms, when
    interning a record construction, or patterns, when intering record
    pattern-matching). It will sort the fields according to the record
    declaration order (which is important when type-checking them in
    presence of dependencies between fields). If the parameter
    [complete] is true, we require the assignment to be complete: all
    the fields of the record must be present in the
    assignment. Otherwise the record assignment may be partial
    (in a pattern, we may match on some fields only), and we call the
    function [completer] to fill the missing fields; the returned
    field assignment list is always complete. *)
let sort_fields ~complete loc fields completer =
  match fields with
    | [] -> None
    | (first_field_ref, _):: _ ->
        let (first_field_glob_ref, record) = intern_field_ref first_field_ref in
        (* the number of parameters *)
        let nparams = record.Structure.nparams in
        (* the reference constructor of the record *)
        let base_constructor = GlobRef.ConstructRef (record.Structure.name,1) in
        let () = check_duplicate ?loc fields in
        let build_proj idx proj =
          if proj.Structure.proj_body = None && complete then
            (* we don't want anonymous fields *)
            user_err ?loc (str "This record contains anonymous fields.")
          else
            (idx, proj.Structure.proj_body, proj.Structure.proj_true) in
        let proj_list =
          List.map_i build_proj 1 record.Structure.projections in
        (* now we want to have all fields assignments indexed by their place in
           the constructor *)
        let rec index_fields fields remaining_projs acc =
          match fields with
            | (field_ref, field_value) :: fields ->
               let field_glob_ref,this_field_record = intern_field_ref field_ref in
               let remaining_projs, (field_index, _, regular) =
                 let the_proj = function
                   | (idx, Some glob_id, _) -> GlobRef.equal field_glob_ref (GlobRef.ConstRef glob_id)
                   | (idx, None, _) -> false in
                 try CList.extract_first the_proj remaining_projs
                 with Not_found ->
                   Loc.raise ?loc (InternalizationError(ProjectionsOfDifferentRecords (record, this_field_record)))
               in
               if not regular && complete then
                 (* "regular" is false when the field is defined
                    by a let-in in the record declaration
                    (its value is fixed from other fields). *)
                 user_err ?loc  (str "No local fields allowed in a record construction.");
               Dumpglob.add_glob ?loc:field_ref.CAst.loc field_glob_ref;
               index_fields fields remaining_projs ((field_index, field_value) :: acc)
            | [] ->
               let remaining_fields =
                 let complete_field (idx, field_ref, regular) =
                   if not regular && complete then
                     (* For terms, we keep only regular fields *)
                     None
                   else
                     Some (idx, completer idx field_ref (record.Structure.name,1)) in
                 List.map_filter complete_field remaining_projs in
               List.rev_append remaining_fields acc
        in
        let unsorted_indexed_fields = index_fields fields proj_list [] in
        let sorted_indexed_fields =
          let cmp_by_index (i, _) (j, _) = Int.compare i j in
          List.sort cmp_by_index unsorted_indexed_fields in
        let sorted_fields = List.map snd sorted_indexed_fields in
        Some (nparams, base_constructor, sorted_fields)

(** {6 Manage multiple aliases} *)

type alias = {
  alias_ids : lident list;
  alias_map : Id.t Id.Map.t;
}

let empty_alias = {
  alias_ids = [];
  alias_map = Id.Map.empty;
}

  (* [merge_aliases] returns the sets of all aliases encountered at this
     point and a substitution mapping extra aliases to the first one *)
let merge_aliases aliases {loc;v=na} =
  match na with
  | Anonymous -> aliases
  | Name id ->
  let alias_ids = aliases.alias_ids @ [make ?loc id] in
  let alias_map = match aliases.alias_ids with
  | [] -> aliases.alias_map
  | {v=id'} :: _ -> Id.Map.add id id' aliases.alias_map
  in
  { alias_ids; alias_map; }

let alias_of als = match als.alias_ids with
  | [] -> Anonymous
  | {v=id} :: _ -> Name id

(** {6 Expanding notations }

    @returns a raw_case_pattern_expr :
    - no notations and syntactic definition
    - global reference and identifier instead of reference

*)

let merge_subst s1 s2 = Id.Map.fold Id.Map.add s1 s2

let product_of_cases_patterns aliases idspl =
  (* each [pl] is a disjunction of patterns over common identifiers [ids] *)
  (* We stepwise build a disjunction of patterns [ptaill] over common [ids'] *)
  List.fold_right (fun (ids,pl) (ids',ptaill) ->
    (ids @ ids',
     (* Cartesian prod of the or-pats for the nth arg and the tail args *)
     List.flatten (
       List.map (fun (subst,p) ->
         List.map (fun (subst',ptail) -> (merge_subst subst subst',p::ptail)) ptaill) pl)))
    idspl (aliases.alias_ids,[aliases.alias_map,[]])

let rec subst_pat_iterator y t = DAst.(map (function
  | RCPatAtom id as p ->
    begin match id with Some ({v=x},_) when Id.equal x y -> DAst.get t | _ -> p end
  | RCPatCstr (id,l) ->
    RCPatCstr (id,List.map (subst_pat_iterator y t) l)
  | RCPatAlias (p,a) -> RCPatAlias (subst_pat_iterator y t p,a)
  | RCPatOr pl -> RCPatOr (List.map (subst_pat_iterator y t) pl)))

let is_non_zero c = match c with
  | { CAst.v = CPrim (Number p) } -> not (NumTok.Signed.is_zero p)
  | _ -> false

let is_non_zero_pat c = match c with
  | { CAst.v = CPatPrim (Number p) } -> not (NumTok.Signed.is_zero p)
  | _ -> false

let get_asymmetric_patterns = Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Asymmetric";"Patterns"]
    ~value:false

type global_reference_test = {
  for_ind : bool;
  test_kind : ?loc:Loc.t -> GlobRef.t -> unit
}

let drop_notations_pattern (test_kind_top,test_kind_inner) genv env pat =
  (* At toplevel, Constructors and Inductives are accepted, in recursive calls
     only constructor are allowed *)
  let ensure_kind {test_kind} ?loc g =
    try test_kind ?loc g
    with Not_found ->
      error_invalid_pattern_notation ?loc ()
  in
  (* [rcp_of_glob] : from [glob_constr] to [raw_cases_pattern_expr] *)
  let rec rcp_of_glob scopes x = DAst.(map (function
    | GVar id -> RCPatAtom (Some (CAst.make ?loc:x.loc id,scopes))
    | GHole (_,_,_) -> RCPatAtom None
    | GRef (g,_) -> RCPatCstr (g, [])
    | GApp (r, l) ->
      begin match DAst.get r with
      | GRef (g,_) ->
        let allscs = find_arguments_scope g in
        let allscs = simple_adjust_scopes (List.length l) allscs in
        RCPatCstr (g, List.map2 (fun sc a -> rcp_of_glob (sc,snd scopes) a) allscs l)
      | _ ->
        CErrors.anomaly Pp.(str "Invalid return pattern from Notation.interp_prim_token_cases_pattern_expr.")
      end
    | _ -> CErrors.anomaly Pp.(str "Invalid return pattern from Notation.interp_prim_token_cases_pattern_expr."))) x
  in
  let make_pars ?loc g =
    let env = Global.env () in
    let n = match g with
      | GlobRef.ConstructRef (ind,_) -> Inductiveops.inductive_nparams env ind
      | _ -> 0 in
    List.make n (DAst.make ?loc @@ RCPatAtom None)
  in
  let rec drop_abbrev {test_kind} ?loc scopes qid add_par_if_no_ntn_with_par no_impl pats =
    try
      if qualid_is_ident qid && Option.cata (Id.Set.mem (qualid_basename qid)) false env.pat_ids && List.is_empty pats then
        raise Not_found;
      let intern_not subst pat = in_not test_kind_inner qid.loc scopes subst [] pat in
      let g, expanded, ntnpats, pats = intern_qualid_for_pattern (test_kind ?loc) intern_not qid pats in
      match ntnpats with
      | None ->
        (* deactivate implicit *)
        let ntnpats = if add_par_if_no_ntn_with_par then make_pars ?loc g else [] in
        Some (g, in_patargs ?loc scopes g expanded true ntnpats pats)
      | Some ntnpats ->
        let ntnpats = if add_par_if_no_ntn_with_par && ntnpats = [] then make_pars ?loc g else ntnpats in
        Some (g, in_patargs ?loc scopes g expanded no_impl ntnpats pats)
    with Not_found -> None
  and in_pat ({for_ind} as test_kind) scopes pt =
    let open CAst in
    let loc = pt.loc in
    (* The two policies implied by asymmetric pattern mode *)
    let add_par_if_no_ntn_with_par = get_asymmetric_patterns () && not for_ind in
    let no_impl = get_asymmetric_patterns () && not for_ind in
    match pt.v with
    | CPatAlias (p, id) -> DAst.make ?loc @@ RCPatAlias (in_pat test_kind scopes p, id)
    | CPatRecord l ->
      let sorted_fields =
        sort_fields ~complete:false loc l (fun _idx fieldname constructor -> CAst.make ?loc @@ CPatAtom None) in
      begin match sorted_fields with
        | None -> DAst.make ?loc @@ RCPatAtom None
        | Some (n, head, pl) ->
          let pars = make_pars ?loc head in
          let pats = in_patargs ?loc scopes head true true pars pl in
          DAst.make ?loc @@ RCPatCstr(head, pats)
      end
    | CPatCstr (head, None, pl) ->
      begin
        match drop_abbrev test_kind ?loc scopes head add_par_if_no_ntn_with_par no_impl pl with
        | Some (g,pl) -> DAst.make ?loc @@ RCPatCstr(g, pl)
        | None -> Loc.raise ?loc (InternalizationError (NotAConstructor head))
      end
    | CPatCstr (qid, Some expl_pl, pl) ->
      begin
        match drop_abbrev test_kind ?loc scopes qid false true (expl_pl@pl) with
        | Some (g,pl) -> DAst.make ?loc @@ RCPatCstr (g, pl)
        | None -> Loc.raise ?loc (InternalizationError (NotAConstructor qid))
      end
    | CPatNotation (_,(InConstrEntry,"- _"),([a],[]),[]) when is_non_zero_pat a ->
      let p = match a.CAst.v with CPatPrim (Number (_, p)) -> p | _ -> assert false in
      let pat, _df = Notation.interp_prim_token_cases_pattern_expr ?loc (ensure_kind test_kind_inner) (Number (SMinus,p)) scopes in
      rcp_of_glob scopes pat
    | CPatNotation (_,(InConstrEntry,"( _ )"),([a],[]),[]) ->
      in_pat test_kind scopes a
    | CPatNotation (_,ntn,fullargs,extrargs) ->
      let ntn,(terms,termlists) = contract_curly_brackets_pat ntn fullargs in
      let ((ids',c),df) = Notation.interp_notation ?loc ntn scopes in
      let subst = split_by_type_pat ?loc ids' (terms,termlists) in
      Dumpglob.dump_notation_location (patntn_loc ?loc fullargs ntn) ntn df;
      in_not test_kind loc scopes subst extrargs c
    | CPatDelimiters (key, e) ->
      in_pat test_kind (None,find_delimiters_scope ?loc key::snd scopes) e
    | CPatPrim p ->
      let pat, _df = Notation.interp_prim_token_cases_pattern_expr ?loc test_kind_inner.test_kind p scopes in
      rcp_of_glob scopes pat
    | CPatAtom (Some id) ->
      begin
        match drop_abbrev test_kind ?loc scopes id add_par_if_no_ntn_with_par no_impl [] with
        | Some (g, pl) -> DAst.make ?loc @@ RCPatCstr (g, pl)
        | None         -> DAst.make ?loc @@ RCPatAtom (Some ((make ?loc @@ find_pattern_variable id),scopes))
      end
    | CPatAtom None -> DAst.make ?loc @@ RCPatAtom None
    | CPatOr pl     -> DAst.make ?loc @@ RCPatOr (List.map (in_pat test_kind scopes) pl)
    | CPatCast (_,_) ->
      (* We raise an error if the pattern contains a cast, due to
         current restrictions on casts in patterns. Cast in patterns
         are supported only in local binders and only at for_ind level.
         The only reason they are in the [cases_pattern_expr] type
         is that the parser needs to factor the "c : t" notation
         with user defined notations. In the long term, we will try to
         support such casts everywhere, and perhaps use them to print
         the domains of lambdas in the encoding of match in constr.
         This check is here and not in the parser because it would require
         duplicating the levels of the [pattern] rule. *)
      CErrors.user_err ?loc (Pp.strbrk "Casts are not supported in this pattern.")
  and in_pat_sc scopes x = in_pat test_kind_inner (x,snd scopes)
  and in_patargs ?loc scopes
    gr (* head of the pattern *)
    expanded (* tell if comes from a notation (for error reporting) *)
    no_impl (* tell if implicit are not expected (for asymmetric patterns, or @, or {| |} *)
    ntnpats (* prefix of patterns obtained by expansion of notations or parameter insertion *)
    pats (* user given patterns *)
    =
    let default = DAst.make ?loc @@ RCPatAtom None in
    let npats = List.length pats in
    let n = List.length ntnpats in
    let ntnpats_with_letin, tags =
      let tags = match gr with
      | GlobRef.ConstructRef cstr -> constructor_alltags (Global.env()) cstr
      | GlobRef.IndRef ind -> inductive_alltags (Global.env()) ind
      | _ -> assert false in
      let ntnpats_with_letin = adjust_to_up tags ntnpats default in
      ntnpats_with_letin, List.skipn (List.length ntnpats_with_letin) tags in
    let imps =
      let imps =
        if no_impl then [] else
          let impls_st = implicits_of_global gr in
          if Int.equal n 0 then select_impargs_size npats impls_st
          else List.skipn_at_least n (select_stronger_impargs impls_st) in
      adjust_to_down tags imps None in
    let subscopes = adjust_to_down tags (List.skipn_at_least n (find_arguments_scope gr)) None in
    let has_letin = check_has_letin ?loc gr expanded npats (List.count is_status_implicit imps) tags in
    let rec aux imps subscopes tags pats =
    match imps, subscopes, tags, pats with
    | _, _, true::tags, p::pats when has_letin ->
      in_pat_sc scopes None p :: aux imps subscopes tags pats
    | _, _, true::tags, _ ->
      default :: aux imps subscopes tags pats
    | imp::imps, sc::subscopes, false::tags, _ when is_status_implicit imp ->
      default :: aux imps subscopes tags pats
    | imp::imps, sc::subscopes, false::tags, p::pats ->
      in_pat_sc scopes sc p :: aux imps subscopes tags pats
    | _, _, [], [] -> []
    | _ -> assert false in
    ntnpats_with_letin @ aux imps subscopes tags pats
  and in_not test_kind loc scopes (subst,substlist as fullsubst) args = function
    | NVar id ->
      begin
        (* subst remembers the delimiters stack in the interpretation *)
        (* of the notations *)
        try
          let (a,(scopt,subscopes)) = Id.Map.find id subst in
          in_pat test_kind (scopt,subscopes@snd scopes) (mkAppPattern ?loc a args)
        with Not_found ->
          if Id.equal id ldots_var then
            if List.is_empty args then
              DAst.make ?loc @@ RCPatAtom (Some ((make ?loc id),scopes))
            else
              user_err (str "Recursive notations with arguments not supported in patterns.")
          else
            anomaly (str "Unbound pattern notation variable: " ++ Id.print id ++ str ".")
      end
    | NApp (NVar id,ntnpl) ->
      user_err ?loc (str "Notations with an applied head variable not supported in patterns.")
    | NRef (g,_) ->
      ensure_kind test_kind ?loc g;
      DAst.make ?loc @@ RCPatCstr (g, in_patargs ?loc scopes g true false [] args)
    | NApp (NRef (g,_),ntnpl) ->
      ensure_kind test_kind ?loc g;
      let ntnpl = List.map (in_not test_kind_inner loc scopes fullsubst []) ntnpl in
      let no_impl =
        (* Convention: if notation is @f, encoded as NApp(Nref g,[]), then
           implicit arguments are not inherited *)
        ntnpl = [] in
      DAst.make ?loc @@ RCPatCstr (g, in_patargs ?loc scopes g true no_impl ntnpl args)
    | NList (x,y,iter,terminator,revert) ->
      if not (List.is_empty args) then user_err ?loc
        (strbrk "Application of arguments to a recursive notation not supported in patterns.");
      (try
         (* All elements of the list are in scopes (scopt,subscopes) *)
         let (l,(scopt,subscopes)) = Id.Map.find x substlist in
         let termin = in_not test_kind_inner loc scopes fullsubst [] terminator in
         List.fold_right (fun a t ->
           let nsubst = Id.Map.add y (a, (scopt, subscopes)) subst in
           let u = in_not test_kind_inner loc scopes (nsubst, substlist) [] iter in
           subst_pat_iterator ldots_var t u)
           (if revert then List.rev l else l) termin
       with Not_found ->
         anomaly (Pp.str "Inconsistent substitution of recursive notation."))
    | NHole (_,_,None) ->
      if not (List.is_empty args) then user_err ?loc (str "Such pattern cannot have arguments.");
      DAst.make ?loc @@ RCPatAtom None
    | NHole (_,_,Some _) ->
      user_err ?loc (str "Quotations not supported in patterns.")
    | t -> error_invalid_pattern_notation ?loc ()
  in in_pat test_kind_top env.pat_scopes pat

let rec intern_pat genv ntnvars aliases pat =
  let intern_cstr_with_all_args loc c with_letin idslpl1 pl2 =
    let idslpl2 = List.map (intern_pat genv ntnvars empty_alias) pl2 in
    let (ids',pll) = product_of_cases_patterns aliases (idslpl1@idslpl2) in
    let pl' = List.map (fun (asubst,pl) ->
      (asubst, DAst.make ?loc @@ PatCstr (c,chop_params_pattern loc (fst c) pl with_letin,alias_of aliases))) pll in
    ids',pl' in
  let loc = pat.loc in
  match DAst.get pat with
    | RCPatAlias (p, id) ->
      let aliases' = merge_aliases aliases id in
      intern_pat genv ntnvars aliases' p
    | RCPatCstr (head, pl) ->
      let c = find_constructor_head ?loc head in
      intern_cstr_with_all_args loc c true [] pl
    | RCPatAtom (Some ({loc;v=id},scopes)) ->
      let aliases = merge_aliases aliases (make ?loc @@ Name id) in
      set_var_is_binder ?loc id ntnvars;
      (aliases.alias_ids,[aliases.alias_map, DAst.make ?loc @@ PatVar (alias_of aliases)]) (* TO CHECK: aura-t-on id? *)
    | RCPatAtom None ->
      let { alias_ids = ids; alias_map = asubst; } = aliases in
      (ids, [asubst, DAst.make ?loc @@ PatVar (alias_of aliases)])
    | RCPatOr pl ->
      assert (not (List.is_empty pl));
      let pl' = List.map (intern_pat genv ntnvars aliases) pl in
      let (idsl,pl') = List.split pl' in
      let ids = List.hd idsl in
      check_or_pat_variables loc ids (List.tl idsl);
      (ids,List.flatten pl')

let intern_cases_pattern test_kind genv ntnvars env aliases pat =
  let test = {for_ind=false;test_kind} in
  intern_pat genv ntnvars aliases
    (drop_notations_pattern (test,test) genv env pat)

let _ =
  intern_cases_pattern_fwd :=
    fun test_kind ntnvars env p ->
    intern_cases_pattern test_kind (Global.env ()) ntnvars env empty_alias p

let intern_ind_pattern genv ntnvars env pat =
  let test_kind_top ?loc = function
    | GlobRef.IndRef _  -> ()
    | GlobRef.ConstructRef _ | GlobRef.ConstRef _ | GlobRef.VarRef _ ->
      (* A non-inductive global reference at top is an error *)
      error_invalid_pattern_notation ?loc () in
  let test_kind_inner ?loc = function
    | GlobRef.ConstructRef _ -> ()
    | GlobRef.IndRef _ | GlobRef.ConstRef _ | GlobRef.VarRef _ ->
      (* A non-constructor global reference deep in a pattern is seen as a variable *)
      raise Not_found in
  let no_not =
    try
      let test_top = {for_ind=true;test_kind=test_kind_top} in
      let test_inner = {for_ind=false;test_kind=test_kind_inner} in
      drop_notations_pattern (test_top,test_inner) genv env pat
    with InternalizationError (NotAConstructor _) as exn ->
      let _, info = Exninfo.capture exn in
      error_bad_inductive_type ~info ()
  in
  let loc = no_not.CAst.loc in
  match DAst.get no_not with
    | RCPatCstr (head, pl) ->
      let ind = find_inductive_head ?loc head in
      let idslpl = List.map (intern_pat genv ntnvars empty_alias) pl in
      (match product_of_cases_patterns empty_alias idslpl with
       | ids,[asubst,pl] -> (ind,ids,asubst,chop_params_pattern loc ind pl true)
       | _ -> error_bad_inductive_type ?loc ())
    | x -> error_bad_inductive_type ?loc ()

(**********************************************************************)
(* Utilities for application                                          *)

let get_implicit_name n imps =
  Some (Impargs.name_of_implicit (List.nth imps (n-1)))

let set_hole_implicit i b c =
  let loc = c.CAst.loc in
  let loc, r = match DAst.get c with
  | GRef (r, _) -> loc, r
  | GApp (r, _) ->
    let loc = r.CAst.loc in
    begin match DAst.get r with
    | GRef (r, _) -> loc, r
    | GProj ((cst,_), _, _) -> (* Improve: *) loc, GlobRef.ConstRef cst
    | _ -> anomaly (Pp.str "Only refs have implicits.")
    end
  | GProj ((cst,_), _, _) -> loc, GlobRef.ConstRef cst
  | GVar id -> loc, GlobRef.VarRef id
  | _ -> anomaly (Pp.str "Only refs have implicits.") in
  Loc.tag ?loc (Evar_kinds.ImplicitArg (r,i,b),IntroAnonymous,None)

let exists_implicit_name id =
  List.exists (fun imp -> is_status_implicit imp && Id.equal id (name_of_implicit imp))

let print_allowed_named_implicit imps =
  let l = List.map_filter (function Some ((Name id,_,_),_,_) -> Some id | _ -> None) imps in
  match l with
  | [] -> mt ()
  | l ->
    let n = List.length l in
    str " (possible " ++ str (String.plural n "name") ++ str ":" ++ spc () ++
    pr_sequence Id.print l ++ str ")"

let print_allowed_nondep_implicit imps =
  let l = List.map_filter (function Some ((_,_,Some n),_,_) -> Some n | _ -> None) imps in
  match l with
  | [] -> mt ()
  | l ->
    let n = List.length l in
    str " (possible " ++ str (String.plural n "position") ++ str ":" ++ spc () ++
    pr_sequence Pp.int l ++ str ")"

let extract_explicit_arg imps args =
  let rec aux = function
  | [] -> [], []
  | (a,e)::l ->
      let (eargs,rargs) = aux l in
      match e with
      | None -> (eargs,a::rargs)
      | Some {loc;v=pos} ->
          let () = match pos with
          | ExplByName id ->
              if not (exists_implicit_name id imps) then
                user_err ?loc
                  (str "Wrong argument name " ++ Id.print id ++
                   print_allowed_named_implicit imps ++ str ".");
              if List.mem_assoc pos eargs then
                user_err ?loc  (str "Argument name " ++ Id.print id
                ++ str " occurs more than once.")
          | ExplByPos p ->
              if not (is_nondep_implicit p imps) then
                user_err ?loc
                  (str"Wrong argument position " ++ int p ++
                   print_allowed_nondep_implicit imps ++ str ".");
              if List.mem_assoc pos eargs then
                user_err ?loc (str"Argument at position " ++ int p ++
                  str " is mentioned more than once.") in
          ((pos,(loc,a))::eargs, rargs)
  in aux args

let extract_regular_arguments args =
  List.map_filter (function
      | (a,Some pos) -> user_err ?loc:pos.loc (str "Unexpected explicit argument.")
      | (a,None) -> Some a) args

(**********************************************************************)
(* Main loop                                                          *)

let internalize globalenv env pattern_mode (_, ntnvars as lvar) c =
  let rec intern env = CAst.with_loc_val (fun ?loc -> function
    | CRef (ref,us) ->
        let c,_ =
          intern_applied_reference ~isproj:false intern env (Environ.named_context_val globalenv)
            lvar us [] ref
        in
          apply_impargs env loc c []

    | CFix ({ CAst.loc = locid; v = iddef}, dl) ->
        let lf = List.map (fun ({CAst.v = id},_,_,_,_) -> id) dl in
        let dl = Array.of_list dl in
        let n =
          try List.index0 Id.equal iddef lf
          with Not_found as exn ->
            let _, info = Exninfo.capture exn in
            let info = Option.cata (Loc.add_loc info) info locid in
            Exninfo.iraise (InternalizationError (UnboundFixName (false,iddef)),info)
        in
        let env = restart_lambda_binders env in
        let idl_temp = Array.map
            (fun (id,recarg,bl,ty,_) ->
               let recarg = Option.map (function { CAst.v = v; loc } -> match v with
                 | CStructRec i -> i
                 | _ -> user_err ?loc Pp.(str "Well-founded induction requires Program Fixpoint or Function.")) recarg
               in
               let (env',bl) = List.fold_left intern_local_binder (env,[]) bl in
               let bl = List.rev_map glob_local_binder_of_extended bl in
               let n = Option.map (fun recarg ->
                   List.fold_left_until (fun n (id,_,body,_) -> match body with
                       | None ->
                         if Name.equal id (Name recarg.v) then Stop n else Cont (n+1)
                       | Some _ -> Cont n (* let-ins don't count *))
                     0 bl)
                   recarg
               in
               let bl_impls = remember_binders_impargs env' bl in
               (n, bl, intern_type env' ty, bl_impls)) dl in
        (* We add the recursive functions to the environment *)
        let env_rec = List.fold_left_i (fun i en name ->
           let (_,bli,tyi,_) = idl_temp.(i) in
           let binder_index,fix_args = impls_binder_list 1 bli in
           let impls = impls_type_list ~args:fix_args binder_index tyi in
           push_name_env ntnvars impls en (CAst.make @@ Name name)) 0 env lf in
        let idl = Array.map2 (fun (_,_,_,_,bd) (n,bl,ty,before_impls) ->
            (* We add the binders common to body and type to the environment *)
            let env_body = restore_binders_impargs env_rec before_impls in
            (n,bl,ty,intern {env_body with tmp_scope = None} bd)) dl idl_temp in
        DAst.make ?loc @@
        GRec (GFix
                (Array.map (fun (ro,_,_,_) -> ro) idl,n),
              Array.of_list lf,
              Array.map (fun (_,bl,_,_) -> bl) idl,
              Array.map (fun (_,_,ty,_) -> ty) idl,
              Array.map (fun (_,_,_,bd) -> bd) idl)

    | CCoFix ({ CAst.loc = locid; v = iddef }, dl) ->
        let lf = List.map (fun ({CAst.v = id},_,_,_) -> id) dl in
        let dl = Array.of_list dl in
        let n =
          try List.index0 Id.equal iddef lf
          with Not_found as exn ->
            let _, info = Exninfo.capture exn in
            let info = Option.cata (Loc.add_loc info) info locid in
            Exninfo.iraise (InternalizationError (UnboundFixName (true,iddef)), info)
        in
        let env = restart_lambda_binders env in
        let idl_tmp = Array.map
          (fun ({ CAst.loc; v = id },bl,ty,_) ->
            let (env',rbl) = List.fold_left intern_local_binder (env,[]) bl in
            let bl = List.rev (List.map glob_local_binder_of_extended rbl) in
            let bl_impls = remember_binders_impargs env' bl in
            (bl,intern_type env' ty,bl_impls)) dl in
        let env_rec = List.fold_left_i (fun i en name ->
          let (bli,tyi,_) = idl_tmp.(i) in
          let binder_index,cofix_args = impls_binder_list 1 bli in
          push_name_env ntnvars (impls_type_list ~args:cofix_args binder_index tyi)
            en (CAst.make @@ Name name)) 0 env lf in
        let idl = Array.map2 (fun (_,_,_,bd) (b,c,bl_impls) ->
          (* We add the binders common to body and type to the environment *)
          let env_body = restore_binders_impargs env_rec bl_impls in
          (b,c,intern {env_body with tmp_scope = None} bd)) dl idl_tmp in
        DAst.make ?loc @@
        GRec (GCoFix n,
              Array.of_list lf,
              Array.map (fun (bl,_,_) -> bl) idl,
              Array.map (fun (_,ty,_) -> ty) idl,
              Array.map (fun (_,_,bd) -> bd) idl)
    | CProdN ([],c2) -> anomaly (Pp.str "The AST is malformed, found prod without binders.")
    | CProdN (bl,c2) ->
        let (env',bl) = List.fold_left intern_local_binder (switch_prod_binders env,[]) bl in
        expand_binders ?loc mkGProd bl (intern_type env' c2)
    | CLambdaN ([],c2) -> anomaly (Pp.str "The AST is malformed, found lambda without binders.")
    | CLambdaN (bl,c2) ->
        let (env',bl) = List.fold_left intern_local_binder (reset_tmp_scope (switch_lambda_binders env),[]) bl in
        expand_binders ?loc mkGLambda bl (intern env' c2)
    | CLetIn (na,c1,t,c2) ->
        let inc1 = intern_restart_binders (reset_tmp_scope env) c1 in
        let int = Option.map (intern_type_restart_binders env) t in
        DAst.make ?loc @@
        GLetIn (na.CAst.v, inc1, int,
          intern_restart_binders (push_name_env ntnvars (impls_term_list 1 inc1) env na) c2)
    | CNotation (_,(InConstrEntry,"- _"), ([a],[],[],[])) when is_non_zero a ->
      let p = match a.CAst.v with CPrim (Number (_, p)) -> p | _ -> assert false in
       intern env (CAst.make ?loc @@ CPrim (Number (SMinus,p)))
    | CNotation (_,(InConstrEntry,"( _ )"),([a],[],[],[])) -> intern env a
    | CNotation (_,ntn,args) ->
        let c = intern_notation intern env ntnvars loc ntn args in
        apply_impargs env loc c []
    | CGeneralization (b,c) ->
        intern_generalization intern env ntnvars loc b c
    | CPrim p ->
        fst (Notation.interp_prim_token ?loc p (env.tmp_scope,env.scopes))
    | CDelimiters (key, e) ->
        intern {env with tmp_scope = None;
                  scopes = find_delimiters_scope ?loc key :: env.scopes} e
    | CProj (expl, f, args, c) ->
        intern_proj ?loc env expl f args c []
    | CAppExpl ((ref,us), args) ->
        let f,args =
          let args = List.map (fun a -> (a,None)) args in
          intern_applied_reference ~isproj:false intern env (Environ.named_context_val globalenv)
            lvar us args ref
        in
        check_not_notation_variable f ntnvars;
        let _,args_scopes = find_appl_head_data env lvar f in
        (* Rem: GApp(_,f,[]) stands for @f *)
        let args = intern_args env args_scopes (List.map fst args) in
        if args = [] then DAst.make ?loc @@ GApp (f,[])
        else smart_gapp f loc args
    | CApp (f, args) ->
        begin match f.CAst.v with
         (* t.(f args') args *)
        | CProj (expl, (ref,us), args', c) ->
          intern_proj ?loc:f.CAst.loc env expl (ref,us) args' c args
        | CRef (ref,us) ->
          let f, args = intern_applied_reference ~isproj:false intern env
            (Environ.named_context_val globalenv) lvar us args ref in
          apply_impargs env loc f args
        | CNotation (_,ntn,ntnargs) ->
          let c = intern_notation intern env ntnvars loc ntn ntnargs in
          apply_impargs env loc c args
        | _ ->
          let f = intern_no_implicit env f in
          let _, args_scopes = find_appl_head_data env lvar f in
          let args = extract_regular_arguments args in
          smart_gapp f loc (intern_args env args_scopes args)
        end
    | CRecord fs ->
       let st = Evar_kinds.Define (not (Program.get_proofs_transparency ())) in
       let fields =
         sort_fields ~complete:true loc fs
                     (fun _idx fieldname constructorname ->
                         let open Evar_kinds in
                         let fieldinfo : Evar_kinds.record_field =
                             {fieldname=Option.get fieldname; recordname=inductive_of_constructor constructorname}
                             in
                         CAst.make ?loc @@ CHole (Some
                 (Evar_kinds.QuestionMark { Evar_kinds.default_question_mark with
                     Evar_kinds.qm_obligation=st;
                     Evar_kinds.qm_record_field=Some fieldinfo
                }) , IntroAnonymous, None))
       in
       begin
          match fields with
            | None -> user_err ?loc (str"No constructor inference.")
            | Some (n, constrname, args) ->
                let args_scopes = find_arguments_scope constrname in
                let pars = List.make n (CAst.make ?loc @@ CHole (None, IntroAnonymous, None)) in
                let args = intern_args env args_scopes (List.rev_append pars args) in
                let hd = DAst.make @@ GRef (constrname,None) in
                DAst.make ?loc @@ GApp (hd, args)
       end
    | CCases (sty, rtnpo, tms, eqns) ->
        let as_in_vars = List.fold_left (fun acc (_,na,inb) ->
          (Option.fold_left (fun acc { CAst.v = y } -> Name.fold_right Id.Set.add y acc) acc na))
          Id.Set.empty tms in
        (* as, in & return vars *)
        let forbidden_vars = Option.cata free_vars_of_constr_expr as_in_vars rtnpo in
        let tms,ex_ids,aliases,match_from_in = List.fold_right
          (fun citm (inds,ex_ids,asubst,matchs) ->
            let ((tm,ind),extra_id,(ind_ids,alias_subst,match_td)) =
              intern_case_item env forbidden_vars citm in
            (tm,ind)::inds,
            Id.Set.union ind_ids (Option.fold_right Id.Set.add extra_id ex_ids),
            merge_subst alias_subst asubst,
            List.rev_append match_td matchs)
          tms ([],Id.Set.empty,Id.Map.empty,[]) in
        let env' = Id.Set.fold
          (fun var bli -> push_name_env ntnvars [] bli (CAst.make @@ Name var))
          (Id.Set.union ex_ids as_in_vars)
          (restart_lambda_binders env)
        in
        (* PatVars before a real pattern do not need to be matched *)
        let stripped_match_from_in =
          let rec aux = function
            | [] -> []
            | (_, c) :: q when is_patvar c -> aux q
            | l -> l
          in aux match_from_in in
        let rtnpo = Option.map (replace_vars_constr_expr aliases) rtnpo in
        let rtnpo = match stripped_match_from_in with
          | [] -> Option.map (intern_type (slide_binders env')) rtnpo (* Only PatVar in "in" clauses *)
          | l ->
             (* Build a return predicate by expansion of the patterns of the "in" clause *)
             let thevars, thepats = List.split l in
             let sub_rtn = (* Some (GSort (Loc.ghost,GType None)) *) None in
             let sub_tms = List.map (fun id -> (DAst.make @@ GVar id),(Name id,None)) thevars (* "match v1,..,vn" *) in
             let main_sub_eqn = CAst.make @@
               ([],thepats, (* "|p1,..,pn" *)
                Option.cata (intern_type_no_implicit env')
                  (DAst.make ?loc @@ GHole(Evar_kinds.CasesType false,IntroAnonymous,None))
                  rtnpo) (* "=> P" if there were a return predicate P, and "=> _" otherwise *) in
             let catch_all_sub_eqn =
               if List.for_all (irrefutable globalenv) thepats then [] else
                  [CAst.make @@ ([],List.make (List.length thepats) (DAst.make @@ PatVar Anonymous), (* "|_,..,_" *)
                   DAst.make @@ GHole(Evar_kinds.ImpossibleCase,IntroAnonymous,None))]   (* "=> _" *) in
             Some (DAst.make @@ GCases(RegularStyle,sub_rtn,sub_tms,main_sub_eqn::catch_all_sub_eqn))
        in
        let eqns' = List.map (intern_eqn (List.length tms) env) eqns in
        DAst.make ?loc @@
        GCases (sty, rtnpo, tms, List.flatten eqns')
    | CLetTuple (nal, (na,po), b, c) ->
        let env' = reset_tmp_scope env in
        (* "in" is None so no match to add *)
        let ((b',(na',_)),_,_) = intern_case_item env' Id.Set.empty (b,na,None) in
        let p' = Option.map (fun u ->
          let env'' = push_name_env ntnvars [] env'
            (CAst.make na') in
          intern_type (slide_binders env'') u) po in
        DAst.make ?loc @@
        GLetTuple (List.map (fun { CAst.v } -> v) nal, (na', p'), b',
                   intern (List.fold_left (push_name_env ntnvars []) env nal) c)
    | CIf (c, (na,po), b1, b2) ->
      let env' = reset_tmp_scope env in
      let ((c',(na',_)),_,_) = intern_case_item env' Id.Set.empty (c,na,None) in (* no "in" no match to ad too *)
      let p' = Option.map (fun p ->
          let env'' = push_name_env ntnvars [] env
            (CAst.make na') in
          intern_type (slide_binders env'') p) po in
        DAst.make ?loc @@
        GIf (c', (na', p'), intern env b1, intern env b2)
    | CHole (k, naming, solve) ->
        let k = match k with
        | None ->
           let st = Evar_kinds.Define (not (Program.get_proofs_transparency ())) in
           (match naming with
           | IntroIdentifier id -> Evar_kinds.NamedHole id
           | _ -> Evar_kinds.QuestionMark { Evar_kinds.default_question_mark with Evar_kinds.qm_obligation=st; })
        | Some k -> k
        in
        let solve = match solve with
        | None -> None
        | Some gen ->
          let (ltacvars, ntnvars) = lvar in
          (* Preventively declare notation variables in ltac as non-bindings *)
          Id.Map.iter (fun x (used_as_binder,_,_) -> used_as_binder := false) ntnvars;
          let extra = ltacvars.ltac_extra in
          (* We inform ltac that the interning vars and the notation vars are bound *)
          (* but we could instead rely on the "intern_sign" *)
          let lvars = Id.Set.union ltacvars.ltac_bound ltacvars.ltac_vars in
          let lvars = Id.Set.union lvars (Id.Map.domain ntnvars) in
          let ltacvars = Id.Set.union lvars env.ids in
          (* Propagating enough information for mutual interning with tac-in-term *)
          let intern_sign = {
            Genintern.intern_ids = env.ids;
            Genintern.notation_variable_status = ntnvars
          } in
          let ist = {
            Genintern.genv = globalenv;
            ltacvars;
            extra;
            intern_sign;
          } in
          let (_, glb) = Genintern.generic_intern ist gen in
          Some glb
        in
        DAst.make ?loc @@
        GHole (k, naming, solve)
    (* Parsing pattern variables *)
    | CPatVar n when pattern_mode ->
        DAst.make ?loc @@
        GPatVar (Evar_kinds.SecondOrderPatVar n)
    | CEvar (n, []) when pattern_mode ->
        DAst.make ?loc @@
        GPatVar (Evar_kinds.FirstOrderPatVar n.CAst.v)
    (* end *)
    (* Parsing existential variables *)
    | CEvar (n, l) ->
        DAst.make ?loc @@
        GEvar (n, List.map (on_snd (intern_no_implicit env)) l)
    | CPatVar _ ->
      Loc.raise ?loc (InternalizationError IllegalMetavariable)
    (* end *)
    | CSort s ->
        DAst.make ?loc @@
        GSort (intern_sort ~local_univs:env.local_univs s)
    | CCast (c1, k, c2) ->
        DAst.make ?loc @@
        GCast (intern env c1, k, intern_type (slide_binders env) c2)
    | CArray(u,t,def,ty) ->
      DAst.make ?loc @@ GArray(intern_instance ~local_univs:env.local_univs u, Array.map (intern env) t, intern env def, intern env ty)
    )
  and intern_type env = intern (set_type_scope env)

  and intern_type_no_implicit env = intern (restart_no_binders (set_type_scope env))

  and intern_no_implicit env = intern (restart_no_binders env)

  and intern_restart_binders env = intern (restart_lambda_binders env)

  and intern_type_restart_binders env = intern (restart_prod_binders (set_type_scope env))

  and intern_local_binder env bind : intern_env * Glob_term.extended_glob_local_binder list =
    intern_local_binder_aux intern ntnvars env bind

  (* Expands a multiple pattern into a disjunction of multiple patterns *)
  and intern_multiple_pattern env n pl =
    let env = { pat_ids = None; pat_scopes = (None,env.scopes) } in
    let idsl_pll = List.map (intern_cases_pattern test_kind_tolerant globalenv ntnvars env empty_alias) pl in
    let loc = loc_of_multiple_pattern pl in
    check_number_of_pattern loc n pl;
    product_of_cases_patterns empty_alias idsl_pll

  (* Expands a disjunction of multiple pattern *)
  and intern_disjunctive_multiple_pattern env loc n mpl =
    assert (not (List.is_empty mpl));
    let mpl' = List.map (intern_multiple_pattern env n) mpl in
    let (idsl,mpl') = List.split mpl' in
    let ids = List.hd idsl in
    check_or_pat_variables loc ids (List.tl idsl);
    (ids,List.flatten mpl')

  (* Expands a pattern-matching clause [lhs => rhs] *)
  and intern_eqn n env {loc;v=(lhs,rhs)} =
    let eqn_ids,pll = intern_disjunctive_multiple_pattern env loc n lhs in
    (* Linearity implies the order in ids is irrelevant *)
    let eqn_ids = List.map (fun x -> x.v) eqn_ids in
    check_linearity lhs eqn_ids;
    let env_ids = List.fold_right Id.Set.add eqn_ids env.ids in
    List.map (fun (asubst,pl) ->
      let rhs = replace_vars_constr_expr asubst rhs in
      let rhs' = intern_no_implicit {env with ids = env_ids} rhs in
      CAst.make ?loc (eqn_ids,pl,rhs')) pll

  and intern_case_item env forbidden_names_for_gen (tm,na,t) =
    (* the "match" part *)
    let tm' = intern_no_implicit env tm in
    (* the "as" part *)
    let extra_id,na =
      let loc = tm'.CAst.loc in
      match DAst.get tm', na with
      | GVar id, None when not (Id.Map.mem id (snd lvar)) -> Some id, CAst.make ?loc @@ Name id
      | GRef (GlobRef.VarRef id, _), None -> Some id, CAst.make ?loc @@ Name id
      | _, None -> None, CAst.make Anonymous
      | _, Some ({ CAst.loc; v = na } as lna) -> None, lna in
    (* the "in" part *)
    let match_td,typ = match t with
    | Some t ->
        let (ind,ind_ids,alias_subst,l) =
          intern_ind_pattern globalenv ntnvars (env_for_pattern (set_type_scope env)) t in
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
              | { CAst.v = Anonymous } -> l
              | { CAst.loc; v = (Name y as x) } -> (y, DAst.make ?loc @@ PatVar x) :: l in
            match case_rel_ctxt,arg_pats with
              | [],[] ->
                (add_name match_acc na, var_acc)
              | (LocalAssum (cano_name,ty) | LocalDef (cano_name,_,ty)) :: t, c::tt ->
                begin match DAst.get c with
                | PatVar x ->
                  let loc = c.CAst.loc in
                  canonize_args t tt forbidden_names
                    (add_name match_acc CAst.(make ?loc x)) (CAst.make ?loc x::var_acc)
                | _ ->
                  let fresh =
                    Namegen.next_name_away_with_default_using_types "iV" cano_name.binder_name forbidden_names (EConstr.of_constr ty) in
                  canonize_args t tt (Id.Set.add fresh forbidden_names)
                    ((fresh,c)::match_acc) ((CAst.make ?loc:(cases_pattern_loc c) @@ Name fresh)::var_acc)
                end
              | _ -> assert false in
          let _,args_rel =
            List.chop nparams (List.rev mip.Declarations.mind_arity_ctxt) in
          canonize_args args_rel l forbidden_names_for_gen [] [] in
        (Id.Set.of_list (List.map (fun id -> id.CAst.v) ind_ids),alias_subst,match_to_do),
        Some (CAst.make ?loc:(cases_pattern_expr_loc t) (ind,List.rev_map (fun x -> x.v) nal))
    | None ->
      (Id.Set.empty,Id.Map.empty,[]), None in
    (tm',(na.CAst.v, typ)), extra_id, match_td

  and intern_proj ?loc env expl (qid,us) args1 c args2 =
    let f,args1 =
      intern_applied_reference ~isproj:true intern env
        (Environ.named_context_val globalenv) lvar us args1 qid
    in
    match find_projection_data f with
    | Some (p, us, args0, nexpectedparams) ->
      (* A reference registered as projection *)
      check_not_notation_variable f ntnvars;
      let impl, subscopes = find_appl_head_data env lvar f in
      let imps1, imps2 =
        if expl then
          [], []
        else
          let ngivenparams = List.count (fun (_,x) -> Option.is_empty x) args1 in
          let nextraargs = List.length args2 in
          match select_impargs_size_for_proj ~nexpectedparams ~ngivenparams ~nextraargs impl with
          | Inl (imps1,imps2) -> (imps1,imps2)
          | Inr l ->
            let l = Lazy.force l in
            let n = match l with [n] -> n | _ -> 2 in (* singular only when l = [1] *)
            user_err ?loc:qid.CAst.loc (str "Projection " ++ pr_qualid qid ++ str " expected " ++ pr_choice int l ++
                           str (String.plural n " explicit parameter") ++ str ".")
      in
      let subscopes1, subscopes2 = List.chop (nexpectedparams + 1) subscopes in
      let c,args1 = List.sep_last (intern_impargs f env imps1 subscopes1 (args1@[c,None])) in
      let p = DAst.make ?loc (GProj ((p,us),args0@args1,c)) in
      let args2 = intern_impargs p env imps2 subscopes2 args2 in
      smart_gapp p loc args2
    | None ->
      (* Tolerate a use of t.(f) notation for an ordinary application until a decision is taken about it *)
      if expl then intern env (CAst.make ?loc (CAppExpl ((qid,us), List.map fst args1@c::List.map fst args2)))
      else intern env (CAst.make ?loc (CApp ((CAst.make ?loc:qid.CAst.loc (CRef (qid,us))), args1@(c,None)::args2)))

  and intern_impargs c env l subscopes args =
    let eargs, rargs = extract_explicit_arg l args in
    if !parsing_explicit then
      if List.is_empty eargs then intern_args env subscopes rargs
      else user_err Pp.(str "Arguments given by name or position not supported in explicit mode.")
    else
    let rec aux n impl subscopes eargs rargs =
      let (enva,subscopes') = apply_scope_env env subscopes in
      match (impl,rargs) with
      | (imp::impl', rargs) when is_status_implicit imp ->
          begin try
            let eargs',(_,(_,a)) = List.extract_first (fun (pos,a) -> match_implicit imp pos) eargs in
            intern_no_implicit enva a :: aux (n+1) impl' subscopes' eargs' rargs
          with Not_found ->
          if List.is_empty rargs && List.is_empty eargs && not (maximal_insertion_of imp) then
            (* Less regular arguments than expected: complete *)
            (* with implicit arguments if maximal insertion is set *)
            []
          else
              (DAst.map_from_loc (fun ?loc (a,b,c) -> GHole(a,b,c))
                (set_hole_implicit (n,get_implicit_name n l) (force_inference_of imp) c)
              ) :: aux (n+1) impl' subscopes' eargs rargs
          end
      | (imp::impl', a::rargs') ->
          intern_no_implicit enva a :: aux (n+1) impl' subscopes' eargs rargs'
      | (imp::impl', []) ->
          if not (List.is_empty eargs) then
            (let pr_position = function ExplByName id -> Id.print id | ExplByPos n -> str "position " ++ int n in
            let (pos,(loc,_)) = List.hd eargs in
               user_err ?loc (str "Not enough non implicit \
            arguments to accept the argument bound to " ++
                 pr_position pos ++ str"."));
          []
      | ([], rargs) ->
          assert (List.is_empty eargs);
          intern_args env subscopes rargs
    in aux 1 l subscopes eargs rargs

  and apply_impargs env loc c args =
    let impl, subscopes = find_appl_head_data env lvar c in
    let imp = select_impargs_size (List.length (List.filter (fun (_,x) -> x == None) args)) impl in
    let args = intern_impargs c env imp subscopes args in
    smart_gapp c loc args

  and smart_gapp f loc = function
    | [] -> f
    | l ->
      let loc' = f.CAst.loc in
      match DAst.get f with
      | GApp (g, args) -> DAst.make ?loc:(Loc.merge_opt loc' loc) @@ GApp (g, args@l)
      | _ -> DAst.make ?loc:(Loc.merge_opt (loc_of_glob_constr f) loc) @@ GApp (f, l)

  and intern_args env subscopes = function
    | [] -> []
    | a::args ->
      let (enva,subscopes) = apply_scope_env env subscopes in
      let a = intern_no_implicit enva a in
      a :: (intern_args env subscopes args)

  in
  intern env c

(**************************************************************************)
(* Functions to translate constr_expr into glob_constr                    *)
(**************************************************************************)

let extract_ids env =
  List.fold_right Id.Set.add
    (Termops.ids_of_rel_context (Environ.rel_context env))
    Id.Set.empty

let bound_univs sigma = Evd.universe_binders sigma

let scope_of_type_kind env sigma = function
  | IsType -> Notation.current_type_scope_name ()
  | OfType typ -> compute_type_scope env sigma typ
  | WithoutTypeConstraint | UnknownIfTermOrType -> None

let allowed_binder_kind_of_type_kind = function
  | IsType -> Some AbsPi
  | OfType _ | WithoutTypeConstraint -> Some AbsLambda
  | UnknownIfTermOrType -> None

let empty_ltac_sign = {
  ltac_vars = Id.Set.empty;
  ltac_bound = Id.Set.empty;
  ltac_extra = Genintern.Store.empty;
}

let intern_gen kind env sigma
               ?(impls=empty_internalization_env) ?(pattern_mode=false) ?(ltacvars=empty_ltac_sign)
               c =
  let tmp_scope = scope_of_type_kind env sigma kind in
  let k = allowed_binder_kind_of_type_kind kind in
  internalize env {ids = extract_ids env; unb = false;
                   local_univs = { bound = bound_univs sigma; unb_univs = true };
                   tmp_scope = tmp_scope; scopes = [];
                   impls; binder_block_names = Some k}
    pattern_mode (ltacvars, Id.Map.empty) c

let intern_constr env sigma c = intern_gen WithoutTypeConstraint env sigma c
let intern_type env sigma c = intern_gen IsType env sigma c
let intern_pattern globalenv patt =
  let env = {pat_ids = None; pat_scopes = (None, [])} in
  intern_cases_pattern test_kind_tolerant globalenv Id.Map.empty env empty_alias patt

(*********************************************************************)
(* Functions to parse and interpret constructions *)

(* All evars resolved *)

let interp_gen ?flags kind env sigma ?(impls=empty_internalization_env) c =
  let c = intern_gen kind ~impls env sigma c in
  understand ?flags ~expected_type:kind env sigma c

let interp_constr ?flags ?(expected_type=WithoutTypeConstraint) env sigma ?(impls=empty_internalization_env) c =
  interp_gen ?flags expected_type env sigma c

let interp_type ?flags env sigma ?(impls=empty_internalization_env) c =
  interp_gen ?flags IsType env sigma ~impls c

let interp_casted_constr ?flags env sigma ?(impls=empty_internalization_env) c typ =
  interp_gen ?flags (OfType typ) env sigma ~impls c

(* Not all evars expected to be resolved *)

let interp_open_constr ?(expected_type=WithoutTypeConstraint) env sigma c =
  understand_tcc env sigma (intern_gen expected_type env sigma c)

(* Not all evars expected to be resolved and computation of implicit args *)

let interp_constr_evars_gen_impls ?(flags=Pretyping.all_no_fail_flags) env sigma
    ?(impls=empty_internalization_env) expected_type c =
  let c = intern_gen expected_type ~impls env sigma c in
  let imps = Implicit_quantifiers.implicits_of_glob_constr ~with_products:(expected_type == IsType) c in
  let sigma, c = understand_tcc ~flags env sigma ~expected_type c in
  sigma, (c, imps)

let interp_constr_evars_impls ?(program_mode=false) env sigma ?(impls=empty_internalization_env) c =
  let flags = { Pretyping.all_no_fail_flags with program_mode } in
  interp_constr_evars_gen_impls ~flags env sigma ~impls WithoutTypeConstraint c

let interp_casted_constr_evars_impls ?(program_mode=false) env evdref ?(impls=empty_internalization_env) c typ =
  let flags = { Pretyping.all_no_fail_flags with program_mode } in
  interp_constr_evars_gen_impls ~flags env evdref ~impls (OfType typ) c

let interp_type_evars_impls ?(flags=Pretyping.all_no_fail_flags) env sigma ?(impls=empty_internalization_env) c =
  interp_constr_evars_gen_impls ~flags env sigma ~impls IsType c

(* Not all evars expected to be resolved, with side-effect on evars *)

let interp_constr_evars_gen ?(program_mode=false) env sigma ?(impls=empty_internalization_env) expected_type c =
  let c = intern_gen expected_type ~impls env sigma c in
  let flags = { Pretyping.all_no_fail_flags with program_mode } in
  understand_tcc ~flags env sigma ~expected_type c

let interp_constr_evars ?program_mode env evdref ?(impls=empty_internalization_env) c =
  interp_constr_evars_gen ?program_mode env evdref WithoutTypeConstraint ~impls c

let interp_casted_constr_evars ?program_mode env sigma ?(impls=empty_internalization_env) c typ =
  interp_constr_evars_gen ?program_mode env sigma ~impls (OfType typ) c

let interp_type_evars ?program_mode env sigma ?(impls=empty_internalization_env) c =
  interp_constr_evars_gen ?program_mode env sigma IsType ~impls c

(* Miscellaneous *)

let intern_constr_pattern env sigma ?(as_type=false) ?(ltacvars=empty_ltac_sign) c =
  let c = intern_gen (if as_type then IsType else WithoutTypeConstraint)
            ~pattern_mode:true ~ltacvars env sigma c in
  pattern_of_glob_constr c

let interp_constr_pattern env sigma ?(expected_type=WithoutTypeConstraint) c =
  let c = intern_gen expected_type ~pattern_mode:true env sigma c in
  let flags = { Pretyping.no_classes_no_fail_inference_flags with expand_evars = false } in
  let sigma, c = understand_tcc ~flags env sigma ~expected_type c in
  (* FIXME: it is necessary to be unsafe here because of the way we handle
     evars in the pretyper. Sometimes they get solved eagerly. *)
  legacy_bad_pattern_of_constr env sigma c

let intern_core kind env sigma ?(pattern_mode=false) ?(ltacvars=empty_ltac_sign)
      { Genintern.intern_ids = ids; Genintern.notation_variable_status = vl } c =
  let tmp_scope = scope_of_type_kind env sigma kind in
  let impls = empty_internalization_env in
  let k = allowed_binder_kind_of_type_kind kind in
  internalize env
    {ids; unb = false;
     local_univs = { bound = bound_univs sigma; unb_univs = true };
     tmp_scope; scopes = []; impls;
     binder_block_names = Some k}
    pattern_mode (ltacvars, vl) c

let interp_notation_constr env ?(impls=empty_internalization_env) nenv a =
  let ids = extract_ids env in
  (* [vl] is intended to remember the scope of the free variables of [a] *)
  let vl = Id.Map.map (function
    | (NtnInternTypeAny None | NtnInternTypeOnlyBinder) as typ -> (ref false, ref None, typ)
    | NtnInternTypeAny (Some scope) as typ ->
        (ref false, ref (Some (Some scope,[])), typ)
    ) nenv.ninterp_var_type in
  let impls = Id.Map.fold (fun id _ impls -> Id.Map.remove id impls) nenv.ninterp_var_type impls in
  let c = internalize env
      {ids; unb = false;
       local_univs = empty_local_univs;
       tmp_scope = None; scopes = []; impls; binder_block_names = None}
      false (empty_ltac_sign, vl) a
  in
  (* Splits variables into those that are binding, bound, or both *)
  (* Translate and check that [c] has all its free variables bound in [vars] *)
  let a, reversible = notation_constr_of_glob_constr nenv c in
  (* binding and bound *)
  let out_scope = function None -> None,[] | Some (a,l) -> a,l in
  let unused = match reversible with NonInjective ids -> ids | _ -> [] in
  let vars = Id.Map.mapi (fun id (used_as_binder, sc, typ) ->
    (!used_as_binder && not (List.mem_f Id.equal id unused), out_scope !sc)) vl in
  (* Returns [a] and the ordered list of variables with their scopes *)
  vars, a, reversible

(* Interpret binders and contexts  *)

let interp_binder env sigma na t =
  let t = intern_gen IsType env sigma t in
  let t' = locate_if_hole ?loc:(loc_of_glob_constr t) na t in
  understand ~expected_type:IsType env sigma t'

let interp_binder_evars env sigma na t =
  let t = intern_gen IsType env sigma t in
  let t' = locate_if_hole ?loc:(loc_of_glob_constr t) na t in
  understand_tcc env sigma ~expected_type:IsType t'

let my_intern_constr env lvar acc c =
  internalize env acc false lvar c

let intern_context env ~bound_univs impl_env binders =
  let lvar = (empty_ltac_sign, Id.Map.empty) in
  let ids =
    (* We assume all ids around are parts of the prefix of the current
       context being interpreted *)
     extract_ids env in
  let lenv, bl = List.fold_left
            (fun (lenv, bl) b ->
               let (env, bl) = intern_local_binder_aux (my_intern_constr env lvar) Id.Map.empty (lenv, bl) b in
               (env, bl))
            ({ids; unb = false;
              local_univs = { bound = bound_univs; unb_univs = true };
              tmp_scope = None; scopes = []; impls = impl_env;
              binder_block_names = Some (Some AbsPi)}, []) binders in
  (lenv.impls, List.map glob_local_binder_of_extended bl)

let interp_glob_context_evars ?(program_mode=false) env sigma bl =
  let open EConstr in
  let flags = { Pretyping.all_no_fail_flags with program_mode } in
  let env, sigma, par, impls =
    List.fold_left
      (fun (env,sigma,params,impls) (na, k, b, t) ->
       let t' =
         if Option.is_empty b then locate_if_hole ?loc:(loc_of_glob_constr t) na t
         else t
       in
       let sigma, t = understand_tcc ~flags env sigma ~expected_type:IsType t' in
        match b with
          None ->
              let r = Retyping.relevance_of_type env sigma t in
              let d = LocalAssum (make_annot na r,t) in
              let impls =
                match k with
                | NonMaxImplicit -> CAst.make (Some (na,false)) :: impls
                | MaxImplicit -> CAst.make (Some (na,true)) :: impls
                | Explicit -> CAst.make None :: impls
              in
                (push_rel d env, sigma, d::params, impls)
          | Some b ->
              let sigma, c = understand_tcc ~flags env sigma ~expected_type:(OfType t) b in
              let r = Retyping.relevance_of_type env sigma t in
              let d = LocalDef (make_annot na r, c, t) in
                (push_rel d env, sigma, d::params, impls))
      (env,sigma,[],[]) (List.rev bl)
  in
  sigma, ((env, par), List.rev impls)

let interp_context_evars ?program_mode ?(impl_env=empty_internalization_env) env sigma params =
  let int_env,bl = intern_context env ~bound_univs:(bound_univs sigma) impl_env params in
  let sigma, x = interp_glob_context_evars ?program_mode env sigma bl in
  sigma, (int_env, x)

let interp_named_context_evars ?(program_mode=false) ?(impl_env=empty_internalization_env) env sigma bl =
  let open EConstr in
  let lvar = (empty_ltac_sign, Id.Map.empty) in
  let ids =
    (* We assume all ids around are parts of the prefix of the current
       context being interpreted *)
     extract_ids env in
  let int_env = {ids; unb = false;
              local_univs = { bound = bound_univs sigma; unb_univs = true };
              tmp_scope = None; scopes = []; impls = impl_env;
              binder_block_names = Some (Some AbsPi)} in
  let flags = { Pretyping.all_no_fail_flags with program_mode } in
  let (int_env, (env, sigma, bl, impls)) =
    List.fold_left
      (fun (int_env, acc) b ->
        let int_env, bl = intern_local_binder_aux (my_intern_constr env lvar) Id.Map.empty (int_env,[]) b in
        let bl = List.map glob_local_binder_of_extended bl in
        let acc = List.fold_right (fun (na, bk, b, t) (int_env, (env,sigma,params,impls)) ->
          let id = match na with
          | Name id -> id
          | Anonymous -> user_err Pp.(str "Unexpected anonymous variable.")
          in
          let open Context.Named.Declaration in
          match b with
          | None ->
            let t' = locate_if_hole ?loc:(loc_of_glob_constr t) na t in (* useful? *)
            let sigma, t = understand_tcc ~flags env sigma ~expected_type:IsType t' in
            let (ty,imps,sc,uid) = Id.Map.find id int_env.impls in
            let imps = List.map (function None -> CAst.make None | Some (_,_,(max,_)) -> CAst.make @@ Some (na,max)) imps in
            let imps = compute_internalization_data env sigma id ty t imps in
            let int_env = { int_env with impls = Id.Map.add id imps int_env.impls } in
            let r = Retyping.relevance_of_type env sigma t in
            let d = LocalAssum (make_annot id r,t) in
            let impls =
              match bk with
              | NonMaxImplicit -> CAst.make (Some (na,false)) :: impls
              | MaxImplicit -> CAst.make (Some (na,true)) :: impls
              | Explicit -> CAst.make None :: impls
            in
            (int_env, (push_named d env, sigma, d::params, impls))
          | Some b ->
            assert (bk = Explicit);
            let sigma, t = understand_tcc ~flags env sigma ~expected_type:IsType t in
            let sigma, c = understand_tcc ~flags env sigma ~expected_type:(OfType t) b in
            let r = Retyping.relevance_of_type env sigma t in
            let d = LocalDef (make_annot id r, c, t) in
            (int_env, (push_named d env, sigma, d::params, impls)))
          bl (int_env,acc) in
        acc)
      (int_env,(env,sigma,[],[])) bl
  in
  sigma, (int_env.impls, ((env, bl), List.rev impls))

(** Local universe and constraint declarations. *)

let known_universe_level_name evd lid =
  try Evd.universe_of_name evd lid.CAst.v
  with Not_found ->
    let u = Nametab.locate_universe (Libnames.qualid_of_lident lid) in
    Univ.Level.make u

let known_glob_level evd = function
  | GSProp | GProp ->
    CErrors.user_err (Pp.str "Universe constraints cannot mention Prop or SProp.")
  | GSet -> Univ.Level.set
  | GUniv u -> u
  | GRawUniv u -> anomaly Pp.(str "Raw universe in known_glob_level.")
  | GLocalUniv lid ->
    try known_universe_level_name evd lid
    with Not_found ->
      user_err ?loc:lid.CAst.loc
        (str "Undeclared universe " ++ Id.print lid.CAst.v)

let interp_known_level evd u =
  let u = intern_sort_name ~local_univs:{bound = bound_univs evd; unb_univs=false} u in
  known_glob_level evd u

let interp_univ_constraint evd (u,c,v) =
  let u = interp_known_level evd u in
  let v = interp_known_level evd v in
  u,c,v

let interp_univ_constraints env evd cstrs =
  let interp (evd,cstrs) cstr =
    let cstr = interp_univ_constraint evd cstr in
    try
      let evd = Evd.add_constraints evd (Univ.Constraints.singleton cstr) in
      evd, Univ.Constraints.add cstr cstrs
    with UGraph.UniverseInconsistency e as exn ->
      let _, info = Exninfo.capture exn in
      CErrors.user_err ~info
        (UGraph.explain_universe_inconsistency (Termops.pr_evd_level evd) e)
  in
  List.fold_left interp (evd,Univ.Constraints.empty) cstrs

let interp_univ_decl env decl =
  let open UState in
  let binders : lident list = decl.univdecl_instance in
  let evd = Evd.from_env ~binders env in
  let evd, cstrs = interp_univ_constraints env evd decl.univdecl_constraints in
  let decl = {
    univdecl_instance = binders;
    univdecl_extensible_instance = decl.univdecl_extensible_instance;
    univdecl_constraints = cstrs;
    univdecl_extensible_constraints = decl.univdecl_extensible_constraints;
  }
  in evd, decl

let interp_cumul_univ_decl env decl =
  let open UState in
  let binders = List.map fst decl.univdecl_instance in
  let variances = Array.map_of_list snd decl.univdecl_instance in
  let evd = Evd.from_ctx (UState.from_env ~binders env) in
  let evd, cstrs = interp_univ_constraints env evd decl.univdecl_constraints in
  let decl = {
    univdecl_instance = binders;
    univdecl_extensible_instance = decl.univdecl_extensible_instance;
    univdecl_constraints = cstrs;
    univdecl_extensible_constraints = decl.univdecl_extensible_constraints;
  }
  in
  evd, decl, variances

let interp_univ_decl_opt env l =
  match l with
  | None -> Evd.from_env env, UState.default_univ_decl
  | Some decl -> interp_univ_decl env decl

let interp_cumul_univ_decl_opt env = function
  | None -> Evd.from_env env, UState.default_univ_decl, [| |]
  | Some decl -> interp_cumul_univ_decl env decl
