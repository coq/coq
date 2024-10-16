(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


let debug_dependent_congruence = CDebug.create ~name:"dependent_congruence" ()


let print env sigma t = Printer.pr_econstr_env env sigma t

(*get the ith (1 based) argument in a series of prods*)
let get_ith_arg sigma i term =
  let (rels_to_arg,rest) = EConstr.decompose_prod_n sigma (i-1) term in
  let (arg_name,arg_type,rest) = EConstr.destProd sigma rest in
  (rels_to_arg, (arg_name, arg_type), rest)

(*determin if the ith (1 based real constructor arguments without parametes) field of a constructor depends on its other fields*)
let is_field_i_dependent env sigma cnstr i : bool =
  let constructor_type = Inductiveops.e_type_of_constructor env sigma cnstr in
  let ind_n_params = Inductiveops.inductive_nparams env (fst (fst cnstr)) in
  let (field_rel_context,(_,field_type),_) = get_ith_arg sigma (i + ind_n_params) constructor_type in
  debug_dependent_congruence (fun () -> Pp.(
    str "++++++++++++++++++++++++" ++ str "\n" ++
    str "+ IS FIELD I DEPENDENT +" ++ str "\n" ++
    str "++++++++++++++++++++++++" ++ str "\n" ++
    str "cnstr:\n" ++ Printer.pr_constructor env (fst cnstr) ++ str "\n" ++
    str "i:\n" ++ int i ++ str "\n" ++
    str "constructor_type:\n" ++ print env sigma constructor_type ++ str "\n" ++
    str "ind_n_params:\n" ++ int ind_n_params ++ str "\n" ++
    str "field_type:\n" ++ print (List.fold_left (fun env annot -> Termops.push_rel_assum annot env) env field_rel_context) sigma field_type ++ str "\n"
    ));
  let rec is_field_i_dependent_rec i =
  (
    if i <= 0
        then false
    else
      if Termops.dependent sigma (EConstr.mkRel i) field_type
        then true
    else is_field_i_dependent_rec (i-1)
  ) in is_field_i_dependent_rec (i-1)

let fresh_id env id =
  Namegen.next_ident_away id (Environ.ids_of_named_context_val @@ Environ.named_context_val env)

let build_simple_projection env sigma intype cnstr special default =
  let open EConstr in
  let open Names in
  let open Context in
  let ci = (snd (fst cnstr)) in
  let body = Combinators.make_selector env sigma ~pos:ci ~special ~default (mkRel 1) intype in
  let id = fresh_id env (Id.of_string "t") in
  sigma, mkLambda (make_annot (Name id) ERelevance.relevant, intype, body)

type type_extraction =
(* The term that is getting extracted *)
| Id of EConstr.t
(* The rel term that is getting extracted, the rel term from wich its getting extracted, The constructor from which to extract, Type of the Cosntructor that is getting extracted, index (1 based) to extract from, further extraction *)
| Extraction of (EConstr.t * EConstr.t * (Names.constructor * EConstr.EInstance.t) * EConstr.t * int * type_extraction)

let pr_type_extraction env sigma ?(level="") (type_extraction:type_extraction) =
  let rec pr_type_extraction_rec type_extraction level =
    match type_extraction with
    | Id e -> Pp.(str level ++ str "Id: " ++ print env sigma e)
    | Extraction (re_term_to_extract, rel_term_to_extract_from, (cnstr, u), env_term_to_extract_from, index, extraction) ->
      let (_,env_type_to_extract_from) = Typing.type_of env sigma env_term_to_extract_from in
      Pp.(
        str level ++ str "extract: " ++ print env sigma re_term_to_extract ++ str "\n" ++
        str level ++ str "from: " ++ print env sigma rel_term_to_extract_from ++ str "\n" ++
        str level ++ str "type: " ++ print env sigma env_type_to_extract_from ++ str "\n" ++
        str level ++ str "in: " ++ Printer.pr_constructor env cnstr ++ str "\n" ++
        str level ++ str "index: " ++ int index ++ str "\n" ++
        str level ++ str "by:\n" ++ pr_type_extraction_rec extraction (level ^ "\t")
      )
  in pr_type_extraction_rec type_extraction level

type type_composition =
(* env type to compose *)
| FromEnv of EConstr.t
(* env type to compose, env parameter term to extract from, index (1 based) of parameter, extraction for the given type*)
| FromParameter of EConstr.t * EConstr.t * int * type_extraction
(* env type to compose, rel index term to extract from, index (1 based) index to compose from, extraction for the given type *)
| FromIndex of EConstr.t * EConstr.t * int * type_extraction
(* (env f type to compose, composition for f), array of (env arg type to compose, composition for arg)*)
| Composition of (EConstr.t * type_composition) * (EConstr.t * type_composition) array

let pr_type_composition env sigma ?(level="") type_composition  =
  let rec pr_type_composition_rec type_composition level =
    match type_composition with
    | FromEnv e -> Pp.(str "From Env: " ++ print env sigma e)
    | FromParameter (type_to_compose, type_to_compose_from, index, extraction)->
      Pp.(
        str level ++ str "compose: " ++ print env sigma type_to_compose ++ str "\n" ++
        str level ++ str "from param: " ++ print env sigma type_to_compose_from ++ str "\n" ++
        str level ++ str "at: " ++ int index ++ str "\n" ++
        str level ++ str "by: " ++ pr_type_extraction env sigma extraction ~level:(level ^"\t") ++ str "\n"
      )
    | FromIndex (type_to_compose, type_to_compose_from, index, extraction)->
      Pp.(
        str level ++ str "compose: " ++ print env sigma type_to_compose ++ str "\n" ++
        str level ++ str "from index: " ++ print env sigma type_to_compose_from ++ str "\n" ++
        str level ++ str "at: " ++ int index ++ str "\n" ++
        str level ++ str "by:\n" ++ pr_type_extraction env sigma extraction ~level:(level ^ "\t") ++ str "\n"
      )
    | Composition ((f,f_composition), args_compositions) ->
      Pp.(
        str level ++ str "compose: " ++ print env sigma f ++ str "(" ++ seq (List.map (fun (arg,_) -> print env sigma arg ++ str ", ") (Array.to_list args_compositions)) ++ str ")" ++ str "\n" ++
                     pr_type_composition_rec f_composition (level ^ "\t") ++ str "\n" ++
        str level ++ str "(" ++ str "\n" ++
                     seq (List.map (fun (_,c) -> pr_type_composition_rec c (level ^ "\t") ++ str ", ") (Array.to_list args_compositions)) ++ str "\n" ++
        str level ++ str ")" ++ str "\n"
      )
  in pr_type_composition_rec type_composition level

type projection_type =
| Simple
| Dependent of type_composition
| NotProjectable

(*find a composition to form a given term by extracting from given terms*)
let find_type_composition
  env sigma (cnstr:Names.constructor * EConstr.EInstance.t) (argindex:int) (env_field_type:EConstr.t) (ind:Names.inductive EConstr.puniverses) (env_ind_params:EConstr.t array) (env_ind_args:EConstr.t array)
  : (Evd.evar_map * type_composition option) =
  let env_ind_n_params = Array.length env_ind_params in
  let rel_type_of_constructor = Inductiveops.type_of_constructor env cnstr in
  let (rel_field_context, (rel_field_annot, rel_field_type), rel_field_rest) = get_ith_arg sigma (argindex+env_ind_n_params) rel_type_of_constructor in
  let rel_field_rest_env = (List.fold_left (fun env annot -> Termops.push_rel_assum annot env) env (((rel_field_annot, rel_field_type)::rel_field_context))) in
  let (rel_target_context, rel_target_type) = EConstr.decompose_prod sigma rel_field_rest in
  let rel_field_type_lifted = EConstr.Vars.lift (List.length rel_target_context + 1) rel_field_type in
  let (_,rel_args) = EConstr.decompose_app sigma rel_target_type in
  let (rel_ind_params, rel_ind_args) = CArray.chop env_ind_n_params rel_args in
  let rel_target_env = (List.fold_left (fun env annot -> Termops.push_rel_assum annot env) env (rel_target_context @ ((rel_field_annot, rel_field_type)::rel_field_context))) in
  debug_dependent_congruence  ( fun () -> Pp.(
    str "+++++++++++++++++++++++++" ++ str "\n" ++
    str "+ FIND TYPE COMPOSITION +" ++ str "\n" ++
    str "+++++++++++++++++++++++++" ++ str "\n" ++
    str "cnstr:\n\t" ++ Printer.pr_constructor env (fst cnstr) ++ str "\n" ++
    str "argindex:\n\t" ++ int argindex ++ str "\n" ++
    str "env_field_type:\n\t" ++ print env sigma env_field_type ++ str "\n" ++
    str "ind:\n\t" ++ Printer.pr_inductive env (fst ind) ++ str "\n" ++
    str "ind_params:\n\t" ++ seq (List.map (fun e -> print env sigma e ++ str ", ") (Array.to_list env_ind_params)) ++ str "\n" ++
    str "ind_args:\n\t" ++ seq (List.map (fun e -> print env sigma e ++ str ", ") (Array.to_list env_ind_args)) ++ str "\n" ++
    str "rel_type_of_constructor:\n\t" ++ print env sigma rel_type_of_constructor ++ str "\n" ++
    str "rel_field_type:\n\t" ++ print rel_target_env sigma rel_field_type_lifted ++ str "\n" ++
    str "rel_field_rest:\n\t" ++ print rel_field_rest_env sigma rel_field_rest ++ str "\n" ++
    str "rel_target_type:\n\t" ++ print rel_target_env sigma rel_target_type ++ str "\n" ++
    str "rel_ind_params:\n\t" ++ seq (List.map (fun e -> print rel_target_env sigma e ++ str ", ") (Array.to_list rel_ind_params)) ++ str "\n" ++
    str "rel_args:\n\t" ++ seq (List.map (fun e -> print rel_target_env sigma e ++ str ", ") (Array.to_list rel_args)) ++ str "\n" ++
    str "rel_ind_args:\n\t" ++ seq (List.map (fun e -> print rel_target_env sigma e ++ str ", ") (Array.to_list rel_ind_args)) ++ str "\n" ++
    str "env_ind_params:\n\t" ++ seq (List.map (fun e -> print env sigma e ++ str ", ") (Array.to_list env_ind_params)) ++ str "\n" ++
    str "env_ind_args:\n\t" ++ seq (List.map (fun e -> print env sigma e ++ str ", ") (Array.to_list env_ind_args)) ++ str "\n"
  ));

  let rec find_type_composition_rec env sigma (rel_term_to_compose:EConstr.t) (env_term_to_compose:EConstr.t)=
    let rel_term_to_compose_kind = EConstr.kind sigma rel_term_to_compose in
    match rel_term_to_compose_kind with
    | Var _ | Const _ | Ind _ | Construct _ -> (sigma, Some (FromEnv rel_term_to_compose))
    | _ ->(
      match find_arg env sigma rel_term_to_compose rel_ind_params env_ind_params with
      | Some (i, rel_term_to_compose_from, extraction) ->
        debug_dependent_congruence (fun () -> Pp.(str"FOUND " ++ int i));
        debug_dependent_congruence (fun () -> Pp.(str"FOUND " ++ print env sigma env_ind_params.(i-1)));
        (sigma, Some (FromParameter (env_term_to_compose, env_ind_params.(i-1), i, extraction)))
      | None -> (
        match find_arg env sigma rel_term_to_compose rel_ind_args env_ind_args with
        | Some (i, rel_term_to_compose_from, extraction) -> (sigma, Some (FromIndex (env_term_to_compose, rel_term_to_compose_from, i, extraction)))
        | None ->(
          match rel_term_to_compose_kind with
          | App (rel_f,rel_args) ->(
            let (env_f,env_args) = EConstr.decompose_app sigma env_term_to_compose in
            let (sigma, f_composition) = find_type_composition_rec env sigma rel_f env_f in
            debug_dependent_congruence (fun () -> Pp.(
              str "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n"++
              str "env_term_to_compose: " ++ print env sigma env_term_to_compose ++ str "\n" ++
              str "rel_term_to_compose: " ++ print env sigma rel_term_to_compose ++ str "\n" ++
              str "rel_f: " ++ print env sigma rel_f ++ str "\n" ++
              str "env_f: " ++ print env sigma env_f ++ str "\n" ++
              str "rel_args: " ++ seq (List.map ( fun e -> print env sigma e) (Array.to_list rel_args) ) ++ str "\n" ++
              str "env_args: " ++ seq (List.map ( fun e -> print env sigma e) (Array.to_list env_args) ) ++ str "\n"
            ));
            match f_composition with
            | Some f_composition ->(
              if Array.length env_args != Array.length rel_args then (sigma, None) else
              let (sigma, args_compositions) = (
                  let exception ArgNotComposable of Evd.evar_map in
                  try(
                    let (sigma, args_compositions) =
                      CArray.fold_left_map_i
                        (fun i sigma rel_arg ->
                          debug_dependent_congruence (fun () -> Pp.(str "!!!try!!!" ++ int i));
                          debug_dependent_congruence (fun () -> Pp.(str "!!!with!!!" ++ print env sigma rel_arg));
                          debug_dependent_congruence (fun () -> Pp.(str "!!!with!!!" ++ print env sigma env_args.(i)));

                          let (sigma, arg_composition) = find_type_composition_rec env sigma rel_arg env_args.(i) in
                          match arg_composition with
                          | Some arg_composition -> (sigma, (env_args.(i), arg_composition))
                          | None -> raise (ArgNotComposable sigma)
                        )
                        sigma
                        rel_args
                    in
                    (sigma, Some args_compositions)
                  ) with ArgNotComposable sigma -> (sigma, None)
              ) in
              match args_compositions with
              | Some args_compositions ->(
                (sigma, Some (Composition ((env_f, f_composition), args_compositions)))
              )
              | None -> (sigma, None)
            )
            | None -> (sigma, None)
          )
          | _ -> (sigma, None)
        )
      )
    )
  and find_arg env sigma (term_to_extract:EConstr.t) (terms_to_extract_from:EConstr.t array) (env_types_of_fields:EConstr.t array): (int * EConstr.t * type_extraction) option =
    debug_dependent_congruence (fun () -> Pp.(
      str "++++++++++++" ++ str "\n" ++
      str "+ FIND ARG +" ++ str "\n" ++
      str "++++++++++++" ++ str "\n" ++
      str "term_to_extract:\n\t" ++ print env sigma term_to_extract ++ str "\n" ++
      str "terms_to_extract_from:\n\t" ++ seq (List.map (fun e -> print env sigma e ++ str ", ") (Array.to_list terms_to_extract_from)) ++ str "\n" ++
      str "env_types_of_fields:\n\t" ++ seq (List.map (fun e -> print env sigma e ++ str ", ") (Array.to_list env_types_of_fields)) ++ str "\n"
    ));
    let rec seq_find_map f xs =
      match xs() with
      | Seq.Nil -> None
      | Seq.Cons(x,xs) ->
        match f x with
        | None -> seq_find_map f xs
        | Some _ as result -> result
    in
    seq_find_map
      (fun (i, term_to_extract_from) ->
        debug_dependent_congruence (fun () -> Pp.(str "try i: " ++ int i));
        Option.map
          (fun r -> (i+1, term_to_extract_from, r))
          (find_extraction env sigma term_to_extract term_to_extract_from env_types_of_fields.(i))
      )
      (Array.to_seqi terms_to_extract_from)
  and find_extraction env sigma (term_to_extract:EConstr.t) (term_to_extract_from:EConstr.t) (type_of_term_to_extract_from:EConstr.t): type_extraction option =
    debug_dependent_congruence (fun () -> Pp.(
      str "+++++++++++++++++++" ++ str "\n" ++
      str "+ FIND EXTRACTION +" ++ str "\n" ++
      str "+++++++++++++++++++" ++ str "\n" ++
      str "term_to_extract:\n\t" ++ print env sigma term_to_extract ++ str "\n" ++
      str "term_to_extract_from:\n\t" ++ print env sigma term_to_extract_from ++ str "\n" ++
      str "type_of_term_to_extract_from:\n\t" ++ print env sigma type_of_term_to_extract_from ++ str "\n"
    ));
    if EConstr.eq_constr_nounivs sigma term_to_extract term_to_extract_from
    then(
      Some (Id term_to_extract)
    )
    else(
      match EConstr.kind sigma term_to_extract_from with
      | App (f, args) -> (
          match EConstr.kind sigma f with
          | Construct c -> (
              let (_,env_args) = EConstr.decompose_app sigma type_of_term_to_extract_from in
              let first_arg_option =
                find_arg env sigma term_to_extract args env_args
              in
              match first_arg_option with
              | Some (i, arg_to_extract_from, extraction_result) ->
                Some (Extraction (term_to_extract, arg_to_extract_from, c, type_of_term_to_extract_from, i, extraction_result))
              | None -> None
          )
          | _ -> None
      )
      | _ -> None
    )
  in find_type_composition_rec env sigma rel_field_type_lifted env_field_type

let projectability_test
  env sigma (cnstr:Names.constructor * EConstr.EInstance.t) (argindex:int) (field_type:EConstr.t) (ind: Names.inductive EConstr.puniverses) (ind_params:EConstr.t array) (ind_args:EConstr.t array)
  : (Evd.evar_map * projection_type) =
  let dependent = is_field_i_dependent env sigma cnstr argindex in
  if dependent then (
    debug_dependent_congruence (fun () -> Pp.(str "DEPENDENT"));
    let (sigma, composition) = find_type_composition env sigma cnstr argindex field_type ind ind_params ind_args in
    match composition with
    | Some composition -> (sigma, Dependent composition)
    | None -> (sigma, NotProjectable)
  )
  else (
    debug_dependent_congruence (fun () -> Pp.(str "SIMPLE"));
    (sigma, Simple)
  )

let rec build_extraction env sigma default rel_term_to_extract_from env_term_to_extract_from extraction =
  debug_dependent_congruence (fun () -> Pp.(
    str "++++++++++++++++++++" ++ str "\n" ++
    str "+ BUILD EXTRACTION +" ++ str "\n" ++
    str "++++++++++++++++++++" ++ str "\n" ++
    str "extraction:\n\t" ++ pr_type_extraction env sigma extraction ++ str "\n" ++
    str "rel_term_to_extract_from:\n\t" ++ print env sigma rel_term_to_extract_from ++ str "\n" ++
    str "env_term_to_extract_from:\n\t" ++ print env sigma env_term_to_extract_from ++ str "\n"
  ));
  match extraction with
  (* The term that is getting extracted *)
  | Id term_getting_extracted -> rel_term_to_extract_from
  (* The term that is getting extracted, the term from wich its getting extracted, The constructor from which zu extract, index (1 based without params) to extract from, further extraction *)
  | Extraction (rel_term_getting_extracted, rel_next_term_to_extrect_from, (cnstr, u), env_next_term_to_extract_from, index, next_extraction) -> (
    let cnstr_n_args = Inductiveops.constructor_nrealargs env cnstr in
    let special = build_extraction env sigma default (EConstr.mkRel (cnstr_n_args-(index-1))) env_next_term_to_extract_from next_extraction in
    let pos = snd cnstr in
    let (_,match_type) = Typing.type_of env sigma env_term_to_extract_from in
    Combinators.make_selector env sigma ~pos ~special ~default rel_term_to_extract_from match_type
  )


let rec build_type_composition env sigma type_composition ind_params n_ind_params ind_args n_ind_args =
  debug_dependent_congruence (fun () -> Pp.(
    str "+++++++++++++++++++++" ++ str "\n" ++
    str "+ BUILD RETURN TYPE +" ++ str "\n" ++
    str "+++++++++++++++++++++" ++ str "\n" ++
    str "type_composition:\n\t" ++ pr_type_composition env sigma type_composition ++ str "\n" ++
    str "ind_params:\n\t" ++ seq (List.map (fun e -> print env sigma e ++ str ", ") (Array.to_list ind_params)) ++ str "\n" ++
    str "n_ind_params:\n\t" ++ int n_ind_params ++ str "\n" ++
    str "ind_args:\n\t" ++ seq (List.map (fun e -> print env sigma e ++ str ", ") (Array.to_list ind_args)) ++ str "\n" ++
    str "n_ind_args:\n\t" ++ int n_ind_args ++ str "\n"
  ));
  match type_composition with
  (* type to compose *)
  | FromEnv env_type_to_compose -> env_type_to_compose
  (* type to compose, parameter term to extract from, index (1 based) of parameter, extraction for the given type*)
  | FromParameter (env_type_to_compose, env_parameter_to_extract_from, parameter_index, extraction) -> ( (* TODO: parameters don't bind so make them accasibble some other way*)
    let type_to_extract_from = ind_params.(parameter_index-1) in
    build_extraction env sigma env_type_to_compose env_parameter_to_extract_from type_to_extract_from extraction
    )
    (* type to compose, indec term to extract from, index (1 based) index to compose from, extraction for the given type *)
    | FromIndex (env_type_to_compose, index_to_compose_from, index_index, extraction) ->(
    let type_to_extract_from = ind_args.(index_index-1) in
    build_extraction env sigma env_type_to_compose (EConstr.mkRel (n_ind_args-(index_index-1))) type_to_extract_from extraction
  )
  (* (f type to compose, composition for f), array of (arg type to compose, composition for arg)*)
  | Composition ((f_to_compose , f_composition),  arg_compositions) -> (
    let f_extraction_term = build_type_composition env sigma f_composition ind_params n_ind_params ind_args n_ind_args in
    let arg_extraction_terms = Array.map (fun (_,arg_composition) -> build_type_composition env sigma arg_composition ind_params n_ind_params ind_args n_ind_args) arg_compositions in
    EConstr.mkApp (f_extraction_term, arg_extraction_terms)
  )

let match_indices env sigma (cnst_summary:Inductiveops.constructor_summary) term_to_match n_ind_args max_free_rel =
  let rec replace_rec n t = (
    match EConstr.kind sigma t with
    | Rel i-> (
      if i <= n_ind_args + n && i > n then
        cnst_summary.cs_concl_realargs.(n_ind_args-i)
      else
        t
    )
    | _ -> EConstr.map_with_binders sigma (fun n -> n+1) replace_rec n t
  ) in
  EConstr.map_with_binders sigma (fun n -> n+1) replace_rec 0 term_to_match

let make_annot_numbered s i r =
  Context.make_annot (Names.Name.mk_name (Nameops.make_ident s i)) r

let make_selector_match_indices env sigma ~pos ~special c (ind_fam, ind_args) return_type composition_type_template =
  let open Inductiveops in
  let open EConstr in
  let n_ind_args = List.length ind_args in
  let indt = Inductiveops.IndType (ind_fam, ind_args) in
  let (ind, _),_ = dest_ind_family ind_fam in
  let () = Tacred.check_privacy env ind in
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let deparsign = make_arity_signature env sigma true ind_fam in
  let p = it_mkLambda_or_LetIn return_type deparsign in
  let cstrs = get_constructors env ind_fam in
  let build_branch i =
    let max_free_rel = Option.default 0 (Int.Set.max_elt_opt (Termops.free_rels sigma composition_type_template)) in
    let matched_template = match_indices env sigma cstrs.(i-1) composition_type_template n_ind_args max_free_rel in
    let endpt = if Int.equal i pos then
      EConstr.mkLambda (Context.make_annot Names.Name.Anonymous EConstr.ERelevance.relevant, matched_template, EConstr.Vars.lift 1 special)
    else
      EConstr.mkLambda (make_annot_numbered "t" None EConstr.ERelevance.relevant, matched_template, EConstr.mkRel 1)
    in
    let args = cstrs.(i-1).cs_args in
    it_mkLambda_or_LetIn endpt args in
  let brl =
    List.map build_branch(CList.interval 1 (Array.length mip.mind_consnames)) in
  let rci = ERelevance.relevant in (* TODO relevance *)
  let ci = make_case_info env ind RegularStyle in
  Inductiveops.make_case_or_project env sigma indt ci (p, rci) c (Array.of_list brl)

let build_dependent_projection env sigma cnstr default special argty type_composition ((ind, ind_params) as ind_fam) ind_args: (Evd.evar_map * EConstr.t) =
  debug_dependent_congruence (fun () -> Pp.(
    str "++++++++++++++++++++++++++++++" ++ str "\n" ++
    str "+ BUILD DEPENDENT PROJECTION +" ++ str "\n" ++
    str "++++++++++++++++++++++++++++++" ++ str "\n" ++
    str "type_composition:\n\t" ++ pr_type_composition env sigma type_composition ++ str "\n"
  ));
  let n_ind_params = List.length ind_params in
  let n_ind_args = List.length ind_args in
  let composition_type_template = build_type_composition env sigma type_composition (Array.of_list ind_params) n_ind_params (Array.of_list ind_args) n_ind_args in
  debug_dependent_congruence (fun () -> Pp.(str "return_type_template: " ++ print env sigma composition_type_template));
  let return_type = EConstr.Vars.lift 1 (
    EConstr.mkProd (Context.make_annot Names.Name.Anonymous EConstr.ERelevance.relevant, composition_type_template, EConstr.Vars.lift 1 composition_type_template)
  ) in
  debug_dependent_congruence (fun () -> Pp.(str "return_type: " ++ print env sigma return_type));
  let e_match = make_selector_match_indices  env sigma ~pos:(snd (fst cnstr)) ~special (EConstr.mkRel 1) (Inductiveops.make_ind_family ind_fam, ind_args) return_type composition_type_template in
  let match_default = EConstr.mkApp (e_match, [|default|]) in
  let proj = EConstr.mkLambda (make_annot_numbered "e" None EConstr.ERelevance.relevant, argty, match_default) in
  debug_dependent_congruence (fun () -> Pp.(str "proj:\n" ++ print env sigma proj));
  (sigma, proj)

let build_projection
  (env : Environ.env)
  (sigma : Evd.evar_map)
  (cnstr : Constr.pconstructor) (*constructor that is getting projected*)
  (argindex : int) (*1 based index of the field to project counted from left without induction params*)
  (field_type : EConstr.t) (*type of the field that gets projected*)
  (default : EConstr.t) (*p.p_lhs so the thing inside the constructor*)
  (special : EConstr.t) (*Rel (nargs-argind+1) so the debrujin index of the field to project directly after binding*)
  (argty : EConstr.types) (*type of the constructor term that is getting projected*)
  :
  (Evd.evar_map * EConstr.t) =

  let Inductiveops.IndType (ind_family,ind_args) =
    try Inductiveops.find_rectype env sigma argty
    with Not_found ->
      CErrors.user_err
        Pp.(str "Cannot discriminate on inductive constructors with \
                 dependent types.") in
  let (ind, ind_params) = Inductiveops.dest_ind_family ind_family in
  debug_dependent_congruence (fun () -> Pp.(
    str "++++++++++++++++++++" ++ str "\n" ++
    str "+ BUILD PROJECTION +" ++ str "\n" ++
    str "++++++++++++++++++++" ++ str "\n" ++
    str "cnstr:\n\t" ++ Printer.pr_constructor env (fst cnstr) ++ str "\n" ++
    str "argindex:\n\t" ++ int argindex ++ str "\n" ++
    str "field_type:\n\t" ++ print env sigma field_type ++ str "\n" ++
    str "default:\n\t" ++ print env sigma default ++ str "\n" ++
    str "special:\n\t" ++ print Environ.empty_env sigma special ++ str "\n" ++
    str "argty:\n\t" ++ print env sigma argty ++ str "\n" ++
    str "ind_params:\n\t" ++ seq (List.map (fun e -> print env sigma e ++ str ", ") ind_params) ++ str "\n" ++
    str "ind_args:\n\t" ++ seq (List.map (fun e -> print env sigma e ++ str ", ") ind_args) ++ str "\n"
  ));
  let (cnstr : Names.constructor * EConstr.EInstance.t) =
    (fst cnstr, EConstr.EInstance.make (snd cnstr))
  in
  let (sigma, proj_result) = projectability_test env sigma cnstr argindex field_type ind (Array.of_list ind_params) (Array.of_list ind_args) in
  match proj_result with
  | Simple | NotProjectable-> build_simple_projection env sigma argty cnstr special default
  | Dependent type_composition -> build_dependent_projection env sigma cnstr default special argty type_composition (ind, ind_params) ind_args
