(* Utility Functions *)

(*CSC: Problem: here we are using the wrong (???) hypothesis that there do *)
(*CSC: not exist two modules whose dir_paths are one a prefix of the other *)
let remove_sections_from_dirpath dir =
 let module No = Nameops in
  let current_module_dir = Lib.module_sp () in
   if No.is_dirpath_prefix_of current_module_dir dir then
    let (_,id) = No.split_dirpath dir in
     No.extend_dirpath current_module_dir id
   else dir
;;

exception TwoModulesWhoseDirPathIsOneAPrefixOfTheOther;;
let get_module_path_of_section_path path =
 let dirpath = fst (Names.repr_path path) in
 let modules = Lib.module_sp () :: (Library.loaded_modules ()) in
  match
   List.filter
    (function modul -> Nameops.is_dirpath_prefix_of modul dirpath) modules
  with
     [modul] -> modul
   | _ -> raise TwoModulesWhoseDirPathIsOneAPrefixOfTheOther
;;

(*CSC: Problem: here we are using the wrong (???) hypothesis that there do *)
(*CSC: not exist two modules whose dir_paths are one a prefix of the other *)
let remove_module_dirpath_from_dirpath ~basedir dir =
 let module No = Nameops in
  if No.is_dirpath_prefix_of basedir dir then
   let ids = Names.repr_dirpath dir in
   let rec remove_firsts n l =
    match n,l with
       (0,l) -> l
     | (n,he::tl) -> remove_firsts (n-1) tl
     | _ -> assert false
   in
    let ids' =
     List.rev
      (remove_firsts
        (List.length (Names.repr_dirpath basedir))
        (List.rev ids))
    in
     ids'
  else Names.repr_dirpath dir
;;


let get_uri_of_var v pvars =
 let module D = Declare in
 let module N = Names in
  let rec search_in_pvars names =
   function
      [] -> None
    | ((name,l)::tl) ->
       let names' = name::names in
        if List.mem v l then
         Some names'
        else
         search_in_pvars names' tl
  in
  let rec search_in_open_sections =
   function
      [] -> Util.error "Variable not found"
    | he::tl as modules ->
       let dirpath = N.make_dirpath modules in
        if List.mem (N.id_of_string v) (D.last_section_hyps dirpath) then
         modules
        else
         search_in_open_sections tl
  in
   let path =
    match search_in_pvars [] pvars with
       None -> search_in_open_sections (N.repr_dirpath (Lib.cwd ()))
     | Some path -> path
   in
    "cic:" ^
     List.fold_left
      (fun i x -> "/" ^ N.string_of_id x ^ i) "" path
;;

type tag =
   Constant
 | Inductive
 | Variable
;;

let ext_of_tag =
 function
    Constant  -> "con"
  | Inductive -> "ind"
  | Variable  -> "var"
;;

let uri_of_path sp tag =
 let module N = Names in
 let module No = Nameops in
  let dir0 = No.extend_dirpath (No.dirpath sp) (No.basename sp) in
  let dir1 = remove_sections_from_dirpath dir0 in
  let dir = List.map N.string_of_id (List.rev (N.repr_dirpath dir1)) in
   "cic:/" ^ (String.concat "/" dir) ^ "." ^ (ext_of_tag tag)
;;

(* Main Functions *)

type anntypes =
 {annsynthesized : Acic.aconstr ; annexpected : Acic.aconstr option}
;;

let gen_id seed =
 let res = "i" ^ string_of_int !seed in
  incr seed ;
  res
;;

let fresh_id seed ids_to_terms constr_to_ids ids_to_father_ids =
 fun father t ->
  let res = gen_id seed in
   Hashtbl.add ids_to_father_ids res father ;
   Hashtbl.add ids_to_terms res t ;
   Acic.CicHash.add constr_to_ids t res ;
   res
;;

let source_id_of_id id = "#source#" ^ id;;

let acic_of_cic_context' computeinnertypes seed ids_to_terms constr_to_ids
 ids_to_father_ids ids_to_inner_sorts ids_to_inner_types pvars env idrefs
 evar_map t expectedty
=
 let module D = DoubleTypeInference in
 let module E = Environ in
 let module N = Names in
 let module A = Acic in
 let module T = Term in
  let fresh_id' = fresh_id seed ids_to_terms constr_to_ids ids_to_father_ids in
   (* CSC: do you have any reasonable substitute for 503? *)
   let terms_to_types = Acic.CicHash.create 503 in
    D.double_type_of env evar_map t expectedty terms_to_types ;
    let rec aux computeinnertypes father passed_lambdas_or_prods_or_letins env
     idrefs ?(subst=None,[]) tt
    =
     let fresh_id'' = fresh_id' father tt in
     let aux' = aux computeinnertypes (Some fresh_id'') [] in
      let string_of_sort_family =
       function
          T.InProp -> "Prop"
        | T.InSet  -> "Set"
        | T.InType -> "Type"
      in
      let string_of_sort t =
       string_of_sort_family
        (T.family_of_sort
         (T.destSort (Reductionops.whd_betadeltaiota env evar_map t)))
      in
       let ainnertypes,innertype,innersort,expected_available =
        let {D.synthesized = synthesized; D.expected = expected} =
         if computeinnertypes then
try
          Acic.CicHash.find terms_to_types tt
with _ ->
(*CSC: Warning: it really happens, for example in Ring_theory!!! *)
Pp.ppnl (Pp.(++) (Pp.str "BUG: this subterm was not visited during the double-type-inference: ") (Printer.prterm tt)) ; assert false (* buco nella double-type-inference *) ; {D.synthesized = Reductionops.nf_beta (Retyping.get_type_of env evar_map (Evarutil.refresh_universes tt)) ; D.expected = None}
         else
          (* We are already in an inner-type and Coscoy's double *)
          (* type inference algorithm has not been applied.      *)
          (* We need to refresh the universes because we are doing *)
          (* type inference on an already inferred type.           *)
          {D.synthesized =
            Reductionops.nf_beta
             (Retyping.get_type_of env evar_map
              (Evarutil.refresh_universes tt)) ;
           D.expected = None}
        in
(* Debugging only:
print_endline "TERMINE:" ; flush stdout ;
Pp.ppnl (Printer.prterm tt) ; flush stdout ;
print_endline "TIPO:" ; flush stdout ;
Pp.ppnl (Printer.prterm synthesized) ; flush stdout ;
print_endline "ENVIRONMENT:" ; flush stdout ;
Pp.ppnl (Printer.pr_context_of env) ; flush stdout ;
print_endline "FINE_ENVIRONMENT" ; flush stdout ;
*)
         let innersort = Retyping.get_sort_family_of env evar_map synthesized in
(* Debugging only:
print_endline "PASSATO" ; flush stdout ;
*)
          let ainnertypes,expected_available =
           if computeinnertypes then
            let annexpected,expected_available =
               match expected with
                  None -> None,false
                | Some expectedty' ->
                   Some (aux false (Some fresh_id'') [] env idrefs expectedty'),
                    true
            in
             Some
              {annsynthesized =
                aux false (Some fresh_id'') [] env idrefs synthesized ;
               annexpected = annexpected
              }, expected_available
           else
            None,false
          in
           ainnertypes,synthesized, string_of_sort_family innersort,
            expected_available
       in
        let add_inner_type id =
         match ainnertypes with
            None -> ()
          | Some ainnertypes -> Hashtbl.add ids_to_inner_types id ainnertypes
        in

         (* explicit_substitute_and_eta_expand_if_required h t t'         *)
         (* where [t] = [] and [tt] = [h]{[t']} ("{.}" denotes explicit   *)
         (* named substitution) or [tt] = (App [h]::[t]) (and [t'] = [])  *)
         (* check if [h] is a term that requires an explicit named        *)
         (* substitution and, in that case, uses the first arguments of   *)
         (* [t] as the actual arguments of the substitution. If there     *)
         (* are not enough parameters in the list [t], then eta-expansion *)
         (* is performed.                                                 *)
         let
          explicit_substitute_and_eta_expand_if_required h t t'
           compute_result_if_eta_expansion_not_required
         =
          let subst,residual_args,uninst_vars =
           let variables,basedir =
            match T.kind_of_term h with
               T.Const sp
             | T.Ind (sp,_)
             | T.Construct ((sp,_),_) ->
                Dischargedhypsmap.get_discharged_hyps sp,
                 get_module_path_of_section_path sp
             | T.Var id ->
                let sp = Declare.find_section_variable id in
                 Dischargedhypsmap.get_discharged_hyps sp,
                  get_module_path_of_section_path sp
             | _ ->
                (* no explicit substitution *)
                [], Nameops.dirpath_of_string "dummy"
           in
           (* returns a triple whose first element is  *)
           (* an explicit named substitution of "type" *)
           (* (variable * argument) list, whose        *)
           (* second element is the list of residual   *)
           (* arguments and whose third argument is    *) 
           (* the list of uninstantiated variables     *)
           let rec get_explicit_subst variables arguments =
            match variables,arguments with
               [],_ -> [],arguments,[]
             | _,[] -> [],[],variables
             | he1::tl1,he2::tl2 ->
                let subst,extra_args,uninst = get_explicit_subst tl1 tl2 in
                let (he1_sp, he1_id) = Names.repr_path he1 in
                let he1' = remove_module_dirpath_from_dirpath ~basedir he1_sp in
                let he1'' =
                 String.concat "/"
                  (List.map Names.string_of_id (List.rev he1')) ^ "/"
                 ^ (Names.string_of_id he1_id) ^ ".var" 
                in
                 (he1'',he2)::subst, extra_args, uninst
           in
            get_explicit_subst variables t'
          in
           let uninst_vars_length = List.length uninst_vars in
            if uninst_vars_length > 0 then
             (* Not enough arguments provided. We must eta-expand! *)
             let un_args,_ =
              T.decompose_prod_n uninst_vars_length
               (Retyping.get_type_of env evar_map tt)
             in
              let eta_expanded =
               let arguments =
                List.map (T.lift uninst_vars_length) t @
                 Termops.rel_list 0 uninst_vars_length
               in
                T.unshare
                 (T.lamn uninst_vars_length un_args
                  (T.applistc h arguments))
              in
               D.double_type_of env evar_map eta_expanded
                None terms_to_types ;
               Hashtbl.remove ids_to_inner_types fresh_id'' ;
               aux' env idrefs eta_expanded
            else
             compute_result_if_eta_expansion_not_required subst residual_args
         in

          (* Now that we have all the auxiliary functions we  *)
          (* can finally proceed with the main case analysis. *) 
          match T.kind_of_term tt with
             T.Rel n ->
              let id =
               match List.nth (E.rel_context env) (n - 1) with
                  (N.Name id,_,_)   -> id
                | (N.Anonymous,_,_) -> Nameops.make_ident "_" None
              in
               Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
               if innersort = "Prop"  && expected_available then
                add_inner_type fresh_id'' ;
               A.ARel (fresh_id'', n, List.nth idrefs (n-1), id)
           | T.Var id ->
              let path = get_uri_of_var (N.string_of_id id) pvars in
               Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
               if innersort = "Prop"  && expected_available then
                add_inner_type fresh_id'' ;
               A.AVar
                (fresh_id'', path ^ "/" ^ (N.string_of_id id) ^ ".var")
           | T.Evar (n,l) ->
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if innersort = "Prop"  && expected_available then
               add_inner_type fresh_id'' ;
              A.AEvar
               (fresh_id'', n, Array.to_list (Array.map (aux' env idrefs) l))
           | T.Meta _ -> Util.anomaly "Meta met during exporting to XML"
           | T.Sort s -> A.ASort (fresh_id'', s)
           | T.Cast (v,t) ->
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if innersort = "Prop" then
               add_inner_type fresh_id'' ;
              A.ACast (fresh_id'', aux' env idrefs v, aux' env idrefs t)
           | T.Prod (n,s,t) ->
              let n' =
               match n with
                  N.Anonymous -> N.Anonymous
                | _ ->
                  N.Name (Nameops.next_name_away n (Termops.ids_of_context env))
              in
               Hashtbl.add ids_to_inner_sorts fresh_id''
                (string_of_sort innertype) ;
               let sourcetype = Retyping.get_type_of env evar_map s in
                Hashtbl.add ids_to_inner_sorts (source_id_of_id fresh_id'')
                 (string_of_sort sourcetype) ;
               let new_passed_prods =
                let father_is_prod =
                 match father with
                    None -> false
                  | Some father' ->
                     match
                      Term.kind_of_term (Hashtbl.find ids_to_terms father')
                     with
                        T.Prod _ -> true
                      | _ -> false
                in
                 (fresh_id'', n', aux' env idrefs s)::
                  (if father_is_prod then
                    passed_lambdas_or_prods_or_letins
                   else [])
               in
                let new_env = E.push_rel (n', None, s) env in
                let new_idrefs = fresh_id''::idrefs in
                 (match Term.kind_of_term t with
                     T.Prod _ ->
                      aux computeinnertypes (Some fresh_id'') new_passed_prods
                       new_env new_idrefs t
                   | _ ->
                     A.AProds (new_passed_prods, aux' new_env new_idrefs t))
           | T.Lambda (n,s,t) ->
              let n' =
               match n with
                  N.Anonymous -> N.Anonymous
                | _ ->
                  N.Name (Nameops.next_name_away n (Termops.ids_of_context env))
              in
               Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
               let sourcetype = Retyping.get_type_of env evar_map s in
                Hashtbl.add ids_to_inner_sorts (source_id_of_id fresh_id'')
                 (string_of_sort sourcetype) ;
               let father_is_lambda =
                match father with
                   None -> false
                 | Some father' ->
                    match
                     Term.kind_of_term (Hashtbl.find ids_to_terms father')
                    with
                       T.Lambda _ -> true
                     | _ -> false
               in
                if innersort = "Prop" &&
                   ((not father_is_lambda) || expected_available)
                then add_inner_type fresh_id'' ;
                let new_passed_lambdas =
                 (fresh_id'',n', aux' env idrefs s)::
                  (if father_is_lambda then
                    passed_lambdas_or_prods_or_letins
                   else []) in
                let new_env = E.push_rel (n', None, s) env in
                let new_idrefs = fresh_id''::idrefs in
                 (match Term.kind_of_term t with
                     T.Lambda _ ->
                      aux computeinnertypes (Some fresh_id'') new_passed_lambdas
                       new_env new_idrefs t
                   | _ ->
                     let t' = aux' new_env new_idrefs t in
                      (* eta-expansion for explicit named substitutions *)
                      (* can create nested Lambdas. Here we perform the *)
                      (* flattening.                                    *)
                      match t' with
                         A.ALambdas (lambdas, t'') ->
                          A.ALambdas (lambdas@new_passed_lambdas, t'')
                       | _ ->
                         A.ALambdas (new_passed_lambdas, t')
                 )
           | T.LetIn (n,s,t,d) ->
              let n' =
               match n with
                  N.Anonymous -> N.Anonymous
                | _ ->
                  N.Name (Nameops.next_name_away n (Termops.ids_of_context env))
              in
               Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
               let sourcesort =
                Retyping.get_sort_family_of env evar_map
                 (Retyping.get_type_of env evar_map s)
               in
                Hashtbl.add ids_to_inner_sorts (source_id_of_id fresh_id'')
                 (string_of_sort_family sourcesort) ;
               let father_is_letin =
                match father with
                   None -> false
                 | Some father' ->
                    match
                     Term.kind_of_term (Hashtbl.find ids_to_terms father')
                    with
                       T.LetIn _ -> true
                     | _ -> false
               in
                if innersort = "Prop" then
                 add_inner_type fresh_id'' ;
                let new_passed_letins =
                 (fresh_id'',n', aux' env idrefs s)::
                  (if father_is_letin then
                    passed_lambdas_or_prods_or_letins
                   else []) in
                let new_env = E.push_rel (n', Some s, t) env in
                let new_idrefs = fresh_id''::idrefs in
                 (match Term.kind_of_term d with
                     T.LetIn _ ->
                      aux computeinnertypes (Some fresh_id'') new_passed_letins
                       new_env new_idrefs d
                   | _ -> A.ALetIns
                           (new_passed_letins, aux' new_env new_idrefs d))
           | T.App (h,t) ->
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if innersort = "Prop" then
               add_inner_type fresh_id'' ;
              let
               compute_result_if_eta_expansion_not_required subst residual_args
              =
               let residual_args_not_empty = List.length residual_args > 0 in
               let h' =
                if residual_args_not_empty then
                 aux' env idrefs ~subst:(None,subst) h
                else
                 aux' env idrefs ~subst:(Some fresh_id'',subst) h
               in
                (* maybe all the arguments were used for the explicit *)
                (* named substitution                                 *)
                if residual_args_not_empty then
                 A.AApp (fresh_id'', h'::residual_args)
                else
                 h'
              in
               let t' =
                Array.fold_right (fun x i -> (aux' env idrefs x)::i) t []
               in
                explicit_substitute_and_eta_expand_if_required h
                 (Array.to_list t) t'
                 compute_result_if_eta_expansion_not_required
           | T.Const sp ->
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if innersort = "Prop"  && expected_available then
               add_inner_type fresh_id'' ;
              let compute_result_if_eta_expansion_not_required _ _ =
               A.AConst (fresh_id'', subst, (uri_of_path sp Constant))
              in
               let (_,subst') = subst in
                explicit_substitute_and_eta_expand_if_required tt []
                 (List.map snd subst')
                 compute_result_if_eta_expansion_not_required
           | T.Ind (sp,i) ->
              let compute_result_if_eta_expansion_not_required _ _ =
               A.AInd (fresh_id'', subst, (uri_of_path sp Inductive), i)
              in
               let (_,subst') = subst in
                explicit_substitute_and_eta_expand_if_required tt []
                 (List.map snd subst')
                 compute_result_if_eta_expansion_not_required
           | T.Construct ((sp,i),j) ->
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if innersort = "Prop"  && expected_available then
               add_inner_type fresh_id'' ;
              let compute_result_if_eta_expansion_not_required _ _ =
               A.AConstruct
                (fresh_id'', subst, (uri_of_path sp Inductive), i, j)
              in
               let (_,subst') = subst in
                explicit_substitute_and_eta_expand_if_required tt []
                 (List.map snd subst')
                 compute_result_if_eta_expansion_not_required
           | T.Case ({T.ci_ind=(sp,i)},ty,term,a) ->
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if innersort = "Prop" then
               add_inner_type fresh_id'' ;
              let a' =
               Array.fold_right (fun x i -> (aux' env idrefs x)::i) a []
              in
               A.ACase
                (fresh_id'', (uri_of_path sp Inductive), i, aux' env idrefs ty,
                 aux' env idrefs term, a')
           | T.Fix ((ai,i),((f,t,b) as rec_decl)) ->
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if innersort = "Prop" then add_inner_type fresh_id'' ;
              let fresh_idrefs =
               Array.init (Array.length t) (function _ -> gen_id seed) in
              let new_idrefs =
               (List.rev (Array.to_list fresh_idrefs)) @ idrefs
              in
               A.AFix (fresh_id'', i,
                Array.fold_right
                 (fun (id,fi,ti,bi,ai) i ->
                   let fi' =
                    match fi with
                       N.Name fi -> fi
                     | N.Anonymous -> Util.error "Anonymous fix function met"
                   in
                    (id, fi', ai,
                     aux' env idrefs ti,
                     aux' (E.push_rec_types rec_decl env) new_idrefs bi)::i)
                 (Array.mapi
                  (fun j x -> (fresh_idrefs.(j),x,t.(j),b.(j),ai.(j))) f 
                 ) []
                )
           | T.CoFix (i,((f,t,b) as rec_decl)) ->
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if innersort = "Prop" then add_inner_type fresh_id'' ;
              let fresh_idrefs =
               Array.init (Array.length t) (function _ -> gen_id seed) in
              let new_idrefs =
               (List.rev (Array.to_list fresh_idrefs)) @ idrefs
              in
               A.ACoFix (fresh_id'', i,
                Array.fold_right
                 (fun (id,fi,ti,bi) i ->
                   let fi' =
                    match fi with
                       N.Name fi -> fi
                     | N.Anonymous -> Util.error "Anonymous fix function met"
                   in
                    (id, fi',
                     aux' env idrefs ti,
                     aux' (E.push_rec_types rec_decl env) new_idrefs bi)::i)
                 (Array.mapi
                   (fun j x -> (fresh_idrefs.(j),x,t.(j),b.(j)) ) f
                 ) []
                )
    in
     aux computeinnertypes None [] env idrefs t
;;

let acic_of_cic_context metasenv context t =
 let ids_to_terms = Hashtbl.create 503 in
 let constr_to_ids = Acic.CicHash.create 503 in
 let ids_to_father_ids = Hashtbl.create 503 in
 let ids_to_inner_sorts = Hashtbl.create 503 in
 let ids_to_inner_types = Hashtbl.create 503 in
 let seed = ref 0 in
   acic_of_cic_context' true seed ids_to_terms constr_to_ids ids_to_father_ids
    ids_to_inner_sorts ids_to_inner_types metasenv context t,
   ids_to_terms, ids_to_father_ids, ids_to_inner_sorts, ids_to_inner_types
;;

let acic_object_of_cic_object pvars sigma obj =
 let module A = Acic in
  let ids_to_terms = Hashtbl.create 503 in
  let constr_to_ids = Acic.CicHash.create 503 in
  let ids_to_father_ids = Hashtbl.create 503 in
  let ids_to_inner_sorts = Hashtbl.create 503 in
  let ids_to_inner_types = Hashtbl.create 503 in
  let ids_to_conjectures = Hashtbl.create 11 in
  let ids_to_hypotheses = Hashtbl.create 127 in
  let hypotheses_seed = ref 0 in
  let conjectures_seed = ref 0 in
  let seed = ref 0 in
  let acic_term_of_cic_term_context' =
   acic_of_cic_context' true seed ids_to_terms constr_to_ids ids_to_father_ids
    ids_to_inner_sorts ids_to_inner_types pvars in
(*CSC: is this the right env to use? Hhmmm. There is a problem: in    *)
(*CSC: Global.env () the object we are exporting is already defined,  *)
(*CSC: either in the environment or in the named context (in the case *)
(*CSC: of variables. Is this a problem?                               *)
  let env = Global.env () in
  let acic_term_of_cic_term' = acic_term_of_cic_term_context' env [] sigma in
(*CSC: the fresh_id is not stored anywhere. This _MUST_ be fixed using *)
(*CSC: a modified version of the already existent fresh_id function    *)
  let fresh_id () =
   let res = "i" ^ string_of_int !seed in
    incr seed ;
    res
  in
   let aobj =
    match obj with
      A.Constant (id,bo,ty,params) ->
       let abo =
        match bo with
           None -> None
         | Some bo' -> Some (acic_term_of_cic_term' bo' (Some ty))
       in
       let aty = acic_term_of_cic_term' ty None in
        A.AConstant (fresh_id (),id,abo,aty,params)
    | A.Variable (id,bo,ty,params) ->
       let abo =
        match bo with
           Some bo -> Some (acic_term_of_cic_term' bo (Some ty))
         | None -> None
       in
       let aty = acic_term_of_cic_term' ty None in
        A.AVariable (fresh_id (),id,abo,aty,params)
    | A.CurrentProof (id,conjectures,bo,ty) ->
       let aconjectures =
        List.map
         (function (i,canonical_context,term) as conjecture ->
           let cid = "c" ^ string_of_int !conjectures_seed in
            Hashtbl.add ids_to_conjectures cid conjecture ;
            incr conjectures_seed ;
            let canonical_env,idrefs',acanonical_context =
             let rec aux env idrefs =
              function
                 [] -> env,idrefs,[]
               | ((n,decl_or_def) as hyp)::tl ->
                  let hid = "h" ^ string_of_int !hypotheses_seed in
                  let new_idrefs = hid::idrefs in
                   Hashtbl.add ids_to_hypotheses hid hyp ;
                   incr hypotheses_seed ;
                   match decl_or_def with
                       A.Decl t ->
                        let final_env,final_idrefs,atl =
                         aux (Environ.push_rel (Names.Name n,None,t) env)
                          new_idrefs tl
                        in
                         let at =
                          acic_term_of_cic_term_context' env idrefs sigma t None
                         in
                          final_env,final_idrefs,(hid,(n,A.Decl at))::atl
                     | A.Def (t,ty) ->
                        let final_env,final_idrefs,atl =
                         aux
                          (Environ.push_rel (Names.Name n,Some t,ty) env)
                           new_idrefs tl
                        in
                         let at =
                          acic_term_of_cic_term_context' env idrefs sigma t None
                         in
                         let dummy_never_used =
                          let s = "dummy_never_used" in
                           A.ARel (s,99,s,Names.id_of_string s)
                         in
                          final_env,final_idrefs,
                           (hid,(n,A.Def (at,dummy_never_used)))::atl
             in
              aux env [] canonical_context
            in
             let aterm =
              acic_term_of_cic_term_context' canonical_env idrefs' sigma term
               None
             in
              (cid,i,List.rev acanonical_context,aterm)
         ) conjectures in
       let abo = acic_term_of_cic_term_context' env [] sigma bo (Some ty) in
       let aty = acic_term_of_cic_term_context' env [] sigma ty None in
        A.ACurrentProof (fresh_id (),id,aconjectures,abo,aty)
    | A.InductiveDefinition (tys,params,paramsno) ->
       let env' =
        List.fold_right
         (fun (name,_,arity,_) env ->
           Environ.push_rel (Names.Name name, None, arity) env
         ) (List.rev tys) env in
       let idrefs = List.map (function _ -> gen_id seed) tys in
       let atys =
        List.map2
         (fun id (name,inductive,ty,cons) ->
           let acons =
            List.map
             (function (name,ty) ->
               (name,
                 acic_term_of_cic_term_context' env' idrefs Evd.empty ty None)
             ) cons
           in
            (id,name,inductive,acic_term_of_cic_term' ty None,acons)
         ) (List.rev idrefs) tys
       in
       A.AInductiveDefinition (fresh_id (),atys,params,paramsno)
   in
    aobj,ids_to_terms,constr_to_ids,ids_to_father_ids,ids_to_inner_sorts,
     ids_to_inner_types,ids_to_conjectures,ids_to_hypotheses
;;
