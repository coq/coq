(* Utility Functions *)

(* get_depth_of_var is used to find the depth when we are printing *)
(* an object in a closed section. Otherwise it returns None and we *)
(* use Nametab to find its path.                                   *)
let get_depth_of_var v pvars =
 let module D = Declare in
 let module N = Names in
  let rec search_in_pvars n =
   function
      [] -> None
    | (he::tl) -> if List.mem v he then Some n else search_in_pvars (n + 1) tl
  in
  let rec search_in_open_sections n =
   function
      [] -> Util.error "Variable not found"
    | he::tl as modules ->
       let dirpath = N.make_dirpath modules in
        if List.mem (N.id_of_string v) (D.last_section_hyps dirpath) then n
        else
         search_in_open_sections (n+1) tl
  in
   match search_in_pvars 0 pvars with
      None -> search_in_open_sections 0 (N.repr_dirpath (Lib.cwd ()))
    | Some n -> n
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
  let ext_of_sp sp = ext_of_tag tag in
  let dir0 = No.extend_dirpath (No.dirpath sp) (No.basename sp) in
  let dir = List.map N.string_of_id (List.rev (N.repr_dirpath dir0)) in
   "cic:/" ^ (String.concat "/" dir) ^ "." ^ (ext_of_sp sp)
;;

(* Main Functions *)

type anntypes =
 {annsynthesized : Acic.aconstr ; annexpected : Acic.aconstr option}
;;

let fresh_id seed ids_to_terms constr_to_ids ids_to_father_ids =
 fun father t ->
  let res = "i" ^ string_of_int !seed in
   incr seed ;
   Hashtbl.add ids_to_father_ids res father ;
   Hashtbl.add ids_to_terms res t ;
   Acic.CicHash.add constr_to_ids t res ;
   res
;;

let acic_of_cic_context' seed ids_to_terms constr_to_ids ids_to_father_ids
 ids_to_inner_sorts ids_to_inner_types pvars env evar_map t expectedty
=
 let module D = DoubleTypeInference in
 let module E = Environ in
 let module N = Names in
 let module A = Acic in
 let module T = Term in
  let fresh_id' = fresh_id seed ids_to_terms constr_to_ids ids_to_father_ids in
   let terms_to_types =
    D.double_type_of env evar_map t expectedty
   in
    let rec aux computeinnertypes father env tt =
     let fresh_id'' = fresh_id' father tt in
     let aux' = aux computeinnertypes (Some fresh_id'') in
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
with _ -> assert false (* buco nella double-type-inference *)
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
                   Some (aux false (Some fresh_id'') env expectedty'),true
            in
             Some
              {annsynthesized =
                aux false (Some fresh_id'') env synthesized ;
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
              A.ARel (fresh_id'', n, id)
          | T.Var id ->
             let depth =
              string_of_int (get_depth_of_var (N.string_of_id id) pvars)
             in
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if innersort = "Prop"  && expected_available then
               add_inner_type fresh_id'' ;
              A.AVar (fresh_id'', depth ^ "," ^ (N.string_of_id id))
          | T.Evar (n,l) ->
             Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
             if innersort = "Prop"  && expected_available then
              add_inner_type fresh_id'' ;
             A.AEvar (fresh_id'', n, Array.to_list (Array.map (aux' env) l))
          | T.Meta _ -> Util.anomaly "Meta met during exporting to XML"
          | T.Sort s -> A.ASort (fresh_id'', s)
          | T.Cast (v,t) ->
             Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
             if innersort = "Prop" then
              add_inner_type fresh_id'' ;
             A.ACast (fresh_id'', aux' env v, aux' env t)
          | T.Prod (n,s,t) ->
             let n' = Nameops.next_name_away n (Termops.ids_of_context env) in
              Hashtbl.add ids_to_inner_sorts fresh_id''
               (string_of_sort innertype) ;
              A.AProd
               (fresh_id'', n, aux' env s,
                aux' (E.push_rel (N.Name n', None, s) env) t)
          | T.Lambda (n,s,t) ->
             let n' = Nameops.next_name_away n (Termops.ids_of_context env) in
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if innersort = "Prop" then
               begin
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
                 if (not father_is_lambda) || expected_available then
                  add_inner_type fresh_id''
               end ;
              A.ALambda
               (fresh_id'',n, aux' env s,
                aux' (E.push_rel (N.Name n', None, s) env) t)
          | T.LetIn (n,s,t,d) ->
             let n' = Nameops.next_name_away n (Termops.ids_of_context env) in
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if innersort = "Prop" then
               add_inner_type fresh_id'' ;
              A.ALetIn
               (fresh_id'', n, aux' env s,
                aux' (E.push_rel (N.Name n', Some s, t) env) d)
          | T.App (h,t) ->
             Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
             if innersort = "Prop" then
              add_inner_type fresh_id'' ;
             let h' = aux' env h in
             let t' = Array.fold_right (fun x i -> (aux' env x)::i) t [] in
              A.AApp (fresh_id'', h'::t')
          | T.Const sp ->
             Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
             if innersort = "Prop"  && expected_available then
              add_inner_type fresh_id'' ;
             A.AConst (fresh_id'', (uri_of_path sp Constant))
          | T.Ind (sp,i) ->
             A.AInd (fresh_id'', (uri_of_path sp Inductive), i)
          | T.Construct ((sp,i),j) ->
             Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
             if innersort = "Prop"  && expected_available then
              add_inner_type fresh_id'' ;
             A.AConstruct (fresh_id'', (uri_of_path sp Inductive), i, j)
          | T.Case ({T.ci_ind=(sp,i)},ty,term,a) ->
             Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
             if innersort = "Prop" then
              add_inner_type fresh_id'' ;
             let a' = Array.fold_right (fun x i -> (aux' env x)::i) a [] in
              A.ACase (fresh_id'', (uri_of_path sp Inductive), i, aux' env ty,
               aux' env term, a')
          | T.Fix ((ai,i),((f,t,b) as rec_decl)) ->
             Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
             if innersort = "Prop" then
              add_inner_type fresh_id'' ;
             A.AFix (fresh_id'', i,
              Array.fold_right
               (fun (fi,ti,bi,ai) i ->
                 let fi' =
                  match fi with
                     N.Name fi -> fi
                   | N.Anonymous -> Util.error "Anonymous fix function met"
                 in
                  (fi', ai, aux' (E.push_rec_types rec_decl env) bi,
                   aux' env ti)::i
               ) (Array.mapi (fun j x -> (x,t.(j),b.(j),ai.(j)) ) f ) []
             )
          | T.CoFix (i,((f,t,b) as rec_decl)) ->
             Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
             if innersort = "Prop" then
              add_inner_type fresh_id'' ;
             A.ACoFix (fresh_id'', i,
              Array.fold_right
               (fun (fi,ti,bi) i ->
                 let fi' =
                  match fi with
                     N.Name fi -> fi
                   | N.Anonymous -> Util.error "Anonymous fix function met"
                 in
                  (fi', aux' (E.push_rec_types rec_decl env) bi,
                   aux' env ti)::i
               ) (Array.mapi (fun j x -> (x,t.(j),b.(j)) ) f ) []
             )
        in
         aux true None env t
;;

let acic_of_cic_context metasenv context t =
 let ids_to_terms = Hashtbl.create 503 in
 let constr_to_ids = Acic.CicHash.create 503 in
 let ids_to_father_ids = Hashtbl.create 503 in
 let ids_to_inner_sorts = Hashtbl.create 503 in
 let ids_to_inner_types = Hashtbl.create 503 in
 let seed = ref 0 in
   acic_of_cic_context' seed ids_to_terms constr_to_ids ids_to_father_ids
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
   acic_of_cic_context' seed ids_to_terms constr_to_ids ids_to_father_ids
    ids_to_inner_sorts ids_to_inner_types pvars in
(*CSC: is this the right env to use? I think so *)
  let env = (Safe_typing.env_of_safe_env (Global.safe_env ())) in
  let acic_term_of_cic_term' = acic_term_of_cic_term_context' env sigma in
(*CSC: the fresh_id is not stored anywhere. This _MUST_ be fixed using *)
(*CSC: a modified version of the already existent fresh_id function    *)
  let fresh_id () =
   let res = "i" ^ string_of_int !seed in
    incr seed ;
    res
  in
   let aobj =
    match obj with
      A.Definition (id,bo,ty,params) ->
       let abo = acic_term_of_cic_term' bo (Some ty) in
       let aty = acic_term_of_cic_term' ty None in
        A.ADefinition (fresh_id (),id,abo,aty,params)
    | A.Axiom (id,ty,params) ->
       let aty = acic_term_of_cic_term' ty None in
        A.AAxiom (fresh_id (),id,aty,params)
    | A.Variable (id,bo,ty) ->
       let abo =
        match bo with
           Some bo -> Some (acic_term_of_cic_term' bo (Some ty))
         | None -> None
       in
       let aty = acic_term_of_cic_term' ty None in
        A.AVariable (fresh_id (),id,abo,aty)
    | A.CurrentProof (id,conjectures,bo,ty) ->
       let aconjectures =
prerr_endline "NON STAMPO LE IPOTESI: DA IMPLEMENTARE" ; flush stderr ;
[] (*
        List.map
         (function (i,canonical_context,term) as conjecture ->
           let cid = "c" ^ string_of_int !conjectures_seed in
            Hashtbl.add ids_to_conjectures cid conjecture ;
            incr conjectures_seed ;
            let acanonical_context =
             let rec aux =
              function
                 [] -> []
               | hyp::tl ->
                  let hid = "h" ^ string_of_int !hypotheses_seed in
                   Hashtbl.add ids_to_hypotheses hid hyp ;
                   incr hypotheses_seed ;
(*CSC: bug certo: dovrei usare un env ottenuto a partire da tl!!! *)
                   match hyp with
                      n,A.Decl t ->
                        let at =
                         acic_term_of_cic_term_context' env sigma t None
                        in
                         (hid,(n,A.Decl at))::(aux tl)
                    | n,A.Def t ->
                        let at =
                         acic_term_of_cic_term_context' env sigma t None
                        in
                         (hid,(n,A.Def at))::(aux tl)
             in
              aux canonical_context
            in
             let aterm =
              acic_term_of_cic_term_context' env sigma
               term None
             in
              (cid,i,acanonical_context,aterm)
         ) conjectures in
*) in
       let abo = acic_term_of_cic_term_context' env sigma bo (Some ty) in
       let aty = acic_term_of_cic_term_context' env sigma ty None in
        A.ACurrentProof ("mettereaposto",id,aconjectures,abo,aty)
    | A.InductiveDefinition (tys,params,paramsno) ->
       let env' =
        List.fold_right
         (fun (name,_,arity,_) env ->
           Environ.push_rel (Names.Name name, None, arity) env
         ) tys env
       in
       let atys =
        List.map
         (function (name,inductive,ty,cons) ->
           let acons =
            List.map
             (function (name,ty) ->
               (name,acic_term_of_cic_term_context' env' Evd.empty ty None)
             ) cons
           in
            (name,inductive,acic_term_of_cic_term' ty None,acons)
         )
         tys
       in
       A.AInductiveDefinition (fresh_id (),atys,params,paramsno)
   in
    aobj,ids_to_terms,constr_to_ids,ids_to_father_ids,ids_to_inner_sorts,
     ids_to_inner_types,ids_to_conjectures,ids_to_hypotheses
;;
