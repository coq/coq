(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
open Names
open Nameops
open Sorts
open Term
open Constr
open Context
open Vars
open Environ

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

module Internal = struct

  let debug_print_constr sigma c = Constr.debug_print (EConstr.to_constr sigma c)
  let fallback_printer _env sigma c = debug_print_constr sigma c
  let term_printer = ref fallback_printer

  let print_constr_env env sigma t = !term_printer (env:env) sigma (t:Evd.econstr)
  let set_print_constr f = term_printer := f

  let pr_var_decl env sigma decl =
    let open NamedDecl in
    let pbody = match decl with
      | LocalAssum _ ->  mt ()
      | LocalDef (_,c,_) ->
        (* Force evaluation *)
        let c = EConstr.of_constr c in
        let pb = print_constr_env env sigma c in
        (str" := " ++ pb ++ cut () ) in
    let pt = print_constr_env env sigma (EConstr.of_constr (get_type decl)) in
    let ptyp = (str" : " ++ pt) in
    (Id.print (get_id decl) ++ hov 0 (pbody ++ ptyp))

  let pr_rel_decl env sigma decl =
    let open RelDecl in
    let pbody = match decl with
      | LocalAssum _ -> mt ()
      | LocalDef (_,c,_) ->
        (* Force evaluation *)
        let c = EConstr.of_constr c in
        let pb = print_constr_env env sigma c in
        (str":=" ++ spc () ++ pb ++ spc ()) in
    let ptyp = print_constr_env env sigma (EConstr.of_constr (get_type decl)) in
    match get_name decl with
    | Anonymous -> hov 0 (str"<>" ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)
    | Name id -> hov 0 (Id.print id ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)

  let print_named_context env sigma =
    hv 0 (fold_named_context
            (fun env _status d pps ->
               pps ++ ws 2 ++ pr_var_decl env sigma d)
            env ~init:(mt ()))

  let print_rel_context env sigma =
    hv 0 (fold_rel_context
            (fun env d pps -> pps ++ ws 2 ++ pr_rel_decl env sigma d)
            env ~init:(mt ()))

  let print_env env sigma =
    let sign_env =
      fold_named_context
        (fun env _status d pps ->
           let pidt =  pr_var_decl env sigma d in
           (pps ++ fnl () ++ pidt))
        env ~init:(mt ())
    in
    let db_env =
      fold_rel_context
        (fun env d pps ->
           let pnat = pr_rel_decl env sigma d in (pps ++ fnl () ++ pnat))
        env ~init:(mt ())
    in
    (sign_env ++ db_env)

  let protect f x =
    try f x
    with e when
        (* maybe should be just "not is_interrupted"? *)
        CErrors.noncritical e || !Flags.in_debugger ->
      str "EXCEPTION: " ++ str (Printexc.to_string e)

  let print_kconstr env sigma a =
    protect (fun c -> print_constr_env env sigma c) a

end

let vars_of_env env =
  let s = Environ.ids_of_named_context_val (Environ.named_context_val env) in
  Context.Rel.fold_outside
    (fun decl s -> match RelDecl.get_name decl with Name id -> Id.Set.add id s | _ -> s)
    (rel_context env) ~init:s

let pr_global_env env g = Nametab.pr_global_env (vars_of_env env) g

let evar_suggested_name env sigma evk =
  let open Evd in
  let base_id evk' evi =
  match evar_ident evk' sigma with
  | Some id -> Libnames.basename id
  | None -> match Evd.evar_source evi with
  | _,Evar_kinds.ImplicitArg (c,(n,id),b) -> id
  | _,Evar_kinds.VarInstance id -> id
  | _,Evar_kinds.QuestionMark {Evar_kinds.qm_name = Name id} -> id
  | _,Evar_kinds.GoalEvar -> Id.of_string "Goal"
  | _ ->
      let env = reset_with_named_context (Evd.evar_hyps evi) env in
      Namegen.id_of_name_using_hdchar env sigma (Evd.evar_concl evi) Anonymous
  in
  let names = Evar.Map.mapi base_id (undefined_map sigma) in
  let id = Evar.Map.find evk names in
  let fold evk' id' (seen, n) =
    if seen then (seen, n)
    else if Evar.equal evk evk' then (true, n)
    else if Id.equal id id' then (seen, succ n)
    else (seen, n)
  in
  let (_, n) = Evar.Map.fold fold names (false, 0) in
  if n = 0 then id else Nameops.add_suffix id (string_of_int (pred n))

let evar_string env sigma evk =
  match Evd.evar_ident evk sigma with
  | Some id -> Libnames.string_of_path id
  | None -> Id.to_string (evar_suggested_name env sigma evk)

let pr_existential_key env sigma evk =
let open Evd in
match evar_ident evk sigma with
| None ->
  str "?" ++ Id.print (evar_suggested_name env sigma evk)
| Some id ->
  str "?" ++ Libnames.pr_path id

let pr_decl env sigma (decl,ok) =
  let open NamedDecl in
  let print_constr = Internal.print_kconstr in
  match decl with
  | LocalAssum ({binder_name=id},_) ->
    if ok then Id.print id else (str "{" ++ Id.print id ++ str "}")
  | LocalDef ({binder_name=id},c,_) ->
    str (if ok then "(" else "{") ++ Id.print id ++ str ":=" ++
    print_constr env sigma c ++ str (if ok then ")" else "}")

let pr_evar_source env sigma = function
  | Evar_kinds.NamedHole id -> Id.print id
  | Evar_kinds.QuestionMark _ -> str "underscore"
  | Evar_kinds.CasesType false -> str "pattern-matching return predicate"
  | Evar_kinds.CasesType true ->
      str "subterm of pattern-matching return predicate"
  | Evar_kinds.BinderType (Name id) -> str "type of " ++ Id.print id
  | Evar_kinds.BinderType Anonymous -> str "type of anonymous binder"
  | Evar_kinds.EvarType (ido,evk) ->
      let pp = match ido with
        | Some id -> str "?" ++ Id.print id
        | None ->
          try pr_existential_key env sigma evk
          with (* defined *) Not_found -> str "an internal placeholder" in
     str "type of " ++ pp
  | Evar_kinds.ImplicitArg (c,(n,id),b) ->
      str "parameter " ++ Id.print id ++ spc () ++ str "of" ++
      spc () ++ pr_global_env env c
  | Evar_kinds.InternalHole -> str "internal placeholder"
  | Evar_kinds.TomatchTypeParameter (ind,n) ->
      pr_nth n ++ str " argument of type " ++ pr_global_env env (IndRef ind)
  | Evar_kinds.GoalEvar -> str "goal evar"
  | Evar_kinds.ImpossibleCase -> str "type of impossible pattern-matching clause"
  | Evar_kinds.MatchingVar _ -> str "matching variable"
  | Evar_kinds.VarInstance id -> str "instance of " ++ Id.print id
  | Evar_kinds.SubEvar (where,evk) ->
     (match where with
     | None -> str "subterm of "
     | Some Evar_kinds.Body -> str "body of "
     | Some Evar_kinds.Domain -> str "domain of "
     | Some Evar_kinds.Codomain -> str "codomain of ") ++ Evar.print evk
  | Evar_kinds.RewriteRulePattern Anonymous -> str "anonymous pattern variable"
  | Evar_kinds.RewriteRulePattern Name id -> str "pattern variable " ++ Id.print id

let pr_evar_info (type a) env sigma (evi : a Evd.evar_info) =
  let open Evd in
  let print_constr = Internal.print_kconstr in
  let phyps =
    try
      let decls = match Filter.repr (evar_filter evi) with
      | None -> List.map (fun c -> (c, true)) (evar_context evi)
      | Some filter -> List.combine (evar_context evi) filter
      in
      prlist_with_sep spc (pr_decl env sigma) (List.rev decls)
    with Invalid_argument _ -> str "Ill-formed filtered context" in
  let pb =
    match Evd.evar_body evi with
      | Evar_empty -> print_constr env sigma (Evd.evar_concl evi)
      | Evar_defined c -> str"=> "  ++ print_constr env sigma c
  in
  let candidates =
    match Evd.evar_body evi with
      | Evar_empty ->
        begin match evar_candidates evi with
        | None -> mt ()
        | Some l ->
           spc () ++ str "{" ++
           prlist_with_sep (fun () -> str "|") (print_constr env sigma) l ++ str "}"
        end
      | _ ->
          mt ()
  in
  let src = str "(" ++ pr_evar_source env sigma (snd (Evd.evar_source evi)) ++ str ")" in
  hov 2
    (str"["  ++ phyps ++ spc () ++ str"|-" ++ spc() ++ pb ++ str"]" ++
       candidates ++ spc() ++ src)

let compute_evar_dependency_graph sigma =
  let open Evd in
  (* Compute the map binding ev to the evars whose body depends on ev *)
  let fold evk (EvarInfo evi) acc =
    let fold_ev evk' acc =
      let tab =
        try Evar.Map.find evk' acc
        with Not_found -> Evar.Set.empty
      in
      Evar.Map.add evk' (Evar.Set.add evk tab) acc
    in
    match evar_body evi with
    | Evar_empty -> acc
    | Evar_defined c -> Evar.Set.fold fold_ev (evars_of_term sigma c) acc
  in
  Evd.fold fold sigma Evar.Map.empty

let evar_dependency_closure n sigma =
  let open Evd in
  (* Create the DAG of depth [n] representing the recursive dependencies of
     undefined evars. *)
  let graph = compute_evar_dependency_graph sigma in
  let rec aux n curr accu =
    if Int.equal n 0 then Evar.Set.union curr accu
    else
      let fold evk accu =
        try
          let deps = Evar.Map.find evk graph in
          Evar.Set.union deps accu
        with Not_found -> accu
      in
      (* Consider only the newly added evars *)
      let ncurr = Evar.Set.fold fold curr Evar.Set.empty in
      (* Merge the others *)
      let accu = Evar.Set.union curr accu in
      aux (n - 1) ncurr accu
  in
  let undef = Evar.Map.domain (undefined_map sigma) in
  aux n undef Evar.Set.empty

let evar_dependency_closure n sigma =
  let open Evd in
  let deps = evar_dependency_closure n sigma in
  let map = Evar.Map.bind (fun ev -> find sigma ev) deps in
  Evar.Map.bindings map

let has_no_evar sigma =
  try let () = Evd.fold (fun _ _ () -> raise_notrace Exit) sigma () in true
  with Exit -> false

let pr_evd_level sigma = UState.pr_uctx_level (Evd.ustate sigma)

let pr_evd_qglobal sigma = UState.pr_uctx_qglobal (Evd.ustate sigma)

let pr_evd_qvar sigma = UState.pr_uctx_qvar (Evd.ustate sigma)

let pr_evd_quality sigma q = Quality.pr (Evd.quality_printer sigma) q

let reference_of_level sigma l = UState.qualid_of_level (Evd.ustate sigma) l

let pr_evar_universe_context = UState.pr

let print_env_short env sigma =
  let print_constr = Internal.print_kconstr in
  let pr_rel_decl = function
    | RelDecl.LocalAssum (n,_) -> Name.print n.binder_name
    | RelDecl.LocalDef (n,b,_) -> str "(" ++ Name.print n.binder_name ++ str " := "
                                  ++ print_constr env sigma (EConstr.of_constr b) ++ str ")"
  in
  let pr_named_decl = NamedDecl.to_rel_decl %> pr_rel_decl in
  let nc = List.rev (named_context env) in
  let rc = List.rev (rel_context env) in
    str "[" ++ pr_sequence pr_named_decl nc ++ str "]" ++ spc () ++
    str "[" ++ pr_sequence pr_rel_decl rc ++ str "]"

let pr_evar_constraints sigma pbs =
  let pr_evconstr (pbty, env, t1, t2) =
    let env =
      (* We currently allow evar instances to refer to anonymous de
         Bruijn indices, so we protect the error printing code in this
         case by giving names to every de Bruijn variable in the
         rel_context of the conversion problem. MS: we should rather
         stop depending on anonymous variables, they can be used to
         indicate independency. Also, this depends on a strategy for
         naming/renaming. *)
      Namegen.make_all_name_different env sigma
    in
    hov 2 (hov 2 (print_env_short env sigma) ++ spc () ++ str "|-" ++ spc () ++
      Internal.print_kconstr env sigma t1 ++ spc () ++
      str (match pbty with
            | Conversion.CONV -> "=="
            | Conversion.CUMUL -> "<=") ++
      spc () ++ Internal.print_kconstr env sigma t2)
  in
  prlist_with_sep fnl pr_evconstr pbs

let pr_evar_map_gen with_univs pr_evars env sigma =
  let uvs = Evd.ustate sigma in
  let (_, conv_pbs) = Evd.extract_all_conv_pbs sigma in
  let evs = if has_no_evar sigma then mt () else pr_evars sigma ++ fnl ()
  and svs = if with_univs then UState.pr uvs else mt ()
  and cstrs =
    if List.is_empty conv_pbs then mt ()
    else
    str "CONSTRAINTS:" ++ brk (0, 1) ++
      pr_evar_constraints sigma conv_pbs ++ fnl ()
  and typeclasses =
    let evars = Evd.get_typeclass_evars sigma in
    if Evar.Set.is_empty evars then mt ()
    else
      str "TYPECLASSES:" ++ brk (0, 1) ++
      prlist_with_sep spc Evar.print (Evar.Set.elements evars) ++ fnl ()
  and obligations =
    let evars = Evd.get_obligation_evars sigma in
    if Evar.Set.is_empty evars then mt ()
    else
      str "OBLIGATIONS:" ++ brk (0, 1) ++
      prlist_with_sep spc Evar.print (Evar.Set.elements evars) ++ fnl ()
  and shelf =
    str "SHELF:" ++ brk (0, 1) ++ Evd.pr_shelf sigma ++ fnl ()
  and future_goals =
    str "FUTURE GOALS STACK:" ++ brk (0, 1) ++ Evd.pr_future_goals_stack sigma ++ fnl ()
  in
  evs ++ svs ++ cstrs ++ typeclasses ++ obligations ++ shelf ++ future_goals

let pr_evar_list env sigma l =
  let open Evd in
  let pr_alias ev =
    match is_aliased_evar sigma ev with
    | None -> mt ()
    | Some ev' -> str " (aliased to " ++ Evar.print ev' ++ str ")"
  in
  let pr (ev, EvarInfo evi) =
    h (Evar.print ev ++
      str "==" ++ pr_evar_info env sigma evi ++
      pr_alias ev ++
      begin match Evd.evar_body evi with
      | Evar_empty -> str " {" ++ pr_existential_key env sigma ev ++ str "}"
      | Evar_defined _ -> mt ()
      end)
  in
  hv 0 (prlist_with_sep fnl pr l)

let to_list d =
  let open Evd in
  (* Workaround for change in Map.fold behavior in ocaml 3.08.4 *)
  let l = ref [] in
  let fold_def evk (EvarInfo evi) () = match Evd.evar_body evi with
    | Evar_defined _ -> l := (evk, EvarInfo evi) :: !l
    | Evar_empty -> ()
  in
  let fold_undef evk (EvarInfo evi) () = match Evd.evar_body evi with
    | Evar_empty -> l := (evk, EvarInfo evi) :: !l
    | Evar_defined _ -> ()
  in
  Evd.fold fold_def d ();
  Evd.fold fold_undef d ();
  !l

let pr_evar_by_depth depth env sigma = match depth with
| None ->
  (* Print all evars *)
  str"EVARS:" ++ brk(0,1) ++ pr_evar_list env sigma (to_list sigma) ++ fnl()
| Some n ->
  (* Print closure of undefined evars *)
  str"UNDEFINED EVARS:"++
  (if Int.equal n 0 then mt() else str" (+level "++int n++str" closure):")++
  brk(0,1)++
  pr_evar_list env sigma (evar_dependency_closure n sigma) ++ fnl()

let pr_evar_by_filter filter env sigma =
  let open Evd in
  let elts = Evd.fold (fun evk evi accu -> (evk, evi) :: accu) sigma [] in
  let elts = List.rev elts in
  let is_def (_, EvarInfo evi) = match Evd.evar_body evi with
  | Evar_defined _ -> true
  | Evar_empty -> false
  in
  let (defined, undefined) = List.partition is_def elts in
  let filter (evk, evi) = filter evk evi in
  let defined = List.filter filter defined in
  let undefined = List.filter filter undefined in
  let prdef =
    if List.is_empty defined then mt ()
    else str "DEFINED EVARS:" ++ brk (0, 1) ++
      pr_evar_list env sigma defined
  in
  let prundef =
    if List.is_empty undefined then mt ()
    else str "UNDEFINED EVARS:" ++ brk (0, 1) ++
      pr_evar_list env sigma undefined
  in
  prdef ++ prundef

let pr_evar_map ?(with_univs=true) depth env sigma =
  pr_evar_map_gen with_univs (fun sigma -> pr_evar_by_depth depth env sigma) env sigma

let pr_evar_map_filter ?(with_univs=true) filter env sigma =
  pr_evar_map_gen with_univs (fun sigma -> pr_evar_by_filter filter env sigma) env sigma

(* [Rel (n+m);...;Rel(n+1)] *)
let rel_vect n m = Array.init m (fun i -> mkRel(n+m-i))

let rel_list n m =
  let open EConstr in
  let rec reln l p =
    if p>m then l else reln (mkRel(n+p)::l) (p+1)
  in
  reln [] 1

let push_rel_assum (x,t) env =
  let open RelDecl in
  let open EConstr in
  push_rel (LocalAssum (x,t)) env

let push_rels_assum assums =
  let open RelDecl in
  push_rel_context (List.map (fun (x,t) -> LocalAssum (x,t)) assums)

let lookup_rel_id id sign =
  let open RelDecl in
  let rec lookrec n = function
    | [] -> raise Not_found
    | decl :: l ->
      if Names.Name.equal (Name id) (get_name decl)
      then (n, get_value decl, get_type decl)
      else lookrec (n+1) l
  in
  lookrec 1 sign

(* On Constr *)
let it_named_context_quantifier f ~init = List.fold_left (fun c d -> f d c) init
let it_mkNamedProd_wo_LetIn init = it_named_context_quantifier mkNamedProd_wo_LetIn ~init

let it_mkLambda_or_LetIn_from_no_LetIn c decls =
  let open RelDecl in
  let rec aux k decls c = match decls with
  | [] -> c
  | LocalDef (na,b,t) :: decls -> mkLetIn (na,b,t,aux (k-1) decls (liftn 1 k c))
  | LocalAssum (na,t) :: decls -> mkLambda (na,t,aux (k-1) decls c)
  in aux (List.length decls) (List.rev decls) c

(* strips head casts and flattens head applications *)
let rec strip_head_cast sigma c = match EConstr.kind sigma c with
  | App (f,cl) ->
      let rec collapse_rec f cl2 = match EConstr.kind sigma f with
        | App (g,cl1) -> collapse_rec g (Array.append cl1 cl2)
        | Cast (c,_,_) -> collapse_rec c cl2
        | _ -> if Int.equal (Array.length cl2) 0 then f else EConstr.mkApp (f,cl2)
      in
      collapse_rec f cl
  | Cast (c,_,_) -> strip_head_cast sigma c
  | _ -> c

let rec drop_extra_implicit_args sigma c = match EConstr.kind sigma c with
  (* Removed trailing extra implicit arguments, what improves compatibility
     for constants with recently added maximal implicit arguments *)
  | App (f,args) when EConstr.isEvar sigma (Array.last args) ->
      let open EConstr in
      drop_extra_implicit_args sigma
        (mkApp (f,fst (Array.chop (Array.length args - 1) args)))
  | _ -> c

let last_arg sigma c = match EConstr.kind sigma c with
  | App (f,cl) -> Array.last cl
  | _ -> anomaly (Pp.str "last_arg.")

let adjust_app_list_size f1 l1 f2 l2 =
  let open EConstr in
  let len1 = List.length l1 and len2 = List.length l2 in
  if Int.equal len1 len2 then (f1,l1,f2,l2)
  else if len1 < len2 then
   let extras,restl2 = List.chop (len2-len1) l2 in
    (f1, l1, applist (f2,extras), restl2)
  else
    let extras,restl1 = List.chop (len1-len2) l1 in
    (applist (f1,extras), restl1, f2, l2)

let adjust_app_array_size f1 l1 f2 l2 =
  let open EConstr in
  let len1 = Array.length l1 and len2 = Array.length l2 in
  if Int.equal len1 len2 then (f1,l1,f2,l2)
  else if len1 < len2 then
    let extras,restl2 = Array.chop (len2-len1) l2 in
    (f1, l1, mkApp (f2,extras), restl2)
  else
    let extras,restl1 = Array.chop (len1-len2) l1 in
    (mkApp (f1,extras), restl1, f2, l2)

(* [map_constr_with_binders_left_to_right g f n c] maps [f n] on the
   immediate subterms of [c]; it carries an extra data [n] (typically
   a lift index) which is processed by [g] (which typically add 1 to
   [n]) at each binder traversal; the subterms are processed from left
   to right according to the usual representation of the constructions
   (this may matter if [f] does a side-effect); it is not recursive;
   in fact, the usual representation of the constructions is at the
   time being almost those of the ML representation (except for
   (co-)fixpoint) *)

let fold_rec_types g (lna,typarray,_) e =
  let open EConstr in
  let open Vars in
  let ctxt = Array.map2_i (fun i na t -> RelDecl.LocalAssum (na, lift i t)) lna typarray in
  Array.fold_left (fun e assum -> g assum e) e ctxt

let map_left2 f a g b =
  let l = Array.length a in
  if Int.equal l 0 then [||], [||] else begin
    let r = Array.make l (f a.(0)) in
    let s = Array.make l (g b.(0)) in
    for i = 1 to l - 1 do
      r.(i) <- f a.(i);
      s.(i) <- g b.(i)
    done;
    r, s
  end

let map_constr_with_binders_left_to_right env sigma g f l c =
  let open RelDecl in
  let open EConstr in
  match EConstr.kind sigma c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _ | String _) -> c
  | Cast (b,k,t) ->
    let b' = f l b in
    let t' = f l t in
      if b' == b && t' == t then c
      else mkCast (b',k,t')
  | Prod (na,t,b) ->
      let t' = f l t in
      let b' = f (g (LocalAssum (na,t)) l) b in
        if t' == t && b' == b then c
        else mkProd (na, t', b')
  | Lambda (na,t,b) ->
      let t' = f l t in
      let b' = f (g (LocalAssum (na,t)) l) b in
        if t' == t && b' == b then c
        else mkLambda (na, t', b')
  | LetIn (na,bo,t,b) ->
      let bo' = f l bo in
      let t' = f l t in
      let b' = f (g (LocalDef (na,bo,t)) l) b in
        if bo' == bo && t' == t && b' == b then c
        else mkLetIn (na, bo', t', b')
  | App (c,[||]) -> assert false
  | App (t,al) ->
      (*Special treatment to be able to recognize partially applied subterms*)
      let a = al.(Array.length al - 1) in
      let app = (mkApp (t, Array.sub al 0 (Array.length al - 1))) in
      let app' = f l app in
      let a' = f l a in
        if app' == app && a' == a then c
        else mkApp (app', [| a' |])
  | Proj (p,r,b) ->
    let b' = f l b in
      if b' == b then c
      else mkProj (p, r, b')
  | Evar ev ->
    let ev' = EConstr.map_existential sigma (fun c -> f l c) ev in
    if ev' == ev then c else mkEvar ev'
  | Case (ci,u,pms,(p,r),iv,b,bl) ->
      let (ci, _, pms, (p0,_), _, b, bl0) = annotate_case env sigma (ci, u, pms, (p,r), iv, b, bl) in
      let f_ctx (nas, _ as r) (ctx, c) =
        let c' = f (List.fold_right g ctx l) c in
        if c' == c then r else (nas, c')
      in
      (* In v8 concrete syntax, predicate is after the term to match! *)
      let b' = f l b in
      let pms' = Array.map_left (f l) pms in
      let p' = f_ctx p p0 in
      let iv' = map_invert (f l) iv in
      let bl' = Array.map_left (fun (c, c0) -> f_ctx c c0) (Array.map2 (fun x y -> (x, y)) bl bl0) in
        if b' == b && pms' == pms && p' == p && iv' == iv && bl' == bl then c
        else mkCase (ci, u, pms', (p',r), iv', b', bl')
  | Fix (ln,(lna,tl,bl as fx)) ->
      let l' = fold_rec_types g fx l in
      let (tl', bl') = map_left2 (f l) tl (f l') bl in
        if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl'
        then c
        else mkFix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl as fx)) ->
      let l' = fold_rec_types g fx l in
      let (tl', bl') = map_left2 (f l) tl (f l') bl in
        if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl'
        then c
        else mkCoFix (ln,(lna,tl',bl'))
  | Array(u,t,def,ty) ->
      let t' = Array.map_left (f l) t in
      let def' = f l def in
      let ty' = f l ty in
      if def' == def && t' == t && ty' == ty then c
      else mkArray(u,t',def',ty')
  | PBlock (u,ty,entries,t) ->
      let ty' = f l ty in
      let body_l, entries' = Array.fold_left_map
        (fun entry_l entry ->
          let context', context_l = List.fold_right
            (fun decl (context, context_l) ->
              let decl' = RelDecl.map_constr (f context_l) decl in
              decl' :: context, g decl context_l)
            entry.pbe_context ([], entry_l)
          in
          let type' = f context_l entry.pbe_type in
          let value' = f context_l entry.pbe_value in
          let hidden_type = it_mkProd_or_LetIn entry.pbe_type entry.pbe_context in
          let body_l = g (LocalAssum
            (Context.make_annot Anonymous entry.pbe_relevance, hidden_type)) entry_l
          in
          body_l,
          if context' == entry.pbe_context && type' == entry.pbe_type && value' == entry.pbe_value
          then entry
          else { entry with pbe_context = context'; pbe_type = type'; pbe_value = value' })
        l entries
      in
      let entries' = if Array.for_all2 (==) entries entries' then entries else entries' in
      let t' = f body_l t in
      if ty' == ty && entries' == entries && t' == t then c
      else mkPBlock (u,ty',entries',t')
  | PRun (ty,k,b,cont) ->
      let ty' = f l ty in
      let k' = f l k in
      let b' = f l b in
      let cont' = f l cont in
      if ty' == ty && k' == k && b' == b && cont' == cont then c
      else mkPRun (ty',k',b',cont')

(* strong *)
let map_constr_with_full_binders env sigma g f l cstr =
  let open EConstr in
  match EConstr.kind sigma cstr with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _ | String _) -> cstr
  | Cast (c,k, t) ->
      let c' = f l c in
      let t' = f l t in
      if c==c' && t==t' then cstr else mkCast (c', k, t')
  | Prod (na,t,c) ->
      let t' = f l t in
      let c' = f (g (RelDecl.LocalAssum (na, t)) l) c in
      if t==t' && c==c' then cstr else mkProd (na, t', c')
  | Lambda (na,t,c) ->
      let t' = f l t in
      let c' = f (g (RelDecl.LocalAssum (na, t)) l) c in
      if t==t' && c==c' then cstr else  mkLambda (na, t', c')
  | LetIn (na,b,t,c) ->
      let b' = f l b in
      let t' = f l t in
      let c' = f (g (RelDecl.LocalDef (na, b, t)) l) c in
      if b==b' && t==t' && c==c' then cstr else mkLetIn (na, b', t', c')
  | App (c,al) ->
      let c' = f l c in
      let al' = Array.map (f l) al in
      if c==c' && Array.for_all2 (==) al al' then cstr else mkApp (c', al')
  | Proj (p,r,c) ->
      let c' = f l c in
        if c' == c then cstr else mkProj (p, r, c')
  | Evar ev ->
    let ev' = EConstr.map_existential sigma (fun c -> f l c) ev in
    if ev' == ev then cstr else mkEvar ev'
  | Case (ci, u, pms, (p,r), iv, c, bl) ->
      let (ci, _, pms, (p0,_), _, c, bl0) = annotate_case env sigma (ci, u, pms, (p,r), iv, c, bl) in
      let f_ctx (nas, _ as r) (ctx, c) =
        let c' = f (List.fold_right g ctx l) c in
        if c' == c then r else (nas, c')
      in
      let pms' = Array.Smart.map (f l) pms in
      let p' = f_ctx p p0 in
      let iv' = map_invert (f l) iv in
      let c' = f l c in
      let bl' = Array.map2 f_ctx bl bl0 in
      if pms==pms' && p==p' && iv'==iv && c==c' && Array.for_all2 (==) bl bl' then cstr else
        mkCase (ci, u, pms', (p',r), iv', c', bl')
  | Fix (ln,(lna,tl,bl as fx)) ->
      let tl' = Array.map (f l) tl in
      let l' = fold_rec_types g fx l in
      let bl' = Array.map (f l') bl in
      if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl'
      then cstr
      else mkFix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl as fx)) ->
      let tl' = Array.map (f l) tl in
      let l' = fold_rec_types g fx l in
      let bl' = Array.map (f l') bl in
      if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl'
      then cstr
      else mkCoFix (ln,(lna,tl',bl'))
  | Array(u,t,def,ty) ->
      let t' = Array.Smart.map (f l) t in
      let def' = f l def in
      let ty' = f l ty in
      if def==def' && t == t' && ty==ty' then cstr else mkArray (u,t', def',ty')
  | PBlock (u,ty,entries,t) ->
      let ty' = f l ty in
      let body_l, entries' = Array.fold_left_map
        (fun entry_l entry ->
          let context', context_l = List.fold_right
            (fun decl (context, context_l) ->
              let decl' = RelDecl.map_constr (f context_l) decl in
              decl' :: context, g decl context_l)
            entry.pbe_context ([], entry_l)
          in
          let type' = f context_l entry.pbe_type in
          let value' = f context_l entry.pbe_value in
          let hidden_type = it_mkProd_or_LetIn entry.pbe_type entry.pbe_context in
          let body_l = g (LocalAssum
            (Context.make_annot Anonymous entry.pbe_relevance, hidden_type)) entry_l
          in
          body_l,
          if context' == entry.pbe_context && type' == entry.pbe_type && value' == entry.pbe_value
          then entry
          else { entry with pbe_context = context'; pbe_type = type'; pbe_value = value' })
        l entries
      in
      let entries' = if Array.for_all2 (==) entries entries' then entries else entries' in
      let t' = f body_l t in
      if ty' == ty && entries' == entries && t' == t then cstr
      else mkPBlock (u,ty',entries',t')
  | PRun (ty,k,b,cont) ->
      let ty' = f l ty in
      let k' = f l k in
      let b' = f l b in
      let cont' = f l cont in
      if ty' == ty && k' == k && b' == b && cont' == cont then cstr
      else mkPRun (ty',k',b',cont')

(* [fold_constr_with_binders g f n acc c] folds [f n] on the immediate
   subterms of [c] starting from [acc] and proceeding from left to
   right according to the usual representation of the constructions as
   [fold_constr] but it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive *)

let fold_constr_with_full_binders env sigma g f n acc c =
  let open EConstr.Vars in
  let open Context.Rel.Declaration in
  match EConstr.kind sigma c with
  | Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _ | Construct _  | Int _ | Float _ | String _ -> acc
  | Cast (c,_, t) -> f n (f n acc c) t
  | Prod (na,t,c) -> f (g (LocalAssum (na,t)) n) (f n acc t) c
  | Lambda (na,t,c) -> f (g (LocalAssum (na,t)) n) (f n acc t) c
  | LetIn (na,b,t,c) -> f (g (LocalDef (na,b,t)) n) (f n (f n acc b) t) c
  | App (c,l) -> Array.fold_left (f n) (f n acc c) l
  | Proj (_,_,c) -> f n acc c
  | Evar ev ->
    let args = Evd.expand_existential sigma ev in
    List.fold_left (fun c -> f n c) acc args
  | Case (ci, u, pms, p, iv, c, bl) ->
    let (ci, _, pms, (p,_), _, c, bl) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, c, bl) in
    let f_ctx acc (ctx, c) = f (List.fold_right g ctx n) acc c in
    Array.fold_left f_ctx (f n (fold_invert (f n) (f_ctx (Array.fold_left (f n) acc pms) p) iv) c) bl
  | Fix (_,(lna,tl,bl)) ->
      let n' = CArray.fold_left2_i (fun i c n t -> g (LocalAssum (n,lift i t)) c) n lna tl in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
  | CoFix (_,(lna,tl,bl)) ->
      let n' = CArray.fold_left2_i (fun i c n t -> g (LocalAssum (n,lift i t)) c) n lna tl in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
  | Array(_u,t,def,ty) -> f n (f n (Array.fold_left (f n) acc t) def) ty
  | PBlock (_u,ty,entries,t) ->
    let n, acc = Array.fold_left
      (fun (entry_n, acc) entry ->
        let context_n, acc = Context.Rel.fold_outside
          (fun decl (context_n, acc) ->
            let acc = RelDecl.fold_constr (fun term acc -> f context_n acc term) decl acc in
            g decl context_n, acc)
          entry.pbe_context ~init:(entry_n, acc)
        in
        let acc = f context_n (f context_n acc entry.pbe_type) entry.pbe_value in
        let hidden_type = EConstr.it_mkProd_or_LetIn entry.pbe_type entry.pbe_context in
        let entry_n = g (LocalAssum
          (Context.make_annot Anonymous entry.pbe_relevance, hidden_type)) entry_n
        in
        entry_n, acc)
      (n, f n acc ty) entries
    in
    f n acc t
  | PRun (ty,k,b,cont) -> f n (f n (f n (f n acc ty) k) b) cont

(***************************)
(* occurs check functions  *)
(***************************)

exception Occur

let occur_meta sigma c =
  let rec occrec h c =
    let h, knd = EConstr.Expand.kind sigma h c in
    match knd with
    | Meta _ -> raise Occur
    | Evar (evk, args) ->
      let evi = Evd.find_undefined sigma evk in
      let args = EConstr.Expand.expand_instance ~skip:true evi h args in
      SList.Skip.iter (fun c -> occrec h c) args
    | _ -> EConstr.Expand.iter sigma occrec h knd
  in
  let h, c = EConstr.Expand.make c in
  try occrec h c; false with Occur -> true

let occur_existential sigma c =
  let rec occrec h c =
    let h, knd = EConstr.Expand.kind sigma h c in
    match knd with
    | Evar _ -> raise Occur
    | _ -> EConstr.Expand.iter sigma occrec h knd
  in
  let h, c = EConstr.Expand.make c in
  try occrec h c; false with Occur -> true

let occur_meta_or_existential sigma c =
  let rec occrec h c =
    let h, knd = EConstr.Expand.kind sigma h c in
    match knd with
    | Evar _ -> raise Occur
    | Meta _ -> raise Occur
    | _ -> EConstr.Expand.iter sigma occrec h knd
  in
  let h, c = EConstr.Expand.make c in
  try occrec h c; false with Occur -> true

let occur_metavariable sigma m c =
  let rec occrec c = match EConstr.kind sigma c with
  | Meta m' -> if Int.equal m m' then raise Occur
  | Evar (_, args) -> SList.Skip.iter occrec args
  | _ -> EConstr.iter sigma occrec c
  in
  try occrec c; false with Occur -> true

let occur_evar sigma n c =
  let rec occur_rec c = match EConstr.kind sigma c with
    | Evar (sp, args) ->
      if Evar.equal sp n then raise Occur
      else SList.Skip.iter occur_rec args
    | _ -> EConstr.iter sigma occur_rec c
  in
  try occur_rec c; false with Occur -> true

let occur_in_global env id constr =
  let vars = vars_of_global env constr in
  Id.Set.mem id vars

let occur_var env sigma id c =
  let rec occur_rec c =
    match EConstr.destRef sigma c with
    | gr, _ -> if occur_in_global env id gr then raise Occur
    | exception DestKO -> EConstr.iter sigma occur_rec c
  in
  try occur_rec c; false with Occur -> true

let occur_vars env sigma ids c =
  let rec occur_rec c =
    match EConstr.destRef sigma c with
    | gr, _ ->
      let vars = vars_of_global env gr in
      if not (Id.Set.is_empty (Id.Set.inter ids vars)) then raise Occur
    | exception DestKO -> EConstr.iter sigma occur_rec c
  in
  try occur_rec c; false with Occur -> true

exception OccurInGlobal of GlobRef.t

let occur_var_indirectly env sigma id c =
  let var = GlobRef.VarRef id in
  let rec occur_rec c =
    match EConstr.destRef sigma c with
    | gr, _ -> if not (QGlobRef.equal env gr var) && occur_in_global env id gr then raise (OccurInGlobal gr)
    | exception DestKO -> EConstr.iter sigma occur_rec c
  in
  try occur_rec c; None with OccurInGlobal gr -> Some gr

let occur_var_in_decl env sigma hyp decl =
  NamedDecl.exists (occur_var env sigma hyp) decl

let occur_vars_in_decl env sigma hyps decl =
  NamedDecl.exists (occur_vars env sigma hyps) decl

let local_occur_var sigma id c =
  let rec occur c = match EConstr.kind sigma c with
  | Var id' -> if Id.equal id id' then raise Occur
  | _ -> EConstr.iter sigma occur c
  in
  try occur c; false with Occur -> true

let local_occur_var_in_decl sigma hyp decl =
  NamedDecl.exists (local_occur_var sigma hyp) decl

  (* returns the list of free debruijn indices in a term *)

let free_rels sigma m =
  let rec frec depth acc c = match EConstr.kind sigma c with
    | Rel n       -> if n >= depth then Int.Set.add (n-depth+1) acc else acc
    | Evar (_, args) -> SList.Skip.fold (fun acc c -> frec depth acc c) acc args
    | _ -> EConstr.fold_with_binders sigma succ frec depth acc c
  in
  frec 1 Int.Set.empty m

(* collects all metavar occurrences, in left-to-right order, preserving
 * repetitions and all. *)

let collect_metas sigma c =
  let rec collrec acc c =
    match EConstr.kind sigma c with
      | Meta mv -> List.add_set Int.equal mv acc
      | Evar (_, args) -> SList.Skip.fold collrec acc args
      | _       -> EConstr.fold sigma collrec acc c
  in
  List.rev (collrec [] c)

(* collects all vars; warning: this is only visible vars, not dependencies in
   all section variables; for the latter, use global_vars_set *)
let collect_vars sigma c =
  let rec aux vars c = match EConstr.kind sigma c with
  | Var id -> Id.Set.add id vars
  | _ -> EConstr.fold sigma aux vars c in
  aux Id.Set.empty c

(* Tests whether [m] is a subterm of [t]:
   [m] is appropriately lifted through abstractions of [t] *)

let dependent_main noevar sigma m t =
  let open EConstr in
  let eqc x y = eq_constr_nounivs sigma x y in
  let rec deprec m t =
    if eqc m t then
      raise Occur
    else
      match EConstr.kind sigma m, EConstr.kind sigma t with
        | App (fm,lm), App (ft,lt) when Array.length lm < Array.length lt ->
            deprec m (mkApp (ft,Array.sub lt 0 (Array.length lm)));
            Array.Fun1.iter deprec m
              (Array.sub lt
                (Array.length lm) ((Array.length lt) - (Array.length lm)))
        | _, Cast (c,_,_) when noevar && isMeta sigma c -> ()
        | _, Evar _ when noevar -> ()
        | _ -> EConstr.iter_with_binders sigma (fun c -> Vars.lift 1 c) deprec m t
  in
  try deprec m t; false with Occur -> true

let dependent sigma c t = dependent_main false sigma c t
let dependent_no_evar sigma c t = dependent_main true sigma c t

let dependent_in_decl sigma a decl =
  NamedDecl.exists (dependent sigma a) decl

let count_occurrences sigma m t =
  let open EConstr in
  let n = ref 0 in
  let rec countrec m t =
    if EConstr.eq_constr sigma m t then
      incr n
    else
      match EConstr.kind sigma m, EConstr.kind sigma t with
        | App (fm,lm), App (ft,lt) when Array.length lm < Array.length lt ->
            countrec m (mkApp (ft,Array.sub lt 0 (Array.length lm)));
            Array.iter (countrec m)
              (Array.sub lt
                (Array.length lm) ((Array.length lt) - (Array.length lm)))
        | _, Cast (c,_,_) when isMeta sigma c -> ()
        | _, Evar _ -> ()
        | _ -> EConstr.iter_with_binders sigma (Vars.lift 1) countrec m t
  in
  countrec m t;
  !n

let pop t = EConstr.Vars.lift (-1) t

(***************************)
(*  bindings functions *)
(***************************)

type meta_type_map = (metavariable * types) list

type meta_value_map = (metavariable * constr) list

let isMetaOf sigma mv c =
  match EConstr.kind sigma c with Meta mv' -> Int.equal mv mv' | _ -> false

let rec subst_meta bl c =
  match kind c with
    | Meta i -> (try Int.List.assoc i bl with Not_found -> c)
    | _ -> Constr.map (subst_meta bl) c

let rec strip_outer_cast sigma c = match EConstr.kind sigma c with
  | Cast (c,_,_) -> strip_outer_cast sigma c
  | _ -> c

(* First utilities for avoiding telescope computation for subst_term *)

let prefix_application sigma eq_fun k l1 t =
  let open EConstr in
  if 0 < l1 then match EConstr.kind sigma t with
    | App (f2,cl2) ->
        let l2 = Array.length cl2 in
        if l1 <= l2
           && eq_fun sigma k (mkApp (f2, Array.sub cl2 0 l1)) then
          Some (Array.sub cl2 l1 (l2 - l1))
        else
          None
    | _ -> None
  else None

let eq_upto_lift cache c sigma k t =
  let c =
    try Int.Map.find k !cache
    with Not_found ->
      let c = EConstr.Vars.lift k c in
      let () = cache := Int.Map.add k c !cache in
      c
  in
  EConstr.eq_constr sigma c t

(* Recognizing occurrences of a given subterm in a term :
   [replace_term c1 c2 t] substitutes [c2] for all occurrences of
   term [c1] in a term [t]; works if [c1] and [c2] have rels *)

let replace_term_gen sigma eq_fun ar by_c in_t =
  let rec substrec k t =
    match prefix_application sigma eq_fun k ar t with
      | Some args -> EConstr.mkApp (EConstr.Vars.lift k by_c, args)
      | None ->
    (if eq_fun sigma k t then (EConstr.Vars.lift k by_c) else
      EConstr.map_with_binders sigma succ substrec k t)
  in
  substrec 0 in_t

let replace_term sigma c byc t =
  let cache = ref Int.Map.empty in
  let ar = Array.length (snd (EConstr.decompose_app sigma c)) in
  let eq sigma k t = eq_upto_lift cache c sigma k t in
  replace_term_gen sigma eq ar byc t

let subst_term sigma c t = replace_term sigma c (EConstr.mkRel 1) t

let add_vname vars = function
    Name id -> Id.Set.add id vars
  | _ -> vars

(*************************)
(*   Names environments  *)
(*************************)
type names_context = Name.t list
let add_name n nl = n::nl
let lookup_name_of_rel p names =
  try List.nth names (p-1)
  with Invalid_argument _ | Failure _ -> raise Not_found
let lookup_rel_of_name id names =
  let rec lookrec n = function
    | Anonymous :: l  -> lookrec (n+1) l
    | (Name id') :: l -> if Id.equal id' id then n else lookrec (n+1) l
    | []            -> raise Not_found
  in
  lookrec 1 names
let empty_names_context = []

let ids_of_rel_context sign =
  Context.Rel.fold_outside
    (fun decl l -> match RelDecl.get_name decl with Name id -> id::l | Anonymous -> l)
    sign ~init:[]

let ids_of_named_context sign =
  Context.Named.fold_outside (fun decl idl -> NamedDecl.get_id decl :: idl) sign ~init:[]

let ids_of_context env =
  (ids_of_rel_context (rel_context env))
  @ (ids_of_named_context (named_context env))


let names_of_rel_context env =
  List.map RelDecl.get_name (rel_context env)

let is_section_variable_sign ?check sign id =
  match Environ.var_status_ctxt ?check id sign with
  | SecVar -> true
  | ProofVar -> false

let is_section_variable_env ?check env id =
  is_section_variable_sign ?check (Environ.named_context_val env) id

let is_template_polymorphic_ref env sigma f =
  match EConstr.kind sigma f with
  | Ind (ind, u) | Construct ((ind, _), u) ->
    if not (EConstr.EInstance.is_empty u) then false
    else Environ.template_polymorphic_ind ind env
  | _ -> false

let is_template_polymorphic_ind env sigma f =
  match EConstr.kind sigma f with
  | Ind (ind, u) ->
    if not (EConstr.EInstance.is_empty u) then false
    else Environ.template_polymorphic_ind ind env
  | _ -> false

let base_sort_cmp pb s0 s1 =
  match (s0,s1) with
  | SProp, SProp | Prop, Prop | Set, Set | Type _, Type _ -> true
  | VSort (q1, _), VSort (q2, _) -> Sorts.QVar.equal q1 q2
  | VSort _, _ | _, VSort _ -> false
  | GSort (q1, _), GSort (q2, _) -> Sorts.QGlobal.equal q1 q2
  | GSort _, _ | _, GSort _ -> false
  | SProp, _ | _, SProp -> false
  | Prop, Set | Prop, Type _ | Set, Type _ -> pb == Conversion.CUMUL
  | Set, Prop | Type _, Prop | Type _, Set -> false

let rec is_Prop sigma c = match EConstr.kind sigma c with
  | Sort u ->
    begin match EConstr.ESorts.kind sigma u with
    | Prop -> true
    | _ -> false
    end
  | Cast (c,_,_) -> is_Prop sigma c
  | _ -> false

let rec is_Set sigma c = match EConstr.kind sigma c with
  | Sort u ->
    begin match EConstr.ESorts.kind sigma u with
    | Set -> true
    | _ -> false
    end
  | Cast (c,_,_) -> is_Set sigma c
  | _ -> false

let rec is_Type sigma c = match EConstr.kind sigma c with
  | Sort u ->
    begin match EConstr.ESorts.kind sigma u with
    | Type _ -> true
    | _ -> false
    end
  | Cast (c,_,_) -> is_Type sigma c
  | _ -> false

(* eq_constr extended with universe erasure *)
let compare_constr_univ env sigma f cv_pb t1 t2 =
  let open EConstr in
  match EConstr.kind sigma t1, EConstr.kind sigma t2 with
      Sort s1, Sort s2 -> base_sort_cmp cv_pb (ESorts.kind sigma s1) (ESorts.kind sigma s2)
    | Prod (_,t1,c1), Prod (_,t2,c2) ->
        f Conversion.CONV t1 t2 && f cv_pb c1 c2
    | Const (c, u), Const (c', u') -> QConstant.equal env c c'
    | Ind (i, _), Ind (i', _) -> QInd.equal env i i'
    | Construct (i, _), Construct (i', _) -> QConstruct.equal env i i'
    | _ -> EConstr.compare_constr sigma (fun t1 t2 -> f Conversion.CONV t1 t2) t1 t2

let constr_cmp env sigma cv_pb t1 t2 =
  let rec compare cv_pb t1 t2 = compare_constr_univ env sigma compare cv_pb t1 t2 in
  compare cv_pb t1 t2

let eq_constr env sigma t1 t2 = constr_cmp env sigma Conversion.CONV t1 t2

let nb_lam sigma c =
  let rec nbrec n c = match EConstr.kind sigma c with
    | Lambda (_,_,c) -> nbrec (n+1) c
    | Cast (c,_,_) -> nbrec n c
    | _ -> n
  in
  nbrec 0 c

let nb_prod sigma c =
  let rec nbrec n c = match EConstr.kind sigma c with
    | Prod (_,_,c) -> nbrec (n+1) c
    | Cast (c,_,_) -> nbrec n c
    | _ -> n
  in
  nbrec 0 c

let nb_prod_modulo_zeta sigma x =
  let rec count n c =
    match EConstr.kind sigma c with
        Prod(_,_,t) -> count (n+1) t
      | LetIn(_,a,_,t) -> count n (EConstr.Vars.subst1 a t)
      | Cast(c,_,_) -> count n c
      | _ -> n
  in count 0 x

(* We reduce a series of head eta-redex or nothing at all   *)
(* [x1:c1;...;xn:cn]@(f;a1...an;x1;...;xn) --> @(f;a1...an) *)
(* Remplace 2 earlier buggish versions                      *)

let rec eta_reduce_head sigma c =
  let open EConstr in
  let open Vars in
  match EConstr.kind sigma c with
    | Lambda (_,c1,c') ->
        (match EConstr.kind sigma (eta_reduce_head sigma c') with
           | App (f,cl) ->
               let lastn = (Array.length cl) - 1 in
               if lastn < 0 then anomaly (Pp.str "application without arguments.")
               else
                 (match EConstr.kind sigma cl.(lastn) with
                    | Rel 1 ->
                        let c' =
                          if Int.equal lastn 0 then f
                          else mkApp (f, Array.sub cl 0 lastn)
                        in
                        if noccurn sigma 1 c'
                        then lift (-1) c'
                        else c
                    | _   -> c)
           | _ -> c)
    | _ -> c

let eta_expand_instantiation ?evars env inst ctxt =
  let open Context.Rel.Declaration in
  let eta_inst = Array.make (Array.length inst) mkProp in
  let rec fold subst i = function
  | [] -> assert (Array.length inst = i)
  | LocalAssum (_, ty) :: ctx ->
    let ty = substl subst ty in
    let eta_t = Reduction.eta_expand ?evars env inst.(i) ty in
    let () = eta_inst.(i) <- eta_t in
    fold (eta_t :: subst) (i + 1) ctx
  | LocalDef (_, bd, _) :: ctx ->
    fold (bd :: subst) i ctx
  in
  let () = fold [] 0 (List.rev ctxt) in
  eta_inst

(* iterator on rel context *)
let process_rel_context f env =
  let sign = named_context_val env in
  let rels = EConstr.rel_context env in
  let env0 = reset_with_named_context sign env in
  Context.Rel.fold_outside f rels ~init:env0

let assums_of_rel_context sign =
  Context.Rel.fold_outside
    (fun decl l ->
      match decl with
      | RelDecl.LocalDef _ -> l
      | RelDecl.LocalAssum (na,t) -> (na, t)::l)
    sign ~init:[]

let map_rel_context_in_env f env sign =
  let rec aux env acc = function
    | d::sign ->
        aux (push_rel d env) (RelDecl.map_constr (f env) d :: acc) sign
    | [] ->
        acc
  in
  aux env [] (List.rev sign)

let fold_named_context_both_sides f l ~init = List.fold_right_and_left f l init

let mem_named_context_val id ctxt =
  try ignore(Environ.lookup_named_ctxt id ctxt); true with Not_found -> false

let clear_named_body id env =
  let open NamedDecl in
  let aux _ status = function
  | LocalDef (id',c,t) when Id.equal id id'.binder_name -> push_named status (LocalAssum (id',t))
  | d -> push_named status d in
  fold_named_context aux env ~init:(reset_context env)

let global_vars_set env sigma constr =
  let rec filtrec acc c =
    match EConstr.destRef sigma c with
    | gr, _ -> Id.Set.union (vars_of_global env gr) acc
    | exception DestKO -> EConstr.fold sigma filtrec acc c
  in
  filtrec Id.Set.empty constr

let global_vars_set_of_decl env sigma = function
  | NamedDecl.LocalAssum (_,t) -> global_vars_set env sigma t
  | NamedDecl.LocalDef (_,c,t) ->
      Id.Set.union (global_vars_set env sigma t)
        (global_vars_set env sigma c)

let dependency_closure env sigma sign hyps =
  if Id.Set.is_empty hyps then [] else
    let (_,lh) =
      Context.Named.fold_inside
        (fun (hs,hl) d ->
          let x = NamedDecl.get_id d in
          if Id.Set.mem x hs then
            (Id.Set.union (global_vars_set_of_decl env sigma d) (Id.Set.remove x hs),
            x::hl)
          else (hs,hl))
        ~init:(hyps,[])
        sign in
    List.rev lh

let global_app_of_constr env sigma c =
  let open GlobRef in
  match EConstr.kind sigma c with
  | Const (c, u) -> (ConstRef c, u), None
  | Ind (i, u) -> (IndRef i, u), None
  | Construct (c, u) -> (ConstructRef c, u), None
  | Var id -> (VarRef id, EConstr.EInstance.empty), None
  | Proj (p, _, c) -> (ConstRef (Environ.projection_repr_constant env (Projection.repr p)), EConstr.EInstance.empty), Some c
  | _ -> raise Not_found

let prod_applist sigma c l =
  let open EConstr in
  let rec app subst c l =
    match EConstr.kind sigma c, l with
    | Prod(_,_,c), arg::l -> app (arg::subst) c l
    | _, [] -> Vars.substl subst c
    | _ -> anomaly (Pp.str "Not enough prod's.") in
  app [] c l

let prod_applist_decls sigma n c l =
  let open EConstr in
  let rec app n subst c l =
    if Int.equal n 0 then
      if l == [] then Vars.substl subst c
      else anomaly (Pp.str "Not enough arguments.")
    else match EConstr.kind sigma c, l with
    | Prod(_,_,c), arg::l -> app (n-1) (arg::subst) c l
    | LetIn(_,b,_,c), _ -> app (n-1) (Vars.substl subst b::subst) c l
    | _ -> anomaly (Pp.str "Not enough prod/let's.") in
  app n [] c l

(* Do not skip let-in's *)
let env_rel_context_chop k env =
  let open EConstr in
  let rels = rel_context env in
  let ctx1,ctx2 = List.chop k rels in
  push_rel_context ctx2 (reset_with_named_context (named_context_val env) env),
  ctx1

(** Terms as a datatype *)

module ConstrData =
struct

open Constr

type t = Constr.t

let compare_invert f iv1 iv2 =
  match iv1, iv2 with
  | NoInvert, NoInvert -> 0
  | NoInvert, CaseInvert _ -> -1
  | CaseInvert _, NoInvert -> 1
  | CaseInvert iv1, CaseInvert iv2 ->
    Array.compare f iv1.indices iv2.indices

let constr_ord_int f t1 t2 =
  let open! Compare in
  let fix_cmp (a1, i1) (a2, i2) =
    compare [(Array.compare Int.compare,a1,a2); (Int.compare,i1,i2)]
  in
  let ctx_cmp f (_n1, p1) (_n2, p2) = f p1 p2 in
  let decl_cmp f d1 d2 = match d1, d2 with
    | RelDecl.LocalAssum (_, ty1), RelDecl.LocalAssum (_, ty2) -> f ty1 ty2
    | RelDecl.LocalAssum _, RelDecl.LocalDef _ -> -1
    | RelDecl.LocalDef _, RelDecl.LocalAssum _ -> 1
    | RelDecl.LocalDef (_, value1, ty1), RelDecl.LocalDef (_, value2, ty2) ->
      compare [(f, value1, value2); (f, ty1, ty2)]
  in
  let entry_cmp f entry1 entry2 =
    compare [
      (List.compare (decl_cmp f), entry1.pbe_context, entry2.pbe_context);
      (f, entry1.pbe_type, entry2.pbe_type);
      (f, entry1.pbe_value, entry2.pbe_value);
    ]
  in
  match kind t1, kind t2 with
    | Cast (c1,_,_), _ -> f c1 t2
    | _, Cast (c2,_,_) -> f t1 c2
    (* Why this special case? *)
    | App (c1,l1), _ when isCast c1 -> let c1 = pi1 (destCast c1) in f (mkApp (c1,l1)) t2
    | _, App (c2,l2) when isCast c2 -> let c2 = pi1 (destCast c2) in f t1 (mkApp (c2,l2))
    | Rel n1, Rel n2 -> Int.compare n1 n2
    | Rel _, _ -> -1 | _, Rel _ -> 1
    | Var id1, Var id2 -> Id.compare id1 id2
    | Var _, _ -> -1 | _, Var _ -> 1
    | Meta m1, Meta m2 -> Int.compare m1 m2
    | Meta _, _ -> -1 | _, Meta _ -> 1
    | Evar (e1,l1), Evar (e2,l2) ->
      compare [(Evar.compare, e1, e2); (SList.compare f, l1, l2)]
    | Evar _, _ -> -1 | _, Evar _ -> 1
    | Sort s1, Sort s2 -> Sorts.compare s1 s2
    | Sort _, _ -> -1 | _, Sort _ -> 1
    | Prod (_,t1,c1), Prod (_,t2,c2)
    | Lambda (_,t1,c1), Lambda (_,t2,c2) -> compare [(f,t1,t2); (f,c1,c2)]
    | Prod _, _ -> -1 | _, Prod _ -> 1
    | Lambda _, _ -> -1 | _, Lambda _ -> 1
    | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) -> compare [(f,b1,b2); (f,t1,t2); (f,c1,c2)]
    | LetIn _, _ -> -1 | _, LetIn _ -> 1
    | App (c1,l1), App (c2,l2) -> compare [(f,c1,c2); (Array.compare f, l1, l2)]
    | App _, _ -> -1 | _, App _ -> 1
    | Const (c1,_u1), Const (c2,_u2) -> Constant.UserOrd.compare c1 c2
    | Const _, _ -> -1 | _, Const _ -> 1
    | Ind (ind1, _u1), Ind (ind2, _u2) -> Ind.UserOrd.compare ind1 ind2
    | Ind _, _ -> -1 | _, Ind _ -> 1
    | Construct (ct1,_u1), Construct (ct2,_u2) -> Construct.UserOrd.compare ct1 ct2
    | Construct _, _ -> -1 | _, Construct _ -> 1
    | Case (_,_u1,pms1,(p1,_r1),iv1,c1,bl1), Case (_,_u2,pms2,(p2,_r2),iv2,c2,bl2) ->
      compare [
        (Array.compare f, pms1, pms2);
        (ctx_cmp f, p1, p2);
        (compare_invert f, iv1, iv2);
        (f, c1, c2);
        (Array.compare (ctx_cmp f), bl1, bl2);
      ]
    | Case _, _ -> -1 | _, Case _ -> 1
    | Fix (ln1,(_,tl1,bl1)), Fix (ln2,(_,tl2,bl2)) ->
      compare [(fix_cmp, ln1, ln2); (Array.compare f, tl1, tl2); (Array.compare f, bl1, bl2)]
    | Fix _, _ -> -1 | _, Fix _ -> 1
    | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
      compare [(Int.compare, ln1, ln2); (Array.compare f, tl1, tl2); (Array.compare f, bl1, bl2)]
    | CoFix _, _ -> -1 | _, CoFix _ -> 1
    | Proj (p1,_r1,c1), Proj (p2,_r2,c2) -> compare [(Projection.UserOrd.compare, p1, p2); (f, c1, c2)]
    | Proj _, _ -> -1 | _, Proj _ -> 1
    | Int i1, Int i2 -> Uint63.compare i1 i2
    | Int _, _ -> -1 | _, Int _ -> 1
    | Float f1, Float f2 -> Float64.total_compare f1 f2
    | Float _, _ -> -1 | _, Float _ -> 1
    | String s1, String s2 -> Pstring.compare s1 s2
    | String _, _ -> -1 | _, String _ -> 1
    | Array(_u1,t1,def1,ty1), Array(_u2,t2,def2,ty2) ->
      compare [(Array.compare f, t1, t2); (f, def1, def2); (f, ty1, ty2)]
    | Array _, _ -> -1 | _, Array _ -> 1
    | PBlock (_u1,ty1,entries1,t1), PBlock (_u2,ty2,entries2,t2) ->
      compare [(f, ty1, ty2); (Array.compare (entry_cmp f), entries1, entries2); (f, t1, t2)]
    | PBlock _, _ -> -1 | _, PBlock _ -> 1
    | PRun (ty1,k1,b1,cont1), PRun (ty2,k2,b2,cont2) ->
      compare [(f, ty1, ty2); (f, k1, k2); (f, b1, b2); (f, cont1, cont2)]

let rec compare m n =
  constr_ord_int compare m n

let equal m n = Int.equal (compare m n) 0

(* Exported hashing fonction on constr, used mainly in plugins. *)

open UVars
open Hashset.Combine

let rec hash t =
  match kind t with
    | Var i -> combinesmall 1 (Id.hash i)
    | Sort s -> combinesmall 2 (Sorts.hash s)
    | Cast (c, k, t) ->
      let hc = hash c in
      let ht = hash t in
      combinesmall 3 (combine3 hc (hash_cast_kind k) ht)
    | Prod (_, t, c) -> combinesmall 4 (combine (hash t) (hash c))
    | Lambda (_, t, c) -> combinesmall 5 (combine (hash t) (hash c))
    | LetIn (_, b, t, c) ->
      combinesmall 6 (combine3 (hash b) (hash t) (hash c))
    | App (c,l) -> begin match kind c with
        | Cast (c, _, _) -> hash (mkApp (c,l)) (* WTF *)
        | _ -> combinesmall 7 (combine (hash_term_array l) (hash c))
      end
    | Evar (e,l) ->
      combinesmall 8 (combine (Evar.hash e) (hash_term_list l))
    | Const (c,u) ->
      combinesmall 9 (combine (Constant.UserOrd.hash c) (Instance.hash u))
    | Ind (ind,u) ->
      combinesmall 10 (combine (Ind.UserOrd.hash ind) (Instance.hash u))
    | Construct (c,u) ->
      combinesmall 11 (combine (Construct.UserOrd.hash c) (Instance.hash u))
    | Case (_ , u, pms, (p,r), iv, c, bl) ->
      combinesmall 12 (combine5 (hash c) (hash_invert iv) (hash_term_array pms) (Instance.hash u)
                         (combine3 (hash_under_context p) (Sorts.relevance_hash r) (hash_branches bl)))
    | Fix (_ln ,(_, tl, bl)) ->
      combinesmall 13 (combine (hash_term_array bl) (hash_term_array tl))
    | CoFix(_ln, (_, tl, bl)) ->
       combinesmall 14 (combine (hash_term_array bl) (hash_term_array tl))
    | Meta n -> combinesmall 15 n
    | Rel n -> combinesmall 16 n
    | Proj (p,r, c) ->
      combinesmall 17 (combine3 (Projection.UserOrd.hash p) (Sorts.relevance_hash r) (hash c))
    | Int i -> combinesmall 18 (Uint63.hash i)
    | Float f -> combinesmall 19 (Float64.hash f)
    | String s -> combinesmall 20 (Pstring.hash s)
    | Array(u,t,def,ty) ->
      combinesmall 21 (combine4 (Instance.hash u) (hash_term_array t) (hash def) (hash ty))
    | PBlock (u,ty,entries,t) ->
      let hash_decl = function
        | RelDecl.LocalAssum (_, ty) -> combinesmall 1 (hash ty)
        | RelDecl.LocalDef (_, value, ty) -> combinesmall 2 (combine (hash value) (hash ty))
      in
      let hash_entry entry =
        let hctx = List.fold_right (fun decl acc -> combine (hash_decl decl) acc)
          entry.pbe_context 0
        in
        combine3 hctx (hash entry.pbe_type) (hash entry.pbe_value)
      in
      let hentries = Array.fold_left (fun acc entry -> combine acc (hash_entry entry)) 0 entries in
      combinesmall 22 (combine4 (Instance.hash u) (hash ty) hentries (hash t))
    | PRun (ty,k,b,cont) ->
      combinesmall 24 (combine4 (hash ty) (hash k) (hash b) (hash cont))

and hash_invert = function
  | NoInvert -> 0
  | CaseInvert {indices;} ->
    combinesmall 1 (hash_term_array indices)

and hash_term_array t =
  Array.fold_left (fun acc t -> combine acc (hash t)) 0 t

and hash_term_list t =
  SList.Skip.fold (fun acc t -> combine (hash t) acc) 0 t

and hash_under_context (_, t) = hash t

and hash_branches bl =
  Array.fold_left (fun acc t -> combine acc (hash_under_context t)) 0 bl

end

(* deprecated *)
let is_section_variable env id =
  try let _ = Environ.lookup_named id env in true
  with Not_found -> false
