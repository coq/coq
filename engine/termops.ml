(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
open Term
open Constr
open Vars
open Environ

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration
module CompactedDecl = Context.Compacted.Declaration

module Internal = struct

(* Sorts and sort family *)

let print_sort = function
  | Set -> (str "Set")
  | Prop -> (str "Prop")
  | Type u -> (str "Type(" ++ Univ.Universe.pr u ++ str ")")

let pr_sort_family = function
  | InSet -> (str "Set")
  | InProp -> (str "Prop")
  | InType -> (str "Type")

let pr_con sp = str(Constant.to_string sp)

let pr_fix pr_constr ((t,i),(lna,tl,bl)) =
  let fixl = Array.mapi (fun i na -> (na,t.(i),tl.(i),bl.(i))) lna in
  hov 1
      (str"fix " ++ int i ++ spc() ++  str"{" ++
         v 0 (prlist_with_sep spc (fun (na,i,ty,bd) ->
           Name.print na ++ str"/" ++ int i ++ str":" ++ pr_constr ty ++
	   cut() ++ str":=" ++ pr_constr bd) (Array.to_list fixl)) ++
         str"}")

let pr_puniverses p u = 
  if Univ.Instance.is_empty u then p 
  else p ++ str"(*" ++ Univ.Instance.pr UnivNames.pr_with_global_universes u ++ str"*)"

(* Minimalistic constr printer, typically for debugging *)

let rec pr_constr c = match kind c with
  | Rel n -> str "#"++int n
  | Meta n -> str "Meta(" ++ int n ++ str ")"
  | Var id -> Id.print id
  | Sort s -> print_sort s
  | Cast (c,_, t) -> hov 1
      (str"(" ++ pr_constr c ++ cut() ++
       str":" ++ pr_constr t ++ str")")
  | Prod (Name(id),t,c) -> hov 1
      (str"forall " ++ Id.print id ++ str":" ++ pr_constr t ++ str"," ++
       spc() ++ pr_constr c)
  | Prod (Anonymous,t,c) -> hov 0
      (str"(" ++ pr_constr t ++ str " ->" ++ spc() ++
       pr_constr c ++ str")")
  | Lambda (na,t,c) -> hov 1
      (str"fun " ++ Name.print na ++ str":" ++
       pr_constr t ++ str" =>" ++ spc() ++ pr_constr c)
  | LetIn (na,b,t,c) -> hov 0
      (str"let " ++ Name.print na ++ str":=" ++ pr_constr b ++
       str":" ++ brk(1,2) ++ pr_constr t ++ cut() ++
       pr_constr c)
  | App (c,l) ->  hov 1
      (str"(" ++ pr_constr c ++ spc() ++
       prlist_with_sep spc pr_constr (Array.to_list l) ++ str")")
  | Evar (e,l) -> hov 1
      (str"Evar#" ++ int (Evar.repr e) ++ str"{" ++
       prlist_with_sep spc pr_constr (Array.to_list l) ++str"}")
  | Const (c,u) -> str"Cst(" ++ pr_puniverses (pr_con c) u ++ str")"
  | Ind ((sp,i),u) -> str"Ind(" ++ pr_puniverses (MutInd.print sp ++ str"," ++ int i) u ++ str")"
  | Construct (((sp,i),j),u) ->
      str"Constr(" ++ pr_puniverses (MutInd.print sp ++ str"," ++ int i ++ str"," ++ int j) u ++ str")"
  | Proj (p,c) -> str"Proj(" ++ pr_con (Projection.constant p) ++ str"," ++ bool (Projection.unfolded p) ++ pr_constr c ++ str")"
  | Case (ci,p,c,bl) -> v 0
      (hv 0 (str"<"++pr_constr p++str">"++ cut() ++ str"Case " ++
             pr_constr c ++ str"of") ++ cut() ++
       prlist_with_sep (fun _ -> brk(1,2)) pr_constr (Array.to_list bl) ++
      cut() ++ str"end")
  | Fix f -> pr_fix pr_constr f
  | CoFix(i,(lna,tl,bl)) ->
      let fixl = Array.mapi (fun i na -> (na,tl.(i),bl.(i))) lna in
      hov 1
        (str"cofix " ++ int i ++ spc() ++  str"{" ++
         v 0 (prlist_with_sep spc (fun (na,ty,bd) ->
           Name.print na ++ str":" ++ pr_constr ty ++
           cut() ++ str":=" ++ pr_constr bd) (Array.to_list fixl)) ++
         str"}")

let debug_print_constr c = pr_constr EConstr.Unsafe.(to_constr c)
let debug_print_constr_env env sigma c = pr_constr EConstr.(to_constr sigma c)
let term_printer = ref debug_print_constr_env

let print_constr_env env sigma t = !term_printer env sigma t
let print_constr t =
  let env = Global.env () in
  let evd = Evd.from_env env in
  !term_printer env evd t

let set_print_constr f = term_printer := f

module EvMap = Evar.Map

let pr_evar_suggested_name evk sigma =
  let open Evd in
  let base_id evk' evi =
  match evar_ident evk' sigma with
  | Some id -> id
  | None -> match evi.evar_source with
  | _,Evar_kinds.ImplicitArg (c,(n,Some id),b) -> id
  | _,Evar_kinds.VarInstance id -> id
  | _,Evar_kinds.QuestionMark {Evar_kinds.qm_name = Name id} -> id
  | _,Evar_kinds.GoalEvar -> Id.of_string "Goal"
  | _ ->
      let env = reset_with_named_context evi.evar_hyps (Global.env()) in
      Namegen.id_of_name_using_hdchar env sigma evi.evar_concl Anonymous
  in
  let names = EvMap.mapi base_id (undefined_map sigma) in
  let id = EvMap.find evk names in
  let fold evk' id' (seen, n) =
    if seen then (seen, n)
    else if Evar.equal evk evk' then (true, n)
    else if Id.equal id id' then (seen, succ n)
    else (seen, n)
  in
  let (_, n) = EvMap.fold fold names (false, 0) in
  if n = 0 then id else Nameops.add_suffix id (string_of_int (pred n))

let pr_existential_key sigma evk =
let open Evd in
match evar_ident evk sigma with
| None ->
  str "?" ++ Id.print (pr_evar_suggested_name evk sigma)
| Some id ->
  str "?" ++ Id.print id

let pr_instance_status (sc,typ) =
  let open Evd in
  begin match sc with
  | IsSubType -> str " [or a subtype of it]"
  | IsSuperType -> str " [or a supertype of it]"
  | Conv -> mt ()
  end ++
  begin match typ with
  | CoerceToType -> str " [up to coercion]"
  | TypeNotProcessed -> mt ()
  | TypeProcessed -> str " [type is checked]"
  end

let protect f x =
  try f x
  with e -> str "EXCEPTION: " ++ str (Printexc.to_string e)

let print_kconstr a =
  protect (fun c -> print_constr c) a

let pr_meta_map evd =
  let open Evd in
  let print_constr = print_kconstr in
  let pr_name = function
      Name id -> str"[" ++ Id.print id ++ str"]"
    | _ -> mt() in
  let pr_meta_binding = function
    | (mv,Cltyp (na,b)) ->
      	hov 0
	  (pr_meta mv ++ pr_name na ++ str " : " ++
           print_constr b.rebus ++ fnl ())
    | (mv,Clval(na,(b,s),t)) ->
      	hov 0
	  (pr_meta mv ++ pr_name na ++ str " := " ++
           print_constr b.rebus ++
	   str " : " ++ print_constr t.rebus ++
	   spc () ++ pr_instance_status s ++ fnl ())
  in
  prlist pr_meta_binding (meta_list evd)

let pr_decl (decl,ok) =
  let open NamedDecl in
  let print_constr = print_kconstr in
  match decl with
  | LocalAssum (id,_) -> if ok then Id.print id else (str "{" ++ Id.print id ++ str "}")
  | LocalDef (id,c,_) -> str (if ok then "(" else "{") ++ Id.print id ++ str ":=" ++
                           print_constr c ++ str (if ok then ")" else "}")

let pr_evar_source = function
  | Evar_kinds.NamedHole id -> Id.print id
  | Evar_kinds.QuestionMark _ -> str "underscore"
  | Evar_kinds.CasesType false -> str "pattern-matching return predicate"
  | Evar_kinds.CasesType true ->
      str "subterm of pattern-matching return predicate"
  | Evar_kinds.BinderType (Name id) -> str "type of " ++ Id.print id
  | Evar_kinds.BinderType Anonymous -> str "type of anonymous binder"
  | Evar_kinds.ImplicitArg (c,(n,ido),b) ->
      let open Globnames in
      let print_constr = print_kconstr in
      let id = Option.get ido in
      str "parameter " ++ Id.print id ++ spc () ++ str "of" ++
      spc () ++ print_constr (EConstr.of_constr @@ printable_constr_of_global c)
  | Evar_kinds.InternalHole -> str "internal placeholder"
  | Evar_kinds.TomatchTypeParameter (ind,n) ->
      let print_constr = print_kconstr in
      pr_nth n ++ str " argument of type " ++ print_constr (EConstr.mkInd ind)
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

let pr_evar_info evi =
  let open Evd in
  let print_constr = print_kconstr in
  let phyps =
    try
      let decls = match Filter.repr (evar_filter evi) with
      | None -> List.map (fun c -> (c, true)) (evar_context evi)
      | Some filter -> List.combine (evar_context evi) filter
      in
      prlist_with_sep spc pr_decl (List.rev decls)
    with Invalid_argument _ -> str "Ill-formed filtered context" in
  let pty = print_constr evi.evar_concl in
  let pb =
    match evi.evar_body with
      | Evar_empty -> mt ()
      | Evar_defined c -> spc() ++ str"=> "  ++ print_constr c
  in
  let candidates =
    match evi.evar_body, evi.evar_candidates with
      | Evar_empty, Some l ->
           spc () ++ str "{" ++
           prlist_with_sep (fun () -> str "|") print_constr l ++ str "}"
      | _ ->
          mt ()
  in
  let src = str "(" ++ pr_evar_source (snd evi.evar_source) ++ str ")" in
  hov 2
    (str"["  ++ phyps ++ spc () ++ str"|- "  ++ pty ++ pb ++ str"]" ++
       candidates ++ spc() ++ src)

let compute_evar_dependency_graph sigma =
  let open Evd in
  (* Compute the map binding ev to the evars whose body depends on ev *)
  let fold evk evi acc =
    let fold_ev evk' acc =
      let tab =
        try EvMap.find evk' acc
        with Not_found -> Evar.Set.empty
      in
      EvMap.add evk' (Evar.Set.add evk tab) acc
    in
    match evar_body evi with
    | Evar_empty -> acc
    | Evar_defined c -> Evar.Set.fold fold_ev (evars_of_term (EConstr.Unsafe.to_constr c)) acc
  in
  Evd.fold fold sigma EvMap.empty

let evar_dependency_closure n sigma =
  let open Evd in
  (** Create the DAG of depth [n] representing the recursive dependencies of
      undefined evars. *)
  let graph = compute_evar_dependency_graph sigma in
  let rec aux n curr accu =
    if Int.equal n 0 then Evar.Set.union curr accu
    else
      let fold evk accu =
        try
          let deps = EvMap.find evk graph in
          Evar.Set.union deps accu
        with Not_found -> accu
      in
      (** Consider only the newly added evars *)
      let ncurr = Evar.Set.fold fold curr Evar.Set.empty in
      (** Merge the others *)
      let accu = Evar.Set.union curr accu in
      aux (n - 1) ncurr accu
  in
  let undef = EvMap.domain (undefined_map sigma) in
  aux n undef Evar.Set.empty

let evar_dependency_closure n sigma =
  let open Evd in
  let deps = evar_dependency_closure n sigma in
  let map = EvMap.bind (fun ev -> find sigma ev) deps in
  EvMap.bindings map

let has_no_evar sigma =
  try let () = Evd.fold (fun _ _ () -> raise Exit) sigma () in true
  with Exit -> false

let pr_evd_level evd = UState.pr_uctx_level (Evd.evar_universe_context evd)
let reference_of_level evd l = UState.qualid_of_level (Evd.evar_universe_context evd) l

let pr_evar_universe_context ctx =
  let open UState in
  let prl = pr_uctx_level ctx in
  if UState.is_empty ctx then mt ()
  else
    (str"UNIVERSES:"++brk(0,1)++ 
       h 0 (Univ.pr_universe_context_set prl (UState.context_set ctx)) ++ fnl () ++
     str"ALGEBRAIC UNIVERSES:"++brk(0,1)++
     h 0 (Univ.LSet.pr prl (UState.algebraics ctx)) ++ fnl() ++
     str"UNDEFINED UNIVERSES:"++brk(0,1)++
     h 0 (UnivSubst.pr_universe_opt_subst (UState.subst ctx)) ++ fnl() ++
     str "WEAK CONSTRAINTS:"++brk(0,1)++
     h 0 (UState.pr_weak prl ctx) ++ fnl ())

let print_env_short env =
  let print_constr = print_kconstr in
  let pr_rel_decl = function
    | RelDecl.LocalAssum (n,_) -> Name.print n
    | RelDecl.LocalDef (n,b,_) -> str "(" ++ Name.print n ++ str " := "
                                  ++ print_constr (EConstr.of_constr b) ++ str ")"
  in
  let pr_named_decl = NamedDecl.to_rel_decl %> pr_rel_decl in
  let nc = List.rev (named_context env) in
  let rc = List.rev (rel_context env) in
    str "[" ++ pr_sequence pr_named_decl nc ++ str "]" ++ spc () ++
    str "[" ++ pr_sequence pr_rel_decl rc ++ str "]"

let pr_evar_constraints sigma pbs =
  let pr_evconstr (pbty, env, t1, t2) =
    let env =
      (** We currently allow evar instances to refer to anonymous de
          Bruijn indices, so we protect the error printing code in this
          case by giving names to every de Bruijn variable in the
          rel_context of the conversion problem. MS: we should rather
          stop depending on anonymous variables, they can be used to
          indicate independency. Also, this depends on a strategy for
          naming/renaming. *)
      Namegen.make_all_name_different env sigma
    in
    print_env_short env ++ spc () ++ str "|-" ++ spc () ++
      protect (print_constr_env env sigma) t1 ++ spc () ++
      str (match pbty with
            | Reduction.CONV -> "=="
            | Reduction.CUMUL -> "<=") ++
      spc () ++ protect (print_constr_env env @@ Evd.from_env env) t2
  in
  prlist_with_sep fnl pr_evconstr pbs

let pr_evar_map_gen with_univs pr_evars sigma =
  let uvs = Evd.evar_universe_context sigma in
  let (_, conv_pbs) = Evd.extract_all_conv_pbs sigma in
  let evs = if has_no_evar sigma then mt () else pr_evars sigma ++ fnl ()
  and svs = if with_univs then pr_evar_universe_context uvs else mt ()
  and cstrs =
    if List.is_empty conv_pbs then mt ()
    else
    str "CONSTRAINTS:" ++ brk (0, 1) ++
      pr_evar_constraints sigma conv_pbs ++ fnl ()
  and metas =
    if List.is_empty (Evd.meta_list sigma) then mt ()
    else
      str "METAS:" ++ brk (0, 1) ++ pr_meta_map sigma
  in
  evs ++ svs ++ cstrs ++ metas

let pr_evar_list sigma l =
  let open Evd in
  let pr (ev, evi) =
    h 0 (Evar.print ev ++
      str "==" ++ pr_evar_info evi ++
      (if evi.evar_body == Evar_empty
       then str " {" ++ pr_existential_key sigma ev ++ str "}"
       else mt ()))
  in
  h 0 (prlist_with_sep fnl pr l)

let to_list d =
  let open Evd in
  (* Workaround for change in Map.fold behavior in ocaml 3.08.4 *)
  let l = ref [] in
  let fold_def evk evi () = match evi.evar_body with
    | Evar_defined _ -> l := (evk, evi) :: !l
    | Evar_empty -> ()
  in
  let fold_undef evk evi () = match evi.evar_body with
    | Evar_empty -> l := (evk, evi) :: !l
    | Evar_defined _ -> ()
  in
  Evd.fold fold_def d ();
  Evd.fold fold_undef d ();
  !l

let pr_evar_by_depth depth sigma = match depth with
| None ->
  (* Print all evars *)
  str"EVARS:" ++ brk(0,1) ++ pr_evar_list sigma (to_list sigma) ++ fnl()
| Some n ->
  (* Print closure of undefined evars *)
  str"UNDEFINED EVARS:"++
  (if Int.equal n 0 then mt() else str" (+level "++int n++str" closure):")++
  brk(0,1)++
  pr_evar_list sigma (evar_dependency_closure n sigma) ++ fnl()

let pr_evar_by_filter filter sigma =
  let open Evd in
  let elts = Evd.fold (fun evk evi accu -> (evk, evi) :: accu) sigma [] in
  let elts = List.rev elts in
  let is_def (_, evi) = match evi.evar_body with
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
      pr_evar_list sigma defined
  in
  let prundef =
    if List.is_empty undefined then mt ()
    else str "UNDEFINED EVARS:" ++ brk (0, 1) ++
      pr_evar_list sigma undefined
  in
  prdef ++ prundef

let pr_evar_map ?(with_univs=true) depth sigma =
  pr_evar_map_gen with_univs (fun sigma -> pr_evar_by_depth depth sigma) sigma

let pr_evar_map_filter ?(with_univs=true) filter sigma =
  pr_evar_map_gen with_univs (fun sigma -> pr_evar_by_filter filter sigma) sigma

let pr_metaset metas =
  str "[" ++ pr_sequence pr_meta (Evd.Metaset.elements metas) ++ str "]"

let pr_var_decl env decl =
  let open NamedDecl in
  let evd = Evd.from_env env in
  let pbody = match decl with
    | LocalAssum _ ->  mt ()
    | LocalDef (_,c,_) ->
	(* Force evaluation *)
	let c = EConstr.of_constr c in
        let pb = print_constr_env env evd c in
	  (str" := " ++ pb ++ cut () ) in
  let pt = print_constr_env env evd (EConstr.of_constr (get_type decl)) in
  let ptyp = (str" : " ++ pt) in
    (Id.print (get_id decl) ++ hov 0 (pbody ++ ptyp))

let pr_rel_decl env decl =
  let open RelDecl in
  let evd = Evd.from_env env in
  let pbody = match decl with
    | LocalAssum _ -> mt ()
    | LocalDef (_,c,_) ->
	(* Force evaluation *)
	let c = EConstr.of_constr c in
        let pb = print_constr_env env evd c in
	  (str":=" ++ spc () ++ pb ++ spc ()) in
  let ptyp = print_constr_env env evd (EConstr.of_constr (get_type decl)) in
    match get_name decl with
      | Anonymous -> hov 0 (str"<>" ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)
      | Name id -> hov 0 (Id.print id ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)

let print_named_context env =
  hv 0 (fold_named_context
	  (fun env d pps ->
	    pps ++ ws 2 ++ pr_var_decl env d)
          env ~init:(mt ()))

let print_rel_context env =
  hv 0 (fold_rel_context
	  (fun env d pps -> pps ++ ws 2 ++ pr_rel_decl env d)
          env ~init:(mt ()))

let print_env env =
  let sign_env =
    fold_named_context
      (fun env d pps ->
         let pidt =  pr_var_decl env d in
	 (pps ++ fnl () ++ pidt))
      env ~init:(mt ())
  in
  let db_env =
    fold_rel_context
      (fun env d pps ->
         let pnat = pr_rel_decl env d in (pps ++ fnl () ++ pnat))
      env ~init:(mt ())
  in
    (sign_env ++ db_env)

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

let push_named_rec_types (lna,typarray,_) env =
  let open NamedDecl in
  let ctxt =
    Array.map2_i
      (fun i na t ->
	 match na with
	   | Name id -> LocalAssum (id, lift i t)
	   | Anonymous -> anomaly (Pp.str "Fix declarations must be named."))
      lna typarray in
  Array.fold_left
    (fun e assum -> push_named assum e) env ctxt

let lookup_rel_id id sign =
  let open RelDecl in
  let rec lookrec n = function
    | [] ->
        raise Not_found
    | (LocalAssum (Anonymous, _) | LocalDef (Anonymous,_,_)) :: l ->
        lookrec (n + 1) l
    | LocalAssum (Name id', t) :: l  ->
        if Names.Id.equal id' id then (n,None,t)  else lookrec (n + 1) l
    | LocalDef (Name id', b, t) :: l  ->
        if Names.Id.equal id' id then (n,Some b,t) else lookrec (n + 1) l
  in
  lookrec 1 sign

(* Constructs either [forall x:t, c] or [let x:=b:t in c] *)
let mkProd_or_LetIn = EConstr.mkProd_or_LetIn
(* Constructs either [forall x:t, c] or [c] in which [x] is replaced by [b] *)
let mkProd_wo_LetIn decl c =
  let open EConstr in
  let open RelDecl in
  match decl with
    | LocalAssum (na,t) -> mkProd (na, t, c)
    | LocalDef (_,b,_) -> Vars.subst1 b c

let it_mkProd init = List.fold_left (fun c (n,t)  -> EConstr.mkProd (n, t, c)) init
let it_mkLambda init = List.fold_left (fun c (n,t)  -> EConstr.mkLambda (n, t, c)) init

let it_named_context_quantifier f ~init =
  List.fold_left (fun c d -> f d c) init

let it_mkProd_or_LetIn init = it_named_context_quantifier mkProd_or_LetIn ~init
let it_mkProd_wo_LetIn init = it_named_context_quantifier mkProd_wo_LetIn ~init
let it_mkLambda_or_LetIn init = it_named_context_quantifier mkLambda_or_LetIn ~init
let it_mkNamedProd_or_LetIn init = it_named_context_quantifier EConstr.mkNamedProd_or_LetIn ~init
let it_mkNamedProd_wo_LetIn init = it_named_context_quantifier mkNamedProd_wo_LetIn ~init
let it_mkNamedLambda_or_LetIn init = it_named_context_quantifier EConstr.mkNamedLambda_or_LetIn ~init

let it_mkLambda_or_LetIn_from_no_LetIn c decls =
  let open RelDecl in
  let rec aux k decls c = match decls with
  | [] -> c
  | LocalDef (na,b,t) :: decls -> mkLetIn (na,b,t,aux (k-1) decls (liftn 1 k c))
  | LocalAssum (na,t) :: decls -> mkLambda (na,t,aux (k-1) decls c)
  in aux (List.length decls) (List.rev decls) c

(* *)

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

(* Get the last arg of an application *)
let last_arg sigma c = match EConstr.kind sigma c with
  | App (f,cl) -> Array.last cl
  | _ -> anomaly (Pp.str "last_arg.")

(* Get the last arg of an application *)
let decompose_app_vect sigma c =
  match EConstr.kind sigma c with
  | App (f,cl) -> (f, cl)
  | _ -> (c,[||])

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

let map_constr_with_binders_left_to_right sigma g f l c =
  let open RelDecl in
  let open EConstr in
  match EConstr.kind sigma c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> c
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
  | Proj (p,b) ->
    let b' = f l b in
      if b' == b then c
      else mkProj (p, b')
  | Evar (e,al) -> 
    let al' = Array.map_left (f l) al in
      if Array.for_all2 (==) al' al then c
      else mkEvar (e, al')
  | Case (ci,p,b,bl) ->
      (* In v8 concrete syntax, predicate is after the term to match! *)
      let b' = f l b in
      let p' = f l p in
      let bl' = Array.map_left (f l) bl in
	if b' == b && p' == p && bl' == bl then c
	else mkCase (ci, p', b', bl')
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

(* strong *)
let map_constr_with_full_binders sigma g f l cstr =
  let open EConstr in
  let open RelDecl in
  match EConstr.kind sigma cstr with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> cstr
  | Cast (c,k, t) ->
      let c' = f l c in
      let t' = f l t in
      if c==c' && t==t' then cstr else mkCast (c', k, t')
  | Prod (na,t,c) ->
      let t' = f l t in
      let c' = f (g (LocalAssum (na, t)) l) c in
      if t==t' && c==c' then cstr else mkProd (na, t', c')
  | Lambda (na,t,c) ->
      let t' = f l t in
      let c' = f (g (LocalAssum (na, t)) l) c in
      if t==t' && c==c' then cstr else  mkLambda (na, t', c')
  | LetIn (na,b,t,c) ->
      let b' = f l b in
      let t' = f l t in
      let c' = f (g (LocalDef (na, b, t)) l) c in
      if b==b' && t==t' && c==c' then cstr else mkLetIn (na, b', t', c')
  | App (c,al) ->
      let c' = f l c in
      let al' = Array.map (f l) al in
      if c==c' && Array.for_all2 (==) al al' then cstr else mkApp (c', al')
  | Proj (p,c) -> 
      let c' = f l c in
	if c' == c then cstr else mkProj (p, c')
  | Evar (e,al) ->
      let al' = Array.map (f l) al in
      if Array.for_all2 (==) al al' then cstr else mkEvar (e, al')
  | Case (ci,p,c,bl) ->
      let p' = f l p in
      let c' = f l c in
      let bl' = Array.map (f l) bl in
      if p==p' && c==c' && Array.for_all2 (==) bl bl' then cstr else
        mkCase (ci, p', c', bl')
  | Fix (ln,(lna,tl,bl)) ->
      let tl' = Array.map (f l) tl in
      let l' =
        Array.fold_left2 (fun l na t -> g (LocalAssum (na, t)) l) l lna tl in
      let bl' = Array.map (f l') bl in
      if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl'
      then cstr
      else mkFix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl)) ->
      let tl' = Array.map (f l) tl in
      let l' =
        Array.fold_left2 (fun l na t -> g (LocalAssum (na, t)) l) l lna tl in
      let bl' = Array.map (f l') bl in
      if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl'
      then cstr
      else mkCoFix (ln,(lna,tl',bl'))

(* [fold_constr_with_binders g f n acc c] folds [f n] on the immediate
   subterms of [c] starting from [acc] and proceeding from left to
   right according to the usual representation of the constructions as
   [fold_constr] but it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive *)

let fold_constr_with_full_binders sigma g f n acc c =
  let open RelDecl in
  match EConstr.kind sigma c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> acc
  | Cast (c,_, t) -> f n (f n acc c) t
  | Prod (na,t,c) -> f (g (LocalAssum (na, t)) n) (f n acc t) c
  | Lambda (na,t,c) -> f (g (LocalAssum (na, t)) n) (f n acc t) c
  | LetIn (na,b,t,c) -> f (g (LocalDef (na, b, t)) n) (f n (f n acc b) t) c
  | App (c,l) -> Array.fold_left (f n) (f n acc c) l
  | Proj (p,c) -> f n acc c
  | Evar (_,l) -> Array.fold_left (f n) acc l
  | Case (_,p,c,bl) -> Array.fold_left (f n) (f n (f n acc p) c) bl
  | Fix (_,(lna,tl,bl)) ->
      let n' = CArray.fold_left2 (fun c n t -> g (LocalAssum (n, t)) c) n lna tl in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
  | CoFix (_,(lna,tl,bl)) ->
      let n' = CArray.fold_left2 (fun c n t -> g (LocalAssum (n, t)) c) n lna tl in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd

let fold_constr_with_binders sigma g f n acc c =
  fold_constr_with_full_binders sigma (fun _ x -> g x) f n acc c

(* [iter_constr_with_full_binders g f acc c] iters [f acc] on the immediate
   subterms of [c]; it carries an extra data [acc] which is processed by [g] at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let iter_constr_with_full_binders sigma g f l c =
  let open RelDecl in
  match EConstr.kind sigma c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> ()
  | Cast (c,_, t) -> f l c; f l t
  | Prod (na,t,c) -> f l t; f (g (LocalAssum (na,t)) l) c
  | Lambda (na,t,c) -> f l t; f (g (LocalAssum (na,t)) l) c
  | LetIn (na,b,t,c) -> f l b; f l t; f (g (LocalDef (na,b,t)) l) c
  | App (c,args) -> f l c; Array.iter (f l) args
  | Proj (p,c) -> f l c
  | Evar (_,args) -> Array.iter (f l) args
  | Case (_,p,c,bl) -> f l p; f l c; Array.iter (f l) bl
  | Fix (_,(lna,tl,bl)) ->
      let l' = Array.fold_left2 (fun l na t -> g (LocalAssum (na,t)) l) l lna tl in
      Array.iter (f l) tl;
      Array.iter (f l') bl
  | CoFix (_,(lna,tl,bl)) ->
      let l' = Array.fold_left2 (fun l na t -> g (LocalAssum (na,t)) l) l lna tl in
      Array.iter (f l) tl;
      Array.iter (f l') bl

(***************************)
(* occurs check functions  *)
(***************************)

exception Occur

let occur_meta sigma c =
  let rec occrec c = match EConstr.kind sigma c with
    | Meta _ -> raise Occur
    | _ -> EConstr.iter sigma occrec c
  in try occrec c; false with Occur -> true

let occur_existential sigma c =
  let rec occrec c = match EConstr.kind sigma c with
    | Evar _ -> raise Occur
    | _ -> EConstr.iter sigma occrec c
  in try occrec c; false with Occur -> true

let occur_meta_or_existential sigma c =
  let rec occrec c = match EConstr.kind sigma c with
    | Evar _ -> raise Occur
    | Meta _ -> raise Occur
    | _ -> EConstr.iter sigma occrec c
  in try occrec c; false with Occur -> true

let occur_metavariable sigma m c =
  let rec occrec c = match EConstr.kind sigma c with
  | Meta m' -> if Int.equal m m' then raise Occur
  | _ -> EConstr.iter sigma occrec c
  in
  try occrec c; false with Occur -> true

let occur_evar sigma n c =
  let rec occur_rec c = match EConstr.kind sigma c with
    | Evar (sp,_) when Evar.equal sp n -> raise Occur
    | _ -> EConstr.iter sigma occur_rec c
  in
  try occur_rec c; false with Occur -> true

let occur_in_global env id constr =
  let vars = vars_of_global env constr in
  if Id.Set.mem id vars then raise Occur

let occur_var env sigma id c =
  let rec occur_rec c =
    match EConstr.kind sigma c with
    | Var _ | Const _ | Ind _ | Construct _ -> occur_in_global env id (EConstr.to_constr sigma c)
    | _ -> EConstr.iter sigma occur_rec c
  in
  try occur_rec c; false with Occur -> true

let occur_var_in_decl env sigma hyp decl =
  let open NamedDecl in
  match decl with
    | LocalAssum (_,typ) -> occur_var env sigma hyp typ
    | LocalDef (_, body, typ) ->
        occur_var env sigma hyp typ ||
        occur_var env sigma hyp body

let local_occur_var sigma id c =
  let rec occur c = match EConstr.kind sigma c with
  | Var id' -> if Id.equal id id' then raise Occur
  | _ -> EConstr.iter sigma occur c
  in
  try occur c; false with Occur -> true

  (* returns the list of free debruijn indices in a term *)

let free_rels sigma m =
  let rec frec depth acc c = match EConstr.kind sigma c with
    | Rel n       -> if n >= depth then Int.Set.add (n-depth+1) acc else acc
    | _ -> fold_constr_with_binders sigma succ frec depth acc c
  in
  frec 1 Int.Set.empty m

(* collects all metavar occurrences, in left-to-right order, preserving
 * repetitions and all. *)

let collect_metas sigma c =
  let rec collrec acc c =
    match EConstr.kind sigma c with
      | Meta mv -> List.add_set Int.equal mv acc
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

let vars_of_global_reference env gr =
  let c, _ = Global.constr_of_global_in_context env gr in
  vars_of_global (Global.env ()) c

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
  let open NamedDecl in
  match decl with
    | LocalAssum (_,t) -> dependent sigma a t
    | LocalDef (_, body, t) -> dependent sigma a body || dependent sigma a t

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

(* flattens application lists throwing casts in-between *)
let collapse_appl sigma c = match EConstr.kind sigma c with
  | App (f,cl) ->
    if EConstr.isCast sigma f then
      let rec collapse_rec f cl2 =
        match EConstr.kind sigma (strip_outer_cast sigma f) with
        | App (g,cl1) -> collapse_rec g (Array.append cl1 cl2)
        | _ -> EConstr.mkApp (f,cl2)
      in
      collapse_rec f cl
    else c
  | _ -> c

(* First utilities for avoiding telescope computation for subst_term *)

let prefix_application sigma eq_fun (k,c) t =
  let open EConstr in
  let c' = collapse_appl sigma c and t' = collapse_appl sigma t in
  match EConstr.kind sigma c', EConstr.kind sigma t' with
    | App (f1,cl1), App (f2,cl2) ->
	let l1 = Array.length cl1
	and l2 = Array.length cl2 in
	if l1 <= l2
	   && eq_fun sigma c' (mkApp (f2, Array.sub cl2 0 l1)) then
	  Some (mkApp (mkRel k, Array.sub cl2 l1 (l2 - l1)))
	else
	  None
    | _ -> None

let my_prefix_application sigma eq_fun (k,c) by_c t =
  let open EConstr in
  let c' = collapse_appl sigma c and t' = collapse_appl sigma t in
  match EConstr.kind sigma c', EConstr.kind sigma t' with
    | App (f1,cl1), App (f2,cl2) ->
	let l1 = Array.length cl1
	and l2 = Array.length cl2 in
	if l1 <= l2
	   && eq_fun sigma c' (mkApp (f2, Array.sub cl2 0 l1)) then
	  Some (mkApp ((Vars.lift k by_c), Array.sub cl2 l1 (l2 - l1)))
	else
	  None
    | _ -> None

(* Recognizing occurrences of a given subterm in a term: [subst_term c t]
   substitutes [(Rel 1)] for all occurrences of term [c] in a term [t];
   works if [c] has rels *)

let subst_term_gen sigma eq_fun c t =
  let open EConstr in
  let open Vars in
  let rec substrec (k,c as kc) t =
    match prefix_application sigma eq_fun kc t with
      | Some x -> x
      | None ->
    if eq_fun sigma c t then mkRel k
    else
      EConstr.map_with_binders sigma (fun (k,c) -> (k+1,lift 1 c)) substrec kc t
  in
  substrec (1,c) t

let subst_term sigma c t = subst_term_gen sigma EConstr.eq_constr c t

(* Recognizing occurrences of a given subterm in a term :
   [replace_term c1 c2 t] substitutes [c2] for all occurrences of
   term [c1] in a term [t]; works if [c1] and [c2] have rels *)

let replace_term_gen sigma eq_fun c by_c in_t =
  let rec substrec (k,c as kc) t =
    match my_prefix_application sigma eq_fun kc by_c t with
      | Some x -> x
      | None ->
    (if eq_fun sigma c t then (EConstr.Vars.lift k by_c) else
      EConstr.map_with_binders sigma (fun (k,c) -> (k+1,EConstr.Vars.lift 1 c))
	substrec kc t)
  in
  substrec (0,c) in_t

let replace_term sigma c byc t = replace_term_gen sigma EConstr.eq_constr c byc t

let vars_of_env env =
  let s = Environ.ids_of_named_context_val (Environ.named_context_val env) in
  if List.is_empty (Environ.rel_context env) then s
  else
  Context.Rel.fold_outside
    (fun decl s -> match RelDecl.get_name decl with Name id -> Id.Set.add id s | _ -> s)
    (rel_context env) ~init:s

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

let is_section_variable id =
  try let _ = Global.lookup_named id in true
  with Not_found -> false

let global_of_constr sigma c =
  let open Globnames in
  match EConstr.kind sigma c with
  | Const (c, u) -> ConstRef c, u
  | Ind (i, u) -> IndRef i, u
  | Construct (c, u) -> ConstructRef c, u
  | Var id -> VarRef id, EConstr.EInstance.empty
  | _ -> raise Not_found

let is_global sigma c t =
  let open Globnames in
  match c, EConstr.kind sigma t with
  | ConstRef c, Const (c', _) -> Constant.equal c c'
  | IndRef i, Ind (i', _) -> eq_ind i i'
  | ConstructRef i, Construct (i', _) -> eq_constructor i i'
  | VarRef id, Var id' -> Id.equal id id'
  | _ -> false

let isGlobalRef sigma c =
  match EConstr.kind sigma c with
  | Const _ | Ind _ | Construct _ | Var _ -> true
  | _ -> false

let is_template_polymorphic env sigma f =
  match EConstr.kind sigma f with
  | Ind (ind, u) ->
    if not (EConstr.EInstance.is_empty u) then false
    else Environ.template_polymorphic_ind ind env
  | _ -> false

let base_sort_cmp pb s0 s1 =
  match (s0,s1) with
  | Prop, Prop | Set, Set | Type _, Type _ -> true
  | Prop, Set | Prop, Type _ | Set, Type _ -> pb == Reduction.CUMUL
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
let compare_constr_univ sigma f cv_pb t1 t2 =
  let open EConstr in
  match EConstr.kind sigma t1, EConstr.kind sigma t2 with
      Sort s1, Sort s2 -> base_sort_cmp cv_pb (ESorts.kind sigma s1) (ESorts.kind sigma s2)
    | Prod (_,t1,c1), Prod (_,t2,c2) ->
	f Reduction.CONV t1 t2 && f cv_pb c1 c2
    | Const (c, u), Const (c', u') -> Constant.equal c c'
    | Ind (i, _), Ind (i', _) -> eq_ind i i'
    | Construct (i, _), Construct (i', _) -> eq_constructor i i'
    | _ -> EConstr.compare_constr sigma (fun t1 t2 -> f Reduction.CONV t1 t2) t1 t2

let constr_cmp sigma cv_pb t1 t2 =
  let rec compare cv_pb t1 t2 = compare_constr_univ sigma compare cv_pb t1 t2 in
  compare cv_pb t1 t2

let eq_constr sigma t1 t2 = constr_cmp sigma Reduction.CONV t1 t2

(* App(c,[t1,...tn]) -> ([c,t1,...,tn-1],tn)
   App(c,[||]) -> ([],c) *)
let split_app sigma c = match EConstr.kind sigma c with
    App(c,l) ->
      let len = Array.length l in
      if Int.equal len 0 then ([],c) else
	let last = Array.get l (len-1) in
	let prev = Array.sub l 0 (len-1) in
	c::(Array.to_list prev), last
  | _ -> assert false

type subst = (EConstr.rel_context * EConstr.constr) Evar.Map.t

exception CannotFilter

let filtering sigma env cv_pb c1 c2 =
  let open EConstr in
  let open Vars in
  let evm = ref Evar.Map.empty in
  let define cv_pb e1 ev c1 =
    try let (e2,c2) = Evar.Map.find ev !evm in
    let shift = List.length e1 - List.length e2 in
    if constr_cmp sigma cv_pb c1 (lift shift c2) then () else raise CannotFilter
    with Not_found ->
      evm := Evar.Map.add ev (e1,c1) !evm
  in
  let rec aux env cv_pb c1 c2 =
    match EConstr.kind sigma c1, EConstr.kind sigma c2 with
      | App _, App _ ->
        let ((p1,l1),(p2,l2)) = (split_app sigma c1),(split_app sigma c2) in
        let () = aux env cv_pb l1 l2 in
        begin match p1, p2 with
        | [], [] -> ()
        | (h1 :: p1), (h2 :: p2) ->
          aux env cv_pb (applist (h1, p1)) (applist (h2, p2))
        | _ -> assert false
        end
      | Prod (n,t1,c1), Prod (_,t2,c2) ->
	  aux env cv_pb t1 t2;
	  aux (RelDecl.LocalAssum (n,t1) :: env) cv_pb c1 c2
      | _, Evar (ev,_) -> define cv_pb env ev c1
      | Evar (ev,_), _ -> define cv_pb env ev c2
      | _ ->
	  if compare_constr_univ sigma
	  (fun pb c1 c2 -> aux env pb c1 c2; true) cv_pb c1 c2 then ()
	  else raise CannotFilter
	  (* TODO: le reste des binders *)
  in
  aux env cv_pb c1 c2; !evm

let decompose_prod_letin sigma c =
  let rec prodec_rec i l c = match EConstr.kind sigma c with
    | Prod (n,t,c)    -> prodec_rec (succ i) (RelDecl.LocalAssum (n,t)::l) c
    | LetIn (n,d,t,c) -> prodec_rec (succ i) (RelDecl.LocalDef (n,d,t)::l) c
    | Cast (c,_,_)    -> prodec_rec i l c
    | _               -> i,l,c in
  prodec_rec 0 [] c

(* (nb_lam [na1:T1]...[nan:Tan]c) where c is not an abstraction
 * gives n (casts are ignored) *)
let nb_lam sigma c =
  let rec nbrec n c = match EConstr.kind sigma c with
    | Lambda (_,_,c) -> nbrec (n+1) c
    | Cast (c,_,_) -> nbrec n c
    | _ -> n
  in
  nbrec 0 c

(* similar to nb_lam, but gives the number of products instead *)
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

let align_prod_letin sigma c a =
  let (lc,_,_) = decompose_prod_letin sigma c in
  let (la,l,a) = decompose_prod_letin sigma a in
  if not (la >= lc) then invalid_arg "align_prod_letin";
  let (l1,l2) = Util.List.chop lc l in
  l2,it_mkProd_or_LetIn a l1

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

let map_rel_context_with_binders f sign =
  let rec aux k = function
    | d::sign -> RelDecl.map_constr (f k) d :: aux (k-1) sign
    | [] -> []
  in
  aux (Context.Rel.length sign) sign

let substl_rel_context l =
  map_rel_context_with_binders (fun k -> substnl l (k-1))

let lift_rel_context n =
  map_rel_context_with_binders (liftn n)

let smash_rel_context sign =
  let rec aux acc = function
  | [] -> acc
  | (RelDecl.LocalAssum _ as d) :: l -> aux (d::acc) l
  | RelDecl.LocalDef (_,b,_) :: l ->
      (* Quadratic in the number of let but there are probably a few of them *)
      aux (List.rev (substl_rel_context [b] (List.rev acc))) l
  in List.rev (aux [] sign)

let fold_named_context_both_sides f l ~init = List.fold_right_and_left f l init

let mem_named_context_val id ctxt =
  try ignore(Environ.lookup_named_ctxt id ctxt); true with Not_found -> false

let map_rel_decl f = function
| RelDecl.LocalAssum (id, t) -> RelDecl.LocalAssum (id, f t)
| RelDecl.LocalDef (id, b, t) -> RelDecl.LocalDef (id, f b, f t)

let map_named_decl f = function
| NamedDecl.LocalAssum (id, t) -> NamedDecl.LocalAssum (id, f t)
| NamedDecl.LocalDef (id, b, t) -> NamedDecl.LocalDef (id, f b, f t)

let compact_named_context sign =
  let compact l decl =
    match decl, l with
    | NamedDecl.LocalAssum (i,t), [] ->
       [CompactedDecl.LocalAssum ([i],t)]
    | NamedDecl.LocalDef (i,c,t), [] ->
       [CompactedDecl.LocalDef ([i],c,t)]
    | NamedDecl.LocalAssum (i1,t1), CompactedDecl.LocalAssum (li,t2) :: q ->
       if Constr.equal t1 t2
       then CompactedDecl.LocalAssum (i1::li, t2) :: q
       else CompactedDecl.LocalAssum ([i1],t1) :: CompactedDecl.LocalAssum (li,t2) :: q
    | NamedDecl.LocalDef (i1,c1,t1), CompactedDecl.LocalDef (li,c2,t2) :: q ->
       if Constr.equal c1 c2 && Constr.equal t1 t2
       then CompactedDecl.LocalDef (i1::li, c2, t2) :: q
       else CompactedDecl.LocalDef ([i1],c1,t1) :: CompactedDecl.LocalDef (li,c2,t2) :: q
    | NamedDecl.LocalAssum (i,t), q ->
       CompactedDecl.LocalAssum ([i],t) :: q
    | NamedDecl.LocalDef (i,c,t), q ->
       CompactedDecl.LocalDef ([i],c,t) :: q
  in
  sign |> Context.Named.fold_inside compact ~init:[] |> List.rev

let clear_named_body id env =
  let open NamedDecl in
  let aux _ = function
  | LocalDef (id',c,t) when Id.equal id id' -> push_named (LocalAssum (id,t))
  | d -> push_named d in
  fold_named_context aux env ~init:(reset_context env)

let global_vars_set env sigma constr =
  let rec filtrec acc c =
    let acc = match EConstr.kind sigma c with
    | Var _ | Const _ | Ind _ | Construct _ ->
      Id.Set.union (vars_of_global env (EConstr.to_constr sigma c)) acc
    | _ -> acc
    in
    EConstr.fold sigma filtrec acc c
  in
  filtrec Id.Set.empty constr

let global_vars env sigma ids = Id.Set.elements (global_vars_set env sigma ids)

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

let global_app_of_constr sigma c =
  let open Globnames in
  match EConstr.kind sigma c with
  | Const (c, u) -> (ConstRef c, u), None
  | Ind (i, u) -> (IndRef i, u), None
  | Construct (c, u) -> (ConstructRef c, u), None
  | Var id -> (VarRef id, EConstr.EInstance.empty), None
  | Proj (p, c) -> (ConstRef (Projection.constant p), EConstr.EInstance.empty), Some c
  | _ -> raise Not_found

let prod_applist sigma c l =
  let open EConstr in
  let rec app subst c l =
    match EConstr.kind sigma c, l with
    | Prod(_,_,c), arg::l -> app (arg::subst) c l
    | _, [] -> Vars.substl subst c
    | _ -> anomaly (Pp.str "Not enough prod's.") in
  app [] c l

let prod_applist_assum sigma n c l =
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

(* Combinators on judgments *)

let on_judgment f j = { uj_val = f j.uj_val; uj_type = f j.uj_type }
let on_judgment_value f j = { j with uj_val = f j.uj_val }
let on_judgment_type f j = { j with uj_type = f j.uj_type }

(* Cut a context ctx in 2 parts (ctx1,ctx2) with ctx1 containing k non let-in
     variables skips let-in's; let-in's in the middle are put in ctx2 *)
let context_chop k ctx =
  let rec chop_aux acc = function
    | (0, l2) -> (List.rev acc, l2)
    | (n, (RelDecl.LocalDef _ as h)::t) -> chop_aux (h::acc) (n, t)
    | (n, (h::t)) -> chop_aux (h::acc) (pred n, t)
    | (_, []) -> anomaly (Pp.str "context_chop.")
  in chop_aux [] (k,ctx)

(* Do not skip let-in's *)
let env_rel_context_chop k env =
  let open EConstr in
  let rels = rel_context env in
  let ctx1,ctx2 = List.chop k rels in
  push_rel_context ctx2 (reset_with_named_context (named_context_val env) env),
  ctx1
end

include Internal
