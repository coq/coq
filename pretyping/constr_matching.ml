(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Pp
open CErrors
open Util
open Names
open Globnames
open Nameops
open Termops
open Reductionops
open Term
open Vars
open Pattern
open Patternops
open Misctypes
open Context.Rel.Declaration
(*i*)

(* Given a term with second-order variables in it,
   represented by Meta's, and possibly applied using [SOAPP] to
   terms, this function will perform second-order, binding-preserving,
   matching, in the case where the pattern is a pattern in the sense
   of Dale Miller.

   ALGORITHM:

   Given a pattern, we decompose it, flattening Cast's and apply's,
   recursing on all operators, and pushing the name of the binder each
   time we descend a binder.

   When we reach a first-order variable, we ask that the corresponding
   term's free-rels all be higher than the depth of the current stack.

   When we reach a second-order application, we ask that the
   intersection of the free-rels of the term and the current stack be
   contained in the arguments of the application, and in that case, we
   construct a LAMBDA with the names on the stack.

 *)

type bound_ident_map = Id.t Id.Map.t

exception PatternMatchingFailure

let warn_meta_collision =
  CWarnings.create ~name:"meta-collision" ~category:"ltac"
         (fun name ->
          strbrk "Collision between bound variable " ++ pr_id name ++
            strbrk " and a metavariable of same name.")

(**  *)
let constrain sigma n (ids, m as x) (names, terms as subst) =
  try
    let (ids', m') = Id.Map.find n terms in
    if List.equal Id.equal ids ids' then
      let (sigma,b) = Evd.eq_constr_univs sigma m m' in
      if b then (sigma,subst)
      else raise PatternMatchingFailure
    else raise PatternMatchingFailure
  with Not_found ->
    let () = if Id.Map.mem n names then warn_meta_collision n in
    (sigma, (names, Id.Map.add n x terms))

let add_binders na1 na2 binding_vars (names, terms as subst) =
  match na1, na2 with
  | Name id1, Name id2 when Id.Set.mem id1 binding_vars ->
    if Id.Map.mem id1 names then
      let () = Glob_ops.warn_variable_collision id1 in
      (names, terms)
    else
      let names = Id.Map.add id1 id2 names in
      let () = if Id.Map.mem id1 terms then
        warn_meta_collision id1 in
      (names, terms)
  | _ -> subst

let rec build_lambda vars ctx m = match vars with
| [] ->
  if Vars.closed0 m then m else raise PatternMatchingFailure
| n :: vars ->
  (* change [ x1 ... xn y z1 ... zm |- t ] into
     [ x1 ... xn z1 ... zm |- lam y. t ] *)
  let len = List.length ctx in
  let pre, suf = List.chop (pred n) ctx in
  let (na, t, suf) = match suf with
  | [] -> assert false
  | (_, na, t) :: suf -> (na, t, suf)
  in
  (** Check that the abstraction is legal by generating a transitive closure of
      its dependencies. *)
  let is_nondep t clear = match clear with
  | [] -> true
  | _ ->
    let rels = free_rels t in
    let check i b = b || not (Int.Set.mem i rels) in
    List.for_all_i check 1 clear
  in
  let fold (_, _, t) clear = is_nondep t clear :: clear in
  (** Produce a list of booleans: true iff we keep the hypothesis *)
  let clear = List.fold_right fold pre [false] in
  let clear = List.drop_last clear in
  (** If the conclusion depends on a variable we cleared, failure *)
  let () = if not (is_nondep m clear) then raise PatternMatchingFailure in
  (** Create the abstracted term *)
  let fold (k, accu) keep =
    if keep then
      let k = succ k in
      (k, Some k :: accu)
    else (k, None :: accu)
  in
  let keep, shift = List.fold_left fold (0, []) clear in
  let shift = List.rev shift in
  let map = function
  | None -> mkProp (** dummy term *)
  | Some i -> mkRel (i + 1)
  in
  (** [x1 ... xn y z1 ... zm] -> [x1 ... xn f(z1) ... f(zm) y] *)
  let subst =
    List.map map shift @
    mkRel 1 ::
    List.mapi (fun i _ -> mkRel (i + keep + 2)) suf
  in
  let map i (id, na, c) =
    let i = succ i in
    let subst = List.skipn i subst in
    let subst = List.map (fun c -> Vars.lift (- i) c) subst in
    (id, na, substl subst c)
  in
  let pre = List.mapi map pre in
  let pre = List.filter_with clear pre in
  let m = substl subst m in
  let map i =
    if i > n then i - n + keep
    else match List.nth shift (i - 1) with
    | None ->
      (** We cleared a variable that we wanted to abstract! *)
      raise PatternMatchingFailure
    | Some k -> k
  in
  let vars = List.map map vars in
  (** Create the abstraction *)
  let m = mkLambda (na, Vars.lift keep t, m) in
  build_lambda vars (pre @ suf) m

let rec extract_bound_aux k accu frels ctx = match ctx with
| [] -> accu
| (na1, na2, _) :: ctx ->
  if Int.Set.mem k frels then
    begin match na1 with
    | Name id ->
      let () = assert (match na2 with Anonymous -> false | Name _ -> true) in
      let () = if Id.Set.mem id accu then raise PatternMatchingFailure in
      extract_bound_aux (k + 1) (Id.Set.add id accu) frels ctx
    | Anonymous -> raise PatternMatchingFailure
    end
  else extract_bound_aux (k + 1) accu frels ctx

let extract_bound_vars frels ctx =
  extract_bound_aux 1 Id.Set.empty frels ctx

let dummy_constr = mkProp

let make_renaming ids = function
| (Name id, Name _, _) ->
  begin
    try mkRel (List.index Id.equal id ids)
    with Not_found -> dummy_constr
  end
| _ -> dummy_constr

let merge_binding sigma allow_bound_rels ctx n cT subst =
  let c = match ctx with
  | [] -> (* Optimization *)
    ([], cT)
  | _ ->
    let frels = free_rels cT in
    if allow_bound_rels then
      let vars = extract_bound_vars frels ctx in
      let ordered_vars = Id.Set.elements vars in
      let rename binding = make_renaming ordered_vars binding in
      let renaming = List.map rename ctx in
      (ordered_vars, substl renaming cT)
    else
      let depth = List.length ctx in
      let min_elt = try Int.Set.min_elt frels with Not_found -> succ depth in
      if depth < min_elt then
        ([], lift (- depth) cT)
      else raise PatternMatchingFailure
  in
  constrain sigma n c subst
      
let matches_core env sigma ~convert ~allow_partial_app ~allow_bound_rels
    (binding_vars,pat) c =
  let convref ref c = 
    match ref, kind_of_term c with
    | VarRef id, Var id' -> Names.id_eq id id'
    | ConstRef c, Const (c',_) -> Names.eq_constant c c'
    | IndRef i, Ind (i', _) -> Names.eq_ind i i'
    | ConstructRef c, Construct (c',u) -> Names.eq_constructor c c'
    | _, _ -> 
      (if convert then 
	  let sigma,c' = Evd.fresh_global env sigma ref in
	    is_conv env sigma c' c
       else false)
  in
  let rec sorec ctx env (sigma,subst as current) p t =
    let cT = strip_outer_cast t in
    match p,kind_of_term cT with
      | PSoApp (n,args),m ->
        let fold (sigma, ans, seen) = function
        | PRel n ->
          let () = if Int.Set.mem n seen then error "Non linear second-order pattern" in
          (sigma, n :: ans, Int.Set.add n seen)
        | _ -> error "Only bound indices allowed in second order pattern matching."
        in
        let sigma, relargs, relset = List.fold_left fold (sigma, [], Int.Set.empty) args in
        let frels = free_rels cT in
        if Int.Set.subset frels relset then
          constrain sigma n ([], build_lambda relargs ctx cT) subst
        else
          raise PatternMatchingFailure

      | PMeta (Some n), m -> merge_binding sigma allow_bound_rels ctx n cT subst

      | PMeta None, m -> current

      | PRef (VarRef v1), Var v2 when Id.equal v1 v2 -> current

      | PVar v1, Var v2 when Id.equal v1 v2 -> current

      | PRef ref, _ when convref ref cT -> current

      | PRel n1, Rel n2 when Int.equal n1 n2 -> current

      | PSort GProp, Sort (Prop Null) -> current

      | PSort GSet, Sort (Prop Pos) -> current

      | PSort (GType _), Sort (Type _) -> current

      | PApp (p, [||]), _ -> sorec ctx env current p t

      | PApp (PApp (h, a1), a2), _ ->
          sorec ctx env current (PApp(h,Array.append a1 a2)) t

      | PApp (PMeta meta,args1), App (c2,args2) when allow_partial_app ->
         (let diff = Array.length args2 - Array.length args1 in
          if diff >= 0 then
            let args21, args22 = Array.chop diff args2 in
	    let c = mkApp(c2,args21) in
            let current =
              match meta with
              | None -> current
              | Some n -> merge_binding sigma allow_bound_rels ctx n c subst in
            Array.fold_left2 (sorec ctx env) current args1 args22
          else (* Might be a projection on the right *)
	    match kind_of_term c2 with
	    | Proj (pr, c) when not (Projection.unfolded pr) ->
	      (try let term = Retyping.expand_projection env sigma pr c (Array.to_list args2) in
		     sorec ctx env current p term
	       with Retyping.RetypeError _ -> raise PatternMatchingFailure)
	    | _ -> raise PatternMatchingFailure)
	   
      | PApp (c1,arg1), App (c2,arg2) ->
	(match c1, kind_of_term c2 with
	| PRef (ConstRef r), Proj (pr,c) when not (eq_constant r (Projection.constant pr))
	    || Projection.unfolded pr ->
	  raise PatternMatchingFailure
	| PProj (pr1,c1), Proj (pr,c) ->
	  if Projection.equal pr1 pr then 
	    try Array.fold_left2 (sorec ctx env) (sorec ctx env current c1 c) arg1 arg2
	    with Invalid_argument _ -> raise PatternMatchingFailure
	  else raise PatternMatchingFailure
	| _, Proj (pr,c) when not (Projection.unfolded pr) ->
	  (try let term = Retyping.expand_projection env sigma pr c (Array.to_list arg2) in
		 sorec ctx env current p term
	   with Retyping.RetypeError _ -> raise PatternMatchingFailure)	    
	| _, _ ->
          try Array.fold_left2 (sorec ctx env) (sorec ctx env current c1 c2) arg1 arg2
          with Invalid_argument _ -> raise PatternMatchingFailure)
	  
      | PApp (PRef (ConstRef c1), _), Proj (pr, c2) 
	when Projection.unfolded pr || not (eq_constant c1 (Projection.constant pr)) -> 
	raise PatternMatchingFailure
	
      | PApp (c, args), Proj (pr, c2) ->
	(try let term = Retyping.expand_projection env sigma pr c2 [] in
	       sorec ctx env current p term
	 with Retyping.RetypeError _ -> raise PatternMatchingFailure)

      | PProj (p1,c1), Proj (p2,c2) when Projection.equal p1 p2 ->
          sorec ctx env current c1 c2

      | PProd (na1,c1,d1), Prod(na2,c2,d2)
      | PLambda (na1,c1,d1), Lambda(na2,c2,d2) ->
         let (sigma, subst) = sorec ctx env current c1 c2 in
	  sorec ((na1,na2,c2)::ctx) (Environ.push_rel (LocalAssum (na2,c2)) env)
            (sigma, add_binders na1 na2 binding_vars subst) d1 d2

      | PLetIn (na1,c1,d1), LetIn(na2,c2,t2,d2) ->
         let (sigma, subst) = sorec ctx env current c1 c2 in
	  sorec ((na1,na2,t2)::ctx) (Environ.push_rel (LocalDef (na2,c2,t2)) env)
            (sigma, add_binders na1 na2 binding_vars subst) d1 d2

      | PIf (a1,b1,b1'), Case (ci,_,a2,[|b2;b2'|]) ->
	  let ctx_b2,b2 = decompose_lam_n_decls ci.ci_cstr_ndecls.(0) b2 in
	  let ctx_b2',b2' = decompose_lam_n_decls ci.ci_cstr_ndecls.(1) b2' in
	  let n = Context.Rel.length ctx_b2 in
          let n' = Context.Rel.length ctx_b2' in
	  if noccur_between 1 n b2 && noccur_between 1 n' b2' then
            let f l (LocalAssum (na,t) | LocalDef (na,_,t)) = (Anonymous,na,t)::l in
	    let ctx_br = List.fold_left f ctx ctx_b2 in
	    let ctx_br' = List.fold_left f ctx ctx_b2' in
	    let b1 = lift_pattern n b1 and b1' = lift_pattern n' b1' in
	    sorec ctx_br' (Environ.push_rel_context ctx_b2' env)
	      (sorec ctx_br (Environ.push_rel_context ctx_b2 env)
                 (sorec ctx env current a1 a2) b1 b2) b1' b2'
          else
            raise PatternMatchingFailure

      | PCase (ci1,p1,a1,br1), Case (ci2,p2,a2,br2) ->
	  let n2 = Array.length br2 in
          let () = match ci1.cip_ind with
          | None -> ()
          | Some ind1 ->
            (** ppedrot: Something spooky going here. The comparison used to be
                the generic one, so I may have broken something. *)
            if not (eq_ind ind1 ci2.ci_ind) then raise PatternMatchingFailure
          in
          let () =
            if not ci1.cip_extensible && not (Int.equal (List.length br1) n2)
            then raise PatternMatchingFailure
          in
	  let chk_branch current (j,n,c) =
	    (* (ind,j+1) is normally known to be a correct constructor
	       and br2 a correct match over the same inductive *)
	    assert (j < n2);
	    sorec ctx env current c br2.(j)
	  in
	  let chk_head = sorec ctx env (sorec ctx env current a1 a2) p1 p2 in
	  List.fold_left chk_branch chk_head br1

      |	PFix c1, Fix _ when eq_constr (mkFix c1) cT -> current
      |	PCoFix c1, CoFix _ when eq_constr (mkCoFix c1) cT -> current
      | _ -> raise PatternMatchingFailure

  in
  sorec [] env (sigma, (Id.Map.empty, Id.Map.empty)) pat c

let matches_core_closed env sigma ~convert ~allow_partial_app pat c =
  let (sigma,(names,subst)) =
    matches_core env sigma ~convert ~allow_partial_app ~allow_bound_rels:false pat c
  in
  (sigma,(names, Id.Map.map snd subst))

let extended_matches env sigma =
  matches_core env sigma ~convert:false ~allow_partial_app:true ~allow_bound_rels:true

let matches env sigma pat c =
  let (sigma,subst) =
    matches_core_closed env sigma false true (Id.Set.empty,pat) c
  in
  (sigma, snd subst)

let special_meta = (-1)

type matching_result =
    { m_sub : bound_ident_map * patvar_map;
      m_evarmap : Evd.evar_map;
      m_ctx : constr; }

let mkresult s sigma c n =
  IStream.Cons ( { m_sub=s; m_evarmap = sigma; m_ctx=c; } , (IStream.thunk n) )

let isPMeta = function PMeta _ -> true | _ -> false

let matches_head env sigma pat c =
  let head =
    match pat, kind_of_term c with
    | PApp (c1,arg1), App (c2,arg2) ->
        if isPMeta c1 then c else
        let n1 = Array.length arg1 in
        if n1 < Array.length arg2 then mkApp (c2,Array.sub arg2 0 n1) else c
    | c1, App (c2,arg2) when not (isPMeta c1) -> c2
    | _ -> c in
  matches env sigma pat head

(* Tells if it is an authorized occurrence and if the instance is closed *)
let authorized_occ env sigma partial_app closed pat c mk_ctx =
  try
    let (sigma,subst) = matches_core_closed env sigma false partial_app pat c in
    if closed && Id.Map.exists (fun _ c -> not (closed0 c)) (snd subst)
    then (fun next -> next ())
    else (fun next -> mkresult subst sigma (mk_ctx (mkMeta special_meta)) next)
  with PatternMatchingFailure -> (fun next -> next ())

let subargs env v = Array.map_to_list (fun c -> (env, c)) v

(* Tries to match a subterm of [c] with [pat] *)
let sub_match env sigma ?(partial_app=false) ?(closed=true) pat c =
  let rec aux env c mk_ctx next =
  let here = authorized_occ env sigma partial_app closed pat c mk_ctx in
  let next () = match kind_of_term c with
  | Cast (c1,k,c2) ->
      let next_mk_ctx = function
      | [c1] -> mk_ctx (mkCast (c1, k, c2))
      | _ -> assert false
      in
      try_aux [env, c1] next_mk_ctx next
  | Lambda (x,c1,c2) ->
      let next_mk_ctx = function
      | [c1; c2] -> mk_ctx (mkLambda (x, c1, c2))
      | _ -> assert false
      in
      let env' = Environ.push_rel (LocalAssum (x,c1)) env in
      try_aux [(env, c1); (env', c2)] next_mk_ctx next
  | Prod (x,c1,c2) ->
      let next_mk_ctx = function
      | [c1; c2] -> mk_ctx (mkProd (x, c1, c2))
      | _ -> assert false
      in
      let env' = Environ.push_rel (LocalAssum (x,c1)) env in
      try_aux [(env, c1); (env', c2)] next_mk_ctx next
  | LetIn (x,c1,t,c2) ->
      let next_mk_ctx = function
      | [c1; c2] -> mk_ctx (mkLetIn (x, c1, t, c2))
      | _ -> assert false
      in
      let env' = Environ.push_rel (LocalDef (x,c1,t)) env in
      try_aux [(env, c1); (env', c2)] next_mk_ctx next
  | App (c1,lc) ->
        let topdown = true in
        if partial_app then
          if topdown then
            let lc1 = Array.sub lc 0 (Array.length lc - 1) in
            let app = mkApp (c1,lc1) in
            let mk_ctx = function
              | [app';c] -> mk_ctx (mkApp (app',[|c|]))
              | _ -> assert false in
            try_aux [(env, app); (env, Array.last lc)] mk_ctx next
          else
            let rec aux2 app args next =
              match args with
              | [] ->
                  let mk_ctx le =
                    mk_ctx (mkApp (List.hd le, Array.of_list (List.tl le))) in
                  let sub = (env, c1) :: subargs env lc in
                  try_aux sub mk_ctx next
              | arg :: args ->
                  let app = mkApp (app,[|arg|]) in
                  let next () = aux2 app args next in
                  let mk_ctx ce = mk_ctx (mkApp (ce, Array.of_list args)) in
                  aux env app mk_ctx next in
            aux2 c1 (Array.to_list lc) next
        else
          let mk_ctx le =
            mk_ctx (mkApp (List.hd le, Array.of_list (List.tl le))) in
          let sub = (env, c1) :: subargs env lc in
          try_aux sub mk_ctx next
  | Case (ci,hd,c1,lc) ->
      let next_mk_ctx = function
      | c1 :: hd :: lc -> mk_ctx (mkCase (ci,hd,c1,Array.of_list lc))
      | _ -> assert false
      in
      let sub = (env, c1) :: (env, hd) :: subargs env lc in
      try_aux sub next_mk_ctx next
  | Fix (indx,(names,types,bodies)) ->
    let nb_fix = Array.length types in
    let next_mk_ctx le =
      let (ntypes,nbodies) = CList.chop nb_fix le in
      mk_ctx (mkFix (indx,(names, Array.of_list ntypes, Array.of_list nbodies))) in
    let sub = subargs env types @ subargs env bodies in
    try_aux sub next_mk_ctx next
  | CoFix (i,(names,types,bodies)) ->
    let nb_fix = Array.length types in
    let next_mk_ctx le =
      let (ntypes,nbodies) = CList.chop nb_fix le in
      mk_ctx (mkCoFix (i,(names, Array.of_list ntypes, Array.of_list nbodies))) in
    let sub = subargs env types @ subargs env bodies in
    try_aux sub next_mk_ctx next
  | Proj (p,c') ->
    let next_mk_ctx le = mk_ctx (mkProj (p,List.hd le)) in
      if partial_app then
	try 
	  let term = Retyping.expand_projection env sigma p c' [] in
	    aux env term mk_ctx next
	with Retyping.RetypeError _ -> next ()
      else
      try_aux [env, c'] next_mk_ctx next
  | Construct _| Ind _|Evar _|Const _ | Rel _|Meta _|Var _|Sort _ ->
    next ()
  in
  here next

  (* Tries [sub_match] for all terms in the list *)
  and try_aux lc mk_ctx next =
    let rec try_sub_match_rec lacc lc =
      match lc with
      | [] -> next ()
      | (env, c) :: tl ->
        let mk_ctx ce = mk_ctx (List.rev_append lacc (ce :: List.map snd tl)) in
        let next () = try_sub_match_rec (c :: lacc) tl in
        aux env c mk_ctx next
    in
    try_sub_match_rec [] lc in
  let lempty () = IStream.Nil in
  let result () = aux env c (fun x -> x) lempty in
  IStream.thunk result

let match_subterm env sigma pat c = sub_match env sigma (Id.Set.empty,pat) c

let match_appsubterm env sigma pat c = 
  sub_match ~partial_app:true env sigma (Id.Set.empty,pat) c

let match_subterm_gen env sigma app pat c = 
  sub_match ~partial_app:app env sigma pat c

let is_matching env sigma pat c =
  try let _ = matches env sigma pat c in true
  with PatternMatchingFailure -> false

let is_matching_head env sigma pat c =
  try let _ = matches_head env sigma pat c in true
  with PatternMatchingFailure -> false

let is_matching_appsubterm ?(closed=true) env sigma pat c =
  let pat = (Id.Set.empty,pat) in
  let results = sub_match ~partial_app:true ~closed env sigma pat c in
  not (IStream.is_empty results)

let matches_conv env sigma p c =
  let sigma, subst = matches_core_closed env sigma true false (Id.Set.empty,p) c in
  sigma, snd subst

let is_matching_conv env sigma pat n =
  try let _ = matches_conv env sigma pat n in true
  with PatternMatchingFailure -> false
