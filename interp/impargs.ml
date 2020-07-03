(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Pp
open Util
open Names
open Constr
open Globnames
open Glob_term
open Declarations
open Lib
open Libobject
open EConstr
open Reductionops
open Namegen
open Constrexpr

module NamedDecl = Context.Named.Declaration

(*s Flags governing the computation of implicit arguments *)

type implicits_flags = {
  auto : bool;                     (* automatic or manual only *)
  strict : bool;                   (* true = strict *)
  strongly_strict : bool;          (* true = strongly strict *)
  reversible_pattern : bool;
  contextual : bool;               (* true = contextual *)
  maximal : bool
}

let implicit_args = ref {
  auto = false;
  strict = true;
  strongly_strict = false;
  reversible_pattern = false;
  contextual = false;
  maximal = false;
}

let make_implicit_args flag =
  implicit_args := { !implicit_args with auto = flag }

let make_strict_implicit_args flag =
  implicit_args := { !implicit_args with strict = flag }

let make_strongly_strict_implicit_args flag =
  implicit_args := { !implicit_args with strongly_strict = flag }

let make_reversible_pattern_implicit_args flag =
  implicit_args := { !implicit_args with reversible_pattern = flag }

let make_contextual_implicit_args flag =
  implicit_args := { !implicit_args with contextual = flag }

let make_maximal_implicit_args flag =
  implicit_args := { !implicit_args with maximal = flag }

let is_implicit_args () = !implicit_args.auto
let is_strict_implicit_args () = !implicit_args.strict
let is_strongly_strict_implicit_args () = !implicit_args.strongly_strict
let is_reversible_pattern_implicit_args () = !implicit_args.reversible_pattern
let is_contextual_implicit_args () = !implicit_args.contextual
let is_maximal_implicit_args () = !implicit_args.maximal

let with_implicit_protection f x =
  let oflags = !implicit_args in
  try
    let rslt = f x in
    implicit_args := oflags;
    rslt
  with reraise ->
    let reraise = Exninfo.capture reraise in
    let () = implicit_args := oflags in
    Exninfo.iraise reraise

type on_trailing_implicit = Error | Info | Silent


let msg_trailing_implicit (fail : on_trailing_implicit) na i =
  let pos = match na with
  | Anonymous -> "number " ^ string_of_int i
  | Name id -> Names.Id.to_string id in
  let str1 = "Argument " ^ pos ^ " is a trailing implicit, " in
  match fail with
  | Error ->
    user_err (strbrk (str1 ^ "so it can't be declared non maximal. Please use { } instead of [ ]."))
  | Info ->
    Flags.if_verbose Feedback.msg_info (strbrk (str1 ^ "so it has been declared maximally inserted."))
  | Silent -> ()

let set_maximality fail na i imps b =
  (* Force maximal insertion on ending implicits (compatibility) *)
  b || (
    let is_set x = match x with None -> false | _ -> true in
    let b' = List.for_all is_set imps in
    if b' then msg_trailing_implicit fail na i;
    b')

(*s Computation of implicit arguments *)

(* We remember various information about why an argument is
   inferable as implicit

- [DepRigid] means that the implicit argument can be found by
  unification along a rigid path (we do not print the arguments of
  this kind if there is enough arguments to infer them)

- [DepFlex] means that the implicit argument can be found by unification
  along a collapsible path only (e.g. as x in (P x) where P is another
  argument) (we do (defensively) print the arguments of this kind)

- [DepFlexAndRigid] means that the least argument from which the
  implicit argument can be inferred is following a collapsible path
  but there is a greater argument from where the implicit argument is
  inferable following a rigid path (useful to know how to print a
  partial application)

- [Manual] means the argument has been explicitly set as implicit.

  We also consider arguments inferable from the conclusion but it is
  operational only if [conclusion_matters] is true.
*)

type argument_position =
  | Conclusion
  | Hyp of int

let argument_position_eq p1 p2 = match p1, p2 with
| Conclusion, Conclusion -> true
| Hyp h1, Hyp h2 -> Int.equal h1 h2
| _ -> false

type implicit_explanation =
  | DepRigid of argument_position
  | DepFlex of argument_position
  | DepFlexAndRigid of (*flex*) argument_position * (*rig*) argument_position
  | Manual

let argument_less = function
  | Hyp n, Hyp n' -> n<n'
  | Hyp _, Conclusion -> true
  | Conclusion, _ -> false

let update pos rig st =
  let e =
  if rig then
    match st with
      | None -> DepRigid pos
      | Some (DepRigid n as x) ->
          if argument_less (pos,n) then DepRigid pos else x
      | Some (DepFlexAndRigid (fpos,rpos) as x) ->
          if argument_less (pos,fpos) || argument_position_eq pos fpos then DepRigid pos else
          if argument_less (pos,rpos) then DepFlexAndRigid (fpos,pos) else x
      | Some (DepFlex fpos) ->
          if argument_less (pos,fpos) || argument_position_eq pos fpos then DepRigid pos
          else DepFlexAndRigid (fpos,pos)
      | Some Manual -> assert false
  else
    match st with
      | None -> DepFlex pos
      | Some (DepRigid rpos as x) ->
          if argument_less (pos,rpos) then DepFlexAndRigid (pos,rpos) else x
      | Some (DepFlexAndRigid (fpos,rpos) as x) ->
          if argument_less (pos,fpos) then DepFlexAndRigid (pos,rpos) else x
      | Some (DepFlex fpos as x) ->
          if argument_less (pos,fpos) then DepFlex pos else x
      | Some Manual -> assert false
  in Some e

(* modified is_rigid_reference with a truncated env *)
let is_flexible_reference env sigma bound depth f =
  match kind sigma f with
    | Rel n when n >= bound+depth -> (* inductive type *) false
    | Rel n when n >= depth -> (* previous argument *) true
    | Rel n -> (* since local definitions have been expanded *) false
    | Const (kn,_) ->
        let cb = Environ.lookup_constant kn env in
        (match cb.const_body with Def _ -> true | _ -> false)
    | Var id ->
        env |> Environ.lookup_named id |> NamedDecl.is_local_def
    | Ind _ | Construct _ -> false
    |  _ -> true

let push_lift d (e,n) = (push_rel d e,n+1)

let is_reversible_pattern sigma bound depth f l =
  isRel sigma f && let n = destRel sigma f in (n < bound+depth) && (n >= depth) &&
  Array.for_all (fun c -> isRel sigma c && destRel sigma c < depth) l &&
  Array.distinct l

(* Precondition: rels in env are for inductive types only *)
let add_free_rels_until strict strongly_strict revpat bound env sigma m pos acc =
  let rec frec rig (env,depth as ed) c =
    let hd = if strict then whd_all env sigma c else c in
    let c = if strongly_strict then hd else c in
    match kind sigma hd with
    | Rel n when (n < bound+depth) && (n >= depth) ->
        let i = bound + depth - n - 1 in
        acc.(i) <- update pos rig acc.(i)
    | App (f,l) when revpat && is_reversible_pattern sigma bound depth f l ->
        let i = bound + depth - EConstr.destRel sigma f - 1 in
        acc.(i) <- update pos rig acc.(i)
    | App (f,_) when rig && is_flexible_reference env sigma bound depth f ->
        if strict then () else
          iter_with_full_binders sigma push_lift (frec false) ed c
    | Proj (p, _) when rig ->
      if strict then () else
        iter_with_full_binders sigma push_lift (frec false) ed c
    | Case _ when rig ->
        if strict then () else
          iter_with_full_binders sigma push_lift (frec false) ed c
    | Evar _ -> ()
    | _ ->
        iter_with_full_binders sigma push_lift (frec rig) ed c
  in
  let () = if not (Vars.noccur_between sigma 1 bound m) then frec true (env,1) m in
  acc

(* compute the list of implicit arguments *)

let rec is_rigid_head sigma t = match kind sigma t with
  | Rel _ | Evar _ -> false
  | Ind _ | Const _ | Var _ | Sort _ -> true
  | Case (_,_,f,_) -> is_rigid_head sigma f
  | Proj (p,c) -> true
  | App (f,args) ->
      (match kind sigma f with
        | Fix ((fi,i),_) -> is_rigid_head sigma (args.(Option.get fi.(i)))
        | _ -> is_rigid_head sigma f)
  | Lambda _ | LetIn _ | Construct _ | CoFix _ | Fix _
  | Prod _ | Meta _ | Cast _ | Int _ | Float _ -> assert false

let is_rigid env sigma t =
  let open Context.Rel.Declaration in
  let t = whd_all env sigma t in
  match kind sigma t with
  | Prod (na,a,b) ->
     let (_,t) = splay_prod (push_rel (LocalAssum (na,a)) env) sigma b in
     is_rigid_head sigma t
  | _ -> true

let find_displayed_name_in sigma all avoid na (env, b) =
  let envnames_b = (env, b) in
  let flag = RenamingElsewhereFor envnames_b in
  if all then compute_and_force_displayed_name_in sigma flag avoid na b
  else compute_displayed_name_in sigma flag avoid na b

let compute_implicits_names_gen all env sigma t =
  let open Context.Rel.Declaration in
  let rec aux env avoid names t =
    let t = whd_all env sigma t in
    match kind sigma t with
    | Prod (na,a,b) ->
       let na',avoid' = find_displayed_name_in sigma all avoid na.Context.binder_name (names,b) in
       aux (push_rel (LocalAssum (na,a)) env) avoid' (na'::names) b
    | _ -> List.rev names
  in aux env Id.Set.empty [] t

let compute_implicits_names = compute_implicits_names_gen true

let compute_implicits_explanation_gen strict strongly_strict revpat contextual env sigma t =
  let open Context.Rel.Declaration in
  let rec aux env n t =
    let t = whd_all env sigma t in
    match kind sigma t with
    | Prod (na,a,b) ->
       add_free_rels_until strict strongly_strict revpat n env sigma a (Hyp (n+1))
         (aux (push_rel (LocalAssum (na,a)) env) (n+1) b)
    | _ ->
       let v = Array.make n None in
       if contextual then
         add_free_rels_until strict strongly_strict revpat n env sigma t Conclusion v
       else v
  in
  match kind sigma (whd_all env sigma t) with
  | Prod (na,a,b) ->
     let v = aux (push_rel (LocalAssum (na,a)) env) 1 b in
     Array.to_list v
  | _ -> []

let compute_implicits_explanation_flags env sigma f t =
  compute_implicits_explanation_gen
    (f.strict || f.strongly_strict) f.strongly_strict
    f.reversible_pattern f.contextual env sigma t

let compute_implicits_flags env sigma f all t =
  List.combine
    (compute_implicits_names_gen all env sigma t)
    (compute_implicits_explanation_flags env sigma f t)

let compute_auto_implicits env sigma flags enriching t =
  List.combine
    (compute_implicits_names env sigma t)
    (if enriching then compute_implicits_explanation_flags env sigma flags t
     else compute_implicits_explanation_gen false false false true env sigma t)

(* Extra information about implicit arguments *)

type maximal_insertion = bool (* true = maximal contextual insertion *)
type force_inference = bool (* true = always infer, never turn into evar/subgoal *)

type implicit_status =
    (* None = Not implicit *)
    (explicitation * implicit_explanation * (maximal_insertion * force_inference)) option

type implicit_side_condition = DefaultImpArgs | LessArgsThan of int

type implicits_list = implicit_side_condition * implicit_status list

let is_status_implicit = function
  | None -> false
  | _ -> true

let name_of_pos k = Id.of_string ("arg_" ^ string_of_int k)

let binding_kind_of_status = function
  | Some (_, _, (false, _)) -> NonMaxImplicit
  | Some (_, _, (true, _)) -> MaxImplicit
  | None -> Explicit

let name_of_implicit = function
  | None -> anomaly (Pp.str "Not an implicit argument.")
  | Some (ExplByName id,_,_) -> id
  | Some (ExplByPos (k,_),_,_) -> name_of_pos k

let maximal_insertion_of = function
  | Some (_,_,(b,_)) -> b
  | None -> anomaly (Pp.str "Not an implicit argument.")

let force_inference_of = function
  | Some (_, _, (_, b)) -> b
  | None -> anomaly (Pp.str "Not an implicit argument.")

(* [in_ctx] means we know the expected type, [n] is the index of the argument *)
let is_inferable_implicit in_ctx n = function
  | None -> false
  | Some (_,DepRigid (Hyp p),_) -> in_ctx || n >= p
  | Some (_,DepFlex (Hyp p),_) -> false
  | Some (_,DepFlexAndRigid (_,Hyp q),_) -> in_ctx || n >= q
  | Some (_,DepRigid Conclusion,_) -> in_ctx
  | Some (_,DepFlex Conclusion,_) -> false
  | Some (_,DepFlexAndRigid (_,Conclusion),_) -> in_ctx
  | Some (_,Manual,_) -> true

let positions_of_implicits (_,impls) =
  let rec aux n = function
      [] -> []
    | Some _ :: l -> n :: aux (n+1) l
    | None :: l -> aux (n+1) l
  in aux 1 impls

(* Manage user-given implicit arguments *)

let rec prepare_implicits i f = function
  | [] -> []
  | (Anonymous, Some _)::_ -> anomaly (Pp.str "Unnamed implicit.")
  | (Name id, Some imp)::imps ->
      let imps' = prepare_implicits (i+1) f imps in
      Some (ExplByName id,imp,(set_maximality Silent (Name id) i imps' f.maximal,true)) :: imps'
  | _::imps -> None :: prepare_implicits (i+1) f imps

let set_manual_implicits silent flags enriching autoimps l =
  (* Compare with automatic implicits to recover printing data and names *)
  let rec merge k autoimps explimps = match autoimps, explimps with
    | autoimp::autoimps, explimp::explimps ->
       let imps' = merge (k+1) autoimps explimps in
       begin match autoimp, explimp.CAst.v with
       | (Name id,_), Some (_,max) ->
          Some (ExplByName id, Manual, (set_maximality (if silent then Silent else Error) (Name id) k imps' max, true))
       | (Name id,Some exp), None when enriching ->
          Some (ExplByName id, exp, (set_maximality (if silent then Silent else Info) (Name id) k imps' flags.maximal, true))
       | (Name _,_), None -> None
       | (Anonymous,_), Some (Name id,max) ->
          Some (ExplByName id,Manual,(max,true))
       | (Anonymous,_), Some (Anonymous,max) ->
          Some (ExplByPos (k,None),Manual,(max,true))
       | (Anonymous,_), None -> None
       end :: imps'
    | [], [] -> []
    | [], _ -> assert false
    (* possibly more automatic than manual implicit arguments n
       when the conclusion is an unfoldable constant *)
    | autoimps, [] -> merge k autoimps [CAst.make None]
  in merge 1 autoimps l

let compute_semi_auto_implicits env sigma f t =
  if not f.auto then [DefaultImpArgs, []]
  else let l = compute_implicits_flags env sigma f false t in
       [DefaultImpArgs, prepare_implicits 1 f l]

(*s Constants. *)

let compute_constant_implicits flags cst =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let cb = Environ.lookup_constant cst env in
  let ty = of_constr cb.const_type in
  let impls = compute_semi_auto_implicits env sigma flags ty in
  impls

(*s Inductives and constructors. Their implicit arguments are stored
   in an array, indexed by the inductive number, of pairs $(i,v)$ where
   $i$ are the implicit arguments of the inductive and $v$ the array of
   implicit arguments of the constructors. *)

let compute_mib_implicits flags kn =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let mib = Environ.lookup_mind kn env in
  let ar =
    Array.to_list
      (Array.mapi  (* No need to lift, arities contain no de Bruijn *)
        (fun i mip ->
          (* No need to care about constraints here *)
          let ty, _ = Typeops.type_of_global_in_context env (GlobRef.IndRef (kn,i)) in
          let r = Inductive.relevance_of_inductive env (kn,i) in
          Context.Rel.Declaration.LocalAssum (Context.make_annot (Name mip.mind_typename) r, ty))
        mib.mind_packets) in
  let env_ar = Environ.push_rel_context ar env in
  let imps_one_inductive i mip =
    let ind = (kn,i) in
    let ar, _ = Typeops.type_of_global_in_context env (GlobRef.IndRef ind) in
    ((GlobRef.IndRef ind,compute_semi_auto_implicits env sigma flags (of_constr ar)),
     Array.mapi (fun j (ctx, cty) ->
      let c = of_constr (Term.it_mkProd_or_LetIn cty ctx) in
       (GlobRef.ConstructRef (ind,j+1),compute_semi_auto_implicits env_ar sigma flags c))
       mip.mind_nf_lc)
  in
  Array.mapi imps_one_inductive mib.mind_packets

let compute_all_mib_implicits flags kn =
  let imps = compute_mib_implicits flags kn in
  List.flatten
    (Array.map_to_list (fun (ind,cstrs) -> ind::Array.to_list cstrs) imps)

(*s Variables. *)

let compute_var_implicits flags id =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  compute_semi_auto_implicits env sigma flags (NamedDecl.get_type (lookup_named id env))

(* Implicits of a global reference. *)

let compute_global_implicits flags = let open GlobRef in function
  | VarRef id -> compute_var_implicits flags id
  | ConstRef kn -> compute_constant_implicits flags kn
  | IndRef (kn,i) ->
      let ((_,imps),_) = (compute_mib_implicits flags kn).(i) in imps
  | ConstructRef ((kn,i),j) ->
      let (_,cimps) = (compute_mib_implicits flags kn).(i) in snd cimps.(j-1)

(* Merge a manual explicitation with an implicit_status list *)

let merge_impls (cond,oldimpls) (_,newimpls) =
  let oldimpls,usersuffiximpls = List.chop (List.length newimpls) oldimpls in
  cond, (List.map2 (fun orig ni ->
    match orig with
    | Some (_, Manual, _) -> orig
    | _ -> ni) oldimpls newimpls)@usersuffiximpls

(* Caching implicits *)

type implicit_interactive_request =
  | ImplAuto
  | ImplManual of int

type implicit_discharge_request =
  | ImplLocal
  | ImplConstant of implicits_flags
  | ImplMutualInductive of MutInd.t * implicits_flags
  | ImplInteractive of implicits_flags *
      implicit_interactive_request

let implicits_table = Summary.ref GlobRef.Map.empty ~name:"implicits"

let implicits_of_global ref =
  try
    let l = GlobRef.Map.find ref !implicits_table in
    try
      let rename_l = Arguments_renaming.arguments_names ref in
      let rec rename implicits names = match implicits, names with
        | [], _ -> []
        | _, [] -> implicits
        | Some (_, x,y) :: implicits, Name id :: names ->
           Some (ExplByName id, x,y) :: rename implicits names
        | imp :: implicits, _ :: names -> imp :: rename implicits names
      in
      List.map (fun (t, il) -> t, rename il rename_l) l
    with Not_found -> l
  with Not_found -> [DefaultImpArgs,[]]

let cache_implicits_decl (ref,imps) =
  implicits_table := GlobRef.Map.add ref imps !implicits_table

let load_implicits _ (_,(_,l)) = List.iter cache_implicits_decl l

let cache_implicits o =
  load_implicits 1 o

let subst_implicits_decl subst (r,imps as o) =
  let r' = fst (subst_global subst r) in if r==r' then o else (r',imps)

let subst_implicits (subst,(req,l)) =
  (ImplLocal,List.Smart.map (subst_implicits_decl subst) l)

(* This was moved out of lib.ml, however it is not stored with regular
   implicit data *)
let sec_implicits =
  Summary.ref Id.Map.empty ~name:"section-implicits"

let impls_of_context ctx =
  let map decl =
    let id = NamedDecl.get_id decl in
    match Id.Map.get id !sec_implicits with
    | NonMaxImplicit -> Some (ExplByName id, Manual, (false, true))
    | MaxImplicit -> Some (ExplByName id, Manual, (true, true))
    | Explicit -> None
  in
  List.rev_map map (List.filter (NamedDecl.is_local_assum) ctx)

let adjust_side_condition p = function
  | LessArgsThan n -> LessArgsThan (n+p)
  | DefaultImpArgs -> DefaultImpArgs

let add_section_impls vars extra_impls (cond,impls) =
  let p = List.length vars - List.length extra_impls in
  adjust_side_condition p cond, extra_impls @ impls

let discharge_implicits (_,(req,l)) =
  match req with
  | ImplLocal -> None
  | ImplMutualInductive _ | ImplInteractive _ | ImplConstant _ ->
     let l' =
       try
         List.map (fun (gr, l) ->
             let vars = variable_section_segment_of_reference gr in
             let extra_impls = impls_of_context vars in
             let newimpls = List.map (add_section_impls vars extra_impls) l in
             (gr, newimpls)) l
       with Not_found -> l in
     Some (req,l')

let rebuild_implicits (req,l) =
  match req with
  | ImplLocal -> assert false
  | ImplConstant flags ->
      let ref,oldimpls = List.hd l in
      let newimpls = compute_global_implicits flags ref in
      req, [ref, List.map2 merge_impls oldimpls newimpls]
  | ImplMutualInductive (kn,flags) ->
      let newimpls = compute_all_mib_implicits flags kn in
      let rec aux olds news =
       match olds, news with
       | (_, oldimpls) :: old, (gr, newimpls) :: tl ->
          (gr, List.map2 merge_impls oldimpls newimpls) :: aux old tl
       | [], [] -> []
       | _, _ -> assert false
      in req, aux l newimpls

  | ImplInteractive (flags,o) ->
      let ref,oldimpls = List.hd l in
      (if isVarRef ref && is_in_section ref then ImplLocal else req),
      match o with
      | ImplAuto ->
         let newimpls = compute_global_implicits flags ref in
         [ref,List.map2 merge_impls oldimpls newimpls]
      | ImplManual userimplsize ->
         if flags.auto then
           let newimpls = List.hd (compute_global_implicits flags ref) in
           let p = List.length (snd newimpls) - userimplsize in
           let newimpls = on_snd (List.firstn p) newimpls in
           [ref,List.map (fun o -> merge_impls o newimpls) oldimpls]
         else
           [ref,oldimpls]

let classify_implicits (req,_ as obj) = match req with
| ImplLocal -> Dispose
| _ -> Substitute obj

type implicits_obj =
    implicit_discharge_request *
      (GlobRef.t * implicits_list list) list

let inImplicits : implicits_obj -> obj =
  declare_object {(default_object "IMPLICITS") with
    cache_function = cache_implicits;
    load_function = load_implicits;
    subst_function = subst_implicits;
    classify_function = classify_implicits;
    discharge_function = discharge_implicits;
    rebuild_function = rebuild_implicits }

let is_local local ref = local || isVarRef ref && is_in_section ref

let declare_implicits_gen req flags ref =
  let imps = compute_global_implicits flags ref in
  add_anonymous_leaf (inImplicits (req,[ref,imps]))

let declare_implicits local ref =
  let flags = { !implicit_args with auto = true } in
  let req =
    if is_local local ref then ImplLocal else ImplInteractive(flags,ImplAuto) in
    declare_implicits_gen req flags ref

let declare_var_implicits id ~impl =
  let flags = !implicit_args in
  sec_implicits := Id.Map.add id impl !sec_implicits;
  declare_implicits_gen ImplLocal flags (GlobRef.VarRef id)

let declare_constant_implicits con =
  let flags = !implicit_args in
    declare_implicits_gen (ImplConstant flags) flags (GlobRef.ConstRef con)

let declare_mib_implicits kn =
  let flags = !implicit_args in
  let imps = Array.map_to_list
    (fun (ind,cstrs) -> ind::(Array.to_list cstrs))
    (compute_mib_implicits flags kn) in
    add_anonymous_leaf
      (inImplicits (ImplMutualInductive (kn,flags),List.flatten imps))

(* Declare manual implicits *)
type manual_implicits = (Name.t * bool) option CAst.t list

let compute_implicits_with_manual env sigma typ enriching l =
  let autoimpls = compute_auto_implicits env sigma !implicit_args enriching typ in
  set_manual_implicits true !implicit_args enriching autoimpls l

let check_inclusion l =
  (* Check strict inclusion *)
  let rec aux = function
    | n1::(n2::_ as nl) ->
        if n1 <= n2 then
          user_err Pp.(str "Sequences of implicit arguments must be of different lengths.");
        aux nl
    | _ -> () in
  aux (List.map snd l)

let check_rigidity isrigid =
  if not isrigid then
    user_err  (strbrk "Multiple sequences of implicit arguments available only for references that cannot be applied to an arbitrarily large number of arguments.")

let projection_implicits env p impls =
  let npars = Projection.npars p in
  CList.skipn_at_least npars impls

let declare_manual_implicits local ref ?enriching l =
  let flags = !implicit_args in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let t, _ = Typeops.type_of_global_in_context env ref in
  let t = of_constr t in
  let enriching = Option.default flags.auto enriching in
  let autoimpls = compute_auto_implicits env sigma flags enriching t in
  let l = [DefaultImpArgs, set_manual_implicits false flags enriching autoimpls l] in
  let req =
    if is_local local ref then ImplLocal
    else ImplInteractive(flags,ImplManual (List.length autoimpls))
  in add_anonymous_leaf (inImplicits (req,[ref,l]))

let maybe_declare_manual_implicits local ref ?enriching l =
  if List.exists (fun x -> x.CAst.v <> None) l then
    declare_manual_implicits local ref ?enriching l

let explicit_kind i = function
  | Name id -> ExplByName id
  | Anonymous -> ExplByPos (i,None)

let compute_implicit_statuses autoimps l =
  let rec aux i = function
    | _ :: autoimps, Explicit :: manualimps -> None :: aux (i+1) (autoimps, manualimps)
    | na :: autoimps, MaxImplicit :: manualimps ->
       Some (explicit_kind i na, Manual, (true, true)) :: aux (i+1) (autoimps, manualimps)
    | na :: autoimps, NonMaxImplicit :: manualimps ->
       let imps' = aux (i+1) (autoimps, manualimps) in
       let max = set_maximality Error na i imps' false in
       Some (explicit_kind i na, Manual, (max, true)) :: imps'
    | autoimps, [] -> List.map (fun _ -> None) autoimps
    | [], _::_ -> assert false
  in aux 1 (autoimps, l)

let set_implicits local ref l =
  let flags = !implicit_args in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let t, _ = Typeops.type_of_global_in_context env ref in
  let t = of_constr t in
  let autoimpls = compute_implicits_names env sigma t in
  let l' = match l with
    | [] -> assert false
    | [l] ->
       [DefaultImpArgs, compute_implicit_statuses autoimpls l]
    | _ ->
       check_rigidity (is_rigid env sigma t);
       (* Sort by number of implicits, decreasing *)
       let is_implicit = function
         | Explicit -> false
         | _ -> true in
       let l = List.map (fun imps -> (imps,List.count is_implicit imps)) l in
       let l = List.sort (fun (_,n1) (_,n2) -> n2 - n1) l in
       check_inclusion l;
       let nargs = List.length autoimpls in
       List.map (fun (imps,n) ->
           (LessArgsThan (nargs-n),
            compute_implicit_statuses autoimpls imps)) l in
  let req =
    if is_local local ref then ImplLocal
    else ImplInteractive(flags,ImplManual (List.length autoimpls))
  in add_anonymous_leaf (inImplicits (req,[ref,l']))

let extract_impargs_data impls =
  let rec aux p = function
    | (DefaultImpArgs, imps)::_ -> [None,imps]
    | (LessArgsThan n, imps)::l -> (Some (p,n),imps) :: aux (n+1) l
    | [] -> [] in
  aux 0 impls

let make_implicits_list l = [DefaultImpArgs, l]

let rec drop_first_implicits p l =
  if Int.equal p 0 then l else match l with
  | _,[] as x -> x
  | DefaultImpArgs,imp::impls ->
      drop_first_implicits (p-1) (DefaultImpArgs,impls)
  | LessArgsThan n,imp::impls ->
      let n = if is_status_implicit imp then n-1 else n in
      drop_first_implicits (p-1) (LessArgsThan n,impls)

let rec select_impargs_size n = function
  | [] -> [] (* Tolerance for (DefaultImpArgs,[]) *)
  | [_, impls] | (DefaultImpArgs, impls)::_ -> impls
  | (LessArgsThan p, impls)::l ->
      if n <= p then impls else select_impargs_size n l

let select_stronger_impargs = function
  | [] -> [] (* Tolerance for (DefaultImpArgs,[]) *)
  | (_,impls)::_ -> impls
