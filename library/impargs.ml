(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Libnames
open Term
open Reduction
open Declarations
open Environ
open Inductive
open Libobject
open Lib
open Nametab
open Pp
open Topconstr
open Termops
open Namegen

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

let with_implicits flags f x =
  let oflags = !implicit_args in
  try
    implicit_args := flags;
    let rslt = f x in
    implicit_args := oflags;
    rslt
  with e -> begin
    implicit_args := oflags;
    raise e
  end

let set_maximality imps b =
  (* Force maximal insertion on ending implicits (compatibility) *)
  b || List.for_all ((<>) None) imps

(*s Computation of implicit arguments *)

(* We remember various information about why an argument is
   inferable as implicit

- [DepRigid] means that the implicit argument can be found by
  unification along a rigid path (we do not print the arguments of
  this kind if there is enough arguments to infer them)

- [DepFlex] means that the implicit argument can be found by unification
  along a collapsable path only (e.g. as x in (P x) where P is another
  argument) (we do (defensively) print the arguments of this kind)

- [DepFlexAndRigid] means that the least argument from which the
  implicit argument can be inferred is following a collapsable path
  but there is a greater argument from where the implicit argument is
  inferable following a rigid path (useful to know how to print a
  partial application)

- [Manual] means the argument has been explicitely set as implicit.

  We also consider arguments inferable from the conclusion but it is
  operational only if [conclusion_matters] is true.
*)

type argument_position =
  | Conclusion
  | Hyp of int

type implicit_explanation =
  | DepRigid of argument_position
  | DepFlex of argument_position
  | DepFlexAndRigid of (*flex*) argument_position * (*rig*) argument_position
  | Manual

let argument_less = function
  | Hyp n, Hyp n' -> n<n'
  | Hyp _, Conclusion -> true
  | Conclusion, _ -> false

let update pos rig (na,st) =
  let e =
  if rig then
    match st with
      | None -> DepRigid pos
      | Some (DepRigid n as x) ->
          if argument_less (pos,n) then DepRigid pos else x
      | Some (DepFlexAndRigid (fpos,rpos) as x) ->
          if argument_less (pos,fpos) or pos=fpos then DepRigid pos else
          if argument_less (pos,rpos) then DepFlexAndRigid (fpos,pos) else x
      | Some (DepFlex fpos) ->
          if argument_less (pos,fpos) or pos=fpos then DepRigid pos
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
  in na, Some e

(* modified is_rigid_reference with a truncated env *)
let is_flexible_reference env bound depth f =
  match kind_of_term f with
    | Rel n when n >= bound+depth -> (* inductive type *) false
    | Rel n when n >= depth -> (* previous argument *) true
    | Rel n -> (* since local definitions have been expanded *) false
    | Const kn ->
        let cb = Environ.lookup_constant kn env in
        cb.const_body <> None & not cb.const_opaque
    | Var id ->
        let (_,value,_) = Environ.lookup_named id env in value <> None
    | Ind _ | Construct _ -> false
    |  _ -> true

let push_lift d (e,n) = (push_rel d e,n+1)

let is_reversible_pattern bound depth f l =
  isRel f & let n = destRel f in (n < bound+depth) & (n >= depth) &
  array_for_all (fun c -> isRel c & destRel c < depth) l &
  array_distinct l

(* Precondition: rels in env are for inductive types only *)
let add_free_rels_until strict strongly_strict revpat bound env m pos acc =
  let rec frec rig (env,depth as ed) c =
    let hd = if strict then whd_betadeltaiota env c else c in
    let c = if strongly_strict then hd else c in
    match kind_of_term hd with
    | Rel n when (n < bound+depth) & (n >= depth) ->
	let i = bound + depth - n - 1 in
        acc.(i) <- update pos rig acc.(i)
    | App (f,l) when revpat & is_reversible_pattern bound depth f l ->
	let i = bound + depth - destRel f - 1 in
	acc.(i) <- update pos rig acc.(i)
    | App (f,_) when rig & is_flexible_reference env bound depth f ->
	if strict then () else
          iter_constr_with_full_binders push_lift (frec false) ed c
    | Case _ when rig ->
	if strict then () else
          iter_constr_with_full_binders push_lift (frec false) ed c
    | Evar _ -> ()
    | _ ->
        iter_constr_with_full_binders push_lift (frec rig) ed c
  in
  frec true (env,1) m; acc

let rec is_rigid_head t = match kind_of_term t with
  | Rel _ | Evar _ -> false
  | Ind _ | Const _ | Var _ | Sort _ -> true
  | Case (_,_,f,_) -> is_rigid_head f
  | App (f,args) ->
      (match kind_of_term f with
	| Fix ((fi,i),_) -> is_rigid_head (args.(fi.(i)))
	| _ -> is_rigid_head f)
  | Lambda _ | LetIn _ | Construct _ | CoFix _ | Fix _
  | Prod _ | Meta _ | Cast _ -> assert false

(* calcule la liste des arguments implicites *)

let find_displayed_name_in all avoid na b =
  if all then
    compute_and_force_displayed_name_in (RenamingElsewhereFor b) avoid na b
  else
    compute_displayed_name_in (RenamingElsewhereFor b) avoid na b

let compute_implicits_gen strict strongly_strict revpat contextual all env t =
  let rigid = ref true in
  let rec aux env avoid n names t =
    let t = whd_betadeltaiota env t in
    match kind_of_term t with
      | Prod (na,a,b) ->
	  let na',avoid' = find_displayed_name_in all avoid na b in
	  add_free_rels_until strict strongly_strict revpat n env a (Hyp (n+1))
            (aux (push_rel (na',None,a) env) avoid' (n+1) (na'::names) b)
      | _ ->
	  rigid := is_rigid_head t;
	  let names = List.rev names in
	  let v = Array.map (fun na -> na,None) (Array.of_list names) in
	  if contextual then
	    add_free_rels_until strict strongly_strict revpat n env t Conclusion v
	  else v
  in
  match kind_of_term (whd_betadeltaiota env t) with
    | Prod (na,a,b) ->
	let na',avoid = find_displayed_name_in all [] na b in
	let v = aux (push_rel (na',None,a) env) avoid 1 [na'] b in
	!rigid, Array.to_list v
    | _ -> true, []

let compute_implicits_flags env f all t =
  compute_implicits_gen
    (f.strict or f.strongly_strict) f.strongly_strict
    f.reversible_pattern f.contextual all env t

let compute_auto_implicits env flags enriching t =
  if enriching then compute_implicits_flags env flags true t
  else compute_implicits_gen false false false true true env t

(* Extra information about implicit arguments *)

type maximal_insertion = bool (* true = maximal contextual insertion *)
type force_inference = bool (* true = always infer, never turn into evar/subgoal *)

type implicit_status =
    (* None = Not implicit *)
    (identifier * implicit_explanation * (maximal_insertion * force_inference)) option

type implicit_side_condition = DefaultImpArgs | LessArgsThan of int

type implicits_list = implicit_side_condition * implicit_status list

let is_status_implicit = function
  | None -> false
  | _ -> true

let name_of_implicit = function
  | None -> anomaly "Not an implicit argument"
  | Some (id,_,_) -> id

let maximal_insertion_of = function
  | Some (_,_,(b,_)) -> b
  | None -> anomaly "Not an implicit argument"

let force_inference_of = function
  | Some (_, _, (_, b)) -> b
  | None -> anomaly "Not an implicit argument"

(* [in_ctx] means we know the expected type, [n] is the index of the argument *)
let is_inferable_implicit in_ctx n = function
  | None -> false
  | Some (_,DepRigid (Hyp p),_) -> in_ctx or n >= p
  | Some (_,DepFlex (Hyp p),_) -> false
  | Some (_,DepFlexAndRigid (_,Hyp q),_) -> in_ctx or n >= q
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

let rec prepare_implicits f = function
  | [] -> []
  | (Anonymous, Some _)::_ -> anomaly "Unnamed implicit"
  | (Name id, Some imp)::imps ->
      let imps' = prepare_implicits f imps in
      Some (id,imp,(set_maximality imps' f.maximal,true)) :: imps'
  | _::imps -> None :: prepare_implicits f imps

let set_implicit id imp insmax =
  (id,(match imp with None -> Manual | Some imp -> imp),insmax)

let rec assoc_by_pos k = function
    (ExplByPos (k', x), b) :: tl when k = k' -> (x,b), tl
  | hd :: tl -> let (x, tl) = assoc_by_pos k tl in x, hd :: tl
  | [] -> raise Not_found

let check_correct_manual_implicits autoimps l =
  List.iter (function
    | ExplByName id,(b,fi,forced) ->
	if not forced then
	  error ("Wrong or non-dependent implicit argument name: "^(string_of_id id)^".")
    | ExplByPos (i,_id),_t ->
	if i<1 or i>List.length autoimps then
	  error ("Bad implicit argument number: "^(string_of_int i)^".")
	else
	  errorlabstrm ""
	    (str "Cannot set implicit argument number " ++ int i ++
	      str ": it has no name.")) l

let set_manual_implicits env flags enriching autoimps l =
  let try_forced k l =
    try
      let (id, (b, fi, fo)), l' = assoc_by_pos k l in
	if fo then
	  let id = match id with Some id -> id | None -> id_of_string ("arg_" ^ string_of_int k) in
	    l', Some (id,Manual,(b,fi))
	else l, None
    with Not_found -> l, None
  in
  if not (list_distinct l) then
    error ("Some parameters are referred more than once.");
  (* Compare with automatic implicits to recover printing data and names *)
  let rec merge k l = function
  | (Name id,imp)::imps ->
      let l',imp,m =
	try
	  let (b, fi, fo) = List.assoc (ExplByName id) l in
	  List.remove_assoc (ExplByName id) l, (Some Manual), (Some (b, fi))
	with Not_found ->
	try
	  let (id, (b, fi, fo)), l' = assoc_by_pos k l in
	    l', (Some Manual), (Some (b,fi))
	with Not_found ->
	  l,imp, if enriching && imp <> None then Some (flags.maximal,true) else None
      in
      let imps' = merge (k+1) l' imps in
      let m = Option.map (fun (b,f) -> set_maximality imps' b, f) m in
      Option.map (set_implicit id imp) m :: imps'
  | (Anonymous,imp)::imps ->
      let l', forced = try_forced k l in
	forced :: merge (k+1) l' imps
  | [] when l = [] -> []
  | [] ->
      check_correct_manual_implicits autoimps l;
      []
  in
  merge 1 l autoimps

let compute_semi_auto_implicits env f manual t =
  match manual with
  | [] ->
      if not f.auto then [DefaultImpArgs, []]
      else let _,l = compute_implicits_flags env f false t in
	     [DefaultImpArgs, prepare_implicits f l]
  | _ ->
      let _,autoimpls = compute_auto_implicits env f f.auto t in
      [DefaultImpArgs, set_manual_implicits env f f.auto autoimpls manual]

let compute_implicits env t = compute_semi_auto_implicits env !implicit_args [] t

(*s Constants. *)

let compute_constant_implicits flags manual cst =
  let env = Global.env () in
  compute_semi_auto_implicits env flags manual (Typeops.type_of_constant env cst)

(*s Inductives and constructors. Their implicit arguments are stored
   in an array, indexed by the inductive number, of pairs $(i,v)$ where
   $i$ are the implicit arguments of the inductive and $v$ the array of
   implicit arguments of the constructors. *)

let compute_mib_implicits flags manual kn =
  let env = Global.env () in
  let mib = lookup_mind kn env in
  let ar =
    Array.to_list
      (Array.map  (* No need to lift, arities contain no de Bruijn *)
        (fun mip ->
	  (Name mip.mind_typename, None, type_of_inductive env (mib,mip)))
        mib.mind_packets) in
  let env_ar = push_rel_context ar env in
  let imps_one_inductive i mip =
    let ind = (kn,i) in
    let ar = type_of_inductive env (mib,mip) in
    ((IndRef ind,compute_semi_auto_implicits env flags manual ar),
     Array.mapi (fun j c ->
       (ConstructRef (ind,j+1),compute_semi_auto_implicits env_ar flags manual c))
       mip.mind_nf_lc)
  in
  Array.mapi imps_one_inductive mib.mind_packets

let compute_all_mib_implicits flags manual kn =
  let imps = compute_mib_implicits flags manual kn in
  List.flatten
    (array_map_to_list (fun (ind,cstrs) -> ind::Array.to_list cstrs) imps)

(*s Variables. *)

let compute_var_implicits flags manual id =
  let env = Global.env () in
  let (_,_,ty) = lookup_named id env in
  compute_semi_auto_implicits env flags manual ty

(* Implicits of a global reference. *)

let compute_global_implicits flags manual = function
  | VarRef id -> compute_var_implicits flags manual id
  | ConstRef kn -> compute_constant_implicits flags manual kn
  | IndRef (kn,i) ->
      let ((_,imps),_) = (compute_mib_implicits flags manual kn).(i) in imps
  | ConstructRef ((kn,i),j) ->
      let (_,cimps) = (compute_mib_implicits flags manual kn).(i) in snd cimps.(j-1)

(* Merge a manual explicitation with an implicit_status list *)

let merge_impls (cond,oldimpls) (_,newimpls) =
  let oldimpls,usersuffiximpls = list_chop (List.length newimpls) oldimpls in
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
  | ImplConstant of constant * implicits_flags
  | ImplMutualInductive of mutual_inductive * implicits_flags
  | ImplInteractive of global_reference * implicits_flags *
      implicit_interactive_request

let implicits_table = ref Refmap.empty

let implicits_of_global ref =
  try Refmap.find ref !implicits_table with Not_found -> [DefaultImpArgs,[]]

let cache_implicits_decl (ref,imps) =
  implicits_table := Refmap.add ref imps !implicits_table

let load_implicits _ (_,(_,l)) = List.iter cache_implicits_decl l

let cache_implicits o =
  load_implicits 1 o

let subst_implicits_decl subst (r,imps as o) =
  let r' = fst (subst_global subst r) in if r==r' then o else (r',imps)

let subst_implicits (subst,(req,l)) =
  (ImplLocal,list_smartmap (subst_implicits_decl subst) l)

let impls_of_context ctx =
  List.rev_map (fun (id,impl,_,_) -> if impl = Lib.Implicit then Some (id, Manual, (true,true)) else None)
    (List.filter (fun (_,_,b,_) -> b = None) ctx)

let section_segment_of_reference = function
  | ConstRef con -> section_segment_of_constant con
  | IndRef (kn,_) | ConstructRef ((kn,_),_) ->
      section_segment_of_mutual_inductive kn
  | _ -> []

let adjust_side_condition p = function
  | LessArgsThan n -> LessArgsThan (n+p)
  | DefaultImpArgs -> DefaultImpArgs

let add_section_impls vars extra_impls (cond,impls) =
  let p = List.length vars - List.length extra_impls in
  adjust_side_condition p cond, extra_impls @ impls

let discharge_implicits (_,(req,l)) =
  match req with
  | ImplLocal -> None
  | ImplInteractive (ref,flags,exp) ->
      let vars = section_segment_of_reference ref in
      let ref' = if isVarRef ref then ref else pop_global_reference ref in
      let extra_impls = impls_of_context vars in
      let l' = [ref', List.map (add_section_impls vars extra_impls) (snd (List.hd l))] in
      Some (ImplInteractive (ref',flags,exp),l')
  | ImplConstant (con,flags) ->
      let con' = pop_con con in
      let vars = section_segment_of_constant con in
      let extra_impls = impls_of_context vars in
      let l' = [ConstRef con',List.map (add_section_impls vars extra_impls) (snd (List.hd l))] in
	Some (ImplConstant (con',flags),l')
  | ImplMutualInductive (kn,flags) ->
      let l' = List.map (fun (gr, l) ->
	let vars = section_segment_of_reference gr in
	let extra_impls = impls_of_context vars in
	((if isVarRef gr then gr else pop_global_reference gr),
	 List.map (add_section_impls vars extra_impls) l)) l
      in
	Some (ImplMutualInductive (pop_kn kn,flags),l')

let rebuild_implicits (req,l) =
  match req with
  | ImplLocal -> assert false
  | ImplConstant (con,flags) ->
      let oldimpls = snd (List.hd l) in
      let newimpls = compute_constant_implicits flags [] con in
      req, [ConstRef con, List.map2 merge_impls oldimpls newimpls]
  | ImplMutualInductive (kn,flags) ->
      let newimpls = compute_all_mib_implicits flags [] kn in
      let rec aux olds news =
	match olds, news with
	| (_, oldimpls) :: old, (gr, newimpls) :: tl ->
	    (gr, List.map2 merge_impls oldimpls newimpls) :: aux old tl
	| [], [] -> []
	| _, _ -> assert false
      in req, aux l newimpls

  | ImplInteractive (ref,flags,o) ->
      (if isVarRef ref && is_in_section ref then ImplLocal else req),
      match o with
      | ImplAuto ->
	  let oldimpls = snd (List.hd l) in
	  let newimpls = compute_global_implicits flags [] ref in
	    [ref,List.map2 merge_impls oldimpls newimpls]
      | ImplManual userimplsize ->
	  let oldimpls = snd (List.hd l) in
	  if flags.auto then
	    let newimpls = List.hd (compute_global_implicits flags [] ref) in
	    let p = List.length (snd newimpls) - userimplsize in
	    let newimpls = on_snd (list_firstn p) newimpls in
	    [ref,List.map (fun o -> merge_impls o newimpls) oldimpls]
	  else
	    [ref,oldimpls]

let classify_implicits (req,_ as obj) =
  if req = ImplLocal then Dispose else Substitute obj

let inImplicits =
  declare_object {(default_object "IMPLICITS") with
    cache_function = cache_implicits;
    load_function = load_implicits;
    subst_function = subst_implicits;
    classify_function = classify_implicits;
    discharge_function = discharge_implicits;
    rebuild_function = rebuild_implicits }

let is_local local ref = local || isVarRef ref && is_in_section ref

let declare_implicits_gen req flags ref =
  let imps = compute_global_implicits flags [] ref in
  add_anonymous_leaf (inImplicits (req,[ref,imps]))

let declare_implicits local ref =
  let flags = { !implicit_args with auto = true } in
  let req =
    if is_local local ref then ImplLocal else ImplInteractive(ref,flags,ImplAuto) in
    declare_implicits_gen req flags ref

let declare_var_implicits id =
  let flags = !implicit_args in
    declare_implicits_gen ImplLocal flags (VarRef id)

let declare_constant_implicits con =
  let flags = !implicit_args in
    declare_implicits_gen (ImplConstant (con,flags)) flags (ConstRef con)

let declare_mib_implicits kn =
  let flags = !implicit_args in
  let imps = array_map_to_list
    (fun (ind,cstrs) -> ind::(Array.to_list cstrs))
    (compute_mib_implicits flags [] kn) in
    add_anonymous_leaf
      (inImplicits (ImplMutualInductive (kn,flags),List.flatten imps))

(* Declare manual implicits *)
type manual_explicitation = Topconstr.explicitation * (bool * bool * bool)

type manual_implicits = manual_explicitation list

let compute_implicits_with_manual env typ enriching l =
  let _,autoimpls = compute_auto_implicits env !implicit_args enriching typ in
  set_manual_implicits env !implicit_args enriching autoimpls l

let check_inclusion l =
  (* Check strict inclusion *)
  let rec aux = function
    | n1::(n2::_ as nl) ->
	if n1 <= n2 then
	  error "Sequences of implicit arguments must be of different lengths";
	aux nl
    | _ -> () in
  aux (List.map (fun (imps,_) -> List.length imps) l)

let check_rigidity isrigid =
  if not isrigid then
    errorlabstrm "" (strbrk "Multiple sequences of implicit arguments available only for references that cannot be applied to an arbitrarily large number of arguments.")

let declare_manual_implicits local ref ?enriching l =
  let flags = !implicit_args in
  let env = Global.env () in
  let t = Global.type_of_global ref in
  let enriching = Option.default flags.auto enriching in
  let isrigid,autoimpls = compute_auto_implicits env flags enriching t in
  let l' = match l with
    | [] -> assert false
    | [l] ->
	[DefaultImpArgs, set_manual_implicits env flags enriching autoimpls l]
    | _ ->
	check_rigidity isrigid;
	let l = List.map (fun imps -> (imps,List.length imps)) l in
	let l = Sort.list (fun (_,n1) (_,n2) -> n1 > n2) l in
	check_inclusion l;
	let nargs = List.length autoimpls in
	List.map (fun (imps,n) ->
	  (LessArgsThan (nargs-n),
	   set_manual_implicits env flags enriching autoimpls imps)) l in
  let req =
    if is_local local ref then ImplLocal
    else ImplInteractive(ref,flags,ImplManual (List.length autoimpls))
  in
    add_anonymous_leaf (inImplicits (req,[ref,l']))

let maybe_declare_manual_implicits local ref ?enriching l =
  if l = [] then ()
  else declare_manual_implicits local ref ?enriching [l]

let extract_impargs_data impls =
  let rec aux p = function
    | (DefaultImpArgs, imps)::_ -> [None,imps]
    | (LessArgsThan n, imps)::l -> (Some (p,n),imps) :: aux (n+1) l
    | [] -> [] in
  aux 0 impls

let lift_implicits n =
  List.map (fun x ->
    match fst x with
	ExplByPos (k, id) -> ExplByPos (k + n, id), snd x
      | _ -> x)

let make_implicits_list l = [DefaultImpArgs, l]

let rec drop_first_implicits p l =
  if p = 0 then l else match l with
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

let rec select_stronger_impargs = function
  | [] -> [] (* Tolerance for (DefaultImpArgs,[]) *)
  | (_,impls)::_ -> impls

(*s Registration as global tables *)

let init () = implicits_table := Refmap.empty
let freeze () = !implicits_table
let unfreeze t = implicits_table := t

let _ =
  Summary.declare_summary "implicits"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }
