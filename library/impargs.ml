(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

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
open Termops
open Topconstr

(*s Flags governing the computation of implicit arguments *)

type implicits_flags = {
  main : bool;
  strict : bool;                   (* true = strict *)
  strongly_strict : bool;            (* true = strongly strict *)
  reversible_pattern : bool;
  contextual : bool;               (* true = contextual *)
  maximal : bool
}

(* les implicites sont stricts par défaut en v8 *)

let implicit_args = ref { 
  main = false;
  strict = true;
  strongly_strict = false;
  reversible_pattern = false;
  contextual = false;
  maximal = false;
}

let make_implicit_args flag =
  implicit_args := { !implicit_args with main = flag }

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

let is_implicit_args () = !implicit_args.main
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

(* We remember various information about why an argument is (automatically)
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
  | Manual of bool

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
      | Some (Manual _) -> assert false
  else
    match st with
      | None -> DepFlex pos
      | Some (DepRigid rpos as x) ->
          if argument_less (pos,rpos) then DepFlexAndRigid (pos,rpos) else x
      | Some (DepFlexAndRigid (fpos,rpos) as x) ->
          if argument_less (pos,fpos) then DepFlexAndRigid (pos,rpos) else x
      | Some (DepFlex fpos as x) ->
          if argument_less (pos,fpos) then DepFlex pos else x
      | Some (Manual _) -> assert false
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

(* calcule la liste des arguments implicites *)

let concrete_name avoid_flags l env_names n all c =
  if n = Anonymous & noccurn 1 c then
    (Anonymous,l)
  else
    let fresh_id = next_name_not_occuring avoid_flags n l env_names c in
    let idopt = if not all && noccurn 1 c then Anonymous else Name fresh_id in
    (idopt, fresh_id::l)

let compute_implicits_gen strict strongly_strict revpat contextual all env t =
  let rec aux env avoid n names t =
    let t = whd_betadeltaiota env t in
    match kind_of_term t with
      | Prod (na,a,b) ->
	  let na',avoid' = concrete_name None avoid names na all b in
	  add_free_rels_until strict strongly_strict revpat n env a (Hyp (n+1))
            (aux (push_rel (na',None,a) env) avoid' (n+1) (na'::names) b)
      | _ -> 
	  let names = List.rev names in
	  let v = Array.map (fun na -> na,None) (Array.of_list names) in
	  if contextual then
	    add_free_rels_until strict strongly_strict revpat n env t Conclusion v
	  else v
  in 
  match kind_of_term (whd_betadeltaiota env t) with 
    | Prod (na,a,b) ->
	let na',avoid = concrete_name None [] [] na all b in
	let v = aux (push_rel (na',None,a) env) avoid 1 [na'] b in
	Array.to_list v
    | _ -> []

let rec prepare_implicits f = function
  | [] -> []
  | (Anonymous, Some _)::_ -> anomaly "Unnamed implicit"
  | (Name id, Some imp)::imps -> 
      let imps' = prepare_implicits f imps in
      Some (id,imp,set_maximality imps' f.maximal) :: imps'
  | _::imps -> None :: prepare_implicits f imps

let compute_implicits_flags env f all t = 
  compute_implicits_gen 
    f.strict f.strongly_strict f.reversible_pattern f.contextual all env t
    
let compute_implicits_auto env f t =
  let l = compute_implicits_flags env f false t in
    prepare_implicits f l

let compute_implicits env t = compute_implicits_auto env !implicit_args t

let set_implicit id imp insmax =
  (id,(match imp with None -> Manual false | Some imp -> imp),insmax)

let merge_imps f = function 
    None -> Some (Manual f)
  | x -> x

let rec assoc_by_pos k = function
    (ExplByPos (k', x), b) :: tl when k = k' -> (x,b), tl
  | hd :: tl -> let (x, tl) = assoc_by_pos k tl in x, hd :: tl
  | [] -> raise Not_found

let compute_manual_implicits flags env t enriching l =
  let autoimps =
    if enriching then compute_implicits_flags env flags true t
    else compute_implicits_gen false false false true true env t in
  let n = List.length autoimps in
  let try_forced k l =
    try 
      let (id, (b, f)), l' = assoc_by_pos k l in
	if f then
	  let id = match id with Some id -> id | None -> id_of_string ("arg_" ^ string_of_int k) in
	    l', Some (id,Manual f,b)
	else l, None
    with Not_found -> l, None
  in
  if not (list_distinct l) then 
    error ("Some parameters are referred more than once");
  (* Compare with automatic implicits to recover printing data and names *)
  let rec merge k l = function
  | (Name id,imp)::imps ->
      let l',imp,m =
	try 
	  let (b, f) = List.assoc (ExplByName id) l in
	  List.remove_assoc (ExplByName id) l, merge_imps f imp,Some b
	with Not_found ->
	try 
	  let (id, (b, f)), l' = assoc_by_pos k l in
	    l', merge_imps f imp,Some b
	with Not_found ->
	  l,imp, if enriching && imp <> None then Some flags.maximal else None
      in
      let imps' = merge (k+1) l' imps in
      let m = Option.map (set_maximality imps') m in
      Option.map (set_implicit id imp) m :: imps'
  | (Anonymous,imp)::imps ->
      let l', forced = try_forced k l in
	forced :: merge (k+1) l' imps
  | [] when l = [] -> []
  | [] ->
      match List.hd l with
	| ExplByName id,b ->
	      error ("Wrong or not dependent implicit argument name: "^(string_of_id id))
	| ExplByPos (i,_id),_t ->
	    if i<1 or i>n then 
	      error ("Bad implicit argument number: "^(string_of_int i))
	    else
	      errorlabstrm ""
		(str "Cannot set implicit argument number " ++ int i ++
		    str ": it has no name")
  in
  merge 1 l autoimps

type maximal_insertion = bool (* true = maximal contextual insertion *)

type implicit_status =
    (* None = Not implicit *)
    (identifier * implicit_explanation * maximal_insertion) option

type implicits_list = implicit_status list

let is_status_implicit = function
  | None -> false
  | _ -> true

let name_of_implicit = function
  | None -> anomaly "Not an implicit argument"
  | Some (id,_,_) -> id

let maximal_insertion_of = function
  | Some (_,_,b) -> b
  | None -> anomaly "Not an implicit argument"

let forced_implicit = function
  | Some (_,Manual b,_) -> b
  | _ -> false

(* [in_ctx] means we know the expected type, [n] is the index of the argument *)
let is_inferable_implicit in_ctx n = function
  | None -> false
  | Some (_,DepRigid (Hyp p),_) -> in_ctx or n >= p
  | Some (_,DepFlex (Hyp p),_) -> false
  | Some (_,DepFlexAndRigid (_,Hyp q),_) -> in_ctx or n >= q
  | Some (_,DepRigid Conclusion,_) -> in_ctx
  | Some (_,DepFlex Conclusion,_) -> false
  | Some (_,DepFlexAndRigid (_,Conclusion),_) -> in_ctx
  | Some (_,Manual _,_) -> true

let positions_of_implicits =
  let rec aux n = function
      [] -> []
    | Some _ :: l -> n :: aux (n+1) l
    | None :: l -> aux (n+1) l
  in aux 1

(*s Constants. *)

let compute_constant_implicits flags cst =
  let env = Global.env () in
  compute_implicits_auto env flags (Typeops.type_of_constant env cst)

(*s Inductives and constructors. Their implicit arguments are stored
   in an array, indexed by the inductive number, of pairs $(i,v)$ where
   $i$ are the implicit arguments of the inductive and $v$ the array of 
   implicit arguments of the constructors. *)

let compute_mib_implicits flags kn =
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
    ((IndRef ind,compute_implicits_auto env flags ar),
     Array.mapi (fun j c ->
       (ConstructRef (ind,j+1),compute_implicits_auto env_ar flags c))
       mip.mind_nf_lc)
  in
  Array.mapi imps_one_inductive mib.mind_packets

let compute_all_mib_implicits flags kn =
  let imps = compute_mib_implicits flags kn in
  List.flatten 
    (array_map_to_list (fun (ind,cstrs) -> ind::Array.to_list cstrs) imps)

(*s Variables. *)

let compute_var_implicits flags id =
  let env = Global.env () in
  let (_,_,ty) = lookup_named id env in
  compute_implicits_auto env flags ty

(* Implicits of a global reference. *)

let compute_global_implicits flags = function
  | VarRef id -> compute_var_implicits flags id
  | ConstRef kn -> compute_constant_implicits flags kn
  | IndRef (kn,i) -> 
      let ((_,imps),_) = (compute_mib_implicits flags kn).(i) in imps
  | ConstructRef ((kn,i),j) -> 
      let (_,cimps) = (compute_mib_implicits flags kn).(i) in snd cimps.(j-1)

(* Merge a manual explicitation with an implicit_status list *)

let list_split_at index l = 
  let rec aux i acc = function
      tl when i = index -> (List.rev acc), tl
    | hd :: tl -> aux (succ i) (hd :: acc) tl
    | [] -> failwith "list_split_at: Invalid argument"
  in aux 0 [] l
    
let merge_impls oimpls impls =
  let oimpls, _ = list_split_at (List.length oimpls - List.length impls) oimpls in
    oimpls @ impls

(* Caching implicits *)

type implicit_interactive_request =
  | ImplAuto
  | ImplManual of implicit_status list

type implicit_discharge_request =
  | ImplNoDischarge
  | ImplConstant of constant * implicits_flags
  | ImplMutualInductive of kernel_name * implicits_flags
  | ImplInteractive of global_reference * implicits_flags * 
      implicit_interactive_request

let implicits_table = ref Refmap.empty

let implicits_of_global ref =
  try Refmap.find ref !implicits_table with Not_found -> []

let cache_implicits_decl (ref,imps) =
  implicits_table := Refmap.add ref imps !implicits_table

let load_implicits _ (_,(_,l)) = List.iter cache_implicits_decl l

let cache_implicits o =
  load_implicits 1 o

let subst_implicits_decl subst (r,imps as o) =
  let r' = fst (subst_global subst r) in if r==r' then o else (r',imps)

let subst_implicits (_,subst,(req,l)) =
  (ImplNoDischarge,list_smartmap (subst_implicits_decl subst) l)

let discharge_implicits (_,(req,l)) =
  match req with
  | ImplNoDischarge -> None
  | ImplInteractive (ref,flags,exp) -> 
      Some (ImplInteractive (pop_global_reference ref,flags,exp),l)
  | ImplConstant (con,flags) ->
      Some (ImplConstant (pop_con con,flags),l)
  | ImplMutualInductive (kn,flags) ->
      Some (ImplMutualInductive (pop_kn kn,flags),l)

let rebuild_implicits (req,l) =
  let l' = match req with
  | ImplNoDischarge -> assert false
  | ImplConstant (con,flags) -> 
      [ConstRef con,compute_constant_implicits flags con]
  | ImplMutualInductive (kn,flags) ->
      compute_all_mib_implicits flags kn
  | ImplInteractive (ref,flags,o) ->
      match o with
      | ImplAuto -> [ref,compute_global_implicits flags ref]
      | ImplManual l -> 
	  let auto = compute_global_implicits flags ref in
	  let l' = merge_impls auto l in [ref,l']
  in (req,l')


let (inImplicits, _) =
  declare_object {(default_object "IMPLICITS") with 
    cache_function = cache_implicits;
    load_function = load_implicits;
    subst_function = subst_implicits;
    classify_function = (fun (_,x) -> Substitute x);
    discharge_function = discharge_implicits;
    rebuild_function = rebuild_implicits;
    export_function = (fun x -> Some x) }

let declare_implicits_gen req flags ref =
  let imps = compute_global_implicits flags ref in
  add_anonymous_leaf (inImplicits (req,[ref,imps]))

let declare_implicits local ref =
  let flags = { !implicit_args with main = true } in
  let req = 
    if local then ImplNoDischarge else ImplInteractive(ref,flags,ImplAuto) in
  declare_implicits_gen req flags ref

let declare_var_implicits id =
  if !implicit_args.main then
    declare_implicits_gen ImplNoDischarge !implicit_args (VarRef id)

let declare_constant_implicits con =
  if !implicit_args.main then
    let flags = !implicit_args in
    declare_implicits_gen (ImplConstant (con,flags)) flags (ConstRef con)

let declare_mib_implicits kn =
  if !implicit_args.main then
    let flags = !implicit_args in
    let imps = array_map_to_list
      (fun (ind,cstrs) -> ind::(Array.to_list cstrs))
      (compute_mib_implicits flags kn) in
    add_anonymous_leaf
      (inImplicits (ImplMutualInductive (kn,flags),List.flatten imps))

(* Declare manual implicits *)
type manual_explicitation = Topconstr.explicitation * (bool * bool) 

let compute_implicits_with_manual env typ enriching l = 
  compute_manual_implicits !implicit_args env typ enriching l

let declare_manual_implicits local ref enriching l =
  let flags = !implicit_args in
  let env = Global.env () in
  let t = Global.type_of_global ref in
  let l' = compute_manual_implicits flags env t enriching l in
  let req =
    if local or isVarRef ref then ImplNoDischarge
    else ImplInteractive(ref,flags,ImplManual l')
  in
    add_anonymous_leaf (inImplicits (req,[ref,l']))

(*s Registration as global tables *)

let init () = implicits_table := Refmap.empty
let freeze () = !implicits_table
let unfreeze t = implicits_table := t

let _ = 
  Summary.declare_summary "implicits"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_module = false;
      Summary.survive_section = false }
