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

(* les implicites sont stricts par défaut en v8 *)
let implicit_args = ref false
let strict_implicit_args = ref (not !Options.v7)
let contextual_implicit_args = ref false

let implicit_args_out = ref false
let strict_implicit_args_out = ref true
let contextual_implicit_args_out = ref false

let make_implicit_args flag =
  implicit_args := flag;
  if not !Options.v7_only then implicit_args_out := flag;
  if !Options.translate_strict_impargs then
    strict_implicit_args_out := not flag

let make_strict_implicit_args flag =
  strict_implicit_args := flag;
  if not !Options.v7_only then strict_implicit_args_out := flag

let make_contextual_implicit_args flag =
  contextual_implicit_args := flag;
  if not !Options.v7_only then contextual_implicit_args_out := flag

let is_implicit_args () = !implicit_args
let is_implicit_args_out () = !implicit_args_out
let is_strict_implicit_args () = !strict_implicit_args
let is_contextual_implicit_args () = !contextual_implicit_args

type implicits_flags = (bool * bool * bool) * (bool * bool * bool)

let with_implicits ((a,b,c),(d,e,g)) f x =
  let oa = !implicit_args in
  let ob = !strict_implicit_args in
  let oc = !contextual_implicit_args in
  let od = !implicit_args_out in
  let oe = !strict_implicit_args_out in
  let og = !contextual_implicit_args_out in
  try 
    implicit_args := a;
    strict_implicit_args := b;
    contextual_implicit_args := c;
    implicit_args_out := d;
    strict_implicit_args_out := e;
    contextual_implicit_args_out := g;
    let rslt = f x in 
    implicit_args := oa;
    strict_implicit_args := ob;
    contextual_implicit_args := oc;
    implicit_args_out := od;
    strict_implicit_args_out := oe;
    contextual_implicit_args_out := og;
    rslt
  with e -> begin
    implicit_args := oa;
    strict_implicit_args := ob;
    contextual_implicit_args := oc;
    implicit_args_out := od;
    strict_implicit_args_out := oe;
    contextual_implicit_args_out := og;
    raise e
  end

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
      | Some (DepFlex fpos as x) ->
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

(* Precondition: rels in env are for inductive types only *)
let add_free_rels_until strict bound env m pos acc =
  let rec frec rig (env,depth as ed) c =
    match kind_of_term (whd_betadeltaiota env c) with
    | Rel n when (n < bound+depth) & (n >= depth) ->
        acc.(bound+depth-n-1) <- update pos rig (acc.(bound+depth-n-1))
    | App (f,_) when rig & is_flexible_reference env bound depth f ->
	if strict then () else
          iter_constr_with_full_binders push_lift (frec false) ed c
    | Case _ when rig ->
	if strict then () else
          iter_constr_with_full_binders push_lift (frec false) ed c
    | _ ->
        iter_constr_with_full_binders push_lift (frec rig) ed c
  in 
  frec true (env,1) m; acc

(* calcule la liste des arguments implicites *)

let my_concrete_name avoid names t = function
  | Anonymous -> Anonymous, avoid, Anonymous::names
  | na -> 
      let id = Termops.next_name_not_occuring false na avoid names t in
      Name id, id::avoid, Name id::names
  
let compute_implicits_gen strict contextual env t =
  let rec aux env avoid n names t =
    let t = whd_betadeltaiota env t in
    match kind_of_term t with
      | Prod (na,a,b) ->
	  let na',avoid' = Termops.concrete_name false avoid names na b in
	  add_free_rels_until strict n env a (Hyp (n+1))
            (aux (push_rel (na',None,a) env) avoid' (n+1) (na'::names) b)
      | _ -> 
	  let names = List.rev names in
	  let v = Array.map (fun na -> na,None) (Array.of_list names) in
	  if contextual then add_free_rels_until strict n env t Conclusion v
	  else v
  in 
  match kind_of_term (whd_betadeltaiota env t) with 
    | Prod (na,a,b) ->
	let na',avoid = Termops.concrete_name false [] [] na b in
	let v = aux (push_rel (na',None,a) env) avoid 1 [na'] b in
	Array.to_list v
    | _ -> []

let compute_implicits output env t =
  let strict =
    (not output & !strict_implicit_args) or
    (output & !strict_implicit_args_out) in 
  let contextual =
    (not output & !contextual_implicit_args) or
    (output & !contextual_implicit_args_out) in
  let l = compute_implicits_gen strict contextual env t in
  List.map (function
    | (Name id, Some imp) -> Some (id,imp)
    | (Anonymous, Some _) -> anomaly "Unnamed implicit"
    | _ -> None) l

type implicit_status =
    (* None = Not implicit *)
    (identifier * implicit_explanation) option

type implicits_list = implicit_status list

let is_status_implicit = function
  | None -> false
  | _ -> true

let name_of_implicit = function
  | None -> anomaly "Not an implicit argument"
  | Some (id,_) -> id

(* [in_ctx] means we now the expected type, [n] is the index of the argument *)
let is_inferable_implicit in_ctx n = function
  | None -> false
  | Some (_,DepRigid (Hyp p)) -> n >= p
  | Some (_,DepFlex (Hyp p)) -> false
  | Some (_,DepFlexAndRigid (_,Hyp q)) -> n >= q
  | Some (_,DepRigid Conclusion) -> in_ctx
  | Some (_,DepFlex Conclusion) -> false
  | Some (_,DepFlexAndRigid (_,Conclusion)) -> false
  | Some (_,Manual) -> true

let positions_of_implicits =
  let rec aux n = function
      [] -> []
    | Some _ :: l -> n :: aux (n+1) l
    | None :: l -> aux (n+1) l
  in aux 1

type strict_flag = bool     (* true = strict *)
type contextual_flag = bool (* true = contextual *)

type implicits =
  | Impl_auto of strict_flag * contextual_flag * implicits_list
  | Impl_manual of implicits_list
  | No_impl

let auto_implicits env ty =
  let impl = 
    if !implicit_args then
      let l = compute_implicits false env ty in
      Impl_auto (!strict_implicit_args,!contextual_implicit_args,l)
    else
      No_impl in
  if Options.do_translate () then
    impl, 
    if !implicit_args_out then 
      (let l = compute_implicits true env ty in
      Impl_auto (!strict_implicit_args_out,!contextual_implicit_args_out,l))
    else No_impl
  else 
    impl, impl

let list_of_implicits = function 
  | Impl_auto (_,_,l) -> l
  | Impl_manual l -> l
  | No_impl -> []

(*s Constants. *)

let constants_table = ref KNmap.empty

let compute_constant_implicits kn =
  let env = Global.env () in
  let cb = lookup_constant kn env in
  auto_implicits env (body_of_type cb.const_type)

let constant_implicits sp =
  try KNmap.find sp !constants_table with Not_found -> No_impl,No_impl

(*s Inductives and constructors. Their implicit arguments are stored
   in an array, indexed by the inductive number, of pairs $(i,v)$ where
   $i$ are the implicit arguments of the inductive and $v$ the array of 
   implicit arguments of the constructors. *)

let inductives_table = ref Indmap.empty

let constructors_table = ref Constrmap.empty

let compute_mib_implicits kn =
  let env = Global.env () in
  let mib = lookup_mind kn env in
  let ar =
    Array.to_list
      (Array.map  (* No need to lift, arities contain no de Bruijn *)
        (fun mip -> (Name mip.mind_typename, None, mip.mind_user_arity))
        mib.mind_packets) in
  let env_ar = push_rel_context ar env in
  let imps_one_inductive i mip =
    let ind = (kn,i) in
    ((IndRef ind,auto_implicits env (body_of_type mip.mind_user_arity)),
     Array.mapi (fun j c -> (ConstructRef (ind,j+1),auto_implicits env_ar c))
       mip.mind_user_lc)
  in
  Array.mapi imps_one_inductive mib.mind_packets

let inductive_implicits indp =
  try Indmap.find indp !inductives_table with Not_found -> No_impl,No_impl

let constructor_implicits consp =
  try Constrmap.find consp !constructors_table with Not_found -> No_impl,No_impl
(*s Variables. *)

let var_table = ref Idmap.empty

let compute_var_implicits id =
  let env = Global.env () in
  let (_,_,ty) = lookup_named id env in
  auto_implicits env ty

let var_implicits id = 
  try Idmap.find id !var_table with Not_found -> No_impl,No_impl

(* Caching implicits *)

let cache_implicits_decl (r,imps) =
  match r with
  | VarRef id -> 
      var_table := Idmap.add id imps !var_table
  | ConstRef kn ->
      constants_table := KNmap.add kn imps !constants_table
  | IndRef indp ->
      inductives_table := Indmap.add indp imps !inductives_table;
  | ConstructRef consp -> 
      constructors_table := Constrmap.add consp imps !constructors_table

let cache_implicits (_,l) = List.iter cache_implicits_decl l

let subst_implicits_decl subst (r,imps as o) =
  let r' = subst_global subst r in if r==r' then o else (r',imps)

let subst_implicits (_,subst,l) =
  list_smartmap (subst_implicits_decl subst) l

let (in_implicits, _) =
  declare_object {(default_object "IMPLICITS") with 
    cache_function = cache_implicits;
    load_function = (fun _ -> cache_implicits);
    subst_function = subst_implicits;
    classify_function = (fun (_,x) -> Substitute x);
    export_function = (fun x -> Some x) }

(* Implicits of a global reference. *)

let compute_global_implicits = function
  | VarRef id -> compute_var_implicits id
  | ConstRef kn -> compute_constant_implicits kn
  | IndRef (kn,i) -> 
      let ((_,imps),_) = (compute_mib_implicits kn).(i) in imps
  | ConstructRef ((kn,i),j) -> 
      let (_,cimps) = (compute_mib_implicits kn).(i) in snd cimps.(j-1)

let declare_implicits_gen r = 
  add_anonymous_leaf (in_implicits [r,compute_global_implicits r])

let declare_implicits r =
  with_implicits
    ((true,!strict_implicit_args,!contextual_implicit_args),
     (true,!strict_implicit_args_out,!contextual_implicit_args_out))
    declare_implicits_gen r

let declare_var_implicits id =
  if !implicit_args or !implicit_args_out then
    declare_implicits_gen (VarRef id)

let declare_constant_implicits kn =
  if !implicit_args or !implicit_args_out then
    declare_implicits_gen (ConstRef kn)

let declare_mib_implicits kn =
  if !implicit_args or !implicit_args_out then
  let imps = compute_mib_implicits kn in
  let imps = array_map_to_list
    (fun (ind,cstrs) -> ind::(Array.to_list cstrs)) imps in
  add_anonymous_leaf (in_implicits (List.flatten imps))

let implicits_of_global_gen = function
  | VarRef id -> var_implicits id
  | ConstRef sp -> constant_implicits sp
  | IndRef isp -> inductive_implicits isp
  | ConstructRef csp ->	constructor_implicits csp

let implicits_of_global r =
  let (imp_in,imp_out) = implicits_of_global_gen r in
  list_of_implicits imp_in

let implicits_of_global_out r =
  let (imp_in,imp_out) = implicits_of_global_gen r in
  list_of_implicits imp_out

(* Declare manual implicits *)

(*
let check_range n = function
  | loc,ExplByPos i ->
      if i<1 or i>n then error ("Bad argument number: "^(string_of_int i))
  | loc,ExplByName id ->
()
*)

let rec list_remove a = function
  | b::l when a = b -> l
  | b::l -> b::list_remove a l
  | [] -> raise Not_found

let set_implicit id imp =
  Some (id,match imp with None -> Manual | Some imp -> imp)

let declare_manual_implicits r l =
  let t = Global.type_of_global r in
  let autoimps = compute_implicits_gen false true (Global.env()) t in
  let n = List.length autoimps in
  if not (list_distinct l) then 
    error ("Some parameters are referred more than once");
(*  List.iter (check_range n) l;*)
(*  let l = List.sort (-) l in*)
  (* Compare with automatic implicits to recover printing data and names *)
  let rec merge k l = function
    | (Name id,imp)::imps ->
	let l',imp =
	  try list_remove (ExplByPos k) l, set_implicit id imp
	  with Not_found ->
	  try list_remove (ExplByName id) l, set_implicit id imp
	  with Not_found ->
	  l, None in
	imp :: merge (k+1) l' imps
    | (Anonymous,imp)::imps -> 
	None :: merge (k+1) l imps
    | [] when l = [] -> []
    | _ ->
	match List.hd l with
	| ExplByName id ->
	    error ("Wrong or not dependent implicit argument name: "^(string_of_id id))
	| ExplByPos i ->
	    if i<1 or i>n then 
	      error ("Bad implicit argument number: "^(string_of_int i))
	    else
	      errorlabstrm ""
		(str "Cannot set implicit argument number " ++ int i ++
		 str ": it has no name") in
  let l = Impl_manual (merge 1 l autoimps) in
  let (_,oimp_out) = implicits_of_global_gen r in
  let l = l, if !Options.v7_only then oimp_out else l in
  add_anonymous_leaf (in_implicits [r,l])

(* Tests if declared implicit *)

let test = function
  | No_impl | Impl_manual _ -> false,false,false
  | Impl_auto (s,c,_) -> true,s,c

let test_if_implicit find a =
  try let b,c = find a in test b, test c
  with Not_found -> (false,false,false),(false,false,false)
    
let is_implicit_constant sp =
  test_if_implicit (KNmap.find sp) !constants_table

let is_implicit_inductive_definition indp =
  test_if_implicit (Indmap.find (indp,0)) !inductives_table

let is_implicit_var id =
  test_if_implicit (Idmap.find id) !var_table

(*s Registration as global tables *)

let init () =
  constants_table := KNmap.empty;
  inductives_table := Indmap.empty;
  constructors_table := Constrmap.empty;
  var_table := Idmap.empty

let freeze () =
  (!constants_table, !inductives_table, 
   !constructors_table, !var_table)

let unfreeze (ct,it,const,vt) =
  constants_table := ct;
  inductives_table := it;
  constructors_table := const;
  var_table := vt

let _ = 
  Summary.declare_summary "implicits"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_module = false;
      Summary.survive_section = false }

(* Remark: flags implicit_args, contextual_implicit_args
   are synchronized by the general options mechanism - see Vernacentries *)

let init () =
  (* strict_implicit_args_out must be not !Options.v7 
     but init is done before parsing *)
  strict_implicit_args:=not !Options.v7;
  implicit_args_out:=false;
  (* strict_implicit_args_out needs to be not !Options.v7 or
     Options.do_translate() but init is done before parsing *)
  strict_implicit_args_out:=true;
  contextual_implicit_args_out:=false

let freeze () =
  (!strict_implicit_args,
   !implicit_args_out,!strict_implicit_args_out,!contextual_implicit_args_out)

let unfreeze (b,d,e,f) =
  strict_implicit_args := b;
  implicit_args_out := d;
  strict_implicit_args_out := e;
  contextual_implicit_args_out := f

let _ = 
  Summary.declare_summary "implicits-out-options"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_module = false;
      Summary.survive_section = true }
