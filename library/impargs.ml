(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

(*s Calcul arguments implicites *)

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

(* Set this to true to have arguments inferable from conclusion only implicit*)
let conclusion_matters = false

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
  in Some e

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

(* [iter_constr_with_full_binders g f acc c] iters [f acc] on the immediate
   subterms of [c]; it carries an extra data [acc] which is processed by [g] at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let iter_constr_with_full_binders g f l c = match kind_of_term c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> ()
  | Cast (c,t) -> f l c; f l t
  | Prod (na,t,c) -> f l t; f (g (na,None,t) l) c
  | Lambda (na,t,c) -> f l t; f (g (na,None,t) l) c
  | LetIn (na,b,t,c) -> f l b; f l t; f (g (na,Some b,t) l) c
  | App (c,args) -> f l c; Array.iter (f l) args
  | Evar (_,args) -> Array.iter (f l) args
  | Case (_,p,c,bl) -> f l p; f l c; Array.iter (f l) bl
  | Fix (_,(lna,tl,bl)) -> 
      let l' = array_fold_left2 (fun l na t -> g (na,None,t) l) l lna tl in
      Array.iter (f l) tl;
      Array.iter (f l') bl
  | CoFix (_,(lna,tl,bl)) ->
      let l' = array_fold_left2 (fun l na t -> g (na,None,t) l) l lna tl in
      Array.iter (f l) tl;
      Array.iter (f l') bl

let push_lift d (e,n) = (push_rel d e,n+1)

(* Precondition: rels in env are for inductive types only *)
let add_free_rels_until bound env m pos acc =
  let rec frec rig (env,depth as ed) c =
    match kind_of_term (whd_betadeltaiota env c) with
    | Rel n when (n < bound+depth) & (n >= depth) ->
        acc.(bound+depth-n-1) <- update pos rig (acc.(bound+depth-n-1))
    | App (f,_) when rig & is_flexible_reference env bound depth f ->
        iter_constr_with_full_binders push_lift (frec false) ed c
    | Case _ when rig ->
        iter_constr_with_full_binders push_lift (frec false) ed c
    | _ ->
        iter_constr_with_full_binders push_lift (frec rig) ed c
  in 
  frec true (env,1) m; acc

(* calcule la liste des arguments implicites *)

let compute_implicits env t =
  let rec aux env n t =
    let t = whd_betadeltaiota env t in
    match kind_of_term t with
      | Prod (x,a,b) ->
	  add_free_rels_until n env a (Hyp (n+1))
            (aux (push_rel (x,None,a) env) (n+1) b)
      | _ -> 
          add_free_rels_until n env t Conclusion (Array.create n None)
  in 
  match kind_of_term (whd_betadeltaiota env t) with 
    | Prod (x,a,b) ->
	Array.to_list (aux (push_rel (x,None,a) env) 1 b)
    | _ -> []

type implicit_status = implicit_explanation option (* None = Not implicit *)

type implicits_list = implicit_status list

let is_status_implicit = function
  | None -> false
  | Some (DepRigid Conclusion) -> conclusion_matters
  | Some (DepFlex Conclusion) -> conclusion_matters
  | _ -> true

let is_inferable_implicit n = function
  | None -> false
  | Some (DepRigid (Hyp p)) -> n >= p
  | Some (DepFlex (Hyp p)) -> false
  | Some (DepFlexAndRigid (_,Hyp q)) -> n >= q
  | Some (DepRigid Conclusion) -> conclusion_matters
  | Some (DepFlex Conclusion) -> false
  | Some (DepFlexAndRigid (_,Conclusion)) -> false
  | Some Manual -> true

let positions_of_implicits =
  let rec aux n = function
      [] -> []
    | Some _::l -> n :: aux (n+1) l
    | None::l -> aux (n+1) l
  in aux 1

type implicits =
  | Impl_auto of implicits_list
  | Impl_manual of implicits_list
  | No_impl

let implicit_args = ref false

let make_implicit_args flag = implicit_args := flag
let is_implicit_args () = !implicit_args

let with_implicits b f x =
  let oimplicit = !implicit_args in
  try 
    implicit_args := b;
    let rslt = f x in 
    implicit_args := oimplicit;
    rslt
  with e -> begin
    implicit_args := oimplicit;
    raise e
  end

let implicitly f = with_implicits true f

let using_implicits = function
  | No_impl -> with_implicits false
  | _ -> with_implicits true

let auto_implicits env ty = Impl_auto (compute_implicits env ty)

let list_of_implicits = function 
  | Impl_auto l -> l
  | Impl_manual l -> l
  | No_impl -> []

(*s Constants. *)

let constants_table = ref KNmap.empty

let compute_constant_implicits kn =
  let env = Global.env () in
  let cb = lookup_constant kn env in
  auto_implicits env (body_of_type cb.const_type)

let cache_constant_implicits (_,(kn,imps)) = 
  constants_table := KNmap.add kn imps !constants_table

let subst_constant_implicits (_,subst,(kn,imps as obj)) = 
  let kn' = subst_kn subst kn in
    if kn' == kn then obj else
      kn',imps

let (in_constant_implicits, _) =
  declare_object {(default_object "CONSTANT-IMPLICITS") with
    cache_function = cache_constant_implicits;
    load_function = (fun _ -> cache_constant_implicits);
    subst_function = subst_constant_implicits;
    classify_function = (fun (_,x) -> Substitute x);
    export_function = (fun x -> Some x) }

let declare_constant_implicits kn =
  let imps = compute_constant_implicits kn in
  add_anonymous_leaf (in_constant_implicits (kn,imps))

let constant_implicits sp =
  try KNmap.find sp !constants_table with Not_found -> No_impl

let constant_implicits_list sp =
  list_of_implicits (constant_implicits sp)

(*s Inductives and constructors. Their implicit arguments are stored
   in an array, indexed by the inductive number, of pairs $(i,v)$ where
   $i$ are the implicit arguments of the inductive and $v$ the array of 
   implicit arguments of the constructors. *)

module Inductive_path = struct
  type t = inductive
  let compare (spx,ix) (spy,iy) = 
    let c = ix - iy in if c = 0 then compare spx spy else c
end

module Indmap = Map.Make(Inductive_path)

let inductives_table = ref Indmap.empty

module Construtor_path = struct
  type t = constructor
  let compare (indx,ix) (indy,iy) = 
    let c = ix - iy in if c = 0 then Inductive_path.compare indx indy else c
end

module Constrmap = Map.Make(Construtor_path)

let inductives_table = ref Indmap.empty

let constructors_table = ref Constrmap.empty

let cache_inductive_implicits (_,(indp,imps)) =
  inductives_table := Indmap.add indp imps !inductives_table

let subst_inductive_implicits (_,subst,((kn,i),imps as obj)) = 
  let kn' = subst_kn subst kn in
    if kn' == kn then obj else
      (kn',i),imps

let (in_inductive_implicits, _) =
  declare_object {(default_object "INDUCTIVE-IMPLICITS") with 
    cache_function = cache_inductive_implicits;
    load_function = (fun _ -> cache_inductive_implicits);
    subst_function = subst_inductive_implicits;
    classify_function = (fun (_,x) -> Substitute x);
    export_function = (fun x -> Some x)  }

let cache_constructor_implicits (_,(consp,imps)) =
  constructors_table := Constrmap.add consp imps !constructors_table

let subst_constructor_implicits (_,subst,(((kn,i),j),imps as obj)) = 
  let kn' = subst_kn subst kn in
    if kn' == kn then obj else
      ((kn',i),j),imps


let (in_constructor_implicits, _) =
  declare_object {(default_object "CONSTRUCTOR-IMPLICITS") with 
    cache_function = cache_constructor_implicits;
    load_function = (fun _ -> cache_constructor_implicits);
    subst_function = subst_constructor_implicits;
    classify_function = (fun (_,x) -> Substitute x);
    export_function = (fun x -> Some x)  }


let compute_mib_implicits kn =
  let env = Global.env () in
  let mib = lookup_mind kn env in
  let ar =
    Array.to_list
      (Array.map  (* No need to lift, arities contain no de Bruijn *)
        (fun mip -> (Name mip.mind_typename, None, mip.mind_user_arity))
        mib.mind_packets) in
  let env_ar = push_rel_context ar env in
  let imps_one_inductive mip =
    (auto_implicits env (body_of_type mip.mind_user_arity),
     Array.map (fun c -> auto_implicits env_ar (body_of_type c))
       mip.mind_user_lc)
  in
  Array.map imps_one_inductive mib.mind_packets

let cache_mib_implicits (_,(kn,mibimps)) =
  Array.iteri
    (fun i (imps,v) ->
       let indp = (kn,i) in
       inductives_table := Indmap.add indp imps !inductives_table;
       Array.iteri 
	 (fun j imps ->
	    constructors_table := 
	      Constrmap.add (indp,succ j) imps !constructors_table) v)
    mibimps

let subst_mib_implicits (_,subst,(kn,mibimps as obj)) = 
  let kn' = subst_kn subst kn in
    if kn' == kn then obj else
      kn',mibimps

let (in_mib_implicits, _) =
  declare_object {(default_object "MIB-IMPLICITS") with 
    cache_function = cache_mib_implicits;
    load_function = (fun _ -> cache_mib_implicits);
    subst_function = subst_mib_implicits;
    classify_function = (fun (_,x) -> Substitute x);
    export_function = (fun x -> Some x)  }
 
let declare_mib_implicits kn =
  let imps = compute_mib_implicits kn in
  add_anonymous_leaf (in_mib_implicits (kn,imps))

let inductive_implicits indp =
  try Indmap.find indp !inductives_table with Not_found -> No_impl

let constructor_implicits consp =
  try Constrmap.find consp !constructors_table with Not_found -> No_impl

let constructor_implicits_list constr_sp = 
  list_of_implicits (constructor_implicits constr_sp)

let inductive_implicits_list ind_sp =
  list_of_implicits (inductive_implicits ind_sp)

(*s Variables. *)

let var_table = ref Idmap.empty

let compute_var_implicits id =
  let env = Global.env () in
  let (_,_,ty) = lookup_named id env in
  auto_implicits env ty

let cache_var_implicits (_,(id,imps)) =
  var_table := Idmap.add id imps !var_table

let (in_var_implicits, _) =
  declare_object {(default_object "VARIABLE-IMPLICITS") with 
    cache_function = cache_var_implicits;
    load_function = (fun _ -> cache_var_implicits);
    export_function = (fun x -> Some x)  }



let declare_var_implicits id =
  let imps = compute_var_implicits id in
  add_anonymous_leaf (in_var_implicits (id,imps))

let implicits_of_var id =
  list_of_implicits (try Idmap.find id !var_table with Not_found -> No_impl)

(*s Implicits of a global reference. *)

let declare_implicits = function
  | VarRef id -> 
      declare_var_implicits id
  | ConstRef kn -> 
      declare_constant_implicits kn
  | IndRef ((kn,i) as indp) -> 
      let mib_imps = compute_mib_implicits kn in
      let imps = fst mib_imps.(i) in
      add_anonymous_leaf (in_inductive_implicits (indp, imps))
  | ConstructRef (((kn,i),j) as consp) -> 
      let mib_imps = compute_mib_implicits kn in
      let imps = (snd mib_imps.(i)).(j-1) in
      add_anonymous_leaf (in_constructor_implicits (consp, imps))

let context_of_global_reference = function
  | VarRef sp -> []
  | ConstRef sp -> (Global.lookup_constant sp).const_hyps
  | IndRef (sp,_) -> (Global.lookup_mind sp).mind_hyps
  | ConstructRef ((sp,_),_) -> (Global.lookup_mind sp).mind_hyps

let check_range n i =
  if i<1 or i>n then error ("Bad argument number: "^(string_of_int i))

let declare_manual_implicits r l =
  let t = Global.type_of_global r in
  let n = List.length (fst (dest_prod (Global.env()) t)) in
  if not (list_distinct l) then error ("Some numbers occur several time");
  List.iter (check_range n) l;
  let l = List.sort (-) l in
  let rec aux k = function
    | [] -> if k>n then [] else None :: aux (k+1) []
    | p::l as l' ->
        if k=p then Some Manual :: aux (k+1) l else None :: aux (k+1) l'
  in let l = Impl_manual (aux 1 l) in
  match r with
  | VarRef id -> 
      add_anonymous_leaf (in_var_implicits (id,l))
  | ConstRef sp ->
      add_anonymous_leaf (in_constant_implicits (sp,l))
  | IndRef indp ->
      add_anonymous_leaf (in_inductive_implicits (indp,l))
  | ConstructRef consp -> 
      add_anonymous_leaf (in_constructor_implicits (consp,l))

(*s Tests if declared implicit *)

let is_implicit_constant sp =
  try let _ = KNmap.find sp !constants_table in true with Not_found -> false

let is_implicit_inductive_definition indp =
  try let _ = Indmap.find indp !inductives_table in true 
  with Not_found -> false

let is_implicit_var id =
  try let _ = Idmap.find id !var_table in true with Not_found -> false

let implicits_of_global = function
  | VarRef id -> implicits_of_var id
  | ConstRef sp -> list_of_implicits (constant_implicits sp)
  | IndRef isp -> list_of_implicits (inductive_implicits isp)
  | ConstructRef csp ->	list_of_implicits (constructor_implicits csp)

(*s Registration as global tables and rollback. *)

type frozen_t = implicits KNmap.t 
              * implicits Indmap.t 
	      * implicits Constrmap.t
              * implicits Idmap.t

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
      Summary.survive_section = false }

let rollback f x =
  let fs = freeze () in
  try f x with e -> begin unfreeze fs; raise e end
