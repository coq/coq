(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Amokrane Saïbi, Dec 1998 *)
(* Addition of products and sorts in canonical structures by Pierre
   Corbineau, Feb 2008 *)

(* This file registers properties of records: projections and
   canonical structures *)

open CErrors
open Util
open Pp
open Names
open Globnames
open Nametab
open Constr
open Libobject
open Mod_subst
open Reductionops

(*s A structure S is a non recursive inductive type with a single
   constructor (the name of which defaults to Build_S) *)

(* Table des structures: le nom de la structure (un [inductive]) donne
   le nom du constructeur, le nombre de paramètres et pour chaque
   argument réel du constructeur, le nom de la projection
   correspondante, si valide, et un booléen disant si c'est une vraie
   projection ou bien une fonction constante (associée à un LetIn) *)

type struc_typ = {
  s_CONST : constructor;
  s_EXPECTEDPARAM : int;
  s_PROJKIND : (Name.t * bool) list;
  s_PROJ : Constant.t option list }

let structure_table =
  Summary.ref (Indmap.empty : struc_typ Indmap.t) ~name:"record-structs"
let projection_table =
  Summary.ref (Cmap.empty : struc_typ Cmap.t) ~name:"record-projs"

(* TODO: could be unify struc_typ and struc_tuple ? in particular,
   is the inductive always (fst constructor) ? It seems so... *)

type struc_tuple =
    inductive * constructor * (Name.t * bool) list * Constant.t option list

let load_structure i (_,(ind,id,kl,projs)) =
  let open Declarations in
  let mib, mip = Global.lookup_inductive ind in
  let n = mib.mind_nparams in
  let struc =
    { s_CONST = id; s_EXPECTEDPARAM = n; s_PROJ = projs; s_PROJKIND = kl } in
  structure_table := Indmap.add ind struc !structure_table;
  projection_table :=
    List.fold_right (Option.fold_right (fun proj -> Cmap.add proj struc))
      projs !projection_table

let cache_structure o =
  load_structure 1 o

let subst_structure (subst,((kn,i),id,kl,projs as obj)) = 
  let kn' = subst_mind subst kn in
  let projs' =
   (* invariant: struc.s_PROJ is an evaluable reference. Thus we can take *)
   (* the first component of subst_con.                                   *)
   List.Smart.map
     (Option.Smart.map (fun kn -> fst (subst_con_kn subst kn)))
    projs
  in
  let id' = fst (subst_constructor subst id) in
    if projs' == projs && kn' == kn && id' == id then obj else
      ((kn',i),id',kl,projs')

let discharge_constructor (ind, n) =
  (Lib.discharge_inductive ind, n)

let discharge_structure (_,(ind,id,kl,projs)) =
  Some (Lib.discharge_inductive ind, discharge_constructor id, kl,
        List.map (Option.map Lib.discharge_con) projs)

let inStruc : struc_tuple -> obj =
  declare_object {(default_object "STRUCTURE") with
    cache_function = cache_structure;
    load_function = load_structure;
    subst_function = subst_structure;
    classify_function = (fun x -> Substitute x);
    discharge_function = discharge_structure }

let declare_structure (s,c,kl,pl) =
  Lib.add_anonymous_leaf (inStruc (s,c,kl,pl))

let lookup_structure indsp = Indmap.find indsp !structure_table

let lookup_projections indsp = (lookup_structure indsp).s_PROJ

let find_projection_nparams = function
  | ConstRef cst -> (Cmap.find cst !projection_table).s_EXPECTEDPARAM
  | _ -> raise Not_found

let find_projection = function
  | ConstRef cst -> Cmap.find cst !projection_table
  | _ -> raise Not_found

let prim_table =
  Summary.ref (Cmap_env.empty : Projection.Repr.t Cmap_env.t) ~name:"record-prim-projs"

let load_prim i (_,p) =
  prim_table := Cmap_env.add (Projection.Repr.constant p) p !prim_table

let cache_prim p = load_prim 1 p

let subst_prim (subst,p) = subst_proj_repr subst p

let discharge_prim (_,p) = Some (Lib.discharge_proj_repr p)

let inPrim : Projection.Repr.t -> obj =
  declare_object {
    (default_object "PRIMPROJS") with
    cache_function = cache_prim ;
    load_function = load_prim;
    subst_function = subst_prim;
    classify_function = (fun x -> Substitute x);
    discharge_function = discharge_prim }

let declare_primitive_projection p = Lib.add_anonymous_leaf (inPrim p)

let is_primitive_projection c = Cmap_env.mem c !prim_table

let find_primitive_projection c =
  try Some (Cmap_env.find c !prim_table) with Not_found -> None

(************************************************************************)
(*s A canonical structure declares "canonical" conversion hints between *)
(*  the effective components of a structure and the projections of the  *)
(*  structure *)

(* Table des definitions "object" : pour chaque object c,

  c := [x1:B1]...[xk:Bk](Build_R a1...am t1...t_n)

  If ti has the form (ci ui1...uir) where ci is a global reference (or
  a sort, or a product or a reference to a parameter) and if the 
  corresponding projection Li of the structure R is defined, one
  declares a "conversion" between ci and Li.

    x1:B1..xk:Bk |- (Li a1..am (c x1..xk)) =_conv (ci ui1...uir)

  that maps the pair (Li,ci) to the following data

    o_DEF = c
    o_TABS = B1...Bk
    o_INJ = Some n        (when ci is a reference to the parameter xi)
    o_PARAMS = a1...am
    o_NARAMS = m
    o_TCOMP = ui1...uir

*)

type obj_typ = {
  o_DEF : constr;
  o_CTX : Univ.AUContext.t;
  o_INJ : int option;      (* position of trivial argument if any *)
  o_TABS : constr list;    (* ordered *)
  o_TPARAMS : constr list; (* ordered *)
  o_NPARAMS : int;
  o_TCOMPS : constr list } (* ordered *)

type cs_pattern =
    Const_cs of GlobRef.t
  | Prod_cs
  | Sort_cs of Sorts.family
  | Default_cs

let eq_cs_pattern p1 p2 = match p1, p2 with
| Const_cs gr1, Const_cs gr2 -> GlobRef.equal gr1 gr2
| Prod_cs, Prod_cs -> true
| Sort_cs s1, Sort_cs s2 -> Sorts.family_equal s1 s2
| Default_cs, Default_cs -> true
| _ -> false

let rec assoc_pat a = function
  | ((pat, t), e) :: xs -> if eq_cs_pattern pat a then (t, e) else assoc_pat a xs
  | [] -> raise Not_found


let object_table =
  Summary.ref (Refmap.empty : ((cs_pattern * constr) * obj_typ) list Refmap.t)
    ~name:"record-canonical-structs"

let canonical_projections () =
  Refmap.fold (fun x -> List.fold_right (fun ((y,_),c) acc -> ((x,y),c)::acc))
    !object_table []

let keep_true_projections projs kinds =
  let filter (p, (_, b)) = if b then Some p else None in
  List.map_filter filter (List.combine projs kinds)

let cs_pattern_of_constr env t =
  match kind t with
      App (f,vargs) ->
	begin
	  try Const_cs (global_of_constr f) , None, Array.to_list vargs
          with e when CErrors.noncritical e -> raise Not_found
	end
    | Rel n -> Default_cs, Some n, []
    | Prod (_,a,b) when Vars.noccurn 1 b -> Prod_cs, None, [a; Vars.lift (-1) b]
    | Proj (p, c) ->
      let { Environ.uj_type = ty } = Typeops.infer env c in
      let _, params = Inductive.find_rectype env ty in
      Const_cs (ConstRef (Projection.constant p)), None, params @ [c]
    | Sort s -> Sort_cs (Sorts.family s), None, []
    | _ ->
	begin
	  try Const_cs (global_of_constr t) , None, []
          with e when CErrors.noncritical e -> raise Not_found
	end

let warn_projection_no_head_constant =
  CWarnings.create ~name:"projection-no-head-constant" ~category:"typechecker"
         (fun (sign,env,t,con,proji_sp) ->
          let env = Termops.push_rels_assum sign env in
          let con_pp = Nametab.pr_global_env Id.Set.empty (ConstRef con) in
          let proji_sp_pp = Nametab.pr_global_env Id.Set.empty (ConstRef proji_sp) in
          let term_pp = Termops.Internal.print_constr_env env (Evd.from_env env) (EConstr.of_constr t) in
          strbrk "Projection value has no head constant: "
          ++ term_pp ++ strbrk " in canonical instance "
          ++ con_pp ++ str " of " ++ proji_sp_pp ++ strbrk ", ignoring it.")

(* Intended to always succeed *)
let compute_canonical_projections warn (con,ind) =
  let env = Global.env () in
  let ctx = Environ.constant_context env con in
  let u = Univ.make_abstract_instance ctx in
  let v = (mkConstU (con,u)) in
  let c = Environ.constant_value_in env (con,u) in
  let sign,t = Reductionops.splay_lam env (Evd.from_env env) (EConstr.of_constr c) in
  let sign = List.map (on_snd EConstr.Unsafe.to_constr) sign in
  let t = EConstr.Unsafe.to_constr t in
  let lt = List.rev_map snd sign in
  let args = snd (decompose_app t) in
  let { s_EXPECTEDPARAM = p; s_PROJ = lpj; s_PROJKIND = kl } =
    lookup_structure ind in
  let params, projs = List.chop p args in
  let lpj = keep_true_projections lpj kl in
  let lps = List.combine lpj projs in
  let nenv = Termops.push_rels_assum sign env in
  let comp =
    List.fold_left
      (fun l (spopt,t) -> (* comp=components *)
	 match spopt with
           | Some proji_sp ->
	       begin
		 try
		   let patt, n , args = cs_pattern_of_constr nenv t in
		     ((ConstRef proji_sp, patt, t, n, args) :: l)
		 with Not_found ->
                   if warn then warn_projection_no_head_constant (sign,env,t,con,proji_sp);
                   l
	       end
	   | _ -> l)
      [] lps in
  List.map (fun (refi,c,t,inj,argj) ->
    (refi,(c,t)),
    {o_DEF=v; o_CTX=ctx; o_INJ=inj; o_TABS=lt;
     o_TPARAMS=params; o_NPARAMS=List.length params; o_TCOMPS=argj})
    comp

let pr_cs_pattern = function
    Const_cs c -> Nametab.pr_global_env Id.Set.empty c
  | Prod_cs -> str "_ -> _"
  | Default_cs -> str "_"
  | Sort_cs s -> Termops.pr_sort_family s

let warn_redundant_canonical_projection =
  CWarnings.create ~name:"redundant-canonical-projection" ~category:"typechecker"
         (fun (hd_val,prj,new_can_s,old_can_s) ->
          strbrk "Ignoring canonical projection to " ++ hd_val
          ++ strbrk " by " ++ prj ++ strbrk " in "
          ++ new_can_s ++ strbrk ": redundant with " ++ old_can_s)

let add_canonical_structure warn o =
    let lo = compute_canonical_projections warn o in
    List.iter (fun ((proj,(cs_pat,_ as pat)),s) ->
      let l = try Refmap.find proj !object_table with Not_found -> [] in
      let ocs = try Some (assoc_pat cs_pat l)
      with Not_found -> None
      in match ocs with
        | None -> object_table := Refmap.add proj ((pat,s)::l) !object_table;
        | Some (c, cs) ->
              (* XXX: Undesired global access to env *)
              let env = Global.env () in
              let sigma = Evd.from_env env in
              let old_can_s = (Termops.Internal.print_constr_env env sigma (EConstr.of_constr cs.o_DEF))
              and new_can_s = (Termops.Internal.print_constr_env env sigma (EConstr.of_constr s.o_DEF))
              in
              let prj = (Nametab.pr_global_env Id.Set.empty proj)
              and hd_val = (pr_cs_pattern cs_pat) in
              if warn then warn_redundant_canonical_projection (hd_val,prj,new_can_s,old_can_s))
          lo

let open_canonical_structure i (_, o) =
  if Int.equal i 1 then add_canonical_structure false o

let cache_canonical_structure (_, o) =
  add_canonical_structure true o

let subst_canonical_structure (subst,(cst,ind as obj)) =
  (* invariant: cst is an evaluable reference. Thus we can take *)
  (* the first component of subst_con.                                   *)
  let cst' = subst_constant subst cst in
  let ind' = subst_ind subst ind in
  if cst' == cst && ind' == ind then obj else (cst',ind')

let discharge_canonical_structure (_,(cst,ind)) =
  Some (Lib.discharge_con cst,Lib.discharge_inductive ind)

let inCanonStruc : Constant.t * inductive -> obj =
  declare_object {(default_object "CANONICAL-STRUCTURE") with
    open_function = open_canonical_structure;
    cache_function = cache_canonical_structure;
    subst_function = subst_canonical_structure;
    classify_function = (fun x -> Substitute x);
    discharge_function = discharge_canonical_structure }

let add_canonical_structure x = Lib.add_anonymous_leaf (inCanonStruc x)

(*s High-level declaration of a canonical structure *)

let error_not_structure ref description =
  user_err ~hdr:"object_declare"
    (str"Could not declare a canonical structure " ++
       (Id.print (basename_of_global ref) ++ str"." ++ spc() ++
          description))

let check_and_decompose_canonical_structure ref =
  let sp =
    match ref with
      ConstRef sp -> sp
    |  _ -> error_not_structure ref (str "Expected an instance of a record or structure.")
  in
  let env = Global.env () in
  let u = Univ.make_abstract_instance (Environ.constant_context env sp) in
  let vc = match Environ.constant_opt_value_in env (sp, u) with
    | Some vc -> vc
    | None -> error_not_structure ref (str "Could not find its value in the global environment.") in
  let env = Global.env () in
  let evd = Evd.from_env env in
  let body = snd (splay_lam (Global.env()) evd (EConstr.of_constr vc)) in
  let body = EConstr.Unsafe.to_constr body in
  let f,args = match kind body with
    | App (f,args) -> f,args
    | _ ->
       error_not_structure ref (str "Expected a record or structure constructor applied to arguments.") in
  let indsp = match kind f with
    | Construct ((indsp,1),u) -> indsp
    | _ -> error_not_structure ref (str "Expected an instance of a record or structure.") in
  let s =
    try lookup_structure indsp
    with Not_found ->
      error_not_structure ref
        (str "Could not find the record or structure " ++ Termops.Internal.print_constr_env env evd (EConstr.mkInd indsp)) in
  let ntrue_projs = List.count snd s.s_PROJKIND in
  if s.s_EXPECTEDPARAM + ntrue_projs > Array.length args then
    error_not_structure ref (str "Got too few arguments to the record or structure constructor.");
  (sp,indsp)

let declare_canonical_structure ref =
  add_canonical_structure (check_and_decompose_canonical_structure ref)

let lookup_canonical_conversion (proj,pat) =
  assoc_pat pat (Refmap.find proj !object_table)

let decompose_projection sigma c args =
  match EConstr.kind sigma c with
  | Const (c, u) ->
     let n = find_projection_nparams (ConstRef c) in
     (** Check if there is some canonical projection attached to this structure *)
     let _ = Refmap.find (ConstRef c) !object_table in
     let arg = Stack.nth args n in
     arg
  | Proj (p, c) ->
     let _ = Refmap.find (ConstRef (Projection.constant p)) !object_table in
     c
  | _ -> raise Not_found

let is_open_canonical_projection env sigma (c,args) =
  let open EConstr in
  try
    let arg = decompose_projection sigma c args in
    try
      let arg = whd_all env sigma arg in
      let hd = match EConstr.kind sigma arg with App (hd, _) -> hd | _ -> arg in
      not (isConstruct sigma hd)
    with Failure _ -> false
  with Not_found -> false
