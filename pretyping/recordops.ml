(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Amokrane Saïbi, Dec 1998 *)
(* Addition of products and sorts in canonical structures by Pierre
   Corbineau, Feb 2008 *)

(* This file registers properties of records: projections and
   canonical structures *)

open Errors
open Util
open Pp
open Names
open Globnames
open Nametab
open Term
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
  s_PROJ : constant option list }

let structure_table =
  Summary.ref (Indmap.empty : struc_typ Indmap.t) ~name:"record-structs"
let projection_table =
  Summary.ref Cmap.empty ~name:"record-projs"

(* TODO: could be unify struc_typ and struc_tuple ? in particular,
   is the inductive always (fst constructor) ? It seems so... *)

type struc_tuple =
    inductive * constructor * (Name.t * bool) list * constant option list

let load_structure i (_,(ind,id,kl,projs)) =
  let n = (fst (Global.lookup_inductive ind)).Declarations.mind_nparams in
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
   List.smartmap
     (Option.smartmap (fun kn -> fst (subst_con_kn subst kn)))
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
  o_CTX : Univ.ContextSet.t;
  o_INJ : int option;      (* position of trivial argument if any *)
  o_TABS : constr list;    (* ordered *)
  o_TPARAMS : constr list; (* ordered *)
  o_NPARAMS : int;
  o_TCOMPS : constr list } (* ordered *)

type cs_pattern =
    Const_cs of global_reference
  | Prod_cs
  | Sort_cs of sorts_family
  | Default_cs

let eq_cs_pattern p1 p2 = match p1, p2 with
| Const_cs gr1, Const_cs gr2 -> eq_gr gr1 gr2
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

let cs_pattern_of_constr t =
  match kind_of_term t with
      App (f,vargs) ->
	begin
	  try Const_cs (global_of_constr f) , None, Array.to_list vargs
          with e when Errors.noncritical e -> raise Not_found
	end
    | Rel n -> Default_cs, Some n, []
    | Prod (_,a,b) when not (Termops.dependent (mkRel 1) b) -> Prod_cs, None, [a; Termops.pop b]
    | Sort s -> Sort_cs (family_of_sort s), None, []
    | _ ->
	begin
	  try Const_cs (global_of_constr t) , None, []
          with e when Errors.noncritical e -> raise Not_found
	end

(* Intended to always succeed *)
let compute_canonical_projections (con,ind) =
  let env = Global.env () in
  let ctx = Environ.constant_context env con in
  let u = Univ.UContext.instance ctx in
  let v = (mkConstU (con,u)) in
  let ctx = Univ.ContextSet.of_context ctx in
  let c = Environ.constant_value_in env (con,u) in
  let lt,t = Reductionops.splay_lam env Evd.empty c in
  let lt = List.rev_map snd lt in
  let args = snd (decompose_app t) in
  let { s_EXPECTEDPARAM = p; s_PROJ = lpj; s_PROJKIND = kl } =
    lookup_structure ind in
  let params, projs = List.chop p args in
  let lpj = keep_true_projections lpj kl in
  let lps = List.combine lpj projs in
  let comp =
    List.fold_left
      (fun l (spopt,t) -> (* comp=components *)
	 match spopt with
           | Some proji_sp ->
	       begin
		 try
		   let patt, n , args = cs_pattern_of_constr t in
		     ((ConstRef proji_sp, patt, t, n, args) :: l)
		 with Not_found ->
                   if Flags.is_verbose () then
                     (let con_pp = Nametab.pr_global_env Id.Set.empty (ConstRef con)
                      and proji_sp_pp = Nametab.pr_global_env Id.Set.empty (ConstRef proji_sp) in
		      msg_warning (strbrk "No global reference exists for projection value"
                                   ++ Termops.print_constr t ++ strbrk " in instance "  
                                   ++ con_pp ++ str " of " ++ proji_sp_pp ++ strbrk ", ignoring it."));
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

let open_canonical_structure i (_,o) =
  if Int.equal i 1 then
    let lo = compute_canonical_projections o in
    List.iter (fun ((proj,(cs_pat,_ as pat)),s) ->
      let l = try Refmap.find proj !object_table with Not_found -> [] in
      let ocs = try Some (assoc_pat cs_pat l)
      with Not_found -> None
      in match ocs with
        | None -> object_table := Refmap.add proj ((pat,s)::l) !object_table;
        | Some (c, cs) ->
            if Flags.is_verbose () then
              let old_can_s = (Termops.print_constr cs.o_DEF)
              and new_can_s = (Termops.print_constr s.o_DEF) in
              let prj = (Nametab.pr_global_env Id.Set.empty proj)
              and hd_val = (pr_cs_pattern cs_pat) in
              msg_warning (strbrk "Ignoring canonical projection to " ++ hd_val
                             ++ strbrk " by " ++ prj ++ strbrk " in "
                             ++ new_can_s ++ strbrk ": redundant with " ++ old_can_s)) lo

let cache_canonical_structure o =
  open_canonical_structure 1 o

let subst_canonical_structure (subst,(cst,ind as obj)) =
  (* invariant: cst is an evaluable reference. Thus we can take *)
  (* the first component of subst_con.                                   *)
  let cst' = subst_constant subst cst in
  let ind' = subst_ind subst ind in
  if cst' == cst && ind' == ind then obj else (cst',ind')

let discharge_canonical_structure (_,(cst,ind)) =
  Some (Lib.discharge_con cst,Lib.discharge_inductive ind)

let inCanonStruc : constant * inductive -> obj =
  declare_object {(default_object "CANONICAL-STRUCTURE") with
    open_function = open_canonical_structure;
    cache_function = cache_canonical_structure;
    subst_function = subst_canonical_structure;
    classify_function = (fun x -> Substitute x);
    discharge_function = discharge_canonical_structure }

let add_canonical_structure x = Lib.add_anonymous_leaf (inCanonStruc x)

(*s High-level declaration of a canonical structure *)

let error_not_structure ref =
  errorlabstrm "object_declare"
    (Nameops.pr_id (basename_of_global ref) ++ str" is not a structure object.")

let check_and_decompose_canonical_structure ref =
  let sp = match ref with ConstRef sp -> sp | _ -> error_not_structure ref in
  let env = Global.env () in
  let ctx = Environ.constant_context env sp in
  let u = Univ.UContext.instance ctx in
  let vc = match Environ.constant_opt_value_in env (sp, u) with
    | Some vc -> vc
    | None -> error_not_structure ref in
  let body = snd (splay_lam (Global.env()) Evd.empty vc) in
  let f,args = match kind_of_term body with
    | App (f,args) -> f,args
    | _ -> error_not_structure ref in
  let indsp = match kind_of_term f with
    | Construct ((indsp,1),u) -> indsp
    | _ -> error_not_structure ref in
  let s = try lookup_structure indsp with Not_found -> error_not_structure ref in
  let ntrue_projs = List.length (List.filter (fun (_, x) -> x) s.s_PROJKIND) in
  if s.s_EXPECTEDPARAM + ntrue_projs > Array.length args then
    error_not_structure ref;
  (sp,indsp)

let declare_canonical_structure ref =
  add_canonical_structure (check_and_decompose_canonical_structure ref)

let lookup_canonical_conversion (proj,pat) =
  assoc_pat pat (Refmap.find proj !object_table)

let is_open_canonical_projection env sigma (c,args) =
  try
    let ref = global_of_constr c in
    let n = find_projection_nparams ref in
    (** Check if there is some canonical projection attached to this structure *)
    let _ = Refmap.find ref !object_table in
    try
      let arg = whd_betadeltaiota env sigma (Stack.nth args n) in
      let hd = match kind_of_term arg with App (hd, _) -> hd | _ -> arg in
      not (isConstruct hd)
    with Failure _ -> false
  with Not_found -> false
