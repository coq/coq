(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
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
open Constr
open Mod_subst
open Reductionops

(*s A structure S is a non recursive inductive type with a single
   constructor (the name of which defaults to Build_S) *)

(* Table of structures.
   It maps to each structure name (of type [inductive]):
     - the name of its constructor;
     - the number of parameters;
     - for each true argument, some data about the corresponding projection:
         * its name (may be anonymous);
         * whether it is a true projection (as opposed to a constant function, LetIn);
         * whether it should be used as a canonical hint;
         * the constant realizing this projection (if any).
*)

type proj_kind = {
  pk_name: Name.t;
  pk_true_proj: bool;
  pk_canonical: bool;
}

type struc_typ = {
  s_CONST : constructor;
  s_EXPECTEDPARAM : int;
  s_PROJKIND : proj_kind list;
  s_PROJ : Constant.t option list }

let structure_table =
  Summary.ref (Indmap.empty : struc_typ Indmap.t) ~name:"record-structs"
let projection_table =
  Summary.ref (Cmap.empty : struc_typ Cmap.t) ~name:"record-projs"

(* TODO: could be unify struc_typ and struc_tuple ? *)

type struc_tuple =
    constructor * proj_kind list * Constant.t option list

let register_structure env (id,kl,projs) =
  let open Declarations in
  let ind = fst id in
  let mib, mip = Inductive.lookup_mind_specif env ind in
  let n = mib.mind_nparams in
  let struc =
    { s_CONST = id; s_EXPECTEDPARAM = n; s_PROJ = projs; s_PROJKIND = kl } in
  structure_table := Indmap.add ind struc !structure_table;
  projection_table :=
    List.fold_right (Option.fold_right (fun proj -> Cmap.add proj struc))
      projs !projection_table

let subst_structure subst (id, kl, projs as obj) =
  let projs' =
   (* invariant: struc.s_PROJ is an evaluable reference. Thus we can take *)
   (* the first component of subst_con.                                   *)
   List.Smart.map
     (Option.Smart.map (subst_constant subst))
    projs
  in
  let id' = subst_constructor subst id in
  if projs' == projs && id' == id then obj else
    (id',kl,projs')

let lookup_structure indsp = Indmap.find indsp !structure_table

let lookup_projections indsp = (lookup_structure indsp).s_PROJ

let find_projection_nparams = function
  | ConstRef cst -> (Cmap.find cst !projection_table).s_EXPECTEDPARAM
  | _ -> raise Not_found

let find_projection = function
  | ConstRef cst -> Cmap.find cst !projection_table
  | _ -> raise Not_found

let is_projection cst = Cmap.mem cst !projection_table

let prim_table =
  Summary.ref (Cmap_env.empty : Projection.Repr.t Cmap_env.t) ~name:"record-prim-projs"

let register_primitive_projection p c =
  prim_table := Cmap_env.add c p !prim_table

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
  Summary.ref (GlobRef.Map.empty : ((cs_pattern * constr) * obj_typ) list GlobRef.Map.t)
    ~name:"record-canonical-structs"

let canonical_projections () =
  GlobRef.Map.fold (fun x -> List.fold_right (fun ((y,_),c) acc -> ((x,y),c)::acc))
    !object_table []

let keep_true_projections projs kinds =
  let filter (p, { pk_true_proj ; pk_canonical }) = if pk_true_proj then Some (p, pk_canonical) else None in
  List.map_filter filter (List.combine projs kinds)

let rec cs_pattern_of_constr env t =
  match kind t with
  | App (f,vargs) ->
    let patt, n, args = cs_pattern_of_constr env f in
    patt, n, args @ Array.to_list vargs
  | Rel n -> Default_cs, Some n, []
  | Prod (_,a,b) when Vars.noccurn 1 b -> Prod_cs, None, [a; Vars.lift (-1) b]
  | Proj (p, c) ->
    let { Environ.uj_type = ty } = Typeops.infer env c in
    let _, params = Inductive.find_rectype env ty in
    Const_cs (ConstRef (Projection.constant p)), None, params @ [c]
  | Sort s -> Sort_cs (Sorts.family s), None, []
  | _ -> Const_cs (global_of_constr t) , None, []

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
let compute_canonical_projections env ~warn (con,ind) =
  let o_CTX = Environ.constant_context env con in
  let u = Univ.make_abstract_instance o_CTX in
  let o_DEF = mkConstU (con, u) in
  let c = Environ.constant_value_in env (con,u) in
  let sign,t = Reductionops.splay_lam env (Evd.from_env env) (EConstr.of_constr c) in
  let sign = List.map (on_snd EConstr.Unsafe.to_constr) sign in
  let t = EConstr.Unsafe.to_constr t in
  let o_TABS = List.rev_map snd sign in
  let args = snd (decompose_app t) in
  let { s_EXPECTEDPARAM = p; s_PROJ = lpj; s_PROJKIND = kl } =
    lookup_structure ind in
  let o_TPARAMS, projs = List.chop p args in
  let o_NPARAMS = List.length o_TPARAMS in
  let lpj = keep_true_projections lpj kl in
  let nenv = Termops.push_rels_assum sign env in
  List.fold_left2 (fun acc (spopt, canonical) t ->
      if canonical
      then
        Option.cata (fun proji_sp ->
            match cs_pattern_of_constr nenv t with
            | patt, o_INJ, o_TCOMPS ->
              ((ConstRef proji_sp, (patt, t)),
               { o_DEF ; o_CTX ; o_INJ ; o_TABS ; o_TPARAMS ; o_NPARAMS ; o_TCOMPS })
              :: acc
            | exception Not_found ->
              if warn then warn_projection_no_head_constant (sign, env, t, con, proji_sp);
              acc
          ) acc spopt
      else acc
    ) [] lpj projs

let pr_cs_pattern = function
    Const_cs c -> Nametab.pr_global_env Id.Set.empty c
  | Prod_cs -> str "_ -> _"
  | Default_cs -> str "_"
  | Sort_cs s -> Sorts.pr_sort_family s

let warn_redundant_canonical_projection =
  CWarnings.create ~name:"redundant-canonical-projection" ~category:"typechecker"
         (fun (hd_val,prj,new_can_s,old_can_s) ->
          strbrk "Ignoring canonical projection to " ++ hd_val
          ++ strbrk " by " ++ prj ++ strbrk " in "
          ++ new_can_s ++ strbrk ": redundant with " ++ old_can_s)

let register_canonical_structure ~warn env sigma o =
    compute_canonical_projections env ~warn o |>
    List.iter (fun ((proj, (cs_pat, _ as pat)), s) ->
      let l = try GlobRef.Map.find proj !object_table with Not_found -> [] in
      match assoc_pat cs_pat l with
      | exception Not_found ->
          object_table := GlobRef.Map.add proj ((pat, s) :: l) !object_table
      | _, cs ->
        if warn
        then
          let old_can_s = Termops.Internal.print_constr_env env sigma (EConstr.of_constr cs.o_DEF) in
          let new_can_s = Termops.Internal.print_constr_env env sigma (EConstr.of_constr s.o_DEF) in
          let prj = Nametab.pr_global_env Id.Set.empty proj in
          let hd_val = pr_cs_pattern cs_pat in
          warn_redundant_canonical_projection (hd_val, prj, new_can_s, old_can_s)
      )

let subst_canonical_structure subst (cst,ind as obj) =
  (* invariant: cst is an evaluable reference. Thus we can take *)
  (* the first component of subst_con.                                   *)
  let cst' = subst_constant subst cst in
  let ind' = subst_ind subst ind in
  if cst' == cst && ind' == ind then obj else (cst',ind')

(*s High-level declaration of a canonical structure *)

let error_not_structure ref description =
  user_err ~hdr:"object_declare"
    (str"Could not declare a canonical structure " ++
       (Id.print (Nametab.basename_of_global ref) ++ str"." ++ spc() ++
          description))

let check_and_decompose_canonical_structure env sigma ref =
  let sp =
    match ref with
      ConstRef sp -> sp
    |  _ -> error_not_structure ref (str "Expected an instance of a record or structure.")
  in
  let u = Univ.make_abstract_instance (Environ.constant_context env sp) in
  let vc = match Environ.constant_opt_value_in env (sp, u) with
    | Some vc -> vc
    | None -> error_not_structure ref (str "Could not find its value in the global environment.") in
  let body = snd (splay_lam env sigma (EConstr.of_constr vc)) in
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
        (str "Could not find the record or structure " ++ Termops.Internal.print_constr_env env sigma (EConstr.mkInd indsp)) in
  let ntrue_projs = List.count (fun { pk_true_proj } -> pk_true_proj) s.s_PROJKIND in
  if s.s_EXPECTEDPARAM + ntrue_projs > Array.length args then
    error_not_structure ref (str "Got too few arguments to the record or structure constructor.");
  (sp,indsp)

let lookup_canonical_conversion (proj,pat) =
  assoc_pat pat (GlobRef.Map.find proj !object_table)

let decompose_projection sigma c args =
  match EConstr.kind sigma c with
  | Const (c, u) ->
     let n = find_projection_nparams (ConstRef c) in
     (* Check if there is some canonical projection attached to this structure *)
     let _ = GlobRef.Map.find (ConstRef c) !object_table in
     let arg = Stack.nth args n in
     arg
  | Proj (p, c) ->
     let _ = GlobRef.Map.find (ConstRef (Projection.constant p)) !object_table in
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
