(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

module Structure = struct

type projection = {
  proj_name : Names.Name.t;
  proj_true : bool;
  proj_canonical : bool;
  proj_body : Names.Constant.t option;
}

type t = {
  name : Names.inductive;
  projections : projection list;
  nparams : int;
}

let make env name projections =
  let nparams = Inductiveops.inductive_nparams env name in
  { name; projections; nparams }

let structure_table =
  Summary.ref (Indmap.empty : t Indmap.t) ~name:"record-structs"
let projection_table =
  Summary.ref (Cmap.empty : t Cmap.t) ~name:"record-projs"

let register ({ name; projections; nparams } as s) =
  structure_table := Indmap.add name s !structure_table;
  projection_table :=
    List.fold_right (fun { proj_body } m ->
      Option.fold_right (fun proj -> Cmap.add proj s) proj_body m)
    projections !projection_table

let subst subst ({ name; projections; nparams } as s) =
  let subst_projection subst ({ proj_body } as p) =
    let proj_body = Option.Smart.map (subst_constant subst) proj_body in
    if proj_body == p.proj_body then p else
    { p with proj_body } in
  let projections = List.Smart.map (subst_projection subst) projections in
  let name = Mod_subst.subst_ind subst name in
  if projections == s.projections &&
     name == s.name
  then s
  else { name; projections; nparams }

let rebuild env s =
  let mib = Environ.lookup_mind (fst s.name) env in
  let nparams = mib.Declarations.mind_nparams in
  { s with nparams }

let find indsp = Indmap.find indsp !structure_table

let find_projections indsp =
  (find indsp).projections |>
  List.map (fun { proj_body } -> proj_body)

let find_from_projection cst = Cmap.find cst !projection_table

let projection_nparams cst = (Cmap.find cst !projection_table).nparams

let is_projection cst = Cmap.mem cst !projection_table

let projection_number env cst =
  let s = find_from_projection cst in
  CList.index0 (Option.equal (Environ.QConstant.equal env)) (Some cst)
    (List.map (fun x -> x.proj_body) s.projections)

end

(************************************************************************)
(*s A canonical structure declares "canonical" conversion hints between *)
(*  the effective components of a structure and the projections of the  *)
(*  structure *)

(* Table of "object" definitions: for each object c,

  c := [x1:B1]...[xk:Bk](Build_R a1...am t1...t_n)

  If ti has the form (ci ui1...uir) where ci is a global reference (or
  a sort, or a product or a reference to a parameter) and if the
  corresponding projection Li of the structure R is defined, one
  declares a "conversion" between ci and Li.

    x1:B1..xk:Bk |- (Li a1..am (c x1..xk)) =_conv (ci ui1...uir)

  that maps the pair (Li,ci) to the following data

    o_ORIGIN = c (the constant name which this conversion rule is
                  synthesized from)
    o_DEF = c
    o_TABS = B1...Bk
    o_INJ = Some n        (when ci is a reference to the parameter xi)
    o_TPARAMS = a1...am
    o_NPARAMS = m
    o_TCOMP = ui1...uir

*)

type obj_typ = {
  o_ORIGIN : GlobRef.t;
  o_DEF : constr;
  o_CTX : UVars.AbstractContext.t;
  o_INJ : int option;      (* position of trivial argument if any *)
  o_TABS : constr list;    (* ordered *)
  o_TPARAMS : constr list; (* ordered *)
  o_NPARAMS : int;
  o_TCOMPS : constr list } (* ordered *)

module ValuePattern = struct

type t =
    Const_cs of GlobRef.t
  | Proj_cs of Names.Projection.Repr.t
  | Prod_cs
  | Sort_cs of Sorts.family
  | Default_cs

let equal env p1 p2 = match p1, p2 with
  | Const_cs gr1, Const_cs gr2 -> Environ.QGlobRef.equal env gr1 gr2
  | Proj_cs p1, Proj_cs p2 -> Environ.QProjection.Repr.equal env p1 p2
  | Prod_cs, Prod_cs -> true
  | Sort_cs s1, Sort_cs s2 -> Sorts.family_equal s1 s2
  | Default_cs, Default_cs -> true
  | _ -> false

let compare p1 p2 = match p1, p2 with
  | Const_cs gr1, Const_cs gr2 -> GlobRef.CanOrd.compare gr1 gr2
  | Proj_cs p1, Proj_cs p2 -> Projection.Repr.CanOrd.compare p1 p2
  | Prod_cs, Prod_cs -> 0
  | Sort_cs s1, Sort_cs s2 -> Sorts.family_compare s1 s2
  | Default_cs, Default_cs -> 0
  | _ -> Stdlib.compare p1 p2

let rec of_constr sigma t =
  match EConstr.kind sigma t with
  | App (f,vargs) ->
    let patt, n, args = of_constr sigma f in
    patt, n, args @ Array.to_list vargs
  | Rel n -> Default_cs, Some n, []
  | Lambda (_, _, b) -> let patt, _, _ = of_constr sigma b in patt, None, []
  | Prod (_,_,_) -> Prod_cs, None, [t]
  | Proj (p, _, c) -> Proj_cs (Names.Projection.repr p), None, [c]
  | Sort s -> Sort_cs (EConstr.ESorts.family sigma s), None, []
  | _ -> Const_cs (fst @@ EConstr.destRef sigma t) , None, []

let print = function
    Const_cs c -> Nametab.pr_global_env Id.Set.empty c
  | Proj_cs p -> Nametab.pr_global_env Id.Set.empty (GlobRef.ConstRef (Names.Projection.Repr.constant p))
  | Prod_cs -> str "forall _, _"
  | Default_cs -> str "_"
  | Sort_cs s -> Sorts.pr_sort_family s

end

module PatMap = Map.Make(ValuePattern)

let object_table =
  Summary.ref (GlobRef.Map.empty : (constr * obj_typ) PatMap.t GlobRef.Map.t)
    ~name:"record-canonical-structs"

let keep_true_projections projs =
  let filter { Structure.proj_true ; proj_canonical; proj_body } = if proj_true then Some (proj_body, proj_canonical) else None in
  List.map_filter filter projs

let warn_projection_no_head_constant =
  CWarnings.create ~name:"projection-no-head-constant" ~category:CWarnings.CoreCategories.records
         (fun (sign,env,t,ref,proji_sp) ->
          let env = Environ.push_rel_context sign env in
          let con_pp = Nametab.pr_global_env Id.Set.empty ref in
          let proji_sp_pp = Nametab.pr_global_env Id.Set.empty (GlobRef.ConstRef proji_sp) in
          let term_pp = Termops.Internal.print_constr_env env (Evd.from_env env) (EConstr.of_constr t) in
          strbrk "Projection value has no head constant: "
          ++ term_pp ++ strbrk " in canonical instance "
          ++ con_pp ++ str " of " ++ proji_sp_pp ++ strbrk ", ignoring it.")

(* Intended to always succeed *)
let compute_canonical_projections env sigma ~warn (gref,ind) =
  let o_CTX = Environ.universes_of_global env gref in
  let o_DEF, c =
    match gref with
    | GlobRef.ConstRef con ->
        let u = UVars.make_abstract_instance o_CTX in
        mkConstU (con, u), Environ.constant_value_in env (con,u)
    | GlobRef.VarRef id ->
        mkVar id, Option.get (Environ.named_body id env)
    | GlobRef.ConstructRef _ | GlobRef.IndRef _ -> assert false
  in
  let sign,t = Reduction.whd_decompose_lambda env c in
  let o_TABS = List.rev_map Context.Rel.Declaration.get_type sign in
  let args = snd (decompose_app_list t) in
  let { Structure.nparams = p; projections = lpj } =
    Structure.find ind in
  let o_TPARAMS, projs = List.chop p args in
  let o_NPARAMS = List.length o_TPARAMS in
  let lpj = keep_true_projections lpj in
  List.fold_left2 (fun acc (spopt, canonical) t ->
      let t = EConstr.Unsafe.to_constr (shrink_eta sigma (EConstr.of_constr t)) in
      if canonical
      then
        Option.cata (fun proji_sp ->
            match ValuePattern.of_constr sigma (EConstr.of_constr t) with
            | patt, o_INJ, o_TCOMPS ->
              ((GlobRef.ConstRef proji_sp, (patt, t)),
               { o_ORIGIN = gref ; o_DEF ; o_CTX ; o_INJ ; o_TABS ; o_TPARAMS ; o_NPARAMS ; o_TCOMPS = List.map EConstr.Unsafe.to_constr o_TCOMPS })
              :: acc
            | exception DestKO ->
              if warn then warn_projection_no_head_constant (sign, env, t, gref, proji_sp);
              acc
          ) acc spopt
      else acc
    ) [] lpj projs

let warn_redundant_canonical_projection =
  CWarnings.create ~name:"redundant-canonical-projection" ~category:CWarnings.CoreCategories.records
         (fun (hd_val,prj,new_can_s,old_can_s) ->
          strbrk "Ignoring canonical projection to " ++ hd_val
          ++ strbrk " by " ++ prj ++ strbrk " in "
          ++ new_can_s ++ strbrk ": redundant with " ++ old_can_s)

module Instance = struct

type t = GlobRef.t * inductive

let repr = fst

let subst subst (gref,ind as obj) =
  (* invariant: cst is an evaluable reference. Thus we can take *)
  (* the first component of subst_con.                                   *)
  match gref with
  | GlobRef.ConstRef cst ->
      let cst' = subst_constant subst cst in
      let ind' = subst_ind subst ind in
      if cst' == cst && ind' == ind then obj else (GlobRef.ConstRef cst',ind')
  | _ -> assert false

(*s High-level declaration of a canonical structure *)

let error_not_structure ref description =
  user_err
    (str"Could not declare a canonical structure " ++
       (Id.print (Nametab.basename_of_global ref) ++ str"." ++ spc() ++
          description) ++ str ".")

let make env sigma ref =
  let vc =
    match ref with
    | GlobRef.ConstRef sp ->
        let u = UVars.make_abstract_instance (Environ.constant_context env sp) in
        begin match Environ.constant_opt_value_in env (sp, u) with
        | Some vc -> vc
        | None -> error_not_structure ref (str "Could not find its value in the global environment") end
    | GlobRef.VarRef id ->
        begin match Environ.named_body id env with
        | Some b -> b
        | None -> error_not_structure ref (str "Could not find its value in the global environment") end
    | GlobRef.IndRef _ | GlobRef.ConstructRef _ ->
        error_not_structure ref (str "Expected an instance of a record or structure")
  in
  let body = snd (whd_decompose_lambda env sigma (EConstr.of_constr vc)) in
  let body = EConstr.Unsafe.to_constr body in
  let f,args = match kind body with
    | App (f,args) -> f,args
    | _ ->
       error_not_structure ref (str "Expected a record or structure constructor applied to arguments") in
  let indsp = match kind f with
    | Construct ((indsp,1),u) -> indsp
    | _ -> error_not_structure ref (str "Expected an instance of a record or structure") in
  let s =
    try Structure.find indsp
    with Not_found ->
      error_not_structure ref
        (str "Could not find the record or structure " ++ Termops.pr_global_env env (IndRef indsp)) in
  let ntrue_projs = List.count (fun { Structure.proj_true = x } -> x) s.Structure.projections in
  if s.Structure.nparams + ntrue_projs > Array.length args then
    error_not_structure ref (str "Got too few arguments to the record or structure constructor");
  (ref,indsp)

let register ~warn env sigma o =
    compute_canonical_projections env sigma ~warn o |>
    List.iter (fun ((proj, (cs_pat, t)), s) ->
      let l = try GlobRef.Map.find proj !object_table with Not_found -> PatMap.empty in
      match PatMap.find cs_pat l with
      | exception Not_found ->
          object_table := GlobRef.Map.add proj (PatMap.add cs_pat (t, s) l) !object_table
      | _, cs ->
        if warn
        then
          let old_can_s = Termops.Internal.print_constr_env env sigma (EConstr.of_constr cs.o_DEF) in
          let new_can_s = Termops.Internal.print_constr_env env sigma (EConstr.of_constr s.o_DEF) in
          let prj = Nametab.pr_global_env Id.Set.empty proj in
          let hd_val = ValuePattern.print cs_pat in
          warn_redundant_canonical_projection (hd_val, prj, new_can_s, old_can_s)
      )

end

(** The canonical solution of a problem (proj,val) is a global
    [constant = fun abs : abstractions_ty => body] and
    [ body = RecodConstructor params canon_values ] and the canonical value
    corresponding to val is [val cvalue_arguments].
    It is possible that val is one of the [abs] abstractions, eg [Default_cs],
    and in that case [cvalue_abstraction = Some i] *)

module CanonicalSolution = struct
type t = {
  constant : EConstr.t;

  abstractions_ty : EConstr.t list;
  body : EConstr.t;

  nparams : int;
  params : EConstr.t list;
  cvalue_abstraction : int option;
  cvalue_arguments : EConstr.t list;
}

let find env sigma (proj,pat) =
  let t', { o_DEF = c; o_CTX = ctx; o_INJ=n; o_TABS = bs;
        o_TPARAMS = params; o_NPARAMS = nparams; o_TCOMPS = us } = PatMap.find pat (GlobRef.Map.find proj !object_table) in
  let us = List.map EConstr.of_constr us in
  let params = List.map EConstr.of_constr params in
  let u, ctx' = UnivGen.fresh_instance_from ctx None in
  let u = EConstr.EInstance.make u in
  let c = EConstr.of_constr c in
  let c' = EConstr.Vars.subst_instance_constr u c in
  let t' = EConstr.of_constr t' in
  let t' = EConstr.Vars.subst_instance_constr u t' in
  let bs' = List.map (EConstr.of_constr %> EConstr.Vars.subst_instance_constr u) bs in
  let params = List.map (fun c -> EConstr.Vars.subst_instance_constr u c) params in
  let us = List.map (fun c -> EConstr.Vars.subst_instance_constr u c) us in
  let sigma = Evd.merge_sort_context_set Evd.univ_flexible sigma ctx' in
  sigma, { body = t'; constant = c'; abstractions_ty = bs'; nparams; params; cvalue_arguments = us; cvalue_abstraction = n }


let rec get_nth n = function
| [] -> raise Not_found
| arg :: args ->
  let len = Array.length arg in
  if n < len then arg.(n)
  else get_nth (n - len) args

let rec decompose_projection ?metas sigma c args =
  match EConstr.kind sigma c with
  | Meta mv ->
    begin match metas with
    | None -> raise Not_found
    | Some m ->
      match m.meta_value mv with
      | None -> raise Not_found
      | Some v -> decompose_projection ?metas sigma v args
    end
  | Cast (c, _, _) -> decompose_projection ?metas sigma c args
  | App (c, arg) -> decompose_projection ?metas sigma c (arg :: args)
  | Const (c, u) ->
     let n = Structure.projection_nparams c in
     (* Check if there is some canonical projection attached to this structure *)
     let _ = GlobRef.Map.find (GlobRef.ConstRef c) !object_table in
     get_nth n args
  | Proj (p, _, c) ->
     let _ = GlobRef.Map.find (GlobRef.ConstRef (Names.Projection.constant p)) !object_table in
     c
  | _ -> raise Not_found

let is_open_canonical_projection ?metas env sigma c =
  let open EConstr in
  try
    let arg = decompose_projection ?metas sigma c [] in
    try
      let arg = whd_all ?metas env sigma arg in
      let hd = match EConstr.kind sigma arg with App (hd, _) -> hd | _ -> arg in
      not (isConstruct sigma hd)
    with Failure _ -> false
  with Not_found -> false

let print env sigma s =
  let pr_econstr = Termops.Internal.debug_print_constr sigma in
  let pr_econstr_list l = Pp.(str "[ " ++ prlist_with_sep (fun () -> str "; ") pr_econstr l ++ str " ]") in
  Pp.(str "{ constant = " ++ pr_econstr s.constant ++ cut () ++
     str "abstractions_ty = " ++ pr_econstr_list s.abstractions_ty ++ cut () ++
     str "body = " ++ pr_econstr s.body ++ cut () ++
     str "nparams = " ++ int s.nparams ++ cut () ++
     str "params = " ++ pr_econstr_list s.params ++ cut () ++
     str "cvalue_abstractions = " ++ pr_opt int s.cvalue_abstraction ++ cut () ++
     str "cvalue_arguments = " ++ pr_econstr_list s.cvalue_arguments ++ cut () ++
     str "}")

end

module CSTable = struct

type entry = {
  projection : Names.GlobRef.t;
  value : ValuePattern.t;
  solution : Names.GlobRef.t;
}

let canonical_entry_of_object projection value (_, { o_ORIGIN = solution }) =
  { projection; value; solution }

let entries () =
  GlobRef.Map.fold (fun p ol acc ->
    PatMap.fold (fun pat o acc -> canonical_entry_of_object p pat o :: acc) ol acc)
    !object_table []

let entries_for ~projection:p =
  try
    GlobRef.Map.find p !object_table |>
    PatMap.bindings |>
    List.map (fun (pat, o) -> canonical_entry_of_object p pat o)
  with Not_found -> []

end

module PrimitiveProjections = struct

let prim_table =
  Summary.ref (Cmap_env.empty : Names.Projection.Repr.t Cmap_env.t) ~name:"record-prim-projs"

let register p c =
  prim_table := Cmap_env.add c p !prim_table

let mem c = Cmap_env.mem c !prim_table

let find_opt c =
  try Some (Cmap_env.find c !prim_table) with Not_found -> None

let find_opt_with_relevance (c,u) =
  find_opt c |>
  Option.map (fun p ->
      let u = EConstr.Unsafe.to_instance u in
      p, EConstr.ERelevance.make @@ Relevanceops.relevance_of_projection_repr (Global.env()) (p,u))

let is_transparent_constant ts c =
  match find_opt c with
  | None -> TransparentState.is_transparent_constant ts c
  | Some p -> TransparentState.is_transparent_projection ts p

end
