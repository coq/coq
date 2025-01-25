(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Nameops
open Termops
open Constr
open Context
open Evarutil
open Tactypes

(** {6 Evar-based clauses} *)

type hole = {
  hole_evar : EConstr.constr;
  hole_type : EConstr.types;
  hole_deps  : bool;
  hole_name : Name.t;
  hole_evar_key : Evar.t;
}

type clause = {
  cl_holes : hole list;
  cl_concl : EConstr.types;
}

let qhyp_eq h1 h2 = match h1, h2 with
| NamedHyp n1, NamedHyp n2 -> lident_eq n1 n2
| AnonHyp i1, AnonHyp i2 -> Int.equal i1 i2
| _ -> false

let check_bindings bl =
  match List.duplicates qhyp_eq (List.map (fun {CAst.v=x} -> fst x) bl) with
    | NamedHyp s :: _ ->
        user_err ?loc:s.CAst.loc
          Pp.(str "The variable " ++ Id.print s.CAst.v ++
              str " occurs more than once in binding list.");
    | AnonHyp n :: _ ->
        user_err
          Pp.(str "The position " ++ int n ++
              str " occurs more than once in binding list.")
    | [] -> ()

let explain_no_such_bound_variable mvl {CAst.v=id;loc} =
  let open Pp in
  let expl = match mvl with
  | [] -> str "(no bound variables at all in the expression)."
  | [id] -> str "(possible name is: " ++ Id.print id ++ str ")."
  | _ -> str "(possible names are: " ++ pr_enum Id.print mvl ++ str ")."
  in
  user_err ?loc (str "No such bound variable " ++ Id.print id ++ spc () ++ expl)

let error_not_right_number_missing_arguments n =
  user_err
    Pp.(strbrk "Not the right number of missing arguments (expected " ++
        int n ++ str ").")

let make_evar_clause env sigma ?len t =
  let open EConstr in
  let open Vars in
  let bound = match len with
  | None -> -1
  | Some n -> assert (0 <= n); n
  in
  let rec clrec (sigma, holes) inst n t =
    if n = 0 then (sigma, holes, t)
    else match EConstr.kind sigma t with
    | Cast (t, _, _) -> clrec (sigma, holes) inst n t
    | Prod (na, t1, t2) ->
      (* Share the evar instances as we are living in the same context *)
      let inst, ctx, args, subst = match inst with
      | None ->
        (* Dummy type *)
        let hypnaming = RenameExistingBut (VarSet.variables (Global.env ())) in
        let ctx, _, args, subst = push_rel_context_to_named_context ~hypnaming env sigma mkProp in
        Some (ctx, args, subst), ctx, args, subst
      | Some (ctx, args, subst) -> inst, ctx, args, subst
      in
      let (sigma, evk) = new_pure_evar ~typeclass_candidate:false ctx sigma
          ~relevance:na.binder_relevance
          (csubst_subst sigma subst t1)
      in
      let ev = mkEvar (evk, args) in
      let dep = not (noccurn sigma 1 t2) in
      let hole = {
        hole_evar = ev;
        hole_type = t1;
        hole_deps = dep;
        (* We fix it later *)
        hole_name = na.binder_name;
        hole_evar_key = evk;
      } in
      let t2 = subst1 ev t2 in
      clrec (sigma, hole :: holes) inst (pred n) t2
    | LetIn (na, b, _, t) -> clrec (sigma, holes) inst n (subst1 b t)
    | _ -> (sigma, holes, t)
  in
  let (sigma, holes, t) = clrec (sigma, []) None bound t in
  let holes = List.rev holes in
  let clause = { cl_concl = t; cl_holes = holes } in
  (sigma, clause)

let evar_with_name holes ({CAst.v=id} as lid) =
  let map h = match h.hole_name with
  | Anonymous -> None
  | Name id' -> if Id.equal id id' then Some h else None
  in
  let hole = List.map_filter map holes in
  match hole with
  | [] ->
    let fold h accu = match h.hole_name with
      | Anonymous -> accu
      | Name id -> id :: accu
    in
    let mvl = List.fold_right fold holes [] in
    explain_no_such_bound_variable mvl lid
  | h::_ -> h.hole_evar

let evar_of_binder holes = function
| NamedHyp s -> evar_with_name holes s
| AnonHyp n ->
  try
    let nondeps = List.filter (fun hole -> not hole.hole_deps) holes in
    let h = List.nth nondeps (pred n) in
    h.hole_evar
  with e when CErrors.noncritical e ->
    user_err Pp.(str "No such binder.")

let define_with_type sigma env ev c =
  let open EConstr in
  let t = Retyping.get_type_of env sigma ev in
  let ty = Retyping.get_type_of env sigma c in
  let j = Environ.make_judge c ty in
  let (sigma, j, _trace) = Coercion.inh_conv_coerce_to ~program_mode:false ~resolve_tc:true env sigma j t in
  let (ev, _) = destEvar sigma ev in
  let sigma = Evd.define ev j.Environ.uj_val sigma in
  sigma

let solve_evar_clause env sigma hyp_only clause = function
| NoBindings -> sigma
| ImplicitBindings largs ->
  let open EConstr in
  let fold holes h =
    if h.hole_deps then
      (* Some subsequent term uses the hole *)
      let (ev, _) = destEvar sigma h.hole_evar in
      let is_dep hole = occur_evar sigma ev hole.hole_type in
      let in_hyp = List.exists is_dep holes in
      let in_ccl = occur_evar sigma ev clause.cl_concl in
      let dep = if hyp_only then in_hyp && not in_ccl else in_hyp || in_ccl in
      let h = { h with hole_deps = dep } in
      h :: holes
    else
      (* The hole does not occur anywhere *)
      h :: holes
  in
  let holes = List.fold_left fold [] (List.rev clause.cl_holes) in
  let map h = if h.hole_deps then Some h.hole_evar else None in
  let evs = List.map_filter map holes in
  let len = List.length evs in
  if Int.equal len (List.length largs) then
    let fold sigma ev arg = define_with_type sigma env ev arg in
    let sigma = List.fold_left2 fold sigma evs largs in
    sigma
  else
    error_not_right_number_missing_arguments len
| ExplicitBindings lbind ->
  let () = check_bindings lbind in
  let fold sigma {CAst.v=(binder, c)} =
    let ev = evar_of_binder clause.cl_holes binder in
    define_with_type sigma env ev c
  in
  let sigma = List.fold_left fold sigma lbind in
  sigma

let check_evar_clause env sigma sigma' eq_clause =
  let f h = if h.hole_deps then Some h.hole_evar_key else None in
  match Tacticals.check_evar_list env sigma' (Evar.Set.of_list (List.map_filter f eq_clause.cl_holes)) sigma with
  | [] -> ()
  | evkl ->
    let filter h = if List.exists (Evar.equal h.hole_evar_key) evkl then Some h.hole_name else None in
    let bindings = List.map_filter filter eq_clause.cl_holes in
    Loc.raise (Logic.RefinerError (env, sigma, UnresolvedBindings bindings))
