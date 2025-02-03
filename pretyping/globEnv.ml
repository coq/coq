(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp
open CErrors
open Names
open Environ
open EConstr
open Evarutil
open Termops
open Vars
open Ltac_pretype

(** This files provides a level of abstraction for the kind of
    environment used for type inference (so-called pretyping); in
    particular:
    - it supports that term variables can be interpreted as Ltac
      variables pointing to the effective expected name
    - it incrementally and lazily computes the renaming of rel
      variables used to build purely-named evar contexts
*)

type t = {
  static_env : env;
  (** For locating indices *)
  renamed_env : env;
  (** For name management *)
  extra : ext_named_context Lazy.t;
  (** Delay the computation of the evar extended environment *)
  lvar : ltac_var_map;
}

let make ~hypnaming env sigma lvar =
  let get_extra env sigma =
    let avoid = Environ.ids_of_named_context_val (Environ.named_context_val env) in
    Context.Rel.fold_outside (fun d acc -> push_rel_decl_to_named_context ~hypnaming sigma d acc)
      (rel_context env) ~init:(empty_csubst, avoid, named_context_val env) in
  {
    static_env = env;
    renamed_env = env;
    extra = lazy (get_extra env sigma);
    lvar = lvar;
  }

let env env = env.static_env
let renamed_env env = env.renamed_env
let lfun env = env.lvar.ltac_genargs

let vars_of_env env =
  Id.Set.union (Id.Map.domain env.lvar.ltac_genargs) (vars_of_env env.static_env)

let ltac_interp_id { ltac_idents ; ltac_genargs } id =
  try Id.Map.find id ltac_idents
  with Not_found ->
    if Id.Map.mem id ltac_genargs then
      user_err (str "Ltac variable" ++ spc () ++ Id.print id ++
                spc () ++ str "is not bound to an identifier." ++
                spc () ++str "It cannot be used in a binder.")
    else id

let ltac_interp_name lvar = Nameops.Name.map (ltac_interp_id lvar)

let push_rel ~hypnaming sigma d env =
  let open Context.Rel.Declaration in
  let d' = map_name (ltac_interp_name env.lvar) d in
  let env = {
    static_env = push_rel d env.static_env;
    renamed_env = push_rel d' env.renamed_env;
    extra = lazy (push_rel_decl_to_named_context ~hypnaming:hypnaming sigma d' (Lazy.force env.extra));
    lvar = env.lvar;
    } in
  d', env

let push_rel_context ~hypnaming ?(force_names=false) sigma ctx env =
  let open Context.Rel.Declaration in
  let ctx' = List.Smart.map (map_name (ltac_interp_name env.lvar)) ctx in
  let ctx' = if force_names then Namegen.name_context env.renamed_env sigma ctx' else ctx' in
  let env = {
    static_env = push_rel_context ctx env.static_env;
    renamed_env = push_rel_context ctx' env.renamed_env;
    extra = lazy (List.fold_right (fun d acc -> push_rel_decl_to_named_context ~hypnaming:hypnaming sigma d acc) ctx' (Lazy.force env.extra));
    lvar = env.lvar;
    } in
  ctx', env

let push_rec_types ~hypnaming sigma (lna,typarray) env =
  let open Context.Rel.Declaration in
  let ctxt = Array.map2_i (fun i na t -> Context.Rel.Declaration.LocalAssum (na, lift i t)) lna typarray in
  let env,ctx = Array.fold_left_map (fun e assum -> let (d,e) = push_rel sigma assum e ~hypnaming in (e,d)) env ctxt in
  Array.map get_annot ctx, env

let new_evar env sigma ?src ?(naming = Namegen.IntroAnonymous) ?relevance typ =
  let (subst, _, sign) as ext = Lazy.force env.extra in
  let instance = Evarutil.default_ext_instance ext in
  let typ' = csubst_subst sigma subst typ in
  let name = Evarutil.next_evar_name sigma naming in
  let relevance = match relevance with
    | Some r -> r
    | None -> Retyping.relevance_of_type env.static_env sigma typ
  in
  let (sigma, evk) = new_pure_evar sign sigma typ' ?src ~relevance ?name in
  (sigma, mkEvar (evk, instance))

let new_type_evar env sigma ~src =
  let sigma, s = Evd.new_sort_variable Evd.univ_flexible_alg sigma in
  new_evar env sigma ~src (EConstr.mkSort s) ~relevance:ERelevance.relevant

let hide_variable env expansion id =
  let lvar = env.lvar in
  if Id.Map.mem id lvar.ltac_genargs then
    let lvar = match expansion with
    | Name id' ->
       (* We are typically in a situation [match id return P with ... end]
          which we interpret as [match id' as id' return P with ... end],
          with [P] interpreted in an environment where [id] is bound to [id'].
          The variable is already bound to [id'], so nothing to do *)
       lvar
    | _ ->
       (* We are typically in a situation [match id return P with ... end]
          with [id] bound to a non-variable term [c]. We interpret as
         [match c as id return P with ... end], and hides [id] while
         interpreting [P], since it has become a binder and cannot be anymore be
         substituted by a variable coming from the Ltac substitution. *)
       { lvar with
         ltac_uconstrs = Id.Map.remove id lvar.ltac_uconstrs;
         ltac_constrs = Id.Map.remove id lvar.ltac_constrs;
         ltac_genargs = Id.Map.remove id lvar.ltac_genargs } in
    { env with lvar }
  else
    env

let invert_ltac_bound_name env id0 id =
  try mkRel (pi1 (lookup_rel_id id (rel_context env.static_env)))
  with Not_found ->
    user_err  (str "Ltac variable " ++ Id.print id0 ++
                       str " depends on pattern variable name " ++ Id.print id ++
                       str " which is not bound in current context.")

let interp_ltac_variable ?loc typing_fun env sigma id : Evd.evar_map * unsafe_judgment =
  (* Check if [id] is an ltac variable *)
  match Id.Map.find_opt id env.lvar.ltac_constrs with
  | Some (ids, c) ->
    let subst = List.map (invert_ltac_bound_name env id) ids in
    let c = substl subst c in
    sigma, { uj_val = c; uj_type = Retyping.reinterpret_get_type_of ~src:id env.renamed_env sigma c }
  | None ->
  match Id.Map.find_opt id env.lvar.ltac_uconstrs with
  | Some {closure;term} ->
    let lvar = {
      ltac_constrs = closure.typed;
      ltac_uconstrs = closure.untyped;
      ltac_idents = closure.idents;
      ltac_genargs = closure.genargs; }
    in
    (* spiwack: I'm catching [Not_found] potentially too eagerly
       here, as the call to the main pretyping function is caught
       inside the try but I want to avoid refactoring this function
       too much for now. *)
    typing_fun {env with lvar; static_env = env.renamed_env} term
  | None ->
  (* Check if [id] is a ltac variable not bound to a term *)
  (* and build a nice error message *)
  if Id.Map.mem id env.lvar.ltac_idents then begin
    let bnd = Id.Map.find id env.lvar.ltac_idents in
    user_err ?loc
     (str "Variable " ++ Id.print id ++ str " should be bound to a term but is \
      bound to the identifier " ++ quote (Id.print bnd) ++ str ".")
  end;
  if Id.Map.mem id env.lvar.ltac_genargs then begin
    let Geninterp.Val.Dyn (typ, _) = Id.Map.find id env.lvar.ltac_genargs in
    user_err ?loc
     (str "Variable " ++ Id.print id ++ str " should be bound to a term but is \
      bound to a " ++ Geninterp.Val.pr typ ++ str ".")
  end;
  raise Not_found

let interp_ltac_id env id = ltac_interp_id env.lvar id

type 'a obj_interp_fun =
  ?loc:Loc.t -> poly:bool -> t -> Evd.evar_map -> Evardefine.type_constraint ->
  'a -> unsafe_judgment * Evd.evar_map

module ConstrInterpObj =
struct
  type ('r, 'g, 't) obj = 'g obj_interp_fun
  let name = "constr_interp"
  let default _ = None
end

module ConstrInterp = Genarg.Register(ConstrInterpObj)

let register_constr_interp0 = ConstrInterp.register0

let interp_glob_genarg ?loc ~poly env sigma ty arg =
  let open Genarg in
  let GenArg (Glbwit tag, arg) = arg in
  let interp = ConstrInterp.obj tag in
  interp ?loc ~poly env sigma ty arg
