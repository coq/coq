(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
  env : env;
  (** Built using statically-given names *)
  extra : (Evarutil.ext_named_context * Id.t Id.Map.t) Lazy.t;
  (** Delay the computation of the evar extended environment *)
  lvar : ltac_var_map;
  (** Possible interpretation of variables as names or terms *)
}

let make env sigma lvar =
  let get_extra env sigma =
    let avoid = Environ.ids_of_named_context_val (Environ.named_context_val env) in
    Context.Rel.fold_outside (fun d acc -> push_rel_decl_to_named_context sigma d acc)
      (rel_context env) ~init:(empty_csubst, avoid, named_context env) in
  {
    env = env;
    extra = lazy (get_extra env sigma, Id.Map.empty);
    lvar = lvar;
  }

let env env = env.env

let vars_of_env env =
  Id.Set.union (Id.Map.domain env.lvar.ltac_genargs) (vars_of_env env.env)

let ltac_interp_name { ltac_idents ; ltac_genargs } = function
  | Anonymous -> Anonymous
  | Name id as na ->
      try Name (Id.Map.find id ltac_idents)
      with Not_found ->
        if Id.Map.mem id ltac_genargs then
          user_err (str "Ltac variable" ++ spc () ++ Id.print id ++
                    spc () ++ str "is not bound to an identifier." ++
                    spc () ++str "It cannot be used in a binder.")
        else na

let push_rel_decl_to_named_context_upto_ltac_interp sigma static_d interpreted_d (extra,renaming) =
  let open Context.Rel.Declaration in
  let extra' = push_rel_decl_to_named_context ~hypnaming:KeepExistingNames sigma interpreted_d extra in
  let new_interpreted_id = Context.Named.Declaration.get_id (List.hd (pi3 extra')) in
  let renaming = match get_name static_d with
  | Name static_id -> Id.Map.add static_id new_interpreted_id renaming
  | _ -> renaming in
  (extra',renaming)

let push_rel sigma d env =
  let d' = Context.Rel.Declaration.map_name (ltac_interp_name env.lvar) d in
  let env = {
    env = push_rel d env.env;
    extra = lazy (push_rel_decl_to_named_context_upto_ltac_interp sigma d d' (Lazy.force env.extra));
    lvar = env.lvar;
    } in
  d', env

let push_rel_context ?(force_names=false) sigma ctx env =
  let open Context.Rel.Declaration in
  let ctx' = List.Smart.map (map_name (ltac_interp_name env.lvar)) ctx in
  let ctx' = if force_names then Namegen.name_context env.env sigma ctx' else ctx' in
  let env = {
    env = push_rel_context ctx env.env;
    extra = lazy (List.fold_right2 (push_rel_decl_to_named_context_upto_ltac_interp sigma) ctx ctx' (Lazy.force env.extra));
    lvar = env.lvar;
    } in
  ctx', env

let push_rec_types sigma (lna,typarray) env =
  let open Context.Rel.Declaration in
  let ctxt = Array.map2_i (fun i na t -> Context.Rel.Declaration.LocalAssum (na, lift i t)) lna typarray in
  let env,ctx = Array.fold_left_map (fun e assum -> let (d,e) = push_rel sigma assum e in (e,d)) env ctxt in
  Array.map get_name ctx, env

let new_evar ?src ?naming env sigma typ =
  let open Context.Named.Declaration in
  let inst_vars = List.map (get_id %> mkVar) (named_context env.env) in
  let inst_rels = List.rev (rel_list 0 (nb_rel env.env)) in
  let (subst, _, nc),_ = Lazy.force env.extra in
  let typ' = csubst_subst subst typ in
  let instance = inst_rels @ inst_vars in
  let sign = val_of_named_context nc in
  new_evar_instance sign sigma typ' ?src ?naming instance

let new_type_evar ~src env sigma =
  let (sigma', s) = Evd.new_sort_variable Evd.univ_flexible_alg sigma in
  new_evar ~src env sigma' (EConstr.mkSort s)

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

let protected_get_type_of env sigma c =
  try Retyping.get_type_of ~lax:true env sigma c
  with Retyping.RetypeError _ ->
    user_err
      (str "Cannot reinterpret " ++ quote (print_constr c) ++
       str " in the current environment.")

let invert_ltac_bound_name env id0 id =
  try mkRel (pi1 (lookup_rel_id id (rel_context env.env)))
  with Not_found ->
    user_err  (str "Ltac variable " ++ Id.print id0 ++
                       str " depends on pattern variable name " ++ Id.print id ++
                       str " which is not bound in current context.")

let interp_ltac_variable ?loc typing_fun env sigma id =
  (* Check if [id] is an ltac variable *)
  try
    let (ids,c) = Id.Map.find id env.lvar.ltac_constrs in
    let subst = List.map (invert_ltac_bound_name env id) ids in
    let c = substl subst c in
      { uj_val = c; uj_type = protected_get_type_of env.env sigma c }
  with Not_found ->
  try
    let {closure;term} = Id.Map.find id env.lvar.ltac_uconstrs in
    let lvar = {
      ltac_constrs = closure.typed;
      ltac_uconstrs = closure.untyped;
      ltac_idents = closure.idents;
      ltac_genargs = Id.Map.empty; }
    in
    (* spiwack: I'm catching [Not_found] potentially too eagerly
       here, as the call to the main pretyping function is caught
       inside the try but I want to avoid refactoring this function
       too much for now. *)
    typing_fun {env with lvar} term
  with Not_found ->
  (* Check if [id] is a ltac variable not bound to a term *)
  (* and build a nice error message *)
  if Id.Map.mem id env.lvar.ltac_genargs then begin
    let Geninterp.Val.Dyn (typ, _) = Id.Map.find id env.lvar.ltac_genargs in
    user_err ?loc
     (str "Variable " ++ Id.print id ++ str " should be bound to a term but is \
      bound to a " ++ Geninterp.Val.pr typ ++ str ".")
  end;
  raise Not_found

module ConstrInterpObj =
struct
  type ('r, 'g, 't) obj =
    unbound_ltac_var_map -> env -> Evd.evar_map -> types -> 'g -> constr * Evd.evar_map
  let name = "constr_interp"
  let default _ = None
end

module ConstrInterp = Genarg.Register(ConstrInterpObj)

let register_constr_interp0 = ConstrInterp.register0

let interp_glob_genarg env sigma ty arg =
  let open Genarg in
  let open Context.Named.Declaration in
  let (subst,_,sign),renaming = Lazy.force env.extra in
  (* We inform the ltac interpreter that variables of the original
     environment have been renamed *)
  let tag = Geninterp.val_tag (Topwit Geninterp.wit_ident) in
  let add id id' acc = Id.Map.add id (Geninterp.Val.inject tag id') acc in
  let ist = Id.Map.fold add renaming env.lvar.ltac_genargs in
  (* We prepare a typing context free with indices turned into names *)
  let nrel = nb_rel env.env in
  let env = reset_with_named_context (val_of_named_context sign) env.env in
  let ty = csubst_subst subst ty in
  (* We call the genarg interpreter *)
  let GenArg (Glbwit tag, arg) = arg in
  let interp = ConstrInterp.obj tag in
  let c,sigma = interp ist env sigma ty arg in
  (* We instantiate the result with the current environment *)
  let inst_rels = List.rev (rel_list 0 nrel) in
  let vars_to_inst = List.map get_id (List.firstn nrel sign) in
  let rev_subst = List.combine vars_to_inst inst_rels in
  replace_vars rev_subst c, sigma
