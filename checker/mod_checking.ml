
open Pp
open Util
open Names
open Cic
open Term
open Reduction
open Typeops
open Indtypes
open Modops
open Subtyping
open Declarations
open Environ

(** {6 Checking constants } *)

let refresh_arity ar =
  let ctxt, hd = decompose_prod_assum ar in
  match hd with
      Sort (Type u) when not (Univ.is_univ_variable u) ->
        let u' = Univ.Universe.make (Univ.Level.make empty_dirpath 1) in
        mkArity (ctxt,Prop Null), 
	  Univ.enforce_leq u u' Univ.empty_constraint
    | _ -> ar, Univ.empty_constraint

let check_constant_declaration env kn cb =
  Flags.if_verbose ppnl (str "  checking cst: " ++ prcon kn); pp_flush ();
  let env' = add_constraints (Univ.UContext.constraints cb.const_universes) env in
  let envty, ty = 
    match cb.const_type with
      RegularArity ty ->
        let ty', cu = refresh_arity ty in
        let envty = add_constraints cu env' in
        let _ = infer_type envty ty' in envty, ty
    | TemplateArity(ctxt,par) ->
        let _ = check_ctxt env' ctxt in
        check_polymorphic_arity env' ctxt par;
	env', it_mkProd_or_LetIn (Sort(Type par.template_level)) ctxt 
  in
  let () = 
    match body_of_constant cb with
    | Some bd ->
      (match cb.const_proj with 
      | None -> let j = infer envty bd in
		  conv_leq envty j ty
      | Some pb -> 
	let env' = add_constant kn cb env' in
	let j = infer env' bd in
	  conv_leq envty j ty)
    | None -> ()
  in
  if cb.const_polymorphic then add_constant kn cb env
  else add_constant kn cb env'

(** {6 Checking modules } *)

(** We currently ignore the [mod_type_alg] and [typ_expr_alg] fields.
    The only delicate part is when [mod_expr] is an algebraic expression :
    we need to expand it before checking it is indeed a subtype of [mod_type].
    Fortunately, [mod_expr] cannot contain any [MEwith]. *)

let lookup_module mp env =
  try Environ.lookup_module mp env
  with Not_found ->
    failwith ("Unknown module: "^string_of_mp mp)

let mk_mtb mp sign delta =
  { mod_mp = mp;
    mod_expr = Abstract;
    mod_type = sign;
    mod_type_alg = None;
    mod_constraints = Univ.Constraint.empty;
    mod_delta = delta;
    mod_retroknowledge = []; }

let rec check_module env mp mb =
  let (_:module_signature) =
    check_signature env mb.mod_type mb.mod_mp mb.mod_delta
  in
  let optsign = match mb.mod_expr with
    |Struct sign -> Some (check_signature env sign mb.mod_mp mb.mod_delta)
    |Algebraic me -> Some (check_mexpression env me mb.mod_mp mb.mod_delta)
    |Abstract|FullStruct -> None
  in
  match optsign with
  |None -> ()
  |Some sign ->
    let mtb1 = mk_mtb mp sign mb.mod_delta
    and mtb2 = mk_mtb mp mb.mod_type mb.mod_delta in
    let env = add_module_type mp mtb1 env in
    Subtyping.check_subtypes env mtb1 mtb2

and check_module_type env mty =
  let (_:module_signature) =
    check_signature env mty.mod_type mty.mod_mp mty.mod_delta in
  ()

and check_structure_field env mp lab res = function
  | SFBconst cb ->
      let c = Constant.make2 mp lab in
      check_constant_declaration env c cb
  | SFBmind mib ->
      let kn = MutInd.make2 mp lab in
      let kn = mind_of_delta res kn in
      Indtypes.check_inductive env kn mib
  | SFBmodule msb ->
      let () = check_module env (MPdot(mp,lab)) msb in
      Modops.add_module msb env
  | SFBmodtype mty ->
      check_module_type env mty;
      add_modtype (MPdot(mp,lab)) mty env

and check_mexpr env mse mp_mse res = match mse with
  | MEident mp ->
      let mb = lookup_module mp env in
      (subst_and_strengthen mb mp_mse).mod_type
  | MEapply (f,mp) ->
      let sign = check_mexpr env f mp_mse res in
      let farg_id, farg_b, fbody_b = destr_functor sign in
      let mtb = module_type_of_module (Some mp) (lookup_module mp env) in
      check_subtypes env mtb farg_b;
      subst_signature (map_mbid farg_id mp) fbody_b
  | MEwith _ -> error_with_module ()

and check_mexpression env sign mp_mse res = match sign with
  | MoreFunctor (arg_id, mtb, body) ->
      check_module_type env mtb;
      let env' = add_module_type (MPbound arg_id) mtb env in
      let body = check_mexpression env' body mp_mse res in
      MoreFunctor(arg_id,mtb,body)
  | NoFunctor me -> check_mexpr env me mp_mse res

and check_signature env sign mp_mse res = match sign with
  | MoreFunctor (arg_id, mtb, body) ->
      check_module_type env mtb;
      let env' = add_module_type (MPbound arg_id) mtb env in
      let body = check_signature env' body mp_mse res in
      MoreFunctor(arg_id,mtb,body)
  | NoFunctor struc ->
      let (_:env) = List.fold_left (fun env (lab,mb) ->
	check_structure_field env mp_mse lab res mb) env struc
      in
      NoFunctor struc
