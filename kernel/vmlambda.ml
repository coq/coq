open Util
open Names
open Esubst
open Term
open Constr
open Declarations
open Genlambda
open Vmvalues
open Environ

module RelDecl = Context.Rel.Declaration

type lambda = structured_values Genlambda.lambda

(*s Operators on substitution *)
let subst_id = subs_id 0

(** Simplification of lambda expression *)

(* TODO: make the VM and native agree *)
let can_subst lam =
  match lam with
  | Lrel _ | Lvar _ | Lconst _ | Luint _
  | Lval _ | Lsort _ | Lind _ -> true
  | _ -> false

let simplify subst lam = simplify can_subst subst lam

(*s Translation from [constr] to [lambda] *)

(* Translation of constructor *)

(* Limitation due to OCaml's representation of non-constant
  constructors: limited to 245 + 1 (0 tag) cases. *)

exception TooLargeInductive of Pp.t

let max_nb_const = 0x1000000
let max_nb_block = 0x1000000 + Obj.last_non_constant_constructor_tag - 1

let str_max_constructors =
  Format.sprintf
    " which has more than %i constant constructors or more than %i non-constant constructors" max_nb_const max_nb_block

let check_compilable ib =

  if not (ib.mind_nb_args <= max_nb_block && ib.mind_nb_constant <= max_nb_const) then
    let msg =
      Pp.(str "Cannot compile code for virtual machine as it uses inductive "
          ++ Id.print ib.mind_typename ++ str str_max_constructors)
    in
    raise (TooLargeInductive msg)

let is_value lc =
  match lc with
  | Lval _ | Lint _ | Luint _ -> true
  | _ -> false

let get_value lc =
  match lc with
  | Luint i -> val_of_uint i
  | Lval v -> v
  | Lint i -> val_of_int i
  | _ -> raise Not_found

let as_value tag args =
  if Array.for_all is_value args then
    if tag < Obj.last_non_constant_constructor_tag then
      Some (val_of_block tag (Array.map get_value args))
    else
      let args = Array.map get_value args in
      let args = Array.append [| val_of_int (tag - Obj.last_non_constant_constructor_tag) |] args in
      Some (val_of_block Obj.last_non_constant_constructor_tag args)
  else None

(* Translation of constructors *)
let makeblock ind tag nparams arity args =
  Genlambda.makeblock as_value ind tag nparams arity args

let makearray args def = Lparray (args, def)

(*i Global environment *)

let get_names decl =
  let decl = Array.of_list decl in
  Array.map fst decl

let dummy_lambda = Lrel(Anonymous, 0)

let empty_args = [||]

module Renv =
struct

  type constructor_info = tag * int * int (* nparam nrealargs *)

  type t = {
    env : env;
    evar_body : constr evar_handler;
    meta_type : metavariable -> types;
    construct_tbl : (constructor, constructor_info) Hashtbl.t;
  }

  let make env sigma = {
    env = env;
    evar_body = sigma.evars_val;
    meta_type = sigma.evars_metas;
    construct_tbl = Hashtbl.create 111
  }

  let push_rel env decl = { env with env = Environ.push_rel decl env.env }

  let push_rels env decls = { env with env = Environ.push_rel_context decls env.env }

  let push_rec_types env rect = { env with env = Environ.push_rec_types rect env.env }

  let get env n =
    let na = RelDecl.get_name @@ Environ.lookup_rel n env.env in
    Lrel (na, n)

  let get_construct_info env c =
    try Hashtbl.find env.construct_tbl c
    with Not_found ->
      let ((mind,j), i) = c in
      let oib = lookup_mind mind env.env in
      let oip = oib.mind_packets.(j) in
      check_compilable oip;
      let tag,arity = oip.mind_reloc_tbl.(i-1) in
      let nparams = oib.mind_nparams in
      let r = (tag, nparams, arity) in
      Hashtbl.add env.construct_tbl c r;
      r
end

open Renv

let rec lambda_of_constr env c =
  match Constr.kind c with
  | Meta mv ->
    let ty = lambda_of_constr env (env.meta_type mv) in
    Lmeta (mv, ty)
  | Evar ev ->
    begin match env.evar_body.evar_expand ev with
    | Constr.EvarUndefined (evk, args) ->
        let args = Array.map_of_list (fun c -> lambda_of_constr env c) args in
        Levar (evk, args)
    | Constr.EvarDefined t -> lambda_of_constr env t
    end

  | Cast (c, _, _) -> lambda_of_constr env c

  | Rel i -> Renv.get env i

  | Var id -> Lvar id

  | Sort s -> Lsort s
  | Ind ind -> Lind ind

  | Prod(id, dom, codom) ->
    let ld = lambda_of_constr env dom in
    let nenv = Renv.push_rel env (RelDecl.LocalAssum (id, dom)) in
    let lc = lambda_of_constr nenv codom in
    Lprod(ld, Llam([|id|], lc))

  | Lambda _ ->
    let params, body = decompose_lam c in
    let decls = List.map (fun (id, dom) -> RelDecl.LocalAssum (id, dom)) params in
    let nenv = Renv.push_rels env decls in
    let lb = lambda_of_constr nenv body in
    mkLlam (get_names (List.rev params)) lb

  | LetIn(id, def, ty, body) ->
    let ld = lambda_of_constr env def in
    let nenv = Renv.push_rel env (RelDecl.LocalDef (id, def, ty)) in
    let lb = lambda_of_constr nenv body in
    Llet(id, ld, lb)

  | App(f, args) -> lambda_of_app env f args

  | Const _ -> lambda_of_app env c empty_args

  | Construct _ ->  lambda_of_app env c empty_args

  | Case (ci, u, pms, t, iv, a, br) -> (* XXX handle iv *)
    let (ci, t, _iv, a, branches) = Inductive.expand_case env.env (ci, u, pms, t, iv, a, br) in
    let ind = ci.ci_ind in
    let mib = lookup_mind (fst ind) env.env in
    let oib = mib.mind_packets.(snd ind) in
    let () = check_compilable oib in
    let rtbl = oib.mind_reloc_tbl in


    (* translation of the argument *)
    let la = lambda_of_constr env a in
    (* translation of the type *)
    let lt = lambda_of_constr env t in
    (* translation of branches *)
    let consts = Array.make oib.mind_nb_constant dummy_lambda in
    let blocks = Array.make oib.mind_nb_args ([||],dummy_lambda) in
    for i = 0 to Array.length rtbl - 1 do
      let tag, arity = rtbl.(i) in
      let b = lambda_of_constr env branches.(i) in
      if arity = 0 then consts.(tag) <- b
      else
        let b =
          match b with
          | Llam(ids, body) when Array.length ids = arity -> (ids, body)
          | _ ->
            let anon = Context.make_annot Anonymous Sorts.Relevant in (* TODO relevance *)
            let ids = Array.make arity anon in
            let args = make_args arity 1 in
            let ll = lam_lift arity b in
            (ids, mkLapp  ll args)
        in blocks.(tag-1) <- b
    done;
    let branches =
      { constant_branches = consts;
        nonconstant_branches = blocks }
    in
    let annot = (ci, rtbl, mib.mind_finite) in
    Lcase (annot, lt, la, branches)

  | Fix ((ln, i), (names, type_bodies, rec_bodies)) ->
    let ltypes = lambda_of_args env 0 type_bodies in
    let nenv = Renv.push_rec_types env (names, type_bodies, rec_bodies) in
    let lbodies = lambda_of_args nenv 0 rec_bodies in
    let dummy = [||] in (* FIXME: not used by the VM, requires the environment to be computed *)
    Lfix ((ln, dummy, i), (names, ltypes, lbodies))

  | CoFix(init,(names,type_bodies,rec_bodies)) ->
    let rec_bodies = Array.map2 (Reduction.eta_expand env.env) rec_bodies type_bodies in
    let ltypes = lambda_of_args env 0 type_bodies in
    let nenv = Renv.push_rec_types env (names, type_bodies, rec_bodies) in
    let lbodies = lambda_of_args nenv 0 rec_bodies in
    Lcofix(init, (names, ltypes, lbodies))

  | Proj (p,c) ->
    let lc = lambda_of_constr env c in
    Lproj (Projection.repr p,lc)

  | Int i -> Luint i
  | Float f -> Lfloat f
  | Array(_u, t,def,_ty) ->
    let def = lambda_of_constr env def in
    makearray (lambda_of_args env 0 t) def

and lambda_of_app env f args =
  match Constr.kind f with
  | Const (kn,u as c) ->
      let kn = get_alias env.env kn in
      let cb = lookup_constant kn env.env in
      begin match cb.const_body with
      | Primitive op -> lambda_of_prim env.env (kn,u) op (lambda_of_args env 0 args)
      | Def csubst when cb.const_inline_code ->
          lambda_of_app env csubst args
      | Def _ | OpaqueDef _ | Undef _ -> mkLapp (Lconst c) (lambda_of_args env 0 args)
      end
  | Construct (c,_) ->
      let tag, nparams, arity = Renv.get_construct_info env c in
      let nargs = Array.length args in
      if nparams < nargs then (* got all parameters *)
        let args = lambda_of_args env nparams args in
        makeblock (fst c) tag 0 arity args
      else makeblock (fst c) tag (nparams - nargs) arity empty_args
  | _ ->
      let f = lambda_of_constr env f in
      let args = lambda_of_args env 0 args in
      mkLapp f args

and lambda_of_args env start args =
  let nargs = Array.length args in
  if start < nargs then
    Array.init (nargs - start)
      (fun i -> lambda_of_constr env args.(start + i))
  else empty_args

(*********************************)
let dump_lambda = ref false

let optimize_lambda lam =
  let lam = simplify subst_id lam in
  remove_let subst_id lam

let lambda_of_constr ~optimize genv sigma c =
  let env = Renv.make genv sigma in
  let lam = lambda_of_constr env c in
  let lam = if optimize then optimize_lambda lam else lam in
  if !dump_lambda then
    Feedback.msg_debug (pp_lam lam);
  lam
