open Util
open Names
open Esubst
open Term
open Constr
open Declarations
open Genlambda
open Vmvalues
open Environ

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

let make_args start _end =
  Array.init (start - _end + 1) (fun i -> Lrel (Anonymous, start - i))

(* Translation of constructors *)
let expand_constructor ind tag nparams arity =
  let anon = Context.make_annot Anonymous Sorts.Relevant in (* TODO relevance *)
  let ids = Array.make (nparams + arity) anon in
  if arity = 0 then mkLlam ids (Lint tag)
  else
    let args = make_args arity 1 in
    Llam (ids, Lmakeblock (ind, tag, args))

let makeblock ind tag nparams arity args =
  let nargs = Array.length args in
  if nparams > 0 || nargs < arity then
    mkLapp (expand_constructor ind tag nparams arity) args
  else
    (* The constructor is fully applied *)
  if arity = 0 then Lint tag
  else
  if Array.for_all is_value args then
    if tag < Obj.last_non_constant_constructor_tag then
      Lval(val_of_block tag (Array.map get_value args))
    else
      let args = Array.map get_value args in
      let args = Array.append [| val_of_int (tag - Obj.last_non_constant_constructor_tag) |] args in
      Lval(val_of_block Obj.last_non_constant_constructor_tag args)
  else Lmakeblock (ind, tag, args)

let makearray args def = Lparray (args, def)

(* Compiling constants *)

let rec get_alias env kn =
  let cb = lookup_constant kn env in
  let tps = cb.const_body_code in
  match tps with
  | None -> kn
  | Some tps ->
    (match tps with
     | Vmemitcodes.BCalias kn' -> get_alias env kn'
     | _ -> kn)

(* Compilation of primitive *)

let prim kn p args =
  Lprim (kn, p, args)

let expand_prim kn op arity =
  (* primitives are always Relevant *)
  let ids = Array.make arity Context.anonR in
  let args = make_args arity 1 in
  Llam(ids, prim kn op args)

let lambda_of_prim kn op args =
  let arity = CPrimitives.arity op in
  match Int.compare (Array.length args) arity with
  | 0 -> prim kn op args
  | x when x > 0 ->
    let prim_args = Array.sub args 0 arity in
    let extra_args = Array.sub args arity (Array.length args - arity) in
    mkLapp(prim kn op prim_args) extra_args
  | _ -> mkLapp (expand_prim kn op arity) args

(*i Global environment *)

let get_names decl =
  let decl = Array.of_list decl in
  Array.map fst decl


(* Rel Environment *)
module Vect =
struct
  type 'a t = {
    mutable elems : 'a array;
    mutable size : int;
  }

  let make n a = {
    elems = Array.make n a;
    size = 0;
  }

  let extend (v : 'a t) =
    if v.size = Array.length v.elems then
      let new_size = min (2*v.size) Sys.max_array_length in
      if new_size <= v.size then raise (Invalid_argument "Vect.extend");
      let new_elems = Array.make new_size v.elems.(0) in
      Array.blit v.elems 0 new_elems 0 (v.size);
      v.elems <- new_elems

  let push v a =
    extend v;
    v.elems.(v.size) <- a;
    v.size <- v.size + 1

  let popn (v : 'a t) n =
    v.size <- max 0 (v.size - n)

  let pop v = popn v 1

  let get_last (v : 'a t) n =
    if v.size <= n then raise
        (Invalid_argument "Vect.get:index out of bounds");
    v.elems.(v.size - n - 1)

end

let dummy_lambda = Lrel(Anonymous, 0)

let empty_args = [||]

module Renv =
struct

  type constructor_info = tag * int * int (* nparam nrealargs *)

  type t = {
    global_env : env;
    evar_body : constr evar_handler;
    meta_type : metavariable -> types;
    name_rel : Name.t Vect.t;
    construct_tbl : (constructor, constructor_info) Hashtbl.t;
  }

  let make env sigma = {
    global_env = env;
    evar_body = sigma.evars_val;
    meta_type = sigma.evars_metas;
    name_rel = Vect.make 16 Anonymous;
    construct_tbl = Hashtbl.create 111
  }

  let push_rel env id = Vect.push env.name_rel id.Context.binder_name

  let push_rels env ids =
    Array.iter (push_rel env) ids

  let pop env = Vect.pop env.name_rel

  let popn env n =
    for _i = 1 to n do pop env done

  let get env n =
    Lrel (Vect.get_last env.name_rel (n-1), n)

  let get_construct_info env c =
    try Hashtbl.find env.construct_tbl c
    with Not_found ->
      let ((mind,j), i) = c in
      let oib = lookup_mind mind env.global_env in
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
    Renv.push_rel env id;
    let lc = lambda_of_constr env codom in
    Renv.pop env;
    Lprod(ld, Llam([|id|], lc))

  | Lambda _ ->
    let params, body = decompose_lam c in
    let ids = get_names (List.rev params) in
    Renv.push_rels env ids;
    let lb = lambda_of_constr env body in
    Renv.popn env (Array.length ids);
    mkLlam ids lb

  | LetIn(id, def, _, body) ->
    let ld = lambda_of_constr env def in
    Renv.push_rel env id;
    let lb = lambda_of_constr env body in
    Renv.pop env;
    Llet(id, ld, lb)

  | App(f, args) -> lambda_of_app env f args

  | Const _ -> lambda_of_app env c empty_args

  | Construct _ ->  lambda_of_app env c empty_args

  | Case (ci, u, pms, t, iv, a, br) -> (* XXX handle iv *)
    let (ci, t, _iv, a, branches) = Inductive.expand_case env.global_env (ci, u, pms, t, iv, a, br) in
    let ind = ci.ci_ind in
    let mib = lookup_mind (fst ind) env.global_env in
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
    Renv.push_rels env names;
    let lbodies = lambda_of_args env 0 rec_bodies in
    Renv.popn env (Array.length names);
    let dummy = [||] in (* FIXME: not used by the VM, requires the environment to be computed *)
    Lfix ((ln, dummy, i), (names, ltypes, lbodies))

  | CoFix(init,(names,type_bodies,rec_bodies)) ->
    let rec_bodies = Array.map2 (Reduction.eta_expand env.global_env) rec_bodies type_bodies in
    let ltypes = lambda_of_args env 0 type_bodies in
    Renv.push_rels env names;
    let lbodies = lambda_of_args env 0 rec_bodies in
    Renv.popn env (Array.length names);
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
      let kn = get_alias env.global_env kn in
      let cb = lookup_constant kn env.global_env in
      begin match cb.const_body with
      | Primitive op -> lambda_of_prim (kn,u) op (lambda_of_args env 0 args)
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
  let ids = List.rev_map Context.Rel.Declaration.get_annot (rel_context genv) in
  Renv.push_rels env (Array.of_list ids);
  let lam = lambda_of_constr env c in
  let lam = if optimize then optimize_lambda lam else lam in
  if !dump_lambda then
    Feedback.msg_debug (pp_lam lam);
  lam
