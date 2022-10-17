(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Util
open Names
open Esubst
open Constr
open Declarations
open Environ
open Genlambda
open Nativevalues

module RelDecl = Context.Rel.Declaration

(** This file defines the lambda code generation phase of the native compiler *)
type prefix = string

type lambda = Nativevalues.t Genlambda.lambda

(*s Constructors *)

(*s Operators on substitution *)
let subst_id = subs_id 0

(* Linked code location utilities *)
let get_mind_prefix env mind =
   let _,name = lookup_mind_key mind env in
   match !name with
   | NotLinked -> ""
   | Linked s -> s

let get_const_prefix env c =
   let _,(nameref,_) = lookup_constant_key c env in
   match !nameref with
   | NotLinked -> ""
   | Linked s -> s

(** Simplification of lambda expression *)

(* TODO: make the VM and native agree *)
let can_subst lam =
  match lam with
  | Lrel _ | Lvar _ | Lconst _ | Lval _ | Lsort _ | Lind _ | Llam _
  | Lmeta _ | Levar _ -> true
  | _ -> false

let simplify subst lam = simplify can_subst subst lam

(*s Translation from [constr] to [lambda] *)

(* Translation of constructor *)

let is_value lc =
  match lc with
  | Lval _ | Lint _ | Luint _ | Lfloat _ -> true
  | _ -> false

let get_value lc =
  match lc with
  | Lval v -> v
  | Lint tag -> Nativevalues.mk_int tag
  | Luint i -> Nativevalues.mk_uint i
  | Lfloat f -> Nativevalues.mk_float f
  | _ -> raise Not_found

(* Translation of constructors *)
let expand_constructor ind tag nparams arity =
  let anon = Context.make_annot Anonymous Sorts.Relevant in (* TODO relevance *)
  let ids = Array.make (nparams + arity) anon in
  if Int.equal arity 0 then mkLlam ids (Lint tag)
  else
  let args = make_args arity 1 in
  Llam(ids, Lmakeblock (ind, tag, args))

(* [nparams] is the number of parameters still expected *)
let makeblock _env ind tag nparams arity args =
  let nargs = Array.length args in
  if nparams > 0 || nargs < arity then
    mkLapp (expand_constructor ind tag nparams arity) args
  else
  (* The constructor is fully applied *)
  if Int.equal arity 0 then Lint tag
  else
  if Array.for_all is_value args then
    let dummy_val = Obj.magic 0 in
    let args =
      (* Don't simplify this to Array.map, cf. the related comment in
         function eval_to_patch, file kernel/csymtable.ml *)
      let a = Array.make (Array.length args) dummy_val in
      Array.iteri (fun i v -> a.(i) <- get_value v) args; a in
    Lval (Nativevalues.mk_block tag args)
  else
    Lmakeblock(ind, tag, args)

let makearray args def =
  Lparray (args, def)

(*i Global environment *)

let get_names decl =
  let decl = Array.of_list decl in
  Array.map fst decl

let empty_args = [||]

module Cache =
  struct

    module ConstrHash =
    struct
      type t = constructor
      let equal = Construct.CanOrd.equal
      let hash = Construct.CanOrd.hash
    end

    module ConstrTable = Hashtbl.Make(ConstrHash)

    type constructor_info = tag * int * int (* nparam nrealargs *)

    let get_construct_info cache env c : constructor_info =
      try ConstrTable.find cache c
      with Not_found ->
        let ((mind,j), i) = c in
        let oib = lookup_mind mind env in
        let oip = oib.mind_packets.(j) in
        let tag,arity = oip.mind_reloc_tbl.(i-1) in
        let nparams = oib.mind_nparams in
        let r = (tag, nparams, arity) in
        ConstrTable.add cache c r;
        r
  end

let is_lazy t =
  match Constr.kind t with
  | App _ | LetIn _ | Case _ | Proj _ -> true
  | _ -> false

let evar_value sigma ev = sigma.evars_val.evar_expand ev

let meta_type sigma mv = sigma.evars_metas mv

(** Extract the inductive type over which a fixpoint is decreasing *)
let rec get_fix_struct env i t = match kind (Reduction.whd_all env t) with
| Prod (na, dom, t) ->
  if Int.equal i 0 then
    let dom = Reduction.whd_all env dom in
    let (dom, _) = decompose_appvect dom in
    match kind dom with
    | Ind (ind, _) -> ind
    | _ -> assert false
  else
    let env = Environ.push_rel (RelDecl.LocalAssum (na, dom)) env in
    get_fix_struct env (i - 1) t
| _ -> assert false

let rec lambda_of_constr cache env sigma c =
  match kind c with
  | Meta mv ->
     let ty = meta_type sigma mv in
     Lmeta (mv, lambda_of_constr cache env sigma ty)

  | Evar ev ->
     (match evar_value sigma ev with
     | Constr.EvarUndefined (evk, args) ->
        let args = Array.map_of_list (fun c -> lambda_of_constr cache env sigma c) args in
        Levar(evk, args)
     | Constr.EvarDefined t -> lambda_of_constr cache env sigma t)

  | Cast (c, _, _) -> lambda_of_constr cache env sigma c

  | Rel i -> Lrel (RelDecl.get_name (Environ.lookup_rel i env), i)

  | Var id -> Lvar id

  | Sort s -> Lsort s

  | Ind pind -> Lind pind

  | Prod(id, dom, codom) ->
      let ld = lambda_of_constr cache env sigma dom in
      let env = Environ.push_rel (RelDecl.LocalAssum (id, dom)) env in
      let lc = lambda_of_constr cache env sigma codom in
      Lprod(ld,  Llam([|id|], lc))

  | Lambda _ ->
      let params, body = Term.decompose_lam c in
      let fold (na, t) env = Environ.push_rel (RelDecl.LocalAssum (na, t)) env in
      let env = List.fold_right fold params env in
      let lb = lambda_of_constr cache env sigma body in
      let ids = get_names (List.rev params) in
      mkLlam ids lb

  | LetIn(id, def, t, body) ->
      let ld = lambda_of_constr cache env sigma def in
      let env = Environ.push_rel (RelDecl.LocalDef (id, def, t)) env in
      let lb = lambda_of_constr cache env sigma body in
      Llet(id, ld, lb)

  | App(f, args) -> lambda_of_app cache env sigma f args

  | Const _ -> lambda_of_app cache env sigma c empty_args

  | Construct _ ->  lambda_of_app cache env sigma c empty_args

  | Proj (p, c) ->
    let c = lambda_of_constr cache env sigma c in
    Lproj (Projection.repr p, c)

  | Case (ci, u, pms, t, iv, a, br) -> (* XXX handle iv *)
    let (ci, t, _iv, a, branches) = Inductive.expand_case env (ci, u, pms, t, iv, a, br) in
    let (mind, i) = ci.ci_ind in
    let mib = lookup_mind mind env in
    let oib = mib.mind_packets.(i) in
    let tbl = oib.mind_reloc_tbl in
    (* Building info *)
    let annot_sw = (ci, tbl, mib.mind_finite) in
    (* translation of the argument *)
    let la = lambda_of_constr cache env sigma a in
    (* translation of the type *)
    let lt = lambda_of_constr cache env sigma t in
    (* translation of branches *)
    let dummy = Lrel(Anonymous,0) in
    let consts = Array.make oib.mind_nb_constant dummy in
    let blocks = Array.make oib.mind_nb_args ([||],dummy) in
    let rtbl = oib.mind_reloc_tbl in
    for i = 0 to Array.length rtbl - 1 do
      let tag, arity = rtbl.(i) in
      let b = lambda_of_constr cache env sigma branches.(i) in
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
    Lcase(annot_sw, lt, la, branches)

  | Fix((pos, i), (names,type_bodies,rec_bodies)) ->
      let ltypes = lambda_of_args cache env sigma 0 type_bodies in
      let map i t = get_fix_struct env i t in
      let inds = Array.map2 map pos type_bodies in
      let env = Environ.push_rec_types (names, type_bodies, rec_bodies) env in
      let lbodies = lambda_of_args cache env sigma 0 rec_bodies in
      Lfix((pos, inds, i), (names, ltypes, lbodies))

  | CoFix(init,(names,type_bodies,rec_bodies)) ->
      let rec_bodies = Array.map2 (Reduction.eta_expand env) rec_bodies type_bodies in
      let ltypes = lambda_of_args cache env sigma 0 type_bodies in
      let env = Environ.push_rec_types (names, type_bodies, rec_bodies) env in
      let lbodies = lambda_of_args cache env sigma 0 rec_bodies in
      Lcofix(init, (names, ltypes, lbodies))

  | Int i -> Luint i

  | Float f -> Lfloat f

  | Array (_u, t, def, _ty) ->
    let def = lambda_of_constr cache env sigma def in
    makearray (lambda_of_args cache env sigma 0 t) def

and lambda_of_app cache env sigma f args =
  match kind f with
  | Const (kn, u as c) ->
      let kn = get_alias env kn in
      let cb = lookup_constant kn env in
      begin match cb.const_body with
      | Primitive op -> lambda_of_prim env c op (lambda_of_args cache env sigma 0 args)
      | Def csubst -> (* TODO optimize if f is a proj and argument is known *)
          if cb.const_inline_code then
            lambda_of_app cache env sigma csubst args
          else
          let t =
            if is_lazy csubst then
              mkLapp Lforce [|Lconst (kn, u)|]
            else Lconst (kn, u)
          in
        mkLapp t (lambda_of_args cache env sigma 0 args)
      | OpaqueDef _ | Undef _ ->
          mkLapp (Lconst (kn, u)) (lambda_of_args cache env sigma 0 args)
      end
  | Construct ((ind,_ as c),_) ->
    let tag, nparams, arity = Cache.get_construct_info cache env c in
    let nargs = Array.length args in
    if nparams < nargs then (* got all parameters *)
      let args = lambda_of_args cache env sigma nparams args in
      makeblock env ind tag 0 arity args
    else makeblock env ind tag (nparams - nargs) arity empty_args
  | _ ->
      let f = lambda_of_constr cache env sigma f in
      let args = lambda_of_args cache env sigma 0 args in
      mkLapp f args

and lambda_of_args cache env sigma start args =
  let nargs = Array.length args in
  if start < nargs then
    Array.init (nargs - start)
      (fun i -> lambda_of_constr cache env sigma args.(start + i))
  else empty_args

let optimize lam =
  let lam = simplify subst_id lam in
(*  if Flags.vm_draw_opt () then
    (msgerrnl (str "Simplify = \n" ++ pp_lam lam);flush_all());
  let lam = remove_let subst_id lam in
  if Flags.vm_draw_opt () then
    (msgerrnl (str "Remove let = \n" ++ pp_lam lam);flush_all()); *)
  lam

let lambda_of_constr env sigma c =
  let cache = Cache.ConstrTable.create 91 in
  let lam = lambda_of_constr cache env sigma c in
(*  if Flags.vm_draw_opt () then begin
    (msgerrnl (str "Constr = \n" ++ pr_constr c);flush_all());
    (msgerrnl (str "Lambda = \n" ++ pp_lam lam);flush_all());
  end; *)
  optimize lam
