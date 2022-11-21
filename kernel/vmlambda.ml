open Util
open Names
open Esubst
open Term
open Constr
open Declarations
open Vmvalues
open Environ
open Pp

let pr_con sp = str(Names.Label.to_string (Constant.label sp))

module RelDecl = Context.Rel.Declaration

type lambda =
  | Lrel          of Name.t * int
  | Lvar          of Id.t
  | Levar         of Evar.t * lambda array
  | Lprod         of lambda * lambda
  | Llam          of Name.t Context.binder_annot array * lambda
  | Llet          of Name.t Context.binder_annot * lambda * lambda
  | Lapp          of lambda * lambda array
  | Lconst        of pconstant
  | Lprim         of pconstant * CPrimitives.t * lambda array
  | Lcase         of case_info * reloc_table * lambda * lambda * lam_branches
  | Lfix          of (int array * int) * fix_decl
  | Lcofix        of int * fix_decl
  | Lint          of int
  | Lmakeblock    of int * lambda array
  | Luint         of Uint63.t
  | Lfloat        of Float64.t
  | Lval          of structured_values
  | Lsort         of Sorts.t
  | Lind          of pinductive
  | Lproj         of Projection.Repr.t * lambda

(* We separate branches for constant and non-constant constructors. If the OCaml
   limitation on non-constant constructors is reached, remaining branches are
   stored in [extra_branches]. *)
and lam_branches =
  { constant_branches : lambda array;
    nonconstant_branches : (Name.t Context.binder_annot array * lambda) array }
(*    extra_branches : (name array * lambda) array } *)

and fix_decl =  Name.t Context.binder_annot array * lambda array * lambda array

(** Printing **)

let pr_annot x = Name.print x.Context.binder_name

let pp_names ids =
  prlist_with_sep (fun _ -> brk(1,1)) pr_annot (Array.to_list ids)

let pp_rel name n =
  Name.print name ++  str "##" ++ int n

let pp_sort s =
  match Sorts.family s with
  | InSet -> str "Set"
  | InProp -> str "Prop"
  | InSProp -> str "SProp"
  | InType -> str "Type"

let rec pp_lam lam =
  match lam with
  | Lrel (id,n) -> pp_rel id n
  | Lvar id -> Id.print id
  | Levar (evk, args) ->
    hov 1 (str "evar(" ++ Evar.print evk ++ str "," ++ spc () ++
      prlist_with_sep spc pp_lam (Array.to_list args) ++ str ")")
  | Lprod(dom,codom) -> hov 1
                          (str "forall(" ++
                           pp_lam dom ++
                           str "," ++ spc() ++
                           pp_lam codom ++
                           str ")")
  | Llam(ids,body) -> hov 1
                        (str "(fun " ++
                         pp_names ids ++
                         str " =>" ++
                         spc() ++
                         pp_lam body ++
                         str ")")
  | Llet(id,def,body) -> hov 0
                           (str "let " ++
                            pr_annot id ++
                            str ":=" ++
                            pp_lam def  ++
                            str " in" ++
                            spc() ++
                            pp_lam body)
  | Lapp(f, args) -> hov 1
                       (str "(" ++ pp_lam f ++ spc() ++
                        prlist_with_sep spc pp_lam (Array.to_list args) ++
                        str")")
  | Lconst (kn,_) -> pr_con kn
  | Lcase(_ci, _rtbl, t, a, branches) ->
    let ic = ref (-1) in
    let ib = ref 0 in
    v 0 (str"<" ++ pp_lam t ++ str">" ++ cut() ++
         str "Case" ++ spc () ++ pp_lam a ++ spc() ++ str "of" ++ cut() ++
         v 0
           ((prlist_with_sep (fun _ -> str "")
               (fun c ->
                  cut () ++ str "| " ++
                  int (incr ic; !ic) ++ str " => " ++ pp_lam c)
               (Array.to_list branches.constant_branches)) ++
            (prlist_with_sep (fun _ -> str "")
               (fun (ids,c) ->
                  cut () ++ str "| " ++
                  int (incr ib; !ib) ++ str " " ++
                  pp_names ids ++ str " => " ++ pp_lam c)
               (Array.to_list branches.nonconstant_branches)))
         ++ cut() ++ str "end")
  | Lfix((t,i),(lna,tl,bl)) ->
    let fixl = Array.mapi (fun i id -> (id,t.(i),tl.(i),bl.(i))) lna in
    hov 1
      (str"fix " ++ int i ++ spc() ++  str"{" ++
       v 0
         (prlist_with_sep spc
            (fun (na,i,ty,bd) ->
               pr_annot na ++ str"/" ++ int i ++ str":" ++
               pp_lam ty ++ cut() ++ str":=" ++
               pp_lam bd) (Array.to_list fixl)) ++
       str"}")

  | Lcofix (i,(lna,tl,bl)) ->
    let fixl = Array.mapi (fun i na -> (na,tl.(i),bl.(i))) lna in
    hov 1
      (str"cofix " ++ int i ++ spc() ++  str"{" ++
       v 0
         (prlist_with_sep spc
            (fun (na,ty,bd) ->
               pr_annot na ++ str":" ++ pp_lam ty ++
               cut() ++ str":=" ++ pp_lam bd) (Array.to_list fixl)) ++
       str"}")
  | Lmakeblock(tag, args) ->
    hov 1
      (str "(makeblock " ++ int tag ++ spc() ++
       prlist_with_sep spc pp_lam (Array.to_list args) ++
       str")")
  | Luint i -> str (Uint63.to_string i)
  | Lfloat f -> str (Float64.to_string f)
  | Lval _ -> str "values"
  | Lsort s -> pp_sort s
  | Lind ((mind,i), _) -> MutInd.print mind ++ str"#" ++ int i
  | Lprim ((kn,_u),_op,args) ->
     hov 1
         (str "(PRIM " ++ pr_con kn ++  spc() ++
            prlist_with_sep spc pp_lam  (Array.to_list args) ++
            str")")
  | Lproj(p,arg) ->
    hov 1
      (str "(proj " ++ Projection.Repr.print p ++ str "(" ++ pp_lam arg
       ++ str ")")
  | Lint i ->
    Pp.(str "(int:" ++ int i ++ str ")")

(*s Constructors *)

let mkLapp f args =
  if Array.length args = 0 then f
  else
    match f with
    | Lapp(f', args') -> Lapp (f', Array.append args' args)
    | _ -> Lapp(f, args)

let mkLlam ids body =
  if Array.length ids = 0 then body
  else
    match body with
    | Llam(ids', body) -> Llam(Array.append ids ids', body)
    | _ -> Llam(ids, body)

let decompose_Llam lam =
  match lam with
  | Llam(ids,body) -> ids, body
  | _ -> [||], lam

(*s Operators on substitution *)
let subst_id = subs_id 0
let lift = subs_lift
let liftn = subs_liftn
let cons v subst = subs_cons v subst
let shift subst = subs_shft (1, subst)

(* A generic map function *)

let map_lam_with_binders g f n lam =
  match lam with
  | Lrel _ | Lvar _  | Lconst _ | Lval _ | Lsort _ | Lind _ | Lint _ | Luint _
  | Lfloat _ -> lam
  | Levar (evk, args) ->
    let args' = Array.Smart.map (f n) args in
    if args == args' then lam else Levar (evk, args')
  | Lprod(dom,codom) ->
    let dom' = f n dom in
    let codom' = f n codom in
    if dom == dom' && codom == codom' then lam else Lprod(dom',codom')
  | Llam(ids,body) ->
    let body' = f (g (Array.length ids) n) body in
    if body == body' then lam else mkLlam ids body'
  | Llet(id,def,body) ->
    let def' = f n def in
    let body' = f (g 1 n) body in
    if body == body' && def == def' then lam else Llet(id,def',body')
  | Lapp(fct,args) ->
    let fct' = f n fct in
    let args' = Array.Smart.map (f n) args in
    if fct == fct' && args == args' then lam else mkLapp fct' args'
  | Lcase(ci,rtbl,t,a,branches) ->
    let const = branches.constant_branches in
    let nonconst = branches.nonconstant_branches in
    let t' = f n t in
    let a' = f n a in
    let const' = Array.Smart.map (f n) const in
    let on_b b =
      let (ids,body) = b in
      let body' = f (g (Array.length ids) n) body in
      if body == body' then b else (ids,body') in
    let nonconst' = Array.Smart.map on_b nonconst in
    let branches' =
      if const == const' && nonconst == nonconst' then
        branches
      else
        { constant_branches = const';
          nonconstant_branches = nonconst' }
    in
    if t == t' && a == a' && branches == branches' then lam else
      Lcase(ci,rtbl,t',a',branches')
  | Lfix(init,(ids,ltypes,lbodies)) ->
    let ltypes' = Array.Smart.map (f n) ltypes in
    let lbodies' = Array.Smart.map (f (g (Array.length ids) n)) lbodies in
    if ltypes == ltypes' && lbodies == lbodies' then lam
    else Lfix(init,(ids,ltypes',lbodies'))
  | Lcofix(init,(ids,ltypes,lbodies)) ->
    let ltypes' = Array.Smart.map (f n) ltypes in
    let lbodies' = Array.Smart.map (f (g (Array.length ids) n)) lbodies in
    if ltypes == ltypes' && lbodies == lbodies' then lam
    else Lcofix(init,(ids,ltypes',lbodies'))
  | Lmakeblock(tag,args) ->
    let args' = Array.Smart.map (f n) args in
    if args == args' then lam else Lmakeblock(tag,args')
  | Lprim(kn,op,args) ->
    let args' = Array.Smart.map (f n) args in
    if args == args' then lam else Lprim(kn,op,args')
  | Lproj(p,arg) ->
    let arg' = f n arg in
    if arg == arg' then lam else Lproj(p,arg')

(*s Lift and substitution *)


let rec lam_exlift el lam =
  match lam with
  | Lrel(id,i) ->
    let i' = reloc_rel i el in
    if i == i' then lam else Lrel(id,i')
  | _ -> map_lam_with_binders el_liftn lam_exlift el lam

let lam_lift k lam =
  if k = 0 then lam
  else lam_exlift (el_shft k el_id) lam

let lam_subst_rel lam id n subst =
  match expand_rel n subst with
  | Inl(k,v) -> lam_lift k v
  | Inr(n',_) ->
    if n == n' then lam
    else Lrel(id, n')

let rec lam_exsubst subst lam =
  match lam with
  | Lrel(id,i) -> lam_subst_rel lam id i subst
  | _ -> map_lam_with_binders liftn lam_exsubst subst lam

let lam_subst_args subst args =
  if is_subs_id subst then args
  else Array.Smart.map (lam_exsubst subst) args

(** Simplification of lambda expression *)

(* [simplify subst lam] simplify the expression [lam_subst subst lam] *)
(* that is :                                                          *)
(* - Reduce [let] is the definition can be substituted i.e:           *)
(*    - a variable (rel or identifier)                                *)
(*    - a constant                                                    *)
(*    - a structured constant                                         *)
(*    - a function                                                    *)
(* - Transform beta redex into [let] expression                       *)
(* - Move arguments under [let]                                       *)
(* Invariant : Terms in [subst] are already simplified and can be     *)
(*             substituted                                            *)

let can_subst lam =
  match lam with
  | Lrel _ | Lvar _ | Lconst _ | Luint _
  | Lval _ | Lsort _ | Lind _ -> true
  | _ -> false

let rec simplify subst lam =
  match lam with
  | Lrel(id,i) -> lam_subst_rel lam id i subst

  | Llet(id,def,body) ->
      let def' = simplify subst def in
      if can_subst def' then simplify (cons def' subst) body
      else
        let body' = simplify (lift subst) body in
        if def == def' && body == body' then lam
        else Llet(id,def',body')

  | Lapp(f,args) ->
      begin match simplify_app subst f subst args with
      | Lapp(f',args') when f == f' && args == args' -> lam
      | lam' -> lam'
      end

  | _ -> map_lam_with_binders liftn simplify subst lam

and simplify_app substf f substa args =
  match f with
  | Lrel(id, i) ->
    begin match lam_subst_rel f id i substf with
      | Llam(ids, body) ->
        reduce_lapp
          subst_id (Array.to_list ids) body
          substa (Array.to_list args)
      | f' -> mkLapp f' (simplify_args substa args)
    end
  | Llam(ids, body) ->
    reduce_lapp substf (Array.to_list ids) body substa (Array.to_list args)
  | Llet(id, def, body) ->
    let def' = simplify substf def in
    if can_subst def' then
      simplify_app (cons def' substf) body substa args
    else
      Llet(id, def', simplify_app (lift substf) body (shift substa) args)
  | Lapp(f, args') ->
    let args = Array.append
        (lam_subst_args substf args') (lam_subst_args substa args) in
    simplify_app substf f subst_id args
  | _ -> mkLapp (simplify substf f) (simplify_args substa args)

and simplify_args subst args = Array.Smart.map (simplify subst) args

and reduce_lapp substf lids body substa largs =
  match lids, largs with
  | id::lids, a::largs ->
    let a = simplify substa a in
    if can_subst a then
      reduce_lapp (cons a substf) lids body substa largs
    else
      let body = reduce_lapp (lift substf) lids body (shift substa) largs in
      Llet(id, a, body)
  | [], [] -> simplify substf body
  | _::_, _ ->
    Llam(Array.of_list lids, simplify (liftn (List.length lids) substf) body)
  | [], _ -> simplify_app substf body substa (Array.of_list largs)




(* [occurrence kind k lam]:
   If [kind] is [true] return [true] if the variable [k] does not appear in
   [lam], return [false] if the variable appear one time and not
   under a lambda, a fixpoint, a cofixpoint; else raise Not_found.
   If [kind] is [false] return [false] if the variable does not appear in [lam]
   else raise [Not_found]
*)

let rec occurrence k kind lam =
  match lam with
  | Lrel (_,n) ->
    if n = k then
      if kind then false else raise Not_found
    else kind
  | Lvar _  | Lconst _  | Lval _ | Lsort _ | Lind _ | Lint _ | Luint _
  | Lfloat _ -> kind
  | Levar (_, args) ->
    occurrence_args k kind args
  | Lprod(dom, codom) ->
    occurrence k (occurrence k kind dom) codom
  | Llam(ids,body) ->
    let _ = occurrence (k+Array.length ids) false body in kind
  | Llet(_,def,body) ->
    occurrence (k+1) (occurrence k kind def) body
  | Lapp(f, args) ->
    occurrence_args k (occurrence k kind f) args
  | Lprim(_,_,args) | Lmakeblock(_,args) ->
    occurrence_args k kind args
  | Lcase(_ci,_rtbl,t,a,branches) ->
    let kind = occurrence k (occurrence k kind t) a in
    let r = ref kind in
    Array.iter (fun c -> r := occurrence k kind c  && !r) branches.constant_branches;
    let on_b (ids,c) =
      r := occurrence (k+Array.length ids) kind c && !r
    in
    Array.iter on_b branches.nonconstant_branches;
    !r
  | Lfix(_,(ids,ltypes,lbodies))
  | Lcofix(_,(ids,ltypes,lbodies)) ->
    let kind = occurrence_args k kind ltypes in
    let _ = occurrence_args (k+Array.length ids) false lbodies in
    kind
  | Lproj(_,arg) ->
    occurrence k kind arg

and occurrence_args k kind args =
  Array.fold_left (occurrence k) kind args

let occur_once lam =
  try let _ = occurrence 1 true lam in true
  with Not_found -> false

(* [remove_let lam] remove let expression in [lam] if the variable is *)
(* used at most once time in the body, and does not appear under      *)
(* a lambda or a fix or a cofix                                       *)

let rec remove_let subst lam =
  match lam with
  | Lrel(id,i) -> lam_subst_rel lam id i subst
  | Llet(id,def,body) ->
    let def' = remove_let subst def in
    if occur_once body then remove_let (cons def' subst) body
    else
      let body' = remove_let (lift subst) body in
      if def == def' && body == body' then lam else Llet(id,def',body')
  | _ -> map_lam_with_binders liftn remove_let subst lam


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
let expand_constructor tag nparams arity =
  let anon = Context.make_annot Anonymous Sorts.Relevant in (* TODO relevance *)
  let ids = Array.make (nparams + arity) anon in
  if arity = 0 then mkLlam ids (Lint tag)
  else
    let args = make_args arity 1 in
    Llam(ids, Lmakeblock (tag, args))

let makeblock tag nparams arity args =
  let nargs = Array.length args in
  if nparams > 0 || nargs < arity then
    mkLapp (expand_constructor tag nparams arity) args
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
  else Lmakeblock(tag, args)

let makearray args def =
    let ar = Lmakeblock(0, args) in (* build the ocaml array *)
    let kind = Lmakeblock(0, [|ar; def|]) in (* Parray.Array *)
    Lmakeblock(0,[|kind|]) (* the reference *)

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

let dummy_lambda = Lrel(Anonymous, 0)

let empty_args = [||]

module Renv =
struct

  type constructor_info = tag * int * int (* nparam nrealargs *)

  type t = {
    env : env;
    evar_body : existential -> constr option;
    construct_tbl : (constructor, constructor_info) Hashtbl.t;
  }

  let make env sigma = {
    env = env;
    evar_body = sigma;
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
  | Meta _ -> raise (Invalid_argument "Vmbytegen.lambda_of_constr: Meta")
  | Evar (evk, args as ev) ->
      begin match env.evar_body ev with
      | None ->
          let args = Array.map_of_list (fun c -> lambda_of_constr env c) args in
          Levar (evk, args)
      | Some t -> lambda_of_constr env t
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
    Lcase(ci, rtbl, lt, la, branches)

  | Fix(rec_init,(names,type_bodies,rec_bodies)) ->
    let ltypes = lambda_of_args env 0 type_bodies in
    let nenv = Renv.push_rec_types env (names, type_bodies, rec_bodies) in
    let lbodies = lambda_of_args nenv 0 rec_bodies in
    Lfix(rec_init, (names, ltypes, lbodies))

  | CoFix(init,(names,type_bodies,rec_bodies)) ->
    let ltypes = lambda_of_args env 0 type_bodies in
    let env = Renv.push_rec_types env (names, type_bodies, rec_bodies) in
    let map c ty = Reduction.eta_expand env.env c (Vars.lift (Array.length type_bodies) ty) in
    let rec_bodies = Array.map2 map rec_bodies type_bodies in
    let lbodies = lambda_of_args env 0 rec_bodies in
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
        makeblock tag 0 arity args
      else makeblock tag (nparams - nargs) arity empty_args
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
