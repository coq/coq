(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Esubst
open Names
open Constr

type reloc_table = (int * int) array

type case_annot = case_info * reloc_table * Declarations.recursivity_kind

type 'v lambda =
| Lrel          of Name.t * int
| Lvar          of Id.t
| Lmeta         of metavariable * 'v lambda (* type *)
| Levar         of Evar.t * 'v lambda array (* arguments *)
| Lprod         of 'v lambda * 'v lambda
| Llam          of Name.t Context.binder_annot array * 'v lambda
| Llet          of Name.t Context.binder_annot * 'v lambda * 'v lambda
| Lapp          of 'v lambda * 'v lambda array
| Lconst        of pconstant
| Lproj         of Projection.Repr.t * 'v lambda
| Lprim         of pconstant * CPrimitives.t * 'v lambda array
| Lcase         of case_annot * 'v lambda * 'v lambda * 'v lam_branches
  (* annotations, term being matched, accu, branches *)
| Lfix          of (int array * inductive array * int) * 'v fix_decl
| Lcofix        of int * 'v fix_decl
| Lint          of int
| Lparray       of 'v lambda array * 'v lambda
| Lmakeblock    of inductive * int * 'v lambda array
  (* inductive name, constructor tag, arguments *)
| Luint         of Uint63.t
| Lfloat        of Float64.t
| Lval          of 'v
| Lsort         of Sorts.t
| Lind          of pinductive
| Lforce

and 'v lam_branches =
  { constant_branches : 'v lambda array;
    nonconstant_branches : (Name.t Context.binder_annot array * 'v lambda) array }

and 'v fix_decl = Name.t Context.binder_annot array * 'v lambda array * 'v lambda array

type evars =
    { evars_val : constr evar_handler;
      evars_metas : metavariable -> types }

let empty_evars =
  { evars_val = default_evar_handler;
    evars_metas = (fun _ -> assert false) }

(** Printing **)

let pr_annot x = Name.print x.Context.binder_name

let pp_names ids =
  prlist_with_sep (fun _ -> brk(1,1)) pr_annot (Array.to_list ids)

let pp_rel name n =
  Name.print name ++  str "##" ++ int n

let pp_sort s =
  match Sorts.family s with
  | Sorts.InSet -> str "Set"
  | Sorts.InProp -> str "Prop"
  | Sorts.InSProp -> str "SProp"
  | Sorts.InType -> str "Type"

let pr_con sp = str(Names.Label.to_string (Constant.label sp))

let rec pp_lam lam =
  match lam with
  | Lrel (id,n) -> pp_rel id n
  | Lvar id -> Id.print id
  | Lmeta (mv, ty) ->
    hov 1 (str "meta(" ++ int mv ++ str ":" ++ spc () ++ pp_lam ty ++ str ")")
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
  | Lcase(_annot, t, a, branches) ->
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
  | Lfix ((t, _, i), (lna, tl, bl)) ->
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
  | Lparray (args, def) ->
    hov 1
      (str "(array " ++ spc() ++
       prlist_with_sep spc pp_lam (Array.to_list args) ++
       spc () ++ str "|" ++ spc () ++ pp_lam def ++ str")")
  | Lmakeblock(_, tag, args) ->
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
  | Lforce -> Pp.str "force"

(*s Constructors *)

let mkLapp f args =
  if Array.is_empty args then f
  else
    match f with
    | Lapp(f', args') -> Lapp (f', Array.append args' args)
    | _ -> Lapp(f, args)

let mkLlam ids body =
  if Array.is_empty ids then body
  else
    match body with
    | Llam(ids', body) -> Llam(Array.append ids ids', body)
    | _ -> Llam(ids, body)

let decompose_Llam lam =
  match lam with
  | Llam(ids,body) -> ids, body
  | _ -> [||], lam

let rec decompose_Llam_Llet lam =
  match lam with
  | Llam(ids,body) ->
      let vars, body = decompose_Llam_Llet body in
      Array.fold_right (fun x l -> (x, None) :: l) ids vars, body
  | Llet(id,def,body) ->
      let vars, body = decompose_Llam_Llet body in
      (id,Some def) :: vars, body
  | _ -> [], lam

let decompose_Llam_Llet lam =
  let vars, body = decompose_Llam_Llet lam in
  Array.of_list vars, body

(* A generic map function *)

let map_lam_with_binders g f n lam =
  match lam with
  | Lrel _ | Lvar _  | Lconst _ | Lval _ | Lsort _ | Lind _ | Lint _ | Luint _
  | Lfloat _ -> lam
  | Lmeta (mv, ty) ->
    let ty' = f n ty in
    if ty == ty' then lam else Lmeta (mv, ty')
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
  | Lcase (annot, t, a, branches) ->
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
      Lcase(annot, t', a', branches')
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
  | Lparray (args, def) ->
    let args' = Array.Smart.map (f n) args in
    let def' = f n def in
    if args == args' && def == def' then lam else Lparray (args', def')
  | Lmakeblock (inds, tag, args) ->
    let args' = Array.Smart.map (f n) args in
    if args == args' then lam else Lmakeblock (inds, tag,args')
  | Lprim(kn,op,args) ->
    let args' = Array.Smart.map (f n) args in
    if args == args' then lam else Lprim(kn,op,args')
  | Lproj(p,arg) ->
    let arg' = f n arg in
    if arg == arg' then lam else Lproj(p,arg')
  | Lforce -> Lforce

(*s Operators on substitution *)
let lift = subs_lift
let liftn = subs_liftn
let cons v subst = subs_cons v subst
let shift subst = subs_shft (1, subst)

(*s Lift and substitution *)

let rec lam_exlift el lam =
  match lam with
  | Lrel(id,i) ->
    let i' = reloc_rel i el in
    if i == i' then lam else Lrel(id,i')
  | _ -> map_lam_with_binders el_liftn lam_exlift el lam

let lam_lift k lam =
  if Int.equal k 0 then lam
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

(* [simplify can_subst subst lam] simplifies the expression [lam_subst subst lam] by: *)
(* - Reducing [let] is the definition can be substituted *)
(* - Transforming beta redex into [let] expression *)
(* - Moving arguments under [let] *)
(* Invariant: Terms in [subst] are already simplified and can be substituted *)

let simplify can_subst subst lam =
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
            (subs_id 0) (Array.to_list ids) body
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
      simplify_app substf f (subs_id 0) args
    | _ -> mkLapp (simplify substf f) (simplify_args substa args)

  and simplify_args subst args = Array.Smart.map (fun c -> simplify subst c) args

  and reduce_lapp substf lids body substa largs =
    match lids, largs with
    | id::lids, a::largs ->
      let a = simplify substa a in
      if can_subst a then
        reduce_lapp (subs_cons a substf) lids body substa largs
      else
        let body = reduce_lapp (lift substf) lids body (shift substa) largs in
        Llet(id, a, body)
    | [], [] -> simplify substf body
    | _::_, _ ->
      Llam(Array.of_list lids, simplify (liftn (List.length lids) substf) body)
    | [], _ -> simplify_app substf body substa (Array.of_list largs)
  in
  simplify subst lam
