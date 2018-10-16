open Util
open Names
open Esubst
open Term
open Constr
open Declarations
open Vmvalues
open Cbytecodes
open Cinstr
open Environ
open Pp

let pr_con sp = str(Names.Label.to_string (Constant.label sp))

(** Printing **)

let pp_names ids =
  prlist_with_sep (fun _ -> brk(1,1)) Name.print (Array.to_list ids)

let pp_rel name n =
  Name.print name ++  str "##" ++ int n

let pp_sort s =
  match Sorts.family s with
  | InSet -> str "Set"
  | InProp -> str "Prop"
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
                            Name.print id ++
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
               Name.print na ++ str"/" ++ int i ++ str":" ++
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
               Name.print na ++ str":" ++ pp_lam ty ++
               cut() ++ str":=" ++ pp_lam bd) (Array.to_list fixl)) ++
       str"}")
  | Lmakeblock(tag, args) ->
    hov 1
      (str "(makeblock " ++ int tag ++ spc() ++
       prlist_with_sep spc pp_lam (Array.to_list args) ++
       str")")
  | Lval _ -> str "values"
  | Lsort s -> pp_sort s
  | Lind ((mind,i), _) -> MutInd.print mind ++ str"#" ++ int i
  | Lprim((kn,_u),ar,op,args) ->
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
  | Luint _ ->
    str "(uint)"

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
let cons v subst = subs_cons([|v|], subst)
let shift subst = subs_shft (1, subst)

(* A generic map function *)

let rec map_lam_with_binders g f n lam =
  match lam with
  | Lrel _ | Lvar _  | Lconst _ | Lval _ | Lsort _ | Lind _ | Lint _ -> lam
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
  | Lprim(kn,ar,op,args) ->
    let args' = Array.Smart.map (f n) args in
    if args == args' then lam else Lprim(kn,ar,op,args')
  | Lproj(p,arg) ->
    let arg' = f n arg in
    if arg == arg' then lam else Lproj(p,arg')
  | Luint u ->
    let u' = map_uint g f n u in
    if u == u' then lam else Luint u'

and map_uint g f n u =
  match u with
  | UintVal _ -> u
  | UintDigits(args) ->
    let args' = Array.Smart.map (f n) args in
    if args == args' then u else UintDigits(args')
  | UintDecomp(a) ->
    let a' = f n a in
    if a == a' then u else UintDecomp(a')

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
  | Lrel _ | Lvar _ | Lconst _
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
    Llam(Array.of_list lids,  simplify (liftn (List.length lids) substf) body)
  | [], _::_ -> simplify_app substf body substa (Array.of_list largs)




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
  | Lvar _  | Lconst _  | Lval _ | Lsort _ | Lind _ | Lint _ -> kind
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
  | Lprim(_,_,_,args) | Lmakeblock(_,args) ->
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
  | Luint u -> occurrence_uint k kind u

and occurrence_args k kind args =
  Array.fold_left (occurrence k) kind args

and occurrence_uint k kind u =
  match u with
  | UintVal _ -> kind
  | UintDigits args -> occurrence_args k kind args
  | UintDecomp t -> occurrence k kind t

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
  | Lval _ | Lint _ -> true
  | _ -> false

let get_value lc =
  match lc with
  | Lval v -> v
  | Lint i -> val_of_int i
  | _ -> raise Not_found

let make_args start _end =
  Array.init (start - _end + 1) (fun i -> Lrel (Anonymous, start - i))

(* Translation of constructors *)
let expand_constructor tag nparams arity =
  let ids = Array.make (nparams + arity) Anonymous in
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


(* Compiling constants *)

let rec get_alias env kn =
  let cb = lookup_constant kn env in
  let tps = cb.const_body_code in
  match tps with
  | None -> kn
  | Some tps ->
    (match Cemitcodes.force tps with
     | Cemitcodes.BCalias kn' -> get_alias env kn'
     | _ -> kn)

(* Compilation of primitive *)

let _h =  Name(Id.of_string "f")

(*
let expand_prim kn op arity =
  let ids = Array.make arity Anonymous in
  let args = make_args arity 1 in
  Llam(ids, prim kn op args)
*)

let compile_prim n op kn fc args =
  if not fc then raise Not_found
  else
    Lprim(kn, n, op, args)

    (*
  let (nparams, arity) = CPrimitives.arity op in
  let expected = nparams + arity in
  if Array.length args >= expected then prim kn op args
  else mkLapp (expand_prim kn op expected) args
*)

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

  let extend v =
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

  let popn v n =
    v.size <- max 0 (v.size - n)

  let pop v = popn v 1

  let get_last v n =
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
    name_rel : Name.t Vect.t;
    construct_tbl : (constructor, constructor_info) Hashtbl.t;
  }

  let make env = {
    global_env = env;
    name_rel = Vect.make 16 Anonymous;
    construct_tbl = Hashtbl.create 111
  }

  let push_rel env id = Vect.push env.name_rel id

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
  | Meta _ -> raise (Invalid_argument "Cbytegen.lambda_of_constr: Meta")
  | Evar (evk, args) ->
    let args = lambda_of_args env 0 args in
    Levar (evk, args)

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
    Lprod(ld,  Llam([|id|], lc))

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

  | Case(ci,t,a,branches) ->
    let ind = ci.ci_ind in
    let mib = lookup_mind (fst ind) env.global_env in
    let oib = mib.mind_packets.(snd ind) in
    let () = check_compilable oib in
    let rtbl = oib.mind_reloc_tbl in


    (* translation of the argument *)
    let la = lambda_of_constr env a in
    let entry = mkInd ind in
    let la =
      try
        Retroknowledge.get_vm_before_match_info env.global_env.retroknowledge
          entry la
      with Not_found -> la
    in
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
            let ids = Array.make arity Anonymous in
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
    Renv.push_rels env names;
    let lbodies = lambda_of_args env 0 rec_bodies in
    Renv.popn env (Array.length names);
    Lfix(rec_init, (names, ltypes, lbodies))

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

and lambda_of_app env f args =
  match Constr.kind f with
  | Const (kn,u as c) ->
    let kn = get_alias env.global_env kn in
    (* spiwack: checks if there is a specific way to compile the constant
                if there is not, Not_found is raised, and the function
                falls back on its normal behavior *)
    (try
      (* We delay the compilation of arguments to avoid an exponential behavior *)
      let f = Retroknowledge.get_vm_compiling_info env.global_env.retroknowledge
          (mkConstU (kn,u)) in
      let args = lambda_of_args env 0 args in
      f args
    with Not_found ->
    let cb = lookup_constant kn env.global_env in
    begin match cb.const_body with
      | Def csubst when cb.const_inline_code ->
        lambda_of_app env (Mod_subst.force_constr csubst) args
      | Def _ | OpaqueDef _ | Undef _ -> mkLapp (Lconst c) (lambda_of_args env 0 args)
    end)
  | Construct (c,_) ->
    let tag, nparams, arity = Renv.get_construct_info env c in
    let nargs = Array.length args in
    if Int.equal (nparams + arity) nargs then (* fully applied *)
      (* spiwack: *)
      (* 1/ tries to compile the constructor in an optimal way,
            it is supposed to work only if the arguments are
            all fully constructed, fails with Cbytecodes.NotClosed.
            it can also raise Not_found when there is no special
            treatment for this constructor
            for instance: tries to to compile an integer of the
                form I31 D1 D2 ... D31 to [D1D2...D31] as
                a processor number (a caml number actually) *)
      try
        try
          Retroknowledge.get_vm_constant_static_info
            env.global_env.retroknowledge
            f args
        with NotClosed ->
          (* 2/ if the arguments are not all closed (this is
                              expectingly (and it is currently the case) the only
                              reason why this exception is raised) tries to
                              give a clever, run-time behavior to the constructor.
                              Raises Not_found if there is no special treatment
                              for this integer.
                              this is done in a lazy fashion, using the constructor
                              Bspecial because it needs to know the continuation
                              and such, which can't be done at this time.
                              for instance, for int31: if one of the digit is
                                  not closed, it's not impossible that the number
                                  gets fully instantiated at run-time, thus to ensure
                                  uniqueness of the representation in the vm
                                  it is necessary to try and build a caml integer
                                  during the execution *)
          let rargs = Array.sub args nparams arity in
          let args = lambda_of_args env nparams rargs in
          Retroknowledge.get_vm_constant_dynamic_info
            env.global_env.retroknowledge
            f args
      with Not_found ->
        (* 3/ if no special behavior is available, then the compiler
           falls back to the normal behavior *)
        let args = lambda_of_args env nparams args in
        makeblock tag 0 arity args
    else
      let args = lambda_of_args env nparams args in
      (* spiwack: tries first to apply the run-time compilation
                behavior of the constructor, as in 2/ above *)
      (try
         (Retroknowledge.get_vm_constant_dynamic_info
            env.global_env.retroknowledge
            f) args
       with Not_found ->
         if nparams <= nargs then (* got all parameters *)
           makeblock tag 0 arity args
         else (* still expecting some parameters *)
           makeblock tag (nparams - nargs) arity empty_args)
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

let lambda_of_constr ~optimize genv c =
  let env = Renv.make genv in
  let ids = List.rev_map Context.Rel.Declaration.get_name (rel_context genv) in
  Renv.push_rels env (Array.of_list ids);
  let lam = lambda_of_constr env c in
  let lam = if optimize then optimize_lambda lam else lam in
  if !dump_lambda then
    Feedback.msg_debug (pp_lam lam);
  lam

(** Retroknowledge, to be removed once we move to primitive machine integers *)
let compile_structured_int31 fc args =
  if not fc then raise Not_found else
    Luint (UintVal
    (Uint31.of_int (Array.fold_left
       (fun temp_i -> fun t -> match kind t with
          | Construct ((_,d),_) -> 2*temp_i+d-1
          | _ -> raise NotClosed)
       0 args)))

let dynamic_int31_compilation fc args =
  if not fc then raise Not_found else
  Luint (UintDigits args)

let d0 = Lint 0
let d1 = Lint 1

(* We are relying here on the tags of digits constructors *)
let digits_from_uint i =
  let digits = Array.make 31 d0 in
  for k = 0 to 30 do
    if Int.equal ((Uint31.to_int i lsr k) land 1) 1 then
      digits.(30-k) <- d1
  done;
  digits

let int31_escape_before_match fc t =
  if not fc then
    raise Not_found
  else
  match t with
  | Luint (UintVal i) ->
    let digits = digits_from_uint i in
    Lmakeblock (1, digits)
  | Luint (UintDigits args) ->
    Lmakeblock (1,args)
  | Luint (UintDecomp _) ->
    assert false
  | _ -> Luint (UintDecomp t)
