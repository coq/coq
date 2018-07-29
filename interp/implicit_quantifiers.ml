(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Names
open Decl_kinds
open CErrors
open Util
open Glob_term
open Constrexpr
open Libnames
open Typeclasses
open Pp
open Libobject
open Nameops
open Context.Rel.Declaration

exception MismatchedContextInstance of Environ.env * Typeclasses_errors.contexts * constr_expr list * Constr.rel_context (* found, expected *)
let mismatched_ctx_inst_err env c n m = raise (MismatchedContextInstance (env, c, n, m))

module RelDecl = Context.Rel.Declaration
(*i*)

let generalizable_table = Summary.ref Id.Pred.empty ~name:"generalizable-ident"

let declare_generalizable_ident table {CAst.loc;v=id} =
  if not (Id.equal id (root_of_id id)) then
    user_err ?loc ~hdr:"declare_generalizable_ident"
    ((Id.print id ++ str
      " is not declarable as generalizable identifier: it must have no trailing digits, quote, or _"));
  if Id.Pred.mem id table then
    user_err ?loc ~hdr:"declare_generalizable_ident"
		((Id.print id++str" is already declared as a generalizable identifier"))
  else Id.Pred.add id table

let add_generalizable gen table =
  match gen with
  | None -> Id.Pred.empty
  | Some [] -> Id.Pred.full
  | Some l -> List.fold_left (fun table lid -> declare_generalizable_ident table lid)
      table l

let cache_generalizable_type (_,(local,cmd)) =
  generalizable_table := add_generalizable cmd !generalizable_table

let load_generalizable_type _ (_,(local,cmd)) =
  generalizable_table := add_generalizable cmd !generalizable_table

let in_generalizable : bool * lident list option -> obj =
  declare_object {(default_object "GENERALIZED-IDENT") with
    load_function = load_generalizable_type;
    cache_function = cache_generalizable_type;
    classify_function = (fun (local, _ as obj) -> if local then Dispose else Keep obj)
  }

let declare_generalizable ~local gen =
 Lib.add_anonymous_leaf (in_generalizable (local, gen))

let find_generalizable_ident id = Id.Pred.mem (root_of_id id) !generalizable_table

let ids_of_list l =
  List.fold_right Id.Set.add l Id.Set.empty

let is_global id =
  try ignore (Nametab.locate_extended (qualid_of_ident id)); true
  with Not_found -> false

let is_named id env =
  try ignore (Environ.lookup_named id env); true
  with Not_found -> false

let is_freevar ids env x =
  not (Id.Set.mem x ids || is_named x env || is_global x)


(* Auxiliary functions for the inference of implicitly quantified variables. *)

let ungeneralizable loc id =
  user_err ?loc ~hdr:"Generalization"
	       (str "Unbound and ungeneralizable variable " ++ Id.print id)

let free_vars_of_constr_expr c ?(bound=Id.Set.empty) l =
  let found loc id bdvars l =
    if Id.List.mem id l then l
    else if is_freevar bdvars (Global.env ()) id
    then
      if find_generalizable_ident id then id :: l
      else ungeneralizable loc id
    else l
  in
  let rec aux bdvars l c = match CAst.(c.v) with
    | CRef (qid,_) when qualid_is_ident qid ->
      found c.CAst.loc (qualid_basename qid) bdvars l
    | CNotation ((InConstrEntrySomeLevel,"{ _ : _ | _ }"), ({ CAst.v = CRef (qid,_) } :: _, [], [], [])) when
        qualid_is_ident qid && not (Id.Set.mem (qualid_basename qid) bdvars) ->
        Constrexpr_ops.fold_constr_expr_with_binders (fun a l -> Id.Set.add a l) aux (Id.Set.add (qualid_basename qid) bdvars) l c
    | _ -> Constrexpr_ops.fold_constr_expr_with_binders (fun a l -> Id.Set.add a l) aux bdvars l c
  in aux bound l c

let ids_of_names l =
  List.fold_left (fun acc x -> match x.CAst.v with Name na -> na :: acc | Anonymous -> acc) [] l

let free_vars_of_binders ?(bound=Id.Set.empty) l (binders : local_binder_expr list) =
  let rec aux bdvars l c = match c with
      ((CLocalAssum (n, _, c)) :: tl) ->
	let bound = ids_of_names n in
	let l' = free_vars_of_constr_expr c ~bound:bdvars l in
	  aux (Id.Set.union (ids_of_list bound) bdvars) l' tl

    | ((CLocalDef (n, c, t)) :: tl) ->
        let bound = match n.CAst.v with Anonymous -> [] | Name n -> [n] in
	let l' = free_vars_of_constr_expr c ~bound:bdvars l in
	let l'' = Option.fold_left (fun l t -> free_vars_of_constr_expr t ~bound:bdvars l) l' t in
	  aux (Id.Set.union (ids_of_list bound) bdvars) l'' tl

    | CLocalPattern _ :: tl -> assert false
    | [] -> bdvars, l
  in aux bound l binders

let generalizable_vars_of_glob_constr ?(bound=Id.Set.empty) ?(allowed=Id.Set.empty) =
  let rec vars bound vs c = match DAst.get c with
    | GVar id ->
        let loc = c.CAst.loc in
	if is_freevar bound (Global.env ()) id then
          if List.exists (fun {CAst.v} -> Id.equal v id) vs then vs
          else CAst.(make ?loc id) :: vs
	else vs
    | _ -> Glob_ops.fold_glob_constr_with_binders Id.Set.add vars bound vs c
  in fun rt -> 
    let vars = List.rev (vars bound [] rt) in
      List.iter (fun {CAst.loc;v=id} ->
	if not (Id.Set.mem id allowed || find_generalizable_ident id) then 
	  ungeneralizable loc id) vars;
      vars

let rec make_fresh ids env x =
  if is_freevar ids env x then x else make_fresh ids env (Nameops.increment_subscript x)

let next_name_away_from na avoid =
  match na with
  | Anonymous -> make_fresh avoid (Global.env ()) (Id.of_string "anon")
  | Name id -> make_fresh avoid (Global.env ()) id

let combine_params avoid fn applied needed =
  let named, applied =
    List.partition
      (function
          (t, Some {CAst.loc;v=ExplByName id}) ->
            let is_id (_, decl) = match RelDecl.get_name decl with
            | Name id' -> Id.equal id id'
            | Anonymous -> false
            in
	    if not (List.exists is_id needed) then
	      user_err ?loc  (str "Wrong argument name: " ++ Id.print id);
	    true
	| _ -> false) applied
  in
  let named = List.map
    (fun x -> match x with (t, Some {CAst.loc;v=ExplByName id}) -> id, t | _ -> assert false)
    named
  in
  let is_unset (_, decl) = match decl with
  | LocalAssum _ -> true
  | LocalDef _ -> false
  in
  let needed = List.filter is_unset needed in
  let rec aux ids avoid app need =
    match app, need with
	[], [] -> List.rev ids, avoid

      | app, (_, (LocalAssum (Name id, _) | LocalDef (Name id, _, _))) :: need when Id.List.mem_assoc id named ->
	  aux (Id.List.assoc id named :: ids) avoid app need

      | (x, None) :: app, (None, (LocalAssum (Name id, _) | LocalDef (Name id, _, _))) :: need ->
	  aux (x :: ids) avoid app need

      | _, (Some cl, _ as d) :: need ->
	  let t', avoid' = fn avoid d in
	    aux (t' :: ids) avoid' app need

      | x :: app, (None, _) :: need -> aux (fst x :: ids) avoid app need

      | [], (None, _ as decl) :: need ->
	  let t', avoid' = fn avoid decl in
	    aux (t' :: ids) avoid' app need

      | (x,_) :: _, [] ->
	  user_err ?loc:(Constrexpr_ops.constr_loc x) (str "Typeclass does not expect more arguments")
  in aux [] avoid applied needed

let combine_params_freevar =
  fun avoid (_, decl) ->
    let id' = next_name_away_from (RelDecl.get_name decl) avoid in
      (CAst.make @@ CRef (qualid_of_ident id',None), Id.Set.add id' avoid)

let destClassApp cl =
  let open CAst in
  let loc = cl.loc in
  match cl.v with
    | CApp ((None, { v = CRef (ref, inst) }), l) -> CAst.make ?loc (ref, List.map fst l, inst)
    | CAppExpl ((None, ref, inst), l) -> CAst.make ?loc (ref, l, inst)
    | CRef (ref, inst) -> CAst.make ?loc:cl.loc (ref, [], inst)
    | _ -> raise Not_found

let destClassAppExpl cl =
  let open CAst in
  let loc = cl.loc in
  match cl.v with
    | CApp ((None, { v = CRef (ref, inst) } ), l) -> CAst.make ?loc (ref, l, inst)
    | CRef (ref, inst) -> CAst.make ?loc:cl.loc (ref, [], inst)
    | _ -> raise Not_found

let implicit_application env ?(allow_partial=true) f ty =
  let is_class =
    try
      let ({CAst.v=(qid, _, _)} as clapp) = destClassAppExpl ty in
      let gr = Nametab.locate qid in
	if Typeclasses.is_class gr then Some (clapp, gr) else None
    with Not_found -> None
  in
    match is_class with
    | None -> ty, env
    | Some ({CAst.loc;v=(id, par, inst)}, gr) ->
	let avoid = Id.Set.union env (ids_of_list (free_vars_of_constr_expr ty ~bound:env [])) in
	let c, avoid =
	  let c = class_info gr in
	  let (ci, rd) = c.cl_context in
	  if not allow_partial then
	    begin
              let opt_succ x n = match x with
              | None -> succ n
              | Some _ -> n
              in
	      let applen = List.fold_left (fun acc (x, y) -> opt_succ y acc) 0 par in
	      let needlen = List.fold_left (fun acc x -> opt_succ x acc) 0 ci in
		if not (Int.equal needlen applen) then
                  mismatched_ctx_inst_err (Global.env ()) Typeclasses_errors.Parameters (List.map fst par) rd
	    end;
	  let pars = List.rev (List.combine ci rd) in
	  let args, avoid = combine_params avoid f par pars in
	    CAst.make ?loc @@ CAppExpl ((None, id, inst), args), avoid
	in c, avoid

let warn_ignoring_implicit_status =
  CWarnings.create ~name:"ignoring_implicit_status" ~category:"implicits"
    (fun na ->
       strbrk "Ignoring implicit status of product binder " ++
       Name.print na ++ strbrk " and following binders")

let implicits_of_glob_constr ?(with_products=true) l =
  let add_impl i na bk l = match bk with
  | Implicit ->
    let name =
      match na with
      | Name id -> Some id
      | Anonymous -> None
    in
    (ExplByPos (i, name), (true, true, true)) :: l
  | _ -> l
  in
  let rec aux i c =
    let abs na bk b =
      add_impl i na bk (aux (succ i) b)
    in
    match DAst.get c with
    | GProd (na, bk, t, b) ->
      if with_products then abs na bk b
      else
        let () = match bk with
          | Implicit -> warn_ignoring_implicit_status na ?loc:c.CAst.loc
          | _ -> ()
        in []
    | GLambda (na, bk, t, b) -> abs na bk b
    | GLetIn (na, b, t, c) -> aux i b
    | GRec (fix_kind, nas, args, tys, bds) ->
      let nb = match fix_kind with |GFix (_, n) -> n | GCoFix n -> n in
      List.fold_left_i (fun i l (na,bk,_,_) -> add_impl i na bk l) i (aux (List.length args.(nb) + i) bds.(nb)) args.(nb)
    | _ -> []
  in aux 1 l
