(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Names
open Context
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

module RelDecl = Context.Rel.Declaration
(*i*)

let generalizable_table = Summary.ref Id.Pred.empty ~name:"generalizable-ident"

let declare_generalizable_ident table {CAst.loc;v=id} =
  if not (Id.equal id (root_of_id id)) then
    user_err ?loc
    ((Id.print id ++ str
      " is not declarable as generalizable identifier: it must have no trailing digits, quote, or _."));
  if Id.Pred.mem id table then
    user_err ?loc
                ((Id.print id++str" is already declared as a generalizable identifier."))
  else Id.Pred.add id table

let add_generalizable gen table =
  match gen with
  | None -> Id.Pred.empty
  | Some [] -> Id.Pred.full
  | Some l -> List.fold_left (fun table lid -> declare_generalizable_ident table lid)
      table l

let cache_generalizable_type (local,cmd) =
  generalizable_table := add_generalizable cmd !generalizable_table

let load_generalizable_type _ (local,cmd) =
  generalizable_table := add_generalizable cmd !generalizable_table

let in_generalizable : bool * lident list option -> obj =
  declare_object {(default_object "GENERALIZED-IDENT") with
    load_function = load_generalizable_type;
    cache_function = cache_generalizable_type;
    classify_function = (fun (local, _) -> if local then Dispose else Keep)
  }

let declare_generalizable ~local gen =
 Lib.add_leaf (in_generalizable (local, gen))

let find_generalizable_ident id = Id.Pred.mem (root_of_id id) !generalizable_table

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
  user_err ?loc
               (str "Unbound and ungeneralizable variable " ++ Id.print id ++ str ".")

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
    | CNotation (_,(InConstrEntry,"{ _ : _ | _ }"), ({ CAst.v = CRef (qid,_) } :: _, [], [], [])) when
        qualid_is_ident qid && not (Id.Set.mem (qualid_basename qid) bdvars) ->
        Constrexpr_ops.fold_constr_expr_with_binders (fun a l -> Id.Set.add a l) aux (Id.Set.add (qualid_basename qid) bdvars) l c
    | _ -> Constrexpr_ops.fold_constr_expr_with_binders (fun a l -> Id.Set.add a l) aux bdvars l c
  in aux bound l c

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

let make_fresh ids env x =
  Namegen.next_ident_away_from x (fun x -> not (is_freevar ids env x))

let next_name_away_from na avoid =
  match na with
  | Anonymous -> make_fresh avoid (Global.env ()) (Id.of_string "anon")
  | Name id -> make_fresh avoid (Global.env ()) id

let rec is_class_arg c =
  let open Constr in
  match kind c with
  | Prod (_,_,c)
  | Cast (c,_,_)
  | LetIn (_,_,_,c) -> is_class_arg c
  | _ ->
    let c, _ = decompose_app c in
    match destRef c with
    | exception DestKO -> false
    | r, _ -> is_class r

let combine_params avoid applied needed =
  let named, applied =
    List.partition
      (function
          (t, Some {CAst.loc;v=ExplByName id}) ->
            let is_id decl = Name.equal (Name id) (RelDecl.get_name decl) in
            if not (List.exists is_id needed) then
              user_err ?loc  (str "Wrong argument name: " ++ Id.print id);
            true
        | _ -> false) applied
  in
  let named = List.map
    (fun x -> match x with (t, Some {CAst.loc;v=ExplByName id}) -> id, t | _ -> assert false)
    named
  in
  let rec aux ids avoid app need =
    match need with
    | [] -> begin match app with
        | [] -> List.rev ids, avoid
        | (x, _) :: _ -> user_err ?loc:(Constrexpr_ops.constr_loc x) (str "Typeclass does not expect more arguments")
      end

    | LocalDef _ :: need -> aux ids avoid app need


    | LocalAssum ({binder_name=Name id}, _) :: need when Id.List.mem_assoc id named ->
      aux (Id.List.assoc id named :: ids) avoid app need

    | decl :: need ->
      begin match app, is_class_arg (get_type decl) with
        | (x, _) :: app, false -> aux (x :: ids) avoid app need

        | [], false | _, true ->
          let id' = next_name_away_from (RelDecl.get_name decl) avoid in
          let t' = CAst.make @@ CRef (qualid_of_ident id',None) in
          aux (t' :: ids) (Id.Set.add id' avoid) app need
      end
  in
  aux [] avoid applied needed

let destClassAppExpl cl =
  let open CAst in
  let loc = cl.loc in
  match cl.v with
    | CApp ({ v = CRef (ref, inst) }, l) -> CAst.make ?loc (ref, l, inst)
    | CRef (ref, inst) -> CAst.make ?loc:cl.loc (ref, [], inst)
    | _ -> raise Not_found

let implicit_application env ty =
  let is_class =
    try
      let ({CAst.v=(qid, _, _)} as clapp) = destClassAppExpl ty in
      if Libnames.idset_mem_qualid qid env then None
      else
        let gr = Nametab.locate qid in
        Option.map (fun cl -> cl, clapp) (Typeclasses.class_info gr)
    with Not_found -> None
  in
  match is_class with
  | None -> ty, env
  | Some (c, {CAst.loc;v=(id, par, inst)}) ->
    let avoid = Id.Set.union env (Id.Set.of_list (free_vars_of_constr_expr ty ~bound:env [])) in
    let args, avoid = combine_params avoid par (List.rev c.cl_context) in
    CAst.make ?loc @@ CAppExpl ((id, inst), args), avoid

let warn_ignoring_implicit_status =
  CWarnings.create ~name:"ignoring-implicit-status" ~category:CWarnings.CoreCategories.implicits
    (fun na ->
       strbrk "Ignoring implicit status of product binder " ++
       Name.print na ++ strbrk " and following binders")

let implicits_of_glob_constr ?(with_products=true) l =
  let add_impl ?loc na bk l = match bk with
  | NonMaxImplicit -> CAst.make ?loc (Some (na,false)) :: l
  | MaxImplicit -> CAst.make ?loc (Some (na,true)) :: l
  | Explicit -> CAst.make ?loc None :: l
  in
  let rec aux c =
    match DAst.get c with
    | GProd (na, _, bk, t, b) ->
      if with_products then add_impl na bk (aux b)
      else
        let () = match bk with
          | NonMaxImplicit
          | MaxImplicit -> warn_ignoring_implicit_status na ?loc:c.CAst.loc
          | Explicit -> ()
        in []
    | GLambda (na, _, bk, t, b) -> add_impl ?loc:t.CAst.loc na bk (aux b)
    | GLetIn (na, _, b, t, c) -> aux c
    | GRec (fix_kind, nas, args, tys, bds) ->
      let nb = match fix_kind with |GFix (_, n) -> n | GCoFix n -> n in
      List.fold_right (fun (na,_,bk,t,_) l ->
          match t with
          | Some _ -> l
          | _ -> add_impl ?loc:c.CAst.loc na bk l)
        args.(nb) (aux bds.(nb))
    | _ -> []
  in aux l
