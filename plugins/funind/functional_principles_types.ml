(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Printer
open CErrors
open Term
open Util
open Constr
open Context
open Vars
open Names
open Pp
open Induction
open Context.Rel.Declaration
open Indfun_common
module RelDecl = Context.Rel.Declaration

exception Toberemoved_with_rel of int * constr
exception Toberemoved

let observe s = if do_observe () then Feedback.msg_debug s
let pop t = Vars.lift (-1) t

(*
   Transform an inductive induction principle into
   a functional one
*)
let compute_new_princ_type_from_rel env rel_to_fun sorts princ_type =
  let princ_type = EConstr.of_constr princ_type in
  let princ_type_info = compute_elim_sig Evd.empty princ_type (* FIXME *) in
  let env_with_params = EConstr.push_rel_context princ_type_info.params env in
  let tbl = Hashtbl.create 792 in
  let rec change_predicates_names (avoid : Id.t list)
      (predicates : EConstr.rel_context) : EConstr.rel_context =
    match predicates with
    | [] -> []
    | decl :: predicates -> (
      match Context.Rel.Declaration.get_name decl with
      | Name x ->
        let id = Namegen.next_ident_away x (Id.Set.of_list avoid) in
        Hashtbl.add tbl id x;
        RelDecl.set_name (Name id) decl
        :: change_predicates_names (id :: avoid) predicates
      | Anonymous -> anomaly (Pp.str "Anonymous property binder.") )
  in
  let avoid = Termops.ids_of_context env_with_params in
  let princ_type_info =
    { princ_type_info with
      predicates = change_predicates_names avoid princ_type_info.predicates }
  in
  (*   observe (str "starting princ_type := " ++ pr_lconstr_env env princ_type); *)
  (*   observe (str "princ_infos : " ++ pr_elim_scheme princ_type_info); *)
  let change_predicate_sort i decl =
    let new_sort = sorts.(i) in
    let args, _ =
      decompose_prod_decls (EConstr.Unsafe.to_constr (RelDecl.get_type decl))
    in
    let real_args =
      if princ_type_info.indarg_in_concl then List.tl args else args
    in
    let na = map_annot Nameops.Name.get_id (Context.Rel.Declaration.get_annot decl) in
    let na = EConstr.Unsafe.to_binder_annot na in
    Context.Named.Declaration.LocalAssum (na, Term.it_mkProd_or_LetIn (mkSort new_sort) real_args)
  in
  let new_predicates =
    List.map_i change_predicate_sort 0 princ_type_info.predicates
  in
  let env_with_params_and_predicates =
    List.fold_right Environ.push_named new_predicates env_with_params
  in
  let rel_as_kn =
    fst
      ( match princ_type_info.indref with
      | Some (GlobRef.IndRef ind) -> ind
      | _ -> user_err Pp.(str "Not a valid predicate") )
  in
  let ptes_vars = List.map Context.Named.Declaration.get_id new_predicates in
  let is_pte =
    let set = List.fold_right Id.Set.add ptes_vars Id.Set.empty in
    fun t -> match Constr.kind t with Var id -> Id.Set.mem id set | _ -> false
  in
  let pre_princ =
    let open EConstr in
    it_mkProd_or_LetIn
      (it_mkProd_or_LetIn
         (Option.fold_right mkProd_or_LetIn princ_type_info.indarg
            princ_type_info.concl)
         princ_type_info.args)
      princ_type_info.branches
  in
  let pre_princ = EConstr.Unsafe.to_constr pre_princ in
  let pre_princ = substl (List.map mkVar ptes_vars) pre_princ in
  let is_dom c =
    match Constr.kind c with
    | Ind ((u, _), _) -> Environ.QMutInd.equal env u rel_as_kn
    | Construct (((u, _), _), _) -> Environ.QMutInd.equal env u rel_as_kn
    | _ -> false
  in
  let get_fun_num c =
    match Constr.kind c with
    | Ind ((_, num), _) -> num
    | Construct (((_, num), _), _) -> num
    | _ -> assert false
  in
  let dummy_var = mkVar (Id.of_string "________") in
  let mk_replacement c i args =
    let res = mkApp (rel_to_fun.(i), Array.map pop (array_get_start args)) in
    observe
      ( str "replacing "
      ++ pr_lconstr_env env Evd.empty c
      ++ str " by "
      ++ pr_lconstr_env env Evd.empty res );
    res
  in
  let rec compute_new_princ_type remove env pre_princ : types * constr list =
    let ((new_princ_type, _) as res) =
      match Constr.kind pre_princ with
      | Rel n -> (
        try
          match Environ.lookup_rel n env with
          | (LocalAssum (_, t) | LocalDef (_, _, t)) when is_dom t ->
            raise Toberemoved
          | _ -> (pre_princ, [])
        with Not_found -> assert false )
      | Prod (x, t, b) ->
        compute_new_princ_type_for_binder remove mkProd env x t b
      | Lambda (x, t, b) ->
        compute_new_princ_type_for_binder remove mkLambda env x t b
      | (Ind _ | Construct _) when is_dom pre_princ -> raise Toberemoved
      | App (f, args) when is_dom f ->
        let var_to_be_removed = destRel (Array.last args) in
        let num = get_fun_num f in
        raise
          (Toberemoved_with_rel
             (var_to_be_removed, mk_replacement pre_princ num args))
      | App (f, args) ->
        let args = if is_pte f && remove then array_get_start args else args in
        let new_args, binders_to_remove =
          Array.fold_right
            (compute_new_princ_type_with_acc remove env)
            args ([], [])
        in
        let new_f, binders_to_remove_from_f =
          compute_new_princ_type remove env f
        in
        ( applistc new_f new_args
        , list_union_eq Constr.equal binders_to_remove_from_f binders_to_remove
        )
      | LetIn (x, v, t, b) ->
        compute_new_princ_type_for_letin remove env x v t b
      | _ -> (pre_princ, [])
    in
    (*     let _ = match Constr.kind pre_princ with *)
    (*      | Prod _ -> *)
    (*          observe(str "compute_new_princ_type for "++ *)
    (*            pr_lconstr_env env pre_princ ++ *)
    (*            str" is "++ *)
    (*            pr_lconstr_env env new_princ_type ++ fnl ()) *)
    (*      | _ -> () in *)
    res
  and compute_new_princ_type_for_binder remove bind_fun env x t b =
    try
      let new_t, binders_to_remove_from_t =
        compute_new_princ_type remove env t
      in
      let new_x = map_annot (get_name (Termops.ids_of_context env)) x in
      let new_env = Environ.push_rel (LocalAssum (x, t)) env in
      let new_b, binders_to_remove_from_b =
        compute_new_princ_type remove new_env b
      in
      if List.exists (Constr.equal (mkRel 1)) binders_to_remove_from_b then
        ( pop new_b
        , filter_map (Constr.equal (mkRel 1)) pop binders_to_remove_from_b )
      else
        ( bind_fun (new_x, new_t, new_b)
        , list_union_eq Constr.equal binders_to_remove_from_t
            (List.map pop binders_to_remove_from_b) )
    with
    | Toberemoved ->
      (*          observe (str "Decl of "++Ppconstr.Name.print x ++ str " is removed "); *)
      let new_b, binders_to_remove_from_b =
        compute_new_princ_type remove env (substnl [dummy_var] 1 b)
      in
      (new_b, List.map pop binders_to_remove_from_b)
    | Toberemoved_with_rel (n, c) ->
      (*          observe (str "Decl of "++Ppconstr.Name.print x ++ str " is removed "); *)
      let new_b, binders_to_remove_from_b =
        compute_new_princ_type remove env (substnl [c] n b)
      in
      ( new_b
      , list_add_set_eq Constr.equal (mkRel n)
          (List.map pop binders_to_remove_from_b) )
  and compute_new_princ_type_for_letin remove env x v t b =
    try
      let new_t, binders_to_remove_from_t =
        compute_new_princ_type remove env t
      in
      let new_v, binders_to_remove_from_v =
        compute_new_princ_type remove env v
      in
      let new_x = map_annot (get_name (Termops.ids_of_context env)) x in
      let new_env = Environ.push_rel (LocalDef (x, v, t)) env in
      let new_b, binders_to_remove_from_b =
        compute_new_princ_type remove new_env b
      in
      if List.exists (Constr.equal (mkRel 1)) binders_to_remove_from_b then
        ( pop new_b
        , filter_map (Constr.equal (mkRel 1)) pop binders_to_remove_from_b )
      else
        ( mkLetIn (new_x, new_v, new_t, new_b)
        , list_union_eq Constr.equal
            (list_union_eq Constr.equal binders_to_remove_from_t
               binders_to_remove_from_v)
            (List.map pop binders_to_remove_from_b) )
    with
    | Toberemoved ->
      (*          observe (str "Decl of "++Ppconstr.Name.print x ++ str " is removed "); *)
      let new_b, binders_to_remove_from_b =
        compute_new_princ_type remove env (substnl [dummy_var] 1 b)
      in
      (new_b, List.map pop binders_to_remove_from_b)
    | Toberemoved_with_rel (n, c) ->
      (*          observe (str "Decl of "++Ppconstr.Name.print x ++ str " is removed "); *)
      let new_b, binders_to_remove_from_b =
        compute_new_princ_type remove env (substnl [c] n b)
      in
      ( new_b
      , list_add_set_eq Constr.equal (mkRel n)
          (List.map pop binders_to_remove_from_b) )
  and compute_new_princ_type_with_acc remove env e (c_acc, to_remove_acc) =
    let new_e, to_remove_from_e = compute_new_princ_type remove env e in
    (new_e :: c_acc, list_union_eq Constr.equal to_remove_from_e to_remove_acc)
  in
  (*   observe (str "Computing new principe from " ++ pr_lconstr_env  env_with_params_and_predicates pre_princ); *)
  let pre_res, _ =
    compute_new_princ_type princ_type_info.indarg_in_concl
      env_with_params_and_predicates pre_princ
  in
  let pre_res =
    replace_vars
      (List.map_i (fun i id -> (id, mkRel i)) 1 ptes_vars)
      (lift (List.length ptes_vars) pre_res)
  in
  it_mkProd_or_LetIn
    (it_mkProd_or_LetIn pre_res
       (List.map
          (function
            | Context.Named.Declaration.LocalAssum (id, b) ->
              LocalAssum
                (map_annot (fun id -> Name.mk_name (Hashtbl.find tbl id)) id, b)
            | Context.Named.Declaration.LocalDef (id, t, b) ->
              LocalDef
                ( map_annot (fun id -> Name.mk_name (Hashtbl.find tbl id)) id
                , t
                , b ))
          new_predicates))
    (EConstr.Unsafe.to_rel_context princ_type_info.params)
