(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Environ
open Util
open Vernacexpr
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration

let all_collection_id = Id.of_string "All"
let known_names = Summary.ref [] ~name:"proofusing-nameset"

let is_known_name id = CList.mem_assoc_f Id.equal id !known_names

let rec close_fwd env sigma s =
  let s' =
    List.fold_left (fun s decl ->
      let vb = match decl with
               | LocalAssum _ -> Id.Set.empty
               | LocalDef (_,b,_) -> Termops.global_vars_set env sigma b
      in
      let vty = Termops.global_vars_set env sigma (NamedDecl.get_type decl) in
      let vbty = Id.Set.union vb vty in
      if Id.Set.exists (fun v -> Id.Set.mem v s) vbty
      then Id.Set.add (NamedDecl.get_id decl) (Id.Set.union s vbty) else s)
    s (EConstr.named_context env)
    in
  if Id.Set.equal s s' then s else close_fwd env sigma s'

let set_of_type env sigma ty =
  List.fold_left (fun acc ty ->
      Id.Set.union (Termops.global_vars_set env sigma ty) acc)
    Id.Set.empty ty

let full_set env =
  List.fold_right Id.Set.add (List.map NamedDecl.get_id (named_context env)) Id.Set.empty

let warn_all_collection_precedence = CWarnings.create ~name:"all-collection-precedence" ~category:"deprecated"
    Pp.(fun () -> str "Variable " ++ Id.print all_collection_id ++ str " is shadowed by Collection named " ++ Id.print all_collection_id ++ str " containing all variables.")

let warn_collection_precedence = CWarnings.create ~name:"collection-precedence" ~category:"deprecated"
    Pp.(fun id -> Id.print id ++ str " is both name of a Collection and Variable, Collection " ++ Id.print id ++ str " takes precedence over Variable.")

let warn_redefine_collection = CWarnings.create ~name:"collection-redefinition" ~category:"deprecated"
    Pp.(fun id -> str "New Collection definition of " ++ Id.print id ++ str " shadows the previous one.")

let warn_variable_shadowing = CWarnings.create ~name:"variable-shadowing" ~category:"deprecated"
    Pp.(fun id -> Id.print id ++ str " was already a defined Variable, the name " ++ Id.print id ++ str " will refer to Collection when executing \"Proof using\" command.")

let err_redefine_all_collection () =
  CErrors.user_err Pp.(str "\"" ++ Id.print all_collection_id ++ str "\" is a predefined collection containing all variables. It can't be redefined.")

let process_expr env sigma e v_ty =
  let variable_exists id =
    try ignore (lookup_named id env); true with | Not_found -> false in
  let rec aux = function
    | SsEmpty -> Id.Set.empty
    | SsType -> v_ty
    | SsSingl { CAst.v = id } -> set_of_id id
    | SsUnion(e1,e2) -> Id.Set.union (aux e1) (aux e2)
    | SsSubstr(e1,e2) -> Id.Set.diff (aux e1) (aux e2)
    | SsCompl e -> Id.Set.diff (full_set env) (aux e)
    | SsFwdClose e -> close_fwd env sigma (aux e)
  and set_of_id id =
    if Id.equal id all_collection_id then
      begin
        if variable_exists all_collection_id then
          warn_all_collection_precedence ();
        full_set env
      end
    else if is_known_name id then
      begin
        if variable_exists id then
          warn_collection_precedence id;
        aux (CList.assoc_f Id.equal id !known_names)
      end
    else Id.Set.singleton id
  in
  aux e

let process_expr env sigma e ty =
  let v_ty = set_of_type env sigma ty in
  let s = Id.Set.union v_ty (process_expr env sigma e v_ty) in
  Id.Set.elements s

type t = Names.Id.Set.t

let definition_using env evd ~using ~terms =
  let l = process_expr env evd using terms in
  Names.Id.Set.(List.fold_right add l empty)

let name_set id expr =
  if Id.equal id all_collection_id then err_redefine_all_collection ();
  if is_known_name id then warn_redefine_collection id;
  if Termops.is_section_variable (Global.env ()) id then warn_variable_shadowing id;
  known_names := (id,expr) :: !known_names

let minimize_hyps env ids =
  let rec aux ids =
    let ids' =
      Id.Set.fold (fun id alive ->
        let impl_by_id =
          Id.Set.remove id (really_needed env (Id.Set.singleton id)) in
        if Id.Set.is_empty impl_by_id then alive
        else Id.Set.diff alive impl_by_id)
      ids ids in
    if Id.Set.equal ids ids' then ids else aux ids'
  in
    aux ids

let remove_ids_and_lets env s ids =
  let not_ids id = not (Id.Set.mem id ids) in
  let no_body id = named_body id env = None in
  let deps id = really_needed env (Id.Set.singleton id) in
    (Id.Set.filter (fun id ->
      not_ids id &&
     (no_body id ||
       Id.Set.exists not_ids (Id.Set.filter no_body (deps id)))) s)

let record_proof_using expr =
  Aux_file.record_in_aux "suggest_proof_using" expr

let debug_proof_using = CDebug.create ~name:"proof-using" ()

(* Variables in [skip] come from after the definition, so don't count
   for "All". Used in the variable case since the env contains the
   variable itself. *)
let suggest_common env ppid used ids_typ skip =
  let module S = Id.Set in
  let open Pp in
  let pr_set parens s =
    let wrap ppcmds =
      if parens && S.cardinal s > 1 then str "(" ++ ppcmds ++ str ")"
      else ppcmds in
    wrap (prlist_with_sep (fun _ -> str" ") Id.print (S.elements s)) in

  let needed = minimize_hyps env (remove_ids_and_lets env used ids_typ) in
  let all_needed = really_needed env needed in
  let all = List.fold_left (fun all d -> S.add (NamedDecl.get_id d) all)
      S.empty (named_context env)
  in
  let all = S.diff all skip in
  let fwd_typ = close_fwd env (Evd.from_env env) ids_typ in
  let () = debug_proof_using (fun () ->
      str "All "        ++ pr_set false all ++ fnl() ++
      str "Type "       ++ pr_set false ids_typ ++ fnl() ++
      str "needed "     ++ pr_set false needed ++ fnl() ++
      str "all_needed " ++ pr_set false all_needed ++ fnl() ++
      str "Type* "      ++ pr_set false fwd_typ)
  in
  let valid_exprs = ref [] in
  let valid e = valid_exprs := e :: !valid_exprs in
  if S.is_empty needed then valid (str "Type");
  if S.equal all_needed fwd_typ then valid (str "Type*");
  if S.equal all all_needed then valid(str "All");
  valid (pr_set false needed);
  Feedback.msg_info (
    str"The proof of "++ ppid ++ spc() ++
    str "should start with one of the following commands:"++spc()++
    v 0 (
    prlist_with_sep cut (fun x->str"Proof using " ++x++ str". ") !valid_exprs));
  if Aux_file.recording ()
  then
    let s = string_of_ppcmds (prlist_with_sep (fun _ -> str";")  (fun x->x) !valid_exprs) in
    record_proof_using s

let suggest_proof_using = ref false

let () =
  Goptions.(declare_bool_option
    { optdepr  = false;
      optkey   = ["Suggest";"Proof";"Using"];
      optread  = (fun () -> !suggest_proof_using);
      optwrite = ((:=) suggest_proof_using) })

let suggest_constant env kn =
  if !suggest_proof_using
  then begin
    let open Declarations in
    let body = lookup_constant kn env in
    let used = Id.Set.of_list @@ List.map NamedDecl.get_id body.const_hyps in
    let ids_typ = global_vars_set env body.const_type in
    suggest_common env (Printer.pr_constant env kn) used ids_typ Id.Set.empty
  end

let suggest_variable env id =
  if !suggest_proof_using
  then begin
    match lookup_named id env with
    | LocalDef (_,body,typ) ->
      let ids_typ = global_vars_set env typ in
      let ids_body = global_vars_set env body in
      let used = Id.Set.union ids_body ids_typ in
      suggest_common env (Id.print id) used ids_typ (Id.Set.singleton id)
    | LocalAssum _ -> assert false
  end

let value = ref None

let using_to_string us = Pp.string_of_ppcmds (Ppvernac.pr_using us)
let entry = Pcoq.eoi_entry G_vernac.section_subset_expr
let using_from_string us = Pcoq.Entry.parse entry
    (Pcoq.Parsable.make (Stream.of_string ("( "^us^" )")))

let proof_using_opt_name = ["Default";"Proof";"Using"]
let () =
  Goptions.(declare_stringopt_option
    { optdepr  = false;
      optkey   = proof_using_opt_name;
      optread  = (fun () -> Option.map using_to_string !value);
      optwrite = (fun b -> value := Option.map using_from_string b);
    })

let get_default_proof_using () = !value
