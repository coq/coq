(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Environ
open Util
open Vernacexpr
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration

let to_string e =
  let rec aux = function
    | SsEmpty -> "()"
    | SsSingl (_,id) -> "("^Id.to_string id^")"
    | SsCompl e -> "-" ^ aux e^""
    | SsUnion(e1,e2) -> "("^aux e1 ^" + "^ aux e2^")"
    | SsSubstr(e1,e2) -> "("^aux e1 ^" - "^ aux e2^")"
    | SsFwdClose e -> "("^aux e^")*"
  in aux e

let known_names = Summary.ref [] ~name:"proofusing-nameset"

let in_nameset =
  let open Libobject in
  declare_object { (default_object "proofusing-nameset") with
    cache_function = (fun (_,x) -> known_names := x :: !known_names);
    classify_function = (fun _ -> Dispose);
    discharge_function = (fun _ -> None)
  }

let rec close_fwd e s =
  let s' =
    List.fold_left (fun s decl ->
      let vb = match decl with
               | LocalAssum _ -> Id.Set.empty
               | LocalDef (_,b,_) -> global_vars_set e b
      in
      let vty = global_vars_set e (NamedDecl.get_type decl) in
      let vbty = Id.Set.union vb vty in
      if Id.Set.exists (fun v -> Id.Set.mem v s) vbty
      then Id.Set.add (NamedDecl.get_id decl) (Id.Set.union s vbty) else s)
    s (named_context e)
    in
  if Id.Set.equal s s' then s else close_fwd e s'
;;

let rec process_expr env e ty =
  let rec aux = function
    | SsEmpty -> Id.Set.empty
    | SsSingl (_,id) -> set_of_id env ty id
    | SsUnion(e1,e2) -> Id.Set.union (aux e1) (aux e2)
    | SsSubstr(e1,e2) -> Id.Set.diff (aux e1) (aux e2)
    | SsCompl e -> Id.Set.diff (full_set env) (aux e)
    | SsFwdClose e -> close_fwd env (aux e)
  in
    aux e

and set_of_id env ty id =
  if Id.to_string id = "Type" then
    List.fold_left (fun acc ty ->
        Id.Set.union (global_vars_set env ty) acc)
      Id.Set.empty ty
  else if Id.to_string id = "All" then
    List.fold_right Id.Set.add (List.map NamedDecl.get_id (named_context env)) Id.Set.empty
  else if CList.mem_assoc_f Id.equal id !known_names then
    process_expr env (CList.assoc_f Id.equal id !known_names) []
  else Id.Set.singleton id

and full_set env =
  List.fold_right Id.Set.add (List.map NamedDecl.get_id (named_context env)) Id.Set.empty

let process_expr env e ty =
  let ty_expr = SsSingl(Loc.ghost, Id.of_string "Type") in
  let v_ty = process_expr env ty_expr ty in
  let s = Id.Set.union v_ty (process_expr env e ty) in
  Id.Set.elements s

let name_set id expr = Lib.add_anonymous_leaf (in_nameset (id,expr))

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

let suggest_Proof_using name env vars ids_typ context_ids =
  let module S = Id.Set in
  let open Pp in
  let print x = prerr_endline (string_of_ppcmds x) in
  let pr_set parens s =
    let wrap ppcmds =
      if parens && S.cardinal s > 1 then str "(" ++ ppcmds ++ str ")"
      else ppcmds in
    wrap (prlist_with_sep (fun _ -> str" ") Id.print (S.elements s)) in
  let used = S.union vars ids_typ in
  let needed = minimize_hyps env (remove_ids_and_lets env used ids_typ) in
  let all_needed = really_needed env needed in
  let all = List.fold_right S.add context_ids S.empty in
  let fwd_typ = close_fwd env ids_typ in
  if !Flags.debug then begin
    print (str "All "        ++ pr_set false all);
    print (str "Type "       ++ pr_set false ids_typ);
    print (str "needed "     ++ pr_set false needed);
    print (str "all_needed " ++ pr_set false all_needed);
    print (str "Type* "      ++ pr_set false fwd_typ);
  end;
  let valid_exprs = ref [] in
  let valid e = valid_exprs := e :: !valid_exprs in
  if S.is_empty needed then valid (str "Type");
  if S.equal all_needed fwd_typ then valid (str "Type*");
  if S.equal all all_needed then valid(str "All");
  valid (pr_set false needed);
  Feedback.msg_info (
    str"The proof of "++ str name ++ spc() ++
    str "should start with one of the following commands:"++spc()++
    v 0 (
    prlist_with_sep cut (fun x->str"Proof using " ++x++ str". ") !valid_exprs));
  string_of_ppcmds (prlist_with_sep (fun _ -> str";")  (fun x->x) !valid_exprs)
;;

let value = ref false

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = true;
      Goptions.optdepr  = false;
      Goptions.optname  = "suggest Proof using";
      Goptions.optkey   = ["Suggest";"Proof";"Using"];
      Goptions.optread  = (fun () -> !value);
      Goptions.optwrite = (fun b ->
        value := b;
        if b then Term_typing.set_suggest_proof_using suggest_Proof_using
        else Term_typing.set_suggest_proof_using (fun _ _ _ _ _ -> "")
      ) }

let value = ref None

let _ =
  Goptions.declare_stringopt_option
    { Goptions.optsync  = true;
      Goptions.optdepr  = false;
      Goptions.optname  = "default value for Proof using";
      Goptions.optkey   = ["Default";"Proof";"Using"];
      Goptions.optread  = (fun () -> !value);
      Goptions.optwrite = (fun b -> value := b;) }


let get_default_proof_using () = !value
