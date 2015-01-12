(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Environ
open Util
open Vernacexpr

let to_string = function
  | SsAll -> "All"
  | SsType -> "Type"
  | SsExpr(SsSet l)-> String.concat " " (List.map Id.to_string (List.map snd l))
  | SsExpr e ->
      let rec aux = function
        | SsSet [] -> "( )"
        | SsSet [_,x] -> Id.to_string x
        | SsSet l ->
          "(" ^ String.concat " " (List.map Id.to_string (List.map snd l)) ^ ")"
        | SsCompl e -> "-" ^ aux e^""
        | SsUnion(e1,e2) -> "("^aux e1 ^" + "^ aux e2^")"
        | SsSubstr(e1,e2) -> "("^aux e1 ^" - "^ aux e2^")"
      in aux e

let known_names = Summary.ref [] ~name:"proofusing-nameset"

let in_nameset =
  let open Libobject in
  declare_object { (default_object "proofusing-nameset") with
    cache_function = (fun (_,x) -> known_names := x :: !known_names);
    classify_function = (fun _ -> Dispose);
    discharge_function = (fun _ -> None)
  }

let rec process_expr env e ty =
  match e with
  | SsAll ->
      List.fold_right Id.Set.add (List.map pi1 (named_context env)) Id.Set.empty
  | SsExpr e ->
      let rec aux = function
        | SsSet l -> set_of_list env (List.map snd l)
        | SsUnion(e1,e2) -> Id.Set.union (aux e1) (aux e2)
        | SsSubstr(e1,e2) -> Id.Set.diff (aux e1) (aux e2)
        | SsCompl e -> Id.Set.diff (full_set env) (aux e)
      in
        aux e
  | SsType ->
      List.fold_left (fun acc ty ->
        Id.Set.union (global_vars_set env ty) acc)
      Id.Set.empty ty
and set_of_list env = function
  | [x] when CList.mem_assoc_f Id.equal x !known_names ->
      process_expr env (CList.assoc_f Id.equal x !known_names) []
  | l -> List.fold_right Id.Set.add l Id.Set.empty
and full_set env = set_of_list env (List.map pi1 (named_context env))

let process_expr env e ty =
  let s = Id.Set.union (process_expr env SsType ty) (process_expr env e []) in
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

let minimize_unused_hyps env ids =
  let all_ids = List.map pi1 (named_context env) in
  let deps_of =
    let cache =
      List.map (fun id -> id,really_needed env (Id.Set.singleton id)) all_ids in
    fun id -> List.assoc id cache in
  let inv_dep_of =
    let cache_sum cache id stuff =
      try Id.Map.add id (Id.Set.add stuff (Id.Map.find id cache)) cache
      with Not_found -> Id.Map.add id (Id.Set.singleton stuff) cache in
    let cache =
      List.fold_left (fun cache id ->
        Id.Set.fold (fun d cache -> cache_sum cache d id)
          (Id.Set.remove id (deps_of id)) cache)
        Id.Map.empty all_ids in
    fun id -> try Id.Map.find id cache with Not_found -> Id.Set.empty in
  let rec aux s =
    let s' =
      Id.Set.fold (fun id s ->
        if Id.Set.subset (inv_dep_of id) s then Id.Set.diff s (inv_dep_of id)
        else s)
      s s in
    if Id.Set.equal s s' then s else aux s' in
  aux ids

let suggest_Proof_using kn env vars ids_typ context_ids =
  let module S = Id.Set in
  let open Pp in
  let used = S.union vars ids_typ in
  let needed = minimize_hyps env used in
  let all_needed = really_needed env needed in
  let all = List.fold_right S.add context_ids S.empty in
  let unneeded = minimize_unused_hyps env (S.diff all needed) in
  let pr_set s =
    let wrap ppcmds =
      if S.cardinal s > 1 || S.equal s (S.singleton (Id.of_string "All"))
      then str "(" ++ ppcmds ++ str ")"
      else ppcmds in
    wrap (prlist_with_sep (fun _ -> str" ") Id.print (S.elements s)) in
  if !Flags.debug then begin
    prerr_endline (string_of_ppcmds (str "All " ++ pr_set all));
    prerr_endline (string_of_ppcmds (str "Type" ++ pr_set ids_typ));
    prerr_endline (string_of_ppcmds (str "needed " ++ pr_set needed));
    prerr_endline (string_of_ppcmds (str "unneeded " ++ pr_set unneeded));
  end;
  msg_info (
    str"The proof of "++
    Names.Constant.print kn ++ spc() ++ str "should start with:"++spc()++
    str"Proof using " ++
    if S.is_empty needed then str "."
    else if S.subset needed ids_typ then str "Type."
    else if S.equal all all_needed then str "All."
    else 
      let s1 = string_of_ppcmds (str "-" ++ pr_set unneeded ++ str".") in
      let s2 = string_of_ppcmds (pr_set needed ++ str".") in
      if String.length s1 < String.length s2 then str s1 else str s2)

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
        else Term_typing.set_suggest_proof_using (fun _ _ _ _ _ -> ())
      ) }

let value = ref "_unset_"

let _ =
  Goptions.declare_string_option
    { Goptions.optsync  = true;
      Goptions.optdepr  = false;
      Goptions.optname  = "default value for Proof using";
      Goptions.optkey   = ["Default";"Proof";"Using"];
      Goptions.optread  = (fun () -> !value);
      Goptions.optwrite = (fun b -> value := b;) }


let get_default_proof_using () =
  if !value = "_unset_" then None
  else Some !value
