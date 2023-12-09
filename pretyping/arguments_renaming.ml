(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Names
open Globnames
open Constr
open Context
open Environ
open Util
open Libobject

(*i*)

let name_table =
  Summary.ref (GlobRef.Map.empty : Name.t list GlobRef.Map.t)
    ~name:"rename-arguments"

type req =
  | ReqLocal
  | ReqGlobal

let load_rename_args _ (_, (r, names)) =
  name_table := GlobRef.Map.add r names !name_table

let cache_rename_args o = load_rename_args 1 o

let classify_rename_args = function
  | ReqLocal, _ -> Dispose
  | ReqGlobal, _ -> Substitute

let subst_rename_args (subst, (_, (r, names as orig))) =
  ReqLocal,
  let r' = fst (subst_global subst r) in
  if r==r' then orig else (r', names)

let discharge_rename_args = function
  | ReqGlobal, (c, names) as req when not (isVarRef c && Lib.is_in_section c) ->
     (try
       let var_names = Array.map_to_list (fun c -> Name (destVar c)) (Lib.section_instance c) in
       let names = var_names @ names in
       Some (ReqGlobal, (c, names))
     with Not_found -> Some req)
  | _ -> None

let rebuild_rename_args x = x

let inRenameArgs = declare_object { (default_object "RENAME-ARGUMENTS" ) with
  load_function = load_rename_args;
  cache_function = cache_rename_args;
  classify_function = classify_rename_args;
  subst_function = subst_rename_args;
  discharge_function = discharge_rename_args;
  rebuild_function = rebuild_rename_args;
}

let rename_arguments local r names =
  let () = match r with
    | GlobRef.VarRef id ->
      CErrors.user_err
        Pp.(str "Arguments of section variables such as "
            ++ Id.print id
            ++ str" may not be renamed.")
    | _ -> ()
  in
  let req = if local then ReqLocal else ReqGlobal in
  Lib.add_leaf (inRenameArgs (req, (r, names)))

let arguments_names r = GlobRef.Map.find r !name_table

let declare_arguments_names r =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let changed = ref false in
  let t, _ = Typeops.type_of_global_in_context env r in
  let rec aux l avoid t = match Reductionops.whd_prod env sigma t with
  | Some (na,t,u) ->
    let na = na.binder_name in
    let rels,_ = Termops.free_rels_and_unqualified_refs sigma t in
    List.iteri (fun i b -> if Int.Set.mem (i+1) rels then b := true) l;
    let isdep = ref false in
    let names = aux (isdep :: l) (Nameops.Name.add na avoid) u in
    let na =
      match na with
      | Anonymous ->
        if !isdep then
          (changed:=true; Name (Namegen.next_canonical_ident (Namegen.hd_ident env sigma t) avoid))
        else
          na
      | Name id ->
          let id' = Namegen.next_canonical_ident id avoid in
          if Id.equal id id' then na else (changed:=true; Name id') in
    na :: names
  | None ->
    let rels,_ = Termops.free_rels_and_unqualified_refs sigma t in
    List.iteri (fun i b -> if Int.Set.mem (i+1) rels then b := true) l;
    []
  in
  let names = aux [] Id.Set.empty (EConstr.of_constr t) in
  if !changed then Lib.add_leaf (inRenameArgs (ReqGlobal, (r, names)))

let rename_type ty ref =
  let name_override old_name override =
    match override with
    | Name _ as x -> {old_name with binder_name=x}
    | Anonymous -> old_name in
  let rec rename_type_aux c = function
    | [] -> c
    | rename :: rest as renamings ->
        match Constr.kind c with
        | Prod (old, s, t) ->
            mkProd (name_override old rename, s, rename_type_aux t rest)
        | LetIn (old, s, b, t) ->
            mkLetIn (old ,s, b, rename_type_aux t renamings)
        | Cast (t,_, _) -> rename_type_aux t renamings
        | _ -> c
  in
  try rename_type_aux ty (arguments_names ref)
  with Not_found -> ty

let rename_typing env c =
  let j = Typeops.infer env c in
  let j' =
    match kind c with
    | Const (c,u) -> { j with uj_type = rename_type j.uj_type (GlobRef.ConstRef c) }
    | Ind (i,u) -> { j with uj_type = rename_type j.uj_type (GlobRef.IndRef i) }
    | Construct (k,u) -> { j with uj_type = rename_type j.uj_type (GlobRef.ConstructRef k) }
    | _ -> j
  in j'

