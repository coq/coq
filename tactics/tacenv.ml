(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Genarg
open Pp
open Names
open Tacexpr

(** Tactic notations (TacAlias) *)

type alias = KerName.t

let alias_map = Summary.ref ~name:"tactic-alias"
  (KNmap.empty : glob_tactic_expr KNmap.t)

let register_alias key tac =
  alias_map := KNmap.add key tac !alias_map

let interp_alias key =
  try KNmap.find key !alias_map
  with Not_found -> Errors.anomaly (str "Unknown tactic alias: " ++ KerName.print key)

(** ML tactic extensions (TacML) *)

type ml_tactic =
  typed_generic_argument list -> Geninterp.interp_sign -> unit Proofview.tactic

module MLName =
struct
  type t = ml_tactic_name
  let compare tac1 tac2 =
    let c = String.compare tac1.mltac_tactic tac2.mltac_tactic in
    if c = 0 then String.compare tac1.mltac_plugin tac2.mltac_plugin
    else c
end

module MLTacMap = Map.Make(MLName)

let pr_tacname t =
  t.mltac_plugin ^ "::" ^ t.mltac_tactic

let tac_tab = ref MLTacMap.empty

let register_ml_tactic ?(overwrite = false) s (t : ml_tactic) =
  let () =
    if MLTacMap.mem s !tac_tab then
      if overwrite then
        let () = tac_tab := MLTacMap.remove s !tac_tab in
        msg_warning (str ("Overwriting definition of tactic " ^ pr_tacname s))
      else
        Errors.anomaly (str ("Cannot redeclare tactic " ^ pr_tacname s ^ "."))
  in
  tac_tab := MLTacMap.add s t !tac_tab

let interp_ml_tactic s =
  try
    MLTacMap.find s !tac_tab
  with Not_found ->
    Errors.errorlabstrm ""
      (str "The tactic " ++ str (pr_tacname s) ++ str " is not installed.")

let () =
  let assert_installed opn = let _ = interp_ml_tactic opn in () in
  Hook.set Tacintern.assert_tactic_installed_hook assert_installed

(***************************************************************************)
(* Tactic registration *)

(* Summary and Object declaration *)

open Nametab
open Libnames
open Libobject

let mactab =
  Summary.ref (KNmap.empty : glob_tactic_expr KNmap.t)
    ~name:"tactic-definition"

let interp_ltac r = KNmap.find r !mactab

(* Declaration of the TAC-DEFINITION object *)
let add (kn,td) = mactab := KNmap.add kn td !mactab
let replace (kn,td) = mactab := KNmap.add kn td !mactab

type tacdef_kind =
  | NewTac of Id.t
  | UpdateTac of Nametab.ltac_constant

let load_md i ((sp,kn),(local,defs)) =
  let dp,_ = repr_path sp in
  let mp,dir,_ = repr_kn kn in
  let (id, t) = defs in
    match id with
      | NewTac id ->
          let sp = make_path dp id in
          let kn = Names.make_kn mp dir (Label.of_id id) in
            Nametab.push_tactic (Until i) sp kn;
            add (kn,t)
      | UpdateTac kn -> replace (kn,t)

let open_md i ((sp,kn),(local,defs)) =
  let dp,_ = repr_path sp in
  let mp,dir,_ = repr_kn kn in
  let (id, t) = defs in
    match id with
        NewTac id ->
          let sp = make_path dp id in
          let kn = Names.make_kn mp dir (Label.of_id id) in
            Nametab.push_tactic (Exactly i) sp kn
      | UpdateTac kn -> ()

let cache_md x = load_md 1 x

let subst_kind subst id =
  match id with
    | NewTac _ -> id
    | UpdateTac kn -> UpdateTac (Mod_subst.subst_kn subst kn)

let subst_md (subst,(local,defs)) =
  (local,
   let (id, t) = defs in
     (subst_kind subst id,Tacsubst.subst_tactic subst t))

let classify_md (local,defs as o) =
  if local then Dispose else Substitute o

let inMD : bool * (tacdef_kind * glob_tactic_expr) -> obj =
  declare_object {(default_object "TAC-DEFINITION") with
     cache_function  = cache_md;
     load_function   = load_md;
     open_function   = open_md;
     subst_function = subst_md;
     classify_function = classify_md}

let register_ltac local id tac =
  ignore (Lib.add_leaf id (inMD (local, (NewTac id, tac))))

let redefine_ltac local kn tac =
  Lib.add_anonymous_leaf (inMD (local, (UpdateTac kn, tac)))

let () =
  Hook.set Tacintern.interp_ltac_hook interp_ltac
