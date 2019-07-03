(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Names

module Dyn = Dyn.Make ()

type 'a substitutivity =
    Dispose | Substitute of 'a | Keep of 'a

type object_name = Libnames.full_path * Names.KerName.t

type 'a object_declaration = {
  object_name : string;
  cache_function : object_name * 'a -> unit;
  load_function : int -> object_name * 'a -> unit;
  open_function : int -> object_name * 'a -> unit;
  classify_function : 'a -> 'a substitutivity;
  subst_function : Mod_subst.substitution * 'a -> 'a;
  discharge_function : object_name * 'a -> 'a option;
  rebuild_function : 'a -> 'a }

let default_object s = {
  object_name = s;
  cache_function = (fun _ -> ());
  load_function = (fun _ _ -> ());
  open_function = (fun _ _ -> ());
  subst_function = (fun _ ->
    CErrors.anomaly (str "The object " ++ str s ++ str " does not know how to substitute!"));
  classify_function = (fun atomic_obj -> Keep atomic_obj);
  discharge_function = (fun _ -> None);
  rebuild_function = (fun x -> x)}


(* The suggested object declaration is the following:

   declare_object { (default_object "MY OBJECT") with
       cache_function = fun (sp,a) -> Mytbl.add sp a}

   and the listed functions are only those which definitions actually
   differ from the default.

   This helps introducing new functions in objects.
*)

let ident_subst_function (_,a) = a


type obj = Dyn.t (* persistent dynamic objects *)

(** {6 Substitutive objects}

    - The list of bound identifiers is nonempty only if the objects
      are owned by a functor

    - Then comes either the object segment itself (for interactive
      modules), or a compact way to store derived objects (path to
      a earlier module + substitution).
*)

type algebraic_objects =
  | Objs of objects
  | Ref of Names.ModPath.t * Mod_subst.substitution

and t =
  | ModuleObject of substitutive_objects
  | ModuleTypeObject of substitutive_objects
  | IncludeObject of algebraic_objects
  | KeepObject of objects
  | ImportObject of { export : bool; mp : ModPath.t }
  | AtomicObject of obj

and objects = (Names.Id.t * t) list

and substitutive_objects = MBId.t list * algebraic_objects

type dynamic_object_declaration = {
  dyn_cache_function : object_name * obj -> unit;
  dyn_load_function : int -> object_name * obj -> unit;
  dyn_open_function : int -> object_name * obj -> unit;
  dyn_subst_function : Mod_subst.substitution * obj -> obj;
  dyn_classify_function : obj -> obj substitutivity;
  dyn_discharge_function : object_name * obj -> obj option;
  dyn_rebuild_function : obj -> obj }

let object_tag (Dyn.Dyn (t, _)) = Dyn.repr t

let cache_tab =
  (Hashtbl.create 223 : (string,dynamic_object_declaration) Hashtbl.t)

let declare_object_full odecl =
  let na = odecl.object_name in
  let (infun, outfun) = Dyn.Easy.make_dyn na in
  let cacher (oname,lobj) = odecl.cache_function (oname,outfun lobj)
  and loader i (oname,lobj) = odecl.load_function i (oname,outfun lobj)
  and opener i (oname,lobj) = odecl.open_function i (oname,outfun lobj)
  and substituter (sub,lobj) = infun (odecl.subst_function (sub,outfun lobj))
  and classifier lobj = match odecl.classify_function (outfun lobj) with
  | Dispose -> Dispose
  | Substitute atomic_obj -> Substitute (infun atomic_obj)
  | Keep atomic_obj -> Keep (infun atomic_obj)
  and discharge (oname,lobj) =
    Option.map infun (odecl.discharge_function (oname,outfun lobj))
  and rebuild lobj = infun (odecl.rebuild_function (outfun lobj))
  in
  Hashtbl.add cache_tab na { dyn_cache_function = cacher;
			     dyn_load_function = loader;
                             dyn_open_function = opener;
			     dyn_subst_function = substituter;
			     dyn_classify_function = classifier;
			     dyn_discharge_function = discharge;
			     dyn_rebuild_function = rebuild };
  (infun,outfun)

let declare_object odecl = fst (declare_object_full odecl)
let declare_object_full odecl = declare_object_full odecl

(* this function describes how the cache, load, open, and export functions
   are triggered. *)

let apply_dyn_fun f lobj =
  let tag = object_tag lobj in
  let dodecl =
    try Hashtbl.find cache_tab tag
    with Not_found -> assert false
  in
  f dodecl

let cache_object ((_,lobj) as node) =
  apply_dyn_fun (fun d -> d.dyn_cache_function node) lobj

let load_object i ((_,lobj) as node) =
  apply_dyn_fun (fun d -> d.dyn_load_function i node) lobj

let open_object i ((_,lobj) as node) =
  apply_dyn_fun (fun d -> d.dyn_open_function i node) lobj

let subst_object ((_,lobj) as node) = 
  apply_dyn_fun (fun d -> d.dyn_subst_function node) lobj

let classify_object lobj =
  apply_dyn_fun (fun d -> d.dyn_classify_function lobj) lobj

let discharge_object ((_,lobj) as node) =
  apply_dyn_fun (fun d -> d.dyn_discharge_function node) lobj

let rebuild_object lobj =
  apply_dyn_fun (fun d -> d.dyn_rebuild_function lobj) lobj

let dump = Dyn.dump

let local_object_nodischarge s ~cache =
  { (default_object s) with
    cache_function = cache;
    classify_function = (fun _ -> Dispose);
  }

let local_object s ~cache ~discharge =
  { (local_object_nodischarge s ~cache) with
    discharge_function = discharge }

let global_object_nodischarge s ~cache ~subst =
  let import i o = if Int.equal i 1 then cache o in
  { (default_object s) with
    cache_function = cache;
    open_function = import;
    subst_function = (match subst with
        | None -> fun _ -> CErrors.anomaly (str "The object " ++ str s ++ str " does not know how to substitute!")
        | Some subst -> subst;
      );
    classify_function =
      if Option.has_some subst then (fun o -> Substitute o) else (fun o -> Keep o);
  }

let global_object s ~cache ~subst ~discharge =
  { (global_object_nodischarge s ~cache ~subst) with
    discharge_function = discharge }

let superglobal_object_nodischarge s ~cache ~subst =
  { (default_object s) with
    load_function = (fun _ x -> cache x);
    cache_function = cache;
    subst_function = (match subst with
        | None -> fun _ -> CErrors.anomaly (str "The object " ++ str s ++ str " does not know how to substitute!")
        | Some subst -> subst;
      );
    classify_function =
      if Option.has_some subst then (fun o -> Substitute o) else (fun o -> Keep o);
  }

let superglobal_object s ~cache ~subst ~discharge =
  { (superglobal_object_nodischarge s ~cache ~subst) with
    discharge_function = discharge }
