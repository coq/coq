(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Names

module Dyn = Dyn.Make ()

type 'a substitutivity =
    Dispose | Substitute of 'a | Keep of 'a | Anticipate of 'a

type object_name = Libnames.full_path * Names.KerName.t

module NSet = Globnames.ExtRefSet

type open_filter =
  | Unfiltered
  | Names of NSet.t

let simple_open f filter i o = match filter with
  | Unfiltered -> f i o
  | Names _ -> ()

let filter_and f1 f2 = match f1, f2 with
  | Unfiltered, f | f, Unfiltered -> Some f
  | Names n1, Names n2 ->
    let n = NSet.inter n1 n2 in
    if NSet.is_empty n then None
    else Some (Names n)

let filter_or f1 f2 = match f1, f2 with
  | Unfiltered, f | f, Unfiltered -> Unfiltered
  | Names n1, Names n2 -> Names (NSet.union n1 n2)

let in_filter_ref gr = function
  | Unfiltered -> true
  | Names ns -> NSet.mem (Globnames.TrueGlobal gr) ns

type 'a object_declaration = {
  object_name : string;
  cache_function : object_name * 'a -> unit;
  load_function : int -> object_name * 'a -> unit;
  open_function : open_filter -> int -> object_name * 'a -> unit;
  classify_function : 'a -> 'a substitutivity;
  subst_function : Mod_subst.substitution * 'a -> 'a;
  discharge_function : object_name * 'a -> 'a option;
  rebuild_function : 'a -> 'a }

let default_object s = {
  object_name = s;
  cache_function = (fun _ -> ());
  load_function = (fun _ _ -> ());
  open_function = (fun _ _ _ -> ());
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
  | ExportObject of { mpl : (open_filter * ModPath.t) list }
  | AtomicObject of obj

and objects = (Names.Id.t * t) list

and substitutive_objects = MBId.t list * algebraic_objects

module DynMap = Dyn.Map (struct type 'a t = 'a object_declaration end)

let cache_tab = ref DynMap.empty

let declare_object_full odecl =
  let na = odecl.object_name in
  let tag = Dyn.create na in
  let () = cache_tab := DynMap.add tag odecl !cache_tab in
  tag

let declare_object odecl =
  let tag = declare_object_full odecl in
  let infun v = Dyn.Dyn (tag, v) in
  infun

let cache_object (sp, Dyn.Dyn (tag, v)) =
  let decl = DynMap.find tag !cache_tab in
  decl.cache_function (sp, v)

let load_object i (sp, Dyn.Dyn (tag, v)) =
  let decl = DynMap.find tag !cache_tab in
  decl.load_function i (sp, v)

let open_object f i (sp, Dyn.Dyn (tag, v)) =
  let decl = DynMap.find tag !cache_tab in
  decl.open_function f i (sp, v)

let subst_object (subs, Dyn.Dyn (tag, v)) =
  let decl = DynMap.find tag !cache_tab in
  Dyn.Dyn (tag, decl.subst_function (subs, v))

let classify_object (Dyn.Dyn (tag, v)) =
  let decl = DynMap.find tag !cache_tab in
  match decl.classify_function v with
  | Dispose -> Dispose
  | Substitute v -> Substitute (Dyn.Dyn (tag, v))
  | Keep v -> Keep (Dyn.Dyn (tag, v))
  | Anticipate v -> Anticipate (Dyn.Dyn (tag, v))

let discharge_object (sp, Dyn.Dyn (tag, v)) =
  let decl = DynMap.find tag !cache_tab in
  match decl.discharge_function (sp, v) with
  | None -> None
  | Some v -> Some (Dyn.Dyn (tag, v))

let rebuild_object (Dyn.Dyn (tag, v)) =
  let decl = DynMap.find tag !cache_tab in
  Dyn.Dyn (tag, decl.rebuild_function v)

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
    open_function = simple_open import;
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
