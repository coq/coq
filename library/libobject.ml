(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Dyn = Dyn.Make ()

type substitutivity = Dispose | Substitute | Keep | Escape | Anticipate

type object_name = Libnames.full_path * Names.KerName.t

type open_filter =
  | Unfiltered
  | Filtered of CString.Pred.t

type category = string

let known_cats = ref CString.Set.empty

let create_category s =
  let cats' = CString.Set.add s !known_cats in
  if !known_cats == cats' then CErrors.anomaly Pp.(str "create_category called twice on " ++ str s);
  known_cats := cats';
  s

let unfiltered = Unfiltered
let make_filter ~finite cats =
  if CList.is_empty cats then CErrors.anomaly Pp.(str "Libobject.make_filter got an empty list.");
  let cats = List.fold_left
      (fun cats CAst.{v=cat;loc} ->
         if not (CString.Set.mem cat !known_cats)
         then CErrors.user_err ?loc Pp.(str "Unknown import category " ++ str cat ++ str".");
         CString.Pred.add cat cats)
      CString.Pred.empty
      cats
  in
  let cats = if finite then cats else CString.Pred.complement cats in
  Filtered cats

let in_filter ~cat f =
  match cat, f with
  | _, Unfiltered -> true
  | None, Filtered f -> not (CString.Pred.is_finite f)
  | Some cat, Filtered f -> CString.Pred.mem cat f

let simple_open ?cat f filter i o = if in_filter ~cat filter then f i o

let filter_eq f1 f2 = match f1, f2 with
  | Unfiltered, Unfiltered -> true
  | Unfiltered, _ | _, Unfiltered -> false
  | Filtered f1, Filtered f2 -> CString.Pred.equal f1 f2

let filter_and f1 f2 = match f1, f2 with
  | Unfiltered, f | f, Unfiltered -> Some f
  | Filtered f1, Filtered f2 ->
    let f = CString.Pred.inter f1 f2 in
    if CString.Pred.is_empty f then None
    else Some (Filtered f)

let filter_or f1 f2 = match f1, f2 with
  | Unfiltered, f | f, Unfiltered -> Unfiltered
  | Filtered f1, Filtered f2 -> Filtered (CString.Pred.union f1 f2)

type ('a,'b,'discharged) object_declaration = {
  object_name : string;
  object_stage : Summary.Stage.t;
  cache_function : 'b -> unit;
  load_function : int -> 'b -> unit;
  open_function : open_filter -> int -> 'b -> unit;
  classify_function : 'a -> substitutivity;
  subst_function :  Mod_subst.substitution * 'a -> 'a;
  discharge_function : 'a -> 'discharged option;
  rebuild_function : 'discharged -> 'a;
}

let default_object ?(stage=Summary.Stage.Interp) s = {
  object_name = s;
  object_stage = stage;
  cache_function = (fun _ -> ());
  load_function = (fun _ _ -> ());
  open_function = (fun _ _ _ -> ());
  subst_function = (fun _ ->
    CErrors.anomaly Pp.(str "The object " ++ str s
      ++ str " does not know how to substitute!"));
  classify_function = (fun _ -> CErrors.anomaly Pp.(str "no classify function for " ++ str s));
  discharge_function = (fun _ -> None);
  rebuild_function = (fun x -> x);
}


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

module ExportObj = struct
  type t = { mpl : (open_filter * Names.ModPath.t) list } [@@unboxed]
end

type algebraic_objects =
  | Objs of t list
  | Ref of Names.ModPath.t * Mod_subst.substitution

and t =
  | ModuleObject of Names.Id.t * substitutive_objects
  | ModuleTypeObject of Names.Id.t * substitutive_objects
  | IncludeObject of algebraic_objects
  | KeepObject of Names.Id.t * t list
  | EscapeObject of Names.Id.t * t list
  | ExportObject of ExportObj.t
  | AtomicObject of obj

and substitutive_objects = Names.MBId.t list * algebraic_objects

type 'a stored_decl = O : ('a, Nametab.object_prefix * 'a, 'd) object_declaration -> 'a stored_decl

module DynMap = Dyn.Map (struct type 'a t = 'a stored_decl end)

let cache_tab = ref DynMap.empty

let declare_object_gen odecl =
  let na = odecl.object_name in
  let tag = Dyn.create na in
  let () = cache_tab := DynMap.add tag (O odecl) !cache_tab in
  tag

let make_oname Nametab.{ obj_dir; obj_mp } id =
  Libnames.make_path obj_dir id, Names.KerName.make obj_mp (Names.Label.of_id id)

let declare_named_object_full odecl =
  let odecl =
    let oname = make_oname in
    { object_name = odecl.object_name;
      object_stage = odecl.object_stage;
      cache_function = (fun (p, (id, o)) -> odecl.cache_function (oname p id, o));
      load_function = (fun i (p, (id, o)) -> odecl.load_function i (oname p id, o));
      open_function = (fun f i (p, (id, o)) -> odecl.open_function f i (oname p id, o));
      classify_function = (fun (id, o) -> odecl.classify_function o);
      subst_function = (fun (subst, (id, o)) -> id, odecl.subst_function (subst, o));
      discharge_function = (fun (id, o) -> Option.map (fun x -> id, x) (odecl.discharge_function o));
      rebuild_function = Util.on_snd odecl.rebuild_function;
    }
  in
  declare_object_gen odecl

let declare_named_object odecl =
  let tag = declare_named_object_full odecl in
  let infun id v = Dyn.Dyn (tag, (id, v)) in
  infun

let declare_named_object_gen odecl =
  let tag = declare_object_gen odecl in
  let infun v = Dyn.Dyn (tag, v) in
  infun

let declare_object_full odecl =
  let odecl =
    { odecl with
      cache_function = (fun (_,o) -> odecl.cache_function o);
      load_function = (fun i (_,o) -> odecl.load_function i o);
      open_function = (fun f i (_,o) -> odecl.open_function f i o);
    }
  in
  declare_object_gen odecl

let declare_object odecl =
  let tag = declare_object_full odecl in
  let infun v = Dyn.Dyn (tag, v) in
  infun

let cache_object (sp, Dyn.Dyn (tag, v)) =
  let O decl = DynMap.find tag !cache_tab in
  decl.cache_function (sp, v)

let load_object i (sp, Dyn.Dyn (tag, v)) =
  let O decl = DynMap.find tag !cache_tab in
  decl.load_function i (sp, v)

let open_object f i (sp, Dyn.Dyn (tag, v)) =
  let O decl = DynMap.find tag !cache_tab in
  decl.open_function f i (sp, v)

let subst_object (subs, Dyn.Dyn (tag, v)) =
  let O decl = DynMap.find tag !cache_tab in
  Dyn.Dyn (tag, decl.subst_function (subs, v))

let classify_object (Dyn.Dyn (tag, v)) =
  let O decl = DynMap.find tag !cache_tab in
  decl.classify_function v

type discharged_obj = Discharged : 'a Dyn.tag * 'd * ('d -> 'a) -> discharged_obj

let discharge_object (Dyn.Dyn (tag, v)) =
  let O decl = DynMap.find tag !cache_tab in
  match decl.discharge_function v with
  | None -> None
  | Some v -> Some (Discharged (tag, v, decl.rebuild_function))

let rebuild_object (Discharged (tag, v, rebuild)) =
  Dyn.Dyn (tag, rebuild v)

let object_stage (Dyn.Dyn (tag, v)) =
  let O decl = DynMap.find tag !cache_tab in
  decl.object_stage

let dump = Dyn.dump

let local_object_nodischarge ?stage s ~cache =
  { (default_object ?stage s) with
    cache_function = cache;
    classify_function = (fun _ -> Dispose);
  }

let local_object ?stage s ~cache ~discharge =
  { (local_object_nodischarge ?stage s ~cache) with
    discharge_function = discharge;
  }

let global_object_nodischarge ?cat ?stage s ~cache ~subst =
  let import i o = if Int.equal i 1 then cache o in
  { (default_object ?stage s) with
    cache_function = cache;
    open_function = simple_open ?cat import;
    subst_function = (match subst with
        | None -> fun _ ->
            CErrors.anomaly Pp.(str "The object " ++ str s
              ++ str " does not know how to substitute!")
        | Some subst -> subst;
      );
    classify_function =
      if Option.has_some subst then (fun _ -> Substitute) else (fun _ -> Keep);
  }

let global_object ?cat ?stage s ~cache ~subst ~discharge =
  { (global_object_nodischarge ?cat s ~cache ~subst) with
    discharge_function = discharge }

let superglobal_object_nodischarge ?stage s ~cache ~subst =
  { (default_object ?stage s) with
    load_function = (fun _ x -> cache x);
    cache_function = cache;
    subst_function = (match subst with
        | None -> fun _ ->
            CErrors.anomaly Pp.(str "The object " ++ str s
              ++ str " does not know how to substitute!")
        | Some subst -> subst;
      );
    classify_function =
      if Option.has_some subst then (fun _ -> Substitute) else (fun _ -> Keep);
  }

let superglobal_object ?stage s ~cache ~subst ~discharge =
  { (superglobal_object_nodischarge ?stage s ~cache ~subst) with
    discharge_function = discharge }

type locality = Local | Export | SuperGlobal

let object_with_locality ?stage ?cat s ~cache ~subst ~discharge =
  { (default_object ?stage s) with
    cache_function = (fun (_,v) -> cache v);
    load_function = (fun _ (locality,v) -> match locality with
        | Local -> assert false
        | Export -> ()
        | SuperGlobal -> cache v);
    open_function = simple_open ?cat (fun i (locality,v) -> match locality with
        | Local -> assert false
        | Export -> begin if Int.equal i 1 then cache v else () end
        | SuperGlobal -> ());
    subst_function = (match subst with
        | None -> fun _ -> assert false (* Keep *)
        | Some subst -> fun (s,(locality,v)) -> locality, subst (s,v);
      );
    classify_function = (fun (locality, _) -> match locality with
        | Local -> Dispose
        | Export | SuperGlobal -> if Option.has_some subst then Substitute else Keep);
    discharge_function =
      (fun (locality,v) -> match locality with
         | Local -> None
         | Export | SuperGlobal ->
           let v = discharge v in
           Some (locality, v));
  }
