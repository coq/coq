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
open CErrors
open Util
open Names
open Declarations
open Entries
open Libnames
open Libobject
open Mod_subst

(** {6 Inlining levels} *)

(** Rigid / flexible module signature *)

type 'a module_signature =
  | Enforce of 'a (** ... : T *)
  | Check of 'a list (** ... <: T1 <: T2, possibly empty *)

(** Which module inline annotations should we honor,
    either None or the ones whose level is less or equal
    to the given integer *)

type inline =
  | NoInline
  | DefaultInline
  | InlineAt of int

let default_inline () = Some (Flags.get_inline_level ())

let inl2intopt = function
  | NoInline -> None
  | InlineAt i -> Some i
  | DefaultInline -> default_inline ()

(** ModSubstObjs : a cache of module substitutive objects

   This table is common to modules and module types.
   -  For a Module M:=N, the objects of N will be reloaded
      with M after substitution.
   -  For a Module M:SIG:=..., the module M gets its objects from SIG

   Invariants:
   - A alias (i.e. a module path inside a Ref constructor) should
     never lead to another alias, but rather to a concrete Objs
     constructor.

   We will plug later a handler dealing with missing entries in the
   cache. Such missing entries may come from inner parts of module
   types, which aren't registered by the standard libobject machinery.
*)

module ModSubstObjs :
 sig
   val set : ModPath.t -> substitutive_objects -> unit
   val get : ModPath.t -> substitutive_objects
   val set_missing_handler : (ModPath.t -> substitutive_objects) -> unit
 end =
 struct
   let table =
     Summary.ref (MPmap.empty : substitutive_objects MPmap.t)
       ~name:"MODULE-SUBSTOBJS"
   let missing_handler = ref (fun mp -> assert false)
   let set_missing_handler f = (missing_handler := f)
   let set mp objs = (table := MPmap.add mp objs !table)
   let get mp =
     try MPmap.find mp !table with Not_found -> !missing_handler mp
 end

(** Some utilities about substitutive objects :
    substitution, expansion *)

let sobjs_no_functor (mbids,_) = List.is_empty mbids

let subst_filtered sub (f,mp) =
  let f = match f with
    | Unfiltered -> Unfiltered
  in
  f, subst_mp sub mp

let rec subst_aobjs sub = function
  | Objs o as objs ->
    let o' = subst_objects sub o in
    if o == o' then objs else Objs o'
  | Ref (mp, sub0) as r ->
    let sub0' = join sub0 sub in
    if sub0' == sub0 then r else Ref (mp, sub0')

and subst_sobjs sub (mbids,aobjs as sobjs) =
  let aobjs' = subst_aobjs sub aobjs in
  if aobjs' == aobjs then sobjs else (mbids, aobjs')

and subst_objects subst seg =
  let subst_one (id,obj as node) =
    match obj with
    | AtomicObject obj ->
      let obj' = Libobject.subst_object (subst,obj) in
      if obj' == obj then node else (id, AtomicObject obj')
    | ModuleObject sobjs ->
      let sobjs' = subst_sobjs subst sobjs in
      if sobjs' == sobjs then node else (id, ModuleObject sobjs')
    | ModuleTypeObject sobjs ->
      let sobjs' = subst_sobjs subst sobjs in
      if sobjs' == sobjs then node else (id, ModuleTypeObject sobjs')
    | IncludeObject aobjs ->
      let aobjs' = subst_aobjs subst aobjs in
      if aobjs' == aobjs then node else (id, IncludeObject aobjs')
    | ExportObject { mpl } ->
      let mpl' = List.Smart.map (subst_filtered subst) mpl in
      if mpl'==mpl then node else (id, ExportObject { mpl = mpl' })
    | KeepObject _ -> assert false
  in
  List.Smart.map subst_one seg

let expand_aobjs = function
  | Objs o -> o
  | Ref (mp, sub) ->
    match ModSubstObjs.get mp with
      | (_,Objs o) -> subst_objects sub o
      | _ -> assert false (* Invariant : any alias points to concrete objs *)

let expand_sobjs (_,aobjs) = expand_aobjs aobjs


(** {6 ModObjs : a cache of module objects}

   For each module, we also store a cache of
   "prefix", "substituted objects", "keep objects".
   This is used for instance to implement the "Import" command.

   substituted objects :
     roughly the objects above after the substitution - we need to
     keep them to call open_object when the module is opened (imported)

   keep objects :
     The list of non-substitutive objects - as above, for each of
     them we will call open_object when the module is opened

   (Some) Invariants:
   * If the module is a functor, it won't appear in this cache.

   * Module objects in substitutive_objects part have empty substituted
     objects.

   * Modules which where created with Module M:=mexpr or with
     Module M:SIG. ... End M. have the keep list empty.
*)

type module_objects =
  { module_prefix : Nametab.object_prefix;
    module_substituted_objects : Lib.lib_objects;
    module_keep_objects : Lib.lib_objects;
  }

module ModObjs :
 sig
   val set : ModPath.t -> module_objects -> unit
   val get : ModPath.t -> module_objects (* may raise Not_found *)
   val all : unit -> module_objects MPmap.t
 end =
 struct
   let table =
     Summary.ref (MPmap.empty : module_objects MPmap.t)
       ~name:"MODULE-OBJS"
   let set mp objs = (table := MPmap.add mp objs !table)
   let get mp = MPmap.find mp !table
   let all () = !table
 end


(** {6 Name management}

    Auxiliary functions to transform full_path and kernel_name given
    by Lib into ModPath.t and DirPath.t needed for modules
*)

let mp_of_kn kn =
  let mp,l = KerName.repr kn in
  MPdot (mp,l)

let dir_of_sp sp =
  let dir,id = repr_path sp in
  add_dirpath_suffix dir id


(** {6 Declaration of module substitutive objects} *)

(** These functions register the visibility of the module and iterates
    through its components. They are called by plenty of module functions *)

let consistency_checks exists dir dirinfo =
  if exists then
    let globref =
      try Nametab.locate_dir (qualid_of_dirpath dir)
      with Not_found ->
        user_err ~hdr:"consistency_checks"
          (DirPath.print dir ++ str " should already exist!")
    in
    assert (Nametab.GlobDirRef.equal globref dirinfo)
  else
    if Nametab.exists_dir dir then
      user_err ~hdr:"consistency_checks"
        (DirPath.print dir ++ str " already exists.")

let compute_visibility exists i =
  if exists then Nametab.Exactly i else Nametab.Until i

(** Iterate some function [iter_objects] on all components of a module *)

let do_module exists iter_objects i obj_dir obj_mp sobjs kobjs =
  let prefix = Nametab.{ obj_dir ; obj_mp; } in
  let dirinfo = Nametab.GlobDirRef.DirModule prefix in
  consistency_checks exists obj_dir dirinfo;
  Nametab.push_dir (compute_visibility exists i) obj_dir dirinfo;
  ModSubstObjs.set obj_mp sobjs;
  (* If we're not a functor, let's iter on the internal components *)
  if sobjs_no_functor sobjs then begin
    let objs = expand_sobjs sobjs in
    let module_objects =
      { module_prefix = prefix;
        module_substituted_objects = objs;
        module_keep_objects = kobjs;
      }
    in
    ModObjs.set obj_mp module_objects;
    iter_objects (i+1) prefix objs;
    iter_objects (i+1) prefix kobjs
  end

let do_module' exists iter_objects i ((sp,kn),sobjs) =
  do_module exists iter_objects i (dir_of_sp sp) (mp_of_kn kn) sobjs []

(** Nota: Interactive modules and module types cannot be recached!
    This used to be checked here via a flag along the substobjs. *)

(** {6 Declaration of module type substitutive objects} *)

(** Nota: Interactive modules and module types cannot be recached!
    This used to be checked more properly here. *)

let load_modtype i sp mp sobjs =
  if Nametab.exists_modtype sp then
    anomaly (pr_path sp ++ str " already exists.");
  Nametab.push_modtype (Nametab.Until i) sp mp;
  ModSubstObjs.set mp sobjs

(** {6 Declaration of substitutive objects for Include} *)

let rec load_object i (name, obj) =
  match obj with
  | AtomicObject o -> Libobject.load_object i (name, o)
  | ModuleObject sobjs -> do_module' false load_objects i (name, sobjs)
  | ModuleTypeObject sobjs ->
    let (sp,kn) = name in
    load_modtype i sp (mp_of_kn kn) sobjs
  | IncludeObject aobjs -> load_include i (name, aobjs)
  | ExportObject _ -> ()
  | KeepObject objs -> load_keep i (name, objs)

and load_objects i prefix objs =
  List.iter (fun (id, obj) -> load_object i (Lib.make_oname prefix id, obj)) objs

and load_include i ((sp,kn), aobjs) =
  let obj_dir = Libnames.dirpath sp in
  let obj_mp = KerName.modpath kn in
  let prefix = Nametab.{ obj_dir; obj_mp; } in
  let o = expand_aobjs aobjs in
  load_objects i prefix o

and load_keep i ((sp,kn),kobjs) =
  (* Invariant : seg isn't empty *)
  let obj_dir = dir_of_sp sp and obj_mp  = mp_of_kn kn in
  let prefix = Nametab.{ obj_dir ; obj_mp; } in
  let modobjs =
    try ModObjs.get obj_mp
    with Not_found -> assert false (* a substobjs should already be loaded *)
  in
  assert Nametab.(eq_op modobjs.module_prefix prefix);
  assert (List.is_empty modobjs.module_keep_objects);
  ModObjs.set obj_mp { modobjs with module_keep_objects = kobjs };
  load_objects i prefix kobjs

(** {6 Implementation of Import and Export commands} *)

let mark_object f obj (exports,acc) =
  (exports, (f,obj)::acc)

let rec collect_modules mpl acc =
  List.fold_left (fun acc fmp -> collect_module fmp acc) acc (List.rev mpl)

and collect_module (f,mp) acc =
  (* May raise Not_found for unknown module and for functors *)
  let modobjs = ModObjs.get mp in
  let prefix = modobjs.module_prefix in
  let acc = collect_objects f 1 prefix modobjs.module_keep_objects acc in
  collect_objects f 1 prefix modobjs.module_substituted_objects acc

and collect_object f i (name, obj as o) acc =
  match obj with
  | ExportObject { mpl } -> collect_exports f i mpl acc
  | AtomicObject _ | IncludeObject _ | KeepObject _
  | ModuleObject _ | ModuleTypeObject _ -> mark_object f o acc

and collect_objects f i prefix objs acc =
  List.fold_left (fun acc (id, obj) ->
    collect_object f i (Lib.make_oname prefix id, obj) acc
  ) acc (List.rev objs)

and collect_export f (f',mp) (exports,objs as acc) =
  match filter_and f f' with
  | None -> acc
  | Some f ->
    let exports' = MPmap.update mp (function
        | None -> Some f
        | Some f0 -> Some (filter_or f f0))
        exports
    in
    (* If the map doesn't change there is nothing new to export.

       It's possible that [filter_and] or [filter_or] mangled precise
       filters such that we repeat uselessly, but the important
       [Unfiltered] case is handled correctly.
    *)
    if exports == exports' then acc
    else
      collect_module (f,mp) (exports', objs)


and collect_exports f i mpl acc =
  if Int.equal i 1 then
    List.fold_left (fun acc fmp -> collect_export f fmp acc) acc (List.rev mpl)
  else acc

let open_modtype i ((sp,kn),_) =
  let mp = mp_of_kn kn in
  let mp' =
    try Nametab.locate_modtype (qualid_of_path sp)
    with Not_found ->
      anomaly (pr_path sp ++ str " should already exist!");
  in
  assert (ModPath.equal mp mp');
  Nametab.push_modtype (Nametab.Exactly i) sp mp

let rec open_object f i (name, obj) =
  match obj with
  | AtomicObject o -> Libobject.open_object f i (name, o)
  | ModuleObject sobjs ->
    let dir = dir_of_sp (fst name) in
    let mp = mp_of_kn (snd name) in
    open_module f i dir mp sobjs
  | ModuleTypeObject sobjs -> open_modtype i (name, sobjs)
  | IncludeObject aobjs -> open_include f i (name, aobjs)
  | ExportObject { mpl } -> open_export f i mpl
  | KeepObject objs -> open_keep f i (name, objs)

and open_module f i obj_dir obj_mp sobjs =
  let prefix = Nametab.{ obj_dir ; obj_mp; } in
  let dirinfo = Nametab.GlobDirRef.DirModule prefix in
  consistency_checks true obj_dir dirinfo;
  (match f with
   | Unfiltered -> Nametab.push_dir (Nametab.Exactly i) obj_dir dirinfo
  );
  (* If we're not a functor, let's iter on the internal components *)
  if sobjs_no_functor sobjs then begin
    let modobjs = ModObjs.get obj_mp in
    open_objects f (i+1) modobjs.module_prefix modobjs.module_substituted_objects
  end

and open_objects f i prefix objs =
  List.iter (fun (id, obj) -> open_object f i (Lib.make_oname prefix id, obj)) objs

and open_include f i ((sp,kn), aobjs) =
  let obj_dir = Libnames.dirpath sp in
  let obj_mp = KerName.modpath kn in
  let prefix = Nametab.{ obj_dir; obj_mp; } in
  let o = expand_aobjs aobjs in
  open_objects f i prefix o

and open_export f i mpl =
  let _,objs = collect_exports f i mpl (MPmap.empty, []) in
  List.iter (fun (f,o) -> open_object f 1 o) objs

and open_keep f i ((sp,kn),kobjs) =
  let obj_dir = dir_of_sp sp and obj_mp = mp_of_kn kn in
  let prefix = Nametab.{ obj_dir; obj_mp; } in
  open_objects f i prefix kobjs

let rec cache_object (name, obj) =
  match obj with
  | AtomicObject o -> Libobject.cache_object (name, o)
  | ModuleObject sobjs -> do_module' false load_objects 1 (name, sobjs)
  | ModuleTypeObject sobjs ->
    let (sp,kn) = name in
    load_modtype 0 sp (mp_of_kn kn) sobjs
  | IncludeObject aobjs -> cache_include (name, aobjs)
  | ExportObject { mpl } -> anomaly Pp.(str "Export should not be cached")
  | KeepObject objs -> cache_keep (name, objs)

and cache_include ((sp,kn), aobjs) =
  let obj_dir = Libnames.dirpath sp in
  let obj_mp = KerName.modpath kn in
  let prefix = Nametab.{ obj_dir; obj_mp; } in
  let o = expand_aobjs aobjs in
  load_objects 1 prefix o;
  open_objects Unfiltered 1 prefix o

and cache_keep ((sp,kn),kobjs) =
  anomaly (Pp.str "This module should not be cached!")

(* Adding operations with containers *)

let add_leaf id obj =
  if ModPath.equal (Lib.current_mp ()) ModPath.initial then
    user_err Pp.(str "No session module started (use -top dir)");
  let oname = Lib.make_foname id in
  cache_object (oname,obj);
  Lib.add_entry oname (Lib.Leaf obj);
  oname

let add_leaves id objs =
  let oname = Lib.make_foname id in
  let add_obj obj =
    Lib.add_entry oname (Lib.Leaf obj);
    load_object 1 (oname,obj)
  in
  List.iter add_obj objs;
  oname

(** {6 Handler for missing entries in ModSubstObjs} *)

(** Since the inner of Module Types are not added by default to
    the ModSubstObjs table, we compensate this by explicit traversal
    of Module Types inner objects when needed. Quite a hack... *)

let mp_id mp id = MPdot (mp, Label.of_id id)

let rec register_mod_objs mp (id,obj) = match obj with
  | ModuleObject sobjs -> ModSubstObjs.set (mp_id mp id) sobjs
  | ModuleTypeObject sobjs -> ModSubstObjs.set (mp_id mp id) sobjs
  | IncludeObject aobjs ->
    List.iter (register_mod_objs mp) (expand_aobjs aobjs)
  | _ -> ()

let handle_missing_substobjs mp = match mp with
  | MPdot (mp',l) ->
    let objs = expand_sobjs (ModSubstObjs.get mp') in
    List.iter (register_mod_objs mp') objs;
    ModSubstObjs.get mp
  | _ ->
    assert false (* Only inner parts of module types should be missing *)

let () = ModSubstObjs.set_missing_handler handle_missing_substobjs



(** {6 From module expression to substitutive objects} *)

(** Turn a chain of [MSEapply] into the head ModPath.t and the
    list of ModPath.t parameters (deepest param coming first).
    The left part of a [MSEapply] must be either [MSEident] or
    another [MSEapply]. *)

let get_applications mexpr =
  let rec get params = function
    | MEident mp -> mp, params
    | MEapply (fexpr, mp) -> get (mp::params) fexpr
    | MEwith _ -> user_err Pp.(str "Non-atomic functor application.")
  in get [] mexpr

(** Create the substitution corresponding to some functor applications *)

let rec compute_subst env mbids sign mp_l inl =
  match mbids,mp_l with
    | _,[] -> mbids,empty_subst
    | [],r -> user_err Pp.(str "Application of a functor with too few arguments.")
    | mbid::mbids,mp::mp_l ->
        let farg_id, farg_b, fbody_b = Modops.destr_functor sign in
        let mb = Environ.lookup_module mp env in
        let mbid_left,subst = compute_subst env mbids fbody_b mp_l inl in
        let resolver =
          if Modops.is_functor mb.mod_type then empty_delta_resolver
          else
            Modops.inline_delta_resolver env inl mp farg_id farg_b mb.mod_delta
        in
        mbid_left,join (map_mbid mbid mp resolver) subst

(** Create the objects of a "with Module" structure. *)

let rec replace_module_object idl mp0 objs0 mp1 objs1 =
  match idl, objs0 with
  | _,[] -> []
  | id::idl,(id',obj)::tail when Id.equal id id' ->
    begin match obj with
    | ModuleObject sobjs ->
      let mp_id = MPdot(mp0, Label.of_id id) in
      let objs = match idl with
        | [] -> subst_objects (map_mp mp1 mp_id empty_delta_resolver) objs1
        | _ ->
          let objs_id = expand_sobjs sobjs in
          replace_module_object idl mp_id objs_id mp1 objs1
      in
      (id, ModuleObject ([], Objs objs))::tail
    | _ -> assert false
    end
  | idl,lobj::tail -> lobj::replace_module_object idl mp0 tail mp1 objs1

let type_of_mod mp env = function
  |true -> (Environ.lookup_module mp env).mod_type
  |false -> (Environ.lookup_modtype mp env).mod_type

let rec get_module_path = function
  |MEident mp -> mp
  |MEwith (me,_) -> get_module_path me
  |MEapply (me,_) -> get_module_path me

(** Substitutive objects of a module expression (or module type) *)

let rec get_module_sobjs is_mod env inl = function
  |MEident mp ->
    begin match ModSubstObjs.get mp with
    |(mbids,Objs _) when not (ModPath.is_bound mp) ->
      (mbids,Ref (mp, empty_subst)) (* we create an alias *)
    |sobjs -> sobjs
    end
  |MEwith (mty, WithDef _) -> get_module_sobjs is_mod env inl mty
  |MEwith (mty, WithMod (idl,mp1)) ->
    assert (not is_mod);
    let sobjs0 = get_module_sobjs is_mod env inl mty in
    assert (sobjs_no_functor sobjs0);
    (* For now, we expanse everything, to be safe *)
    let mp0 = get_module_path mty in
    let objs0 = expand_sobjs sobjs0 in
    let objs1 = expand_sobjs (ModSubstObjs.get mp1) in
    ([], Objs (replace_module_object idl mp0 objs0 mp1 objs1))
  |MEapply _ as me ->
    let mp1, mp_l = get_applications me in
    let mbids, aobjs = get_module_sobjs is_mod env inl (MEident mp1) in
    let typ = type_of_mod mp1 env is_mod in
    let mbids_left,subst = compute_subst env mbids typ mp_l inl in
    (mbids_left, subst_aobjs subst aobjs)

let get_functor_sobjs is_mod env inl (params,mexpr) =
  let (mbids, aobjs) = get_module_sobjs is_mod env inl mexpr in
  (List.map fst params @ mbids, aobjs)


(** {6 Handling of module parameters} *)

(** For printing modules, [process_module_binding] adds names of
    bound module (and its components) to Nametab. It also loads
    objects associated to it. *)

let process_module_binding mbid me =
  let dir = DirPath.make [MBId.to_id mbid] in
  let mp = MPbound mbid in
  let sobjs = get_module_sobjs false (Global.env()) (default_inline ()) me in
  let subst = map_mp (get_module_path me) mp empty_delta_resolver in
  let sobjs = subst_sobjs subst sobjs in
  do_module false load_objects 1 dir mp sobjs []

(** Process a declaration of functor parameter(s) (Id1 .. Idn : Typ)
    i.e. possibly multiple names with the same module type.
    Global environment is updated on the fly.
    Objects in these parameters are also loaded.
    Output is accumulated on top of [acc] (in reverse order). *)

let intern_arg (acc, cst) (idl,(typ,ann)) =
  let inl = inl2intopt ann in
  let lib_dir = Lib.library_dp() in
  let env = Global.env() in
  let (mty, _, cst') = Modintern.interp_module_ast env Modintern.ModType typ in
  let () = Global.push_context_set ~strict:true cst' in
  let env = Global.env () in
  let sobjs = get_module_sobjs false env inl mty in
  let mp0 = get_module_path mty in
  let fold acc {CAst.v=id} =
    let dir = DirPath.make [id] in
    let mbid = MBId.make lib_dir id in
    let mp = MPbound mbid in
    let resolver = Global.add_module_parameter mbid mty inl in
    let sobjs = subst_sobjs (map_mp mp0 mp resolver) sobjs in
    do_module false load_objects 1 dir mp sobjs [];
    (mbid,mty,inl)::acc
  in
  let acc = List.fold_left fold acc idl in
  (acc, Univ.ContextSet.union cst cst')

(** Process a list of declarations of functor parameters
    (Id11 .. Id1n : Typ1)..(Idk1 .. Idkm : Typk)
    Global environment is updated on the fly.
    The calls to [interp_modast] should be interleaved with these
    env updates, otherwise some "with Definition" could be rejected.
    Returns a list of mbids and entries (in reversed order).

    This used to be a [List.concat (List.map ...)], but this should
    be more efficient and independent of [List.map] eval order.
*)

let intern_args params =
  List.fold_left intern_arg ([], Univ.ContextSet.empty) params


(** {6 Auxiliary functions concerning subtyping checks} *)

let check_sub mtb sub_mtb_l =
  (* The constraints are checked and forgot immediately : *)
  ignore (List.fold_right
            (fun sub_mtb env ->
               Environ.add_constraints
                 (Subtyping.check_subtypes env mtb sub_mtb) env)
            sub_mtb_l (Global.env()))

(** This function checks if the type calculated for the module [mp] is
    a subtype of all signatures in [sub_mtb_l]. Uses only the global
    environment. *)

let check_subtypes mp sub_mtb_l =
  let mb =
    try Global.lookup_module mp with Not_found -> assert false
  in
  let mtb = Modops.module_type_of_module mb in
  check_sub mtb sub_mtb_l

(** Same for module type [mp] *)

let check_subtypes_mt mp sub_mtb_l =
  let mtb =
    try Global.lookup_modtype mp with Not_found -> assert false
  in
  check_sub mtb sub_mtb_l

(** Create a params entry.
    In [args], the youngest module param now comes first. *)

let mk_params_entry args =
  List.rev_map (fun (mbid,arg_t,_) -> (mbid,arg_t)) args

(** Create a functor type struct.
    In [args], the youngest module param now comes first. *)

let mk_funct_type env args seb0 =
  List.fold_left
    (fun (seb,cst) (arg_id,arg_t,arg_inl) ->
      let mp = MPbound arg_id in
      let arg_t, cst' = Mod_typing.translate_modtype env mp arg_inl ([],arg_t) in
      MoreFunctor(arg_id,arg_t,seb), Univ.Constraints.union cst cst')
    seb0 args

(** Prepare the module type list for check of subtypes *)

let build_subtypes env mp args mtys =
  let (ctx, ans) = List.fold_left_map
    (fun ctx (m,ann) ->
       let inl = inl2intopt ann in
       let mte, _, ctx' = Modintern.interp_module_ast env Modintern.ModType m in
       let env = Environ.push_context_set ~strict:true ctx' env in
       let ctx = Univ.ContextSet.union ctx ctx' in
       let mtb, cst = Mod_typing.translate_modtype env mp inl ([],mte) in
       let mod_type, cst = mk_funct_type env args (mtb.mod_type,cst) in
       let ctx = Univ.ContextSet.add_constraints cst ctx in
       ctx, { mtb with mod_type })
    Univ.ContextSet.empty mtys
  in
  (ans, ctx)


(** {6 Current module information}

    This information is stored by each [start_module] for use
    in a later [end_module]. *)

type current_module_info = {
  cur_typ : (module_struct_entry * int option) option; (** type via ":" *)
  cur_typs : module_type_body list (** types via "<:" *)
}

let default_module_info = { cur_typ = None; cur_typs = [] }

let openmod_info = Summary.ref default_module_info ~name:"MODULE-INFO"


(** {6 Current module type information}

   This information is stored by each [start_modtype] for use
   in a later [end_modtype]. *)

let openmodtype_info =
  Summary.ref ([] : module_type_body list) ~name:"MODTYPE-INFO"


(** {6 Modules : start, end, declare} *)

module RawModOps = struct

let start_module export id args res fs =
  let mp = Global.start_module id in
  let arg_entries_r, ctx = intern_args args in
  let () = Global.push_context_set ~strict:true ctx in
  let env = Global.env () in
  let res_entry_o, subtyps, ctx = match res with
    | Enforce (res,ann) ->
        let inl = inl2intopt ann in
        let (mte, _, ctx) = Modintern.interp_module_ast env Modintern.ModType res in
        let env = Environ.push_context_set ~strict:true ctx env in
        (* We check immediately that mte is well-formed *)
        let _, _, _, cst = Mod_typing.translate_mse env None inl mte in
        let ctx = Univ.ContextSet.add_constraints cst ctx in
        Some (mte, inl), [], ctx
    | Check resl ->
      let typs, ctx = build_subtypes env mp arg_entries_r resl in
      None, typs, ctx
  in
  let () = Global.push_context_set ~strict:true ctx in
  openmod_info := { cur_typ = res_entry_o; cur_typs = subtyps };
  let prefix = Lib.start_module export id mp fs in
  Nametab.(push_dir (Until 1) (prefix.obj_dir) (GlobDirRef.DirOpenModule prefix));
  mp

let end_module () =
  let oldoname,oldprefix,fs,lib_stack = Lib.end_module () in
  let substitute, keep, special = Lib.classify_segment lib_stack in
  let m_info = !openmod_info in

  (* For sealed modules, we use the substitutive objects of their signatures *)
  let sobjs0, keep, special = match m_info.cur_typ with
    | None -> ([], Objs substitute), keep, special
    | Some (mty, inline) ->
      get_module_sobjs false (Global.env()) inline mty, [], []
  in
  let id = basename (fst oldoname) in
  let mp,mbids,resolver = Global.end_module fs id m_info.cur_typ in
  let sobjs = let (ms,objs) = sobjs0 in (mbids@ms,objs) in

  check_subtypes mp m_info.cur_typs;

  (* We substitute objects if the module is sealed by a signature *)
  let sobjs =
    match m_info.cur_typ with
      | None -> sobjs
      | Some (mty, _) ->
        subst_sobjs (map_mp (get_module_path mty) mp resolver) sobjs
  in
  let node = ModuleObject sobjs in
  (* We add the keep objects, if any, and if this isn't a functor *)
  let objects = match keep, mbids with
    | [], _ | _, _ :: _ -> special@[node]
    | _ -> special@[node;KeepObject keep]
  in
  let newoname = add_leaves id objects in

  (* Name consistency check : start_ vs. end_module, kernel vs. library *)
  assert (eq_full_path (fst newoname) (fst oldoname));
  assert (ModPath.equal (mp_of_kn (snd newoname)) mp);

  mp

(* TODO cleanup push universes directly to global env *)
let declare_module id args res mexpr_o fs =
  (* We simulate the beginning of an interactive module,
     then we adds the module parameters to the global env. *)
  let mp = Global.start_module id in
  let arg_entries_r, ctx = intern_args args in
  let params = mk_params_entry arg_entries_r in
  let env = Global.env () in
  let env = Environ.push_context_set ~strict:true ctx env in
  let mty_entry_o, subs, inl_res, ctx' = match res with
    | Enforce (mty,ann) ->
        let inl = inl2intopt ann in
        let (mte, _, ctx) = Modintern.interp_module_ast env Modintern.ModType mty in
        let env = Environ.push_context_set ~strict:true ctx env in
        (* We check immediately that mte is well-formed *)
        let _, _, _, cst = Mod_typing.translate_mse env None inl mte in
        let ctx = Univ.ContextSet.add_constraints cst ctx in
        Some mte, [], inl, ctx
    | Check mtys ->
      let typs, ctx = build_subtypes env mp arg_entries_r mtys in
      None, typs, default_inline (), ctx
  in
  let env = Environ.push_context_set ~strict:true ctx' env in
  let ctx = Univ.ContextSet.union ctx ctx' in
  let mexpr_entry_o, inl_expr, ctx' = match mexpr_o with
    | None -> None, default_inline (), Univ.ContextSet.empty
    | Some (mexpr,ann) ->
      let (mte, _, ctx) = Modintern.interp_module_ast env Modintern.Module mexpr in
      Some mte, inl2intopt ann, ctx
  in
  let env = Environ.push_context_set ~strict:true ctx' env in
  let ctx = Univ.ContextSet.union ctx ctx' in
  let entry = match mexpr_entry_o, mty_entry_o with
    | None, None -> assert false (* No body, no type ... *)
    | None, Some typ -> MType (params, typ)
    | Some body, otyp -> MExpr (params, body, otyp)
  in
  let sobjs, mp0 = match entry with
    | MType (_,mte) | MExpr (_,_,Some mte) ->
      get_functor_sobjs false env inl_res (params,mte), get_module_path mte
    | MExpr (_,me,None) ->
      get_functor_sobjs true env inl_expr (params,me), get_module_path me
  in
  (* Undo the simulated interactive building of the module
     and declare the module as a whole *)
  Summary.unfreeze_summaries fs;
  let inl = match inl_expr with
  | None -> None
  | _ -> inl_res
  in
  let () = Global.push_context_set ~strict:true ctx in
  let mp_env,resolver = Global.add_module id entry inl in

  (* Name consistency check : kernel vs. library *)
  assert (ModPath.equal mp (mp_of_kn (Lib.make_kn id)));
  assert (ModPath.equal mp mp_env);

  check_subtypes mp subs;

  let sobjs = subst_sobjs (map_mp mp0 mp resolver) sobjs in
  ignore (add_leaf id (ModuleObject sobjs));
  mp

end

(** {6 Module types : start, end, declare} *)

module RawModTypeOps = struct

let start_modtype id args mtys fs =
  let mp = Global.start_modtype id in
  let arg_entries_r, cst = intern_args args in
  let () = Global.push_context_set ~strict:true cst in
  let env = Global.env () in
  let sub_mty_l, cst = build_subtypes env mp arg_entries_r mtys in
  let () = Global.push_context_set ~strict:true cst in
  openmodtype_info := sub_mty_l;
  let prefix = Lib.start_modtype id mp fs in
  Nametab.(push_dir (Until 1) (prefix.obj_dir) (GlobDirRef.DirOpenModtype prefix));
  mp

let end_modtype () =
  let oldoname,prefix,fs,lib_stack = Lib.end_modtype () in
  let id = basename (fst oldoname) in
  let substitute, _, special = Lib.classify_segment lib_stack in
  let sub_mty_l = !openmodtype_info in
  let mp, mbids = Global.end_modtype fs id in
  let modtypeobjs = (mbids, Objs substitute) in
  check_subtypes_mt mp sub_mty_l;
  let oname = add_leaves id (special@[ModuleTypeObject modtypeobjs])
  in
  (* Check name consistence : start_ vs. end_modtype, kernel vs. library *)
  assert (eq_full_path (fst oname) (fst oldoname));
  assert (ModPath.equal (mp_of_kn (snd oname)) mp);

  mp

let declare_modtype id args mtys (mty,ann) fs =
  let inl = inl2intopt ann in
  (* We simulate the beginning of an interactive module,
     then we adds the module parameters to the global env. *)
  let mp = Global.start_modtype id in
  let arg_entries_r, arg_ctx = intern_args args in
  let () = Global.push_context_set ~strict:true arg_ctx in
  let params = mk_params_entry arg_entries_r in
  let env = Global.env () in
  let mte, _, mte_ctx = Modintern.interp_module_ast env Modintern.ModType mty in
  let () = Global.push_context_set ~strict:true mte_ctx in
  let env = Global.env () in
  (* We check immediately that mte is well-formed *)
  let _, _, _, mte_cst = Mod_typing.translate_mse env None inl mte in
  let () = Global.push_context_set ~strict:true (Univ.Level.Set.empty,mte_cst) in
  let env = Global.env () in
  let entry = params, mte in
  let sub_mty_l, sub_mty_ctx = build_subtypes env mp arg_entries_r mtys in
  let () = Global.push_context_set ~strict:true sub_mty_ctx in
  let env = Global.env () in
  let sobjs = get_functor_sobjs false env inl entry in
  let subst = map_mp (get_module_path (snd entry)) mp empty_delta_resolver in
  let sobjs = subst_sobjs subst sobjs in

  (* Undo the simulated interactive building of the module type
     and declare the module type as a whole *)
  Summary.unfreeze_summaries fs;

  (* We enrich the global environment *)
  let () = Global.push_context_set ~strict:true arg_ctx in
  let () = Global.push_context_set ~strict:true mte_ctx in
  let () = Global.push_context_set ~strict:true (Univ.Level.Set.empty,mte_cst) in
  let () = Global.push_context_set ~strict:true sub_mty_ctx in
  let mp_env = Global.add_modtype id entry inl in

  (* Name consistency check : kernel vs. library *)
  assert (ModPath.equal mp_env mp);

  (* Subtyping checks *)
  check_subtypes_mt mp sub_mty_l;

  ignore (add_leaf id (ModuleTypeObject sobjs));
  mp

end

(** {6 Include} *)

module RawIncludeOps = struct

let rec include_subst env mp reso mbids sign inline = match mbids with
  | [] -> empty_subst
  | mbid::mbids ->
    let farg_id, farg_b, fbody_b = Modops.destr_functor sign in
    let subst = include_subst env mp reso mbids fbody_b inline in
    let mp_delta =
      Modops.inline_delta_resolver env inline mp farg_id farg_b reso
    in
    join (map_mbid mbid mp mp_delta) subst

let rec decompose_functor mpl typ =
  match mpl, typ with
  | [], _ -> typ
  | _::mpl, MoreFunctor(_,_,str) -> decompose_functor mpl str
  | _ -> user_err Pp.(str "Application of a functor with too much arguments.")

exception NoIncludeSelf

let type_of_incl env is_mod = function
  |MEident mp -> type_of_mod mp env is_mod
  |MEapply _ as me ->
    let mp0, mp_l = get_applications me in
    decompose_functor mp_l (type_of_mod mp0 env is_mod)
  |MEwith _ -> raise NoIncludeSelf

let declare_one_include (me_ast,annot) =
  let env = Global.env() in
  let me, kind, cst = Modintern.interp_module_ast env Modintern.ModAny me_ast in
  let () = Global.push_context_set ~strict:true cst in
  let env = Global.env () in
  let is_mod = (kind == Modintern.Module) in
  let cur_mp = Lib.current_mp () in
  let inl = inl2intopt annot in
  let mbids,aobjs = get_module_sobjs is_mod env inl me in
  let subst_self =
    try
      if List.is_empty mbids then raise NoIncludeSelf;
      let typ = type_of_incl env is_mod me in
      let reso,_ = Safe_typing.delta_of_senv (Global.safe_env ()) in
      include_subst env cur_mp reso mbids typ inl
    with NoIncludeSelf -> empty_subst
  in
  let base_mp = get_module_path me in
  let resolver = Global.add_include me is_mod inl in
  let subst = join subst_self (map_mp base_mp cur_mp resolver) in
  let aobjs = subst_aobjs subst aobjs in
  ignore (add_leaf (Lib.current_mod_id ()) (IncludeObject aobjs))

let declare_include me_asts = List.iter declare_one_include me_asts

end


(** {6 Module operations handling summary freeze/unfreeze} *)

let protect_summaries f =
  let fs = Summary.freeze_summaries ~marshallable:false in
  try f fs
  with reraise ->
    (* Something wrong: undo the whole process *)
    let reraise = Exninfo.capture reraise in
    let () = Summary.unfreeze_summaries fs in
    Exninfo.iraise reraise

let start_module export id args res =
  protect_summaries (RawModOps.start_module export id args res)

let end_module = RawModOps.end_module

let declare_module id args mtys me_l =
  let declare_me fs = match me_l with
    | [] -> RawModOps.declare_module id args mtys None fs
    | [me] -> RawModOps.declare_module id args mtys (Some me) fs
    | me_l ->
        ignore (RawModOps.start_module None id args mtys fs);
        RawIncludeOps.declare_include me_l;
        RawModOps.end_module ()
  in
  protect_summaries declare_me

let start_modtype id args mtys =
  protect_summaries (RawModTypeOps.start_modtype id args mtys)

let end_modtype = RawModTypeOps.end_modtype

let declare_modtype id args mtys mty_l =
  let declare_mt fs = match mty_l with
    | [] -> assert false
    | [mty] -> RawModTypeOps.declare_modtype id args mtys mty fs
    | mty_l ->
        ignore (RawModTypeOps.start_modtype id args mtys fs);
        RawIncludeOps.declare_include mty_l;
        RawModTypeOps.end_modtype ()
  in
  protect_summaries declare_mt

let declare_include me_asts =
  if Global.sections_are_opened () then
    user_err Pp.(str "Include is not allowed inside sections.");
  protect_summaries (fun _ -> RawIncludeOps.declare_include me_asts)


(** {6 Libraries} *)

type library_name = DirPath.t

(** A library object is made of some substitutive objects
    and some "keep" objects. *)

type library_objects = Lib.lib_objects * Lib.lib_objects

(** For the native compiler, we cache the library values *)

let register_library dir cenv (objs:library_objects) digest univ =
  let mp = MPfile dir in
  let () =
    try
      (* Is this library already loaded ? *)
      ignore(Global.lookup_module mp);
    with Not_found ->
      (* If not, let's do it now ... *)
      let mp' = Global.import cenv univ digest in
      if not (ModPath.equal mp mp') then
        anomaly (Pp.str "Unexpected disk module name.");
  in
  let sobjs,keepobjs = objs in
  do_module false load_objects 1 dir mp ([],Objs sobjs) keepobjs

let start_library dir =
  let mp = Global.start_library dir in
  openmod_info := default_module_info;
  Lib.start_compilation dir mp

let end_library_hook = ref ignore
let append_end_library_hook f =
  let old_f = !end_library_hook in
  end_library_hook := fun () -> old_f(); f ()

let end_library ~output_native_objects dir =
  !end_library_hook();
  let oname = Lib.end_compilation_checks dir in
  let mp,cenv,ast = Global.export ~output_native_objects dir in
  let prefix, lib_stack = Lib.end_compilation oname in
  assert (ModPath.equal mp (MPfile dir));
  let substitute, keep, _ = Lib.classify_segment lib_stack in
  cenv,(substitute,keep),ast

let import_modules ~export mpl =
  let _,objs = collect_modules mpl (MPmap.empty, []) in
  List.iter (fun (f,o) -> open_object f 1 o) objs;
  if export then Lib.add_anonymous_entry (Lib.Leaf (ExportObject { mpl }))

let import_module f ~export mp =
  import_modules ~export [f,mp]

(** {6 Iterators} *)

let iter_all_segments f =
  let rec apply_obj prefix (id,obj) = match obj with
    | IncludeObject aobjs ->
      let objs = expand_aobjs aobjs in
      List.iter (apply_obj prefix) objs
    | _ -> f (Lib.make_oname prefix id) obj
  in
  let apply_mod_obj _ modobjs =
    let prefix = modobjs.module_prefix in
    List.iter (apply_obj prefix) modobjs.module_substituted_objects;
    List.iter (apply_obj prefix) modobjs.module_keep_objects
  in
  let apply_node = function
    | sp, Lib.Leaf o -> f sp o
    | _ -> ()
  in
  MPmap.iter apply_mod_obj (ModObjs.all ());
  List.iter apply_node (Lib.contents ())


(** {6 Some types used to shorten declaremods.mli} *)

type module_params = (lident list * (Constrexpr.module_ast * inline)) list

(** {6 Debug} *)

let debug_print_modtab _ =
  let pr_seg = function
    | [] -> str "[]"
    | l -> str "[." ++ int (List.length l) ++ str ".]"
  in
  let pr_modinfo mp modobjs s =
    let objs = modobjs.module_substituted_objects @ modobjs.module_keep_objects in
    s ++ str (ModPath.to_string mp) ++ (spc ())
    ++ (pr_seg (Lib.segment_of_objects modobjs.module_prefix objs))
  in
  let modules = MPmap.fold pr_modinfo (ModObjs.all ()) (mt ()) in
  hov 0 modules
