(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Names
open Libnames
open Mod_subst

(* The relax flag is used to make it possible to load files while ignoring
   failures to incorporate some objects.  This can be useful when one
   wants to work with restricted Coq programs that have only parts of
   the full capabilities, but may still be able to work correctly for
   limited purposes.  One example is for the graphical interface, that uses
   such a limite coq process to do only parsing.  It loads .vo files, but
   is only interested in loading the grammar rule definitions. *)

let relax_flag = ref false;;

let relax b = relax_flag := b;;

type 'a substitutivity =
    Dispose | Substitute of 'a | Keep of 'a | Anticipate of 'a

type 'a object_declaration = {
  object_name : string;
  cache_function : object_name * 'a -> unit;
  load_function : int -> object_name * 'a -> unit;
  open_function : int -> object_name * 'a -> unit;
  classify_function : 'a -> 'a substitutivity;
  subst_function : object_name * substitution * 'a -> 'a;
  discharge_function : object_name * 'a -> 'a option;
  rebuild_function : 'a -> 'a }

let yell s = anomaly s

let default_object s = {
  object_name = s;
  cache_function = (fun _ -> ());
  load_function = (fun _ _ -> ());
  open_function = (fun _ _ -> ());
  subst_function = (fun _ ->
    yell ("The object "^s^" does not know how to substitute!"));
  classify_function = (fun obj -> Keep obj);
  discharge_function = (fun _ -> None);
  rebuild_function = (fun x -> x)}


(* The suggested object declaration is the following:

   declare_object { (default_object "MY OBJECT") with
       cache_function = fun (sp,a) -> Mytbl.add sp a}

   and the listed functions are only those which definitions accually
   differ from the default.

   This helps introducing new functions in objects.
*)

let ident_subst_function (_,_,a) = a

type obj = Dyn.t (* persistent dynamic objects *)

type dynamic_object_declaration = {
  dyn_cache_function : object_name * obj -> unit;
  dyn_load_function : int -> object_name * obj -> unit;
  dyn_open_function : int -> object_name * obj -> unit;
  dyn_subst_function : object_name * substitution * obj -> obj;
  dyn_classify_function : obj -> obj substitutivity;
  dyn_discharge_function : object_name * obj -> obj option;
  dyn_rebuild_function : obj -> obj }

let object_tag lobj = Dyn.tag lobj

let cache_tab =
  (Hashtbl.create 17 : (string,dynamic_object_declaration) Hashtbl.t)

let declare_object odecl =
  let na = odecl.object_name in
  let (infun,outfun) = Dyn.create na in
  let cacher (oname,lobj) =
    if Dyn.tag lobj = na then odecl.cache_function (oname,outfun lobj)
    else anomaly "somehow we got the wrong dynamic object in the cachefun"
  and loader i (oname,lobj) =
    if Dyn.tag lobj = na then odecl.load_function i (oname,outfun lobj)
    else anomaly "somehow we got the wrong dynamic object in the loadfun"
  and opener i (oname,lobj) =
    if Dyn.tag lobj = na then odecl.open_function i (oname,outfun lobj)
    else anomaly "somehow we got the wrong dynamic object in the openfun"
  and substituter (oname,sub,lobj) =
    if Dyn.tag lobj = na then
      infun (odecl.subst_function (oname,sub,outfun lobj))
    else anomaly "somehow we got the wrong dynamic object in the substfun"
  and classifier lobj =
    if Dyn.tag lobj = na then
      match odecl.classify_function (outfun lobj) with
	| Dispose -> Dispose
	| Substitute obj -> Substitute (infun obj)
	| Keep obj -> Keep (infun obj)
	| Anticipate (obj) -> Anticipate (infun obj)
    else
      anomaly "somehow we got the wrong dynamic object in the classifyfun"
  and discharge (oname,lobj) =
    if Dyn.tag lobj = na then
      Option.map infun (odecl.discharge_function (oname,outfun lobj))
    else
      anomaly "somehow we got the wrong dynamic object in the dischargefun"
  and rebuild lobj =
    if Dyn.tag lobj = na then infun (odecl.rebuild_function (outfun lobj))
    else anomaly "somehow we got the wrong dynamic object in the rebuildfun"
  in
  Hashtbl.add cache_tab na { dyn_cache_function = cacher;
			     dyn_load_function = loader;
                             dyn_open_function = opener;
			     dyn_subst_function = substituter;
			     dyn_classify_function = classifier;
			     dyn_discharge_function = discharge;
			     dyn_rebuild_function = rebuild };
  (infun,outfun)

let missing_tab = (Hashtbl.create 17 : (string, unit) Hashtbl.t)

(* this function describes how the cache, load, open, and export functions
   are triggered.  In relaxed mode, this function just return a meaningless
   value instead of raising an exception when they fail. *)

let apply_dyn_fun deflt f lobj =
  let tag = object_tag lobj in
  try
    let dodecl =
      try
        Hashtbl.find cache_tab tag
      with Not_found ->
        failwith "local to_apply_dyn_fun" in
    f dodecl
  with
    Failure "local to_apply_dyn_fun" ->
      if not (!relax_flag || Hashtbl.mem missing_tab tag) then
        begin
          Pp.warning ("Cannot find library functions for an object with tag "
                      ^ tag ^ " (a plugin may be missing)");
          Hashtbl.add missing_tab tag ()
        end;
      deflt

let cache_object ((_,lobj) as node) =
  apply_dyn_fun () (fun d -> d.dyn_cache_function node) lobj

let load_object i ((_,lobj) as node) =
  apply_dyn_fun () (fun d -> d.dyn_load_function i node) lobj

let open_object i ((_,lobj) as node) =
  apply_dyn_fun () (fun d -> d.dyn_open_function i node) lobj

let subst_object ((_,_,lobj) as node) =
  apply_dyn_fun lobj (fun d -> d.dyn_subst_function node) lobj

let classify_object lobj =
  apply_dyn_fun Dispose (fun d -> d.dyn_classify_function lobj) lobj

let discharge_object ((_,lobj) as node) =
  apply_dyn_fun None (fun d -> d.dyn_discharge_function node) lobj

let rebuild_object lobj =
  apply_dyn_fun lobj (fun d -> d.dyn_rebuild_function lobj) lobj
