(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Names
open Libnames

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
    Dispose | Substitute of 'a | Keep of bool * 'a | Anticipate of 'a


type 'a object_declaration = {
  object_name : string;
  cache_function : section_path * 'a -> unit;
  load_function : section_path * 'a -> unit;
  open_function : section_path * 'a -> unit;
  classify_function : section_path * 'a -> 'a substitutivity;
  subst_function : substitution -> 'a -> 'a;
  export_function : 'a -> 'a option }

let yell s = anomaly s

let default_object s = {
  object_name = s;
  cache_function = (fun _ -> ());
  load_function = (fun _ -> ());
  open_function = (fun _ -> ());
  subst_function = (fun _ -> 
    yell ("The object "^s^" does not know how to substitute!"));
  classify_function = (fun (_,obj) -> Keep (true,obj));
  export_function = (fun _ -> None)} 


(* The suggested object declaration is the following:

   declare_object { (default_object "MY OBJECT") with
       cache_function = fun (sp,a) -> Mytbl.add sp a}

   and the listed functions are only those which definitions accually 
   differ from the default.

   This helps introducing new functions in objects.
*)


type obj = Dyn.t (* persistent dynamic objects *)

type dynamic_object_declaration = {
  dyn_cache_function : section_path * obj -> unit;
  dyn_load_function : section_path * obj -> unit;
  dyn_open_function : section_path * obj -> unit;
  dyn_subst_function : substitution -> obj -> obj;
  dyn_classify_function : section_path * obj -> obj substitutivity;
  dyn_export_function : obj -> obj option }

let object_tag lobj = Dyn.tag lobj

let cache_tab = 
  (Hashtbl.create 17 : (string,dynamic_object_declaration) Hashtbl.t)

let declare_object odecl =
  let na = odecl.object_name in
  let (infun,outfun) = Dyn.create na in
  let cacher (spopt,lobj) =
    if Dyn.tag lobj = na then odecl.cache_function (spopt,outfun lobj)
    else anomaly "somehow we got the wrong dynamic object in the cachefun"
  and loader (spopt,lobj) =
    if Dyn.tag lobj = na then odecl.load_function (spopt,outfun lobj)
    else anomaly "somehow we got the wrong dynamic object in the loadfun"
  and opener (spopt,lobj) =
    if Dyn.tag lobj = na then odecl.open_function (spopt,outfun lobj)
    else anomaly "somehow we got the wrong dynamic object in the openfun"
  and substituter sub lobj = 
    if Dyn.tag lobj = na then 
      infun (odecl.subst_function sub (outfun lobj))
    else anomaly "somehow we got the wrong dynamic object in the substfun"
  and classifier (spopt,lobj) = 
    if Dyn.tag lobj = na then 
      match odecl.classify_function (spopt,outfun lobj) with
	| Dispose -> Dispose
	| Substitute obj -> Substitute (infun obj)
	| Keep (b,obj) -> Keep (b,(infun obj))
	| Anticipate (obj) -> Anticipate (infun obj)
    else 
      anomaly "somehow we got the wrong dynamic object in the classifyfun"
  and exporter lobj = 
    if Dyn.tag lobj = na then 
      option_app infun (odecl.export_function (outfun lobj))
    else 
      anomaly "somehow we got the wrong dynamic object in the exportfun"

  in 
  Hashtbl.add cache_tab na { dyn_cache_function = cacher;
			     dyn_load_function = loader;
                             dyn_open_function = opener;
			     dyn_subst_function = substituter;
			     dyn_classify_function = classifier;
                             dyn_export_function = exporter };
  (infun,outfun)

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
	  if !relax_flag then
	    failwith "local to_apply_dyn_fun"
	  else
	    anomaly
	      ("Cannot find library functions for an object with tag "^tag) in 
  	f dodecl
    with
	Failure "local to_apply_dyn_fun" -> deflt;;

let cache_object ((_,lobj) as node) =
  apply_dyn_fun () (fun d -> d.dyn_cache_function node) lobj

let load_object ((_,lobj) as node) = 
  apply_dyn_fun () (fun d -> d.dyn_load_function node) lobj

let open_object ((_,lobj) as node) = 
  apply_dyn_fun () (fun d -> d.dyn_open_function node) lobj

let subst_object subst lobj = 
  apply_dyn_fun lobj (fun d -> d.dyn_subst_function subst lobj) lobj

let classify_object ((_,lobj) as node) = 
  apply_dyn_fun Dispose (fun d -> d.dyn_classify_function node) lobj

let export_object lobj =
  apply_dyn_fun None (fun d -> d.dyn_export_function lobj) lobj
