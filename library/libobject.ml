(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
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

type 'a object_declaration = {
  cache_function : section_path * 'a -> unit;
  load_function : section_path * 'a -> unit;
  open_function : section_path * 'a -> unit;
  export_function : 'a -> 'a option }

type obj = Dyn.t (* persistent dynamic objects *)

type dynamic_object_declaration = {
  dyn_cache_function : section_path * obj -> unit;
  dyn_load_function : section_path * obj -> unit;
  dyn_open_function : section_path * obj -> unit;
  dyn_export_function : obj -> obj option }

let object_tag lobj = Dyn.tag lobj

let cache_tab = 
  (Hashtbl.create 17 : (string,dynamic_object_declaration) Hashtbl.t)

let declare_object (na,odecl) =
  let (infun,outfun) = Dyn.create na in
  let cacher (spopt,lobj) =
    if Dyn.tag lobj = na then odecl.cache_function(spopt,outfun lobj)
    else anomaly "somehow we got the wrong dynamic object in the cachefun"
  and loader (spopt,lobj) =
    if Dyn.tag lobj = na then odecl.load_function (spopt,outfun lobj)
    else anomaly "somehow we got the wrong dynamic object in the loadfun"
  and opener (spopt,lobj) =
    if Dyn.tag lobj = na then odecl.open_function (spopt,outfun lobj)
    else anomaly "somehow we got the wrong dynamic object in the openfun"
  and exporter lobj = 
    option_app infun (odecl.export_function (outfun lobj))
  in 
  Hashtbl.add cache_tab na { dyn_cache_function = cacher;
			     dyn_load_function = loader;
                             dyn_open_function = opener;
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

let export_object lobj =
  apply_dyn_fun None (fun d -> d.dyn_export_function lobj) lobj
