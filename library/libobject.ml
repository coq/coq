
(* $Id$ *)

open Util
open Names

type 'a object_declaration = {
  cache_function : section_path * 'a -> unit;
  load_function : section_path * 'a -> unit;
  open_function : section_path * 'a -> unit;
  specification_function : 'a -> 'a }

type obj = Dyn.t (* persistent dynamic objects *)

type dynamic_object_declaration = {
  dyn_cache_function : section_path * obj -> unit;
  dyn_load_function : section_path * obj -> unit;
  dyn_open_function : section_path * obj -> unit;
  dyn_specification_function : obj -> obj }

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
  and spec_extractor lobj = 
    infun(odecl.specification_function (outfun lobj))
  in 
  Hashtbl.add cache_tab na { dyn_cache_function = cacher;
			     dyn_load_function = loader;
                             dyn_open_function = opener;
                             dyn_specification_function = spec_extractor };
  (infun,outfun)

let apply_dyn_fun f lobj =
  let tag = object_tag lobj in
  try
    let dodecl = Hashtbl.find cache_tab tag in f dodecl
  with Not_found -> 
    anomaly ("Cannot find library functions for an object with tag "^tag)

let cache_object ((_,lobj) as node) =
  apply_dyn_fun (fun d -> d.dyn_cache_function node) lobj

let load_object ((_,lobj) as node) = 
  apply_dyn_fun (fun d -> d.dyn_load_function node) lobj

let open_object ((_,lobj) as node) = 
  apply_dyn_fun (fun d -> d.dyn_open_function node) lobj

let extract_object_specification lobj =
  apply_dyn_fun (fun d -> d.dyn_specification_function lobj) lobj
