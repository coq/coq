
(* $Id$ *)

open Util
open Names

type 'a object_declaration = {
  load_function : 'a -> unit;
  cache_function : section_path * 'a -> unit;
  specification_function : 'a -> 'a }

type obj = Dyn.t (* persistent dynamic objects *)

type dynamic_object_declaration = {
  dyn_load_function : obj -> unit;
  dyn_cache_function : section_path * obj -> unit;
  dyn_specification_function : obj -> obj }

let object_tag lobj = Dyn.tag lobj

let cache_tab = 
  (Hashtbl.create 17 : (string,dynamic_object_declaration) Hashtbl.t)

let declare_object (na,odecl) =
  let (infun,outfun) = Dyn.create na in
  let loader lobj =
    if Dyn.tag lobj = na then odecl.load_function (outfun lobj)
    else anomaly "somehow we got the wrong dynamic object in the loadfun"
  and cacher (spopt,lobj) =
    if Dyn.tag lobj = na then odecl.cache_function(spopt,outfun lobj)
    else anomaly "somehow we got the wrong dynamic object in the cachefun"
  and spec_extractor lobj = 
    infun(odecl.specification_function (outfun lobj))
  in 
  Hashtbl.add cache_tab na { dyn_load_function = loader;
                             dyn_cache_function = cacher;
                             dyn_specification_function = spec_extractor };
  (infun,outfun)


let load_object lobj =
  let tag = object_tag lobj in
  try 
    let dodecl = Hashtbl.find cache_tab tag in 
    dodecl.dyn_load_function lobj
  with Not_found ->
    anomaly ("Cannot find loadfun for an object with tag "^tag)

let cache_object (spopt,lobj) =
  let tag = object_tag lobj in
  try 
    let dodecl = Hashtbl.find cache_tab tag in 
    dodecl.dyn_cache_function(spopt,lobj)
  with Not_found ->
    anomaly ("Cannot find cachefun for an object with tag "^tag)

let extract_object_specification lobj =
  let tag = object_tag lobj in
  try 
    let dodecl = Hashtbl.find cache_tab tag in
    dodecl.dyn_specification_function lobj
  with Not_found ->
    anomaly ("Cannot find specification extractor for an object with tag "^tag)
