
(* $Id$ *)

open Pp
open Util
open Names

type 'a summary_declaration = {
  freeze_function : unit -> 'a;
  unfreeze_function : 'a -> unit;
  init_function : unit -> unit }

let summaries = 
  (Hashtbl.create 17 : (string, Dyn.t summary_declaration) Hashtbl.t)

let declare_summary sumname sdecl =
  let (infun,outfun) = Dyn.create (sumname^"-SUMMARY") in
  let dyn_freeze () = infun (sdecl.freeze_function())
  and dyn_unfreeze sum = sdecl.unfreeze_function (outfun sum)
  and dyn_init = sdecl.init_function in
  let ddecl = {
    freeze_function = dyn_freeze;
    unfreeze_function = dyn_unfreeze;
    init_function = dyn_init} 
  in
  if Hashtbl.mem summaries sumname then
    anomalylabstrm "Summary.declare_summary"
      [< 'sTR "Cannot declare a summary twice: " ; 'sTR sumname >];
  Hashtbl.add summaries sumname ddecl

type frozen = Dyn.t Stringmap.t

let freeze_summaries () =
  let m = ref Stringmap.empty in
  Hashtbl.iter 
    (fun id decl -> m := Stringmap.add id (decl.freeze_function()) !m)
    summaries;
  !m

let unfreeze_summaries fs =
  Hashtbl.iter
    (fun id decl -> 
       try decl.unfreeze_function (Stringmap.find id fs)
       with Not_found -> decl.init_function())
    summaries

let init_summaries () =
  Hashtbl.iter (fun _ decl -> decl.init_function()) summaries
