(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util

type 'a summary_declaration = {
  freeze_function : unit -> 'a;
  unfreeze_function : 'a -> unit;
  init_function : unit -> unit;
  survive_module : bool ;
  survive_section : bool }

let summaries = 
  (Hashtbl.create 17 : (string, Dyn.t summary_declaration) Hashtbl.t)

let internal_declare_summary sumname sdecl =
  let (infun,outfun) = Dyn.create sumname in
  let dyn_freeze () = infun (sdecl.freeze_function())
  and dyn_unfreeze sum = sdecl.unfreeze_function (outfun sum)
  and dyn_init = sdecl.init_function in
  let ddecl = {
    freeze_function = dyn_freeze;
    unfreeze_function = dyn_unfreeze;
    init_function = dyn_init;
    survive_module = sdecl.survive_module;
    survive_section = sdecl.survive_section } 
  in
  if Hashtbl.mem summaries sumname then
    anomalylabstrm "Summary.declare_summary"
      (str "Cannot declare a summary twice: " ++ str sumname);
  Hashtbl.add summaries sumname ddecl

let declare_summary sumname decl = 
  internal_declare_summary (sumname^"-SUMMARY") decl

type frozen = Dyn.t Stringmap.t

let freeze_summaries () =
  let m = ref Stringmap.empty in
  Hashtbl.iter 
    (fun id decl -> m := Stringmap.add id (decl.freeze_function()) !m)
    summaries;
  !m


let unfreeze_some_summaries p fs = 
  Hashtbl.iter
    (fun id decl -> 
       try 
	 if p decl then
	   decl.unfreeze_function (Stringmap.find id fs)
       with Not_found -> decl.init_function())
    summaries

let unfreeze_summaries = 
  unfreeze_some_summaries (fun _ -> true)

let section_unfreeze_summaries =
  unfreeze_some_summaries (fun decl -> not decl.survive_section)

let module_unfreeze_summaries =
  unfreeze_some_summaries (fun decl -> not decl.survive_module)

let init_summaries () =
  Hashtbl.iter (fun _ decl -> decl.init_function()) summaries
