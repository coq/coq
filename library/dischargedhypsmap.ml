(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Libnames
open Names
open Term
open Reduction
open Declarations
open Environ
open Inductive
open Libobject
open Lib
open Nametab

type discharged_hyps = section_path list

let discharged_hyps_map = ref Spmap.empty

let cache_discharged_hyps_map (_,(sp,hyps)) = 
  discharged_hyps_map := Spmap.add sp hyps !discharged_hyps_map

let (in_discharged_hyps_map, _) =
  declare_object { (default_object "DISCHARGED-HYPS-MAP") with
    cache_function = cache_discharged_hyps_map;
    load_function = (fun _ -> cache_discharged_hyps_map);
    export_function = (fun x -> Some x) }

let set_discharged_hyps sp hyps =
 add_anonymous_leaf (in_discharged_hyps_map (sp,hyps))

let get_discharged_hyps sp =
  try
   Spmap.find sp !discharged_hyps_map
  with Not_found ->
   anomaly ("No discharged hypothesis for object " ^ string_of_path sp)

(*s Registration as global tables and rollback. *)

let init () =
  discharged_hyps_map := Spmap.empty

let freeze () = !discharged_hyps_map

let unfreeze dhm = discharged_hyps_map := dhm

let _ = 
  Summary.declare_summary "discharged_hypothesis"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_module = false;
      Summary.survive_section = true }
