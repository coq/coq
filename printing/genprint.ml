(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Genarg

type printer = {
  raw : Obj.t -> std_ppcmds;
  glb : Obj.t -> std_ppcmds;
  top : Obj.t -> std_ppcmds;
}

let default_printer name = (); fun _ -> str "<genarg:" ++ str name ++ str ">"

let default_printer name =
  let pr = default_printer name in
  { raw = pr; glb = pr; top = pr; }

let (arg0_printer_map : printer String.Map.t ref) = ref String.Map.empty

let get_printer0 name =
  try String.Map.find name !arg0_printer_map
  with Not_found -> default_printer name

let obj_printer t = match t with
| ExtraArgType s -> get_printer0 s
| _ -> assert false

let raw_print arg = Obj.magic (obj_printer (unquote (rawwit arg))).raw
let glb_print arg = Obj.magic (obj_printer (unquote (rawwit arg))).glb
let top_print arg = Obj.magic (obj_printer (unquote (rawwit arg))).top

let generic_raw_print v =
  (obj_printer (genarg_tag v)).raw (Unsafe.prj v)
let generic_glb_print v =
  (obj_printer (genarg_tag v)).glb (Unsafe.prj v)
let generic_top_print v =
  (obj_printer (genarg_tag v)).top (Unsafe.prj v)

let register_print0 arg rpr gpr tpr = match unquote (rawwit arg) with
| ExtraArgType s ->
  if String.Map.mem s !arg0_printer_map then
    Errors.anomaly (str "interp0 function already registered: " ++ str s)
  else
    let pr = { raw = Obj.magic rpr; glb = Obj.magic gpr; top = Obj.magic tpr; } in
    arg0_printer_map := String.Map.add s pr !arg0_printer_map
| _ -> assert false
