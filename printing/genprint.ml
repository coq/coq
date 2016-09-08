(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Genarg

type 'a printer = 'a -> std_ppcmds

type ('raw, 'glb, 'top) genprinter = {
  raw : 'raw printer;
  glb : 'glb printer;
  top : 'top printer;
}

module PrintObj =
struct
  type ('raw, 'glb, 'top) obj = ('raw, 'glb, 'top) genprinter
  let name = "printer"
  let default wit = match wit with
  | ExtraArg tag ->
    let name = ArgT.repr tag in
    let printer = {
      raw = (fun _ -> str "<genarg:" ++ str name ++ str ">");
      glb = (fun _ -> str "<genarg:" ++ str name ++ str ">");
      top = (fun _ -> str "<genarg:" ++ str name ++ str ">");
    } in
    Some printer
  | _ -> assert false
end

module Print = Register (PrintObj)

let register_print0 wit raw glb top =
  let printer = { raw; glb; top; } in
  Print.register0 wit printer

let raw_print wit v = (Print.obj wit).raw v
let glb_print wit v = (Print.obj wit).glb v
let top_print wit v = (Print.obj wit).top v

let generic_raw_print (GenArg (Rawwit w, v)) = raw_print w v
let generic_glb_print (GenArg (Glbwit w, v)) = glb_print w v
let generic_top_print (GenArg (Topwit w, v)) = top_print w v
