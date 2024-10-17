(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Genarg
open Geninterp

(* We register printers at two levels:
   - generic arguments for general printers
   - generic values for printing ltac values *)

(* Printing generic values *)

type 'a with_level =
  { default_already_surrounded : Constrexpr.entry_relative_level;
    default_ensure_surrounded : Constrexpr.entry_relative_level;
    printer : 'a }

type printer_result =
| PrinterBasic of (Environ.env -> Evd.evar_map -> Pp.t)
| PrinterNeedsLevel of (Environ.env -> Evd.evar_map -> Constrexpr.entry_relative_level -> Pp.t) with_level

type printer_fun_with_level = Environ.env -> Evd.evar_map -> Constrexpr.entry_relative_level -> Pp.t

type top_printer_result =
| TopPrinterBasic of (unit -> Pp.t)
| TopPrinterNeedsContext of (Environ.env -> Evd.evar_map -> Pp.t)
| TopPrinterNeedsContextAndLevel of printer_fun_with_level with_level

type 'a printer = 'a -> printer_result

type 'a top_printer = 'a -> top_printer_result

module ValMap = ValTMap (struct type 'a t = 'a -> top_printer_result end)

let print0_val_map = ref ValMap.empty

let find_print_val_fun tag v =
  match ValMap.find tag !print0_val_map with
  | f -> f v
  | exception Not_found ->
    (* opening Pp shadows "tag" *)
    let the_tag = tag in
    TopPrinterBasic Pp.(fun () -> str "<no printer for " ++ str (Val.repr the_tag) ++ str ">")

let generic_val_print v =
  let Val.Dyn (tag,v) = v in
  find_print_val_fun tag v

let register_val_print0 s pr =
  print0_val_map := ValMap.add s pr !print0_val_map

let combine_dont_needs pr_pair pr1 = function
  | TopPrinterBasic pr2 ->
     TopPrinterBasic (fun () -> pr_pair (pr1 ()) (pr2 ()))
  | TopPrinterNeedsContext pr2 ->
     TopPrinterNeedsContext (fun env sigma ->
         pr_pair (pr1 ()) (pr2 env sigma))
  | TopPrinterNeedsContextAndLevel { default_ensure_surrounded; printer } ->
     TopPrinterNeedsContext (fun env sigma ->
         pr_pair (pr1 ()) (printer env sigma default_ensure_surrounded))

let combine_needs pr_pair pr1 = function
  | TopPrinterBasic pr2 ->
     TopPrinterNeedsContext (fun env sigma -> pr_pair (pr1 env sigma) (pr2 ()))
  | TopPrinterNeedsContext pr2 ->
     TopPrinterNeedsContext (fun env sigma ->
         pr_pair (pr1 env sigma) (pr2 env sigma))
  | TopPrinterNeedsContextAndLevel { default_ensure_surrounded; printer } ->
     TopPrinterNeedsContext (fun env sigma ->
         pr_pair (pr1 env sigma) (printer env sigma default_ensure_surrounded))

let combine pr_pair pr1 v2 =
  match pr1 with
  | TopPrinterBasic pr1 ->
     combine_dont_needs pr_pair pr1 (generic_val_print v2)
  | TopPrinterNeedsContext pr1 ->
     combine_needs pr_pair pr1 (generic_val_print v2)
  | TopPrinterNeedsContextAndLevel { default_ensure_surrounded; printer } ->
     combine_needs pr_pair (fun env sigma -> printer env sigma default_ensure_surrounded)
       (generic_val_print v2)

let _ =
  let pr_cons a b = Pp.(a ++ spc () ++ b) in
  register_val_print0 Val.typ_list
    (function
     | [] -> TopPrinterBasic mt
     | a::l ->
        List.fold_left (combine pr_cons) (generic_val_print a) l)

let _ =
  register_val_print0 Val.typ_opt
    (function
     | None -> TopPrinterBasic Pp.mt
     | Some v -> generic_val_print v)

let _ =
  let pr_pair a b = Pp.(a ++ spc () ++ b) in
  register_val_print0 Val.typ_pair
    (fun (v1,v2) -> combine pr_pair (generic_val_print v1) v2)

(* Printing generic arguments *)

type ('raw, 'glb, 'top) genprinter = {
  raw : 'raw -> printer_result;
  glb : 'glb -> printer_result;
  top : 'top -> top_printer_result;
}

module PrintObj =
struct
  type ('raw, 'glb, 'top) obj = ('raw, 'glb, 'top) genprinter
  let name = "printer"
  let default tag =
    let name = try ArgT.repr tag with Assert_failure _ when !Flags.in_debugger -> "UNKNOWN" in
    let printer = {
      raw = (fun _ -> PrinterBasic (fun env sigma -> str "<genarg:" ++ str name ++ str ">"));
      glb = (fun _ -> PrinterBasic (fun env sigma -> str "<genarg:" ++ str name ++ str ">"));
      top = (fun _ -> TopPrinterBasic (fun () -> str "<genarg:" ++ str name ++ str ">"));
    } in
    Some printer
end

module Print = Register (PrintObj)

let register_print0 wit raw glb top =
  let printer = { raw; glb; top; } in
  Print.register0 wit printer;
  match val_tag (Topwit wit), wit with
  | Val.Base t, ExtraArg t' when Geninterp.Val.repr t = ArgT.repr t' ->
     register_val_print0 t top
  | _ ->
     (* An alias, thus no primitive printer attached *)
     ()

let register_noval_print0 wit raw glb =
  let top = Util.Empty.abort in
  let printer = { raw; glb; top; } in
  Print.register0 wit printer

let register_vernac_print0 wit raw =
  let glb = Util.Empty.abort in
  let top = Util.Empty.abort in
  let printer = { raw; glb; top; } in
  Print.register0 wit printer

let raw_print wit v = (Print.obj wit).raw v
let glb_print wit v = (Print.obj wit).glb v
let top_print wit v = (Print.obj wit).top v

let generic_raw_print (GenArg (Rawwit w, v)) = raw_print w v
let generic_glb_print (GenArg (Glbwit w, v)) = glb_print w v
let generic_top_print (GenArg (Topwit w, v)) = top_print w v
