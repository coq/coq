(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Vernac
open Vernacexpr
open Pfedit
open Pp
open Util
open Names
open Term
open Printer
open Environ
open Evarutil
open Evd
open Hipattern
open Tacmach
open Reductionops
open Termops
open Namegen
open Ideutils
open Compat

type coqtop = {
  mutable cout : in_channel ;
  mutable cin : out_channel ;
  sup_args : string ;
}

let dummy_coqtop = {
  cout = stdin ;
  cin = stdout ;
  sup_args = "" ;
}

let prerr_endline s = if !debug then prerr_endline s else ()

let output = ref (Format.formatter_of_out_channel stdout)

let msg m =
  let b =  Buffer.create 103 in
  Pp.msg_with (Format.formatter_of_buffer b) m;
  Buffer.contents b

let msgnl m =
  (msg m)^"\n"

let i = ref 0

let get_version_date () =
  let date =
    if Glib.Utf8.validate Coq_config.date
    then Coq_config.date
    else "<date not printable>" in
  try
    let ch = open_in (Coq_config.coqsrc^"/revision") in
    let ver = input_line ch in
    let rev = input_line ch in
    (ver,rev)
  with _ -> (Coq_config.version,date)

let short_version () =
  let (ver,date) = get_version_date () in
  Printf.sprintf "The Coq Proof Assistant, version %s (%s)\n" ver date

let version () =
  let (ver,date) = get_version_date () in
    Printf.sprintf
      "The Coq Proof Assistant, version %s (%s)\
       \nArchitecture %s running %s operating system\
       \nGtk version is %s\
       \nThis is the %s version (%s is the best one for this architecture and OS)\
       \n"
      ver date
      Coq_config.arch Sys.os_type
      (let x,y,z = GMain.Main.version in Printf.sprintf "%d.%d.%d" x y z)
    (if Mltop.is_native then "native" else "bytecode")
    (if Coq_config.best="opt" then "native" else "bytecode")

exception Coq_failure of (Util.loc option * string)

let eval_call coqtop (c:'a Ide_blob.call) =
  Safe_marshal.send coqtop.cin c;
  let res = (Safe_marshal.receive: in_channel -> 'a Ide_blob.value) coqtop.cout in
  match res with
    | Ide_blob.Good v -> v
    | Ide_blob.Fail err -> raise (Coq_failure err)

let is_in_loadpath coqtop s = eval_call coqtop (Ide_blob.is_in_loadpath s)
 
let reset_initial = Ide_blob.reinit

let raw_interp coqtop s = eval_call coqtop (Ide_blob.raw_interp s)

let interp coqtop b s = eval_call coqtop (Ide_blob.interp b s)

let rewind coqtop i = eval_call coqtop (Ide_blob.rewind i)
 
let read_stdout coqtop = eval_call coqtop Ide_blob.read_stdout

let spawn_coqtop sup_args =
  let prog = Sys.argv.(0) in
  let dir = Filename.dirname prog in
  let oc,ic = Unix.open_process (dir^"/coqtop.opt -ideslave "^sup_args) in
  { cin = ic; cout = oc ; sup_args = sup_args }

let kill_coqtop coqtop =
  try raw_interp coqtop "Quit." with _ -> ()

let reset_coqtop coqtop =
  kill_coqtop coqtop;
  let ni = spawn_coqtop coqtop.sup_args in
  coqtop.cin <- ni.cin;
  coqtop.cout <- ni.cout

module PrintOpt =
struct
  type t = string list
  let implicit = ["Implicit"]
  let coercions = ["Coercions"]
  let raw_matching = ["Matching";"Synth"]
  let notations = ["Notations"]
  let all_basic = ["All"]
  let existential = ["Existential Instances"]
  let universes = ["Universes"]

  let state_hack = Hashtbl.create 11
  let _ = List.iter (fun opt -> Hashtbl.add state_hack opt false)
            [ implicit; coercions; raw_matching; notations; all_basic; existential; universes ]

  let set coqtop opt value =
    Hashtbl.replace state_hack opt value;
    List.iter
      (fun cmd -> 
         let str = (if value then "Set" else "Unset") ^ " Printing " ^ cmd ^ "." in
         raw_interp coqtop str)
      opt

  let enforce_hack coqtop = Hashtbl.iter (set coqtop) state_hack 
end

let rec is_pervasive_exn = function
  | Out_of_memory | Stack_overflow | Sys.Break -> true
  | Error_in_file (_,_,e) -> is_pervasive_exn e
  | Loc.Exc_located (_,e) -> is_pervasive_exn e
  | DuringCommandInterp (_,e) -> is_pervasive_exn e
  | _ -> false

let print_toplevel_error exc =
  let (dloc,exc) =
    match exc with
      | DuringCommandInterp (loc,ie) ->
          if loc = dummy_loc then (None,ie) else (Some loc, ie)
      | _ -> (None, exc)
  in
  let (loc,exc) =
    match exc with
      | Loc.Exc_located (loc, ie) -> (Some loc),ie
      | Error_in_file (s, (_,fname, loc), ie) -> None, ie
      | _ -> dloc,exc
  in
  match exc with
    | End_of_input  -> 	str "Please report: End of input",None
    | Vernacexpr.Drop ->  str "Drop is not allowed by coqide!",None
    | Vernacexpr.Quit -> str "Quit is not allowed by coqide! Use menus.",None
    | _ ->
	(try Cerrors.explain_exn exc with e ->
	   str "Failed to explain error. This is an internal Coq error. Please report.\n"
	   ++ str (Printexc.to_string  e)),
	(if is_pervasive_exn exc then None else loc)

let process_exn e = let s,loc= print_toplevel_error e in (msgnl s,loc)

type tried_tactic =
  | Interrupted
  | Success of int (* nb of goals after *)
  | Failed

let goals coqtop =
  PrintOpt.enforce_hack coqtop;
  eval_call coqtop Ide_blob.current_goals

let make_cases coqtop s = eval_call coqtop (Ide_blob.make_cases s)

let current_status coqtop = eval_call coqtop Ide_blob.current_status
