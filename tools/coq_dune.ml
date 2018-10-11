(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* LICENSE NOTE: This file is dually MIT/LGPL 2.1+ licensed. MIT license:
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *)

(* coq_dune: generate dune build rules for .vo files                    *)
(*                                                                      *)
(* At some point this file will become a Dune plugin, so it is very     *)
(* important that this file can be bootstrapped with:                   *)
(*                                                                      *)
(* ocamlfind ocamlopt -linkpkg -package str coq_dune.ml -o coq_dune     *)

open Format

(* Keeping this file self-contained as it is a "bootstrap" utility *)
(* Is OCaml missing these basic functions in the stdlib?           *)
module Aux = struct

  let option_iter f o = match o with
    | Some x -> f x
    | None -> ()

  let option_cata d f o = match o with
    | Some x -> f x
    | None -> d

  let list_compare f = let rec lc x y = match x, y with
      | [], [] -> 0
      | [], _ -> -1
      | _, [] -> 1
      | x::xs, y::ys -> let r = f x y in if r = 0 then lc xs ys else r
    in lc

  let rec pp_list pp sep fmt l = match l with
    | []  -> ()
    | [l] -> fprintf fmt "%a" pp l
    | x::xs -> fprintf fmt "%a%a%a" pp x sep () (pp_list pp sep) xs

  let rec pmap f l = match l with
    | []  -> []
    | x :: xs ->
      begin match f x with
        | None -> pmap f xs
        | Some r -> r :: pmap f xs
      end

  let sep fmt () = fprintf fmt "@;"

  module DirOrd = struct
    type t = string list
    let compare = list_compare String.compare
  end

  module DirMap = Map.Make(DirOrd)

  (* Functions available in newer OCaml versions *)
  (* Taken from the OCaml std library (c) INRIA / LGPL-2.1 *)
  module Legacy = struct

    (* Slower version of DirMap.update, waiting for OCaml 4.06.0 *)
    let dirmap_update key f map =
      match begin
        try f (Some (DirMap.find key map))
        with Not_found -> f None
      end with
      | None   -> DirMap.remove key map
      | Some x -> DirMap.add key x map

  end

  let add_map_list key elem map =
    (* Move to Dirmap.update once we require OCaml >= 4.06.0 *)
    Legacy.dirmap_update key (fun l -> Some (option_cata [elem] (fun ll -> elem :: ll) l)) map

end

open Aux

(* Once this is a Dune plugin the flags will be taken from the env *)
module Options = struct

  type flag = {
    enabled : bool;
    cmd : string;
  }

  let all_opts =
  [ { enabled = false; cmd = "-debug"; }
  ; { enabled = false; cmd = "-native_compiler"; }
  ]

  let build_coq_flags () =
    let popt o = if o.enabled then Some o.cmd else None in
    String.concat " " @@ pmap popt all_opts
end

type vodep = {
  target: string;
  deps : string list;
}

type ldep = | VO of vodep | ML4 of string | MLG of string
type ddir = ldep list DirMap.t

(* Filter `.vio` etc... *)
let filter_no_vo =
  List.filter (fun f -> Filename.check_suffix f ".vo")

(* We could have coqdep to output dune files directly *)

(* Fix once we move to OCaml >= 4.06.0 *)
let list_init len f =
  let rec init_aux i n f =
    if i >= n then []
    else let r = f i in r :: init_aux (i+1) n f
  in init_aux 0 len f

let gen_sub n =
  (* Move to List.init once we can depend on OCaml >= 4.06.0 *)
  String.concat "/" (list_init n (fun _ -> "..")) ^ "/"

let pp_rule fmt targets deps action =
  (* Special printing of the first rule *)
  let ppl = pp_list pp_print_string sep in
  let pp_deps fmt l = match l with
    | [] ->
      ()
    | x :: xs ->
      fprintf fmt "(:pp-file %s)%a" x sep ();
      pp_list pp_print_string sep fmt xs
  in
  fprintf fmt
    "@[(rule@\n @[(targets @[%a@])@\n(deps @[%a@])@\n(action @[%a@])@])@]@\n"
    ppl targets pp_deps deps pp_print_string action

(* Generate the dune rule: *)
let pp_vo_dep dir fmt vo =
  let depth = List.length dir in
  let sdir = gen_sub depth in
  (* All files except those in Init implicitly depend on the Prelude, we account for it here. *)
  let eflag, edep = if List.tl dir = ["Init"] then "-noinit -R theories Coq", [] else "", ["theories/Init/Prelude.vo"] in
  (* Coq flags *)
  let cflag = Options.build_coq_flags () in
  (* Correct path from global to local "theories/Init/Decimal.vo" -> "../../theories/Init/Decimal.vo" *)
  let deps = List.map (fun s -> sdir ^ s) (edep @ vo.deps) in
  (* The source file is also corrected as we will call coqtop from the top dir *)
  let source = String.concat "/" dir ^ "/" ^ Filename.(remove_extension vo.target) ^ ".v" in
  (* The final build rule *)
  let action = sprintf "(chdir %%{project_root} (run coqtop -boot %s %s -compile %s))" eflag cflag source in
  pp_rule fmt [vo.target] deps action

let pp_ml4_dep _dir fmt ml =
  let target = Filename.(remove_extension ml) ^ ".ml" in
  let ml4_rule = "(run coqp5 -loc loc -impl %{pp-file} -o %{targets})" in
  pp_rule fmt [target] [ml] ml4_rule

let pp_mlg_dep _dir fmt ml =
  let target = Filename.(remove_extension ml) ^ ".ml" in
  let ml4_rule = "(run coqpp %{pp-file})" in
  pp_rule fmt [target] [ml] ml4_rule

let pp_dep dir fmt oo = match oo with
  | VO vo -> pp_vo_dep dir fmt vo
  | ML4 f -> pp_ml4_dep dir fmt f
  | MLG f -> pp_mlg_dep dir fmt f

let out_install fmt dir ff =
  let itarget = String.concat "/" dir in
  let ff = pmap (function | VO vo -> Some vo.target | _ -> None) ff in
  let pp_ispec fmt tg = fprintf fmt "(%s as %s)" tg (itarget^"/"^tg) in
  fprintf fmt "(install@\n @[(section lib)@\n(package coq)@\n(files @[%a@])@])@\n"
    (pp_list pp_ispec sep) ff

(* For each directory, we must record two things, the build rules and
   the install specification. *)
let record_dune d ff =
  let sd = String.concat "/" d in
  if Sys.file_exists sd && Sys.is_directory sd then
    let out = open_out (sd^"/dune") in
    let fmt = formatter_of_out_channel out in
    if List.nth d 0 = "plugins" then
      fprintf fmt "(include plugin_base.dune)@\n";
    out_install fmt d ff;
    List.iter (pp_dep d fmt) ff;
    fprintf fmt "%!";
    close_out out
  else
    eprintf "error in coq_dune, a directory disappeared: %s@\n%!" sd

(* File Scanning *)
let choose_ml4g_form f =
  if Filename.check_suffix f ".ml4" then ML4 f
  else MLG f

let scan_mlg4 m d =
  let dir = ["plugins"; d] in
  let m = DirMap.add dir [] m in
  let ml4 = Sys.(List.filter (fun f -> Filename.(check_suffix f ".ml4" || check_suffix f ".mlg"))
                   Array.(to_list @@ readdir String.(concat "/" dir))) in
  List.fold_left (fun m f -> add_map_list ["plugins"; d] (choose_ml4g_form f) m) m ml4

let scan_plugins m =
  let is_plugin_directory dir = Sys.(is_directory dir && file_exists (dir ^ "/plugin_base.dune")) in
  let dirs = Sys.(List.filter (fun f -> is_plugin_directory @@ "plugins/"^f) Array.(to_list @@ readdir "plugins/")) in
  List.fold_left scan_mlg4 m dirs

(* Process .vfiles.d and generate a skeleton for the dune file *)
let parse_coqdep_line l =
  match Str.(split (regexp ":") l) with
  | [targets;deps] ->
    let targets = Str.(split (regexp "[ \t]+") targets) in
    let deps    = Str.(split (regexp "[ \t]+") deps)    in
    let targets = filter_no_vo targets in
    begin match targets with
    | [target] ->
      let dir, target = Filename.(dirname target, basename target) in
      Some (String.split_on_char '/' dir, VO { target; deps; })
    (* Otherwise a vio file, we ignore *)
    | _ -> None
    end
  (* Strange rule, we ignore *)
  | _ -> None

let rec read_vfiles ic map =
  try
    let rule = parse_coqdep_line (input_line ic) in
    (* Add vo_entry to its corresponding map entry *)
    let map = option_cata map (fun (dir, vo) -> add_map_list dir vo map) rule in
    read_vfiles ic map
  with End_of_file -> map

let out_map map =
  DirMap.iter record_dune map

let exec_ifile f =
  match Array.length Sys.argv with
  | 1 -> f stdin
  | 2 ->
    let ic = open_in Sys.argv.(1) in
    (try f ic with _ -> close_in ic)
  | _ -> eprintf "Error: wrong number of arguments@\n%!"; exit 1

let _ =
  exec_ifile (fun ic ->
      let map = scan_plugins DirMap.empty in
      let map = read_vfiles ic map in
      out_map map)
