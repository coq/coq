(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
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

  (* Creation of paths, aware of the platform separator. *)
  let bpath l = String.concat Filename.dir_sep l

  module DirOrd = struct
    type t = string list
    let compare = list_compare String.compare
  end

  module DirMap = Map.Make(DirOrd)

  (* Functions available in newer OCaml versions *)
  (* Taken from the OCaml std library (c) INRIA / LGPL-2.1 *)
  module Legacy = struct


    (* Fix once we move to OCaml >= 4.06.0 *)
    let list_init len f =
      let rec init_aux i n f =
        if i >= n then []
        else let r = f i in r :: init_aux (i+1) n f
      in init_aux 0 len f

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

  let replace_ext ~file ~newext =
    Filename.(remove_extension file) ^ newext

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
  ; { enabled = true; cmd = "-allow-sprop"; }
  ; { enabled = true; cmd = "-w +default"; }
  ]

  let build_coq_flags () =
    let popt o = if o.enabled then Some o.cmd else None in
    String.concat " " @@ pmap popt all_opts
end

type vodep = {
  target: string;
  deps : string list;
}

type ldep = | VO of vodep | MLG of string
type ddir = ldep list DirMap.t

(* Filter `.vio` etc... *)
let filter_no_vo =
  List.filter (fun f -> Filename.check_suffix f ".vo")

(* We could have coqdep to output dune files directly *)

let gen_sub n =
  (* Move to List.init once we can depend on OCaml >= 4.06.0 *)
  bpath @@ Legacy.list_init n (fun _ -> "..")

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

let gen_coqc_targets vo =
  [ vo.target
  ; replace_ext ~file:vo.target ~newext:".glob"
  ; "." ^ replace_ext ~file:vo.target ~newext:".aux"]

(* Generate the dune rule: *)
let pp_vo_dep dir fmt vo =
  let depth = List.length dir in
  let sdir = gen_sub depth in
  (* All files except those in Init implicitly depend on the Prelude, we account for it here. *)
  let eflag, edep = if List.tl dir = ["Init"] then "-noinit -R theories Coq", [] else "", [bpath ["theories";"Init";"Prelude.vo"]] in
  (* Coq flags *)
  let cflag = Options.build_coq_flags () in
  (* Correct path from global to local "theories/Init/Decimal.vo" -> "../../theories/Init/Decimal.vo" *)
  let deps = List.map (fun s -> bpath [sdir;s]) (edep @ vo.deps) in
  (* The source file is also corrected as we will call coqtop from the top dir *)
  let source = bpath (dir @ [replace_ext ~file:vo.target ~newext:".v"]) in
  (* We explicitly include the location of coqlib to avoid tricky issues with coqlib location *)
  let libflag = "-coqlib %{project_root}" in
  (* The final build rule *)
  let action = sprintf "(chdir %%{project_root} (run coqc -q %s %s %s %s))" libflag eflag cflag source in
  let all_targets = gen_coqc_targets vo in
  pp_rule fmt all_targets deps action

let pp_mlg_dep _dir fmt ml =
  let target = Filename.(remove_extension ml) ^ ".ml" in
  let mlg_rule = "(run coqpp %{pp-file})" in
  pp_rule fmt [target] [ml] mlg_rule

let pp_dep dir fmt oo = match oo with
  | VO vo -> pp_vo_dep dir fmt vo
  | MLG f -> pp_mlg_dep dir fmt f

let out_install fmt dir ff =
  let itarget = String.concat "/" dir in
  let ff = List.concat @@ pmap (function | VO vo -> Some (gen_coqc_targets vo) | _ -> None) ff in
  let pp_ispec fmt tg = fprintf fmt "(%s as coq/%s)" tg (bpath [itarget;tg]) in
  fprintf fmt "(install@\n @[(section lib_root)@\n(package coq)@\n(files @[%a@])@])@\n"
    (pp_list pp_ispec sep) ff

(* For each directory, we must record two things, the build rules and
   the install specification. *)
let record_dune d ff =
  let sd = bpath d in
  if Sys.file_exists sd && Sys.is_directory sd then
    let out = open_out (bpath [sd;"dune"]) in
    let fmt = formatter_of_out_channel out in
    if List.nth d 0 = "plugins" || List.nth d 0 = "user-contrib" then
      fprintf fmt "(include plugin_base.dune)@\n";
    out_install fmt d ff;
    List.iter (pp_dep d fmt) ff;
    fprintf fmt "%!";
    close_out out
  else
    eprintf "error in coq_dune, a directory disappeared: %s@\n%!" sd

(* File Scanning *)
let scan_mlg ~root m d =
  let dir = [root; d] in
  let m = DirMap.add dir [] m in
  let mlg = Sys.(List.filter (fun f -> Filename.(check_suffix f ".mlg"))
                   Array.(to_list @@ readdir (bpath dir))) in
  List.fold_left (fun m f -> add_map_list [root; d] (MLG f) m) m mlg

let scan_dir ~root m =
  let is_plugin_directory dir = Sys.(is_directory dir && file_exists (bpath [dir;"plugin_base.dune"])) in
  let dirs = Sys.(List.filter (fun f -> is_plugin_directory @@ bpath [root;f]) Array.(to_list @@ readdir root)) in
  List.fold_left (scan_mlg ~root) m dirs

let scan_plugins m = scan_dir ~root:"plugins" m
let scan_usercontrib m = scan_dir ~root:"user-contrib" m

(* This will be removed when we drop support for Make *)
let fix_cmo_cma file =
  if String.equal Filename.(extension file) ".cmo"
  then replace_ext ~file ~newext:".cma"
  else file

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
      (* coqdep outputs with the '/' directory separator regardless of
         the platform. Anyways, I hope we can link to coqdep instead
         of having to parse its output soon, that should solve this
         kind of issues *)
      let deps = List.map fix_cmo_cma deps in
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
    let in_file = Sys.argv.(1) in
    begin try
      let ic = open_in in_file in
      (try f ic
       with _ -> eprintf "Error: exec_ifile@\n%!"; close_in ic)
      with _ -> eprintf "Error: cannot open input file %s@\n%!" in_file
    end
  | _ -> eprintf "Error: wrong number of arguments@\n%!"; exit 1

let _ =
  exec_ifile (fun ic ->
      let map = scan_plugins DirMap.empty in
      let map = scan_usercontrib map in
      let map = read_vfiles ic map in
      out_map map)
