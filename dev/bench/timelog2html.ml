(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Benchlib

let die fmt = Printf.kfprintf (fun _ -> exit 1) stderr fmt

let colors = [|"#F08080"; "#EEE8AA"; "#98FB98"|]

let usage () = die "Usage: %s VFILE TIMEFILES\n\n%a\n" Sys.argv.(0)
    (fun fmt len -> Printf.fprintf fmt "(Only up to %d time files are supported.)" len)
    (Array.length colors)

let () = if Array.length Sys.argv < 3 ||
            Array.length Sys.argv > 2 + Array.length colors
  then  usage ()

let vfile = Sys.argv.(1)
let data_files = Array.sub Sys.argv 2 (Array.length Sys.argv - 2)
let ndata = Array.length data_files

let htmlescape =
  let r = Str.regexp "[&<>\"]" in
  let subst s = match Str.matched_string s with
    | "&" -> "&amp;"
    | "<" -> "&lt;"
    | ">" -> "&gt;"
    | "\"" -> "&quot;"
    | _ -> assert false
  in
  fun s -> Str.global_substitute r subst s

let sourcelen = (Unix.stat vfile).st_size
let source =
  let ch = try open_in vfile with Sys_error e -> die "Could not open %s: %s" vfile e in
  let s = really_input_string ch sourcelen in
  close_in ch;
  s

(* A measurement, with the original printed string and an exact rational representation *)
type measure = { str: string; q: Q.t; }

let dummy = { str="0"; q=Q.zero; }

type 'a one_command = BenchUtil.source_loc * 'a

let file_data data_file =
  let data = Timelogparser.parse ~file:data_file in
  let data = data |> List.map (fun (loc,{Timelogparser.timestr}) ->
      loc, { str = timestr; q = Q.of_string timestr })
  in
  (* XXX should we join_to_source after combine_related_data? *)
  let data = Sourcehandler.join_to_source ~dummy ~source data in
  data_file, CArray.of_list data

let all_data = Array.map file_data data_files

let all_data : measure array one_command array =
  BenchUtil.combine_related_data all_data

let percentage ~max:m v =
  Q.to_float Q.(v * of_int 100 / m)

let maxq =
  Array.fold_left (fun max (_,data) ->
      Array.fold_left (fun max d ->
          let dq = d.q in
          if Q.lt max dq then dq
          else max)
        max
        data)
    Q.zero all_data

let vname = Filename.basename vfile

let out fmt = Printf.fprintf stdout fmt

let () =
  out
{|<html>
<head>
<title>%s</title>
<style>
|} vname

(* NB: lua "ipairs" is 1-based, ocaml "iteri" is 0-based *)
let () = data_files |> Array.iteri (fun i _ ->
    let color = colors.(i) in
    out
{|.time%d {
  background-color: %s;
  height: %d%%;
  top: %d%%;
  z-index: -1;
  position: absolute;
  opacity: 50%%;
}
|} (i+1) color (100 / ndata) (100 / ndata * i))

let () =
  out
{|.code {
  z-index: 0;
  position: relative;
  border-style: solid;
  border-color: transparent;
  border-width: 1px;
}
.code:hover {
  border-color: black;
}
code::before {
    content:  attr(data-line);
    right: 0.5em;
    position: absolute;
    text-align: right;
}
</style>
</head>
<body>
|}

let () = out "<h1>Timings for %s</h1>\n" vname

let () = out "<ol>\n"

let () = data_files |> Array.iteri (fun i data_file ->
    out "<li style=\"background-color: %s\">%s</li>\n" colors.(i) data_file)

let () = out "</ol>\n"

let () = out "<pre>"

let last_seen_line = ref 0

let line_id fmt l =
  if l > !last_seen_line then begin
    last_seen_line := l;
    Printf.fprintf fmt "id=\"L%d\" " l
  end


let () = all_data |> Array.iteri (fun j ((loc:BenchUtil.source_loc),time) ->
    let () = out {|<div class="code" title="File: %s
Line: %d

|} vname loc.line
    in
    let () = time |> Array.iteri (fun k d ->
        out "Time%d: %ss\n" (k+1) d.str)
    in
    let () = out {|">|} in

    let () = time |> Array.iteri (fun k d ->
        out {|<div class="time%d" style="width: %f%%"></div>|}
          (k+1)
          (percentage d.q ~max:maxq))
    in

    let text = loc.text in
    let text = if text <> "" && text.[0] = '\n'
      then String.sub text 1 (String.length text  - 1)
      else text
    in
    let sublines = String.split_on_char '\n' text in
    let () = sublines |> List.iteri (fun i line ->
        let lnum = loc.line + i in
        out "<code %adata-line=\"%d\">%s</code>\n" line_id lnum lnum (htmlescape line))
    in

    let () = out "</div>" in
    ())

let () =
  out
{|
</pre>

</body>
</html>
|}
