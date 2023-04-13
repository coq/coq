(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let die fmt = Printf.kfprintf (fun _ -> exit 1) stderr fmt

let colors = [|"#F08080"; "#EEE8AA"; "#98FB98"|]

let usage () = die "Usage: %s VFILE TIMEFILES\n\n%a\n" Sys.argv.(0)
    (fun fmt len -> Printf.fprintf fmt "(Only up to %d time files are supported.)" len)
    (Array.length colors)

let () = if Array.length Sys.argv < 3 ||
            Array.length Sys.argv > 2 + Array.length colors
  then  usage ()

module Compat = struct

  (* stdlib version needs ocaml >= 4.13 *)
  let str_fold_left f x a =
    let open String in
    let r = ref x in
    for i = 0 to length a - 1 do
      r := f !r (unsafe_get a i)
    done;
    !r

  (* stdlib version needs ocaml >= 4.13 *)
  let str_for_all p s =
    let open String in
    let n = length s in
    let rec loop i =
      if i = n then true
      else if p (unsafe_get s i) then loop (succ i)
      else false in
    loop 0

end
open Compat

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

let source_substring start stop =
  (* substring from start to stop inclusive, both 1-based *)
  (* start=0 is the same as start=1 *)
  let start = if start = 0 then 1 else start in
  let len = stop - start + 1 (* +1 for inclusive *) in
  String.sub source (start-1) len

type loc = { start: int; stop: int; line: int; text: string; }

(* [line] and [text] are derived data using the same [source] so no need to check them *)
let same_loc a b = a.start = b.start && a.stop = b.stop

(* A measurement, with the original printed string and an exact rational representation *)
type measure = { str: string; q: Q.t; }

let dummy = { str="0"; q=Q.zero; }

type 'a one_command = {
  loc: loc;
  time: 'a;
}

let time_regex = Str.regexp {|^Chars \([0-9]+\) - \([0-9]+\) [^ ]+ \([0-9.]+\) secs|}

let count_newlines s = str_fold_left (fun n c -> if c = '\n' then n+1 else n) 0 s

let is_white_char = function ' '|'\n'|'\t' -> true | _ -> false

(* Set to true when benching with Coq versions that don't output the header / end timing *)
let bench_with_old_version = false

let is_start_end_header l =
  Str.(string_match (regexp "Comments~\"Document Start\"") l 0)
  || Str.(string_match (regexp "Comments~\"Document End\"") l 0)

let rec file_loop filech ~last_end ~lines acc : measure one_command array =
  match input_line filech with
  | exception End_of_file ->
    let acc = if last_end + 1 <= sourcelen then
        let text = source_substring (last_end+1) sourcelen in
        if str_for_all is_white_char text then acc
        else
          { loc = { start = last_end+1; stop = sourcelen; line = lines+1; text; };
            time = dummy;
          } :: acc
      else acc
    in
    CArray.rev_of_list acc
  | l ->
    if bench_with_old_version && is_start_end_header l then
      file_loop filech ~last_end ~lines acc
    else
    if not (Str.string_match time_regex l 0) then
      file_loop filech ~last_end ~lines acc
    else
      let b = int_of_string @@ Str.matched_group 1 l
      and e = int_of_string @@ Str.matched_group 2 l
      and t = Str.matched_group 3 l in
      let acc, lines, last_end = if b > last_end + 1 then
          let text = source_substring (last_end + 1) (b - 1) in
          (* if only spaces since last command, include them in the next command
             typically "Module Foo.\n  Cmd." *)
          if not (str_for_all is_white_char text) then
            let n = count_newlines text in
            let acc =
              { loc = { start = last_end + 1; stop = b-1; line = lines; text };
                time = dummy;
              } :: acc
            in
            acc, (lines+n), b-1
          else acc, lines, last_end
        else acc, lines, last_end
      in
      let text = source_substring (last_end+1) e in
      let lines, n = if text <> "" && text.[0] = '\n' then lines+1, 1 else lines, 0 in
      let n = count_newlines text - n in
      (* lua script has "eoln" but unused *)
      let acc =
        { loc = { start = last_end+1; stop = e; line = lines; text; };
          time = { str=t; q = Q.of_string t; };
        } :: acc
      in
      let lines = lines + n in
      let last_end = e in
      file_loop filech ~last_end ~lines acc

let file_data data_file =
  file_loop (open_in data_file) ~last_end:(-1) ~lines:1 []

let all_data = Array.map file_data data_files

let () =
  data_files |> Array.iteri (fun fidx fname ->
      if Array.length all_data.(0) <> Array.length all_data.(fidx)
      then die "Mismatch between %s and %s: different measurement counts\n" data_files.(0) fname)

let all_data : measure array one_command array =
  all_data.(0) |> Array.mapi (fun i d ->
      let times = data_files |> Array.mapi (fun fidx fname ->
          let fdata = all_data.(fidx).(i) in
          if same_loc d.loc fdata.loc
          then fdata.time
          else die "Mismatch between %s and %s at line %d\n" data_files.(0) fname (i+1))
      in
      { loc = d.loc;
        time = times; })

let percentage ~max:m v =
  Q.to_float Q.(v * of_int 100 / m)

let maxq =
  Array.fold_left (fun max data ->
      Array.fold_left (fun max d ->
          let dq = d.q in
          if Q.lt max dq then dq
          else max)
        max
        data.time)
    Q.zero all_data

let vname = Filename.basename vfile

let out fmt = Printf.kfprintf (fun _ -> ()) stdout fmt

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

let () = all_data |> Array.iteri (fun j d ->
    let () = out {|<div class="code" title="File: %s
Line: %d

|} vname d.loc.line
    in
    let () = d.time |> Array.iteri (fun k d ->
        out "Time%d: %ss\n" (k+1) d.str)
    in
    let () = out {|">|} in

    let () = d.time |> Array.iteri (fun k d ->
        out {|<div class="time%d" style="width: %f%%"></div>|}
          (k+1)
          (percentage d.q ~max:maxq))
    in

    let text = d.loc.text in
    let text = if text <> "" && text.[0] = '\n'
      then String.sub text 1 (String.length text  - 1)
      else text
    in
    let sublines = String.split_on_char '\n' text in
    let () = sublines |> List.iteri (fun i line ->
        out "<code data-line=\"%d\">%s</code>\n" (d.loc.line+i) (htmlescape line))
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
