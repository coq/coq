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

type measures = {
  time: measure;
  major: measure option;
  minor: measure option;
}

let measure_of_string s = { str=s; q = Q.of_string s; }

let dummy = { str="0"; q=Q.zero; }

let dummys = { time=dummy; major=None; minor=None; }

type 'a one_command = {
  loc: loc;
  measures: 'a;
}

let time_regex = Str.regexp {|^Chars \([0-9]+\) - \([0-9]+\) [^ ]+ \([0-9.]+\) secs [^ ]+\( \([0-9.]+\) major Mw, \([0-9.]+\) minor Mw\)?|}

let count_newlines s = str_fold_left (fun n c -> if c = '\n' then n+1 else n) 0 s

let is_white_char = function ' '|'\n'|'\t' -> true | _ -> false

let rec file_loop filech ~last_end ~lines acc : measures one_command array =
  match input_line filech with
  | exception End_of_file ->
    let acc = if last_end + 1 <= sourcelen then
        let text = source_substring (last_end+1) sourcelen in
        if str_for_all is_white_char text then acc
        else
          { loc = { start = last_end+1; stop = sourcelen; line = lines+1; text; };
            measures = dummys;
          } :: acc
      else acc
    in
    CArray.rev_of_list acc
  | l ->
    if not (Str.string_match time_regex l 0) then
      file_loop filech ~last_end ~lines acc
    else
      let b = int_of_string @@ Str.matched_group 1 l
      and e = int_of_string @@ Str.matched_group 2 l
      and t = Str.matched_group 3 l
      and major = try Some (Str.matched_group 5 l) with Not_found -> None
      and minor = try Some (Str.matched_group 6 l) with Not_found -> None in
      let acc, lines, last_end = if b > last_end + 1 then
          let text = source_substring (last_end + 1) (b - 1) in
          (* if only spaces since last command, include them in the next command
             typically "Module Foo.\n  Cmd." *)
          if not (str_for_all is_white_char text) then
            let n = count_newlines text in
            let acc =
              { loc = { start = last_end + 1; stop = b-1; line = lines; text };
                measures = dummys;
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
          measures = {
            time = measure_of_string t;
            major = Option.map measure_of_string major;
            minor = Option.map measure_of_string minor;};
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

let all_data : measures array one_command array =
  all_data.(0) |> Array.mapi (fun i d ->
      let measures = data_files |> Array.mapi (fun fidx fname ->
          let fdata = all_data.(fidx).(i) in
          if same_loc d.loc fdata.loc
          then fdata.measures
          else die "Mismatch between %s and %s at line %d\n" data_files.(0) fname (i+1))
      in
      { loc = d.loc;
        measures; })

let percentage ~max:m v =
  Q.to_float Q.(v * of_int 100 / m)

let max_for get all_data =
  Array.fold_left (fun max data ->
      Array.fold_left (fun max d ->
          match get d with
          | None -> max
          | Some dq ->
            if Q.lt max dq then dq
            else max)
        max
        data.measures)
    Q.zero all_data

let timemaxq = max_for (fun d -> Some d.time.q) all_data
let majormaxq = max_for (fun d -> Option.map (fun d -> d.q) d.major) all_data
let minormaxq = max_for (fun d -> Option.map (fun d -> d.q) d.minor) all_data

let has_mem_data =
  Array.exists (fun d -> Array.exists (fun d -> Option.has_some d.major) d.measures)
    all_data

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
{|.time%d, .major%d, .minor%d {
  background-color: %s;
  height: %d%%;
  top: %d%%;
  z-index: -1;
  position: absolute;
  opacity: 0%%;
}
#time:checked ~ * .time%d { opacity: 50%%; }
#major:checked ~ * .major%d { opacity: 50%%; }
#minor:checked ~ * .minor%d { opacity: 50%%; }
|} (i+1) (i+1) (i+1) color (100 / ndata) (100 / ndata * i) (i+1) (i+1) (i+1))

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

let () = if has_mem_data then
    out {|
<input type="radio" name="toggles" checked=true id="time"><label for="time">Time</label>
<input type="radio" name="toggles" id="major"><label for="major">Major</label>
<input type="radio" name="toggles" id="minor"><label for="minor">Minor</label>
|}
  else
    (* hidden toggle so that the css still displays the time highlights *)
    out {|<input type="radio" name="toggles" checked=true id="time" style="display: none">|}

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

let pr_one_bg_div kind n v ~max =
  out {|<div class="%s%d" style="width: %f%%"></div>|}
    kind n (percentage v ~max)

let () = all_data |> Array.iteri (fun j d ->
    let () = out {|<div class="code" title="File: %s
Line: %d

|} vname d.loc.line
    in
    let () = d.measures |> Array.iteri (fun k m ->
        out "Time%d: %ss\n" (k+1) m.time.str;
        Option.iter (fun d -> out "Major%d: %sMw\n" (k+1) d.str) m.major;
        Option.iter (fun d -> out "Minor%d: %sMw\n" (k+1) d.str) m.minor)
    in
    let () = out {|">|} in

    let () = d.measures |> Array.iteri (fun k m ->
       pr_one_bg_div "time" (k+1) m.time.q ~max:timemaxq;
       Option.iter (fun d -> pr_one_bg_div "major" (k+1) d.q ~max:majormaxq) m.major;
       Option.iter (fun d -> pr_one_bg_div "minor" (k+1) d.q ~max:minormaxq) m.minor)
    in

    let text = d.loc.text in
    let text = if text <> "" && text.[0] = '\n'
      then String.sub text 1 (String.length text  - 1)
      else text
    in
    let sublines = String.split_on_char '\n' text in
    let () = sublines |> List.iteri (fun i line ->
        let lnum = d.loc.line + i in
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
