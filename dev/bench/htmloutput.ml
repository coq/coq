(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open BenchUtil

let die fmt = Printf.kfprintf (fun _ -> exit 1) stderr (fmt^^"\n%!")

let colors = [|"#F08080"; "#EEE8AA"; "#98FB98"|]

let max_data_count = Array.length colors

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

let percentage ~max:m v =
  Q.to_float Q.(v * of_int 100 / m)

let output ch ~vname ~data_files all_data =

let out fmt = Printf.fprintf ch fmt in
let ndata = Array.length data_files in

let totals = Array.fold_left (fun acc (_,data) ->
    Array.map2 (fun acc d -> Q.add acc d.q) acc data)
    (Array.make ndata Q.zero)
    all_data
in

let maxq =
  Array.fold_left (fun max (_,data) ->
      Array.fold_left (fun max d ->
          let dq = d.q in
          if Q.lt max dq then dq
          else max)
        max
        data)
    Q.zero all_data
in

let () =
  out
{|<html>
<head>
<title>%s</title>
<style>
|} vname
in

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
in

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
in

let () = out "<h1>Timings for %s</h1>\n" vname in

let () = out "<ol>\n" in

let () = data_files |> Array.iteri (fun i data_file ->
    out "<li style=\"background-color: %s\">%s (total time: %.3Gs)</li>\n"
      colors.(i)
      data_file
      (Q.to_float totals.(i)))
in

let () = out "</ol>\n" in

let () = out "<pre>" in

let last_seen_line = ref 0 in

let line_id fmt l =
  if l > !last_seen_line then begin
    last_seen_line := l;
    Printf.fprintf fmt "id=\"L%d\" " l
  end
in

let () = all_data |> Array.iteri (fun j (loc,time) ->
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
in

let () =
  out
{|
</pre>

</body>
</html>
|}
in

()

let raw_output ch ~min_diff all_data =
  all_data |> Array.iteri @@ fun j (loc,time) ->
  let t1, t2 = match time with
    | [|t1; t2|] -> t1, t2
    | _ -> die "-raw-o only supports 2 data files, got %d" (Array.length time)
  in
  let diff = Q.(t2.q - t1.q) in
  let ignore = Q.lt (Q.abs diff) min_diff in
  if not ignore then begin
    let pdiff = if Q.(equal zero t1.q) then Float.infinity
      else Q.(to_float @@ ((of_int 100 * diff) / t1.q))
    in
    (* XXX %.4f makes sense for min_diff=1e-4 but should be smarter for other min_diff *)
    Printf.fprintf ch "%s %s %.4f %3.2f%% %d\n"
      t1.str t2.str (Q.to_float diff) pdiff loc.line
  end
