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

let pp_words ~need_comma which w =
  if w = "0 w" then need_comma, ""
  else
    true, (if need_comma then ", " else "")^(String.sub w 0 (String.length w - 1))^which^" w"

let pp_collect ~need_comma which c =
  if c = 0 then need_comma, ""
  else
    true, Printf.sprintf "%s%d %s %s"
      (if need_comma then ", " else "") c which
      (if c = 1 then "collection" else "collections")

let pp_heap ~need_comma = function
  | None -> need_comma, ""
  | Some heap ->
    true, Printf.sprintf "%s%.3G w max heap size" (if need_comma then ", " else "") (float_of_int heap)

let pp_memory ch = function
  | None -> ()
  | Some {major_words; minor_words; major_collect; minor_collect; heap_words} ->
    (* need_comma <-> prefix is nontrivial *)
    let need_comma, minor_words = pp_words ~need_comma:false "minor" minor_words in
    let need_comma, major_words = pp_words ~need_comma "major" major_words in
    let need_comma, minor_collect = pp_collect ~need_comma "minor" minor_collect in
    let need_comma, major_collect = pp_collect ~need_comma "major" major_collect in
    let need_comma, heap = pp_heap ~need_comma heap_words in
    if need_comma then
      Printf.fprintf ch " (%s%s%s%s%s)" minor_words major_words minor_collect major_collect heap

let pp_instr ch = function
  | None -> ()
  | Some i -> Printf.fprintf ch ", %#d instr" i

type totals = {
  total_time: Q.t;
  total_instr: int option;
}


let output ch ~vname ~data_files all_data =

let out fmt = Printf.fprintf ch fmt in
let ndata = Array.length data_files in

let totals = Array.fold_left (fun acc (_,data) ->
    Array.map2 (fun acc d ->
        let total_time = Q.add acc.total_time d.time.q in
        let total_instr =
          match acc.total_instr, d.instructions with
          | Some acc, Some i -> Some (acc + i)
          | (Some _ as acc), None -> acc
          | _, (Some _ as i) -> i
          | None, None -> None
        in
        {total_time;total_instr}
      ) acc data)
    (Array.make ndata {total_time=Q.zero; total_instr=None})
    all_data
in

let maxtime =
  Array.fold_left (fun max (_,data) ->
      Array.fold_left (fun max d ->
          let dq = d.time.q in
          if Q.lt max dq then dq
          else max)
        max
        data)
    Q.zero all_data
in

let maxinstructions =
  Array.fold_left (fun max (_,data) ->
      Array.fold_left (fun max d ->
          Option.cata (fun instructions ->
              if max < instructions then instructions
              else max
            ) max d.instructions
        )
        max
        data)
    0 all_data
in

let maxheap =
  Array.fold_left (fun max (_,data) ->
      Array.fold_left (fun max d ->
          Option.fold_left (fun max mem ->
              Option.fold_left (fun max heap -> Stdlib.max max heap)
                max mem.heap_words)
            max d.memory)
        max
        data)
    0 all_data
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
{|.measure%d {
  background-color: %s;
  height: %d%%;
  top: %d%%;
  z-index: -1;
  position: absolute;
  opacity: 0%%;
}
#instructions:checked ~ pre .instructions { opacity: 50%%; }
#time:checked ~ pre .time { opacity: 50%%; }
#memory:checked ~ pre .memory { opacity: 50%%; }
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

let pp_total_instr fmt = function
  | None -> ()
  | Some total_instr ->
    Printf.fprintf fmt "total instructions: %.3GG, "
      Float.(of_int total_instr /. 1_000_000_000.0)
in

let () = data_files |> Array.iteri (fun i data_file ->
    out "<li style=\"background-color: %s\">%s (%atotal time: %.3Gs)</li>\n"
      colors.(i)
      data_file
      pp_total_instr
      totals.(i).total_instr
      (Q.to_float totals.(i).total_time))
in

let () = out "</ol>\n" in

let () =
  out {|<input type="radio" name="mode" id="instructions" checked><label for="instructions">Instructions</label>
|}
in

let () =
  out {|<input type="radio" name="mode" id="time"><label for="time">Time</label>
|}
in

let () =
  if maxheap > 0 then
    out {|<input type="radio" name="mode" id="memory"><label for="memory">Memory</label>
|}
in

let () = out "<pre>" in

let last_seen_line = ref 0 in

let line_id fmt l =
  if l > !last_seen_line then begin
    last_seen_line := l;
    Printf.fprintf fmt "id=\"L%d\" " l
  end
in

let () = all_data |> Array.iteri (fun j (loc,data) ->
    let () = out {|<div class="code" title="File: %s
Line: %d

|} vname loc.line
    in
    let () = data |> Array.iteri (fun k d ->
        out "Time%d: %ss%a%a\n" (k+1) d.time.str pp_instr d.instructions pp_memory d.memory)
    in
    let () = out {|">|} in

    let () = data |> Array.iteri (fun k d ->
        Option.iter (fun instructions ->
          out {|<div class="measure%d instructions" style="width: %f%%"></div>|}
            (k+1)
            (percentage (Q.of_int instructions) ~max:(Q.of_int maxinstructions))
          ) d.instructions ;
        out {|<div class="measure%d time" style="width: %f%%"></div>|}
          (k+1)
          (percentage d.time.q ~max:maxtime);
        let heap = Option.bind d.memory (fun m -> m.heap_words) in
        heap |> Option.iter (fun heap ->
            out {|<div class="measure%d memory" style="width: %f%%"></div>|}
              (k+1)
              (percentage (Q.of_int heap) ~max:(Q.of_int maxheap))))
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


type selection =
| Instr of { min_diff: int }
| Time of { min_diff: Q.t; }

let raw_output ch ~selection all_data =
  all_data |> Array.iteri @@ fun j (loc,data) ->
  let d1, d2 = match data with
    | [|d1; d2|] -> d1, d2
    | _ -> die "-raw-o only supports 2 data files, got %d" (Array.length data)
  in
  match selection with
  | Time {min_diff} ->
    let diff = Q.(d2.time.q - d1.time.q) in
    let ignore = Q.lt (Q.abs diff) min_diff in
    if not ignore then begin
      let pdiff = if Q.(equal zero d1.time.q) then Float.infinity
        else Q.(to_float @@ ((of_int 100 * diff) / d1.time.q))
      in
      (* XXX %.4f makes sense for min_diff=1e-4 but should be smarter for other min_diff *)
      Printf.fprintf ch "%s %s %.4f %3.2f%% %d\n"
      d1.time.str d2.time.str (Q.to_float diff) pdiff loc.line
    end
  | Instr {min_diff} ->
    Option.iter2 (fun i1 i2 ->
      let diff = i2 - i1 in
      let ignore = Stdlib.Int.abs diff < min_diff in
      if not ignore then begin
        let pdiff = if i1 = 0 then Float.infinity
            else Float.(of_int (100 * diff) /. of_int i1)
        in
        (* XXX %.4f makes sense for min_diff=1e-4 but should be smarter for other min_diff *)
        Printf.fprintf ch "%.2f %.2f %.4f %3.2f%% %d\n"
            Float.(of_int i1 /. 1_000_000_000.0)
            Float.(of_int i2 /. 1_000_000_000.0)
            Float.(of_int diff /. 1_000_000_000.0) pdiff loc.line
      end
      ) d1.instructions d2.instructions
