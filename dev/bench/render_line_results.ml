
(** Recursively list .rocq-timediff files' relative directories in given directory *)
let list_timediff_files dir =
  let rec loop result = function
    | f :: fs when Sys.is_directory f ->
        Sys.readdir f
        |> Array.to_list
        |> CList.map (Filename.concat f)
        |> CList.append fs
        |> loop result
    | f :: fs ->
      if Filename.check_suffix f ".rocq-timediff" then
        loop (f::result) fs
      else
        loop result fs
    | [] -> result
  in
  Sys.readdir dir
  |> Array.to_list
  |> loop []

type one_data = {
  time1 : string;
  time2 : string;
  diff : string;
  pdiff : string;
  lnum : string;
  file : string;
}

exception UnableToParse

(** Read all the lines of a file into a list *)
let read_timing_lines file =
  let ic = open_in file in
  let html_file =  (Filename.chop_extension file) ^ ".html" in
  (* We tail recursively read lines in the file discarding the uninteresting ones *)
  let rec read_lines_aux acc =
    match input_line ic with
    | exception End_of_file -> acc
    | "" -> read_lines_aux acc
    | line ->
      match String.split_on_char ' ' line with
      | [time1; time2; diff; pdiff; lnum] ->
        {time1; time2; diff; pdiff; lnum; file=html_file} :: acc |> read_lines_aux
      | _ -> raise UnableToParse
  in
  let lines =
    try Some (read_lines_aux [])
    with End_of_file ->
      Printf.eprintf "*** Error: Could not read file %s.\n" file; None
  in
  close_in ic; lines

type html_data = { link_prefix : string }

let get_html_data () =
  match Sys.getenv_opt "CI_PAGES_DOMAIN",
        Sys.getenv_opt "CI_PROJECT_NAMESPACE",
        Sys.getenv_opt "CI_PROJECT_NAME",
        Sys.getenv_opt "CI_JOB_ID" with
  | Some domain, Some ns, Some project, Some id ->
    Some { link_prefix =
             Printf.sprintf "https://%s.%s/-/%s/-/jobs/%s/artifacts/_bench/html/"
               ns domain project id }
  | None, _, _, _ | _, None, _, _ | _, _, None, _ | _, _, _, None -> None

let html_str ?html lnum s = match html with
  | None -> Table.raw_str s
  | Some html ->
    let size = String.length s in
    let s = Printf.sprintf "<a href=\"%s%s#L%s\">%s</a>" html.link_prefix s lnum s in
    { Table.str = s; size }

let list_timing_data ?html {time1; time2; diff; pdiff; lnum; file} =
  List.append
    (List.map Table.raw_str [ time1; time2; diff; pdiff; lnum])
    [ html_str ?html lnum file ]

let render_table ?(reverse=false) title num table =
  let open Table.Align in
  let headers = [Table.raw_str title] in
  let top = Table.raw_row [["OLD"; "NEW"; "DIFF"; "%DIFF"; "Ln"; "FILE"]] in
  let align_top = [[Middle; Middle; Middle; Middle; Middle; MidLeft]] in
  let align_rows = [[Right; Right; Right; Right; Right; Left]] in
  (if reverse then CList.rev table else table)
  |> CList.firstn num
  |> fun x -> Table.print headers top x ~align_top ~align_rows ()

let to_file fname fmt =
  Printf.kfprintf close_out (open_out fname) fmt

let main () =
  let () = Printexc.record_backtrace true in
  let data =
    Unix.getcwd ()
    |> list_timediff_files
    |> CList.filter_map read_timing_lines
    |> CList.flatten
    |> CList.sort (fun x y -> Float.compare (float_of_string x.diff) (float_of_string y.diff))
  in
  let table =
    data
    |> CList.map list_timing_data
    |> CList.map (fun x -> [ x ])
  in
  (* What is a good number to choose? *)
  let num = 25 in
  let num = min num (CList.length table) in
  let slow_table = render_table (Printf.sprintf "TOP %d SLOW DOWNS" num) ~reverse:true num table in
  let fast_table = render_table (Printf.sprintf "TOP %d SPEED UPS" num) num table in
  let timings_table = render_table "Significant line time changes in bench" (CList.length table) table in
  (* Print tables to stdout *)
  Printf.printf "%s\n%s\n" slow_table fast_table;
  (* Print tables to files *)
  to_file "slow_table" "%s\n" slow_table;
  to_file "fast_table" "%s\n" fast_table;
  to_file "timings_table" "%s\n" timings_table;
  (* html tables *)
  match get_html_data () with
  | None -> ()
  | Some html ->
    let table =
      data
      |> CList.map (list_timing_data ~html)
      |> CList.map (fun x -> [ x ])
    in
    let slow_table = render_table (Printf.sprintf "TOP %d SLOW DOWNS" num) ~reverse:true num table in
    let fast_table = render_table (Printf.sprintf "TOP %d SPEED UPS" num) num table in
    let timings_table = render_table "Significant line time changes in bench" (CList.length table) table in
    to_file "slow_table.html" "<pre>%s</pre>\n" slow_table;
    to_file "fast_table.html" "<pre>%s</pre>\n" fast_table;
    to_file "timings_table.html" "<pre>%s</pre>\n" timings_table;
    ()


let () = main ()
