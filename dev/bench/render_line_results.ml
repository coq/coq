
(** Recursively list .html files' relative directories in given directory *)
let list_html_files dir =
  let rec loop result = function
    | f :: fs when Sys.is_directory f ->
        Sys.readdir f
        |> Array.to_list
        |> List.map (Filename.concat f)
        |> List.append fs
        |> loop result
    | f :: fs ->
      if Filename.check_suffix f ".html" then
        loop (f::result) fs
      else
        loop result fs
    | [] -> result
  in
  Sys.readdir dir
  |> Array.to_list
  |> loop []

exception UnableToParse

(** Read all the lines of a file into a list *)
let read_timing_lines file =
  let ic = open_in file in
  (* We tail recursively read lines in the file discarding the uninteresting ones *)
  let rec read_lines_aux acc =
    match input_line ic with
    | line ->
        if Str.string_match (Str.regexp "Line:.*") line 0 then
          (* We know this line is ["Line:"] *)
          let line_num = match Str.split (Str.regexp " ") line with
            | _ :: ln :: _ -> int_of_string ln
            | _ -> raise @@ UnableToParse
          in
          (* Second line is empty *)
          let _ = input_line ic in
          (* Time1 - we have floats written with s so with split that too *)
          let time1 = match Str.split (Str.regexp "[ s]") (input_line ic) with
            | _ :: time1_str :: _ -> float_of_string time1_str
            | _ -> raise @@ UnableToParse
          in
          (* Time2 *)
          let time2 = match Str.split (Str.regexp "[ s]") (input_line ic) with
            | _ :: time2_str :: _ -> float_of_string time2_str
            | _ -> raise @@ UnableToParse
          in
          (* Difference *)
          let diff = time2 -. time1 in
          (* Percentage diff *)
          let pdiff = if time1 <> 0.0 then (diff *. 100.0) /. time1 else Float.infinity in
          (* We accumulate the timing data in a tuple if the difference is non-zero *)
          (* We also check that timed values are not too small (tolerence is trial and error) *)
          if Float.abs diff <= 1e-4 then
            acc |> read_lines_aux
          else
            (time1, time2, diff, pdiff, line_num, file) :: acc |> read_lines_aux
        else
          read_lines_aux acc
    | exception End_of_file -> acc
  in
  let lines = read_lines_aux [] in
  close_in ic; lines

let list_timing_data (time1, time2, diff, pdiff, line_num, file) =
  let str_time1 = Printf.sprintf "%.4f" time1 in
  let str_time2 = Printf.sprintf "%.4f" time2 in
  let str_diff  = Printf.sprintf "%.4f" diff in
  let str_pdiff = Printf.sprintf "%3.2f%%" pdiff in
  let str_line_num = string_of_int line_num in
  [ str_time1; str_time2; str_diff; str_pdiff; str_line_num; file ]

let render_table ?(reverse=false) title num table =
  let open Table.Align in
  let headers = [title] in
  let top = [["OLD"; "NEW"; "DIFF"; "%DIFF"; "Ln"; "FILE"]] in
  let align_top = [[Middle; Middle; Middle; Middle; Middle; MidLeft]] in
  let align_rows = [[Right; Right; Right; Right; Right; Left]] in
  (if reverse then List.rev table else table)
  |> Array.of_list
  |> fun x -> Array.sub x 0 num
  |> Array.to_list
  |> fun x -> Table.print headers top x ~align_top ~align_rows ()

let main () =
  let _ = Printexc.record_backtrace true in
  let table =
    Unix.getcwd ()
    |> list_html_files
    |> List.map read_timing_lines
    |> List.flatten
    (* Do we want to do a unique sort? *)
    (* |> List.sort_uniq (fun (_,_,x,_,_,_) (_,_,y,_,_,_) -> Float.compare x y) *)
    |> List.sort (fun (_,_,x,_,_,_) (_,_,y,_,_,_) -> Float.compare x y)
    |> List.map list_timing_data
    |> List.map (fun x -> [ x ])
  in
  (* What is a good number to choose? *)
  let num = 25 in
  let num = min num (List.length table) in
  let slow_table = render_table (Printf.sprintf "TOP %d SLOW DOWNS" num) ~reverse:true num table in
  let fast_table = render_table (Printf.sprintf "TOP %d SPEED UPS" num) num table in
  let timings_table = render_table "Significant line time changes in bench" (List.length table) table in
  (* Print tables to stdout *)
  Printf.printf "%s\n%s\n" slow_table fast_table;
  (* Print slow table to slow_table file *)
  let oc_slow = open_out "slow_table" in
  Printf.fprintf oc_slow "%s\n" slow_table;
  close_out oc_slow;
  (* Print fast table to fast_table file *)
  let oc_fast = open_out "fast_table" in
  Printf.fprintf oc_fast "%s\n" fast_table;
  close_out oc_fast;
  (* Print all timing data to line_timings file *)
  let oc_timings = open_out "timings_table" in
  Printf.fprintf oc_timings "%s\n" timings_table;
  close_out oc_timings;
  ()

let () = main ()
