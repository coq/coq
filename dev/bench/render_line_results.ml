
(** Recursively list .html files' relative directories in given directory *)
let list_html_files dir =
  let rec loop result = function
    | f :: fs when Sys.is_directory f ->
        Sys.readdir f
        |> Array.to_list
        |> CList.map (Filename.concat f)
        |> CList.append fs
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

let parse_time_line l =
  (* we have floats written with s so with split that too *)
  match Str.split (Str.regexp "[ s]") l with
  | _ :: str :: _ -> float_of_string str
  | _ -> raise @@ UnableToParse

let parse_mem_line l =
  (* memory stats are written as Major/Minor: xx.xxMw *)
  match Str.split (Str.regexp "[ M]") l with
  | _ :: str :: _ -> float_of_string str
  | _ -> raise @@ UnableToParse

type diff_kind =
  { name : string
  ; table_name : string
  }

module DiffTupleCore : sig
  (** Lists with length exactly the length of diff_kinds.

     We use a separate type to make it easier to understand what's
     going on when we get a [_ list DiffTuple.t] (which would
     otherwise be [_ list list] and hard to tell which list is
     arbitrary length). *)
  type 'a t = private 'a list

  val diff_kinds : diff_kind t

  val map : ('a -> 'b) -> 'a t -> 'b t

  val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t

  val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

  val iter2 : ('a -> 'b -> unit) -> 'a t -> 'b t -> unit

  val make : 'a -> 'a t

  val of_list : 'a list -> 'a t

end = struct

  type 'a t = 'a list

  let map = CList.map

  let mapi = CList.mapi

  let map2 = CList.map2

  let iter2 = List.iter2

  let diff_kinds = [
    { name = "time";
      table_name = "timings"; };
    { name = "major alloc";
      table_name = "majors"; };
    { name = "minor_allocs";
      table_name = "minors"; };
  ]

  let len = List.length diff_kinds

  let make x = CList.make len x

  let of_list l = assert (List.length l = len); l

end

module DiffTuple : sig
  include module type of DiffTupleCore

  val split : 'a t list -> 'a list t
end = struct
  include DiffTupleCore

  let rec split_rec acc = function
    | [] -> map List.rev acc
    | hd :: tl ->
      let acc = map2 (fun hd acc -> hd :: acc) hd acc in
      split_rec acc tl

  let split l = split_rec (make []) l

end

type one_diff =
  { v1 : float
  ; v2 : float
  ; diff : float
  ; pdiff : float
  ; line_num : int
  ; file : string
  }

(* We accumulate the data in a tuple if the difference is non-zero *)
(* We also check that values are not too small (tolerence is trial and error) *)
let add_if_nonnegligible ~line_num ~file v1 v2 acc =
  let diff = v2 -. v1 in
  let pdiff = if v1 <> 0.0 then (diff *. 100.0) /. v1 else Float.infinity in
  if Float.abs diff <= 1e-4 then acc
  else {v1; v2; diff; pdiff; line_num; file} :: acc

let multi_add ~line_num ~file vs acc =
  DiffTuple.map2 (fun (v1,v2) acc -> add_if_nonnegligible ~line_num ~file v1 v2 acc) vs acc

let add_just_time ~line_num ~file (v1,v2) acc =
  DiffTuple.mapi (fun i acc ->
      if i = 0 then add_if_nonnegligible ~line_num ~file v1 v2 acc else acc)
    acc

(** Read all the lines of a file into a list *)
(* TODO we should really be reading from something nicer than comments
   in a generated html file... *)
let read_lines file =
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
          (* Time1 *)
          let time1 = parse_time_line (input_line ic) in
          let next = input_line ic in
          let acc = if CString.is_prefix "Major1" next then
              let major1 = parse_mem_line next in
              let minor1 = parse_mem_line (input_line ic) in
              (* Time2 *)
              let time2 = parse_time_line (input_line ic) in
              let next = input_line ic in
              if CString.is_prefix "Major2" next then
                let major2 = parse_mem_line next in
                let minor2 = parse_mem_line (input_line ic) in
                multi_add ~line_num ~file
                  (DiffTuple.of_list [(time1,time2); (major1,major2); (minor1,minor2)])
                  acc
              else
                (* support files produced with old Coq without mem stats
                   NB: here the first run had mem stats but not the second *)
                add_just_time ~line_num ~file (time1,time2) acc
            else
              (* support files produced with old Coq without mem stats
                 NB: it's possible that the second run had mem stats but we just skip them *)
              let time2 = parse_time_line next in
              add_just_time ~line_num ~file (time1,time2) acc
          in
          read_lines_aux acc
        else
          read_lines_aux acc
    | exception End_of_file -> acc
  in
  let lines =
    try Some (read_lines_aux (DiffTuple.map (fun _ -> []) DiffTuple.diff_kinds))
    with End_of_file ->
      Printf.eprintf "*** Error: Could not read file %s.\n" file; None
  in
  close_in ic; lines

type html_data = { link_prefix : string }

let get_html_data () =
  match Sys.getenv_opt "CI_PROJECT_NAMESPACE",
        Sys.getenv_opt "CI_PROJECT_NAME",
        Sys.getenv_opt "CI_JOB_ID" with
  | Some ns, Some project, Some id ->
    Some { link_prefix =
             Printf.sprintf "https://%s.gitlab.io/-/%s/-/jobs/%s/artifacts/_bench/html/"
               ns project id }
  | None, _, _ | _, None, _ | _, _, None -> None

let html_str ?html lnum s = match html with
  | None -> Table.raw_str s
  | Some html ->
    let size = String.length s in
    let s = Printf.sprintf "<a href=\"%s%s#L%d\">%s</a>" html.link_prefix s lnum s in
    { Table.str = s; size }

let list_timing_data ?html {v1=time1; v2=time2; diff; pdiff; line_num; file} =
  let str_time1 = Printf.sprintf "%.4f" time1 in
  let str_time2 = Printf.sprintf "%.4f" time2 in
  let str_diff  = Printf.sprintf "%.4f" diff in
  let str_pdiff = Printf.sprintf "%3.2f%%" pdiff in
  let str_line_num = string_of_int line_num in
  List.append
    (List.map Table.raw_str [ str_time1; str_time2; str_diff; str_pdiff; str_line_num])
    [ html_str ?html line_num file ]

let render_table ?(reverse=false) title num table =
  let open Table.Align in
  let headers = [Table.raw_str title] in
  let top = Table.raw_row [["OLD"; "NEW"; "DIFF"; "%DIFF"; "Ln"; "FILE"]] in
  let align_top = [[Middle; Middle; Middle; Middle; Middle; MidLeft]] in
  let align_rows = [[Right; Right; Right; Right; Right; Left]] in
  (if reverse then CList.rev table else table)
  |> (match num with Some num -> CList.firstn num | None -> fun x -> x)
  |> fun x -> Table.print headers top x ~align_top ~align_rows ()

let to_file fname fmt =
  Printf.kfprintf close_out (open_out fname) fmt

let sort_table table =
  table
  |> CList.flatten
  (* Do we want to do a unique sort? *)
  (* |> CList.sort_uniq ... *)
  |> CList.sort (fun x y -> Float.compare x.diff y.diff)

let render_and_print ?html data =
  let tables =
    data |> DiffTuple.map (fun data ->
        data
        |> CList.map (list_timing_data ?html)
        |> CList.map (fun x -> [ x ]))
  in
  let times = List.hd (tables : _ DiffTuple.t :> _ list) in
  (* What is a good number to choose? *)
  let num = 25 in
  let num = min num (CList.length times) in
  let slow_table = render_table (Printf.sprintf "TOP %d SLOW DOWNS" num) ~reverse:true (Some num) times in
  let fast_table = render_table (Printf.sprintf "TOP %d SPEED UPS" num) (Some num) times in
  let () = if Option.is_empty html then Printf.printf "%s\n%s\n" slow_table fast_table in
  let () = DiffTuple.iter2 (fun kind table ->
      let title = Printf.sprintf "Significant %s changes in bench" kind.name in
      let table = render_table title None table in
      let fext, fmt = if Option.is_empty html then "", ("%s\n" : _ format)
        else ".html", ("<pre>%s</pre>\n" : _ format)
      in
      let fname = Printf.sprintf "%s_table%s" kind.table_name fext in
      to_file fname fmt table)
      DiffTuple.diff_kinds tables
  in
  ()

let main () =
  let () = Printexc.record_backtrace true in
  let data =
    Unix.getcwd ()
    |> list_html_files
    |> CList.filter_map read_lines
    |> DiffTuple.split
    |> DiffTuple.map sort_table
  in
  render_and_print data;
  (* html tables *)
  match get_html_data () with
  | None -> ()
  | Some html -> render_and_print ~html data

let () = main ()
