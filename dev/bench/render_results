#! /usr/bin/env ocaml

(* ASSUMPTIONS:
   - the 1-st command line argument (working directory):
     - designates an existing readable directory
     - which contains *.time and *.perf files produced by bench.sh script
   - the 2-nd command line argument (number of iterations):
     - is a positive integer
   - the 3-rd command line argument (minimal user time):
     - is a positive floating point number
   - the 4-th command line argument determines the name of the column according to which the resulting table will be sorted.
     Valid values are:
     - package_name
     - user_time_pdiff
   - the rest of the command line-arguments
     - are names of benchamarked Coq OPAM packages for which bench.sh script generated *.time and *.perf files
 *)

#use "topfind";;
#require "unix";;
#print_depth 100000000;;
#print_length 100000000;;

open Printf
open Unix
;;

let _ = Printexc.record_backtrace true
;;

type ('a,'b) pkg_timings = {
  user_time  : 'a;
  num_instr  : 'b;
  num_cycles : 'b;
  num_mem    : 'b;
  num_faults : 'b;
}
;;

let reduce_pkg_timings (m_f : 'a list -> 'c) (m_a : 'b list -> 'd) (t : ('a,'b) pkg_timings list) : ('c,'d) pkg_timings =
  { user_time  = m_f @@ List.map (fun x -> x.user_time)  t
  ; num_instr  = m_a @@ List.map (fun x -> x.num_instr)  t
  ; num_cycles = m_a @@ List.map (fun x -> x.num_cycles) t
  ; num_mem    = m_a @@ List.map (fun x -> x.num_mem)    t
  ; num_faults = m_a @@ List.map (fun x -> x.num_faults) t
  }
;;

(******************************************************************************)
(* BEGIN Copied from batteries, to remove *)
(******************************************************************************)
let run_and_read cmd =
  (* This code is before the open of BatInnerIO
     to avoid using batteries' wrapped IOs *)
  let string_of_file fn =
    let buff_size = 1024 in
    let buff = Buffer.create buff_size in
    let ic = open_in fn in
    let line_buff = Bytes.create buff_size in
    begin
      let was_read = ref (input ic line_buff 0 buff_size) in
      while !was_read <> 0 do
        Buffer.add_subbytes buff line_buff 0 !was_read;
        was_read := input ic line_buff 0 buff_size;
      done;
      close_in ic;
    end;
    Buffer.contents buff
  in
  let tmp_fn = Filename.temp_file "" "" in
  let cmd_to_run = cmd ^ " > " ^ tmp_fn in
  let status = Unix.system cmd_to_run in
  let output = string_of_file tmp_fn in
  Unix.unlink tmp_fn;
  (status, output)
;;

let ( %> ) f g x = g (f x)
;;

let run = run_and_read %> snd
;;

module Float = struct
  let nan = Pervasives.nan
end

module Tuple4 = struct

  let first (x,_,_,_) = x
  let second (_,y,_,_) = y
  let third (_,_,z,_) = z
  let fourth (_,_,_,z) = z

end
;;

module List = struct
  include List

  let rec init_tailrec_aux acc i n f =
    if i >= n then acc
    else init_tailrec_aux (f i :: acc) (i+1) n f

  let rec init_aux i n f =
    if i >= n then []
    else
      let r = f i in
      r :: init_aux (i+1) n f

  let rev_init_threshold =
    match Sys.backend_type with
    | Sys.Native | Sys.Bytecode -> 10_000
    (* We don't known the size of the stack, better be safe and assume it's small. *)
    | Sys.Other _ -> 50

  let init len f =
    if len < 0 then invalid_arg "List.init" else
    if len > rev_init_threshold then rev (init_tailrec_aux [] 0 len f)
    else init_aux 0 len f

  let rec drop n = function
    | _ :: l when n > 0 -> drop (n-1) l
    | l -> l

  let reduce f = function
    | [] ->
      invalid_arg "List.reduce: Empty List"
    | h :: t ->
      fold_left f h t

  let min l = reduce Pervasives.min l
  let max l = reduce Pervasives.max l

end
;;

module String = struct

  include String

  let rchop ?(n = 1) s =
    if n < 0 then
      invalid_arg "String.rchop: number of characters to chop is negative"
    else
      let slen = length s in
      if slen <= n then "" else sub s 0 (slen - n)

end
;;

(******************************************************************************)
(* END Copied from batteries, to remove *)
(******************************************************************************)

let mk_pkg_timings work_dir pkg_name suffix iteration =
  let command_prefix = "cat " ^ work_dir ^ "/" ^ pkg_name ^ suffix ^ string_of_int iteration in
  let time_command_output = command_prefix ^ ".time" |> run |> String.rchop ~n:1 |> String.split_on_char ' ' in

  let nth x i = List.nth i x in

  { user_time = time_command_output |> nth 0 |> float_of_string
  (* Perf can indeed be not supported in some systems, so we must fail gracefully *)
  ; num_instr =
      (try command_prefix ^ ".perf | grep instructions:u | awk '{print $1}' | sed 's/,//g'" |>
           run |> String.rchop ~n:1 |> int_of_string
       with Failure _ -> 0)
  ; num_cycles =
      (try command_prefix ^ ".perf | grep cycles:u | awk '{print $1}' | sed 's/,//g'" |>
           run |> String.rchop ~n:1 |> int_of_string
       with Failure _ -> 0)
  ; num_mem = time_command_output |> nth 1 |> int_of_string
  ; num_faults = time_command_output |> nth 2 |> int_of_string
  }
;;

(* process command line paramters *)
assert (Array.length Sys.argv > 5);
let work_dir = Sys.argv.(1) in
let num_of_iterations = int_of_string Sys.argv.(2) in
let new_coq_version = Sys.argv.(3) in
let old_coq_version = Sys.argv.(4) in
let minimal_user_time = float_of_string Sys.argv.(5) in
let sorting_column = Sys.argv.(6) in
let coq_opam_packages = Sys.argv |> Array.to_list |> List.drop 7 in

(* ASSUMPTIONS:

   "working_dir" contains all the files produced by the following command:

      two_points_on_the_same_branch.sh $working_directory $coq_repository $coq_branch[:$new:$old] $num_of_iterations coq_opam_package_1 coq_opam_package_2 ... coq_opam_package_N
-sf
*)

(* Run a given bash command;
   wait until it termines;
   check if its exit status is 0;
   return its whole stdout as a string. *)

let proportional_difference_of_integers new_value old_value =
  if old_value = 0
  then Float.nan
  else float_of_int (new_value - old_value) /. float_of_int old_value *. 100.0
in

let count_number_of_digits_before_decimal_point =
  log10 %> floor %> int_of_float %> succ %> max 1
in

(* parse the *.time and *.perf files *)
coq_opam_packages
|> List.map
     (fun package_name ->
       package_name,(* compilation_results_for_NEW : (float * int * int * int) list *)
       List.init num_of_iterations succ |> List.map (mk_pkg_timings work_dir package_name ".NEW."),
       List.init num_of_iterations succ |> List.map (mk_pkg_timings work_dir package_name ".OLD."))

(* from the list of measured values, select just the minimal ones *)

|> List.map
  (fun ((package_name : string),
        (new_measurements : (float, int) pkg_timings list),
        (old_measurements : (float, int) pkg_timings list)) ->
    let f_min : float list -> float = List.min in
    let i_min : int list -> int = List.min in
    package_name,
    reduce_pkg_timings f_min i_min new_measurements,
    reduce_pkg_timings f_min i_min old_measurements
  )

(* compute the "proportional differences in % of the NEW measurement and the OLD measurement" of all measured values *)
|> List.map
     (fun (package_name, new_t, old_t) ->
       package_name, new_t, old_t,
       { user_time  = (new_t.user_time -. old_t.user_time) /. old_t.user_time *. 100.0
       ; num_instr  = proportional_difference_of_integers new_t.num_instr  old_t.num_instr
       ; num_cycles = proportional_difference_of_integers new_t.num_cycles old_t.num_cycles
       ; num_mem    = proportional_difference_of_integers new_t.num_mem    old_t.num_mem
       ; num_faults = proportional_difference_of_integers new_t.num_faults old_t.num_faults
       })

(* sort the table with results *)
|> List.sort
     (match sorting_column with
      | "user_time_pdiff" ->
        fun (_,_,_,perf1) (_,_,_,perf2) ->
          compare perf1.user_time perf2.user_time
      | "package_name" ->
        fun (n1,_,_,_) (n2,_,_,_) -> compare n1 n2
      | _ ->
        assert false
     )

(* Keep only measurements that took at least "minimal_user_time" (in seconds). *)

|> List.filter
     (fun (_, new_t, old_t, _) ->
        minimal_user_time <= new_t.user_time && minimal_user_time <= old_t.user_time)

(* Below we take the measurements and format them to stdout. *)

|> fun measurements ->

     let precision = 2 in

     (* the labels that we will print *)
     let package_name__label = "package_name" in
     let new__label = "NEW" in
     let old__label = "OLD" in
     let proportional_difference__label = "PDIFF" in

     (* the lengths of labels that we will print *)
     let new__label__length = String.length new__label in
     let proportional_difference__label__length = String.length proportional_difference__label in

     (* widths of individual columns of the table *)
     let package_name__width =
       max (measurements |> List.map (Tuple4.first %> String.length) |> List.max)
         (String.length package_name__label) in

     let llf proj =
       let lls = count_number_of_digits_before_decimal_point (List.max proj) + 1 + precision in
       max lls new__label__length in

     let lli proj =
       let lls = count_number_of_digits_before_decimal_point (float_of_int (List.(max proj))) + 1 + precision in
       max lls new__label__length in

     let new_timing_width = reduce_pkg_timings llf lli @@ List.map Tuple4.second measurements in
     let old_timing_width = reduce_pkg_timings llf lli @@ List.map Tuple4.third measurements in

     let llp proj =
       let lls =
         count_number_of_digits_before_decimal_point List.(max List.(map abs_float proj)) + 2 + precision in
       max lls proportional_difference__label__length in

     let perc_timing_width = reduce_pkg_timings llp llp @@ List.map Tuple4.fourth measurements in

     (* print the table *)
     let rec make_dashes = function
       | 0 -> ""
       | count -> "─" ^ make_dashes (pred count)
     in

     let vertical_separator left_glyph middle_glyph right_glyph =
       sprintf "%s─%s─%s─%s─%s─%s───%s─%s─%s─%s───%s─%s─%s─%s───%s─%s─%s─%s───%s─%s─%s─%s───%s\n"
       left_glyph
       (make_dashes package_name__width)
       middle_glyph
       (make_dashes new_timing_width.user_time)
       (make_dashes old_timing_width.user_time)
       (make_dashes perc_timing_width.user_time)
       middle_glyph
       (make_dashes new_timing_width.num_cycles)
       (make_dashes old_timing_width.num_cycles)
       (make_dashes perc_timing_width.num_cycles)
       middle_glyph
       (make_dashes new_timing_width.num_instr)
       (make_dashes old_timing_width.num_instr)
       (make_dashes perc_timing_width.num_instr)
       middle_glyph
       (make_dashes new_timing_width.num_mem)
       (make_dashes old_timing_width.num_mem)
       (make_dashes perc_timing_width.num_mem)
       middle_glyph
       (make_dashes new_timing_width.num_faults)
       (make_dashes old_timing_width.num_faults)
       (make_dashes perc_timing_width.num_faults)
       right_glyph
     in

     let center_string string width =
       let string_length = String.length string in
       let width = max width string_length in
       let left_hfill = (width - string_length) / 2 in
       let right_hfill = width - left_hfill - string_length in
       String.make left_hfill ' ' ^ string ^ String.make right_hfill ' '
     in
     printf "\n";
     print_string (vertical_separator "┌" "┬" "┐");
     "│" ^ String.make (1 + package_name__width + 1) ' ' ^ "│"
     ^ center_string "user time [s]" (1 +  new_timing_width.user_time + 1 + old_timing_width.user_time + 1 + perc_timing_width.user_time + 3) ^ "│"
     ^ center_string "CPU cycles" (1 + new_timing_width.num_cycles    + 1 + old_timing_width.num_cycles    + 1 + perc_timing_width.num_cycles + 3) ^ "│"
     ^ center_string "CPU instructions" (1 + new_timing_width.num_instr + 1 + old_timing_width.num_instr + 1 + perc_timing_width.num_instr + 3) ^ "│"
     ^ center_string "max resident mem [KB]" (1 + new_timing_width.num_mem + 1 + old_timing_width.num_mem + 1 + perc_timing_width.num_mem + 3) ^ "│"
     ^ center_string "mem faults" (1 + new_timing_width.num_faults + 1 + old_timing_width.num_faults + 1 + perc_timing_width.num_faults + 3)
     ^ "│\n" |> print_string;
     printf "│%*s │ %*s│ %*s│ %*s│ %*s│ %*s│\n"
       (1 + package_name__width) ""
       (new_timing_width.user_time    + 1 + old_timing_width.user_time    + 1 + perc_timing_width.user_time + 3) ""
       (new_timing_width.num_cycles       + 1 + old_timing_width.num_cycles       + 1 + perc_timing_width.num_cycles + 3) ""
       (new_timing_width.num_instr + 1 + old_timing_width.num_instr + 1 + perc_timing_width.num_instr + 3) ""
       (new_timing_width.num_mem + 1 + old_timing_width.num_mem + 1 + perc_timing_width.num_mem + 3) ""
       (new_timing_width.num_faults + 1 + old_timing_width.num_faults + 1 + perc_timing_width.num_faults + 3) "";
     printf "│ %*s │ %*s %*s %*s   │ %*s %*s %*s   │ %*s %*s %*s   │ %*s %*s %*s   │ %*s %*s %*s   │\n"
       package_name__width package_name__label
       new_timing_width.user_time new__label
       old_timing_width.user_time old__label
       perc_timing_width.user_time proportional_difference__label
       new_timing_width.num_cycles new__label
       old_timing_width.num_cycles old__label
       perc_timing_width.num_cycles proportional_difference__label
       new_timing_width.num_instr new__label
       old_timing_width.num_instr old__label
       perc_timing_width.num_instr proportional_difference__label
       new_timing_width.num_mem new__label
       old_timing_width.num_mem old__label
       perc_timing_width.num_mem proportional_difference__label
       new_timing_width.num_faults new__label
       old_timing_width.num_faults old__label
       perc_timing_width.num_faults proportional_difference__label;
     measurements |> List.iter
         (fun (package_name, new_t, old_t, perc) ->
           print_string (vertical_separator "├" "┼" "┤");
           printf "│ %*s │ %*.*f %*.*f %+*.*f %% │ %*d %*d %+*.*f %% │ %*d %*d %+*.*f %% │ %*d %*d %+*.*f %% │ %*d %*d %+*.*f %% │\n"
             package_name__width package_name
             new_timing_width.user_time precision new_t.user_time
             old_timing_width.user_time precision old_t.user_time
             perc_timing_width.user_time precision perc.user_time
             new_timing_width.num_cycles new_t.num_cycles
             old_timing_width.num_cycles old_t.num_cycles
             perc_timing_width.num_cycles precision perc.num_cycles
             new_timing_width.num_instr new_t.num_instr
             old_timing_width.num_instr old_t.num_instr
             perc_timing_width.num_instr precision perc.num_instr
             new_timing_width.num_mem new_t.num_mem
             old_timing_width.num_mem old_t.num_mem
             perc_timing_width.num_mem precision perc.num_mem
             new_timing_width.num_faults new_t.num_faults
             old_timing_width.num_faults old_t.num_faults
             perc_timing_width.num_faults precision perc.num_faults);

print_string (vertical_separator "└" "┴" "┘");

(* ejgallego: disable this as it is very verbose and brings up little info in the log. *)
if false then begin
printf "

PDIFF = proportional difference between measurements done for the NEW and the OLD Coq version
      = (NEW_measurement - OLD_measurement) / OLD_measurement * 100%%

NEW = %s
OLD = %s

Columns:

  1. user time [s]

     Total number of CPU-seconds that the process used directly (in user mode), in seconds.
     (In other words, \"%%U\" quantity provided by the \"/usr/bin/time\" command.)

  2. CPU cycles

     Total number of CPU-cycles that the process used directly (in user mode).
     (In other words, \"cycles:u\" quantity provided by the \"/usr/bin/perf\" command.)

  3. CPU instructions

     Total number of CPU-instructions that the process used directly (in user mode).
     (In other words, \"instructions:u\" quantity provided by the \"/usr/bin/perf\" command.)

  4. max resident mem [KB]

     Maximum resident set size of the process during its lifetime, in Kilobytes.
     (In other words, \"%%M\" quantity provided by the \"/usr/bin/time\" command.)

  5. mem faults

     Number of major, or I/O-requiring, page faults that occurred while the process was running.
     These are faults where the page has actually migrated out of primary memory.
     (In other words, \"%%F\" quantity provided by the \"/usr/bin/time\" command.)

" new_coq_version old_coq_version;
end
