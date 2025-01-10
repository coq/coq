
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

open Printf
;;

let _ = Printexc.record_backtrace true
;;

type ('a,'b) pkg_timings = {
  user_time  : 'a;
  num_instr  : 'b;
  num_mem    : 'b;
}
;;

let reduce_pkg_timings (m_f : 'a list -> 'c) (m_a : 'b list -> 'd) (t : ('a,'b) pkg_timings list) : ('c,'d) pkg_timings =
  { user_time  = m_f @@ CList.map (fun x -> x.user_time)  t
  ; num_instr  = m_a @@ CList.map (fun x -> x.num_instr)  t
  ; num_mem    = m_a @@ CList.map (fun x -> x.num_mem)    t
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

let run = run_and_read %> snd

module Float = struct
  let nan = nan
end

module CList = struct
  include CList

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
    if len < 0 then invalid_arg "CList.init" else
    if len > rev_init_threshold then rev (init_tailrec_aux [] 0 len f)
    else init_aux 0 len f

  let rec drop n = function
    | _ :: l when n > 0 -> drop (n-1) l
    | l -> l

  let reduce f = function
    | [] ->
      invalid_arg "CList.reduce: Empty CList"
    | h :: t ->
      fold_left f h t

  let min l = reduce Stdlib.min l

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

let add_timings a b =
  { user_time = a.user_time +. b.user_time;
    num_instr = a.num_instr + b.num_instr;
    num_mem = a.num_mem + b.num_mem;
  }

let mk_pkg_timings work_dir pkg_name suffix iteration =
  let command_prefix = "cat " ^ work_dir ^ "/" ^ pkg_name ^ suffix ^ string_of_int iteration in
  let ncoms = command_prefix ^ ".ncoms" |> run |> String.rchop ~n:1 |> int_of_string in
  let timings = CList.init ncoms (fun ncom ->
      let command_prefix = command_prefix ^ "." ^ string_of_int (ncom+1) in
      let time_command_output = command_prefix ^ ".time" |> run |> String.rchop ~n:1 |> String.split_on_char ' ' in

      let nth x i = CList.nth i x in

      { user_time = time_command_output |> nth 0 |> float_of_string
      (* Perf can indeed be not supported in some systems, so we must fail gracefully *)
      ; num_instr =
          (try command_prefix ^ ".perf | grep instructions:u | awk '{print $1}' | sed 's/,//g'" |>
               run |> String.rchop ~n:1 |> int_of_string
           with Failure _ -> 0)
      ; num_mem = time_command_output |> nth 1 |> int_of_string
      })
  in
  match timings with
  | [] -> assert false
  | timing :: rest -> CList.fold_left add_timings timing rest
;;

(* process command line paramters *)
assert (Array.length Sys.argv > 5);
let work_dir = Sys.argv.(1) in
let num_of_iterations = int_of_string Sys.argv.(2) in
let minimal_user_time = float_of_string Sys.argv.(3) in
let sorting_column = Sys.argv.(4) in
let coq_opam_packages = Sys.argv |> Array.to_list |> CList.drop 5 in

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

(* parse the *.time and *.perf files *)
coq_opam_packages
|> CList.map
     (fun package_name ->
       package_name,(* compilation_results_for_NEW : (float * int * int * int) list *)
       CList.init num_of_iterations succ |> CList.map (mk_pkg_timings work_dir package_name ".NEW."),
       CList.init num_of_iterations succ |> CList.map (mk_pkg_timings work_dir package_name ".OLD."))

(* from the list of measured values, select just the minimal ones *)

|> CList.map
  (fun ((package_name : string),
        (new_measurements : (float, int) pkg_timings list),
        (old_measurements : (float, int) pkg_timings list)) ->
    let f_min : float list -> float = CList.min in
    let i_min : int list -> int = CList.min in
    package_name,
    reduce_pkg_timings f_min i_min new_measurements,
    reduce_pkg_timings f_min i_min old_measurements
  )

(* compute the "proportional differences in % of the NEW measurement and the OLD measurement" of all measured values *)
|> CList.map
     (fun (package_name, new_t, old_t) ->
       package_name, new_t, old_t,
       { user_time  = (new_t.user_time -. old_t.user_time) /. old_t.user_time *. 100.0
       ; num_instr  = proportional_difference_of_integers new_t.num_instr  old_t.num_instr
       ; num_mem    = proportional_difference_of_integers new_t.num_mem    old_t.num_mem
       })

(* sort the table with results *)
|> CList.sort
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

|> CList.filter
     (fun (_, new_t, old_t, _) ->
        minimal_user_time <= new_t.user_time || minimal_user_time <= old_t.user_time)

(* Below we take the measurements and format them to stdout. *)

|> CList.map begin fun (package_name, new_t, old_t, perc) ->

  let precision = 2 in
  let prf f = Printf.sprintf "%.*f" precision f in
  let pri n = Printf.sprintf "%d" n in

  [
    [ package_name ];
    [ prf new_t.user_time; prf old_t.user_time; prf perc.user_time ];
    [ pri new_t.num_instr; pri old_t.num_instr; prf perc.num_instr ];
    [ pri new_t.num_mem; pri old_t.num_mem; prf perc.num_mem ];
  ]

  end

|> fun measurements ->

    let headers = [
      "";
      "user time [s]";
      "CPU instructions";
      "max resident mem [KB]";
    ] in

    let descr = ["NEW"; "OLD"; "PDIFF"] in
    let top = [ [ "package_name" ]; descr; descr; descr ] in

    printf "%s%!" (Table.raw_print headers top measurements ())
