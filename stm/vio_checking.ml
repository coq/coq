(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util

let check_vio (ts,f) =
  Dumpglob.noglob ();
  let long_f_dot_v, _, _, _, _, tasks, _ = Library.load_library_todo f in
  Stm.set_compilation_hints long_f_dot_v;
  List.fold_left (fun acc ids -> Stm.check_task f tasks ids && acc) true ts

module Worker = Spawn.Sync ()

module IntOT = struct
  type t = int
  let compare = compare
end

module Pool = Map.Make(IntOT)

let schedule_vio_checking j fs =
  if j < 1 then CErrors.user_err Pp.(str "The number of workers must be bigger than 0");
  let jobs = ref [] in
  List.iter (fun f ->
    let f =
      if Filename.check_suffix f ".vio" then Filename.chop_extension f
      else f in
    let long_f_dot_v, _,_,_,_, tasks, _ = Library.load_library_todo f in
    Stm.set_compilation_hints long_f_dot_v;
    let infos = Stm.info_tasks tasks in
    let eta = List.fold_left (fun a (_,t,_) -> a +. t) 0.0 infos in
    if infos <> [] then jobs := (f, eta, infos) :: !jobs)
  fs;
  let cmp_job (_,t1,_) (_,t2,_) = compare t2 t1 in
  jobs := List.sort cmp_job !jobs;
  let eta = ref (List.fold_left (fun a j -> a +. pi2 j) 0.0 !jobs) in
  let pool : Worker.process Pool.t ref = ref Pool.empty in
  let rec filter_argv b = function
    | [] -> []
    | "-schedule-vio-checking" :: rest -> filter_argv true rest
    | s :: rest when String.length s > 0 && s.[0] = '-' && b -> filter_argv false (s :: rest)
    | _ :: rest when b -> filter_argv b rest
    | s :: rest -> s :: filter_argv b rest in
  let pack = function
    | [] -> []
    | ((f,_),_,_) :: _ as l ->
        let rec aux last acc = function
          | [] -> [last,acc]
          | ((f',id),_,_) :: tl when last = f' -> aux last (id::acc) tl
          | ((f',id),_,_) :: _ as l -> (last,acc) :: aux f' [] l in
        aux f [] l in
  let prog = Sys.argv.(0) in  
  let stdargs = filter_argv false (List.tl (Array.to_list Sys.argv)) in
  let make_job () =
    let cur = ref 0.0 in
    let what = ref [] in
    let j_left = j - Pool.cardinal !pool in
    let take_next_file () =
      let f, t, tasks = List.hd !jobs in
      jobs := List.tl !jobs;
      cur := !cur +. t;
      what := (List.map (fun (n,t,id) -> (f,id),n,t) tasks) @ !what in
    if List.length !jobs >= j_left then take_next_file ()
    else while !jobs <> [] &&
         !cur < max 0.0 (min 60.0 (!eta /. float_of_int j_left)) do
      let f, t, tasks = List.hd !jobs in
      jobs := List.tl !jobs;
      let n, tt, id = List.hd tasks in
      if List.length tasks > 1 then
        jobs := (f, t -. tt, List.tl tasks) :: !jobs;
      cur := !cur +. tt;
      what := ((f,id),n,tt) :: !what;
    done;
    if !what = [] then take_next_file ();
    eta := !eta -. !cur;
    let cmp_job (f1,_,_) (f2,_,_) = compare f1 f2 in
    List.flatten
      (List.map (fun (f, tl) ->
        "-check-vio-tasks" :: 
        String.concat "," (List.map string_of_int tl) :: [f])
      (pack (List.sort cmp_job !what))) in
  let rc = ref 0 in
  while !jobs <> [] || Pool.cardinal !pool > 0 do
    while Pool.cardinal !pool < j && !jobs <> [] do
      let args = Array.of_list (stdargs @ make_job ()) in
      let proc, _, _ = Worker.spawn prog args in
      pool := Pool.add (Worker.unixpid proc) proc !pool;
    done;
    let pid, ret = Unix.wait () in
    if ret <> Unix.WEXITED 0 then rc := 1;
    pool := Pool.remove pid !pool;
  done;
  exit !rc

let schedule_vio_compilation j fs =
  if j < 1 then CErrors.user_err Pp.(str "The number of workers must be bigger than 0");
  let jobs = ref [] in
  List.iter (fun f ->
    let f =
      if Filename.check_suffix f ".vio" then Filename.chop_extension f
      else f in
    let long_f_dot_v = Loadpath.locate_file (f^".v") in
    let aux = Aux_file.load_aux_file_for long_f_dot_v in
    let eta =
      try float_of_string (Aux_file.get aux "vo_compile_time")
      with Not_found -> 0.0 in
    jobs := (f, eta) :: !jobs)
  fs;
  let cmp_job (_,t1) (_,t2) = compare t2 t1 in
  jobs := List.sort cmp_job !jobs;
  let pool : Worker.process Pool.t ref = ref Pool.empty in
  let rec filter_argv b = function
    | [] -> []
    | "-schedule-vio2vo" :: rest -> filter_argv true rest
    | s :: rest when String.length s > 0 && s.[0] = '-' && b -> filter_argv false (s :: rest)
    | _ :: rest when b -> filter_argv b rest
    | s :: rest -> s :: filter_argv b rest in
  let prog = Sys.argv.(0) in  
  let stdargs = filter_argv false (List.tl (Array.to_list Sys.argv)) in
  let make_job () =
    let f, t = List.hd !jobs in
    jobs := List.tl !jobs;
    [ "-vio2vo"; f ] in
  let rc = ref 0 in
  while !jobs <> [] || Pool.cardinal !pool > 0 do
    while Pool.cardinal !pool < j && !jobs <> [] do
      let args = Array.of_list (stdargs @ make_job ()) in
      let proc, _, _ = Worker.spawn prog args in
      pool := Pool.add (Worker.unixpid proc) proc !pool;
    done;
    let pid, ret = Unix.wait () in
    if ret <> Unix.WEXITED 0 then rc := 1;
    pool := Pool.remove pid !pool;
  done;
  exit !rc

  
