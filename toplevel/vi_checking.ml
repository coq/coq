(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let check_vi (ts,f) =
  Dumpglob.noglob ();
  let tasks, long_f_dot_v = Library.load_library_todo f in
  Stm.set_compilation_hints (Aux_file.load_aux_file_for long_f_dot_v);
  List.iter (Stm.check_task f tasks) ts

let schedule_vi_checking j fs =
  if j < 1 then Errors.error "The number of workers must be bigger than 0";
  let jobs = ref [] in
  List.iter (fun f ->
    let f =
      if Filename.check_suffix f ".vi" then Filename.chop_extension f
      else f in
    let tasks, long_f_dot_v = Library.load_library_todo f in
    Stm.set_compilation_hints (Aux_file.load_aux_file_for long_f_dot_v);
    let infos = Stm.info_tasks tasks in
    jobs := List.map (fun (name,time,id) -> (f,id),name,time) infos @ !jobs)
    fs;
  let cmp_job (_,_,t1) (_,_,t2) = compare t2 t1 in
  jobs := List.sort cmp_job !jobs;
  let workers = Array.make j (0.0,[]) in
  let cmp_worker (t1,_) (t2,_) = compare t1 t2 in
  if j = 1 then
     workers.(0) <- List.fold_left (fun acc (_,_,t) -> acc +. t) 0.0 !jobs, !jobs
  else while !jobs <> [] do
    Array.sort cmp_worker workers;
    for i=0 to j-2 do
      while !jobs <> [] && fst workers.(i) <= fst workers.(i+1) do
        let ((f,id),_,t as job) = List.hd !jobs in
        let rest = List.tl !jobs in
        let tot, joblist = workers.(i) in
        workers.(i) <- tot +. t, job::joblist;
        jobs := rest
      done
    done;
  done;
  for i=0 to j-1 do
    let tot, joblist = workers.(i) in
    let cmp_job (f1,_,_) (f2,_,_) = compare f1 f2 in
    workers.(i) <- tot, List.sort cmp_job joblist
  done;
  let pack = function
    | [] -> []
    | ((f,_),_,_) :: _ as l ->
        let rec aux last acc = function
          | [] -> [last,acc]
          | ((f',id),_,_) :: tl when last = f' -> aux last (id::acc) tl
          | ((f',id),_,_) :: _ as l -> (last,acc) :: aux f' [] l in
        aux f [] l in
  let prog =
    let rec filter_argv b = function
      | [] -> []
      | "-schedule-vi-checking" :: rest -> filter_argv true rest
      | s :: rest when s.[0] = '-' && b -> filter_argv false (s :: rest)
      | _ :: rest when b -> filter_argv b rest
      | s :: rest -> s :: filter_argv b rest in
    String.concat " " (filter_argv false (Array.to_list Sys.argv)) in
  Printf.printf "#!/bin/sh\n";
  Array.iter (fun (tot, joblist) -> if joblist <> [] then
    let joblist = pack joblist in
    Printf.printf "( %s ) &\n"
      (String.concat "; "
        (List.map (fun tasks -> Printf.sprintf "%s -check-vi-tasks %s " prog tasks)
          (List.map (fun (f,tl) ->
             let tl = List.map string_of_int tl in
             String.concat "," tl ^ " " ^ f) joblist))))
    workers;
  Printf.printf "wait\n"

