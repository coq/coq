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
  List.iter (Stm.check_task tasks) ts

let schedule_vi_checking j fs =
  let jobs = ref [] in
  List.iter (fun f ->
    let tasks, long_f_dot_v = Library.load_library_todo f in
    Stm.set_compilation_hints (Aux_file.load_aux_file_for long_f_dot_v);
    let infos = Stm.info_tasks tasks in
    jobs := List.map (fun (name,time,id) -> (f,id),name,time) infos @ !jobs)
    fs;
  let cmp_job (_,_,t1) (_,_,t2) = compare t2 t1 in
  jobs := List.sort cmp_job !jobs;
  let workers = Array.make j (0.0,[]) in
  let cmp_worker (t1,_) (t2,_) = compare t1 t2 in
  while !jobs <> [] do
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
  Array.iter
    (fun (tot, joblist) -> if joblist <> [] then
       let joblist = pack joblist in
       Printf.printf "%s -check-vi-tasks %s & # eta %.2f\n"
         Sys.argv.(0)
         (String.concat " -check-vi-tasks "
           (List.map (fun (f,tl) ->
              let tl = List.map string_of_int tl in
              String.concat "," tl ^ " " ^ f) joblist)) tot)
    workers
