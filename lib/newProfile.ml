(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type settings =
  { file : string
  }

type accu =
  | No
  | File of out_channel

let accu = ref No

let pid = Unix.getpid()

let is_profiling () = !accu <> No

let f fmt = match !accu with
  | No -> assert false
  | File ch -> Printf.fprintf ch fmt

module MiniJson = struct
  type t =
    | String of string
    | Int of string (* string not int so that we can have large ints *)
    | Record of (string * t) list
    | Array of t list

  let rec pr ch = function
    | String s ->
      let s = String.split_on_char '"' s in
      let s = String.concat "\\\"" s in
      Printf.fprintf ch "\"%s\"" s
    | Int s -> Printf.fprintf ch "%s" s
    | Record elts ->
      Printf.fprintf ch "{ %a }" prrecord elts
    | Array elts ->
      Printf.fprintf ch "[\n%a\n]" prarray elts

  and prrecord ch = function
    | [] -> ()
    | [(x,v)] -> Printf.fprintf ch "\"%s\": %a" x pr v
    | (x,v) :: l -> Printf.fprintf ch "\"%s\": %a, %a" x pr v prrecord l

  and prarray ch = function
    | [] -> ()
    | [x] -> pr ch x
    | x :: l -> Printf.fprintf ch "%a,\n%a" pr x prarray l


  let pids = string_of_int pid
  let base = [("pid", Int pids); ("tid", Int pids)]

  let duration ~name ~ph ~ts ?args () =
    let l = ("name", String name) :: ("ph", String ph) :: ("ts", Int ts) :: base in
    let l = match args with
      | None -> l
      | Some args -> ("args", args) :: l
    in
    Record l
end

let prtime () =
  let t = Unix.gettimeofday() in
  Printf.sprintf "%.0f" (t *. 1E6)

let global_start = prtime()
let global_start_stat = Gc.quick_stat()

let duration_gen ?time name ph ?args last () =
  let time = match time with None -> prtime() | Some t -> t in
  f "%a%s\n" MiniJson.pr (MiniJson.duration ~name ~ph ~ts:time ?args ()) last

let duration ?time name ph ?args () = duration_gen ?time name ph ?args "," ()
let enter ?time name ?args () = duration ?time name "B" ?args  ()
let leave ?time name ?args () = duration ?time name "E" ?args ()

let make_mem_diff ~(mstart:Gc.stat) ~(mend:Gc.stat) =
  (* XXX we could use memprof to get sampling stats instead?
     eg stats about how much of the allocation was collected
     in the same span vs how much survived it *)
  let major = mend.major_words -. mstart.major_words in
  let minor = mend.minor_words -. mstart.minor_words in
  let pp tdiff = MiniJson.String (Printf.sprintf "%.3G w" tdiff) in
  MiniJson.Record [("major",pp major); ("minor", pp minor)]

let profile name ?args f () =
  if not (is_profiling ()) then f ()
  else begin
    let args = Option.map (fun f -> f()) args in
    enter name ?args ();
    let mstart = Gc.quick_stat () in
    let v = try f ()
      with e ->
        let e = Exninfo.capture e in
        let mend = Gc.quick_stat () in
        let args = make_mem_diff ~mstart ~mend in
        leave name ~args ();
        Exninfo.iraise e
    in
    let mend = Gc.quick_stat () in
    let args = make_mem_diff ~mstart ~mend in
    leave name ~args ();
    v
  end

let init opts =
  let () = assert (not (is_profiling())) in
  match opts with
  | None ->
    accu := No
  | Some { file } ->
    let ch = open_out file in
    accu := File ch;
    f "{ \"traceEvents\": [\n";
    enter ~time:global_start "process" ();
    enter ~time:global_start "init" ();
    leave "init" ~args:(make_mem_diff ~mstart:global_start_stat ~mend:(Gc.quick_stat())) ()

let finish () = match !accu with
  | No -> ()
  | File ch ->
    duration_gen "process" "E" ""
      ~args:(make_mem_diff ~mstart:global_start_stat ~mend:(Gc.quick_stat()))
      ();
    Printf.fprintf ch "],\n\"displayTimeUnit\": \"us\" }";
    close_out ch

let () = at_exit finish
