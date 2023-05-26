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
      | Some args -> ("args", Record args) :: l
    in
    Record l
end

let gettime = Unix.gettimeofday

let gettimeopt = function
  | Some t -> t
  | None -> gettime()

let prtime t =
  Printf.sprintf "%.0f" (t *. 1E6)

let global_start = gettime()
let global_start_stat = Gc.quick_stat()

let duration ~time name ph ?args ?(last=",") () =
  f "%a%s\n" MiniJson.pr (MiniJson.duration ~name ~ph ~ts:(prtime time) ?args ()) last

let sums = ref []

let enter ?time name ?args ?last () =
  let time = gettimeopt time in
  sums := (time, CString.Map.empty) :: !sums;
  duration ~time name "B" ?args ?last ()

let leave ?time name ?(args=[]) ?last () =
  let time = gettimeopt time in
  let sum = match !sums with
    | [] -> assert false
    | [_,sum] -> sum
    | (start, sum) :: (start', next) :: rest ->
      let dur = time -. start in
      let next = CString.Map.update name (function
          | None -> Some (dur, 1)
          | Some (dur', cnt) -> Some (dur +. dur', cnt+1))
          next
      in
      let next = CString.Map.union (fun name' (l,cnt) (r,cnt') ->
          if String.equal name name' then Some (r,cnt+cnt')
          else Some (l +. r, cnt+cnt'))
          sum next
      in
      sums := (start', next) :: rest;
      sum
  in
  let sum = List.map (fun (name, (t, cnt)) ->
      name, MiniJson.String
        (Printf.sprintf "%.3G us, %d %s" (t *. 1E6) cnt (CString.plural cnt "call")))
      (CString.Map.bindings sum)
  in
  let args = ("subtimes", MiniJson.Record sum) :: args in
  duration ~time name "E" ~args ?last ()

let make_mem_diff ~(mstart:Gc.stat) ~(mend:Gc.stat) =
  (* XXX we could use memprof to get sampling stats instead?
     eg stats about how much of the allocation was collected
     in the same span vs how much survived it *)
  let major = mend.major_words -. mstart.major_words in
  let minor = mend.minor_words -. mstart.minor_words in
  let pp tdiff = MiniJson.String (Printf.sprintf "%.3G w" tdiff) in
  [("major",pp major); ("minor", pp minor)]

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
    leave "process"
      ~last:""
      ~args:(make_mem_diff ~mstart:global_start_stat ~mend:(Gc.quick_stat()))
      ();
    Printf.fprintf ch "],\n\"displayTimeUnit\": \"us\" }";
    close_out ch

let () = at_exit finish
