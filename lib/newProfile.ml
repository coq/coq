(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module MiniJson = struct
  type t =[
    | `Intlit of string
    | `String of string
    | `Assoc of (string * t) list
    | `List of t list
  ]

  let rec pr ch : t -> _ = function
    | `String s ->
      let s = String.split_on_char '"' s in
      let s = String.concat "\\\"" s in
      Format.fprintf ch "\"%s\"" s
    | `Intlit s -> Format.fprintf ch "%s" s
    | `Assoc elts ->
      Format.fprintf ch "{ %a }" prrecord elts
    | `List elts ->
      Format.fprintf ch "[\n%a\n]" prarray elts

  and prrecord ch = function
    | [] -> ()
    | [(x,v)] -> Format.fprintf ch "\"%s\": %a" x pr v
    | (x,v) :: l -> Format.fprintf ch "\"%s\": %a, %a" x pr v prrecord l

  and prarray ch = function
    | [] -> ()
    | [x] -> pr ch x
    | x :: l -> Format.fprintf ch "%a,\n%a" pr x prarray l


  let pid = Unix.getpid()

  let pids = string_of_int pid
  let base = [("pid", `Intlit pids); ("tid", `Intlit pids)]

  let duration ~name ~ph ~ts ?args () =
    let l = ("name", `String name) :: ("ph", `String ph) :: ("ts", `Intlit ts) :: base in
    let l = match args with
      | None -> l
      | Some args -> ("args", `Assoc args) :: l
    in
    `Assoc l
end

type accu = {
  ch : Format.formatter;
  mutable sums : (float * (float * int) CString.Map.t) list;
}

let accu = ref None

let is_profiling () = Option.has_some !accu

let f fmt = match !accu with
  | None -> assert false
  | Some { ch } -> Format.fprintf ch fmt

let gettime = Unix.gettimeofday

let gettimeopt = function
  | Some t -> t
  | None -> gettime()

let prtime t =
  Format.sprintf "%.0f" (t *. 1E6)

let global_start = gettime()
let global_start_stat = Gc.quick_stat()

let duration ~time name ph ?args ?(last=",") () =
  f "%a%s\n%!" MiniJson.pr (MiniJson.duration ~name ~ph ~ts:(prtime time) ?args ()) last

let enter_sums ?time () =
  let accu = Option.get !accu in
  let time = gettimeopt time in
  accu.sums <- (time, CString.Map.empty) :: accu.sums

let enter ?time name ?args () =
  let time = gettimeopt time in
  enter_sums ~time ();
  duration ~time name "B" ?args ()

let leave_sums ?time name () =
  let accu = Option.get !accu in
  let time = gettimeopt time in
  match accu.sums with
  | [] -> assert false
  | [start,sum] -> accu.sums <- []; sum, time -. start
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
   accu. sums <- (start', next) :: rest;
    sum, dur

let leave ?time name ?(args=[]) ?last () =
  let time = gettimeopt time in
  let sum, dur = leave_sums ~time name () in
  let sum = List.map (fun (name, (t, cnt)) ->
      name, `String
        (Format.sprintf "%.3G us, %d %s" (t *. 1E6) cnt (CString.plural cnt "call")))
      (CString.Map.bindings sum)
  in
  let args = ("subtimes", `Assoc sum) :: args in
  duration ~time name "E" ~args ?last ()

let make_mem_diff ~(mstart:Gc.stat) ~(mend:Gc.stat) =
  (* XXX we could use memprof to get sampling stats instead?
     eg stats about how much of the allocation was collected
     in the same span vs how much survived it *)
  let major = mend.major_words -. mstart.major_words in
  let minor = mend.minor_words -. mstart.minor_words in
  let pp tdiff = `String (Format.sprintf "%.3G w" tdiff) in
  [("major",pp major); ("minor", pp minor)]

(* NB: "process" and "init" are unconditional because they don't go
   through [profile] and I'm too lazy to make them conditional *)
let components =
  match Sys.getenv_opt "COQ_PROFILE_COMPONENTS" with
  | None -> CString.Pred.full
  | Some s ->
    List.fold_left (fun cs c -> CString.Pred.add c cs)
      CString.Pred.empty
      (String.split_on_char ',' s)

let profile name ?args f () =
  if not (is_profiling ()) then f ()
  else if CString.Pred.mem name components then begin
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
  else begin
    enter_sums ();
    let v = try f ()
      with e ->
        let e = Exninfo.capture e in
        ignore (leave_sums name () : _ * _);
        Exninfo.iraise e
    in
    ignore (leave_sums name () : _ * _);
    v
  end

type settings =
  { output : Format.formatter
  }

let init { output } =
  let () = assert (not (is_profiling())) in
  accu := Some { ch = output; sums = [] };
  f "{ \"traceEvents\": [\n";
  enter ~time:global_start "process" ();
  enter ~time:global_start "init" ();
  leave "init" ~args:(make_mem_diff ~mstart:global_start_stat ~mend:(Gc.quick_stat())) ()

let pause () =
  let v = !accu in
  accu := None;
  v

let resume v =
  assert (not (is_profiling()));
  accu := Some v

let finish () = match !accu with
  | None -> assert false
  | Some { ch } ->
    leave "process"
      ~last:""
      ~args:(make_mem_diff ~mstart:global_start_stat ~mend:(Gc.quick_stat()))
      ();
    Format.fprintf ch "],\n\"displayTimeUnit\": \"us\" }\n%!";
    accu := None
