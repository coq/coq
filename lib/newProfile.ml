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

  (* https://www.ietf.org/rfc/rfc4627.txt *)
  (* https://github.com/ocaml-community/yojson/blob/4c1d4b52f9e87a4bd3b7f26111e8a4976c1e8676/lib/write.ml#L27 *)
  let prstring ch s =
    let buf = Buffer.create (String.length s) in
    let encode c =
      match c with
      | '"' -> Buffer.add_string buf "\\\""
      | '\\' -> Buffer.add_string buf "\\\\"
      | '\b' -> Buffer.add_string buf "\\b"
      | '\012' -> Buffer.add_string buf "\\f"
      | '\n' -> Buffer.add_string buf "\\n"
      | '\r' -> Buffer.add_string buf "\\r"
      | '\t' -> Buffer.add_string buf "\\t"
      | '\x00'..'\x1F'
      | '\x7F' ->
          Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
      | _ -> Buffer.add_char buf c
    in
    String.iter encode s;
    Format.fprintf ch "\"%s\"" (Buffer.contents buf)

  let rec pr ch : t -> _ = function
    | `String s -> prstring ch s
    | `Intlit s -> Format.fprintf ch "%s" s
    | `Assoc elts ->
      Format.fprintf ch "{ %a }" prrecord elts
    | `List elts ->
      Format.fprintf ch "[\n%a\n]" prarray elts

  and prrecord ch = function
    | [] -> ()
    | [(x,v)] -> Format.fprintf ch "%a: %a" prstring x pr v
    | (x,v) :: l -> Format.fprintf ch "%a: %a, %a" prstring x pr v prrecord l

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

type sums = (float * int) CString.Map.t

type accu = {
  output : Format.formatter option;
  accumulate : MiniJson.t list ref option;
  mutable sums : (float * sums) list;
}

let accu = ref None

let is_profiling () = Option.has_some !accu

let gettime = Unix.gettimeofday

let gettimeopt = function
  | Some t -> t
  | None -> gettime()

let prtime t =
  Format.sprintf "%.0f" (t *. 1E6)

module Counters = struct

  (* time is handled separately because it has special status in the output format *)
  type t = {
    major_words : float;
    minor_words : float;
    major_collections : int;
    minor_collections : int;
    instr : System.instruction_count;
  }

  let get () =
    let gc = Gc.quick_stat() in
    {
      major_words = gc.major_words;
      minor_words = gc.minor_words;
      major_collections = gc.major_collections;
      minor_collections = gc.minor_collections;
      instr = Instr.read_counter();
    }

  let global_start = get ()

  let (-) b a = {
    major_words = b.major_words -. a.major_words;
    minor_words = b.minor_words -. a.minor_words;
    major_collections = b.major_collections - a.major_collections;
    minor_collections = b.minor_collections - a.minor_collections;
    instr = System.instructions_between ~c_start:a.instr ~c_end:b.instr;
  }

  let format x =
    let ppf tdiff = `String (Format.sprintf "%.3G w" tdiff) in
    let ppi i = `Intlit (string_of_int i) in
    let instr = match x.instr with
      | Ok count -> [("instr", `Intlit (Int64.to_string count))]
      | Error _ -> []
    in
    ("major_words",ppf x.major_words) ::
    ("minor_words", ppf x.minor_words) ::
    ("major_collect", ppi x.major_collections) ::
    ("minor_collect", ppi x.minor_collections) ::
    instr

  let make_diffs ~start ~stop = format (stop - start)

end

let global_start_time = gettime ()

let output_event json ?(last=",") () =
  let accu = Option.get !accu in
  accu.output |> Option.iter (fun ch ->
      Format.fprintf ch "%a%s\n" MiniJson.pr json last);
  accu.accumulate |> Option.iter (fun out ->
      out := json :: !out)

let duration ~time name ph ?args ?last () =
  let duration = MiniJson.duration ~name ~ph ~ts:(prtime time) ?args () in
  output_event duration ?last ()

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

let rec pptime fmt t = let open Format in function
  | [] -> assert false
  | [unit] ->
    if t >= 1. then fprintf fmt "%03.0f%s" t unit
    else fprintf fmt "0%s" unit
  | unit :: nextunit :: rest ->
    (* float t is time in [unit] *)
    if t >= 1. then fprintf fmt "%03.0f%s %03.0f%s" t unit (Float.rem (t *. 1_000.) 1_000.) nextunit
    else pptime fmt (t *. 1_000.) (nextunit :: rest)

let pptime fmt t = pptime fmt t ["s";"ms";"us";"ns"]

let leave ?time name ?(args=[]) ?last () =
  let time = gettimeopt time in
  let sum, dur = leave_sums ~time name () in
  let sum = CString.Map.bindings sum in
  let sum = List.sort (fun (_,(t1,_)) (_,(t2,_)) -> Float.compare t2 t1) sum in
  let sum = List.map (fun (name, (t, cnt)) ->
      name, `String
        (Format.asprintf "%a, %d %s" pptime t cnt (CString.plural cnt "call")))
      sum
  in
  let args = ("subtimes", `Assoc sum) :: args in
  duration ~time name "E" ~args ?last ()

(* NB: "process" and "init" are unconditional because they don't go
   through [profile] and I'm too lazy to make them conditional *)
let components =
  match Sys.getenv_opt "COQ_PROFILE_COMPONENTS" with
  | None -> CString.Pred.(full |> remove "unification" |> remove "Conversion")
  | Some s ->
    List.fold_left (fun cs c -> CString.Pred.add c cs)
      CString.Pred.empty
      (String.split_on_char ',' s)

let profile name ?args f =
  if not (is_profiling ()) then f ()
  else if CString.Pred.mem name components then begin
    let args = Option.map (fun f -> f()) args in
    enter name ?args ();
    let start = Counters.get () in
    let v = try f ()
      with e ->
        let e = Exninfo.capture e in
        let args = Counters.make_diffs ~start ~stop:(Counters.get()) in
        leave name ~args ();
        Exninfo.iraise e
    in
    let args = Counters.make_diffs ~start ~stop:(Counters.get()) in
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
  { output : Format.formatter;
    fname : string;
  }

let init { output; fname; } =
  let () = assert (not (is_profiling())) in
  accu := Some { output = Some output; accumulate = None; sums = []; };
  Format.fprintf output "{ \"traceEvents\": [\n";
  enter ~time:global_start_time ~args:["fname", `String fname] "process" ();
  enter ~time:global_start_time "init" ();
  let args = Counters.(make_diffs ~start:global_start ~stop:(get())) in
  leave "init" ~args ()

let pause () =
  let v = !accu in
  accu := None;
  v

let resume v =
  assert (not (is_profiling()));
  accu := Some v

let finish () = match !accu with
  | None | Some { output = None } -> assert false
  | Some { output = Some ch } ->
    let args = Counters.(make_diffs ~start:global_start ~stop:(get())) in
    leave "process" ~last:"" ~args ();
    Format.fprintf ch "],\n\"displayTimeUnit\": \"us\" }@.";
    accu := None

let insert_sums sums =
  let accu = Option.get !accu in
  match accu.sums with
  | [] -> assert false
  | (start, sums') :: rest ->
    let sums = CString.Map.union (fun _name (l,cnt) (r,cnt') ->
        Some (l +. r, cnt + cnt'))
        sums sums'
    in
    accu.sums <- (start, sums) :: rest

let insert_results events sums =
  List.iter (fun e -> output_event e ()) events;
  insert_sums sums

let with_profiling f =
  let out = ref [] in
  let this_accu, old_accu = match !accu with
    | None ->
      { output = None;
        accumulate = Some out;
        sums = [0., CString.Map.empty];
      }
    , None
    | Some accu ->
      { output = accu.output;
        accumulate = Some out;
        sums = [0., CString.Map.empty];
      }
      , Some accu
  in
  let finally () =
    let out = List.rev !out in
    let sums = match this_accu.sums with
      | [_, x] -> x
      | _ -> assert false
    in
    accu := old_accu;
    let () = match old_accu with
      | None -> ()
      | Some accu ->
        (* events have already been output to the formatter if there is one *)
        accu.accumulate |> Option.iter (fun accumulate ->
            accumulate := List.rev_append out !accumulate);
        insert_sums sums
    in
    out, sums
  in
  accu := Some this_accu;
  let v = try f () with e ->
    let e = Exninfo.capture e in
    ignore (finally() : _ * _);
    Exninfo.iraise e
  in

  let out, sums = finally () in

  out, sums, v
