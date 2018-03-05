(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let word_length = Sys.word_size / 8

let float_of_time t = float_of_int t /. 100.
let time_of_float f = int_of_float (f *. 100.)

let get_time () =
  time_of_float (Sys.time ())

(* Since ocaml 3.01, gc statistics are in float *)
let get_alloc () =
  (* If you are unlucky, a minor collection can occur between the *)
  (* measurements and produces allocation; we trigger a minor *)
  (* collection in advance to be sure the measure is not corrupted *)
  Gc.minor ();
  Gc.allocated_bytes ()

(* Rem: overhead was 16 bytes in ocaml 3.00 (long int) *)
(* Rem: overhead is 100 bytes in ocaml 3.01 (double) *)

let get_alloc_overhead =
  let mark1 = get_alloc () in
  let mark2 = get_alloc () in
  let mark3 = get_alloc () in
  (* If you are unlucky, a major collection can occur between the *)
  (* measurements; with two measures the risk decreases *)
  min (mark2 -. mark1) (mark3 -. mark2)

let last_alloc = ref 0.0 (* set by init_profile () *)

let spent_alloc () =
  let now = get_alloc () in
  let before = !last_alloc in
  last_alloc := now;
  now -. before -. get_alloc_overhead

(* Profile records *)

type profile_key = {
  mutable owntime : int;
  mutable tottime : int;
  mutable ownalloc : float;
  mutable totalloc : float;
  mutable owncount : int;
  mutable intcount : int;
  mutable immcount : int;
}

let create_record () = {
  owntime=0;
  tottime=0;
  ownalloc=0.0;
  totalloc=0.0;
  owncount=0;
  intcount=0;
  immcount=0
}

let ajoute_totalloc e dw = e.totalloc <- e.totalloc +. dw
let ajoute_ownalloc e dw = e.ownalloc <- e.ownalloc +. dw

let reset_record (n,e) =
  e.owntime <- 0;
  e.tottime <- 0;
  e.ownalloc <- 0.0;
  e.totalloc <- 0.0;
  e.owncount <- 0;
  e.intcount <- 0;
  e.immcount <- 0

(* Profile tables *)

let prof_table = ref []
let stack = ref []
let init_time = ref 0
let init_alloc = ref 0.0

let reset_profile () = List.iter reset_record !prof_table

let init_profile () =
  (* We test Flags.profile as a way to support declaring profiled
     functions in plugins *)
  if !prof_table <> [] || Flags.profile then begin
  let outside = create_record () in
  stack := [outside];
  last_alloc := get_alloc ();
  init_alloc := !last_alloc;
  init_time := get_time ();
  outside.tottime <- - !init_time;
  outside.owntime <- - !init_time
  end

let ajoute n o =
  o.owntime <- o.owntime + n.owntime;
  o.tottime <- o.tottime + n.tottime;
  ajoute_ownalloc o n.ownalloc;
  ajoute_totalloc o n.totalloc;
  o.owncount <- o.owncount + n.owncount;
  o.intcount <- o.intcount + n.intcount;
  o.immcount <- o.immcount + n.immcount

let ajoute_to_list ((name,n) as e) l =
  try ajoute n (List.assoc name l); l
  with Not_found -> e::l

let magic = 1249

let merge_profile filename (curr_table, curr_outside, curr_total as new_data) =
  let (old_table, old_outside, old_total) =
    try
      let c = open_in filename in
      if input_binary_int c <> magic
      then Printf.printf "Incompatible recording file: %s\n" filename;
      let old_data = input_value c in
      close_in c;
      old_data
    with Sys_error msg ->
      (Printf.printf "Unable to open %s: %s\n" filename msg;
       new_data) in
  let updated_data =
    let updated_table = List.fold_right ajoute_to_list curr_table old_table in
    ajoute curr_outside old_outside;
    ajoute curr_total old_total;
    (updated_table, old_outside, old_total) in
  begin
    (try
       let c =
	 open_out_gen
           [Open_creat;Open_wronly;Open_trunc;Open_binary] 0o644 filename in
       output_binary_int c magic;
       output_value c updated_data;
       close_out c
     with Sys_error _ -> Printf.printf "Unable to create recording file");
    updated_data
  end

(************************************************)
(* Compute a rough estimation of time overheads *)

(* Time and space are not measured in the same way *)

(* Byte allocation is an exact number and for long runs, the total
   number of allocated bytes may exceed the maximum integer capacity
   (2^31 on 32-bits architectures);  therefore, allocation is measured
   by small steps, total allocations are computed by adding elementary
   measures and carries are controlled from step to step *)

(* Unix measure of time is approximate and short delays are often
   unperceivable; therefore, total times are measured in one (big)
   step to avoid rounding errors and to get the best possible
   approximation.
   Note: Sys.time is the same as:
     Unix.(let x = times () in x.tms_utime +. x.tms_stime)
 *)

(*
----------        start profile for f1
overheadA|        ...
  ---------- [1w1]  1st call to get_time for f1
  overheadB|        ...
  ----------        start f1
   real 1  |        ...
  ----------        start profile for 1st call to f2 inside f1
  overheadA|        ...
    ---------- [2w1]  1st call to get_time for 1st f2
    overheadB|        ...
    ----------        start 1st f2
     real 2  |        ...
    ----------        end 1st f2
    overheadC|        ...
    ---------- [2w1]  2nd call to get_time for 1st f2
  overheadD|        ...
  ----------        end profile for 1st f2
   real 1  |        ...
  ----------        start profile for 2nd call to f2 inside f1
  overheadA|        ...
    ---------- [2'w1] 1st call to get_time for 2nd f2
    overheadB|        ...
    ----------        start 2nd f2
     real 2' |        ...
    ----------        end 2nd f2
    overheadC|        ...
    ---------- [2'w2]  2nd call to get_time for 2nd f2
  overheadD|        ...
  ----------        end profile for f2
   real 1  |        ...
  ----------        end f1
  overheadC|        ...
---------- [1w1'] 2nd call to get_time for f1
overheadD|        ...
----------        end profile for f1

When profiling f2, overheadB + overheadC should be subtracted from measure
and overheadA + overheadB + overheadC + overheadD should be subtracted from
the amount for f1

Then the relevant overheads are :

  "overheadB + overheadC" to be subtracted to the measure of f as many time as f is called and

  "overheadA + overheadB + overheadC + overheadD" to be subtracted to
  the measure of f as many time as f calls a profiled function (itself
  included)
*)

let dummy_last_alloc = ref 0.0
let dummy_spent_alloc () =
  let now = get_alloc () in
  let before = !last_alloc in
  last_alloc := now;
  now -. before
let dummy_f x = x
let dummy_stack = ref [create_record ()]
let dummy_ov = 0

let loops = 10000

let time_overhead_A_D () =
  let e = create_record () in
  let before = get_time () in
  for _i = 1 to loops do
    (* This is a copy of profile1 for overhead estimation *)
    let dw = dummy_spent_alloc () in
    match !dummy_stack with [] -> assert false | p::_ ->
      ajoute_ownalloc p dw;
      ajoute_totalloc p dw;
      e.owncount <- e.owncount + 1;
      if not (p==e) then stack := e::!stack;
      let totalloc0 = e.totalloc in
      let intcount0 = e.intcount in
      let dt = get_time () - 1 in
      e.tottime <- dt + dummy_ov; e.owntime <- e.owntime + e.tottime;
      ajoute_ownalloc p dw;
      ajoute_totalloc p dw;
      p.owntime <- p.owntime - e.tottime;
      ajoute_totalloc p (e.totalloc-.totalloc0);
      p.intcount <- p.intcount + e.intcount - intcount0 + 1;
      p.immcount <- p.immcount + 1;
      if not (p==e) then
	(match !dummy_stack with [] -> assert false | _::s -> stack := s);
      dummy_last_alloc := get_alloc ()
  done;
  let after = get_time () in
  let beforeloop =  get_time () in
  for _i = 1 to loops do () done;
  let afterloop = get_time () in
  float_of_int ((after - before) - (afterloop - beforeloop))
  /. float_of_int loops

let time_overhead_B_C () =
  let dummy_x = 0 in
  let before = get_time () in
  for _i = 1 to loops do
    try
      dummy_last_alloc := get_alloc ();
      let _r = dummy_f dummy_x in
      let _dw = dummy_spent_alloc () in
      let _dt = get_time () in
      ()
    with e when CErrors.noncritical e -> assert false
  done;
  let after = get_time () in
  let beforeloop =  get_time () in
  for _i = 1 to loops do () done;
  let afterloop = get_time () in
  float_of_int ((after - before) - (afterloop - beforeloop))
  /. float_of_int loops

let compute_alloc lo = lo /. (float_of_int word_length)

(************************************************)
(* End a profiling session and print the result *)

let format_profile (table, outside, total) =
  print_newline ();
  Printf.printf
    "%-23s  %9s %9s %10s %10s %10s\n"
    "Function name" "Own time" "Tot. time" "Own alloc" "Tot. alloc" "Calls ";
  let l = List.sort (fun (_,{tottime=p}) (_,{tottime=p'}) -> p' - p) table in
  List.iter (fun (name,e) ->
    Printf.printf
      "%-23s %9.2f %9.2f %10.0f %10.0f %6d %6d\n"
      name
      (float_of_time e.owntime) (float_of_time e.tottime)
      (compute_alloc e.ownalloc)
      (compute_alloc e.totalloc)
      e.owncount e.intcount)
    l;
  Printf.printf "%-23s %9.2f %9.2f %10.0f %10.0f        %6d\n"
    "others"
    (float_of_time outside.owntime) (float_of_time outside.tottime)
    (compute_alloc outside.ownalloc)
    (compute_alloc outside.totalloc)
    outside.intcount;
  (* Here, own contains overhead time/alloc *)
  Printf.printf "%-23s %9.2f %9.2f %10.0f %10.0f\n"
    "Est. overhead/total"
    (float_of_time total.owntime) (float_of_time total.tottime)
    (compute_alloc total.ownalloc)
    (compute_alloc total.totalloc);
  Printf.printf
    "Time in seconds and allocation in words (1 word = %d bytes)\n"
    word_length

let recording_file = ref ""
let set_recording s = recording_file := s

let adjust_time ov_bc ov_ad e =
  let bc_imm = float_of_int e.owncount *. ov_bc in
  let ad_imm = float_of_int e.immcount *. ov_ad in
  let abcd_all = float_of_int e.intcount *. (ov_ad +. ov_bc) in
  {e with
     tottime = e.tottime - int_of_float (abcd_all +. bc_imm);
     owntime = e.owntime - int_of_float (ad_imm +. bc_imm) }

let close_profile print =
  if !prof_table <> [] then begin
      let dw = spent_alloc () in
      let t = get_time () in
      match !stack with
      | [outside] ->
	  outside.tottime <- outside.tottime + t;
	  outside.owntime <- outside.owntime + t;
	  ajoute_ownalloc outside dw;
	  ajoute_totalloc outside dw;
	  let ov_bc = time_overhead_B_C () (* B+C overhead *) in
	  let ov_ad = time_overhead_A_D () (* A+D overhead *) in
	  let adjust (n,e) = (n, adjust_time ov_bc ov_ad e) in
	  let adjtable = List.map adjust !prof_table in
	  let adjoutside = adjust_time ov_bc ov_ad outside in
	  let totalloc = !last_alloc -. !init_alloc in
	  let total = create_record () in
	  total.tottime <- outside.tottime;
	  total.totalloc <- totalloc;
	  (* We compute estimations of overhead, put into "own" fields *)
	  total.owntime <- outside.tottime - adjoutside.tottime;
	  total.ownalloc <- totalloc -. outside.totalloc;
	  let current_data = (adjtable, adjoutside, total) in
	  let updated_data =
	    match !recording_file with
	      |	"" -> current_data
	      | name -> merge_profile !recording_file current_data
	  in
	  if print then format_profile updated_data;
	  init_profile ()
      | _ -> failwith "Inconsistency"
    end

let print_profile () = close_profile true

let declare_profile name =
  if name = "___outside___" || name = "___total___" then
    failwith ("Error: "^name^" is a reserved keyword");
  let e = create_record () in
  prof_table := (name,e)::!prof_table;
  e

(******************************)
(* Entry points for profiling *)
let profile1 e f a =
  let dw = spent_alloc () in
  match !stack with [] -> assert false | p::_ ->
  (* We add spent alloc since last measure to current caller own/total alloc *)
  ajoute_ownalloc p dw;
  ajoute_totalloc p dw;
  e.owncount <- e.owncount + 1;
  if not (p==e) then stack := e::!stack;
  let totalloc0 = e.totalloc in
  let intcount0 = e.intcount in
  let t = get_time () in
  try
    last_alloc := get_alloc ();
    let r = f a in
    let dw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e dw;
    ajoute_totalloc e dw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.totalloc -. totalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    r
  with reraise ->
    let dw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e dw;
    ajoute_totalloc e dw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.totalloc -. totalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    raise reraise

let profile2 e f a b =
  let dw = spent_alloc () in
  match !stack with [] -> assert false | p::_ ->
  (* We add spent alloc since last measure to current caller own/total alloc *)
  ajoute_ownalloc p dw;
  ajoute_totalloc p dw;
  e.owncount <- e.owncount + 1;
  if not (p==e) then stack := e::!stack;
  let totalloc0 = e.totalloc in
  let intcount0 = e.intcount in
  let t = get_time () in
  try
    last_alloc := get_alloc ();
    let r = f a b in
    let dw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e dw;
    ajoute_totalloc e dw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.totalloc -. totalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    r
  with reraise ->
    let dw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e dw;
    ajoute_totalloc e dw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.totalloc -. totalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    raise reraise

let profile3 e f a b c =
  let dw = spent_alloc () in
  match !stack with [] -> assert false | p::_ ->
  (* We add spent alloc since last measure to current caller own/total alloc *)
  ajoute_ownalloc p dw;
  ajoute_totalloc p dw;
  e.owncount <- e.owncount + 1;
  if not (p==e) then stack := e::!stack;
  let totalloc0 = e.totalloc in
  let intcount0 = e.intcount in
  let t = get_time () in
  try
    last_alloc := get_alloc ();
    let r = f a b c in
    let dw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e dw;
    ajoute_totalloc e dw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.totalloc -. totalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    r
  with reraise ->
    let dw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e dw;
    ajoute_totalloc e dw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.totalloc -. totalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    raise reraise

let profile4 e f a b c d =
  let dw = spent_alloc () in
  match !stack with [] -> assert false | p::_ ->
  (* We add spent alloc since last measure to current caller own/total alloc *)
  ajoute_ownalloc p dw;
  ajoute_totalloc p dw;
  e.owncount <- e.owncount + 1;
  if not (p==e) then stack := e::!stack;
  let totalloc0 = e.totalloc in
  let intcount0 = e.intcount in
  let t = get_time () in
  try
    last_alloc := get_alloc ();
    let r = f a b c d in
    let dw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e dw;
    ajoute_totalloc e dw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.totalloc -. totalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    r
  with reraise ->
    let dw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e dw;
    ajoute_totalloc e dw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.totalloc -. totalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    raise reraise

let profile5 e f a b c d g =
  let dw = spent_alloc () in
  match !stack with [] -> assert false | p::_ ->
  (* We add spent alloc since last measure to current caller own/total alloc *)
  ajoute_ownalloc p dw;
  ajoute_totalloc p dw;
  e.owncount <- e.owncount + 1;
  if not (p==e) then stack := e::!stack;
  let totalloc0 = e.totalloc in
  let intcount0 = e.intcount in
  let t = get_time () in
  try
    last_alloc := get_alloc ();
    let r = f a b c d g in
    let dw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e dw;
    ajoute_totalloc e dw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.totalloc -. totalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    r
  with reraise ->
    let dw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e dw;
    ajoute_totalloc e dw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.totalloc -. totalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    raise reraise

let profile6 e f a b c d g h =
  let dw = spent_alloc () in
  match !stack with [] -> assert false | p::_ ->
  (* We add spent alloc since last measure to current caller own/total alloc *)
  ajoute_ownalloc p dw;
  ajoute_totalloc p dw;
  e.owncount <- e.owncount + 1;
  if not (p==e) then stack := e::!stack;
  let totalloc0 = e.totalloc in
  let intcount0 = e.intcount in
  let t = get_time () in
  try
    last_alloc := get_alloc ();
    let r = f a b c d g h in
    let dw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e dw;
    ajoute_totalloc e dw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.totalloc -. totalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    r
  with reraise ->
    let dw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e dw;
    ajoute_totalloc e dw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.totalloc -. totalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    raise reraise

let profile7 e f a b c d g h i =
  let dw = spent_alloc () in
  match !stack with [] -> assert false | p::_ ->
  (* We add spent alloc since last measure to current caller own/total alloc *)
  ajoute_ownalloc p dw;
  ajoute_totalloc p dw;
  e.owncount <- e.owncount + 1;
  if not (p==e) then stack := e::!stack;
  let totalloc0 = e.totalloc in
  let intcount0 = e.intcount in
  let t = get_time () in
  try
    last_alloc := get_alloc ();
    let r = f a b c d g h i in
    let dw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e dw;
    ajoute_totalloc e dw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.totalloc -. totalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    r
  with reraise ->
    let dw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e dw;
    ajoute_totalloc e dw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.totalloc -. totalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    raise reraise

let profile8 e f a b c d g h i j =
  let dw = spent_alloc () in
  match !stack with [] -> assert false | p::_ ->
  (* We add spent alloc since last measure to current caller own/total alloc *)
  ajoute_ownalloc p dw;
  ajoute_totalloc p dw;
  e.owncount <- e.owncount + 1;
  if not (p==e) then stack := e::!stack;
  let totalloc0 = e.totalloc in
  let intcount0 = e.intcount in
  let t = get_time () in
  try
    last_alloc := get_alloc ();
    let r = f a b c d g h i j in
    let dw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e dw;
    ajoute_totalloc e dw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.totalloc -. totalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    r
  with reraise ->
    let dw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e dw;
    ajoute_totalloc e dw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.totalloc -. totalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    raise reraise

let print_logical_stats a =
  let (c, s, d) = CObj.obj_stats a in
  Printf.printf "Expanded size: %10d (str: %8d) Depth: %6d\n" (s+c) c d

let print_stats a =
  let (c1, s, d) = CObj.obj_stats a in
  let c2 = CObj.size a in
  Printf.printf "Size: %8d (exp: %10d)  Depth: %6d\n"
    c2 (s + c1) d
(*
let _ = Gc.set { (Gc.get()) with Gc.verbose = 13 }
*)
