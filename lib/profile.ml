
(* $Id$ *)

open Gc

let word_length = Sys.word_size / 8
let int_size = Sys.word_size - 1
let int_range = -2 * (1 lsl (int_size - 1))

let float_of_time t = float_of_int t /. 100.
let time_of_float f = int_of_float (f *. 100.)

let get_time () =
  let  {Unix.tms_utime = ut;Unix.tms_stime = st} = Unix.times () in
  time_of_float (ut +. st)

let get_alloc () = Gc.allocated_bytes ()

let get_alloc_overhead =
  let now = get_alloc () in
  let after = get_alloc () in
  after - now                    (* Rem: overhead is 16 bytes in ocaml 3.00 *)

let last_alloc = ref 0
let carry_alloc = ref 0

let spent_alloc () =
  let w = get_alloc () in
  let dw = w - !last_alloc in
  let n,dw =
    if dw >= 0 then (0, dw) else (incr carry_alloc; (1, dw+int_range)) in
  last_alloc := w;
  n, dw - get_alloc_overhead

(* Profile records *)

type profile_key = {
  mutable owntime : int;
  mutable tottime : int;
  mutable hiownalloc : int;
  mutable loownalloc : int;
  mutable hitotalloc : int;
  mutable lototalloc : int;
  mutable owncount : int;
  mutable intcount : int;
  mutable immcount : int;
}

let create_record () = {
  owntime=0;
  tottime=0;
  hiownalloc=0;
  loownalloc=0;
  hitotalloc=0;
  lototalloc=0;
  owncount=0;
  intcount=0;
  immcount=0
}

let ajoute_totalloc e hidw lodw =
  let s = e.lototalloc + lodw in
  e.hitotalloc <- e.hitotalloc + hidw;
  e.lototalloc <- s;
  if s < 0 then begin
    e.lototalloc <- e.lototalloc + int_range;
    e.hitotalloc <- e.hitotalloc + 1
  end

let ajoute_ownalloc e hidw lodw =
  let s = e.loownalloc + lodw in
  e.hiownalloc <- e.hiownalloc + hidw;
  e.loownalloc <- s;
  if s < 0 then begin
    e.loownalloc <- e.loownalloc + int_range;
    e.hiownalloc <- e.hiownalloc + 1
  end

let reset_record (n,e) =
  e.owntime <- 0;
  e.tottime <- 0;
  e.hiownalloc <- 0;
  e.loownalloc <- 0;
  e.hitotalloc <- 0;
  e.lototalloc <- 0;
  e.owncount <- 0;
  e.intcount <- 0;
  e.immcount <- 0

(* Profile tables *)

let prof_table = ref []
let stack = ref []
let init_time = ref 0
let init_alloc = ref 0

let reset_profile () = List.iter reset_record !prof_table

let init_profile () =
  prof_table :=[];
  let outside = create_record () in
  stack := [outside];
  last_alloc := get_alloc ();
  init_alloc := !last_alloc;
  init_time := get_time ();
  outside.tottime <- - !init_time;
  outside.owntime <- - !init_time

let ajoute n o =
  o.owntime <- o.owntime + n.owntime;
  o.tottime <- o.tottime + n.tottime;
  ajoute_ownalloc o n.hiownalloc n.loownalloc;
  ajoute_totalloc o n.hitotalloc n.lototalloc;
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
   (2^31 on 32-bits architectures); therefore, allocation is measured
   by small steps, total allocations are computed by adding elementary
   measures and carries are controled from step to step *)

(* Unix measure of time is approximative and short delays are often
   unperceivable; therefore, total times are measured in one (big)
   step to avoid rounding errors and to get the best possible
   approximation *)

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

let dummy_last_alloc = ref 0
let dummy_spent_alloc () =
  let w = get_alloc () in
  let dw = w - !dummy_last_alloc in
  let n,dw = if dw >= 0 then (0, dw) else (1, dw+int_range) in
  dummy_last_alloc := w;
  n, dw - get_alloc_overhead
let dummy_f x = x
let dummy_stack = ref [create_record ()]
let dummy_ov = 0

let time_overhead_A_D () =
  let e = create_record () in
  let n = 100000 in
  let before = get_time () in
  for i=1 to n do
    (* This is a copy of profile1 for overhead estimation *)
    let hidw,lodw = dummy_spent_alloc () in
    match !dummy_stack with [] -> assert false | p::_ ->
      ajoute_ownalloc p hidw lodw;
      ajoute_totalloc p hidw lodw;
      e.owncount <- e.owncount + 1;
      if not (p==e) then stack := e::!stack;
      let hitotalloc0,lototalloc0 = e.hitotalloc,e.lototalloc in
      let intcount0 = e.intcount in
      let dt = get_time () - 1 in
      e.tottime <- dt + dummy_ov; e.owntime <- e.owntime + e.tottime;
      ajoute_ownalloc p hidw lodw;
      ajoute_totalloc p hidw lodw;
      p.owntime <- p.owntime - e.tottime;
      ajoute_totalloc p (e.hitotalloc-hitotalloc0) (e.lototalloc-lototalloc0);
      p.intcount <- p.intcount + e.intcount - intcount0 + 1;
      p.immcount <- p.immcount + 1;
      if not (p==e) then 
	(match !dummy_stack with [] -> assert false | _::s -> stack := s);
      dummy_last_alloc := get_alloc ()
  done;
  let after = get_time () in
  let beforeloop =  get_time () in
  for i=1 to n do () done;
  let afterloop = get_time () in
  float_of_int ((after - before) - (afterloop - beforeloop)) /. float_of_int n

let time_overhead_B_C () =
  let dummy_x = 0 in
  let n = 100000 in
  let before = get_time () in
  for i=1 to n do
    try
      dummy_last_alloc := get_alloc ();
      let r = dummy_f dummy_x in
      let hidw,lodw = dummy_spent_alloc () in
      let dt = get_time () in
      ()
    with _ -> assert false
  done;
  let after = get_time () in
  let beforeloop =  get_time () in
  for i=1 to n do () done;
  let afterloop = get_time () in
  float_of_int ((after - before) - (afterloop - beforeloop)) /. float_of_int n

let compute_alloc hi lo =
  ((float_of_int hi) *. (float_of_int int_range) +. (float_of_int lo))
  /. (float_of_int word_length)

(************************************************)
(* End a profiling session and print the result *)

let format_profile (table, outside, total) =
  print_newline ();
  Printf.printf 
    "%-23s  %9s %9s %10s %10s %10s\n"
    "Function name" "Own time" "Tot. time" "Own alloc" "Tot. alloc" "Calls ";
  let l = Sort.list (fun (_,{tottime=p}) (_,{tottime=p'}) -> p > p') table in
  List.iter (fun (name,e) ->
    Printf.printf
      "%-23s %9.2f %9.2f %10.0f %10.0f %6d %6d\n"
      name
      (float_of_time e.owntime) (float_of_time e.tottime)
      (compute_alloc e.hiownalloc e.loownalloc)
      (compute_alloc e.hitotalloc e.lototalloc)
      e.owncount e.intcount)
    l;
  Printf.printf "%-23s %9.2f %9.2f %10.0f %10.0f        %6d\n"
    "others" 
    (float_of_time outside.owntime) (float_of_time outside.tottime)
    (compute_alloc outside.hiownalloc outside.loownalloc)
    (compute_alloc outside.hitotalloc outside.lototalloc)
    outside.intcount;
  (* Here, own contains overhead time/alloc *)
  Printf.printf "%-23s %9.2f %9.2f %10.0f %10.0f\n"
    "Est. overhead/total"
    (float_of_time total.owntime) (float_of_time total.tottime)
    (compute_alloc total.hiownalloc total.loownalloc)
    (compute_alloc total.hitotalloc total.lototalloc);
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
  let hidw,lodw = spent_alloc () in
  let t = get_time () in
  match !stack with
    | [outside] ->
	outside.tottime <- outside.tottime + t;
	outside.owntime <- outside.owntime + t;
	ajoute_ownalloc outside hidw lodw;
	ajoute_totalloc outside hidw lodw;
	if List.length !prof_table <> 0 then begin
	  let ov_bc = time_overhead_B_C () (* B+C overhead *) in
	  let ov_ad = time_overhead_A_D () (* A+D overhead *) in
	  let adjust (n,e) = (n, adjust_time ov_bc ov_ad e) in
	  let adjtable = List.map adjust !prof_table in
	  let adjoutside = adjust_time ov_bc ov_ad outside in
	  let lototalloc = !last_alloc - !init_alloc in
	  let hitotalloc = !carry_alloc in
	  let total = {
	    tottime = outside.tottime;
	    owntime = outside.tottime - adjoutside.tottime;
	    lototalloc = lototalloc;
	    hitotalloc = hitotalloc;
	    loownalloc = lototalloc;
	    hiownalloc = hitotalloc;
	    immcount = 0; owncount = 0; intcount = 0 (* Dummy values *) } in
	  (* We compute an estimation of overhead *)
	  (* and now "own" contains overhead time/alloc *)
	  ajoute_ownalloc total (-outside.hitotalloc) (-outside.lototalloc);
	  let current_data = (adjtable, adjoutside, total) in
	  let updated_data =
	    match !recording_file with
	      |	"" -> current_data
	      | name -> merge_profile !recording_file current_data
	  in
	  if print then format_profile updated_data;
	  init_profile ()
	end
    | _ -> failwith "Inconsistency"

let append_profile () = close_profile false
let print_profile () = close_profile true

let declare_profile name =
  if name = "___outside___" or name = "___total___" then
    failwith ("Error: "^name^" is a reserved keyword");
  let e = create_record () in
  prof_table := (name,e)::!prof_table;
  e

(* Default initialisation, may be overriden *)
let _ = init_profile ()

(******************************)
(* Entry points for profiling *)
let profile1 e f a =
  let hidw,lodw = spent_alloc () in
  match !stack with [] -> assert false | p::_ ->
  (* We add spent alloc since last measure to current caller own/total alloc *)
  ajoute_ownalloc p hidw lodw;
  ajoute_totalloc p hidw lodw;
  e.owncount <- e.owncount + 1;
  if not (p==e) then stack := e::!stack;
  let hitotalloc0,lototalloc0 = e.hitotalloc,e.lototalloc in
  let intcount0 = e.intcount in
  let t = get_time () in
  try
    last_alloc := get_alloc ();
    let r = f a in
    let hidw,lodw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e hidw lodw;
    ajoute_totalloc e hidw lodw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.hitotalloc - hitotalloc0) (e.lototalloc -lototalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then 
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    r
  with exn ->
    let hidw,lodw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e hidw lodw;
    ajoute_totalloc e hidw lodw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.hitotalloc - hitotalloc0) (e.lototalloc -lototalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then 
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    raise exn

let profile2 e f a b =
  let hidw,lodw = spent_alloc () in
  match !stack with [] -> assert false | p::_ ->
  (* We add spent alloc since last measure to current caller own/total alloc *)
  ajoute_ownalloc p hidw lodw;
  ajoute_totalloc p hidw lodw;
  e.owncount <- e.owncount + 1;
  if not (p==e) then stack := e::!stack;
  let hitotalloc0,lototalloc0 = e.hitotalloc,e.lototalloc in
  let intcount0 = e.intcount in
  let t = get_time () in
  try
    last_alloc := get_alloc ();
    let r = f a b in
    let hidw,lodw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e hidw lodw;
    ajoute_totalloc e hidw lodw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.hitotalloc - hitotalloc0) (e.lototalloc -lototalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then 
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    r
  with exn ->
    let hidw,lodw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e hidw lodw;
    ajoute_totalloc e hidw lodw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.hitotalloc - hitotalloc0) (e.lototalloc -lototalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then 
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    raise exn

let profile3 e f a b c =
  let hidw,lodw = spent_alloc () in
  match !stack with [] -> assert false | p::_ ->
  (* We add spent alloc since last measure to current caller own/total alloc *)
  ajoute_ownalloc p hidw lodw;
  ajoute_totalloc p hidw lodw;
  e.owncount <- e.owncount + 1;
  if not (p==e) then stack := e::!stack;
  let hitotalloc0,lototalloc0 = e.hitotalloc,e.lototalloc in
  let intcount0 = e.intcount in
  let t = get_time () in
  try
    last_alloc := get_alloc ();
    let r = f a b c in
    let hidw,lodw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e hidw lodw;
    ajoute_totalloc e hidw lodw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.hitotalloc - hitotalloc0) (e.lototalloc -lototalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then 
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    r
  with exn ->
    let hidw,lodw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e hidw lodw;
    ajoute_totalloc e hidw lodw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.hitotalloc - hitotalloc0) (e.lototalloc -lototalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then 
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    raise exn

let profile4 e f a b c d =
  let hidw,lodw = spent_alloc () in
  match !stack with [] -> assert false | p::_ ->
  (* We add spent alloc since last measure to current caller own/total alloc *)
  ajoute_ownalloc p hidw lodw;
  ajoute_totalloc p hidw lodw;
  e.owncount <- e.owncount + 1;
  if not (p==e) then stack := e::!stack;
  let hitotalloc0,lototalloc0 = e.hitotalloc,e.lototalloc in
  let intcount0 = e.intcount in
  let t = get_time () in
  try
    last_alloc := get_alloc ();
    let r = f a b c d in
    let hidw,lodw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e hidw lodw;
    ajoute_totalloc e hidw lodw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.hitotalloc - hitotalloc0) (e.lototalloc -lototalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then 
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    r
  with exn ->
    let hidw,lodw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e hidw lodw;
    ajoute_totalloc e hidw lodw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.hitotalloc - hitotalloc0) (e.lototalloc -lototalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then 
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    raise exn

let profile5 e f a b c d g =
  let hidw,lodw = spent_alloc () in
  match !stack with [] -> assert false | p::_ ->
  (* We add spent alloc since last measure to current caller own/total alloc *)
  ajoute_ownalloc p hidw lodw;
  ajoute_totalloc p hidw lodw;
  e.owncount <- e.owncount + 1;
  if not (p==e) then stack := e::!stack;
  let hitotalloc0,lototalloc0 = e.hitotalloc,e.lototalloc in
  let intcount0 = e.intcount in
  let t = get_time () in
  try
    last_alloc := get_alloc ();
    let r = f a b c d g in
    let hidw,lodw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e hidw lodw;
    ajoute_totalloc e hidw lodw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.hitotalloc - hitotalloc0) (e.lototalloc -lototalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then 
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    r
  with exn ->
    let hidw,lodw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e hidw lodw;
    ajoute_totalloc e hidw lodw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.hitotalloc - hitotalloc0) (e.lototalloc -lototalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then 
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    raise exn

let profile6 e f a b c d g h =
  let hidw,lodw = spent_alloc () in
  match !stack with [] -> assert false | p::_ ->
  (* We add spent alloc since last measure to current caller own/total alloc *)
  ajoute_ownalloc p hidw lodw;
  ajoute_totalloc p hidw lodw;
  e.owncount <- e.owncount + 1;
  if not (p==e) then stack := e::!stack;
  let hitotalloc0,lototalloc0 = e.hitotalloc,e.lototalloc in
  let intcount0 = e.intcount in
  let t = get_time () in
  try
    last_alloc := get_alloc ();
    let r = f a b c d g h in
    let hidw,lodw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e hidw lodw;
    ajoute_totalloc e hidw lodw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.hitotalloc - hitotalloc0) (e.lototalloc -lototalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then 
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    r
  with exn ->
    let hidw,lodw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e hidw lodw;
    ajoute_totalloc e hidw lodw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.hitotalloc - hitotalloc0) (e.lototalloc -lototalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then 
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    raise exn

let profile7 e f a b c d g h i =
  let hidw,lodw = spent_alloc () in
  match !stack with [] -> assert false | p::_ ->
  (* We add spent alloc since last measure to current caller own/total alloc *)
  ajoute_ownalloc p hidw lodw;
  ajoute_totalloc p hidw lodw;
  e.owncount <- e.owncount + 1;
  if not (p==e) then stack := e::!stack;
  let hitotalloc0,lototalloc0 = e.hitotalloc,e.lototalloc in
  let intcount0 = e.intcount in
  let t = get_time () in
  try
    last_alloc := get_alloc ();
    let r = f a b c d g h i in
    let hidw,lodw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e hidw lodw;
    ajoute_totalloc e hidw lodw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.hitotalloc - hitotalloc0) (e.lototalloc -lototalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then 
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    r
  with exn ->
    let hidw,lodw = spent_alloc () in
    let dt = get_time () - t in
    e.tottime <- e.tottime + dt; e.owntime <- e.owntime + dt;
    ajoute_ownalloc e hidw lodw;
    ajoute_totalloc e hidw lodw;
    p.owntime <- p.owntime - dt;
    ajoute_totalloc p (e.hitotalloc - hitotalloc0) (e.lototalloc -lototalloc0);
    p.intcount <- p.intcount + e.intcount - intcount0 + 1;
    p.immcount <- p.immcount + 1;
    if not (p==e) then 
      (match !stack with [] -> assert false | _::s -> stack := s);
    last_alloc := get_alloc ();
    raise exn

