
(* $Id$ *)

(* This program is a small time-profiler for Caml-Special-Light *)

(* It requires the UNIX library *)

(* Adapted from Christophe Raffalli *)

(* To use it, link it with the program you want to profile (don not forget
"-cclib -lunix -custom unix.cma" among the link options).

To trace a function "f" you first need to get a key for it by using :

let fkey = declare_profile "f"

(the string is used to print the profile infomation). Warning: this
function does a side effect. Choose the ident you want instead "fkey".

Then if the function has one ONE argument add the following just after
the definition of "f" or just after the declare_profile if this one
follows the defintion of f.

let f = profile fkey f

If f has two arguments do the same with profile2, idem with 3 and
4. For more than 4 arguments ... modify the function profile yourself,
it is very easy (look the differences between profile and profile2.

If you want to profile two mutually recursive functions, you had better
to rename them :

let fkey = declare_profile "f"
let gkey = declare_profile "g"
let f' = .... f' ... g'
and g' = .... f' .... g'


let f = profile fkey f'
let g = profile gkey g'

Before the program quits, you should call "print_profile ()". It
produces a result of the following kind:

f 5.32 7.10
g 4.00 4.00
main 0.12 9.44
total -9.44 0.00

- The first column is the name of the function.

- The third column give the time (utime + stime) spend inside the function.

- The second column give the time spend inside the function minus the
time spend in other profiled functions called by it

The last line can be ignored (there is a bug if the down-right digit is non
zero)

*)

type profile_key = float ref * float ref

let actif = ref true

let tot_ptr = ref 0.0 and tot_ptr' = ref 0.0

let prof_table = ref ["total",(tot_ptr,tot_ptr')]

let stack = ref [tot_ptr']

let ajoute ((name,(ptr1,ptr1')) as e) l =
  try let (ptr,ptr') = List.assoc name l in
  ptr  := !ptr  +. !ptr1;
  ptr' := !ptr' +. !ptr1';
  l
  with Not_found -> e::l


let magic = 1248

let append_profile name =
  if List.length !prof_table <> 1 then begin
    let prof_table =
      if name = "" then !prof_table
      else
	let new_prof_table =
          try 
            let c = open_in name in
            if input_binary_int c <> magic 
            then Printf.printf "Bad already existing recording file\n";
            let old_prof_table = input_value c in
            close_in c;
            List.fold_right ajoute !prof_table old_prof_table
          with Sys_error _ ->
            (Printf.printf "Non existent or unaccessible recording file\n";
             !prof_table)
	in begin
          (try
             let c = open_out_gen 
                       [Open_creat;Open_wronly;Open_trunc;Open_binary] 0o644 name in
             output_binary_int c magic;
             output_value c new_prof_table;
             close_out c
           with Sys_error _ -> Printf.printf "Unable to create recording file");
            new_prof_table
	  end
    in
    print_newline ();
    Printf.printf "%-25s  %11s  %11s\n" 
      "Function name" "Proper time" "Total time";
    let l = Sort.list (fun (_,(_,p)) (_,(_,p')) -> !p > !p') prof_table in
    List.iter (fun (name,(ptr,ptr')) ->
		 Printf.printf "%-25s  %11.2f  %11.2f\n" name !ptr' !ptr) l;
    Gc.print_stat stdout
  end


let recording_file = ref ""
let set_recording s = recording_file := s

let print_profile () = append_profile !recording_file

let reset_profile () = 
  List.iter (fun (name,(p,p')) -> p:=0.0; p':=0.0) !prof_table

let init_profile () = 
  tot_ptr:= 0.0; tot_ptr':=0.0; prof_table :=["total",(tot_ptr,tot_ptr')] 

let declare_profile name = let ptr = ref 0.0 and ptr' = ref 0.0 in
prof_table := (name,(ptr,ptr'))::!prof_table;(ptr,ptr')

let profile (ptr,ptr') f =
  (fun x ->
     let (ut,st) = System.process_time () in
     stack := ptr'::!stack;
     try
       let r = f x in
       let (ut',st') = System.process_time () in
       let t = (ut' -. ut) +. (st' -. st) in
       (match !stack with
	    _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
	  | _ -> failwith "bug in profile");
       ptr := !ptr +. t;
       ptr' := !ptr' +. t;
       r
     with e ->
       let (ut',st') = System.process_time () in
       let t = (ut' -. ut) +. (st' -. st) in
       (match !stack with
	    _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
	  | _ -> failwith "bug in profile");
       ptr := !ptr +. t;
       ptr' := !ptr' +. t;
       raise e)



let profile2 (ptr,ptr') f =
  (fun x y ->
     let (ut,st) = System.process_time () in
     stack := ptr'::!stack;
     try
       let r = f x y in
       let (ut',st') = System.process_time () in
       let t = (ut' -. ut) +. (st' -. st) in
       (match !stack with
	    _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
	  | _ -> failwith "bug in profile");
       ptr := !ptr +. t;
       ptr' := !ptr' +. t;
       r
     with e ->
       let (ut',st') = System.process_time () in
       let t = (ut' -. ut) +. (st' -. st) in
       (match !stack with
	    _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
	  | _ -> failwith "bug in profile");
       ptr := !ptr +. t;
       ptr' := !ptr' +. t;
       raise e)



let profile3 (ptr,ptr') f =
  (fun x y z ->
     let (ut,st) = System.process_time () in
     stack := ptr'::!stack;
     try
       let r = f x y z in
       let (ut',st') = System.process_time () in
       let t = (ut' -. ut) +. (st' -. st) in
       (match !stack with
	    _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
	  | _ -> failwith "bug in profile");
       ptr := !ptr +. t;
       ptr' := !ptr' +. t;
       r
     with e ->
       let (ut',st') = System.process_time () in
       let t = (ut' -. ut) +. (st' -. st) in
       (match !stack with
	    _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
	  | _ -> failwith "bug in profile");
       ptr := !ptr +. t;
       ptr' := !ptr' +. t;
       raise e)



let profile4 (ptr,ptr') f =
  (fun x y z t ->
     let (ut,st) = System.process_time () in
     stack := ptr'::!stack;
     try
       let r = f x y z t in
       let (ut',st') = System.process_time () in
       let t = (ut' -. ut) +. (st' -. st) in
       (match !stack with
	    _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
	  | _ -> failwith "bug in profile");
       ptr := !ptr +. t;
       ptr' := !ptr' +. t;
       r
     with e ->
       let (ut',st') = System.process_time () in
       let t = (ut' -. ut) +. (st' -. st) in
       (match !stack with
	    _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
	  | _ -> failwith "bug in profile");
       ptr := !ptr +. t;
       ptr' := !ptr' +. t;
       raise e)



let profile5 (ptr,ptr') f =
  (fun x y z t u ->
     let (ut,st) = System.process_time () in
     stack := ptr'::!stack;
     try
       let r = f x y z t u in
       let (ut',st') = System.process_time () in
       let t = (ut' -. ut) +. (st' -. st) in
       (match !stack with
	    _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
	  | _ -> failwith "bug in profile");
       ptr := !ptr +. t;
       ptr' := !ptr' +. t;
       r
     with e ->
       let (ut',st') = System.process_time () in
       let t = (ut' -. ut) +. (st' -. st) in
       (match !stack with
	    _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
	  | _ -> failwith "bug in profile");
       ptr := !ptr +. t;
       ptr' := !ptr' +. t;
       raise e)



let profile6 (ptr,ptr') f =
  (fun x y z t u v ->
     let (ut,st) = System.process_time () in
     stack := ptr'::!stack;
     try
       let r = f x y z t u v in
       let (ut',st') = System.process_time () in
       let t = (ut' -. ut) +. (st' -. st) in
       (match !stack with
	    _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
	  | _ -> failwith "bug in profile");
       ptr := !ptr +. t;
       ptr' := !ptr' +. t;
       r
     with e ->
       let (ut',st') = System.process_time () in
       let t = (ut' -. ut) +. (st' -. st) in
       (match !stack with
	    _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
	  | _ -> failwith "bug in profile");
       ptr := !ptr +. t;
       ptr' := !ptr' +. t;
       raise e)



let profile7 (ptr,ptr') f =
  (fun x y z t u v w ->
     let (ut,st) = System.process_time () in
     stack := ptr'::!stack;
     try
       let r = f x y z t u v w in
       let (ut',st') = System.process_time () in
       let t = (ut' -. ut) +. (st' -. st) in
       (match !stack with
	    _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
	  | _ -> failwith "bug in profile");
       ptr := !ptr +. t;
       ptr' := !ptr' +. t;
       r
     with e ->
       let (ut',st') = System.process_time () in
       let t = (ut' -. ut) +. (st' -. st) in
       (match !stack with
	    _::(ptr'::_ as s) -> stack:=s; ptr' := !ptr' -. t
	  | _ -> failwith "bug in profile");
       ptr := !ptr +. t;
       ptr' := !ptr' +. t;
       raise e)
