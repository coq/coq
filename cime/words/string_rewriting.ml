(***************************************************************************

This module defines string rewriting

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


open Format;;
		 
(*

  This module defines string rewriting

*)

type 'symbol rewrite_rule = ('symbol Words.word * 'symbol Words.word)

type 'symbol srs = ('symbol Words.word * 'symbol Words.word) list;;


let rec match_prefix pat obj =
  match pat with
      [] -> obj
    | a::w ->
	match obj with
	    [] -> raise Not_found
	  | b::w' -> 
	      if a=b
	      then match_prefix w w' 
	      else raise Not_found
;;


let rec prefix_matching srs w =
  match srs with 
      [] -> raise Not_found
    | (lhs,rhs)::srs -> 
	try 
	  let suff = match_prefix lhs w in
(*
	    print_string "match found : word = ";
	    Words.print sigma w;
	    print_string "    lhs = ";
	    Words.print sigma lhs;
	    print_string "    rhs = ";
	    Words.print sigma rhs;
	    print_string "    suff = ";
	    Words.print sigma suff;
	    print_newline();
*)
	    (rhs,suff)
	with Not_found -> prefix_matching  srs w
;;
	

let rec normalize_prefix srs pref suff =
  match pref with
      [] -> suff
    | a::w ->
	let w' = a::(normalize_prefix srs w suff) in
	match
	  try
	    Some(prefix_matching srs w') 	
	  with Not_found -> None
	with
	    Some(rhs,next_suff) -> normalize_prefix srs rhs next_suff 
	  | None -> w'
	  
;;


let rec is_nf srs pref =
  match pref with
      [] -> true
    | a::w ->
	(is_nf srs w)  &&
	try
	  let _ = prefix_matching srs pref in
	    false
	with Not_found -> true


let normalize  srs w = 
  normalize_prefix srs w []

type 'symbol compiled_srs =
    Match_found of 'symbol Words.word
  | Switch of ('symbol * 'symbol compiled_srs) list

let rec compiled_prefix_matching srs w =
  match srs with 
      Match_found(rhs) -> (rhs, w)
    | Switch(l) -> 
	match w with
	    [] -> raise Not_found
	  | a::w' ->
		let srs' = List.assoc a l in
		  compiled_prefix_matching srs' w'

let rec compiled_prefix_matching_no_exc srs w =
  match srs with 
      Match_found(rhs) -> Some(rhs, w)
    | Switch(l) -> 
	match w with
	    [] -> None
	  | a::w' ->
		try
		  let srs' = List.assoc a l in
		  compiled_prefix_matching_no_exc srs' w'
		with Not_found -> None



let rec compiled_normalize_prefix srs left middle right =
  match middle with
      a::w -> compiled_normalize_prefix srs (a::left) w right
    | [] ->
	match left with
	    [] -> right
	  | a::next_left ->
	      let next_right = a::right in
	      match compiled_prefix_matching_no_exc srs next_right
	      with
		  Some(rhs,next_right) -> 
		    compiled_normalize_prefix srs next_left rhs next_right
		| None -> 
		    compiled_normalize_prefix srs next_left [] next_right 

let compiled_normalize srs w = 
  compiled_normalize_prefix srs [] w []

(* This version is very effiencient but fails with a Stack oveflow *)
(* very quickly (about 60000 letters in a word). 
Example of speed with [turing_muld.cime2] : 
[Execution time: 0.000000 sec
- : S word = h 1^2 0 q7 1^3 0 1^6 0 h
Execution time: 0.000000 sec
- : S word = h 1^3 0 q7 1^4 0 1^12 0 h
Execution time: 0.010000 sec
- : S word = h 1^5 0 q7 1^5 0 1^25 0 h
Execution time: 0.040000 sec
- : S word = h 1^7 0 q7 1^8 0 1^56 0 h
Execution time: 0.090000 sec
- : S word = h 1^10 0 q7 1^10 0 1^100 0 h
Execution time: 18.860000 sec
- : S word = h 1^35 0 q7 1^43 0 1^1505 0 h]
*)
(*
let rec compiled_normalize_prefix srs pref suff =
  match pref with
      [] -> suff
    | a::w ->
	let w' = a::compiled_normalize_prefix srs w suff in
	match 
	  try
	    Some(compiled_prefix_matching srs w')
	  with Not_found -> None
	with
	    Some(rhs,next_suff) -> 
	      compiled_normalize_prefix srs rhs next_suff 
	  | None -> w'

let compiled_normalize srs w = compiled_normalize_prefix srs w []
*)

(* This version is slower but can normalize HUGE words.
The same test as before: 
Execution time: 0.000000 sec
- : S word = h 1^2 0 q7 1^3 0 1^6 0 h
Execution time: 0.010000 sec
- : S word = h 1^3 0 q7 1^4 0 1^12 0 h
Execution time: 0.000000 sec
- : S word = h 1^5 0 q7 1^5 0 1^25 0 h
Execution time: 0.030000 sec
- : S word = h 1^7 0 q7 1^8 0 1^56 0 h
Execution time: 0.110000 sec
- : S word = h 1^10 0 q7 1^10 0 1^100 0 h
Execution time: 22.640000 sec
- : S word = h 1^35 0 q7 1^43 0 1^1505 0 h]
*)

(*
let rec compiled_normalize_prefix srs pref suff k =
  match pref with
      [] -> k suff
    | a::w ->
	compiled_normalize_prefix srs w suff 
	  (fun w' -> 
	     let w' = a :: w' in
	     match 
	       try
		 Some(compiled_prefix_matching srs w')
	       with Not_found -> None
	     with
		 Some(rhs,next_suff) -> 
		   compiled_normalize_prefix srs rhs next_suff k
	       | None -> k w')

let compiled_normalize srs w = compiled_normalize_prefix srs w [] (fun x -> x)
*)

(* This version of [compiled_normalize_prefix] is still not tail
 recursive. But should be. In fact the static ancestor of f is put on
 the stack by caml. There is a Call instruction and not a jump. Might
 be a problem with the compiler. Is EBX Callee or Caller preserved ?
 The compiler seems to say Caller. The other convention would be
 better and logical with standard X86 code.*) 

(*let compiled_normalize_prefix srs stack = 
  let l2 = ref [] in
  let l = ref [] in
  let r = ref None in
  let outsome = function Some x -> x | _ -> assert false in
  let rec f () =
    l := Stack.pop stack;
    if !l <> [] then 
      begin
	l2 := Stack.pop stack;
	Stack.push [List.hd !l] stack;
	Stack.push !l2 stack;
	Stack.push (List.tl !l) stack;
	f();
	Stack.push (Stack.pop stack @ Stack.pop stack) stack;
	begin
	  try
	    r := Some(compiled_prefix_matching srs (Stack.top stack))
	  with Not_found -> 
	    r := None
	end;
	if !r <> None then begin
	  ignore (Stack.pop stack);
	  Stack.push (snd (outsome !r)) stack;
	  Stack.push (fst (outsome !r)) stack;
	  f ()
	end
      end
  in f()
		  
let compiled_normalize srs w = 
  let my_stack = Stack.create () in
  Stack.push [] my_stack ;
  Stack.push w my_stack;
  compiled_normalize_prefix srs my_stack;
  Stack.pop my_stack
*)

let rec is_nf_compiled srs pref =
  match pref with
      [] -> true
    | a::w ->
	(is_nf_compiled srs w)  &&
	try
	  let _ = compiled_prefix_matching srs pref in
	    false
	with Not_found -> true

(*i
let compile_srs srs =
  let rec add_rule compiled_srs (lhs,rhs) =
    match lhs with
	[] -> Match_found(rhs)
      | a::w ->
	  match compiled_srs with
	      Match_found(_) -> compiled_srs
	    | Switch(l) ->
		Switch(add_to_list (fun c -> add_rule c (w,rhs)) l a)
		  
  and add_to_list modf l head =
    match l with 
      [] -> [head, modf (Switch [])]
      | ((b,compiled_srs') as t)::l ->
	  if head=b
	  then
	    (b,modf compiled_srs') :: l
	  else
	    t :: (add_to_list modf l head)
  in 
    try 
      List.fold_left add_rule (Switch []) srs
    with 
	Stack_overflow -> failwith "compile: stack overflow"
;i*)

let compile_srs srs =
  let rec add_rule compiled_srs (lhs,rhs) =
    match lhs with
	[] -> Match_found(rhs)
      | a::w ->
	  match compiled_srs with
	      Match_found(_) -> compiled_srs
	    | Switch(l) ->
		let rec add_to_list l =
		  match l with 
		      [] -> [(a,add_rule  (Switch []) (w,rhs))]
		    | ((b,compiled_srs') as t)::l ->
			if a=b
			then
			  (b,add_rule  compiled_srs' (w,rhs))::l
			else
			  t::(add_to_list l)
                in 
		  Switch(add_to_list l)
  in
      List.fold_left add_rule (Switch []) srs

(*

\subsection{Printing}

*)

open Format;;

let print_rule sigma print_word (lhs,rhs) =
  open_box 0;
  print_word sigma lhs;
  printf "@ ->@ ";
  print_word sigma rhs;
  close_box ()
;;


let rec print_end_list sigma print_word n srs = 
  match srs with
      [] -> printf " }@ (%d rules)" n;
    | (r::l) -> 
	begin
          print_string  ",";
          force_newline ();
          print_rule sigma print_word r;
          print_end_list sigma print_word (succ n) l
	end
;;

let print_srs sigma print_word srs = 
  match srs with 
      []   -> print_string "{}"
    | r::l ->
	begin
	  print_string "{ ";
	  open_box 0;
	  print_rule sigma print_word r;
	  print_end_list sigma print_word 1 l;
	  close_box ()
	end
;;

let print sigma srs = print_srs sigma Words.print srs;;

let pretty_print sigma srs = print_srs sigma Words.pretty_print srs;;

