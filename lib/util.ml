
(* $Id$ *)

open Pp

(* Errors *)

exception Anomaly of string * std_ppcmds  (* System errors *)
let anomaly string = raise (Anomaly(string,[< 'sTR string >]))
let anomalylabstrm string pps = raise (Anomaly(string,pps))

exception UserError of string * std_ppcmds (* User errors *)
let error string = raise (UserError(string,[< 'sTR string >]))
let errorlabstrm l pps = raise (UserError(l,pps))

(* Strings *)

let explode s = 
  let rec explode_rec n =
    if n >= String.length s then
      []
    else 
      String.make 1 (String.get s n) :: explode_rec (succ n)
  in 
  explode_rec 0

let implode sl =
  let len = List.fold_left (fun a b -> a + (String.length b)) 0 sl in
  let dest = String.create len in
  let _ = List.fold_left 
	    (fun start src ->
	       let src_len = String.length src in
	       String.blit src 0 dest start src_len;
	       start + src_len)
	    0 sl 
  in
  dest

let parse_section_path s =
  let len = String.length s in
  let rec decoupe_dirs n =
    try
      let pos = String.index_from s n '#' in
      let dir = String.sub s n (pos-n) in
      let dirs,n' = decoupe_dirs (succ pos) in
      dir::dirs,n'
    with
      | Not_found -> [],n
  in
  let decoupe_kind n =
    try
      let pos = String.index_from s n '.' in
      String.sub s n (pos-n), String.sub s (succ pos) (pred (len-pos))
    with
      | Not_found -> invalid_arg "parse_section_path"
  in
  if len = 0 || String.get s 0 <> '#' then
    invalid_arg "parse_section_path"
  else
    let dirs,n = decoupe_dirs 1 in
    let id,k = decoupe_kind n in
    dirs,id,k

(* Lists *)

let intersect l1 l2 = 
  List.filter (fun x -> List.mem x l2) l1

let subtract l1 l2 =
  if l2 = [] then l1 else List.filter (fun x -> not (List.mem x l2)) l1

let list_chop n l = 
  let rec chop_aux acc = function
    | (0, l2) -> (List.rev acc, l2)
    | (n, (h::t)) -> chop_aux (h::acc) (pred n, t)
    | (_, []) -> failwith "chop_list"
  in 
  chop_aux [] (n,l)
 
(* Arrays *)

let array_exists f v = 
  let rec exrec = function
    | -1 -> false
    | n -> (f v.(n)) || (exrec (n-1))
  in 
  exrec ((Array.length v)-1) 

let array_for_all f v = 
  let rec allrec = function
    | -1 -> true
    | n -> (f v.(n)) && (allrec (n-1))
  in 
  allrec ((Array.length v)-1) 

let array_for_all2 f v1 v2 =
  let rec allrec = function
    | -1 -> true
    | n -> (f v1.(n) v2.(n)) && (allrec (n-1))
  in 
  let lv1 = Array.length v1 in
  lv1 = Array.length v2 && allrec (pred lv1) 

let array_hd v = 
  match Array.length v with
    | 0 -> failwith "array_hd"
    | _ -> v.(0)

let array_tl v = 
  match Array.length v with
    | 0 -> failwith "array_tl"
    | n -> Array.sub v 1 (pred n)

let array_last v =
  match Array.length v with
    | 0 -> failwith "aray_last"
    | n -> v.(pred n)

let array_cons e v = Array.append [|e|] v

let array_fold_left_from n f a v = 
  let rec fold a n =
    if n >= Array.length v then a else fold (f a v.(n)) (succ n)
  in 
  fold a n

let array_fold_right_from n f v a = 
  let rec fold n =
    if n >= Array.length v then a else f v.(n) (fold (succ n))
  in 
  fold n

let array_app_tl v l = 
  if Array.length v = 0 then 
    invalid_arg "array_app_tl"
  else 
    array_fold_right_from 1 (fun e l -> e::l) v l

let array_list_of_tl v =
  if Array.length v = 0 then 
    invalid_arg "array_list_of_tl"
  else 
    array_fold_right_from 1 (fun e l -> e::l) v []

let array_map_to_list f v =
  List.map f (Array.to_list v)

let array_chop n v =
  let vlen = Array.length v in
  if n > vlen then 
    failwith "chop_vect"
  else 
    (Array.sub v 0 n, Array.sub v n (vlen-n))

(* Functions *)

let compose f g x = f (g x)

let iterate f = 
  let rec iterate_f n x =
    if n <= 0 then x else iterate_f (pred n) (f x)
  in 
  iterate_f
 
(* Misc *)

type ('a,'b) union = Inl of 'a | Inr of 'b

module Intset = Set.Make(struct type t = int let compare = compare end)

(* Pretty-printing *)
  
let pr_spc () = [< 'sPC >];;
let pr_fnl () = [< 'fNL >];;
let pr_int n = [< 'iNT n >];;
let pr_str s = [< 'sTR s >];;
let pr_coma () = [< 'sTR","; 'sPC >];;

let rec prlist elem l = match l with 
  | []   -> [< >]
  | h::t -> let e = elem h and r = prlist elem t in [< e; r >]

let rec prlist_with_sep sep elem l = match l with
  | []   -> [< >]
  | [h]  -> elem h
  | h::t ->
      let e = elem h and s = sep() and r = prlist_with_sep sep elem t in
      [< e; s; r >]
      
let prvect_with_sep sep elem v =
  let rec pr n =
    if n = 0 then 
      elem v.(0)
    else 
      let r = pr (n-1) and s = sep() and e = elem v.(n) in 
      [< r; s; e >]
  in
  if Array.length v = 0 then [< >] else pr (Array.length v - 1)
