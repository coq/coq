
(* $Id$ *)

open Pp

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
