
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

let implode sl = String.concat "" sl

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
  if len = 0 || String.get s 0 <> '#' then invalid_arg "parse_section_path";
  let dirs,n = decoupe_dirs 1 in
  let id,k = decoupe_kind n in
  dirs,id,k

module Stringmap = Map.Make(struct type t = string let compare = compare end)

(* Lists *)

let list_intersect l1 l2 = 
  List.filter (fun x -> List.mem x l2) l1

let list_unionq l1 l2 = 
  let rec urec = function
    | [] -> l2
    | a::l -> if List.memq a l2 then urec l else a::urec l
  in 
  urec l1

let list_subtract l1 l2 =
  if l2 = [] then l1 else List.filter (fun x -> not (List.mem x l2)) l1

let list_subtractq l1 l2 = 
  if l2 = [] then l1 else List.filter (fun x -> not (List.memq x l2)) l1

let list_chop n l = 
  let rec chop_aux acc = function
    | (0, l2) -> (List.rev acc, l2)
    | (n, (h::t)) -> chop_aux (h::acc) (pred n, t)
    | (_, []) -> failwith "chop_list"
  in 
  chop_aux [] (n,l)

let list_tabulate f len = 
  let rec tabrec n =
    if n = len then [] else (f n)::(tabrec (n+1))
  in 
  tabrec 0

let list_assign l n e = 
  let rec assrec stk = function
    | ((h::t), 0) -> List.rev_append stk (e::t)
    | ((h::t), n) -> assrec (h::stk) (t, n-1)
    | ([], _) -> failwith "list_assign"
  in 
  assrec [] (l,n)

let list_map_i f = 
  let rec map_i_rec i = function
    | [] -> [] 
    | x::l -> let v = f i x in v :: map_i_rec (i+1) l
  in 
  map_i_rec

let list_index x = 
  let rec index_x n = function
    | y::l -> if x = y then n else index_x (succ n) l
    | [] -> failwith "index"
  in 
  index_x 1

let list_fold_left_i f = 
  let rec it_list_f i a = function
    | [] -> a 
    | b::l -> it_list_f (i+1) (f i a b) l
 in 
 it_list_f 

let list_for_all_i p = 
  let rec for_all_p i = function
    | [] -> true 
    | a::l -> p i a && for_all_p (i+1) l
  in 
  for_all_p

let list_except x l = List.filter (fun y -> not (x = y)) l

let list_for_all2eq f l1 l2 = try List.for_all2 f l1 l2 with Failure _ -> false

let list_map_i f = 
  let rec map_i_rec i = function
    | [] -> [] 
    | x::l -> let v = f i x in v::map_i_rec (i+1) l
  in 
  map_i_rec

let rec list_sep_last = function
  | [] -> failwith "sep_last"
  | hd::[] -> (hd,[])
  | hd::tl -> let (l,tl) = list_sep_last tl in (l,hd::tl)

let list_try_find_i f = 
  let rec try_find_f n = function
    | [] -> failwith "try_find_i"
    | h::t -> try f n h with Failure _ -> try_find_f (n+1) t
  in 
  try_find_f

let rec list_uniquize = function
  | [] -> []
  | h::t -> if List.mem h t then list_uniquize t else h::(list_uniquize t)

let rec list_distinct = function
  | h::t -> (not (List.mem h t)) && list_distinct t
  | _ -> true

let list_subset l1 l2 =
  let t2 = Hashtbl.create 151 in
  List.iter (fun x -> Hashtbl.add t2 x ()) l2;
  let rec look = function
    | [] -> true
    | x::ll -> try Hashtbl.find t2 x; look ll with Not_found -> false
  in 
  look l1

let list_splitby p = 
  let rec splitby_loop x y = 
    match y with 
      | []      -> ([],[])
      | (a::l)  -> if (p a) then (x,y) else (splitby_loop (x@[a]) l)
  in 
  splitby_loop []

let list_firstn n l =
  let rec aux acc = function
    | (0, l) -> List.rev acc
    | (n, (h::t)) -> aux (h::acc) (pred n, t)
    | _ -> failwith "firstn"
  in 
  aux [] (n,l)

let list_lastn n l =
  let len = List.length l in
  let rec aux m l =
    if m = n then l else aux (m - 1) (List.tl l)
  in
  if len < n then failwith "lastn" else aux len l

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

let array_fold_left2 f a v1 v2 =
  let lv1 = Array.length v1 in
  let rec fold a n = 
    if n >= lv1 then a else fold (f a v1.(n) v2.(n)) (succ n)
  in
  if Array.length v2 <> lv1 then
    invalid_arg "array_fold_left2"
  else
    fold a 0

let array_fold_left2_i f a v1 v2 =
  let lv1 = Array.length v1 in
  let rec fold a n = 
    if n >= lv1 then a else fold (f n a v1.(n) v2.(n)) (succ n)
  in
  if Array.length v2 <> lv1 then
    invalid_arg "array_fold_left2"
  else
    fold a 0

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

let array_map2 f v1 v2 =
  if Array.length v1 <> Array.length v2 then
    invalid_arg "map2_vect"
  else if Array.length v1 == 0 then 
    [| |] 
  else begin
    let res = Array.create (Array.length v1) (f v1.(0) v2.(0)) in
    for i = 1 to pred (Array.length v1) do
      res.(i) <- f v1.(i) v2.(i)
    done;
    res
  end

(* Functions *)

let compose f g x = f (g x)

let iterate f = 
  let rec iterate_f n x =
    if n <= 0 then x else iterate_f (pred n) (f x)
  in 
  iterate_f

let repeat n f x =
  for i = 1 to n do f x done
 
(* Misc *)

type ('a,'b) union = Inl of 'a | Inr of 'b

module Intset = Set.Make(struct type t = int let compare = compare end)

let intset_exists p s = Intset.fold (fun x b -> (p x) || b) s false

module Intmap = Map.Make(struct type t = int let compare = compare end)

let intmap_in_dom x m =
  try let _ = Intmap.find x m in true with Not_found -> false

let intmap_to_list m = Intmap.fold (fun n v l -> (n,v)::l) m []

let intmap_inv m b = Intmap.fold (fun n v l -> if v = b then n::l else l) m []

let in_some x = Some x

let out_some = function
  | Some x -> x
  | None -> failwith "out_some"

let option_app f = function
  | None -> None
  | Some x -> Some (f x)

let map_succeed f = 
  let rec map_f = function 
    | [] -> []
    |  h::t -> try (let x = f h in x :: map_f t) with Failure _ -> map_f t
  in 
  map_f 

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
