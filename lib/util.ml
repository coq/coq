
(* $Id$ *)

open Pp

(* Errors *)

exception Anomaly of string * std_ppcmds  (* System errors *)
let anomaly string = raise (Anomaly(string,[< 'sTR string >]))
let anomalylabstrm string pps = raise (Anomaly(string,pps))

exception UserError of string * std_ppcmds (* User errors *)
let error string = raise (UserError(string,[< 'sTR string >]))
let errorlabstrm l pps = raise (UserError(l,pps))

(* raising located exceptions *)
type loc = int * int
let anomaly_loc (loc,s,strm) = Stdpp.raise_with_loc loc (Anomaly (s,strm))
let user_err_loc (loc,s,strm) = Stdpp.raise_with_loc loc (UserError (s,strm))
let invalid_arg_loc (loc,s) = Stdpp.raise_with_loc loc (Invalid_argument s)

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

let check_is_ident s =
  let len = String.length s in
  if len = 0 then invalid_arg "parse_loadpath: is not a valid name";
  (* TODO... *)
  ()

let parse_loadpath s =
  let len = String.length s in
  let rec decoupe_dirs n =
    try  
      let pos = String.index_from s n '/' in
      if pos = n then
	invalid_arg "parse_loadpath: find an empty dir in loadpath";
      let dir = String.sub s n (pos-n) in
      check_is_ident dir;
      dir :: (decoupe_dirs (succ pos))
    with
      | Not_found -> [String.sub s n (len-n)]
  in
  if len = 0 then [] else decoupe_dirs 0

module Stringset = Set.Make(struct type t = string let compare = compare end)

module Stringmap = Map.Make(struct type t = string let compare = compare end)

let stringmap_to_list m = Stringmap.fold (fun s y l -> (s,y)::l) m []

let stringmap_dom m = Stringmap.fold (fun s _ l -> s::l) m []

(* Lists *)

let list_add_set x l = if List.mem x l then l else x::l

let list_intersect l1 l2 = 
  List.filter (fun x -> List.mem x l2) l1

let list_union l1 l2 = 
  let rec urec = function
    | [] -> l2
    | a::l -> if List.mem a l2 then urec l else a::urec l
  in 
  urec l1

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
    | (_, []) -> failwith "list_chop"
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

let list_map2_i f i l1 l2 =  
  let rec map_i i = function
    | ([], []) -> []
    | ((h1::t1), (h2::t2)) -> (f i h1 h2) :: (map_i (succ i) (t1,t2))
    | (_, _) -> invalid_arg "map2_i"
  in 
  map_i i (l1,l2)

let list_index x = 
  let rec index_x n = function
    | y::l -> if x = y then n else index_x (succ n) l
    | [] -> raise Not_found
  in 
  index_x 1

let list_fold_left_i f = 
  let rec it_list_f i a = function
    | [] -> a 
    | b::l -> it_list_f (i+1) (f i a b) l
  in 
  it_list_f 

(* [list_fold_right_and_left f [a1;...;an] hd =
   f (f (... (f (f hd
                   an
                   [an-1;...;a1])
              an-1
              [an-2;...;a1])
         ...)
        a2
        [a1])
     a1
     []] *)

let rec list_fold_right_and_left f l hd =
  let rec aux tl = function
    | [] -> hd
    | a::l -> let hd = aux (a::tl) l in f hd a tl
   in aux [] l

let list_iter_i f l = list_fold_left_i (fun i _ x -> f i x) 0 () l

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

let rec list_last = function
  | [] -> failwith "list_last"
  | [x] -> x
  | _ :: l -> list_last l

let list_lastn n l =
  let len = List.length l in
  let rec aux m l =
    if m = n then l else aux (m - 1) (List.tl l)
  in
  if len < n then failwith "lastn" else aux len l

let list_prefix_of prefl l = 
  let rec prefrec = function
    | (h1::t1, h2::t2) -> h1 = h2 && prefrec (t1,t2)
    | ([], _) -> true
    | (_, _) -> false
  in 
  prefrec (prefl,l)

let list_map_append f l = List.flatten (List.map f l)

let list_map_append2 f l1 l2 = List.flatten (List.map2 f l1 l2)

let list_share_tails l1 l2 =
  let rec shr_rev acc = function
    | ((x1::l1), (x2::l2)) when x1 == x2 -> shr_rev (x1::acc) (l1,l2)
    | (l1,l2) -> (List.rev l1, List.rev l2, acc)
  in 
  shr_rev [] (List.rev l1, List.rev l2)

let list_except_assoc e = 
  let rec except_e = function
    | [] -> []
    | (x,_ as y)::l -> if x=e then l else y::except_e l
  in 
  except_e 

let list_join_map f l = List.flatten (List.map f l)

let list_try_find f = 
  let rec try_find_f = function
    | [] -> failwith "try_find"
    | h::t -> try f h with Failure _ -> try_find_f t
  in 
  try_find_f


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
  if Array.length v2 <> lv1 then invalid_arg "array_fold_left2";
  fold a 0

let array_fold_left2_i f a v1 v2 =
  let lv1 = Array.length v1 in
  let rec fold a n = 
    if n >= lv1 then a else fold (f n a v1.(n) v2.(n)) (succ n)
  in
  if Array.length v2 <> lv1 then invalid_arg "array_fold_left2";
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
  if Array.length v = 0 then invalid_arg "array_app_tl";
  array_fold_right_from 1 (fun e l -> e::l) v l

let array_list_of_tl v =
  if Array.length v = 0 then invalid_arg "array_list_of_tl";
  array_fold_right_from 1 (fun e l -> e::l) v []

let array_map_to_list f v =
  List.map f (Array.to_list v)

let array_chop n v =
  let vlen = Array.length v in
  if n > vlen then failwith "array_chop";
  (Array.sub v 0 n, Array.sub v n (vlen-n))

let array_map2 f v1 v2 =
  if Array.length v1 <> Array.length v2 then invalid_arg "array_map2";
  if Array.length v1 == 0 then 
    [| |] 
  else begin
    let res = Array.create (Array.length v1) (f v1.(0) v2.(0)) in
    for i = 1 to pred (Array.length v1) do
      res.(i) <- f v1.(i) v2.(i)
    done;
    res
  end

let array_map2_i f v1 v2 =
  if Array.length v1 <> Array.length v2 then invalid_arg "array_map2";
  if Array.length v1 == 0 then 
    [| |] 
  else begin
    let res = Array.create (Array.length v1) (f 0 v1.(0) v2.(0)) in
    for i = 1 to pred (Array.length v1) do
      res.(i) <- f i v1.(i) v2.(i)
    done;
    res
  end

let array_map3 f v1 v2 v3 =
  if Array.length v1 <> Array.length v2 ||
     Array.length v1 <> Array.length v3 then invalid_arg "array_map3";
  if Array.length v1 == 0 then 
    [| |] 
  else begin
    let res = Array.create (Array.length v1) (f v1.(0) v2.(0) v3.(0)) in
    for i = 1 to pred (Array.length v1) do
      res.(i) <- f v1.(i) v2.(i) v3.(i)
    done;
    res
  end

(* Matrices *)

let matrix_transpose mat =
  List.fold_right (List.map2 (fun p c -> p::c)) mat
    (if mat = [] then [] else List.map (fun _ -> []) (List.hd mat))

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

let interval n m = 
  let rec interval_n (l,m) =
    if n > m then l else interval_n (m::l,pred m)
  in 
  interval_n ([],m)

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
      
let prvecti elem v =
  let n = Array.length v in
  let rec pr i =
    if i = 0 then 
      elem 0 v.(0)
    else
      let r = pr (i-1) and e = elem i v.(i) in [< r; e >]
  in
  if n=0 then [< >] else pr (n - 1)

let prvect_with_sep sep elem v =
  let rec pr n =
    if n = 0 then 
      elem v.(0)
    else 
      let r = pr (n-1) and s = sep() and e = elem v.(n) in 
      [< r; s; e >]
      in
  let n = Array.length v in
  if n = 0 then [< >] else pr (n - 1)
