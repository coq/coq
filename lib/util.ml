(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp

(* Errors *)

exception Anomaly of string * std_ppcmds  (* System errors *)
let anomaly string = raise (Anomaly(string, str string))
let anomalylabstrm string pps = raise (Anomaly(string,pps))

exception UserError of string * std_ppcmds (* User errors *)
let error string = raise (UserError(string, str string))
let errorlabstrm l pps = raise (UserError(l,pps))

let todo s = prerr_string ("TODO: "^s^"\n")

(* raising located exceptions *)
type loc = int * int
type 'a located = loc * 'a
let dummy_loc = (0,0)
let anomaly_loc (loc,s,strm) = Stdpp.raise_with_loc loc (Anomaly (s,strm))
let user_err_loc (loc,s,strm) = Stdpp.raise_with_loc loc (UserError (s,strm))
let invalid_arg_loc (loc,s) = Stdpp.raise_with_loc loc (Invalid_argument s)
let join_loc (deb1,_) (_,fin2) = (deb1,fin2)

(* Characters *)

let is_letter c =
  (c >= 'a' && c <= 'z') or
  (c >= 'A' && c <= 'Z') or
  (c >= '\248' && c <= '\255') or
  (c >= '\192' && c <= '\214') or
  (c >= '\216' && c <= '\246')

let is_digit c = (c >= '0' && c <= '9')

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

let parse_loadpath s =
  let len = String.length s in
  let rec decoupe_dirs n =
    try  
      let pos = String.index_from s n '/' in
      if pos = n then
	invalid_arg "parse_loadpath: find an empty dir in loadpath";
      let dir = String.sub s n (pos-n) in
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

let rec list_smartmap f l = match l with
    [] -> l
  | h::tl -> 
      let h' = f h and tl' = list_smartmap f tl in
	if h'==h && tl'==tl then l
	else h'::tl'

let list_map_left f = (* ensures the order in case of side-effects *)
  let rec map_rec = function
    | [] -> [] 
    | x::l -> let v = f x in v :: map_rec l
  in 
  map_rec

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

let list_map3 f l1 l2 l3 =
  let rec map = function
    | ([], [], []) -> []
    | ((h1::t1), (h2::t2), (h3::t3)) -> (f h1 h2 h3) :: (map (t1,t2,t3))
    | (_, _, _) -> invalid_arg "map3"
  in 
  map (l1,l2,l3)

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

let list_try_find f = 
  let rec try_find_f = function
    | [] -> failwith "try_find"
    | h::t -> try f h with Failure _ -> try_find_f t
  in 
  try_find_f

let rec list_uniquize = function
  | [] -> []
  | h::t -> if List.mem h t then list_uniquize t else h::(list_uniquize t)

let rec list_distinct = function
  | h::t -> (not (List.mem h t)) && list_distinct t
  | _ -> true

let rec list_filter2 f = function
  | [], [] as p -> p
  | d::dp, l::lp ->
     let (dp',lp' as p) = list_filter2 f (dp,lp) in
      if f d l then d::dp', l::lp' else p
  | _ -> invalid_arg "list_filter2"

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

let rec list_split3 = function
  | [] -> ([], [], [])
  | (x,y,z)::l ->
      let (rx, ry, rz) = list_split3 l in (x::rx, y::ry, z::rz)

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

let list_join_map f l = List.flatten (List.map f l)

let rec list_fold_map f e = function 
  |  []  -> (e,[])
  |  h::t -> 
       let e',h' = f e h in
       let e'',t' = list_fold_map f e' t in
	 e'',h'::t'

(* (* tail-recursive version of the above function *)
let list_fold_map f e l = 
  let g (e,b') h = 
    let (e',h') = f e h in
      (e',h'::b') 
  in
  let (e',lrev) = List.fold_left g (e,[]) l in
    (e',List.rev lrev)
*)

let list_map_assoc f = List.map (fun (x,a) -> (x,f a))

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

let array_for_all_i f v = 
  let rec allrec = function
    | -1 -> true
    | n -> (f n v.(n)) && (allrec (n-1))
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

let array_fold_right_i f v a =
  let rec fold a n =
    if n=0 then a
    else
      let k = n-1 in
      fold (f k v.(k) a) k in
  fold a (Array.length v)

let array_fold_left_i f v a =
  let n = Array.length a in
  let rec fold i v = if i = n then v else fold (succ i) (f i v a.(i)) in
  fold 0 v

let array_fold_right2 f v1 v2 a =
  let lv1 = Array.length v1 in
  let rec fold a n =
    if n=0 then a
    else
      let k = n-1 in
      fold (f v1.(k) v2.(k) a) k in
  if Array.length v2 <> lv1 then invalid_arg "array_fold_right2";
  fold a lv1

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

exception Local of int

(* If none of the elements is changed by f we return ar itself.
   The for loop looks for the first such an element.
   If found it is temporarily stored in a ref and the new array is produced, 
   but f is not re-applied to elements that are already checked *)
let array_smartmap f ar = 
  let ar_size = Array.length ar in
  let aux = ref None in
  try
    for i = 0 to ar_size-1 do
      let a = ar.(i) in
      let a' = f a in
	if a != a' then (* pointer (in)equality *) begin
	  aux := Some a';
	  raise (Local i)
	end
    done;
    ar
  with
      Local i -> 
	let copy j = 
	  if j<i then ar.(j) 
	  else if j=i then 
	    match !aux with Some a' -> a' | None -> failwith "Error"
	  else f (ar.(j))
	in
	  Array.init ar_size copy

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

let array_update_by_list_map a f l =
  let r = ref l in
    for i = 0 to Array.length a - 1 do
      match !r with
	| x::r' -> a.(i) <- f x; r := r'
	| _ -> anomaly "array_update_by_list_map"
    done

let array_init_by_list_map n v f l =
  let a = Array.make n v in array_update_by_list_map a f l; a

let array_make_by_list_map v f l =
  array_init_by_list_map (List.length l) v f l

let array_to_rev_list a = Array.fold_left (fun l x -> x::l) [] a

(* Matrices *)

let matrix_transpose mat =
  List.fold_right (List.map2 (fun p c -> p::c)) mat
    (if mat = [] then [] else List.map (fun _ -> []) (List.hd mat))

(* Functions *)

let identity x = x

let compose f g x = f (g x)

let iterate f = 
  let rec iterate_f n x =
    if n <= 0 then x else iterate_f (pred n) (f x)
  in 
  iterate_f

let repeat n f x =
  for i = 1 to n do f x done

let iterate_for a b f x =
  let rec iterate i v = if i > b then v else iterate (succ i) (f i v) in
  iterate a x
 
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

let option_cons a l = match a with
  | Some x -> x::l
  | None -> l

let option_fold_left2 f e a b = match (a,b) with
  | Some x, Some y -> f e x y
  | _ -> e

let option_compare f a b = match (a,b) with
  | None, None -> true
  | Some a', Some b' -> f a' b'
  | _ -> failwith "option_compare"

let option_iter f = function
  | None -> ()
  | Some x -> f x

let option_smartmap f a = match a with
  | None -> a
  | Some x -> let x' = f x in if x'==x then a else Some x'

let map_succeed f = 
  let rec map_f = function 
    | [] -> []
    |  h::t -> try (let x = f h in x :: map_f t) with Failure _ -> map_f t
  in 
  map_f 

(* Pretty-printing *)
  
let pr_spc = spc
let pr_fnl = fnl
let pr_int = int
let pr_str = str
let pr_coma () = str "," ++ spc ()
let pr_semicolon () = str ";" ++ spc ()
let pr_bar () = str "|" ++ spc ()

let pr_ord n =
  let suff = match n mod 10 with 1 -> "st" | 2 -> "nd" | _ -> "th" in
  int n ++ str suff

let rec prlist elem l = match l with 
  | []   -> mt ()
  | h::t -> Stream.lapp (fun () -> elem h) (prlist elem t)

let rec prlist_with_sep sep elem l = match l with
  | []   -> mt ()
  | [h]  -> elem h
  | h::t ->
      let e = elem h and s = sep() and r = prlist_with_sep sep elem t in
      e ++ s ++ r

let pr_vertical_list pr = function
  | [] -> str "none" ++ fnl ()
  | l -> fnl () ++ str "  " ++ hov 0 (prlist_with_sep pr_fnl pr l) ++ fnl ()
      
let prvecti elem v =
  let n = Array.length v in
  let rec pr i =
    if i = 0 then 
      elem 0 v.(0)
    else
      let r = pr (i-1) and e = elem i v.(i) in r ++ e
  in
  if n = 0 then mt () else pr (n - 1)

let prvect_with_sep sep elem v =
  let rec pr n =
    if n = 0 then 
      elem v.(0)
    else 
      let r = pr (n-1) and s = sep() and e = elem v.(n) in 
      r ++ s ++ e
      in
  let n = Array.length v in
  if n = 0 then mt () else pr (n - 1)

(*s Size of ocaml values. *)

module Size = struct
  
  open Obj

  (*s Pointers already visited are stored in a hash-table, where
      comparisons are done using physical equality. *)

  module H = Hashtbl.Make(
    struct 
      type t = Obj.t 
      let equal = (==) 
      let hash o = Hashtbl.hash (magic o : int)
    end)
	       
  let node_table = (H.create 257 : unit H.t)
		     
  let in_table o = try H.find node_table o; true with Not_found -> false
      
  let add_in_table o = H.add node_table o ()
			 
  let reset_table () = H.clear node_table
			 
  (*s Objects are traversed recursively, as soon as their tags are less than
      [no_scan_tag]. [count] records the numbers of words already visited. *)

  let size_of_double = size (repr 1.0)
			 
  let count = ref 0
		
  let rec traverse t =
    if not (in_table t) then begin
      add_in_table t;
      if is_block t then begin
	let n = size t in
	let tag = tag t in
	if tag < no_scan_tag then begin
	  count := !count + 1 + n;
	  for i = 0 to n - 1 do
      	    let f = field t i in 
	    if is_block f then traverse f
	  done
	end else if tag = string_tag then
	  count := !count + 1 + n 
	else if tag = double_tag then
	  count := !count + size_of_double
	else if tag = double_array_tag then
	  count := !count + 1 + size_of_double * n 
	else
	  incr count
      end
    end
      
  (*s Sizes of objects in words and in bytes. The size in bytes is computed
      system-independently according to [Sys.word_size]. *)

  let size_w o =
    reset_table ();
    count := 0;
    traverse (repr o);
    !count

  let size_b o = (size_w o) * (Sys.word_size / 8)

  let size_kb o = (size_w o) / (8192 / Sys.word_size)

end

let size_w = Size.size_w
let size_b = Size.size_b
let size_kb = Size.size_kb

(*s Total size of the allocated ocaml heap. *)

let heap_size () =
  let stat = Gc.stat ()
  and control = Gc.get () in
  let max_words_total = stat.Gc.heap_words + control.Gc.minor_heap_size in
  (max_words_total * Sys.word_size / 8)

let heap_size_kb () = (heap_size () + 1023) / 1024
