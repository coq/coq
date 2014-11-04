(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

type 'a cmp = 'a -> 'a -> int
type 'a eq = 'a -> 'a -> bool

module type S = module type of List

module type ExtS =
sig
  include S
  val compare : 'a cmp -> 'a list cmp
  val equal : 'a eq -> 'a list eq
  val is_empty : 'a list -> bool
  val init : int -> (int -> 'a) -> 'a list
  val mem_f : 'a eq -> 'a -> 'a list -> bool
  val add_set : 'a eq -> 'a -> 'a list -> 'a list
  val eq_set : 'a eq -> 'a list -> 'a list -> bool
  val intersect : 'a eq -> 'a list -> 'a list -> 'a list
  val union : 'a eq -> 'a list -> 'a list -> 'a list
  val unionq : 'a list -> 'a list -> 'a list
  val subtract : 'a eq -> 'a list -> 'a list -> 'a list
  val subtractq : 'a list -> 'a list -> 'a list
  val interval : int -> int -> int list
  val make : int -> 'a -> 'a list
  val assign : 'a list -> int -> 'a -> 'a list
  val distinct : 'a list -> bool
  val distinct_f : 'a cmp -> 'a list -> bool
  val duplicates : 'a eq -> 'a list -> 'a list
  val filter2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list * 'b list
  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  val map_filter_i : (int -> 'a -> 'b option) -> 'a list -> 'b list
  val filter_with : bool list -> 'a list -> 'a list
  val smartmap : ('a -> 'a) -> 'a list -> 'a list
  val map_left : ('a -> 'b) -> 'a list -> 'b list
  val map_i : (int -> 'a -> 'b) -> int -> 'a list -> 'b list
  val map2_i :
    (int -> 'a -> 'b -> 'c) -> int -> 'a list -> 'b list -> 'c list
  val map3 :
    ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list
  val map4 :
    ('a -> 'b -> 'c -> 'd -> 'e) -> 'a list -> 'b list -> 'c list -> 'd list -> 'e list
  val filteri :
    (int -> 'a -> bool) -> 'a list -> 'a list
  val smartfilter : ('a -> bool) -> 'a list -> 'a list
  val index : 'a eq -> 'a -> 'a list -> int
  val index0 : 'a eq -> 'a -> 'a list -> int
  val iteri :  (int -> 'a -> unit) -> 'a list -> unit
  val fold_left_until : ('c -> 'a -> 'c CSig.until) -> 'c -> 'a list -> 'c
  val fold_right_i :  (int -> 'a -> 'b -> 'b) -> int -> 'a list -> 'b -> 'b
  val fold_left_i :  (int -> 'a -> 'b -> 'a) -> int -> 'a -> 'b list -> 'a
  val fold_right_and_left :
      ('a -> 'b -> 'b list -> 'a) -> 'b list -> 'a -> 'a
  val fold_left3 : ('a -> 'b -> 'c -> 'd -> 'a) -> 'a -> 'b list -> 'c list -> 'd list -> 'a
  val for_all_i : (int -> 'a -> bool) -> int -> 'a list -> bool
  val except : 'a eq -> 'a -> 'a list -> 'a list
  val remove : 'a eq -> 'a -> 'a list -> 'a list
  val remove_first : ('a -> bool) -> 'a list -> 'a list
  val insert : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
  val for_all2eq : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val sep_last : 'a list -> 'a * 'a list
  val find_map : ('a -> 'b option) -> 'a list -> 'b
  val uniquize : 'a list -> 'a list
  val sort_uniquize : 'a cmp -> 'a list -> 'a list
  val merge_uniq : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list
  val subset : 'a list -> 'a list -> bool
  val chop : int -> 'a list -> 'a list * 'a list
  exception IndexOutOfRange
  val goto : int -> 'a list -> 'a list * 'a list
  val split_when : ('a -> bool) -> 'a list -> 'a list * 'a list
  val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
  val firstn : int -> 'a list -> 'a list
  val last : 'a list -> 'a
  val lastn : int -> 'a list -> 'a list
  val skipn : int -> 'a list -> 'a list
  val skipn_at_least : int -> 'a list -> 'a list
  val addn : int -> 'a -> 'a list -> 'a list
  val prefix_of : 'a eq -> 'a list -> 'a list -> bool
  val drop_prefix : 'a eq -> 'a list -> 'a list -> 'a list
  val drop_last : 'a list -> 'a list
  val map_append : ('a -> 'b list) -> 'a list -> 'b list
  val map_append2 : ('a -> 'b -> 'c list) -> 'a list -> 'b list -> 'c list
  val share_tails : 'a list -> 'a list -> 'a list * 'a list * 'a list
  val fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  val fold_map' : ('b -> 'a -> 'c * 'a) -> 'b list -> 'a -> 'c list * 'a
  val map_assoc : ('a -> 'b) -> ('c * 'a) list -> ('c * 'b) list
  val assoc_f : 'a eq -> 'a -> ('a * 'b) list -> 'b
  val remove_assoc_f : 'a eq -> 'a -> ('a * 'b) list -> ('a * 'b) list
  val mem_assoc_f : 'a eq -> 'a -> ('a * 'b) list -> bool
  val cartesian : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val cartesians : ('a -> 'b -> 'b) -> 'b -> 'a list list -> 'b list
  val combinations : 'a list list -> 'a list list
  val combine3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list
  val cartesians_filter :
    ('a -> 'b -> 'b option) -> 'b -> 'a list list -> 'b list
  val factorize_left : 'a eq -> ('a * 'b) list -> ('a * 'b list) list

  module type MonoS = sig
    type elt
    val equal : elt list -> elt list -> bool
    val mem : elt -> elt list -> bool
    val assoc : elt -> (elt * 'a) list -> 'a
    val mem_assoc : elt -> (elt * 'a) list -> bool
    val remove_assoc : elt -> (elt * 'a) list -> (elt * 'a) list
    val mem_assoc_sym : elt -> ('a * elt) list -> bool
  end

end

include List

(** Tail-rec implementation of usual functions. This is a well-known trick used
    in, for instance, ExtLib and Batteries. *)

type 'a cell = {
  head : 'a;
  mutable tail : 'a list;
}

external cast : 'a cell -> 'a list = "%identity"

let rec map_loop f p = function
| [] -> ()
| x :: l ->
  let c = { head = f x; tail = [] } in
  p.tail <- cast c;
  map_loop f c l

let map f = function
| [] -> []
| x :: l ->
  let c = { head = f x; tail = [] } in
  map_loop f c l;
  cast c

let rec map2_loop f p l1 l2 = match l1, l2 with
| [], [] -> ()
| x :: l1, y :: l2 ->
  let c = { head = f x y; tail = [] } in
  p.tail <- cast c;
  map2_loop f c l1 l2
| _ -> invalid_arg "List.map2"

let map2 f l1 l2 = match l1, l2 with
| [], [] -> []
| x :: l1, y :: l2 ->
  let c = { head = f x y; tail = [] } in
  map2_loop f c l1 l2;
  cast c
| _ -> invalid_arg "List.map2"

let rec append_loop p tl = function
| [] -> p.tail <- tl
| x :: l ->
  let c = { head = x; tail = [] } in
  p.tail <- cast c;
  append_loop c tl l

let append l1 l2 = match l1 with
| [] -> l2
| x :: l ->
  let c = { head = x; tail = [] } in
  append_loop c l2 l;
  cast c

let rec copy p = function
| [] -> p
| x :: l ->
  let c = { head = x; tail = [] } in
  p.tail <- cast c;
  copy c l

let rec init_loop len f p i =
  if Int.equal i len then ()
  else
    let c = { head = f i; tail = [] } in
    p.tail <- cast c;
    init_loop len f c (succ i)

let init len f =
  if len < 0 then invalid_arg "List.init"
  else if Int.equal len 0 then []
  else
    let c = { head = f 0; tail = [] } in
    init_loop len f c 1;
    cast c

let rec concat_loop p = function
| [] -> ()
| x :: l -> concat_loop (copy p x) l

let concat l =
  let dummy = { head = Obj.magic 0; tail = [] } in
  concat_loop dummy l;
  dummy.tail

let flatten = concat

let rec split_loop p q = function
| [] -> ()
| (x, y) :: l ->
  let cl = { head = x; tail = [] } in
  let cr = { head = y; tail = [] } in
  p.tail <- cast cl;
  q.tail <- cast cr;
  split_loop cl cr l

let split = function
| [] -> [], []
| (x, y) :: l ->
  let cl = { head = x; tail = [] } in
  let cr = { head = y; tail = [] } in
  split_loop cl cr l;
  (cast cl, cast cr)

let rec combine_loop p l1 l2 = match l1, l2 with
| [], [] -> ()
| x :: l1, y :: l2 ->
  let c = { head = (x, y); tail = [] } in
  p.tail <- cast c;
  combine_loop c l1 l2
| _ -> invalid_arg "List.combine"

let combine l1 l2 = match l1, l2 with
| [], [] -> []
| x :: l1, y :: l2 ->
  let c = { head = (x, y); tail = [] } in
  combine_loop c l1 l2;
  cast c
| _ -> invalid_arg "List.combine"

let rec filter_loop f p = function
| [] -> ()
| x :: l ->
  if f x then
    let c = { head = x; tail = [] } in
    let () = p.tail <- cast c in
    filter_loop f c l
  else
    filter_loop f p l

let filter f l =
  let c = { head = Obj.magic 0; tail = [] } in
  filter_loop f c l;
  c.tail

(** FIXME: Already present in OCaml 4.00 *)

let rec map_i_loop f i p = function
| [] -> ()
| x :: l ->
  let c = { head = f i x; tail = [] } in
  p.tail <- cast c;
  map_i_loop f (succ i) c l

let map_i f i = function
| [] -> []
| x :: l ->
  let c = { head = f i x; tail = [] } in
  map_i_loop f (succ i) c l;
  cast c

(** Extensions of OCaml Stdlib *)

let rec compare cmp l1 l2 =
  if l1 == l2 then 0 else
  match l1,l2 with
      [], [] -> 0
    | _::_, [] -> 1
    | [], _::_ -> -1
    | x1::l1, x2::l2 ->
        (match cmp x1 x2 with
           | 0 -> compare cmp l1 l2
           | c -> c)

let rec equal cmp l1 l2 =
  l1 == l2 ||
  match l1, l2 with
    | [], [] -> true
    | x1 :: l1, x2 :: l2 ->
      cmp x1 x2 && equal cmp l1 l2
    | _ -> false

let is_empty = function
| [] -> true
| _ -> false

let mem_f cmp x l = List.exists (cmp x) l

let intersect cmp l1 l2 =
  filter (fun x -> mem_f cmp x l2) l1

let union cmp l1 l2 =
  let rec urec = function
    | [] -> l2
    | a::l -> if mem_f cmp a l2 then urec l else a::urec l
  in
  urec l1

let subtract cmp l1 l2 =
  if is_empty l2 then l1
  else List.filter (fun x -> not (mem_f cmp x l2)) l1

let unionq l1 l2 = union (==) l1 l2
let subtractq l1 l2 = subtract (==) l1 l2

let interval n m =
  let rec interval_n (l,m) =
    if n > m then l else interval_n (m::l, pred m)
  in
  interval_n ([], m)

let addn n v =
  let rec aux n l =
    if Int.equal n 0 then l
    else aux (pred n) (v :: l)
  in
  if n < 0 then invalid_arg "List.addn"
  else aux n

let make n v = addn n v []

let assign l n e =
  let rec assrec stk l i = match l, i with
    | ((h::t), 0) -> List.rev_append stk (e :: t)
    | ((h::t), n) -> assrec (h :: stk) t (pred n)
    | ([], _) -> failwith "List.assign"
  in
  assrec [] l n

let rec smartmap f l = match l with
    [] -> l
  | h::tl ->
      let h' = f h and tl' = smartmap f tl in
        if h'==h && tl'==tl then l
        else h'::tl'

let map_left = map

let map2_i f i l1 l2 =
  let rec map_i i = function
    | ([], []) -> []
    | ((h1::t1), (h2::t2)) -> let v = f i h1 h2 in v :: map_i (succ i) (t1,t2)
    | (_, _) -> invalid_arg "map2_i"
  in
  map_i i (l1,l2)

let map3 f l1 l2 l3 =
  let rec map = function
    | ([], [], []) -> []
    | ((h1::t1), (h2::t2), (h3::t3)) -> let v = f h1 h2 h3 in v::map (t1,t2,t3)
    | (_, _, _) -> invalid_arg "map3"
  in
  map (l1,l2,l3)

let map4 f l1 l2 l3 l4 =
  let rec map = function
    | ([], [], [], []) -> []
    | ((h1::t1), (h2::t2), (h3::t3), (h4::t4)) -> let v = f h1 h2 h3 h4 in v::map (t1,t2,t3,t4)
    | (_, _, _, _) -> invalid_arg "map4"
  in
  map (l1,l2,l3,l4)

let rec smartfilter f l = match l with
    [] -> l
  | h::tl ->
      let tl' = smartfilter f tl in
        if f h then
          if tl' == tl then l
          else h :: tl'
        else tl'

let rec index_f f x l n = match l with
| [] -> raise Not_found
| y :: l -> if f x y then n else index_f f x l (succ n)

let index f x l = index_f f x l 1

let index0 f x l = index_f f x l 0

let fold_left_until f accu s =
  let rec aux accu = function
    | [] -> accu
    | x :: xs -> match f accu x with CSig.Stop x -> x | CSig.Cont i -> aux i xs in
  aux accu s

let fold_right_i f i l =
  let rec it_f i l a = match l with
    | [] -> a
    | b::l -> f (i-1) b (it_f (i-1) l a)
  in
  it_f (List.length l + i) l

let fold_left_i f =
  let rec it_list_f i a = function
    | [] -> a
    | b::l -> it_list_f (i+1) (f i a b) l
  in
  it_list_f

let rec fold_left3 f accu l1 l2 l3 =
  match (l1, l2, l3) with
    ([], [], []) -> accu
  | (a1::l1, a2::l2, a3::l3) -> fold_left3 f (f accu a1 a2 a3) l1 l2 l3
  | (_, _, _) -> invalid_arg "List.fold_left3"

(* [fold_right_and_left f [a1;...;an] hd =
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

let fold_right_and_left f l hd =
  let rec aux tl = function
    | [] -> hd
    | a::l -> let hd = aux (a::tl) l in f hd a tl
   in aux [] l

let iteri f l = fold_left_i (fun i _ x -> f i x) 0 () l

let for_all_i p =
  let rec for_all_p i = function
    | [] -> true
    | a::l -> p i a && for_all_p (i+1) l
  in
  for_all_p

let except cmp x l = List.filter (fun y -> not (cmp x y)) l

let remove = except (* Alias *)

let rec remove_first p = function
  | b::l when p b -> l
  | b::l -> b::remove_first p l
  | [] -> raise Not_found

let insert p v l =
  let rec insrec = function
    | [] -> [v]
    | h::tl -> if p v h then v::h::tl else h::insrec tl
  in
  insrec l

let add_set cmp x l = if mem_f cmp x l then l else x :: l

(** List equality up to permutation (but considering multiple occurrences) *)

let eq_set cmp l1 l2 =
  let rec aux l1 = function
  | [] -> is_empty l1
  | a::l2 -> aux (remove_first (cmp a) l1) l2 in
  try aux l1 l2 with Not_found -> false

let for_all2eq f l1 l2 =
  try List.for_all2 f l1 l2 with Invalid_argument _ -> false

let filteri p =
  let rec filter_i_rec i = function
    | [] -> []
    | x::l -> let l' = filter_i_rec (succ i) l in if p i x then x::l' else l'
  in
  filter_i_rec 0

let rec sep_last = function
  | [] -> failwith "sep_last"
  | hd::[] -> (hd,[])
  | hd::tl -> let (l,tl) = sep_last tl in (l,hd::tl)

let rec find_map f = function
| [] -> raise Not_found
| x :: l ->
  match f x with
  | None -> find_map f l
  | Some y -> y

(* FIXME: we should avoid relying on the generic hash function,
   just as we'd better avoid Pervasives.compare *)

let uniquize l =
  let visited = Hashtbl.create 23 in
  let rec aux acc changed = function
    | h::t -> if Hashtbl.mem visited h then aux acc true t else
          begin
            Hashtbl.add visited h h;
            aux (h::acc) changed t
          end
    | [] -> if changed then List.rev acc else l
  in aux [] false l

(** [sort_uniquize] might be an alternative to the hashtbl-based
    [uniquize], when the order of the elements is irrelevant *)

let rec uniquize_sorted cmp = function
  | a::b::l when Int.equal (cmp a b) 0 -> uniquize_sorted cmp (a::l)
  | a::l -> a::uniquize_sorted cmp l
  | [] -> []

let sort_uniquize cmp l = uniquize_sorted cmp (List.sort cmp l)

(* FIXME: again, generic hash function *)

let distinct l =
  let visited = Hashtbl.create 23 in
  let rec loop = function
    | h::t ->
        if Hashtbl.mem visited h then false
        else
          begin
            Hashtbl.add visited h h;
            loop t
          end
    | [] -> true
  in loop l

let distinct_f cmp l =
  let rec loop = function
    | a::b::_ when Int.equal (cmp a b) 0 -> false
    | a::l -> loop l
    | [] -> true
  in loop (List.sort cmp l)

let rec merge_uniq cmp l1 l2 =
  match l1, l2 with
  | [], l2 -> l2
  | l1, [] -> l1
  | h1 :: t1, h2 :: t2 ->
      let c = cmp h1 h2 in
      if Int.equal c 0
      then h1 :: merge_uniq cmp t1 t2
      else if c <= 0
      then h1 :: merge_uniq cmp t1 l2
      else h2 :: merge_uniq cmp l1 t2

let rec duplicates cmp = function
  | [] -> []
  | x::l ->
      let l' = duplicates cmp l in
      if mem_f cmp x l then add_set cmp x l' else l'

let rec filter2_loop f p q l1 l2 = match l1, l2 with
| [], [] -> ()
| x :: l1, y :: l2 ->
  if f x y then
    let c1 = { head = x; tail = [] } in
    let c2 = { head = y; tail = [] } in
    let () = p.tail <- cast c1 in
    let () = q.tail <- cast c2 in
    filter2_loop f c1 c2 l1 l2
  else
    filter2_loop f p q l1 l2
| _ -> invalid_arg "List.filter2"

let filter2 f l1 l2 =
  let c1 = { head = Obj.magic 0; tail = [] } in
  let c2 = { head = Obj.magic 0; tail = [] } in
  filter2_loop f c1 c2 l1 l2;
  (c1.tail, c2.tail)

let rec map_filter f = function
  | [] -> []
  | x::l ->
      let l' = map_filter f l in
      match f x with None -> l' | Some y -> y::l'

let map_filter_i f =
  let rec aux i = function
    | [] -> []
    | x::l ->
      let l' = aux (succ i) l in
        match f i x with None -> l' | Some y -> y::l'
  in aux 0

let rec filter_with filter l = match filter, l with
| [], [] -> []
| true :: filter, x :: l -> x :: filter_with filter l
| false :: filter, _ :: l -> filter_with filter l
| _ -> invalid_arg "List.filter_with"

(* FIXME: again, generic hash function *)

let subset l1 l2 =
  let t2 = Hashtbl.create 151 in
  List.iter (fun x -> Hashtbl.add t2 x ()) l2;
  let rec look = function
    | [] -> true
    | x::ll -> try Hashtbl.find t2 x; look ll with Not_found -> false
  in
  look l1

(** [goto i l] splits [l] into two lists [(l1,l2)] such that
    [(List.rev l1)++l2=l] and [l1] has length [i].  It raises
    [IndexOutOfRange] when [i] is negative or greater than the
    length of [l]. *)
exception IndexOutOfRange
let goto n l =
  let rec goto i acc = function
    | tl when Int.equal i 0 -> (acc, tl)
    | h::t -> goto (pred i) (h::acc) t
    | [] -> raise IndexOutOfRange
  in
  goto n [] l

(* [chop i l] splits [l] into two lists [(l1,l2)] such that
   [l1++l2=l] and [l1] has length [i].
   It raises [Failure] when [i] is negative or greater than the length of [l]  *)

let chop n l =
  try let (h,t) = goto n l in (List.rev h,t)
  with IndexOutOfRange -> failwith "List.chop"
    (* spiwack: should raise [IndexOutOfRange] but I'm afraid of missing
       a try/with when replacing the exception. *)

(* [split_when p l] splits [l] into two lists [(l1,a::l2)] such that
    [l1++(a::l2)=l], [p a=true] and [p b = false] for every element [b] of [l1].
    If there is no such [a], then it returns [(l,[])] instead *)
let split_when p =
  let rec split_when_loop x y =
    match y with
      | []      -> (List.rev x,[])
      | (a::l)  -> if (p a) then (List.rev x,y) else split_when_loop (a::x) l
  in
  split_when_loop []

let rec split3 = function
  | [] -> ([], [], [])
  | (x,y,z)::l ->
      let (rx, ry, rz) = split3 l in (x::rx, y::ry, z::rz)

let firstn n l =
  let rec aux acc = function
    | (0, l) -> List.rev acc
    | (n, (h::t)) -> aux (h::acc) (pred n, t)
    | _ -> failwith "firstn"
  in
  aux [] (n,l)

let rec last = function
  | [] -> failwith "List.last"
  | [x] -> x
  | _ :: l -> last l

let lastn n l =
  let len = List.length l in
  let rec aux m l =
    if Int.equal m n then l else aux (m - 1) (List.tl l)
  in
  if len < n then failwith "lastn" else aux len l

let rec skipn n l = match n,l with
  | 0, _ -> l
  | _, [] -> failwith "List.skipn"
  | n, _::l -> skipn (pred n) l

let skipn_at_least n l =
  try skipn n l with Failure _ -> []

let prefix_of cmp prefl l =
  let rec prefrec = function
    | (h1::t1, h2::t2) -> cmp h1 h2 && prefrec (t1,t2)
    | ([], _) -> true
    | _ -> false
  in
  prefrec (prefl,l)

(** if [l=p++t] then [drop_prefix p l] is [t] else [l] *)

let drop_prefix cmp p l =
  let rec drop_prefix_rec = function
    | (h1::tp, h2::tl) when cmp h1 h2 -> drop_prefix_rec (tp,tl)
    | ([], tl) -> tl
    | _ -> l
  in
  drop_prefix_rec (p,l)

let map_append f l = List.flatten (List.map f l)

let map_append2 f l1 l2 = List.flatten (List.map2 f l1 l2)

let share_tails l1 l2 =
  let rec shr_rev acc = function
    | ((x1::l1), (x2::l2)) when x1 == x2 -> shr_rev (x1::acc) (l1,l2)
    | (l1,l2) -> (List.rev l1, List.rev l2, acc)
  in
  shr_rev [] (List.rev l1, List.rev l2)

let rec fold_map f e = function
  |  []  -> (e,[])
  |  h::t ->
       let e',h' = f e h in
       let e'',t' = fold_map f e' t in
         e'',h'::t'

(* (* tail-recursive version of the above function *)
let fold_map f e l =
  let g (e,b') h =
    let (e',h') = f e h in
      (e',h'::b')
  in
  let (e',lrev) = List.fold_left g (e,[]) l in
    (e',List.rev lrev)
*)

(* The same, based on fold_right, with the effect accumulated on the right *)
let fold_map' f l e =
  List.fold_right (fun x (l,e) -> let (y,e) = f x e in (y::l,e)) l ([],e)

let map_assoc f = List.map (fun (x,a) -> (x,f a))

let rec assoc_f f a = function
  | (x, e) :: xs -> if f a x then e else assoc_f f a xs
  | [] -> raise Not_found

let remove_assoc_f f a l =
  try remove_first (fun (x,_) -> f a x) l with Not_found -> l

let mem_assoc_f f a l = List.exists (fun (x,_) -> f a x) l

(* A generic cartesian product: for any operator (**),
   [cartesian (**) [x1;x2] [y1;y2] = [x1**y1; x1**y2; x2**y1; x2**y1]],
   and so on if there are more elements in the lists. *)

let cartesian op l1 l2 =
  map_append (fun x -> List.map (op x) l2) l1

(* [cartesians] is an n-ary cartesian product: it iterates
   [cartesian] over a list of lists.  *)

let cartesians op init ll =
  List.fold_right (cartesian op) ll [init]

(* combinations [[a;b];[c;d]] gives [[a;c];[a;d];[b;c];[b;d]] *)

let combinations l = cartesians (fun x l -> x::l) [] l

let rec combine3 x y z = 
  match x, y, z with
  | [], [], [] -> []
  | (x :: xs), (y :: ys), (z :: zs) ->
      (x, y, z) :: combine3 xs ys zs
  | _, _, _ -> invalid_arg "List.combine3"
  
(* Keep only those products that do not return None *)

let cartesian_filter op l1 l2 =
  map_append (fun x -> map_filter (op x) l2) l1

(* Keep only those products that do not return None *)

let cartesians_filter op init ll =
  List.fold_right (cartesian_filter op) ll [init]

(* Drop the last element of a list *)

let rec drop_last = function
  | [] -> assert false
  | hd :: [] -> []
  | hd :: tl -> hd :: drop_last tl

(* Factorize lists of pairs according to the left argument *)
let rec factorize_left cmp = function
  | (a,b)::l ->
      let al,l' = partition (fun (a',_) -> cmp a a') l in
      (a,(b::List.map snd al)) :: factorize_left cmp l'
  | [] -> []

module type MonoS = sig
  type elt
  val equal : elt list -> elt list -> bool
  val mem : elt -> elt list -> bool
  val assoc : elt -> (elt * 'a) list -> 'a
  val mem_assoc : elt -> (elt * 'a) list -> bool
  val remove_assoc : elt -> (elt * 'a) list -> (elt * 'a) list
  val mem_assoc_sym : elt -> ('a * elt) list -> bool
end
