(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

module type S =
sig
  val length : 'a list -> int
  val hd : 'a list -> 'a
  val tl : 'a list -> 'a list
  val nth : 'a list -> int -> 'a
  val rev : 'a list -> 'a list
  val append : 'a list -> 'a list -> 'a list
  val rev_append : 'a list -> 'a list -> 'a list
  val concat : 'a list list -> 'a list
  val flatten : 'a list list -> 'a list
  val iter : ('a -> unit) -> 'a list -> unit
  val map : ('a -> 'b) -> 'a list -> 'b list
  val rev_map : ('a -> 'b) -> 'a list -> 'b list
  val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
  val fold_right : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val iter2 : ('a -> 'b -> unit) -> 'a list -> 'b list -> unit
  val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val rev_map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
  val fold_right2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val for_all : ('a -> bool) -> 'a list -> bool
  val exists : ('a -> bool) -> 'a list -> bool
  val for_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val exists2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val mem : 'a -> 'a list -> bool
  val memq : 'a -> 'a list -> bool
  val find : ('a -> bool) -> 'a list -> 'a
  val filter : ('a -> bool) -> 'a list -> 'a list
  val find_all : ('a -> bool) -> 'a list -> 'a list
  val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
  val assoc : 'a -> ('a * 'b) list -> 'b
  val assq : 'a -> ('a * 'b) list -> 'b
  val mem_assoc : 'a -> ('a * 'b) list -> bool
  val mem_assq : 'a -> ('a * 'b) list -> bool
  val remove_assoc : 'a -> ('a * 'b) list -> ('a * 'b) list
  val remove_assq : 'a -> ('a * 'b) list -> ('a * 'b) list
  val split : ('a * 'b) list -> 'a list * 'b list
  val combine : 'a list -> 'b list -> ('a * 'b) list
  val sort : ('a -> 'a -> int) -> 'a list -> 'a list
  val stable_sort : ('a -> 'a -> int) -> 'a list -> 'a list
  val fast_sort : ('a -> 'a -> int) -> 'a list -> 'a list
  val merge : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list
end

module type ExtS =
sig
  include S
  val compare : ('a -> 'a -> int) -> 'a list -> 'a list -> int
  val equal : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
  val add_set : 'a -> 'a list -> 'a list
  val eq_set : 'a list -> 'a list -> bool
  val intersect : 'a list -> 'a list -> 'a list
  val union : 'a list -> 'a list -> 'a list
  val unionq : 'a list -> 'a list -> 'a list
  val subtract : 'a list -> 'a list -> 'a list
  val subtractq : 'a list -> 'a list -> 'a list

  (** [tabulate f n] builds [[f 0; ...; f (n-1)]] *)
  val tabulate : (int -> 'a) -> int -> 'a list
  val interval : int -> int -> int list
  val make : int -> 'a -> 'a list
  val assign : 'a list -> int -> 'a -> 'a list
  val distinct : 'a list -> bool
  val duplicates : 'a list -> 'a list
  val filter2 : ('a -> 'b -> bool) -> 'a list * 'b list -> 'a list * 'b list
  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  val map_filter_i : (int -> 'a -> 'b option) -> 'a list -> 'b list
  val filter_with : bool list -> 'a list -> 'a list

  (** [smartmap f [a1...an] = List.map f [a1...an]] but if for all i
    [ f ai == ai], then [smartmap f l==l] *)
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

  (** [smartfilter f [a1...an] = List.filter f [a1...an]] but if for all i
    [f ai = true], then [smartfilter f l==l] *)
  val smartfilter : ('a -> bool) -> 'a list -> 'a list

  (** [index] returns the 1st index of an element in a list (counting from 1) *)
  val index : 'a -> 'a list -> int
  val index_f : ('a -> 'a -> bool) -> 'a -> 'a list -> int

  (** [unique_index x l] returns [Not_found] if [x] doesn't occur exactly once *)
  val unique_index : 'a -> 'a list -> int

  (** [index0] behaves as [index] except that it starts counting at 0 *)
  val index0 : 'a -> 'a list -> int
  val index0_f : ('a -> 'a -> bool) -> 'a -> 'a list -> int
  val iteri :  (int -> 'a -> unit) -> 'a list -> unit
  val fold_right_i :  (int -> 'a -> 'b -> 'b) -> int -> 'a list -> 'b -> 'b
  val fold_left_i :  (int -> 'a -> 'b -> 'a) -> int -> 'a -> 'b list -> 'a
  val fold_right_and_left :
      ('a -> 'b -> 'b list -> 'a) -> 'b list -> 'a -> 'a
  val fold_left3 : ('a -> 'b -> 'c -> 'd -> 'a) -> 'a -> 'b list -> 'c list -> 'd list -> 'a
  val for_all_i : (int -> 'a -> bool) -> int -> 'a list -> bool
  val except : 'a -> 'a list -> 'a list
  val remove : 'a -> 'a list -> 'a list
  val remove_first : 'a -> 'a list -> 'a list
  val remove_assoc_in_triple : 'a -> ('a * 'b * 'c) list -> ('a * 'b * 'c) list
  val assoc_snd_in_triple : 'a -> ('a * 'b * 'c) list -> 'b
  val for_all2eq : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val sep_last : 'a list -> 'a * 'a list
  val find_map : ('a -> 'b option) -> 'a list -> 'b
  val uniquize : 'a list -> 'a list

  (** merges two sorted lists and preserves the uniqueness property: *)
  val merge_uniq : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list
  val subset : 'a list -> 'a list -> bool
  val chop : int -> 'a list -> 'a list * 'a list
  (* former [split_at] was a duplicate of [chop] *)
  val split_when : ('a -> bool) -> 'a list -> 'a list * 'a list
  val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
  val firstn : int -> 'a list -> 'a list
  val last : 'a list -> 'a
  val lastn : int -> 'a list -> 'a list
  val skipn : int -> 'a list -> 'a list
  val skipn_at_least : int -> 'a list -> 'a list
  val addn : int -> 'a -> 'a list -> 'a list
  val prefix_of : 'a list -> 'a list -> bool

  (** [drop_prefix p l] returns [t] if [l=p++t] else return [l] *)
  val drop_prefix : 'a list -> 'a list -> 'a list
  val drop_last : 'a list -> 'a list

  (** [map_append f [x1; ...; xn]] returns [(f x1)@(f x2)@...@(f xn)] *)
  val map_append : ('a -> 'b list) -> 'a list -> 'b list

  (** raises [Invalid_argument] if the two lists don't have the same length *)
  val map_append2 : ('a -> 'b -> 'c list) -> 'a list -> 'b list -> 'c list
  val share_tails : 'a list -> 'a list -> 'a list * 'a list * 'a list

  (** [fold_map f e_0 [l_1...l_n] = e_n,[k_1...k_n]]
    where [(e_i,k_i)=f e_{i-1} l_i] *)
  val fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  val fold_map' : ('b -> 'a -> 'c * 'a) -> 'b list -> 'a -> 'c list * 'a
  val map_assoc : ('a -> 'b) -> ('c * 'a) list -> ('c * 'b) list
  val assoc_f : ('a -> 'a -> bool) -> 'a -> ('a * 'b) list -> 'b

  (** A generic cartesian product: for any operator (**),
    [cartesian (**) [x1;x2] [y1;y2] = [x1**y1; x1**y2; x2**y1; x2**y1]],
    and so on if there are more elements in the lists. *)
  val cartesian : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

  (** [cartesians] is an n-ary cartesian product: it iterates
    [cartesian] over a list of lists.  *)
  val cartesians : ('a -> 'b -> 'b) -> 'b -> 'a list list -> 'b list

  (** combinations [[a;b];[c;d]] returns [[a;c];[a;d];[b;c];[b;d]] *)
  val combinations : 'a list list -> 'a list list
  val combine3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list

  val cartesians_filter :
    ('a -> 'b -> 'b option) -> 'b -> 'a list list -> 'b list
  (** Keep only those products that do not return None *)

  val factorize_left : ('a * 'b) list -> ('a * 'b list) list

end

include List

(** Tail-rec implementation of usual functions. This is a well-known trick used
    in, for instance, ExtLib and Batteries. *)

type 'a cell = {
  head : 'a;
  mutable tail : 'a list;
}

external cast : 'a cell -> 'a list = "%identity"

let map f = function
| [] -> []
| x :: l ->
  let rec loop p = function
  | [] -> ()
  | x :: l ->
    let c = { head = f x; tail = [] } in
    p.tail <- cast c;
    loop c l
  in
  let c = { head = f x; tail = [] } in
  loop c l;
  cast c

let map2 f l1 l2 = match l1, l2 with
| [], [] -> []
| x :: l1, y :: l2 ->
  let rec loop p l1 l2 = match l1, l2 with
  | [], [] -> ()
  | x :: l1, y :: l2 ->
    let c = { head = f x y; tail = [] } in
    p.tail <- cast c;
    loop c l1 l2
  | _ -> invalid_arg "List.map2"
  in
  let c = { head = f x y; tail = [] } in
  loop c l1 l2;
  cast c
| _ -> invalid_arg "List.map2"

let append l1 l2 = match l1 with
| [] -> l2
| x :: l ->
  let rec loop p = function
  | [] -> p.tail <- l2
  | x :: l ->
    let c = { head = x; tail = [] } in
    p.tail <- cast c;
    loop c l
  in
  let c = { head = x; tail = [] } in
  loop c l;
  cast c

let concat l =
  let rec copy p = function
  | [] -> p
  | x :: l ->
    let c = { head = x; tail = [] } in
    p.tail <- cast c;
    copy c l
  in
  let rec loop p = function
  | [] -> ()
  | x :: l -> loop (copy p x) l
  in
  let dummy = { head = Obj.magic 0; tail = [] } in
  loop dummy l;
  dummy.tail

let flatten = concat

let split = function
| [] -> [], []
| (x, y) :: l ->
  let rec loop p q = function
  | [] -> ()
  | (x, y) :: l ->
    let cl = { head = x; tail = [] } in
    let cr = { head = y; tail = [] } in
    p.tail <- cast cl;
    q.tail <- cast cr;
    loop cl cr l
  in
  let cl = { head = x; tail = [] } in
  let cr = { head = y; tail = [] } in
  loop cl cr l;
  (cast cl, cast cr)

let combine l1 l2 = match l1, l2 with
| [], [] -> []
| x :: l1, y :: l2 ->
  let rec loop p l1 l2 = match l1, l2 with
  | [], [] -> ()
  | x :: l1, y :: l2 ->
    let c = { head = (x, y); tail = [] } in
    p.tail <- cast c;
    loop c l1 l2
  | _ -> invalid_arg "List.combine"
  in
  let c = { head = (x, y); tail = [] } in
  loop c l1 l2;
  cast c
| _ -> invalid_arg "List.combine"

let filter f l =
  let rec loop p = function
  | [] -> ()
  | x :: l ->
    if f x then
      let c = { head = x; tail = [] } in
      let () = p.tail <- cast c in
      loop c l
    else
      loop p l
  in
  let c = { head = Obj.magic 0; tail = [] } in
  loop c l;
  c.tail

(** FIXME: Already present in OCaml 4.00 *)

let map_i f i = function
| [] -> []
| x :: l ->
  let rec loop i p = function
  | [] -> ()
  | x :: l ->
    let c = { head = f i x; tail = [] } in
    p.tail <- cast c;
    loop (succ i) c l
  in
  let c = { head = f i x; tail = [] } in
  loop (succ i) c l;
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

let intersect l1 l2 =
  List.filter (fun x -> List.mem x l2) l1

let union l1 l2 =
  let rec urec = function
    | [] -> l2
    | a::l -> if List.mem a l2 then urec l else a::urec l
  in
  urec l1

let unionq l1 l2 =
  let rec urec = function
    | [] -> l2
    | a::l -> if List.memq a l2 then urec l else a::urec l
  in
  urec l1

let subtract l1 l2 =
  if l2 = [] then l1 else List.filter (fun x -> not (List.mem x l2)) l1

let subtractq l1 l2 =
  if l2 = [] then l1 else List.filter (fun x -> not (List.memq x l2)) l1

let tabulate f len =
  let rec loop p i =
    if len <= i then ()
    else
      let c = { head = f i; tail = [] } in
      let () = p.tail <- cast c in
      loop c (succ i)
  in
  let dummy = { head = Obj.magic 0; tail = [] } in
  loop dummy 0;
  dummy.tail

let interval n m =
  let rec interval_n (l,m) =
    if n > m then l else interval_n (m::l, pred m)
  in
  interval_n ([], m)

let addn n v =
  let rec aux n l =
    if n = 0 then l
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
          
let index_f f x =
  let rec index_x n = function
    | y::l -> if f x y then n else index_x (succ n) l
    | [] -> raise Not_found
  in
  index_x 1

let index0_f f x l = index_f f x l - 1

let index x =
  let rec index_x n = function
    | y::l -> if x = y then n else index_x (succ n) l
    | [] -> raise Not_found
  in
  index_x 1

let index0 x l = index x l - 1

let unique_index x =
  let rec index_x n = function
    | y::l ->
        if x = y then
          if List.mem x l then raise Not_found
          else n
        else index_x (succ n) l
    | [] -> raise Not_found
  in index_x 1

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

let except x l = List.filter (fun y -> not (x = y)) l

let remove = except (* Alias *)

let rec remove_first a = function
  | b::l when a = b -> l
  | b::l -> b::remove_first a l
  | [] -> raise Not_found

let rec remove_assoc_in_triple x = function
  | [] -> []
  | (y,_,_ as z)::l -> if x = y then l else z::remove_assoc_in_triple x l

let rec assoc_snd_in_triple x = function
    [] -> raise Not_found
  | (a,b,_)::l -> if Pervasives.compare a x = 0 then b else assoc_snd_in_triple x l

let add_set x l = if List.mem x l then l else x :: l

let eq_set l1 l2 =
  let rec aux l1 = function
  | [] -> l1 = []
  | a::l2 -> aux (remove_first a l1) l2 in
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

let uniquize l =
  let visited = Hashtbl.create 23 in
  let rec aux acc = function
    | h::t -> if Hashtbl.mem visited h then aux acc t else
          begin
            Hashtbl.add visited h h;
            aux (h::acc) t
          end
    | [] -> List.rev acc
  in aux [] l

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

let rec merge_uniq cmp l1 l2 =
  match l1, l2 with
  | [], l2 -> l2
  | l1, [] -> l1
  | h1 :: t1, h2 :: t2 ->
      let c = cmp h1 h2 in
      if c = 0
      then h1 :: merge_uniq cmp t1 t2
      else if c <= 0
      then h1 :: merge_uniq cmp t1 l2
      else h2 :: merge_uniq cmp l1 t2

let rec duplicates = function
  | [] -> []
  | x::l ->
      let l' = duplicates l in
      if List.mem x l then add_set x l' else l'

let rec filter2 f = function
  | [], [] as p -> p
  | d::dp, l::lp ->
     let (dp',lp' as p) = filter2 f (dp,lp) in
      if f d l then d::dp', l::lp' else p
  | _ -> invalid_arg "List.filter2"

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

let filter_along f filter l =
  snd (filter2 (fun b c -> f b) (filter,l))

let filter_with filter l =
  filter_along (fun x -> x) filter l

let subset l1 l2 =
  let t2 = Hashtbl.create 151 in
  List.iter (fun x -> Hashtbl.add t2 x ()) l2;
  let rec look = function
    | [] -> true
    | x::ll -> try Hashtbl.find t2 x; look ll with Not_found -> false
  in
  look l1

(* [chop i l] splits [l] into two lists [(l1,l2)] such that
   [l1++l2=l] and [l1] has length [i].
   It raises [Failure] when [i] is negative or greater than the length of [l]  *)

let chop n l =
  let rec chop_aux i acc = function
    | tl when i=0 -> (List.rev acc, tl)
    | h::t -> chop_aux (pred i) (h::acc) t
    | [] -> failwith "List.chop"
  in
  chop_aux n [] l

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
    if m = n then l else aux (m - 1) (List.tl l)
  in
  if len < n then failwith "lastn" else aux len l

let rec skipn n l = match n,l with
  | 0, _ -> l
  | _, [] -> failwith "List.skipn"
  | n, _::l -> skipn (pred n) l

let skipn_at_least n l =
  try skipn n l with Failure _ -> []

let prefix_of prefl l =
  let rec prefrec = function
    | (h1::t1, h2::t2) -> h1 = h2 && prefrec (t1,t2)
    | ([], _) -> true
    | (_, _) -> false
  in
    prefrec (prefl,l)

let drop_prefix p l =
(* if l=p++t then return t else l *)
  let rec drop_prefix_rec = function
    | ([], tl) -> Some tl
    | (_, []) -> None
    | (h1::tp, h2::tl) ->
        if h1 = h2 then drop_prefix_rec (tp,tl) else None
  in
    match drop_prefix_rec (p,l) with
      | Some r -> r
      | None -> l

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
  | _, _, _ -> raise (Invalid_argument "List.combine3")
  
(* Keep only those products that do not return None *)

let cartesian_filter op l1 l2 =
  map_append (fun x -> map_filter (op x) l2) l1

(* Keep only those products that do not return None *)

let cartesians_filter op init ll =
  List.fold_right (cartesian_filter op) ll [init]

(* Drop the last element of a list *)

let rec drop_last = function [] -> assert false | hd :: [] -> [] | hd :: tl -> hd :: drop_last tl

(* Factorize lists of pairs according to the left argument *)
let rec factorize_left = function
  | (a,b)::l ->
      let al,l' = partition (fun (a',b) -> a=a') l in
      (a,(b::List.map snd al)) :: factorize_left l'
  | [] ->
      []
