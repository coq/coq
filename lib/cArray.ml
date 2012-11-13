(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

module type S =
sig
  external length : 'a array -> int = "%array_length"
  external get : 'a array -> int -> 'a = "%array_safe_get"
  external set : 'a array -> int -> 'a -> unit = "%array_safe_set"
  external make : int -> 'a -> 'a array = "caml_make_vect"
  external create : int -> 'a -> 'a array = "caml_make_vect"
  val init : int -> (int -> 'a) -> 'a array
  val make_matrix : int -> int -> 'a -> 'a array array
  val create_matrix : int -> int -> 'a -> 'a array array
  val append : 'a array -> 'a array -> 'a array
  val concat : 'a array list -> 'a array
  val sub : 'a array -> int -> int -> 'a array
  val copy : 'a array -> 'a array
  val fill : 'a array -> int -> int -> 'a -> unit
  val blit : 'a array -> int -> 'a array -> int -> int -> unit
  val to_list : 'a array -> 'a list
  val of_list : 'a list -> 'a array
  val iter : ('a -> unit) -> 'a array -> unit
  val map : ('a -> 'b) -> 'a array -> 'b array
  val iteri : (int -> 'a -> unit) -> 'a array -> unit
  val mapi : (int -> 'a -> 'b) -> 'a array -> 'b array
  val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b array -> 'a
  val fold_right : ('b -> 'a -> 'a) -> 'b array -> 'a -> 'a
  val sort : ('a -> 'a -> int) -> 'a array -> unit
  val stable_sort : ('a -> 'a -> int) -> 'a array -> unit
  val fast_sort : ('a -> 'a -> int) -> 'a array -> unit
  external unsafe_get : 'a array -> int -> 'a = "%array_unsafe_get"
  external unsafe_set : 'a array -> int -> 'a -> unit = "%array_unsafe_set"
end

module type ExtS =
sig
  include S
  val compare : ('a -> 'a -> int) -> 'a array -> 'a array -> int
  val equal : ('a -> 'a -> bool) -> 'a array -> 'a array -> bool
  val exists : ('a -> bool) -> 'a array -> bool
  val for_all : ('a -> bool) -> 'a array -> bool
  val for_all2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool
  val for_all3 : ('a -> 'b -> 'c -> bool) ->
    'a array -> 'b array -> 'c array -> bool
  val for_all4 : ('a -> 'b -> 'c -> 'd -> bool) ->
    'a array -> 'b array -> 'c array -> 'd array -> bool
  val for_all_i : (int -> 'a -> bool) -> int -> 'a array -> bool
  val findi : (int -> 'a -> bool) -> 'a array -> int option
  val hd : 'a array -> 'a
  val tl : 'a array -> 'a array
  val last : 'a array -> 'a
  val cons : 'a -> 'a array -> 'a array
  val rev : 'a array -> unit
  val fold_right_i :
    (int -> 'b -> 'a -> 'a) -> 'b array -> 'a -> 'a
  val fold_left_i : (int -> 'a -> 'b -> 'a) -> 'a -> 'b array -> 'a
  val fold_right2 :
    ('a -> 'b -> 'c -> 'c) -> 'a array -> 'b array -> 'c -> 'c
  val fold_left2 :
    ('a -> 'b -> 'c -> 'a) -> 'a -> 'b array -> 'c array -> 'a
  val fold_left3 :
    ('a -> 'b -> 'c -> 'd -> 'a) -> 'a -> 'b array -> 'c array -> 'd array -> 'a
  val fold_left2_i :
    (int -> 'a -> 'b -> 'c -> 'a) -> 'a -> 'b array -> 'c array -> 'a
  val fold_left_from : int -> ('a -> 'b -> 'a) -> 'a -> 'b array -> 'a
  val map_to_list : ('a -> 'b) -> 'a array -> 'b list
  val chop : int -> 'a array -> 'a array * 'a array
  val smartmap : ('a -> 'a) -> 'a array -> 'a array
  val map2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
  val map2_i : (int -> 'a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
  val map3 :
    ('a -> 'b -> 'c -> 'd) -> 'a array -> 'b array -> 'c array -> 'd array
  val map_left : ('a -> 'b) -> 'a array -> 'b array
  val iter2 : ('a -> 'b -> unit) -> 'a array -> 'b array -> unit
  val fold_map' : ('a -> 'c -> 'b * 'c) -> 'a array -> 'c -> 'b array * 'c
  val fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b array -> 'a * 'c array
  val fold_map2' :
    ('a -> 'b -> 'c -> 'd * 'c) -> 'a array -> 'b array -> 'c -> 'd array * 'c
  val distinct : 'a array -> bool
  val rev_to_list : 'a array -> 'a list
  val filter_with : bool list -> 'a array -> 'a array
end

include Array

(* Arrays *)

let compare item_cmp v1 v2 =
  let c = compare (Array.length v1) (Array.length v2) in
  if c<>0 then c else
    let rec cmp = function
        -1 -> 0
      | i ->
          let c' = item_cmp v1.(i) v2.(i) in
          if c'<>0 then c'
          else cmp (i-1) in
    cmp (Array.length v1 - 1)

let equal cmp t1 t2 =
  if t1 == t2 then true else
  if not (Array.length t1 = Array.length t2) then false
  else
  let rec aux i =
    (i = Array.length t1) || (cmp t1.(i) t2.(i) && aux (i + 1))
  in aux 0

let exists f v =
  let rec exrec = function
    | -1 -> false
    | n -> (f v.(n)) || (exrec (n-1))
  in
  exrec ((Array.length v)-1)

let for_all f v =
  let rec allrec = function
    | -1 -> true
    | n -> (f v.(n)) && (allrec (n-1))
  in
  allrec ((Array.length v)-1)

let for_all2 f v1 v2 =
  let rec allrec = function
    | -1 -> true
    | n -> (f v1.(n) v2.(n)) && (allrec (n-1))
  in
  let lv1 = Array.length v1 in
  lv1 = Array.length v2 && allrec (pred lv1)

let for_all3 f v1 v2 v3 =
  let rec allrec = function
    | -1 -> true
    | n -> (f v1.(n) v2.(n) v3.(n)) && (allrec (n-1))
  in
  let lv1 = Array.length v1 in
  lv1 = Array.length v2 && lv1 = Array.length v3 && allrec (pred lv1)

let for_all4 f v1 v2 v3 v4 =
  let rec allrec = function
    | -1 -> true
    | n -> (f v1.(n) v2.(n) v3.(n) v4.(n)) && (allrec (n-1))
  in
  let lv1 = Array.length v1 in
  lv1 = Array.length v2 &&
  lv1 = Array.length v3 &&
  lv1 = Array.length v4 &&
    allrec (pred lv1)

let for_all_i f i v =
  let rec allrec i n = n = Array.length v || f i v.(n) && allrec (i+1) (n+1) in
  allrec i 0

exception Found of int

let findi (pred: int -> 'a -> bool) (arr: 'a array) : int option =
  try
    for i=0 to Array.length arr - 1 do if pred i (arr.(i)) then raise (Found i) done;
    None
  with Found i -> Some i

let hd v =
  match Array.length v with
    | 0 -> failwith "Array.hd"
    | _ -> v.(0)

let tl v =
  match Array.length v with
    | 0 -> failwith "Array.tl"
    | n -> Array.sub v 1 (pred n)

let last v =
  match Array.length v with
    | 0 -> failwith "Array.last"
    | n -> v.(pred n)

let cons e v = Array.append [|e|] v

let rev t =
  let n=Array.length t in
    if n <=0 then ()
    else
      let tmp=ref t.(0) in
      for i=0 to pred (n/2) do
        tmp:=t.((pred n)-i);
        t.((pred n)-i)<- t.(i);
        t.(i)<- !tmp
      done

let fold_right_i f v a =
  let rec fold a n =
    if n=0 then a
    else
      let k = n-1 in
      fold (f k v.(k) a) k in
  fold a (Array.length v)

let fold_left_i f v a =
  let n = Array.length a in
  let rec fold i v = if i = n then v else fold (succ i) (f i v a.(i)) in
  fold 0 v

let fold_right2 f v1 v2 a =
  let lv1 = Array.length v1 in
  let rec fold a n =
    if n=0 then a
    else
      let k = n-1 in
      fold (f v1.(k) v2.(k) a) k in
  if Array.length v2 <> lv1 then invalid_arg "Array.fold_right2";
  fold a lv1

let fold_left2 f a v1 v2 =
  let lv1 = Array.length v1 in
  let rec fold a n =
    if n >= lv1 then a else fold (f a v1.(n) v2.(n)) (succ n)
  in
  if Array.length v2 <> lv1 then invalid_arg "Array.fold_left2";
  fold a 0

let fold_left2_i f a v1 v2 =
  let lv1 = Array.length v1 in
  let rec fold a n =
    if n >= lv1 then a else fold (f n a v1.(n) v2.(n)) (succ n)
  in
  if Array.length v2 <> lv1 then invalid_arg "Array.fold_left2";
  fold a 0

let fold_left3 f a v1 v2 v3 =
  let lv1 = Array.length v1 in
  let rec fold a n =
    if n >= lv1 then a else fold (f a v1.(n) v2.(n) v3.(n)) (succ n)
  in
  if Array.length v2 <> lv1 || Array.length v3 <> lv1 then
    invalid_arg "Array.fold_left2";
  fold a 0

let fold_left_from n f a v =
  let rec fold a n =
    if n >= Array.length v then a else fold (f a v.(n)) (succ n)
  in
  fold a n

let map_to_list f v =
  List.map f (Array.to_list v)

let chop n v =
  let vlen = Array.length v in
  if n > vlen then failwith "Array.chop";
  (Array.sub v 0 n, Array.sub v n (vlen-n))

exception Local of int

(* If none of the elements is changed by f we return ar itself.
   The for loop looks for the first such an element.
   If found it is temporarily stored in a ref and the new array is produced,
   but f is not re-applied to elements that are already checked *)
let smartmap f ar =
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

let map2 f v1 v2 =
  if not (Int.equal (Array.length v1) (Array.length v2)) then
    invalid_arg "Array.map2";
  if Int.equal (Array.length v1) 0 then
    [| |]
  else begin
    let res = Array.create (Array.length v1) (f v1.(0) v2.(0)) in
    for i = 1 to pred (Array.length v1) do
      res.(i) <- f v1.(i) v2.(i)
    done;
    res
  end

let map2_i f v1 v2 =
  if not (Int.equal (Array.length v1) (Array.length v2)) then
    invalid_arg "Array.map2";
  if Int.equal (Array.length v1) 0 then
    [| |]
  else begin
    let res = Array.create (Array.length v1) (f 0 v1.(0) v2.(0)) in
    for i = 1 to pred (Array.length v1) do
      res.(i) <- f i v1.(i) v2.(i)
    done;
    res
  end

let map3 f v1 v2 v3 =
  if Array.length v1 <> Array.length v2 ||
     Array.length v1 <> Array.length v3 then invalid_arg "Array.map3";
  if Int.equal (Array.length v1) 0 then
    [| |]
  else begin
    let res = Array.create (Array.length v1) (f v1.(0) v2.(0) v3.(0)) in
    for i = 1 to pred (Array.length v1) do
      res.(i) <- f v1.(i) v2.(i) v3.(i)
    done;
    res
  end

let map_left f a = (* Ocaml does not guarantee Array.map is LR *)
  let l = Array.length a in (* (even if so), then we rewrite it *)
  if Int.equal l 0 then [||] else begin
    let r = Array.create l (f a.(0)) in
    for i = 1 to l - 1 do
      r.(i) <- f a.(i)
    done;
    r
  end

let iter2 f v1 v2 =
  let n = Array.length v1 in
  if not (Int.equal (Array.length v2) n) then invalid_arg "Array.iter2"
  else for i = 0 to n - 1 do f v1.(i) v2.(i) done

let pure_functional = false

let fold_map' f v e =
if pure_functional then
  let (l,e) =
    Array.fold_right
      (fun x (l,e) -> let (y,e) = f x e in (y::l,e))
      v ([],e) in
  (Array.of_list l,e)
else
  let e' = ref e in
  let v' = Array.map (fun x -> let (y,e) = f x !e' in e' := e; y) v in
  (v',!e')

let fold_map f e v =
  let e' = ref e in
  let v' = Array.map (fun x -> let (e,y) = f !e' x in e' := e; y) v in
  (!e',v')

let fold_map2' f v1 v2 e =
  let e' = ref e in
  let v' =
    map2 (fun x1 x2 -> let (y,e) = f x1 x2 !e' in e' := e; y) v1 v2
  in
  (v',!e')


let distinct v =
  let visited = Hashtbl.create 23 in
  try
    Array.iter
      (fun x ->
        if Hashtbl.mem visited x then raise Exit
        else Hashtbl.add visited x x)
      v;
    true
  with Exit -> false

let rev_to_list a =
  let rec tolist i res =
    if i >= Array.length a then res else tolist (i+1) (a.(i) :: res) in
  tolist 0 []

let filter_with filter v =
  Array.of_list (CList.filter_with filter (Array.to_list v))

