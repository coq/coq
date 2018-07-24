(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type S = module type of Array

module type ExtS =
sig
  include S
  val compare : ('a -> 'a -> int) -> 'a array -> 'a array -> int
  val equal : ('a -> 'a -> bool) -> 'a array -> 'a array -> bool
  val equal_norefl : ('a -> 'a -> bool) -> 'a array -> 'a array -> bool
  val is_empty : 'a array -> bool
  val exists : ('a -> bool) -> 'a array -> bool
  val exists2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool
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
  val fold_left4 :
    ('a -> 'b -> 'c -> 'd -> 'e -> 'a) -> 'a -> 'b array -> 'c array -> 'd array -> 'e array -> 'a
  val fold_left2_i :
    (int -> 'a -> 'b -> 'c -> 'a) -> 'a -> 'b array -> 'c array -> 'a
  val fold_left_from : int -> ('a -> 'b -> 'a) -> 'a -> 'b array -> 'a
  val map_to_list : ('a -> 'b) -> 'a array -> 'b list
  val map_of_list : ('a -> 'b) -> 'a list -> 'b array
  val chop : int -> 'a array -> 'a array * 'a array
  val smartmap : ('a -> 'a) -> 'a array -> 'a array
  [@@ocaml.deprecated "Same as [Smart.map]"]
  val smartfoldmap : ('r -> 'a -> 'r * 'a) -> 'r -> 'a array -> 'r * 'a array
  [@@ocaml.deprecated "Same as [Smart.fold_left_map]"]
  val map2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
  val map2_i : (int -> 'a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
  val map3 :
    ('a -> 'b -> 'c -> 'd) -> 'a array -> 'b array -> 'c array -> 'd array
  val map_left : ('a -> 'b) -> 'a array -> 'b array
  val iter2 : ('a -> 'b -> unit) -> 'a array -> 'b array -> unit
  val iter2_i : (int -> 'a -> 'b -> unit) -> 'a array -> 'b array -> unit
  val fold_left_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b array -> 'a * 'c array
  val fold_right_map : ('a -> 'c -> 'b * 'c) -> 'a array -> 'c -> 'b array * 'c
  val fold_left2_map : ('a -> 'b -> 'c -> 'a * 'd) -> 'a -> 'b array -> 'c array -> 'a * 'd array
  val fold_right2_map : ('a -> 'b -> 'c -> 'd * 'c) -> 'a array -> 'b array -> 'c -> 'd array * 'c
  val fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b array -> 'a * 'c array
  [@@ocaml.deprecated "Same as [fold_left_map]"]
  val fold_map' : ('a -> 'c -> 'b * 'c) -> 'a array -> 'c -> 'b array * 'c
  [@@ocaml.deprecated "Same as [fold_right_map]"]
  val fold_map2' :
    ('a -> 'b -> 'c -> 'd * 'c) -> 'a array -> 'b array -> 'c -> 'd array * 'c
  [@@ocaml.deprecated "Same as [fold_right2_map]"]
  val distinct : 'a array -> bool
  val rev_of_list : 'a list -> 'a array
  val rev_to_list : 'a array -> 'a list
  val filter_with : bool list -> 'a array -> 'a array
  module Smart :
  sig
    val map : ('a -> 'a) -> 'a array -> 'a array
    val map2 : ('a -> 'b -> 'b) -> 'a array -> 'b array -> 'b array
    val fold_left_map : ('a -> 'b -> 'a * 'b) -> 'a -> 'b array -> 'a * 'b array
    val fold_left2_map : ('a -> 'b -> 'c -> 'a * 'c) -> 'a -> 'b array -> 'c array -> 'a * 'c array
  end
  module Fun1 :
  sig
    val map : ('r -> 'a -> 'b) -> 'r -> 'a array -> 'b array
    val smartmap : ('r -> 'a -> 'a) -> 'r -> 'a array -> 'a array
    [@@ocaml.deprecated "Same as [Fun1.Smart.map]"]
    val iter : ('r -> 'a -> unit) -> 'r -> 'a array -> unit
    val iter2 : ('r -> 'a -> 'b -> unit) -> 'r -> 'a array -> 'b array -> unit
    module Smart :
    sig
      val map : ('r -> 'a -> 'a) -> 'r -> 'a array -> 'a array
    end
  end
end

include Array

let uget = Array.unsafe_get

(* Arrays *)

let compare cmp v1 v2 =
  if v1 == v2 then 0
  else
    let len = Array.length v1 in
    let c = Int.compare len (Array.length v2) in
    if c <> 0 then c else
      let rec loop i =
        if i < 0 then 0
        else
          let x = uget v1 i in
          let y = uget v2 i in
          let c = cmp x y in
          if c <> 0 then c
          else loop (i - 1)
      in
      loop (len - 1)

let equal_norefl cmp t1 t2 =
  let len = Array.length t1 in
  if not (Int.equal len (Array.length t2)) then false
  else
    let rec aux i =
      if i < 0 then true
      else
        let x = uget t1 i in
        let y = uget t2 i in
        cmp x y && aux (pred i)
    in
    aux (len - 1)

let equal cmp t1 t2 =
  if t1 == t2 then true else equal_norefl cmp t1 t2
    

let is_empty array = Int.equal (Array.length array) 0

let exists f v =
  let rec exrec = function
    | -1 -> false
    | n -> f (uget v n) || (exrec (n-1))
  in
  exrec ((Array.length v)-1)

let exists2 f v1 v2 =
  let rec exrec = function
    | -1 -> false
    | n -> f (uget v1 n) (uget v2 n) || (exrec (n-1))
  in
  let lv1 = Array.length v1 in
  lv1 = Array.length v2 && exrec (lv1-1)

let for_all f v =
  let rec allrec = function
    | -1 -> true
    | n ->
      let ans = f (uget v n) in
      ans && (allrec (n-1))
  in
  allrec ((Array.length v)-1)

let for_all2 f v1 v2 =
  let rec allrec = function
    | -1 -> true
    | n ->
      let ans = f (uget v1 n) (uget v2 n) in
      ans && (allrec (n-1))
  in
  let lv1 = Array.length v1 in
  lv1 = Array.length v2 && allrec (pred lv1)

let for_all3 f v1 v2 v3 =
  let rec allrec = function
    | -1 -> true
    | n ->
      let ans = f (uget v1 n)
        (uget v2 n) (uget v3 n)
      in
      ans && (allrec (n-1))
  in
  let lv1 = Array.length v1 in
  lv1 = Array.length v2 && lv1 = Array.length v3 && allrec (pred lv1)

let for_all4 f v1 v2 v3 v4 =
  let rec allrec = function
    | -1 -> true
    | n ->
      let ans = f (uget v1 n)
        (uget v2 n) (uget v3 n) (uget v4 n)
      in
      ans && (allrec (n-1))
  in
  let lv1 = Array.length v1 in
  lv1 = Array.length v2 &&
  lv1 = Array.length v3 &&
  lv1 = Array.length v4 &&
  allrec (pred lv1)

let for_all_i f i v =
  let len = Array.length v in
  let rec allrec i n =
    n = len || f i (uget v n) && allrec (i+1) (n+1) in
  allrec i 0

exception Found of int

let findi (pred: int -> 'a -> bool) (arr: 'a array) : int option =
  try
    for i=0 to Array.length arr - 1 do
      if pred i (uget arr i) then raise (Found i) done;
    None
  with Found i -> Some i

let hd v =
  match Array.length v with
    | 0 -> failwith "Array.hd"
    | _ -> uget v 0

let tl v =
  match Array.length v with
    | 0 -> failwith "Array.tl"
    | n -> Array.sub v 1 (pred n)

let last v =
  match Array.length v with
    | 0 -> failwith "Array.last"
    | n -> uget v (pred n)

let cons e v =
  let len = Array.length v in
  let ans = Array.make (Array.length v + 1) e in
  let () = Array.blit v 0 ans 1 len in
  ans

let rev t =
  let n=Array.length t in
    if n <=0 then ()
    else
      for i = 0 to pred (n/2) do
        let tmp = uget t ((pred n)-i) in
        Array.unsafe_set t ((pred n)-i) (uget t i);
        Array.unsafe_set t i tmp
      done

let fold_right_i f v a =
  let rec fold a n =
    if n=0 then a
    else
      let k = n-1 in
      fold (f k (uget v k) a) k in
  fold a (Array.length v)

let fold_left_i f v a =
  let n = Array.length a in
  let rec fold i v = if i = n then v else fold (succ i) (f i v (uget a i)) in
  fold 0 v

let fold_right2 f v1 v2 a =
  let lv1 = Array.length v1 in
  let rec fold a n =
    if n=0 then a
    else
      let k = n-1 in
      fold (f (uget v1 k) (uget v2 k) a) k in
  if Array.length v2 <> lv1 then invalid_arg "Array.fold_right2";
  fold a lv1

let fold_left2 f a v1 v2 =
  let lv1 = Array.length v1 in
  let rec fold a n =
    if n >= lv1 then a else fold (f a (uget v1 n) (uget v2 n)) (succ n)
  in
  if Array.length v2 <> lv1 then invalid_arg "Array.fold_left2";
  fold a 0

let fold_left2_i f a v1 v2 =
  let lv1 = Array.length v1 in
  let rec fold a n =
    if n >= lv1 then a else fold (f n a (uget v1 n) (uget v2 n)) (succ n)
  in
  if Array.length v2 <> lv1 then invalid_arg "Array.fold_left2_i";
  fold a 0

let fold_left3 f a v1 v2 v3 =
  let lv1 = Array.length v1 in
  let rec fold a n =
    if n >= lv1 then a
    else fold (f a (uget v1 n) (uget v2 n) (uget v3 n)) (succ n)
  in
  if Array.length v2 <> lv1 || Array.length v3 <> lv1 then
    invalid_arg "Array.fold_left3";
  fold a 0

let fold_left4 f a v1 v2 v3 v4 =
  let lv1 = Array.length v1 in
  let rec fold a n =
    if n >= lv1 then a
    else fold (f a (uget v1 n) (uget v2 n) (uget v3 n) (uget v4 n)) (succ n)
  in
  if Array.length v2 <> lv1 || Array.length v3 <> lv1 || Array.length v4 <> lv1 then
    invalid_arg "Array.fold_left4";
  fold a 0

let fold_left_from n f a v =
  let len = Array.length v in
  let () = if n < 0 then invalid_arg "Array.fold_left_from" in
  let rec fold a n =
    if n >= len then a else fold (f a (uget v n)) (succ n)
  in
  fold a n

let rev_of_list = function
| [] -> [| |]
| x :: l ->
  let len = List.length l in
  let ans = Array.make (succ len) x in
  let rec set i = function
  | [] -> ()
  | x :: l ->
    Array.unsafe_set ans i x;
    set (pred i) l
  in
  let () = set (len - 1) l in
  ans

let map_to_list = CList.map_of_array

let map_of_list f l =
  let len = List.length l in
  let rec fill i v = function
  | [] -> ()
  | x :: l ->
    Array.unsafe_set v i (f x);
    fill (succ i) v l
  in
  match l with
  | [] -> [||]
  | x :: l ->
    let ans = Array.make len (f x) in
    let () = fill 1 ans l in
    ans

let chop n v =
  let vlen = Array.length v in
  if n > vlen then failwith "Array.chop";
  (Array.sub v 0 n, Array.sub v n (vlen-n))

let map2 f v1 v2 =
  let len1 = Array.length v1 in
  let len2 = Array.length v2 in
  let () = if not (Int.equal len1 len2) then invalid_arg "Array.map2" in
  if Int.equal len1 0 then
    [| |]
  else begin
    let res = Array.make len1 (f (uget v1 0) (uget v2 0)) in
    for i = 1 to pred len1 do
      Array.unsafe_set res i (f (uget v1 i) (uget v2 i))
    done;
    res
  end

let map2_i f v1 v2 =
  let len1 = Array.length v1 in
  let len2 = Array.length v2 in
  let () = if not (Int.equal len1 len2) then invalid_arg "Array.map2" in
  if Int.equal len1 0 then
    [| |]
  else begin
    let res = Array.make len1 (f 0 (uget v1 0) (uget v2 0)) in
    for i = 1 to pred len1 do
      Array.unsafe_set res i (f i (uget v1 i) (uget v2 i))
    done;
    res
  end

let map3 f v1 v2 v3 =
  let len1 = Array.length v1 in
  let () =
    if len1 <> Array.length v2 || len1 <> Array.length v3
    then invalid_arg "Array.map3"
  in
  if Int.equal len1 0 then
    [| |]
  else begin
    let res = Array.make len1 (f (uget v1 0) (uget v2 0) (uget v3 0)) in
    for i = 1 to pred len1 do
      Array.unsafe_set res i (f (uget v1 i) (uget v2 i) (uget v3 i))
    done;
    res
  end

let map_left f a = (* Ocaml does not guarantee Array.map is LR *)
  let l = Array.length a in (* (even if so), then we rewrite it *)
  if Int.equal l 0 then [||] else begin
    let r = Array.make l (f (uget a 0)) in
    for i = 1 to l - 1 do
      Array.unsafe_set r i (f (uget a i))
    done;
    r
  end

let iter2 f v1 v2 =
  let len1 = Array.length v1 in
  let len2 = Array.length v2 in
  let () = if not (Int.equal len2 len1) then invalid_arg "Array.iter2" in
  for i = 0 to len1 - 1 do f (uget v1 i) (uget v2 i) done

let iter2_i f v1 v2 =
  let len1 = Array.length v1 in
  let len2 = Array.length v2 in
  let () = if not (Int.equal len2 len1) then invalid_arg "Array.iter2" in
  for i = 0 to len1 - 1 do f i (uget v1 i) (uget v2 i) done

let pure_functional = false

let fold_right_map f v e =
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

let fold_map' = fold_right_map

let fold_left_map f e v =
  let e' = ref e in
  let v' = Array.map (fun x -> let (e,y) = f !e' x in e' := e; y) v in
  (!e',v')

let fold_map = fold_left_map

let fold_right2_map f v1 v2 e =
  let e' = ref e in
  let v' =
    map2 (fun x1 x2 -> let (y,e) = f x1 x2 !e' in e' := e; y) v1 v2
  in
  (v',!e')

let fold_map2' = fold_right2_map

let fold_left2_map f e v1 v2 =
  let e' = ref e in
  let v' = map2 (fun x1 x2 -> let (e,y) = f !e' x1 x2 in e' := e; y) v1 v2 in
  (!e',v')

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
    if i >= Array.length a then res else tolist (i+1) (uget a i :: res) in
  tolist 0 []

let filter_with filter v =
  Array.of_list (CList.filter_with filter (Array.to_list v))

module Smart =
struct

  (* If none of the elements is changed by f we return ar itself.
     The while loop looks for the first such an element.
     If found, we break here and the new array is produced,
     but f is not re-applied to elements that are already checked *)
  let map f (ar : 'a array) =
    let len = Array.length ar in
    let i = ref 0 in
    let break = ref true in
    let temp = ref None in
    while !break && (!i < len) do
      let v = Array.unsafe_get ar !i in
      let v' = f v in
      if v == v' then incr i
      else begin
        break := false;
        temp := Some v';
      end
    done;
    if !i < len then begin
      (** The array is not the same as the original one *)
      let ans : 'a array = Array.copy ar in
      let v = match !temp with None -> assert false | Some x -> x in
      Array.unsafe_set ans !i v;
      incr i;
      while !i < len do
        let v = Array.unsafe_get ans !i in
        let v' = f v in
        if v != v' then Array.unsafe_set ans !i v';
        incr i
      done;
      ans
    end else ar

  let map2 f aux_ar ar =
    let len = Array.length ar in
    let aux_len = Array.length aux_ar in
    let () = if not (Int.equal len aux_len) then invalid_arg "Array.Smart.map2" in
    let i = ref 0 in
    let break = ref true in
    let temp = ref None in
    while !break && (!i < len) do
      let v = Array.unsafe_get ar !i in
      let w = Array.unsafe_get aux_ar !i in
      let v' = f w v in
      if v == v' then incr i
      else begin
        break := false;
        temp := Some v';
      end
    done;
    if !i < len then begin
      (** The array is not the same as the original one *)
      let ans : 'a array = Array.copy ar in
      let v = match !temp with None -> assert false | Some x -> x in
      Array.unsafe_set ans !i v;
      incr i;
      while !i < len do
        let v = Array.unsafe_get ans !i in
        let w = Array.unsafe_get aux_ar !i in
        let v' = f w v in
        if v != v' then Array.unsafe_set ans !i v';
        incr i
      done;
      ans
    end else ar

  (** Same as [Smart.map] but threads a state meanwhile *)
  let fold_left_map f accu (ar : 'a array) =
    let len = Array.length ar in
    let i = ref 0 in
    let break = ref true in
    let r = ref accu in
    (** This variable is never accessed unset *)
    let temp = ref None in
    while !break && (!i < len) do
      let v = Array.unsafe_get ar !i in
      let (accu, v') = f !r v in
      r := accu;
      if v == v' then incr i
      else begin
        break := false;
        temp := Some v';
      end
    done;
    if !i < len then begin
      let ans : 'a array = Array.copy ar in
      let v = match !temp with None -> assert false | Some x -> x in
      Array.unsafe_set ans !i v;
      incr i;
      while !i < len do
        let v = Array.unsafe_get ar !i in
        let (accu, v') = f !r v in
        r := accu;
        if v != v' then Array.unsafe_set ans !i v';
        incr i
      done;
      !r, ans
    end else !r, ar

  (** Same as [Smart.map2] but threads a state meanwhile *)
  let fold_left2_map f accu aux_ar ar =
    let len = Array.length ar in
    let aux_len = Array.length aux_ar in
    let () = if not (Int.equal len aux_len) then invalid_arg "Array.Smart.fold_left2_map" in
    let i = ref 0 in
    let break = ref true in
    let r = ref accu in
    (** This variable is never accessed unset *)
    let temp = ref None in
    while !break && (!i < len) do
      let v = Array.unsafe_get ar !i in
      let w = Array.unsafe_get aux_ar !i in
      let (accu, v') = f !r w v in
      r := accu;
      if v == v' then incr i
      else begin
        break := false;
        temp := Some v';
      end
    done;
    if !i < len then begin
      let ans : 'a array = Array.copy ar in
      let v = match !temp with None -> assert false | Some x -> x in
      Array.unsafe_set ans !i v;
      incr i;
      while !i < len do
        let v = Array.unsafe_get ar !i in
        let w = Array.unsafe_get aux_ar !i in
        let (accu, v') = f !r w v in
        r := accu;
        if v != v' then Array.unsafe_set ans !i v';
        incr i
      done;
      !r, ans
    end else !r, ar

end

(* Deprecated aliases *)
let smartmap = Smart.map
let smartfoldmap = Smart.fold_left_map

module Fun1 =
struct

  let map f arg v = match v with
  | [| |] -> [| |]
  | _ ->
    let len = Array.length v in
    let x0 = Array.unsafe_get v 0 in
    let ans = Array.make len (f arg x0) in
    for i = 1 to pred len do
      let x = Array.unsafe_get v i in
      Array.unsafe_set ans i (f arg x)
    done;
    ans

  let iter f arg v =
    let len = Array.length v in
    for i = 0 to pred len do
      let x = uget v i in
      f arg x
    done

  let iter2 f arg v1 v2 =
    let len1 = Array.length v1 in
    let len2 = Array.length v2 in
    let () = if not (Int.equal len2 len1) then invalid_arg "Array.Fun1.iter2" in
    for i = 0 to pred len1 do
      let x1 = uget v1 i in
      let x2 = uget v2 i in
      f arg x1 x2
    done

  module Smart =
  struct

    let map f arg (ar : 'a array) =
      let len = Array.length ar in
      let i = ref 0 in
      let break = ref true in
      let temp = ref None in
      while !break && (!i < len) do
        let v = Array.unsafe_get ar !i in
        let v' = f arg v in
        if v == v' then incr i
        else begin
          break := false;
          temp := Some v';
        end
      done;
      if !i < len then begin
        (** The array is not the same as the original one *)
        let ans : 'a array = Array.copy ar in
        let v = match !temp with None -> assert false | Some x -> x in
        Array.unsafe_set ans !i v;
        incr i;
        while !i < len do
          let v = Array.unsafe_get ans !i in
          let v' = f arg v in
          if v != v' then Array.unsafe_set ans !i v';
          incr i
        done;
        ans
      end else ar

  end

  let smartmap = Smart.map

end
