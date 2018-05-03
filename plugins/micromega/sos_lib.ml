(* ========================================================================= *)
(* - This code originates from John Harrison's HOL LIGHT 2.30                *)
(*   (see file LICENSE.sos for license, copyright and disclaimer)            *)
(*   This code is the HOL LIGHT library code used by sos.ml                  *)
(* - Laurent Théry (thery@sophia.inria.fr) has isolated the HOL              *)
(*   independent bits                                                        *)
(* - Frédéric Besson (fbesson@irisa.fr) is using it to feed  micromega       *)
(* ========================================================================= *)

open Num

(* ------------------------------------------------------------------------- *)
(* Comparisons that are reflexive on NaN and also short-circuiting.          *)
(* ------------------------------------------------------------------------- *)

let cmp = Pervasives.compare (** FIXME *)

let (=?) = fun x y -> cmp x y = 0;;
let (<?) = fun x y -> cmp x y < 0;;
let (<=?) = fun x y -> cmp x y <= 0;;
let (>?) = fun x y -> cmp x y > 0;;

(* ------------------------------------------------------------------------- *)
(* Combinators.                                                              *)
(* ------------------------------------------------------------------------- *)

let (o) = fun f g x -> f(g x);;

(* ------------------------------------------------------------------------- *)
(* Some useful functions on "num" type.                                      *)
(* ------------------------------------------------------------------------- *)


let num_0 = Int 0
and num_1 = Int 1
and num_2 = Int 2
and num_10 = Int 10;;

let pow2 n = power_num num_2 (Int n);;
let pow10 n = power_num num_10 (Int n);;

let numdom r =
  let r' = Ratio.normalize_ratio (ratio_of_num r) in
  num_of_big_int(Ratio.numerator_ratio r'),
  num_of_big_int(Ratio.denominator_ratio r');;

let numerator = (o) fst numdom
and denominator = (o) snd numdom;;

let gcd_num n1 n2 =
  num_of_big_int(Big_int.gcd_big_int (big_int_of_num n1) (big_int_of_num n2));;

let lcm_num x y =
  if x =/ num_0 && y =/ num_0 then num_0
  else abs_num((x */ y) // gcd_num x y);;


(* ------------------------------------------------------------------------- *)
(* Various versions of list iteration.                                       *)
(* ------------------------------------------------------------------------- *)

let rec end_itlist f l =
  match l with
        []     -> failwith "end_itlist"
      | [x]    -> x
      | (h::t) -> f h (end_itlist f t);;

(* ------------------------------------------------------------------------- *)
(* All pairs arising from applying a function over two lists.                *)
(* ------------------------------------------------------------------------- *)

let rec allpairs f l1 l2 =
  match l1 with
   h1::t1 -> List.fold_right (fun x a -> f h1 x :: a) l2 (allpairs f t1 l2)
  | [] -> [];;

(* ------------------------------------------------------------------------- *)
(* String operations (surely there is a better way...)                       *)
(* ------------------------------------------------------------------------- *)

let implode l = List.fold_right (^) l "";;

let explode s =
  let rec exap n l =
      if n < 0 then l else
      exap (n - 1) ((String.sub s n 1)::l) in
  exap (String.length s - 1) [];;


(* ------------------------------------------------------------------------- *)
(* Repetition of a function.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec funpow n f x =
  if n < 1 then x else funpow (n-1) f (f x);;



(* ------------------------------------------------------------------------- *)
(* Sequences.                                                *)
(* ------------------------------------------------------------------------- *)

let rec (--) = fun m n -> if m > n then [] else m::((m + 1) -- n);;

(* ------------------------------------------------------------------------- *)
(* Various useful list operations.                                           *)
(* ------------------------------------------------------------------------- *)

let rec tryfind f l =
  match l with
      [] -> failwith "tryfind"
    | (h::t) -> try f h with Failure _ -> tryfind f t;;

(* ------------------------------------------------------------------------- *)
(* "Set" operations on lists.                                                *)
(* ------------------------------------------------------------------------- *)

let rec mem x lis =
  match lis with
    [] -> false
  | (h::t) -> x =? h || mem x t;;

let insert x l =
  if mem x l then l else x::l;;

let union l1 l2 = List.fold_right insert l1 l2;;

let subtract l1 l2 = List.filter (fun x -> not (mem x l2)) l1;;

(* ------------------------------------------------------------------------- *)
(* Common measure predicates to use with "sort".                             *)
(* ------------------------------------------------------------------------- *)

let increasing f x y = f x <? f y;;

(* ------------------------------------------------------------------------- *)
(* Iterating functions over lists.                                           *)
(* ------------------------------------------------------------------------- *)

let rec do_list f l =
  match l with
    [] -> ()
  | (h::t) -> (f h; do_list f t);;

(* ------------------------------------------------------------------------- *)
(* Sorting.                                                                  *)
(* ------------------------------------------------------------------------- *)

let rec sort cmp lis =
  match lis with
    [] -> []
  | piv::rest ->
      let r,l = List.partition (cmp piv) rest in
      (sort cmp l) @ (piv::(sort cmp r));;

(* ------------------------------------------------------------------------- *)
(* Removing adjacent (NB!) equal elements from list.                         *)
(* ------------------------------------------------------------------------- *)

let rec uniq l =
  match l with
    x::(y::_ as t) -> let t' = uniq t in
                      if x =? y then t' else
                      if t'==t then l else x::t'
 | _ -> l;;

(* ------------------------------------------------------------------------- *)
(* Convert list into set by eliminating duplicates.                          *)
(* ------------------------------------------------------------------------- *)

let setify s = uniq (sort (<=?) s);;

(* ------------------------------------------------------------------------- *)
(* Polymorphic finite partial functions via Patricia trees.                  *)
(*                                                                           *)
(* The point of this strange representation is that it is canonical (equal   *)
(* functions have the same encoding) yet reasonably efficient on average.    *)
(*                                                                           *)
(* Idea due to Diego Olivier Fernandez Pons (OCaml list, 2003/11/10).        *)
(* ------------------------------------------------------------------------- *)

type ('a,'b)func =
   Empty
 | Leaf of int * ('a*'b)list
 | Branch of int * int * ('a,'b)func * ('a,'b)func;;

(* ------------------------------------------------------------------------- *)
(* Undefined function.                                                       *)
(* ------------------------------------------------------------------------- *)

let undefined = Empty;;

(* ------------------------------------------------------------------------- *)
(* In case of equality comparison worries, better use this.                  *)
(* ------------------------------------------------------------------------- *)

let is_undefined f =
  match f with
    Empty -> true
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Operation analagous to "map" for lists.                                   *)
(* ------------------------------------------------------------------------- *)

let mapf =
  let rec map_list f l =
    match l with
      [] -> []
    | (x,y)::t -> (x,f(y))::(map_list f t) in
  let rec mapf f t =
    match t with
      Empty -> Empty
    | Leaf(h,l) -> Leaf(h,map_list f l)
    | Branch(p,b,l,r) -> Branch(p,b,mapf f l,mapf f r) in
  mapf;;

(* ------------------------------------------------------------------------- *)
(* Operations analogous to "fold" for lists.                                 *)
(* ------------------------------------------------------------------------- *)

let foldl =
  let rec foldl_list f a l =
    match l with
      [] -> a
    | (x,y)::t -> foldl_list f (f a x y) t in
  let rec foldl f a t =
    match t with
      Empty -> a
    | Leaf(h,l) -> foldl_list f a l
    | Branch(p,b,l,r) -> foldl f (foldl f a l) r in
  foldl;;

let foldr =
  let rec foldr_list f l a =
    match l with
      [] -> a
    | (x,y)::t -> f x y (foldr_list f t a) in
  let rec foldr f t a =
    match t with
      Empty -> a
    | Leaf(h,l) -> foldr_list f l a
    | Branch(p,b,l,r) -> foldr f l (foldr f r a) in
  foldr;;

(* ------------------------------------------------------------------------- *)
(* Redefinition and combination.                                             *)
(* ------------------------------------------------------------------------- *)

let (|->),combine =
  let ldb x y = let z = x lxor y in z land (-z) in
  let newbranch p1 t1 p2 t2 =
    let b = ldb p1 p2 in
    let p = p1 land (b - 1) in
    if p1 land b = 0 then Branch(p,b,t1,t2)
    else Branch(p,b,t2,t1) in
  let rec define_list (x,y as xy) l =
    match l with
      (a,b as ab)::t ->
          if x =? a then xy::t
          else if x <? a then xy::l
          else ab::(define_list xy t)
    | [] -> [xy]
  and combine_list op z l1 l2 =
    match (l1,l2) with
      [],_ -> l2
    | _,[] -> l1
    | ((x1,y1 as xy1)::t1,(x2,y2 as xy2)::t2) ->
          if x1 <? x2 then xy1::(combine_list op z t1 l2)
          else if x2 <? x1 then xy2::(combine_list op z l1 t2) else
          let y = op y1 y2 and l = combine_list op z t1 t2 in
          if z(y) then l else (x1,y)::l in
  let (|->) x y =
    let k = Hashtbl.hash x in
    let rec upd t =
      match t with
        Empty -> Leaf (k,[x,y])
      | Leaf(h,l) ->
           if h = k then Leaf(h,define_list (x,y) l)
           else newbranch h t k (Leaf(k,[x,y]))
      | Branch(p,b,l,r) ->
          if k land (b - 1) <> p then newbranch p t k (Leaf(k,[x,y]))
          else if k land b = 0 then Branch(p,b,upd l,r)
          else Branch(p,b,l,upd r) in
    upd in
  let rec combine op z t1 t2 =
    match (t1,t2) with
      Empty,_ -> t2
    | _,Empty -> t1
    | Leaf(h1,l1),Leaf(h2,l2) ->
          if h1 = h2 then
            let l = combine_list op z l1 l2 in
            if l = [] then Empty else Leaf(h1,l)
          else newbranch h1 t1 h2 t2
    | (Leaf(k,lis) as lf),(Branch(p,b,l,r) as br) |
      (Branch(p,b,l,r) as br),(Leaf(k,lis) as lf) ->
          if k land (b - 1) = p then
            if k land b = 0 then
              let l' = combine op z lf l in
              if is_undefined l' then r else Branch(p,b,l',r)
            else
              let r' = combine op z lf r in
              if is_undefined r' then l else Branch(p,b,l,r')
          else
            newbranch k lf p br
    | Branch(p1,b1,l1,r1),Branch(p2,b2,l2,r2) ->
          if b1 < b2 then
            if p2 land (b1 - 1) <> p1 then newbranch p1 t1 p2 t2
            else if p2 land b1 = 0 then
              let l = combine op z l1 t2 in
              if is_undefined l then r1 else Branch(p1,b1,l,r1)
            else
              let r = combine op z r1 t2 in
              if is_undefined r then l1 else Branch(p1,b1,l1,r)
          else if b2 < b1 then
            if p1 land (b2 - 1) <> p2 then newbranch p1 t1 p2 t2
            else if p1 land b2 = 0 then
              let l = combine op z t1 l2 in
              if is_undefined l then r2 else Branch(p2,b2,l,r2)
            else
              let r = combine op z t1 r2 in
              if is_undefined r then l2 else Branch(p2,b2,l2,r)
          else if p1 = p2 then
            let l = combine op z l1 l2 and r = combine op z r1 r2 in
            if is_undefined l then r
            else if is_undefined r then l else Branch(p1,b1,l,r)
          else
            newbranch p1 t1 p2 t2 in
  (|->),combine;;

(* ------------------------------------------------------------------------- *)
(* Special case of point function.                                           *)
(* ------------------------------------------------------------------------- *)

let (|=>) = fun x y -> (x |-> y) undefined;;


(* ------------------------------------------------------------------------- *)
(* Grab an arbitrary element.                                                *)
(* ------------------------------------------------------------------------- *)

let rec choose t =
  match t with
    Empty -> failwith "choose: completely undefined function"
  | Leaf(h,l) -> List.hd l
  | Branch(b,p,t1,t2) -> choose t1;;

(* ------------------------------------------------------------------------- *)
(* Application.                                                              *)
(* ------------------------------------------------------------------------- *)

let applyd =
  let rec apply_listd l d x =
    match l with
      (a,b)::t -> if x =? a then b
                  else if x >? a then apply_listd t d x else d x
    | [] -> d x in
  fun f d x ->
    let k = Hashtbl.hash x in
    let rec look t =
      match t with
        Leaf(h,l) when h = k -> apply_listd l d x
      | Branch(p,b,l,r) -> look (if k land b = 0 then l else r)
      | _ -> d x in
    look f;;

let apply f = applyd f (fun x -> failwith "apply");;

let tryapplyd f a d = applyd f (fun x -> d) a;;

(* ------------------------------------------------------------------------- *)
(* Undefinition.                                                             *)
(* ------------------------------------------------------------------------- *)

let undefine =
  let rec undefine_list x l =
    match l with
      (a,b as ab)::t ->
          if x =? a then t
          else if x <? a then l else
          let t' = undefine_list x t in
          if t' == t then l else ab::t'
    | [] -> [] in
  fun x ->
    let k = Hashtbl.hash x in
    let rec und t =
      match t with
        Leaf(h,l) when h = k ->
          let l' = undefine_list x l in
          if l' == l then t
          else if l' = [] then Empty
          else Leaf(h,l')
      | Branch(p,b,l,r) when k land (b - 1) = p ->
          if k land b = 0 then
            let l' = und l in
            if l' == l then t
            else if is_undefined l' then r
            else Branch(p,b,l',r)
          else
            let r' = und r in
            if r' == r then t
            else if is_undefined r' then l
            else Branch(p,b,l,r')
      | _ -> t in
    und;;


(* ------------------------------------------------------------------------- *)
(* Mapping to sorted-list representation of the graph, domain and range.     *)
(* ------------------------------------------------------------------------- *)

let graph f = setify (foldl (fun a x y -> (x,y)::a) [] f);;

let dom f = setify(foldl (fun a x y -> x::a) [] f);;

(* ------------------------------------------------------------------------- *)
(* More parser basics.                                                       *)
(* ------------------------------------------------------------------------- *)

exception Noparse;;


let isspace,isnum =
  let charcode s = Char.code(String.get s 0) in
  let spaces = " \t\n\r"
  and separators = ",;"
  and brackets = "()[]{}"
  and symbs = "\\!@#$%^&*-+|\\<=>/?~.:"
  and alphas = "'abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ"
  and nums = "0123456789" in
  let allchars = spaces^separators^brackets^symbs^alphas^nums in
  let csetsize = List.fold_right ((o) max charcode) (explode allchars) 256 in
  let ctable = Array.make csetsize 0 in
  do_list (fun c -> Array.set ctable (charcode c) 1) (explode spaces);
  do_list (fun c -> Array.set ctable (charcode c) 2) (explode separators);
  do_list (fun c -> Array.set ctable (charcode c) 4) (explode brackets);
  do_list (fun c -> Array.set ctable (charcode c) 8) (explode symbs);
  do_list (fun c -> Array.set ctable (charcode c) 16) (explode alphas);
  do_list (fun c -> Array.set ctable (charcode c) 32) (explode nums);
  let isspace c = Array.get ctable (charcode c) = 1
  and isnum c = Array.get ctable (charcode c) = 32 in
  isspace,isnum;;

let parser_or parser1 parser2 input =
  try parser1 input
  with Noparse -> parser2 input;;

let (++) parser1 parser2 input =
  let result1,rest1 = parser1 input in
  let result2,rest2 = parser2 rest1 in
  (result1,result2),rest2;;

let rec many prs input =
  try let result,next = prs input in
      let results,rest = many prs next in
      (result::results),rest
  with Noparse -> [],input;;

let (>>) prs treatment input =
  let result,rest = prs input in
  treatment(result),rest;;

let fix err prs input =
  try prs input
  with Noparse -> failwith (err ^ " expected");;

let listof prs sep err =
  prs ++ many (sep ++ fix err prs >> snd) >> (fun (h,t) -> h::t);;

let possibly prs input =
  try let x,rest = prs input in [x],rest
  with Noparse -> [],input;;

let some p =
  function
      [] -> raise Noparse
    | (h::t) -> if p h then (h,t) else raise Noparse;;

let a tok = some (fun item -> item = tok);;

let rec atleast n prs i =
  (if n <= 0 then many prs
   else prs ++ atleast (n - 1) prs >> (fun (h,t) -> h::t)) i;;

(* ------------------------------------------------------------------------- *)

let temp_path = Filename.get_temp_dir_name ();;

(* ------------------------------------------------------------------------- *)
(* Convenient conversion between files and (lists of) strings.               *)
(* ------------------------------------------------------------------------- *)

let strings_of_file filename =
  let fd = try Pervasives.open_in filename
           with Sys_error _ ->
             failwith("strings_of_file: can't open "^filename) in
  let rec suck_lines acc =
    try let l = Pervasives.input_line fd in
        suck_lines (l::acc)
    with End_of_file -> List.rev acc in
  let data = suck_lines [] in
  (Pervasives.close_in fd; data);;

let string_of_file filename =
  String.concat "\n" (strings_of_file filename);;

let file_of_string filename s =
  let fd = Pervasives.open_out filename in
  output_string fd s; close_out fd;;


(* ------------------------------------------------------------------------- *)
(* Iterative deepening.                                                      *)
(* ------------------------------------------------------------------------- *)

let rec deepen f n =
  try (*print_string "Searching with depth limit ";
      print_int n; print_newline();*) f n
  with Failure _ -> deepen f (n + 1);;

exception TooDeep

let deepen_until limit f n =
  match compare limit 0 with
    | 0 -> raise TooDeep
    | -1 -> deepen f n
    | _  ->
	let rec d_until  f n =
	  try(* if !debugging
	  then (print_string "Searching with depth limit ";
		print_int n; print_newline()) ;*) f n
	  with Failure x ->
	    (*if !debugging then (Printf.printf "solver error : %s\n" x) ; *)
	    if n = limit then raise TooDeep else  d_until f (n + 1) in
	  d_until f n
