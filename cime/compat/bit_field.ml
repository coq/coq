(***************************************************************************

  Bit fields encode vectors of bits of arbitrary length. 
  Boolean operations are provided : body.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

module type S =
sig 
  type t
  val all_zero : int ->  t
  val all_one  : int ->  t
  val bit_length : t -> int
  val bit_and : t -> t -> t
  val bit_or : t -> t -> t
  val bit_not : t -> t
  val bit_nth : int -> int -> t
  val bit_nth_first : int -> int -> t
  val is_zero : t -> bool;;
  val atmost_one_one : t -> bool;;
  val bit_field_to_vect_of_bits : int -> t -> int array
  val vect_of_bits_to_bit_field : int array -> t
  val print_bit_field : int -> t -> unit
end

(*
  For vectors of bits of length < 32
*)

module Small_bit_field =
  struct
    type t = int
    let all_zero _ = 0
    let all_one n = pred (1 lsl n)
    let bit_length _ = 1
    let bit_and = (land)
    let bit_or = (lor)
    let bit_not = lnot
    let bit_nth n _ = 1 lsl n
    let bit_nth_first n _ = pred (1 lsl (succ n))
    let is_zero n = (n = 0)
    let atmost_one_one n = (n land (pred n)) = 0
    let bit_field_to_vect_of_bits longueur n =
      let v = Array.create longueur 0 
      and n' = ref n in
	for i = 0 to (pred longueur) do
	  if (!n' land 1) = 1
	  then v.(i) <- 1;
	  n' := (!n' lsr 1)
	done;
	v
    let vect_of_bits_to_bit_field u =
      let l = Array.length u in
	if l >= 32
	then assert false
	else 
	  let n = ref 0 in
	    for j=0 to pred l do
	      if u.(j) > 0
	      then n:= !n + (1 lsl j)
	    done;
	    !n
    let print_bit_field l n =
      let v = bit_field_to_vect_of_bits l n in
	Printf.printf "[|";
	for i=0 to (l - 2) do
	  Printf.printf "%d ;" v.(i)
	done;
	Printf.printf "%d|]" v.(pred l)
  end

(*
  For vectors of bits of arbitrary length 
*)

module Large_bit_field =
  struct
    type t = int array


(*
  all_zero l fabrique un bit_field qui code le vecteur de bits compose de l 0.
*)

let all_zero l = 
  let q = if (l mod 31) = 0 then (l / 31) else succ (l / 31) in
    Array.create q 0

(*
  all_one l fabrique un bit_field qui code le vecteur de bits compose de l 1.
*)

let all_one l = 
  let q = l / 31
  and r = l mod 31 in
    if r = 0
    then Array.create q (lnot 0)
    else 
      let v = Array.create (succ q) (lnot 0) in
        v.(q) <- pred (1 lsl r);
        v

let bit_length bf = Array.length bf

(*
  bit_and est un "and" bit a bit, qui echoue sur des bit_fields qui codent 
  des vecteurs de bits de longueurs differentes.
*)
let bit_and bf1 bf2 = 
    try 
      let d = Array.length bf1 in
      let v = Array.create d 0 in
        for i=0 to (pred d) do
          v.(i) <- bf1.(i) land bf2.(i)
        done;
        v
    with Failure _ -> assert false

(*
  bit_and est un "or" bit a bit, qui echoue sur des bit_fields qui codent 
  des vecteurs de bits de longueurs differentes.
*)
let bit_or bf1 bf2 = 
    try 
      let d = Array.length bf1 in
      let v = Array.create d 0 in
        for i=0 to (pred d) do 
          v.(i) <- bf1.(i) lor bf2.(i)
        done;
        v
    with Failure _ -> assert false

(*
  bit_not est un not bit a bit.
*)
let bit_not bf = 
  let d = Array.length bf in 
  let v = Array.create d 0 in
    for i=0 to (pred d) do
      v.(i) <- lnot bf.(i)
    done;
    v

(*
  bit_nth n l fabrique un bit_field qui code un vecteur de 31*l bits avec
  uniquement des zeros, sauf a la position n (qui contient 1).
  NB : le premier bit  pour rang 0.
*)
let bit_nth n l =
  try 
    let qn = n / 31
    and rn = n mod 31 in
    let v = Array.create l 0 in
      v.(qn) <- 1 lsl rn;
      v
  with Failure _ -> assert false


(*
  bith_nth_first n l fabrique un bit_field qui code un vecteur de 31*l bits 
  avec des 1 aux n premieres positions, et des 0 ailleurs.
*)

let bit_nth_first n' l = 
  let n = succ n' in
  try 
    let qn = n / 31
    and rn = n mod 31 in
    let v = Array.create l 0 in
      if rn = 0
      then Array.blit (Array.create qn (lnot 0)) 0 v 0 qn
      else (Array.blit (Array.create (succ qn) (lnot 0)) 0 v 0 (succ qn); 
            v.(qn) <- pred (1 lsl rn));
      v
  with Failure _ -> assert false

(*
  is_zero bf teste si le bit_field bf code un vecteur de bits ne 
  contenant que des zeros.
*)

let is_zero bf = 
    try 
      for i=0 to (pred (Array.length bf)) do
        if (bf.(i) <> 0)
        then raise Exit
      done;
      true
    with Exit -> false;;

(*
  atmost_one_one bf teste si le bit_field bf code un vecteur de bits
  contenant uniquement des zeros, sauf eventuellement a une position qui
  contient un 1.
*)
let atmost_one_one bf = 
  try 
    let l = Array.length bf 
    and etat = ref 0 in
      for i=0 to (pred l) do
        let p = bf.(i) in
          if p <> 0
          then 
	    begin
              if (!etat <> 0)
              then raise Exit
              else 
		begin
                  if (p land (pred p)) = 0
                  then etat := 1
                  else raise Exit
                end
            end
      done;
      true
  with Exit -> false


(*
  int_to_vect_of_bits longueur n transforme l'entier n en un vecteur 
  de bits (0 ou 1) qui le code en base 2.
*)
let int_to_vect_of_bits longueur n =
  let v = Array.create longueur 0
  and n' = ref n in
    for i = 0 to (pred longueur) do
      if (!n' land 1) = 1 
      then v.(i) <- 1;
      n' := (!n' lsr 1)
    done;
  v
    

(*
  bit_field_to_vect_of_bits l bf transforme bf en le vecteur de l bits 
  qu'il code.
*)
let bit_field_to_vect_of_bits l bf =
  let v = Array.create l 0 
  and nb_digit = Array.length bf in
    match nb_digit with
        0 -> assert false
      | 1 -> int_to_vect_of_bits l bf.(0)
      | _ -> 
	  for i = 0 to (nb_digit - 2) do
            Array.blit (int_to_vect_of_bits 31 bf.(i)) 0
              v (i * 31) 31
          done;
          let r = l mod 31 in
            Array.blit (int_to_vect_of_bits r bf.(pred nb_digit)) 0
              v ((pred nb_digit) * 31) r;
            v

(*
  vect_of_bits_to_bit_field v transforme le vecteur de bits v en le
  bit_field qui le code.
*)

let vect_of_bits_to_bit_field u = 
  let l = Array.length u in
  let ql = l / 31
  and rl = l mod 31 in
    if rl = 0
    then 
      begin
	let v = Array.create ql 0 in
          for i=0 to (pred ql) do
            let d = 31 * i in
              for j=0 to 31 do
                if (u.(d+j) > 0)
                then v.(i) <- v.(i) + (1 lsl j)
              done
          done;
          v
      end
    else 
      begin
	let v = Array.create (succ ql) 0 in
          for i=0 to (pred ql) do
            let d = 31 * i in
              for j=0 to 31 do
                if (u.(d+j) > 0)
                then v.(i) <- v.(i) + (1 lsl j)
              done
          done;
          let d = 31 * ql in
            for j=0 to (pred rl) do
              if (u.(d+j) > 0)
              then v.(ql) <- v.(ql) + (1 lsl j)
            done;
            v
      end

(* 
  print_bit_field l bf imprime le vecteur de l bits code par bf.
*)
let print_bit_field l bf = 
  let v = bit_field_to_vect_of_bits l bf in
    Printf.printf "[|";
    for i=0 to (l - 2) do
      Printf.printf "%d ;" v.(i)
    done;
    Printf.printf "%d|]" v.(pred l);;
  

end

