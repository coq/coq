
type 'a frozen = 
   Freeze of (unit -> 'a)
 | Val of 'a;;

type 'a llist =
   Nil
 | Cons of 'a cell

and 'a cell = 
    {         head : 'a;
      mutable tail : 'a llist frozen
    }
;;


let hdl = function
    Nil -> failwith "hdl"
  | Cons {head = x; tail = _ } -> x
;;

let rec mapl f = function
  Nil -> Nil
| Cons {head = x; tail = Val l} -> 
      Cons {head = f x; tail = Freeze (function () -> mapl f l)}
| Cons ({head = x; tail = Freeze th} as cell) ->
      let thunk () =
      let tail = th () in 
      cell.tail <- Val tail;
      mapl f tail in
      Cons {head = f x; tail = Freeze thunk}
;;

(*
let rec map f = function
  Nil -> Nil
| Cons {head = x; tail = Val l} -> 
      Cons {head = f x; tail = Freeze (function () -> map f l)}
| Cons ({head = x; tail = Freeze th} as cell) ->
      let thunk () =
      let tail = th () in 
      let _ = cell.tail <- Val tail in
	map f tail in
	Cons {head = f x; tail = Freeze thunk}
*)

let rec map f = function
    [] -> Nil
  | x::[] ->
      begin
	try 
	  let fx = f x in
	    Cons {head = fx; tail = Val Nil}
	with _ -> Nil
      end
  | x::l ->
      try 
	let fx = f x in
	  Cons {head = fx; tail = Freeze (function () -> map f l)}
      with _ -> map f l

let rec map2_without_repetition f = function
    [] -> Nil
  | x::[] ->
      begin
	try 
	  let fx1,fx2 = f x in 
	    Cons {head = fx1; 
		  tail = Val (Cons {head = fx2; tail = Val Nil})}
	with _ -> Nil
      end
  | x::(y::_ as l) ->
      if x = y
      then map2_without_repetition f l
      else
	try 
	  let fx1,fx2 = f x in 
	    Cons {head = fx1; 
		  tail = Val (Cons {head = fx2; 
				    tail = Freeze (function () -> 
						     map2_without_repetition f l)})}
	with _ -> map2_without_repetition f l

let rec lazy_append x y = match x,y with
    Nil, (Val l) -> l
  | Nil, (Freeze th) -> th ()
  | (Cons {head = x; tail = Val l}),  ll ->
      Cons {head = x; tail = Freeze (function () -> lazy_append l ll)}
  | (Cons ({head = x; tail = Freeze th} as cell)), ll -> 
      let thunk () =
	let tail = th () in 
	  cell.tail <- Val tail;
	  lazy_append tail ll in
	Cons {head = x; tail = Freeze thunk}


