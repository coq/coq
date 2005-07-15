let list_index x l =
  let rec aux i = function
      y :: tl -> if x = y then i else aux (succ i) tl
    | [] -> raise Not_found
  in aux 0 l

let list_assoc_index x l =
  let rec aux i = function
      (y, _) :: tl -> if x = y then i else aux (succ i) tl
    | [] -> raise Not_found
  in aux 0 l
