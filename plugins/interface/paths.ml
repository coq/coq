let int_list_to_string s l =
    List.fold_left
       (fun s -> (fun v -> s ^ " " ^ (string_of_int v)))
       s
       l;;

(* Given two paths, this function returns the longest common prefix and the
   two suffixes. *)
let rec decompose_path
     : (int list * int list) -> (int list * int list * int list) =
   function
       (a::l,b::m) when a = b ->
         let (c,p1,p2) = decompose_path (l,m) in
         (a::c,p1,p2)
     |  p1,p2 -> [], p1, p2;;

let rec is_prefix p1 p2 = match p1,p2 with
  [], _ -> true
| a::tl1, b::tl2 when a = b -> is_prefix tl1 tl2
| _ -> false;;

let rec lex_smaller p1 p2 = match p1,p2 with
  [], _ -> true
| a::tl1, b::tl2 when a < b -> true
| a::tl1, b::tl2 when a = b -> lex_smaller tl1 tl2
| _ -> false;;
