
(* $Id$ *)

type loc = int * int

type t =
  | Node of loc * string * t list
  | Nvar of loc * string
  | Slam of loc * string option * t
  | Num of loc * int
  | Id of loc * string
  | Str of loc * string
  | Path of loc * string list* string
  | Dynamic of loc * Dyn.t

type the_coq_ast = t

(* Hash-consing *)
module Hloc = Hashcons.Make(
  struct
    type t = loc
    type u = unit
    let equal (b1,e1) (b2,e2) = b1=b2 & e1=e2
    let hash_sub () x = x
    let hash = Hashtbl.hash
  end)

module Hast = Hashcons.Make(
  struct
    type t = the_coq_ast
    type u = (the_coq_ast -> the_coq_ast) * ((loc -> loc) * (string -> string))
    let hash_sub (hast,(hloc,hstr)) = function
      | Node(l,s,al) -> Node(hloc l, hstr s, List.map hast al)
      | Nvar(l,s) -> Nvar(hloc l, hstr s)
      | Slam(l,None,t) -> Slam(hloc l, None, hast t)
      | Slam(l,Some s,t) -> Slam(hloc l, Some (hstr s), hast t)
      | Num(l,n) -> Num(hloc l, n)
      | Id(l,s) -> Id(hloc l, hstr s)
      | Str(l,s) -> Str(hloc l, hstr s)
      | Path(l,d,k) -> Path(hloc l, List.map hstr d, hstr k)
      | Dynamic(l,d) -> Dynamic(hloc l, d)
    let equal a1 a2 =
      match (a1,a2) with
        | (Node(l1,s1,al1), Node(l2,s2,al2)) ->
            (l1==l2 & s1==s2 & List.length al1 = List.length al2)
            & List.for_all2 (==) al1 al2
        | (Nvar(l1,s1), Nvar(l2,s2)) -> l1==l2 & s1==s2
        | (Slam(l1,None,t1), Slam(l2,None,t2)) -> l1==l2 & t1==t2
        | (Slam(l1,Some s1,t1), Slam(l2,Some s2,t2)) -> l1==l2 & t1==t2
        | (Num(l1,n1), Num(l2,n2)) -> l1==l2 & n1=n2
        | (Id(l1,s1), Id(l2,s2)) -> l1==l2 & s1==s2
        | (Str(l1,s1),Str(l2,s2)) -> l1==l2 & s1==s2
        | (Path(l1,d1,k1), Path(l2,d2,k2)) ->
            (l1==l2 & k1==k2 & List.length d1 = List.length d2)
            & List.for_all2 (==) d1 d2
        | _ -> false
    let hash = Hashtbl.hash
  end)

let hcons_ast hstr =
  let hloc = Hashcons.simple_hcons Hloc.f () in
  let hast = Hashcons.recursive_hcons Hast.f (hloc,hstr) in
  (hast,hloc)


