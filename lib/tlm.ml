
(* $Id$ *)

(* 1er choix : une liste
module MySet = struct
  type 'a t = 'a list
  let mt = []
  let add = add_set
  let rmv = rmv_set
  let toList l = l
  let app = List.map
end
*)

(* 2 ème choix : un arbre *)
module MySet = struct
  type 'a t = 'a Coq_set.t
  let mt = Coq_set.empty
  let add = Coq_set.add
  let rmv = Coq_set.remove
  let toList = Coq_set.elements
  let app f l = Coq_set.fold (fun a b -> add (f a) b) l mt
end

module type MyMapType = sig
  type ('a, 'b) t
  val create : unit -> ('a,'b) t
  val map : ('a,'b) t -> 'a -> 'b
  val dom : ('a,'b) t -> 'a list
  val rng : ('a,'b) t -> 'b list
  val in_dom : ('a,'b) t -> 'a -> bool
  val add : ('a,'b) t -> 'a * 'b -> ('a,'b) t
  val remap : ('a,'b) t -> 'a -> 'b -> ('a,'b) t
  val app : (('a * 'c) -> unit) -> ('a,'c) t -> unit
  val toList : ('a,'b) t -> ('a * 'b) list
end;;

module MyMap = (Listmap : MyMapType);;

type ('a,'b) t =
    NODE of 'b MySet.t * ('a, ('a,'b) t) MyMap.t;;

let create () = NODE(MySet.mt,MyMap.create());;

let map (NODE (_,m)) lbl = MyMap.map m lbl;;
let xtract (NODE (hereset,_)) = MySet.toList hereset;;
let dom (NODE (_,m)) = MyMap.dom m;;
let in_dom (NODE (_,m)) lbl = MyMap.in_dom m lbl;;

let is_empty_node (NODE(a,b)) = (MySet.toList a = []) & (MyMap.toList b = []);;

let assure_arc m lbl =
    if MyMap.in_dom m lbl then m
    else MyMap.add m (lbl,NODE (MySet.mt,MyMap.create()))
;;

let cleanse_arcs (NODE (hereset,m)) =
let l = MyMap.rng m
in NODE(hereset,if List.for_all is_empty_node l then MyMap.create() else m)
;;

let rec at_path f (NODE (hereset,m)) = function
    [] -> cleanse_arcs(NODE(f hereset,m))
  | h::t ->
    let m = assure_arc m h
    in cleanse_arcs(NODE(hereset,
                         MyMap.remap m h (at_path f (MyMap.map m h) t)))
;;

let add tm (path,v) =
    at_path (fun hereset -> MySet.add v hereset) tm path
;;

let rmv tm (path,v) =
    at_path (fun hereset -> MySet.rmv v hereset) tm path
;;

let app f tlm = 
 let rec apprec pfx (NODE(hereset,m)) =
    let path = List.rev pfx
    in (MySet.app (fun v -> f(path,v)) hereset;
        MyMap.app (fun (l,tm) -> apprec (l::pfx) tm) m)
 in apprec [] tlm
;;
    
let toList tlm = 
 let rec torec pfx (NODE(hereset,m)) =
    let path = List.rev pfx
    in List.flatten((List.map (fun v -> (path,v)) (MySet.toList hereset))::
            (List.map (fun (l,tm) -> torec (l::pfx) tm) (MyMap.toList m)))
 in torec [] tlm
;;
