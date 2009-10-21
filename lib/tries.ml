(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)



module Make = 
  functor (X : Set.OrderedType) ->
    functor (Y : Map.OrderedType) ->
struct
  module T_dom = Set.Make(X) 
  module T_codom = Map.Make(Y) 

  type t = Node of T_dom.t * t T_codom.t

  let codom_to_list m = T_codom.fold (fun x y l -> (x,y)::l) m []

  let codom_rng m = T_codom.fold (fun _ y acc -> y::acc) m []

  let codom_dom m = T_codom.fold (fun x _ acc -> x::acc) m []

  let empty = Node (T_dom.empty, T_codom.empty)

  let map (Node (_,m)) lbl = T_codom.find lbl m

  let xtract (Node (hereset,_)) = T_dom.elements hereset
    
  let dom (Node (_,m)) = codom_dom m

  let in_dom (Node (_,m)) lbl = T_codom.mem lbl m

  let is_empty_node (Node(a,b)) = (T_dom.elements a = []) & (codom_to_list b = [])

let assure_arc m lbl =
  if T_codom.mem lbl m then 
    m
  else 
    T_codom.add lbl (Node (T_dom.empty,T_codom.empty)) m

let cleanse_arcs (Node (hereset,m)) =
  let l = codom_rng m in 
  Node(hereset, if List.for_all is_empty_node l then T_codom.empty else m)

let rec at_path f (Node (hereset,m)) = function
  | [] -> 
      cleanse_arcs (Node(f hereset,m))
  | h::t ->
      let m = assure_arc m h in 
      cleanse_arcs (Node(hereset,
                         T_codom.add h (at_path f (T_codom.find h m) t) m))

let add tm (path,v) =
  at_path (fun hereset -> T_dom.add v hereset) tm path
    
let rmv tm (path,v) =
  at_path (fun hereset -> T_dom.remove v hereset) tm path

let app f tlm = 
  let rec apprec pfx (Node(hereset,m)) =
    let path = List.rev pfx in 
    T_dom.iter (fun v -> f(path,v)) hereset;
    T_codom.iter (fun l tm -> apprec (l::pfx) tm) m
  in 
  apprec [] tlm
    
let to_list tlm = 
  let rec torec pfx (Node(hereset,m)) =
    let path = List.rev pfx in 
    List.flatten((List.map (fun v -> (path,v)) (T_dom.elements hereset))::
		 (List.map (fun (l,tm) -> torec (l::pfx) tm) (codom_to_list m)))
  in 
  torec [] tlm

end
