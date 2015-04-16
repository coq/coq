open Util

type 'res lookup_res = Label of 'res | Nothing | Everything

module Make =
    functor (Y : Map.OrderedType) ->
      functor (Z : Map.OrderedType) ->
struct

  module Y_tries = struct
    type t = (Y.t * int) option
    let compare x y =
      match x,y with
	  None,None -> 0
	| Some (l,n),Some (l',n') ->
	    let m = Y.compare l l' in
	    if Int.equal m 0 then
	      n-n'
	    else m
	| Some(l,n),None -> 1
	| None, Some(l,n) -> -1
  end
  module ZSet = Set.Make(Z)
  module X_tries =
  struct
    type t = ZSet.t
    let nil = ZSet.empty
    let is_nil = ZSet.is_empty
    let add = ZSet.union
    let sub = ZSet.diff
  end

  module Trie = Trie.Make(Y_tries)(X_tries)

  type 'a decompose_fun = 'a -> (Y.t * 'a list) option

  type 'tree lookup_fun = 'tree -> (Y.t * 'tree list) lookup_res

  type  t = Trie.t

  let empty = Trie.empty

(* [path_of dna pat] returns the list of nodes of the pattern [pat] read in
prefix ordering, [dna] is the function returning the main node of a pattern *)

  let path_of dna =
    let rec path_of_deferred = function
      | [] -> []
      | h::tl -> pathrec tl h

    and pathrec deferred t =
      match dna t with
	| None ->
	    None :: (path_of_deferred deferred)
	| Some (lbl,[]) ->
	    (Some (lbl,0))::(path_of_deferred deferred)
	| Some (lbl,(h::def_subl as v)) ->
	    (Some (lbl,List.length v))::(pathrec (def_subl@deferred) h)
    in
      pathrec []

  let tm_of tm lbl =
    try [Trie.next tm lbl, true] with Not_found -> []

  let rec skip_arg n tm =
    if Int.equal n 0 then [tm, true]
    else
      let labels = Trie.labels tm in
      let map lbl = match lbl with
      | None -> skip_arg (pred n) (Trie.next tm lbl)
      | Some (_, m) ->
        skip_arg (pred n + m) (Trie.next tm lbl)
      in
      List.flatten (List.map map labels)

  let lookup tm dna t =
    let rec lookrec t tm =
      match dna t with
	| Nothing -> tm_of tm None
	| Label(lbl,v) ->
	    tm_of tm None@
	      (List.fold_left
		 (fun l c ->
		List.flatten(List.map (fun (tm, b) ->
					 if b then lookrec c tm
					 else [tm,b]) l))
		 (tm_of tm (Some(lbl,List.length v))) v)
	| Everything -> skip_arg 1 tm
    in
    List.flatten (List.map (fun (tm,b) -> ZSet.elements (Trie.get tm)) (lookrec t tm))

  let add tm dna (pat,inf) =
    let p = path_of dna pat in Trie.add p (ZSet.singleton inf) tm

  let rmv tm dna (pat,inf) =
    let p = path_of dna pat in Trie.remove p (ZSet.singleton inf) tm

  let app f tm = Trie.iter (fun _ p -> ZSet.iter f p) tm

end

