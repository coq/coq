




module Make = 
  functor (X : Set.OrderedType) ->
    functor (Y : Map.OrderedType) ->
      functor (Z : Map.OrderedType) ->
struct
  
  module Y_tries = struct
    type t = (Y.t * int) option
    let compare x y = 
      match x,y with
	  None,None -> 0
	| Some (l,n),Some (l',n') -> 
	    if (Y.compare l l') = 0 && n = n' then 0 
	    else Pervasives.compare x y
	| a,b -> Pervasives.compare a b 
  end
  module X_tries = struct
    type t = X.t * Z.t
    let compare (x1,x2) (y1,y2) = 
	    if (X.compare x1 y1) = 0 && (Z.compare x2 y2)=0 then 0 
	    else Pervasives.compare (x1,x2) (y1,y2)
  end

  module T = Tries.Make(X_tries)(Y_tries)
    
  type  decompose_fun = X.t -> (Y.t * X.t list) option
    
  type 'res lookup_res = Label of 'res | Nothing | Everything
    
  type 'tree lookup_fun = 'tree -> (Y.t * 'tree list) lookup_res

  type  t = T.t

  let create () = T.empty

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
    try [T.map tm lbl, true] with Not_found -> []
      
  let rec skip_arg n tm =
    if n = 0 then [tm,true]
    else
      List.flatten 
	(List.map 
	   (fun a -> match a with
	      | None -> skip_arg (pred n) (T.map tm a)
	      | Some (lbl,m) -> 
		  skip_arg (pred n + m) (T.map tm a)) 
	   (T.dom tm))
	
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
      List.flatten (List.map (fun (tm,b) -> T.xtract tm) (lookrec t tm))
	
  let add tm dna (pat,inf) =
    let p = path_of dna pat in T.add tm (p,(pat,inf))
				 
  let rmv tm dna (pat,inf) =
  let p = path_of dna pat in T.rmv tm (p,(pat,inf))
			       
  let app f tm = T.app (fun (_,p) -> f p) tm
    
end
  
