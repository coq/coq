




module Make :
  functor (X : Set.OrderedType) ->
    functor (Y : Map.OrderedType) ->
sig
     
  type t 
    
  val empty : t
      
  (* Work on labels, not on paths. *)

  val map : t -> Y.t -> t

  val xtract : t -> X.t list
    
  val dom : t -> Y.t list

  val in_dom : t -> Y.t -> bool

  (* Work on paths, not on labels. *)

  val add : t -> Y.t list * X.t -> t
  
  val rmv : t -> Y.t list * X.t -> t 

  val app : ((Y.t list * X.t) -> unit) -> t -> unit
    
  val to_list : t -> (Y.t list * X.t) list
end
