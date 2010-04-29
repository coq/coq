






module Make : 
  functor (X : Set.OrderedType) ->
    functor (Y : Map.OrderedType) ->
      functor (Z : Map.OrderedType) ->
sig

  type decompose_fun = X.t -> (Y.t * X.t list) option
    
  type t

  val create : unit -> t
    
  (** [add t f (tree,inf)] adds a structured object [tree] together with
     the associated information [inf] to the table [t]; the function
     [f] is used to translated [tree] into its prefix decomposition: [f]
     must decompose any tree into a label characterizing its root node and
     the list of its subtree *)
    
  val add : t -> decompose_fun -> X.t * Z.t -> t
    
  val rmv : t -> decompose_fun -> X.t * Z.t -> t
    
  type 'res lookup_res = Label of 'res | Nothing | Everything
      
  type 'tree lookup_fun = 'tree -> (Y.t * 'tree list) lookup_res
    

(** [lookup t f tree] looks for trees (and their associated
   information) in table [t] such that the structured object [tree]
   matches against them; [f] is used to translated [tree] into its
   prefix decomposition: [f] must decompose any tree into a label
   characterizing its root node and the list of its subtree *)
    
  val lookup : t -> 'term lookup_fun -> 'term
    -> (X.t * Z.t) list
    
  val app : ((X.t * Z.t) -> unit) -> t -> unit
    
  val skip_arg : int -> t -> (t * bool) list
    
end
