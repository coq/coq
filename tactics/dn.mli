type 'res lookup_res = Label of 'res | Nothing | Everything


module Make :
    functor (Y : Map.OrderedType) ->
      functor (Z : Map.OrderedType) ->
sig

  type 'a decompose_fun = 'a -> (Y.t * 'a list) option

  type t

  val empty : t

  (** [add t f (tree,inf)] adds a structured object [tree] together with
     the associated information [inf] to the table [t]; the function
     [f] is used to translated [tree] into its prefix decomposition: [f]
     must decompose any tree into a label characterizing its root node and
     the list of its subtree *)

  val add : t -> 'a decompose_fun -> 'a * Z.t -> t

  val rmv : t -> 'a decompose_fun -> 'a * Z.t -> t

  type 'tree lookup_fun = 'tree -> (Y.t * 'tree list) lookup_res


(** [lookup t f tree] looks for trees (and their associated
   information) in table [t] such that the structured object [tree]
   matches against them; [f] is used to translated [tree] into its
   prefix decomposition: [f] must decompose any tree into a label
   characterizing its root node and the list of its subtree *)

  val lookup : t -> 'term lookup_fun -> 'term
    -> Z.t list

  val app : (Z.t -> unit) -> t -> unit

end
