(***************************************************************************

(This sentence has been added automatically,
it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


module type IntTagMapModule =
sig
  type 'a key 

  type ('a,'data) t

  val empty : ('a,'data) t
    
  val is_empty : ('a,'data) t -> bool
    
  val add : 'a key -> 'data -> ('a,'data) t -> ('a,'data) t
      
  val find : 'a key -> ('a,'data) t -> 'data
      
  val remove : 'a key -> ('a,'data) t -> ('a,'data) t
      
  val mem :  'a key -> ('a,'data) t -> bool
      
  val iter : ('a key -> 'data -> unit) -> ('a,'data) t -> unit
      
  val map : ('data1 -> 'data2) -> ('a,'data1) t -> ('a,'data2) t
      
  val fold : ('a key -> 'data -> 'accu -> 'accu) -> ('a,'data) t -> 'accu -> 'accu

  val size :  ('a,'data) t -> int

  val elements :  ('a,'data) t -> ('a key * 'data) list

  val elt :  ('a,'data) t -> 'a key * 'data

  val max_tag : ('a,'data) t -> 'a key * 'data

(*

  [case2 f0 f1 f2 f t] returns [f0()] if [t] is empty, [f1 x d] if [t]
  has size 1 and contains [(x,d)], [f2 x1 d1 x2 d2] if [t]
  has size 2 and contains [x1,d1;x2,d2], and [f ()] if [t] has size at least 3

*)
 
  
  
  val case2 : 
    (unit -> 'b) -> 
      ('a key -> 'data -> 'b) -> 
	('a key -> 'data -> 'a key -> 'data -> 'b) ->  
	  (unit -> 'b) -> 
	    ('a,'data) t -> 'b

  val equal : 
    ('data -> 'data -> bool) -> ('a,'data) t -> ('a,'data) t -> bool

end


module MakePoly(O : sig type 'a t val tag : 'a t -> int end) :
  (IntTagMapModule with type 'a key = 'a O.t)


module Make(O : sig type t val tag : t -> int end) :
  (IntTagMapModule with type 'a key = O.t)
