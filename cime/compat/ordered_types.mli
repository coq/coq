(***************************************************************************

Ordered polymorphic types.

CiME Project - D�mons research team - LRI - Universit� Paris XI

$Id$

***************************************************************************)

module type OrderedType =
  sig
    type t
    val compare: t -> t -> int
  end


module type OrderedPolyType =
  sig
    type 'a t
    val compare: 'a t -> 'a t -> int
  end

