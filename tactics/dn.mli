
(* $Id$ *)

(* Discrimination nets. *)

type ('lbl,'pat) dn_args = 'pat -> ('lbl * 'pat list) option

type ('lbl,'pat,'inf) t = {
  tm : (('lbl * int) option,'pat * 'inf) Tlm.t;
  args : ('lbl,'pat) dn_args }

type ('lbl,'pat,'inf) under_t = (('lbl * int) option,'pat * 'inf) Tlm.t
				  
val create : ('lbl,'pat) dn_args -> ('lbl,'pat,'inf) t
    
val add : ('lbl,'pat,'inf) t -> 'pat * 'inf -> ('lbl,'pat,'inf) t

val rmv : ('lbl,'pat,'inf) t -> 'pat * 'inf -> ('lbl,'pat,'inf) t

val path_of : ('lbl,'pat) dn_args -> 'pat -> ('lbl * int) option list
    
val lookup : 
  ('lbl,'pat,'inf) t -> ('lbl,'term) dn_args -> 'term -> ('pat * 'inf) list

val app : (('pat * 'inf) -> unit) -> ('lbl,'pat,'inf) t -> unit
