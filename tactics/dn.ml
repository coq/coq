
(* $Id$ *)

(* This file implements the basic structure of what Chet called
   ``discrimination nets''. If my understanding is wright, it serves
   to associate actions (for example, tactics) with a priority to term
   patterns, so that if a hypothesis matches a pattern in the net,
   then the associated tactic is applied. Discrimination nets are used
   (only) to implement the tactics Auto, DHyp and Point.

   A discrimination net is a tries structure, that is, a tree structure 
   specially conceived for searching patterns, like for example strings
   --see the file Tlm.ml in the directory lib/util--. Here the tries
   structure are used for looking for term patterns.

   This module is then used in :
     - termdn.ml   (discrimination nets of terms);
     - btermdn.ml  (discrimination nets of terms with bounded depth,
                    used in the tactic auto);
     - nbtermdn.ml (named discrimination nets with bounded depth, used
                    in the tactics Dhyp and Point).
  Eduardo (4/8/97) *)

(* Definition of the basic structure *)

type ('lbl,'pat) dn_args = 'pat -> ('lbl * 'pat list) option

type ('lbl,'pat,'inf) under_t = (('lbl * int) option,'pat * 'inf) Tlm.t

type ('lbl,'pat,'inf) t = {
  tm   : ('lbl,'pat,'inf) under_t; 
  args :('lbl,'pat) dn_args }

let create dna = {tm = Tlm.create(); args = dna}

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
  try [Tlm.map tm lbl] with Not_found -> []

let lookup dnm dna' t =
  let rec lookrec t tm =
    (tm_of tm None)@
    (match dna' t with
       | None -> []
       | Some(lbl,v) ->
	   List.fold_left 
	     (fun l c -> List.flatten(List.map (lookrec c) l))
             (tm_of tm (Some(lbl,List.length v))) v)
    in 
  List.flatten(List.map Tlm.xtract (lookrec t dnm.tm))

let upd dnm f = { args = dnm.args; tm = f dnm.args dnm.tm }

let add dnm (pat,inf) =
  upd dnm
    (fun dna tm ->
       let p = path_of dna pat in Tlm.add tm (p,(pat,inf)))
    
let rmv dnm (pat,inf) =
  upd dnm
    (fun dna tm ->
       let p = path_of dna pat in Tlm.rmv tm (p,(pat,inf)))
    
let app f dnm = Tlm.app (fun (_,p) -> f p) dnm.tm
