(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Names
open Term
open Libobject
open Library
open Pattern
open Libnames

(* Named, bounded-depth, term-discrimination nets.
   Implementation:
   Term-patterns are stored in discrimination-nets, which are
   themselves stored in a hash-table, indexed by the first label.
   They are also stored by name in a table on-the-side, so that we can
   override them if needed. *)

(* The former comments are from Chet.
   See the module dn.ml for further explanations.
   Eduardo (5/8/97) *)

type ('na,'a) t = {
  mutable table : ('na,constr_pattern * 'a) Gmap.t;
  mutable patterns : (global_reference option,'a Btermdn.t) Gmap.t }

type ('na,'a) frozen_t = 
    ('na,constr_pattern * 'a) Gmap.t
    * (global_reference option,'a Btermdn.t) Gmap.t

let create () =
  { table = Gmap.empty;
    patterns = Gmap.empty }

let get_dn dnm hkey =
  try Gmap.find hkey dnm with Not_found -> Btermdn.create ()

let add dn (na,(pat,valu)) =
  let hkey = Option.map fst (Termdn.constr_pat_discr pat) in 
  dn.table <- Gmap.add na (pat,valu) dn.table;
  let dnm = dn.patterns in
  dn.patterns <- Gmap.add hkey (Btermdn.add (get_dn dnm hkey) (pat,valu)) dnm
    
let rmv dn na =
  let (pat,valu) = Gmap.find na dn.table in
  let hkey = Option.map fst (Termdn.constr_pat_discr pat) in 
  dn.table <- Gmap.remove na dn.table;
  let dnm = dn.patterns in
  dn.patterns <- Gmap.add hkey (Btermdn.rmv (get_dn dnm hkey) (pat,valu)) dnm

let in_dn dn na = Gmap.mem na dn.table
			  
let remap ndn na (pat,valu) =
  rmv ndn na;
  add ndn (na,(pat,valu))

let lookup dn valu =
  let hkey = Option.map fst (Termdn.constr_val_discr valu) in 
  try Btermdn.lookup (Gmap.find hkey  dn.patterns) valu with Not_found -> []

let app f dn = Gmap.iter f dn.table
		       
let dnet_depth = Btermdn.dnet_depth
		   
let freeze dn = (dn.table, dn.patterns)

let unfreeze (fnm,fdnm) dn =
  dn.table <- fnm;
  dn.patterns <- fdnm

let empty dn = 
  dn.table <- Gmap.empty;
  dn.patterns <- Gmap.empty

let to2lists dn = 
  (Gmap.to_list dn.table, Gmap.to_list dn.patterns)

