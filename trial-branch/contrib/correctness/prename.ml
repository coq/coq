(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Names
open Nameops
open Util
open Pp
open Himsg
open Pmisc

(* Variables names management *)

type date = string

(* The following data structure keeps the successive names of the variables
 * as we traverse the program. A each step a ``date'' and a
 * collection of new names is (possibly) given, and updates the
 * previous renaming.
 * 
 * Then, we can ask for the name of a variable, at current date or
 * at a given date.
 *
 * It is easily represented by a list of date x assoc list, most recent coming 
 * first i.e. as follows:
 *
 *   [ date (= current), [ (x,xi); ... ];
 *     date            , [ (z,zk); ... ];
 *     ...
 *     date (= initial), [ (x,xj); (y,yi); ... ]
 *
 * We also keep a list of all names already introduced, in order to
 * quickly get fresh names.
 *)

type t =
    { levels : (date * (identifier * identifier) list) list;
      avoid  : identifier list;
      cpt    : int }
    

let empty_ren = { levels = []; avoid = []; cpt = 0 }

let update r d ids =
  let al,av = renaming_of_ids r.avoid ids in
  { levels = (d,al) :: r.levels; avoid = av; cpt = r.cpt }

let push_date r d = update r d []

let next r ids =
  let al,av = renaming_of_ids r.avoid ids in
  let n = succ r.cpt in
  let d = string_of_int n in
  { levels = (d,al) :: r.levels; avoid = av; cpt = n }


let find r x =
  let rec find_in_one = function
      []         -> raise Not_found
    | (y,v)::rem -> if y = x then v else find_in_one rem
  in
  let rec find_in_all = function
      []         -> raise Not_found
    | (_,l)::rem -> try find_in_one l with Not_found -> find_in_all rem
  in
    find_in_all r.levels


let current_var = find

let current_vars r ids = List.map (fun id -> id,current_var r id) ids


let avoid r ids = { levels = r.levels; avoid = r.avoid @ ids; cpt = r.cpt }

let fresh r ids = fst (renaming_of_ids r.avoid ids)


let current_date r =
  match r.levels with
      [] -> invalid_arg "Renamings.current_date"
    | (d,_)::_ -> d

let all_dates r = List.map fst r.levels

let rec valid_date da r = 
  let rec valid = function
      [] -> false
    | (d,_)::rem -> (d=da) or (valid rem)
  in
    valid r.levels

(* [until d r] selects the part of the renaming [r] starting from date [d] *)
let rec until da r =
  let rec cut = function
      [] -> invalid_arg "Renamings.until"
    | (d,_)::rem as r -> if d=da then r else cut rem
  in
    { avoid = r.avoid; levels = cut r.levels; cpt = r.cpt }

let var_at_date r d id =
  try
    find (until d r) id
  with Not_found ->
    raise (UserError ("Renamings.var_at_date",
	      hov 0 (str"Variable " ++ pr_id id ++ str" is unknown" ++ spc () ++
		       str"at date " ++ str d)))

let vars_at_date r d ids =
  let r' = until d r in List.map (fun id -> id,find r' id) ids


(* pretty-printers *)

open Pp
open Util
open Himsg

let pp r = 
  hov 2 (prlist_with_sep (fun () -> (fnl ()))
	   (fun (d,l) -> 
	      (str d ++ str": " ++ 
		 prlist_with_sep (fun () -> (spc ()))
		   (fun (id,id') -> 
		      (str"(" ++ pr_id id ++ str"," ++ pr_id id' ++ str")"))
		   l))
	   r.levels)

let ppr e =
  Pp.pp (pp e)

