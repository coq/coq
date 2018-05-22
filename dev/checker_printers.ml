(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Names
open Univ

let pp   x = Pp.pp_with Format.std_formatter x

(** Future printer *)

let ppfuture kx = pp (Future.print (fun _ -> str "_") kx)

(* name printers *)
let ppid id = pp (Id.print id)
let pplab l = pp (Label.print l)
let ppmbid mbid = pp (str (MBId.debug_to_string mbid))
let ppdir dir = pp (DirPath.print dir)
let ppmp mp = pp(str (ModPath.debug_to_string mp))
let ppcon con = pp(Constant.debug_print con)
let ppproj con = pp(Constant.debug_print (Projection.constant con))
let ppkn kn = pp(str (KerName.to_string kn))
let ppmind kn = pp(MutInd.debug_print kn)
let ppind (kn,i) = pp(MutInd.debug_print kn ++ str"," ++int i)

(* term printers *)
let ppbigint n = pp (str (Bigint.to_string n));;

let prset pr l = str "[" ++ hov 0 (prlist_with_sep spc pr l) ++ str "]"
let ppintset l = pp (prset int (Int.Set.elements l))
let ppidset l = pp (prset Id.print (Id.Set.elements l))

let prset' pr l = str "[" ++ hov 0 (prlist_with_sep pr_comma pr l) ++ str "]"

let pridmap pr l =
  let pr (id,b) = Id.print id ++ str "=>" ++ pr id b in
  prset' pr (Id.Map.fold (fun a b l -> (a,b)::l) l [])
let ppidmap pr l = pp (pridmap pr l)

let pridmapgen l =
  let dom = Id.Set.elements (Id.Map.domain l) in
  if dom = [] then str "[]" else
  str "[domain= " ++ hov 0 (prlist_with_sep spc Id.print dom) ++ str "]"
let ppidmapgen l = pp (pridmapgen l)

let prididmap = pridmap (fun _ -> Id.print)
let ppididmap = ppidmap (fun _ -> Id.print)

let pP s = pp (hov 0 s)

(* proof printers *)
let ppuni u = pp(Universe.pr u)
let ppuni_level u = pp (Level.pr u)

let ppuniverse_set l = pp (LSet.pr l)
let ppuniverse_instance l = pp (Instance.pr l)
let ppauniverse_context l = pp (AUContext.pr Level.pr l)
let ppuniverse_context l = pp (pr_universe_context Level.pr l)
let ppconstraints c = pp (pr_constraints Level.pr c)
let ppuniverse_context_future c =
  let ctx = Future.force c in
    ppuniverse_context ctx
let ppuniverses u = pp (Univ.pr_universes u)

let pploc x = let (l,r) = Loc.unloc x in
  print_string"(";print_int l;print_string",";print_int r;print_string")"
