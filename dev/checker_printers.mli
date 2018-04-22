(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Printers for the ocaml toplevel. *)

val pp : Pp.t -> unit
val pP : Pp.t -> unit (* with surrounding box *)

val ppfuture : 'a Future.computation -> unit

val ppid : Names.Id.t -> unit
val pplab : Names.Label.t -> unit
val ppmbid : Names.MBId.t -> unit
val ppdir : Names.DirPath.t -> unit
val ppmp : Names.ModPath.t -> unit
val ppcon : Names.Constant.t -> unit
val ppproj : Names.Projection.t -> unit
val ppkn : Names.KerName.t -> unit
val ppmind : Names.MutInd.t -> unit
val ppind : Names.inductive -> unit

val ppbigint : Bigint.bigint -> unit

val ppintset : Int.Set.t -> unit
val ppidset : Names.Id.Set.t -> unit

val pridmap : (Names.Id.Map.key -> 'a -> Pp.t) -> 'a Names.Id.Map.t -> Pp.t
val ppidmap : (Names.Id.Map.key -> 'a -> Pp.t) -> 'a Names.Id.Map.t -> unit

val pridmapgen : 'a Names.Id.Map.t -> Pp.t
val ppidmapgen : 'a Names.Id.Map.t -> unit

val prididmap : Names.Id.t Names.Id.Map.t -> Pp.t
val ppididmap : Names.Id.t Names.Id.Map.t -> unit

(* Universes *)
val ppuni : Univ.Universe.t -> unit
val ppuni_level : Univ.Level.t -> unit (* raw *)
val ppuniverse_set : Univ.LSet.t -> unit
val ppuniverse_instance : Univ.Instance.t -> unit
val ppauniverse_context : Univ.AUContext.t -> unit
val ppuniverse_context : Univ.UContext.t -> unit
val ppconstraints : Univ.Constraint.t -> unit
val ppuniverse_context_future : Univ.UContext.t Future.computation -> unit
val ppuniverses : Univ.universes -> unit

val pploc : Loc.t -> unit
