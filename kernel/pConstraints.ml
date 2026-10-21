(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ
open Sorts

type t = ElimConstraints.t * UnivConstraints.t

type pconstraints = t

let make q u = (q, u)

let qualities = fst

let univs = snd

let add_quality q (qc, lc) = (ElimConstraints.add q qc, lc)

let add_univ u (qc, lc) = (qc, UnivConstraints.add u lc)

let of_qualities qc = make qc UnivConstraints.empty

let of_univs lc = make ElimConstraints.empty lc

let set_qualities qc (_,lc) = make qc lc

let set_univs lc (qc,_) = make qc lc

let empty = (ElimConstraints.empty, UnivConstraints.empty)

let is_empty (qc, lc) =
  ElimConstraints.is_empty qc && UnivConstraints.is_empty lc

let equal (qc, lc) (qc', lc') =
  ElimConstraints.equal qc qc' && UnivConstraints.equal lc lc'

let union (qc, lc) (qc', lc') =
  (ElimConstraints.union qc qc', UnivConstraints.union lc lc')

let fold (qf, lf) (qc, lc) (x, y) =
  (ElimConstraints.fold qf qc x, UnivConstraints.fold lf lc y)

let diff (qc, lc) (qc', lc') =
  (ElimConstraints.diff qc qc', UnivConstraints.diff lc lc')

let elements (qc, lc) =
  (ElimConstraints.elements qc, UnivConstraints.elements lc)

let filter_qualities f (qc, lc) =
  make (ElimConstraints.filter f qc) lc

let filter_univs f (qc, lc) =
  make qc @@ UnivConstraints.filter f lc

let pr (printer:Sorts.printer) (qc, lc) =
  let open Pp in
  let sep = if ElimConstraints.is_empty qc || UnivConstraints.is_empty lc
            then mt ()
            else pr_comma () in
  v 0 (ElimConstraints.pr printer.prq qc ++ sep ++ UnivConstraints.pr printer.pru lc)

module HPConstraints =
  Hashcons.Make(
    struct
      type t = pconstraints
      let hashcons (qf, uf) =
        let hqf, qf = ElimConstraints.hcons qf in
        let huf, uf = UnivConstraints.hcons uf in
        Hashset.Combine.(combine hqf huf), (qf, uf)
      let eq (qc, uc) (qc', uc') =
        qc == qc' && uc == uc'
    end)

let hcons =
  Hashcons.simple_hcons
    HPConstraints.generate
    HPConstraints.hcons ()

(** A value with universe constraints. *)
type 'a constrained = 'a * t

let constraints_of (_, cst) = cst

(** Constraints functions. *)

type 'a constraint_function = 'a -> 'a -> t -> t

let enforce_eq_univ u v c =
  (* We discard trivial constraints like u=u *)
  if Level.equal u v then c
  else add_univ (Universe.make u, UnivConstraint.Eq, Universe.make v) c

let enforce_leq_univ u v c =
  if Level.equal u v then c
  else add_univ (Universe.make u, UnivConstraint.Le, Universe.make v) c

let enforce_elim_to q1 q2 csts =
  if QGraph.ElimTable.eliminates_to q1 q2 then csts
  else add_quality (q1, ElimConstraint.ElimTo, q2) csts
