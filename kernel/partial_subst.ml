(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


open Util

type ('term, 'quality, 'univ) t =
  'term WriteOnceArray.t * 'quality WriteOnceArray.t * 'univ WriteOnceArray.t

let make (m, n, p) =
  (WriteOnceArray.make m, WriteOnceArray.make n, WriteOnceArray.make p)

let add_term i t tqus : ('t, 'q, 'u) t =
  on_pi1 (WriteOnceArray.add (i-1) t) tqus

let maybe_add_term io t tqus : ('t, 'q, 'u) t =
  Option.fold_right (fun i -> add_term i t) io tqus

let add_quality i q tqus : ('t, 'q, 'u) t =
  on_pi2 (WriteOnceArray.add i q) tqus

let maybe_add_quality io q tqus : ('t, 'q, 'u) t =
  Option.fold_right (fun i -> add_quality i q) io tqus

let add_univ i u tqus : ('t, 'q, 'u) t =
  on_pi3 (WriteOnceArray.add i u) tqus

let maybe_add_univ io u tqus : ('t, 'q, 'u) t =
  Option.fold_right (fun i -> add_univ i u) io tqus

let to_arrays (ts, qs, us : _ t) =
  (WriteOnceArray.to_array ts, WriteOnceArray.to_array qs, WriteOnceArray.to_array us)

let pr_nodup_array elem v =
  let a = WriteOnceArray.Internal.unsafe_to_array v in
  Pp.(str "[|" ++ prvect_with_sep pr_semicolon (function None -> str "\u{2205}" (* Empty set *) | Some e -> elem e) a++str"|]")

let pr prt prq pru (ts, qas, us) =
  Pp.(pr_nodup_array prt ts ++ pr_comma () ++ pr_nodup_array prq qas ++ pr_comma () ++ pr_nodup_array pru us)
