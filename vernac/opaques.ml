(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(** {6 Tables of opaque proof terms} *)

(** We now store opaque proof terms apart from the rest of the environment.
    See the [Indirect] constructor in [Lazyconstr.lazy_constr]. This way,
    we can quickly load a first half of a .vo file without these opaque
    terms, and access them only when a specific command (e.g. Print or
    Print Assumptions) needs it. *)

(** Current table of opaque terms *)

module Summary =
struct
  type t = Opaqueproof.proofterm Opaqueproof.HandleMap.t
  let state : t ref = ref Opaqueproof.HandleMap.empty
  let init () = state := Opaqueproof.HandleMap.empty
  let freeze ~marshallable =
    if marshallable then
      let iter _ pf = ignore (Future.join pf) in
      let () = Opaqueproof.HandleMap.iter iter !state in
      !state
    else !state
  let unfreeze s = state := s

  let join ?(except=Future.UUIDSet.empty) () =
    let iter i pf =
      if Future.UUIDSet.mem (Future.uuid pf) except then ()
      else ignore (Future.join pf)
    in
    Opaqueproof.HandleMap.iter iter !state

end

type opaque_disk = Opaqueproof.opaque_proofterm option array

let get_opaque_disk i t =
  let i = Opaqueproof.repr_handle i in
  let () = assert (0 <= i && i < Array.length t) in
  t.(i)

let set_opaque_disk i (c, priv) t =
  let i = Opaqueproof.repr_handle i in
  let () = assert (0 <= i && i < Array.length t) in
  let () = assert (Option.is_empty t.(i)) in
  let c = Constr.hcons c in
  t.(i) <- Some (c, priv)

let current_opaques = Summary.state

let declare_defined_opaque i (body : Safe_typing.private_constants Entries.const_entry_body) =
  (* TODO: don't rely on global effect *)
  let proof =
    Future.chain body begin fun (body, eff) ->
      Global.join_opaque i (body, eff)
    end
  in
  let () = assert (not @@ Opaqueproof.HandleMap.mem i !current_opaques) in
  current_opaques := Opaqueproof.HandleMap.add i proof !current_opaques

let declare_private_opaque opaque =
  let (i, (body, univs)) = Safe_typing.repr_exported_opaque opaque in
  (* Joining was already done at private declaration time *)
  let univs = match univs with
  | Opaqueproof.PrivateMonomorphic () -> Opaqueproof.PrivateMonomorphic Univ.ContextSet.empty
  | Opaqueproof.PrivatePolymorphic (n, actx) -> Opaqueproof.PrivatePolymorphic (n, actx)
  in
  let proof = Future.from_val (body, univs) in
  let () = assert (not @@ Opaqueproof.HandleMap.mem i !current_opaques) in
  current_opaques := Opaqueproof.HandleMap.add i proof !current_opaques

let get_current_opaque i =
  try
    let pf = Opaqueproof.HandleMap.find i !current_opaques in
    let c, ctx = Future.force pf in
    let ctx = match ctx with
    | Opaqueproof.PrivateMonomorphic _ -> Opaqueproof.PrivateMonomorphic ()
    | Opaqueproof.PrivatePolymorphic _ as ctx -> ctx
    in
    Some (c, ctx)
  with Not_found -> None

let get_current_constraints i =
  try
    let pf = Opaqueproof.HandleMap.find i !current_opaques in
    let c, ctx = Future.force pf in
    let ctx = match ctx with
    | Opaqueproof.PrivateMonomorphic ctx -> ctx
    | Opaqueproof.PrivatePolymorphic _ -> Univ.ContextSet.empty
    in
    Some ctx
  with Not_found -> None

let dump ?(except=Future.UUIDSet.empty) () =
  let n =
    if Opaqueproof.HandleMap.is_empty !current_opaques then 0
    else (Opaqueproof.repr_handle @@ fst @@ Opaqueproof.HandleMap.max_binding !current_opaques) + 1
  in
  let opaque_table = Array.make n None in
  let fold i cu f2t_map =
    let i = Opaqueproof.repr_handle i in
    let uid = Future.uuid cu in
    let f2t_map = Future.UUIDMap.add uid i f2t_map in
    let c =
      if Future.is_val cu then
        let (c, priv) = Future.force cu in
        let priv = match priv with
        | Opaqueproof.PrivateMonomorphic _ -> Opaqueproof.PrivateMonomorphic ()
        | Opaqueproof.PrivatePolymorphic _ as p -> p
        in
        Some (c, priv)
      else if Future.UUIDSet.mem uid except then None
      else
        CErrors.anomaly
          Pp.(str"Proof object "++int i++str" is not checked nor to be checked")
    in
    let () = opaque_table.(i) <- c in
    f2t_map
  in
  let f2t_map = Opaqueproof.HandleMap.fold fold !current_opaques Future.UUIDMap.empty in
  (opaque_table, f2t_map)
