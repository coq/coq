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
    This way, we can quickly load a first half of a .vo file without these opaque
    terms, and access them only when a specific command (e.g. Print or
    Print Assumptions) needs it. *)

type 'a const_entry_body = 'a Entries.proof_output Future.computation

type 'a joinable =
| Computation of 'a Future.computation
| Joined of 'a

type opaque_result =
| OpaqueCertif of Safe_typing.opaque_certificate joinable ref
| OpaqueValue of Opaqueproof.opaque_proofterm

let force c = match !c with
| Computation c -> Future.force c
| Joined v -> v

(** Current table of opaque terms *)

module Summary =
struct
  type t = opaque_result Opaqueproof.HandleMap.t
  let state : t ref = ref Opaqueproof.HandleMap.empty
  let init () = state := Opaqueproof.HandleMap.empty
  let freeze ~marshallable =
    if marshallable then
      let iter _ pf = match pf with
      | OpaqueCertif cert ->
        begin match !cert with
        | Computation c -> cert := Joined (Future.force c)
        | Joined _ -> ()
        end
      | OpaqueValue _ -> ()
      in
      let () = Opaqueproof.HandleMap.iter iter !state in
      !state
    else !state
  let unfreeze s = state := s

  let join ?(except=Future.UUIDSet.empty) () =
    let iter i pf = match pf with
    | OpaqueValue _ -> ()
    | OpaqueCertif cert ->
      match !cert with
      | Joined cert ->
        (* FIXME: in this case we lost the fix_exn wrapper. Does that matter? *)
        if not @@ Safe_typing.is_filled_opaque i (Global.safe_env ()) then Global.fill_opaque cert
      | Computation cert ->
        if Future.UUIDSet.mem (Future.uuid cert) except then ()
        else if Safe_typing.is_filled_opaque i (Global.safe_env ()) then
          assert (Future.is_over cert)
        else
          (* Little belly dance to preserve the fix_exn wrapper around filling *)
          Future.force @@ Future.chain cert (fun cert -> Global.fill_opaque cert)
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

let declare_defined_opaque ?feedback_id i (body : Safe_typing.private_constants const_entry_body) =
  (* Note that the environment in which the variable is checked it the one when
     the thunk is evaluated, not the one where this function is called. It does
     not matter because the former must be an extension of the latter or
     otherwise the call to Safe_typing would throw an anomaly. *)
  let proof = Future.chain body begin fun (body, eff) ->
      let cert = Safe_typing.check_opaque (Global.safe_env ()) i (body, eff) in
      let () = Option.iter (fun id -> Feedback.feedback ~id Feedback.Complete) feedback_id in
      cert
    end
  in
  (* If the proof is already computed we fill it eagerly *)
  let () = match Future.peek_val proof with
  | None -> ()
  | Some cert -> Global.fill_opaque cert
  in
  let proof = OpaqueCertif (ref (Computation proof)) in
  let () = assert (not @@ Opaqueproof.HandleMap.mem i !current_opaques) in
  current_opaques := Opaqueproof.HandleMap.add i proof !current_opaques

let declare_private_opaque opaque =
  let (i, pf) = Safe_typing.repr_exported_opaque opaque in
  (* Joining was already done at private declaration time *)
  let proof = OpaqueValue pf in
  let () = assert (not @@ Opaqueproof.HandleMap.mem i !current_opaques) in
  current_opaques := Opaqueproof.HandleMap.add i proof !current_opaques

let get_current_opaque i =
  try
    let pf = Opaqueproof.HandleMap.find i !current_opaques in
    match pf with
    | OpaqueValue pf -> Some pf
    | OpaqueCertif cert ->
      let c, ctx = Safe_typing.repr_certificate (force cert) in
      let ctx = match ctx with
      | Opaqueproof.PrivateMonomorphic _ -> Opaqueproof.PrivateMonomorphic ()
      | Opaqueproof.PrivatePolymorphic _ as ctx -> ctx
      in
      Some (c, ctx)
  with Not_found -> None

let get_current_constraints i =
  try
    let pf = Opaqueproof.HandleMap.find i !current_opaques in
    match pf with
    | OpaqueValue _ -> None
    | OpaqueCertif cert ->
      let _, ctx = Safe_typing.repr_certificate (force cert) in
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
  let fold h cu f2t_map = match cu with
  | OpaqueValue p ->
    let i = Opaqueproof.repr_handle h in
    let () = opaque_table.(i) <- Some p in
    f2t_map
  | OpaqueCertif c ->
    let i = Opaqueproof.repr_handle h in
    let f2t_map, proof = match !c with
    | Computation cert ->
      let uid = Future.uuid cert in
      let f2t_map = Future.UUIDMap.add uid h f2t_map in
      let c = Future.peek_val cert in
      let () = if Option.is_empty c && (not @@ Future.UUIDSet.mem uid except) then
        CErrors.anomaly
          Pp.(str"Proof object "++int i++str" is not checked nor to be checked")
      in
      f2t_map, c
    | Joined cert -> f2t_map, Some cert
    in
    let c = match proof with
    | None -> None
    | Some cert ->
      let (c, priv) = Safe_typing.repr_certificate cert in
      let priv = match priv with
      | Opaqueproof.PrivateMonomorphic _ -> Opaqueproof.PrivateMonomorphic ()
      | Opaqueproof.PrivatePolymorphic _ as p -> p
      in
      Some (c, priv)
    in
    let () = opaque_table.(i) <- c in
    f2t_map
  in
  let f2t_map = Opaqueproof.HandleMap.fold fold !current_opaques Future.UUIDMap.empty in
  (opaque_table, f2t_map)
