(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

let skip_qed_typecheck = ref false

type opaque_proof =
| Checked of Safe_typing.opaque_certificate
| Unchecked of Constr.t * Univ.ContextSet.t Opaqueproof.delayed_universes
(** A proof that the kernel did not type, see {!skip_qed_typecheck}. *)

let fill_proof i = function
| Checked cert -> Global.fill_opaque cert
| Unchecked (c, ctx) -> Global.fill_unchecked_opaque i c ctx

(** The proof and whether the kernel did not type it. *)
let repr_proof = function
| Checked cert -> Safe_typing.repr_certificate cert, false
| Unchecked (c, ctx) -> (c, ctx), true

type opaque_result =
| OpaqueCertif of opaque_proof Future.computation
| OpaqueValue of Opaqueproof.opaque_proofterm * bool
(** The boolean is [true] when the kernel did not type the proof. *)

(** Current table of opaque terms *)

module Summary =
struct
  type t = opaque_result Opaqueproof.HandleMap.t
  let state : t ref = ref Opaqueproof.HandleMap.empty
  let init () = state := Opaqueproof.HandleMap.empty
  let freeze () = !state
  let unfreeze s = state := s

  let join ?(except=Future.UUIDSet.empty) () =
    let iter i pf = match pf with
    | OpaqueValue _ -> ()
    | OpaqueCertif cert ->
      if Future.UUIDSet.mem (Future.uuid cert) except then ()
      else if Safe_typing.is_filled_opaque i (Global.safe_env ()) then
        assert (Future.is_over cert)
      else
        (* Little belly dance to preserve the fix_exn wrapper around filling *)
        Future.force @@ Future.chain cert (fun cert -> fill_proof i cert)
    in
    Opaqueproof.HandleMap.iter iter !state

  let inline ?(except=Future.UUIDSet.empty) () =
    let () = join ~except () in
    let map _ pf = match pf with
    | OpaqueValue _ -> pf
    | OpaqueCertif cert ->
      if Future.UUIDSet.mem (Future.uuid cert) except then pf
      else
        let (c, ctx), unchecked = repr_proof (Option.get (Future.peek_val cert)) in
        let ctx = match ctx with
        | Opaqueproof.PrivateMonomorphic _ -> Opaqueproof.PrivateMonomorphic ()
        | Opaqueproof.PrivatePolymorphic _ as ctx -> ctx
        in
        OpaqueValue ((c, ctx), unchecked)
    in
    state := Opaqueproof.HandleMap.mapi map !state

end

(** Each entry holds a proof and whether the kernel did not type it. *)
type opaque_disk = (Opaqueproof.opaque_proofterm * bool) option array

let get_opaque_disk i t =
  let i = Opaqueproof.repr_handle i in
  let () = assert (0 <= i && i < Array.length t) in
  t.(i)

let set_opaque_disk i (c, priv) t =
  let i = Opaqueproof.repr_handle i in
  let () = assert (0 <= i && i < Array.length t) in
  let () = assert (Option.is_empty t.(i)) in
  let _, c = Constr.hcons c in
  t.(i) <- Some ((c, priv), false)

let current_opaques = Summary.state

let unchecked_opaque ~poly pf =
  let c, ctx = Safe_typing.inline_private_constants (Global.env ()) pf in
  let _, c = Constr.hcons c in
  let _, ctx = Univ.ContextSet.hcons ctx in
  let ctx =
    if poly then Opaqueproof.PrivatePolymorphic ctx
    else Opaqueproof.PrivateMonomorphic ctx
  in
  Unchecked (c, ctx)

let declare_defined_opaque ?feedback_id ~poly i (body : Safe_typing.private_constants const_entry_body) =
  (* Note that the environment in which the variable is checked it the one when
     the thunk is evaluated, not the one where this function is called. It does
     not matter because the former must be an extension of the latter or
     otherwise the call to Safe_typing would throw an anomaly. *)
  let proof = Future.chain body begin fun pf ->
      let proof =
        if !skip_qed_typecheck then unchecked_opaque ~poly pf
        else Checked (Safe_typing.check_opaque (Global.safe_env ()) i pf)
      in
      let () = Option.iter (fun id -> Feedback.feedback ~id Feedback.Complete) feedback_id in
      proof
    end
  in
  (* If the proof is already computed we fill it eagerly *)
  let () = match Future.peek_val proof with
  | None -> ()
  | Some proof -> fill_proof i proof
  in
  let proof = OpaqueCertif proof in
  let () = assert (not @@ Opaqueproof.HandleMap.mem i !current_opaques) in
  current_opaques := Opaqueproof.HandleMap.add i proof !current_opaques

let declare_private_opaque opaque =
  let (i, pf) = Safe_typing.repr_exported_opaque opaque in
  (* Joining was already done at private declaration time *)
  let proof = OpaqueValue (pf, false) in
  let () = assert (not @@ Opaqueproof.HandleMap.mem i !current_opaques) in
  current_opaques := Opaqueproof.HandleMap.add i proof !current_opaques

let get_current_opaque i =
  try
    let pf = Opaqueproof.HandleMap.find i !current_opaques in
    match pf with
    | OpaqueValue (pf, unchecked) -> Some (pf, unchecked)
    | OpaqueCertif cert ->
      let (c, ctx), unchecked = repr_proof (Future.force cert) in
      let ctx = match ctx with
      | Opaqueproof.PrivateMonomorphic _ -> Opaqueproof.PrivateMonomorphic ()
      | Opaqueproof.PrivatePolymorphic _ as ctx -> ctx
      in
      Some ((c, ctx), unchecked)
  with Not_found -> None

let get_current_constraints i =
  try
    let pf = Opaqueproof.HandleMap.find i !current_opaques in
    match pf with
    | OpaqueValue _ -> None
    | OpaqueCertif cert ->
      let (_, ctx), _ = repr_proof (Future.force cert) in
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
  | OpaqueValue (p, unchecked) ->
    let i = Opaqueproof.repr_handle h in
    let () = opaque_table.(i) <- Some (p, unchecked) in
    f2t_map
  | OpaqueCertif cert ->
    let i = Opaqueproof.repr_handle h in
    let f2t_map, proof =
      let uid = Future.uuid cert in
      let f2t_map = Future.UUIDMap.add uid h f2t_map in
      let c = Future.peek_val cert in
      let () = if Option.is_empty c && (not @@ Future.UUIDSet.mem uid except) then
          CErrors.anomaly
            Pp.(str"Proof object "++int i++str" is not checked nor to be checked")
      in
      f2t_map, c
    in
    let c = match proof with
    | None -> None
    | Some proof ->
      let (c, priv), unchecked = repr_proof proof in
      let priv = match priv with
      | Opaqueproof.PrivateMonomorphic _ -> Opaqueproof.PrivateMonomorphic ()
      | Opaqueproof.PrivatePolymorphic _ as p -> p
      in
      Some ((c, priv), unchecked)
    in
    let () = opaque_table.(i) <- c in
    f2t_map
  in
  let f2t_map = Opaqueproof.HandleMap.fold fold !current_opaques Future.UUIDMap.empty in
  (opaque_table, f2t_map)
