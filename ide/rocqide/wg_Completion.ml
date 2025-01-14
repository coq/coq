(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module StringOrd =
struct
  type t = string
  let compare s1 s2 =
    (* we use first size, then usual comparison *)
    let d = String.length s1 - String.length s2 in
    if d <> 0 then d
    else compare s1 s2
end

module Proposals = Set.Make(StringOrd)

(** Retrieve completion proposals in the buffer *)
let get_syntactic_completion (buffer : GText.buffer) pattern accu =
  let rec get_aux accu (iter : GText.iter) =
    match iter#forward_search pattern with
    | None -> accu
    | Some (start, stop) ->
      if Gtk_parsing.starts_word start then
        let ne = Gtk_parsing.find_word_end stop in
        if ne#compare stop = 0 then get_aux accu stop
        else
          let proposal = buffer#get_text ~start ~stop:ne () in
          let accu = Proposals.add proposal accu in
          get_aux accu stop
      else get_aux accu stop
  in
  get_aux accu buffer#start_iter

(** Retrieve completion proposals in Rocq libraries *)
let get_semantic_completion pattern accu =
  let flags = [Interface.Name_Pattern ("^" ^ pattern), true] in
  (* Only get the last part of the qualified name *)
  let rec last accu = function
  | [] -> accu
  | [basename] -> Proposals.add basename accu
  | _ :: l -> last accu l
  in
  let next = function
  | Interface.Good l ->
    let fold accu elt = last accu elt.Interface.coq_object_qualid in
    let ans = List.fold_left fold accu l in
    RocqDriver.return ans
  | _ -> RocqDriver.return accu
  in
  RocqDriver.bind (RocqDriver.search flags) next

let is_substring s1 s2 =
  let s1 = Glib.Utf8.to_unistring s1 in
  let s2 = Glib.Utf8.to_unistring s2 in
  let break = ref true in
  let i = ref 0 in
  let len1 = Array.length s1 in
  let len2 = Array.length s2 in
  while !break && !i < len1 && !i < len2 do
    break := s1.(!i) = s2.(!i);
    incr i;
  done;
  if !break then len2 - len1
  else -1

class completion_provider buffer rocqtop =
  let self_provider = ref None in
  let active = ref true in
  let provider = object (self)

    val mutable auto_complete_length = 3
    val mutable cache = (-1, "", Proposals.empty)
    val mutable insert_offset = -1

    method name = ""

    method icon = None

    method private update_proposals pref =
      let (_, _, props) = cache in
      let filter prop = 0 <= is_substring pref prop in
      let props = Proposals.filter filter props in
      props

    method private add_proposals ctx props =
      let mk text =
        let item = GSourceView3.source_completion_item ~text ~label:text () in
        (item :> GSourceView3.source_completion_proposal)
      in
      let props = List.map mk (Proposals.elements props) in
      ctx#add_proposals (Option.get !self_provider) props true

    method populate ctx =
      let iter = buffer#get_iter_at_mark `INSERT in
      let () = insert_offset <- iter#offset in
      let () = Minilib.log (Printf.sprintf "Completion at offset: %i" insert_offset) in
      let buffer = new GText.buffer iter#buffer in
      if not (Gtk_parsing.ends_word iter#backward_char) then self#add_proposals ctx Proposals.empty else
      let start = Gtk_parsing.find_word_start iter in
      if iter#offset - start#offset < auto_complete_length then self#add_proposals ctx Proposals.empty else
      let w = start#get_text ~stop:iter in
      let () = Minilib.log ("Completion of prefix: '" ^ w ^ "'") in
      let (off, prefix, props) = cache in
      let start_offset = start#offset in
      (* check whether we have the last request in cache *)
      if (start_offset = off) && (0 <= is_substring prefix w) then
        let props = self#update_proposals w in
        self#add_proposals ctx props
      else
        let cancel = ref false in
        let _ = ctx#connect#cancelled ~callback:(fun () -> cancel := true) in
        let update props =
          let () = cache <- (start_offset, w, props) in
          if not !cancel then self#add_proposals ctx props
        in
        (* If not in the cache, we recompute it: first syntactic *)
        let synt = get_syntactic_completion buffer w Proposals.empty in
        (* Then semantic *)
        let next props =
          update props;
          RocqDriver.return ()
        in
        let query = RocqDriver.bind (get_semantic_completion w synt) next in
        (* If rocqtop is computing, do the syntactic completion altogether *)
        let occupied () = update synt in
        ignore @@ RocqDriver.try_grab rocqtop query occupied

    method matched ctx = !active

    method activation = [`INTERACTIVE; `USER_REQUESTED]

    method info_widget proposal = None

    method update_info proposal info = ()

    method start_iter ctx proposal iter = false

    method activate_proposal proposal iter = false

    method interactive_delay = (-1)

    method priority = 0

  end in
  let provider = GSourceView3.source_completion_provider provider in
  object (self)

    inherit GSourceView3.source_completion_provider provider#as_source_completion_provider

    method active = !active

    method set_active b = active := b

    initializer
      self_provider := Some (self :> GSourceView3.source_completion_provider)

  end
