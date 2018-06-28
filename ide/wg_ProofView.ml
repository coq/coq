(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Preferences
open Ideutils

class type proof_view =
  object
    inherit GObj.widget
    method buffer : GText.buffer
    method refresh : force:bool -> unit
    method clear : unit -> unit
    method set_goals : Interface.goals option -> unit
    method set_evars : Interface.evar list option -> unit
  end

(* tag is the tag to be hooked, item is the item covered by this tag, make_menu
 *  * is the template for building menu if needed, sel_cb is the callback if
 *  there
 *   * is a selection o said menu, hover_cb is the callback when there is only
 *    * hovering *)
let hook_tag_cb tag menu_content sel_cb hover_cb =
  ignore (tag#connect#event ~callback:
            (fun ~origin evt it ->
               let iter = new GText.iter it in
               let start = iter#backward_to_tag_toggle (Some tag) in
               let stop = iter#forward_to_tag_toggle (Some tag) in
               match GdkEvent.get_type evt with
                 | `BUTTON_PRESS ->
                     let ev = GdkEvent.Button.cast evt in
                     if (GdkEvent.Button.button ev) <> 3 then false else begin
                       let ctxt_menu = GMenu.menu () in
                       let factory = new GMenu.factory ctxt_menu in
                       List.iter
                         (fun (text,cmd) -> ignore (factory#add_item text ~callback:(sel_cb cmd)))
                         menu_content;
                       ctxt_menu#popup ~button:3 ~time:(GdkEvent.Button.time ev);
                       true
                     end
                 | `MOTION_NOTIFY ->
                     hover_cb start stop; false
                 | _ -> false))

let mode_tactic sel_cb (proof : #GText.view_skel) goals ~unfoc_goals hints = match goals with
  | [] -> assert false
  | { Interface.goal_hyp = hyps; Interface.goal_ccl = cur_goal; } :: rem_goals ->
      let on_hover sel_start sel_stop =
        proof#buffer#remove_tag
          ~start:proof#buffer#start_iter
          ~stop:sel_start
          Tags.Proof.highlight;
        proof#buffer#remove_tag
          ~start:sel_stop
          ~stop:proof#buffer#end_iter
          Tags.Proof.highlight;
        proof#buffer#apply_tag ~start:sel_start ~stop:sel_stop Tags.Proof.highlight
      in
      let goals_cnt = List.length rem_goals + 1 in
      let head_str = Printf.sprintf
        "%d subgoal%s\n" goals_cnt (if 1 < goals_cnt then "s" else "")
      in
      let goal_str ?(shownum=false) index total =
        if shownum then Printf.sprintf
                          "______________________________________(%d/%d)\n" index total
        else Printf.sprintf
               "______________________________________\n"
      in
      (* Insert current goal and its hypotheses *)
      let hyps_hints, goal_hints = match hints with
      | None -> [], []
      | Some (hl, h) -> (hl, h)
      in
      let width = Ideutils.textview_width proof in
      let rec insert_hyp hints hs = match hs with
      | [] -> ()
      | hyp :: hs ->
        let tags, rem_hints = match hints with
        | [] -> [], []
        | hint :: hints ->
          let tag = proof#buffer#create_tag [] in
          let () = hook_tag_cb tag hint sel_cb on_hover in
          [tag], hints
        in
        let () = insert_xml ~tags proof#buffer (Richpp.richpp_of_pp width hyp) in
        proof#buffer#insert "\n";
        insert_hyp rem_hints hs
      in
      let () = proof#buffer#insert head_str in
      let () = insert_hyp hyps_hints hyps in
      let () =
        let _ = if goal_hints <> [] then
          let tag = proof#buffer#create_tag [] in
          let () = hook_tag_cb tag goal_hints sel_cb on_hover in
          [tag]
          else []
        in
        proof#buffer#insert (goal_str ~shownum:true 1 goals_cnt);
        insert_xml ~tags:[Tags.Proof.goal] proof#buffer (Richpp.richpp_of_pp width cur_goal);
        proof#buffer#insert "\n"
      in
      (* Insert remaining goals (no hypotheses) *)
      let fold_goal ?(shownum=false) i _ { Interface.goal_ccl = g } =
        proof#buffer#insert (goal_str ~shownum i goals_cnt);
        insert_xml proof#buffer (Richpp.richpp_of_pp width g);
        proof#buffer#insert "\n"
      in
      let () = Util.List.fold_left_i (fold_goal ~shownum:true) 2 () rem_goals in
      (* show unfocused goal if option set *)
      (* Insert remaining goals (no hypotheses) *)
      if Coq.PrintOpt.printing_unfocused () then
        begin
          ignore(proof#buffer#place_cursor ~where:(proof#buffer#end_iter));
          let unfoc = List.flatten (List.rev (List.map (fun (x,y) -> x@y) unfoc_goals)) in
          if unfoc<>[] then
            begin
              proof#buffer#insert "\nUnfocused Goals:\n";
              Util.List.fold_left_i (fold_goal ~shownum:false) 0 () unfoc
            end
        end;
      ignore(proof#buffer#place_cursor
               ~where:(proof#buffer#end_iter#backward_to_tag_toggle
                         (Some Tags.Proof.goal)));
      ignore(proof#scroll_to_mark `INSERT)

let rec flatten = function
| [] -> []
| (lg, rg) :: l ->
  let inner = flatten l in
  List.rev_append lg inner @ rg

let display mode (view : #GText.view_skel) goals hints evars =
  let () = view#buffer#set_text "" in
  let width = Ideutils.textview_width view in
  match goals with
  | None -> ()
    (* No proof in progress *)
  | Some { Interface.fg_goals = []; bg_goals = bg; shelved_goals; given_up_goals; } ->
    let bg = flatten (List.rev bg) in
    let evars = match evars with None -> [] | Some evs -> evs in
    begin match (bg, shelved_goals,given_up_goals, evars) with
    | [], [], [], [] ->
      view#buffer#insert "No more subgoals."
    | [], [], [], _ :: _ ->
      (* A proof has been finished, but not concluded *)
      view#buffer#insert "No more subgoals, but there are non-instantiated existential variables:\n\n";
      let iter evar =
        let msg = Printf.sprintf "%s\n" evar.Interface.evar_info in
        view#buffer#insert msg
      in
      List.iter iter evars;
      view#buffer#insert "\nYou can use Grab Existential Variables."
    | [], [], _, _ ->
      (* The proof is finished, with the exception of given up goals. *)
      view#buffer#insert "No more subgoals, but there are some goals you gave up:\n\n";
      let iter goal =
        insert_xml view#buffer (Richpp.richpp_of_pp width goal.Interface.goal_ccl);
        view#buffer#insert "\n"
      in
      List.iter iter given_up_goals;
      view#buffer#insert "\nYou need to go back and solve them."
    | [], _, _, _ ->
      (* All the goals have been resolved but those on the shelf. *)
      view#buffer#insert "All the remaining goals are on the shelf:\n\n";
      let iter goal =
        insert_xml view#buffer (Richpp.richpp_of_pp width goal.Interface.goal_ccl);
        view#buffer#insert "\n"
      in
      List.iter iter shelved_goals
    | _, _, _, _ ->
      (* No foreground proofs, but still unfocused ones *)
      let total = List.length bg in
      let goal_str index = Printf.sprintf
        "______________________________________(%d/%d)\n" index total
      in
      view#buffer#insert "This subproof is complete, but there are some unfocused goals:\n\n";
      let iter i goal =
        let () = view#buffer#insert (goal_str (succ i)) in
        insert_xml view#buffer (Richpp.richpp_of_pp width goal.Interface.goal_ccl);
        view#buffer#insert "\n"
      in
      List.iteri iter bg
    end
  | Some { Interface.fg_goals = fg; bg_goals = bg } ->
    mode view fg ~unfoc_goals:bg hints


let proof_view () =
  let buffer = GSourceView2.source_buffer
    ~highlight_matching_brackets:true
    ~tag_table:Tags.Proof.table ()
  in
  let text_buffer = new GText.buffer buffer#as_buffer in
  let view = GSourceView2.source_view
    ~source_buffer:buffer ~editable:false ~wrap_mode:`WORD ()
  in
  let () = Gtk_parsing.fix_double_click view in
  let default_clipboard = GData.clipboard Gdk.Atom.primary in
  let _ = buffer#add_selection_clipboard default_clipboard in
  let cb clr = view#misc#modify_base [`NORMAL, `NAME clr] in
  let _ = background_color#connect#changed ~callback:cb in
  let _ = view#misc#connect#realize ~callback:(fun () -> cb background_color#get) in
  let cb ft = view#misc#modify_font (Pango.Font.from_string ft) in
  stick text_font view cb;

  let pf = object
    inherit GObj.widget view#as_widget
    val mutable goals = None
    val mutable evars = None
    val mutable last_width = -1

    method buffer = text_buffer

    method clear () = buffer#set_text ""

    method set_goals gls = goals <- gls

    method set_evars evs = evars <- evs

    method refresh ~force =
      (* We need to block updates here due to the following race:
         insertion of messages may create a vertical scrollbar, this
         will trigger a width change, calling refresh again and
         going into an infinite loop. *)
      let width = Ideutils.textview_width view  in
      (* Could still this method race if the scrollbar changes the
         textview_width ?? *)
      let needed = force || last_width <> width in
      if needed then begin
        last_width <- width;
        let dummy _ () = () in
        display (mode_tactic dummy) view goals None evars
      end
  end
  in
  (* Is there a better way to connect the signal ? *)
  (* Can this be done in the object constructor? *)
  let w_cb _ = pf#refresh ~force:false in
  ignore (view#misc#connect#size_allocate ~callback:w_cb);
  pf
