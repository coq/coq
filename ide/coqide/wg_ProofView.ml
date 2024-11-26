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
open Preferences
open Ideutils

type goals =
| NoGoals
| FocusGoals of { fg : Interface.goal list; bg : Interface.goal list }
| NoFocusGoals of {
  bg : Interface.goal list;
  shelved : Interface.goal list;
  given_up : Interface.goal list;
}

class type proof_view =
  object
    inherit GObj.widget
    method source_buffer : GSourceView3.source_buffer
    method buffer : GText.buffer
    method select_all : unit -> unit
    method refresh : force:bool -> unit
    method clear : unit -> unit
    method set_goals : goals -> unit
    method set_debug_goal : Pp.t -> unit
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
  | { Interface.goal_hyp = hyps; Interface.goal_ccl = cur_goal; Interface.goal_name = cur_name } :: rem_goals ->
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
        "%d goal%s\n" goals_cnt (if 1 < goals_cnt then "s" else "")
      in
      let goal_str ?(shownum=false) index total name =
        let annot =
          match name with
          | Some id -> Printf.sprintf "(?%s)" id
          | None -> if shownum then Printf.sprintf "(%d/%d)" index total else "" in
        Printf.sprintf "______________________________________%s\n" annot
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
        let () = insert_xml ~tags proof#buffer (Richpp.richpp_of_pp ~width hyp) in
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
        proof#buffer#insert (goal_str ~shownum:true 1 goals_cnt cur_name);
        insert_xml ~tags:[Tags.Proof.goal] proof#buffer (Richpp.richpp_of_pp ~width cur_goal);
        proof#buffer#insert "\n"
      in
      (* Insert remaining goals (no hypotheses) *)
      let fold_goal ?(shownum=false) i _ { Interface.goal_ccl = g; Interface.goal_name = name } =
        proof#buffer#insert (goal_str ~shownum i goals_cnt name);
        insert_xml proof#buffer (Richpp.richpp_of_pp ~width g);
        proof#buffer#insert "\n"
      in
      let () = Util.List.fold_left_i (fold_goal ~shownum:true) 2 () rem_goals in
      (* show unfocused goal if option set *)
      (* Insert remaining goals (no hypotheses) *)
      if RocqDriver.PrintOpt.printing_unfocused () then
        begin
          ignore(proof#buffer#place_cursor ~where:(proof#buffer#end_iter));
          if unfoc_goals<>[] then
            begin
              proof#buffer#insert "\nUnfocused Goals:\n";
              Util.List.fold_left_i (fold_goal ~shownum:false) 0 () unfoc_goals
            end
        end;
      ignore(proof#buffer#place_cursor
               ~where:(proof#buffer#end_iter#backward_to_tag_toggle
                         (Some Tags.Proof.goal)));
      ignore(proof#scroll_to_mark `INSERT)

let display mode (view : #GText.view_skel) goals hints =
  let () = view#buffer#set_text "" in
  let width = Ideutils.textview_width view in
  match goals with
  | NoGoals -> ()
    (* No proof in progress *)
  | FocusGoals { fg; bg } ->
    mode view fg ~unfoc_goals:bg hints
  | NoFocusGoals { bg; shelved; given_up } ->
    begin match (bg, shelved, given_up) with
    | [], [], [] ->
      view#buffer#insert "All goals completed."
    | [], [], _ ->
      (* The proof is finished, with the exception of given up goals. *)
      view#buffer#insert "All goals completed except some admitted goals:\n\n";
      let iter goal =
        insert_xml view#buffer (Richpp.richpp_of_pp ~width goal.Interface.goal_ccl);
        view#buffer#insert "\n"
      in
      List.iter iter given_up;
      view#buffer#insert "\nYou need to go back and solve them."
    | [], _, _ ->
      (* All the goals have been resolved but those on the shelf. *)
      view#buffer#insert "All the remaining goals are on the shelf:\n\n";
      let iter goal =
        insert_xml view#buffer (Richpp.richpp_of_pp ~width goal.Interface.goal_ccl);
        view#buffer#insert "\n"
      in
      List.iter iter shelved
    | _, _, _ ->
      (* No foreground proofs, but still unfocused ones *)
      let total = List.length bg in
      let goal_str index id =
        let annot =
          if Option.has_some (int_of_string_opt id) (* some uid *) then Printf.sprintf "(%d/%d)" index total
          else Printf.sprintf "(?%s)" id in
        Printf.sprintf
               "______________________________________%s\n" annot
      in
      view#buffer#insert "This subproof is complete, but there are some unfocused goals:\n\n";
      let iter i goal =
        let () = view#buffer#insert (goal_str (succ i) goal.Interface.goal_id) in
        insert_xml view#buffer (Richpp.richpp_of_pp ~width goal.Interface.goal_ccl);
        view#buffer#insert "\n"
      in
      List.iteri iter bg
    end


let proof_view () =
  let buffer = GSourceView3.source_buffer
    ~highlight_matching_brackets:true
    ~tag_table:Tags.Proof.table
    ?style_scheme:(style_manager#style_scheme source_style#get) ()
  in
  let text_buffer = new GText.buffer buffer#as_buffer in
  let view = GSourceView3.source_view
    ~source_buffer:buffer ~editable:false ~wrap_mode:`WORD ()
  in
  let () = Gtk_parsing.fix_double_click view in
  let default_clipboard = GData.clipboard Gdk.Atom.primary in
  let _ = buffer#add_selection_clipboard default_clipboard in
(* FIXME: handle this using CSS *)
(*   let cb clr = view#misc#modify_bg [`NORMAL, `NAME clr] in *)
(*   let _ = background_color#connect#changed ~callback:cb in *)
(*   let _ = view#misc#connect#realize ~callback:(fun () -> cb background_color#get) in *)
  let cb ft = view#misc#modify_font (GPango.font_description_from_string ft) in
  stick text_font view cb;

  let pf = object(self)
    inherit GObj.widget view#as_widget
    val mutable goals = NoGoals
    val mutable debug_goal = None
    val mutable last_width = -1

    method source_buffer = buffer

    method buffer = text_buffer

    method select_all () =
      if self#is_focus then
        self#buffer#select_range self#buffer#start_iter self#buffer#end_iter;

    method clear () = buffer#set_text ""

    method set_goals gls = goals <- gls; debug_goal <- None

    method set_debug_goal msg =
      (* Appearance is a bit different from the regular goals display.
         That's probably a feature rather than a bug--it will remind the user
         they're in the debugger. *)
      self#clear ();
      debug_goal <- Some msg;
      let tags = [] in
      let width = Ideutils.textview_width view in
      Ideutils.insert_xml buffer ~tags (Richpp.richpp_of_pp ~width msg);

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
        match debug_goal with
        | None ->
          let dummy _ () = () in
          display (mode_tactic dummy) view goals None
        | Some msg -> self#set_debug_goal msg
      end
  end
  in
  (* Is there a better way to connect the signal ? *)
  (* Can this be done in the object constructor? *)
  let w_cb _ = pf#refresh ~force:false in
  ignore (view#misc#connect#size_allocate ~callback:w_cb);
  pf
