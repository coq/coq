(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This module was initially based on the small configwin library (package lablgtk3-extras). *)

open Preferences

(** Types and functions to generate a dialog with tabs organized in a tree *)

type pref_box = {
  label: string;
  box: GPack.box;
  apply: unit -> unit;
}

type pref_section = {
  label: string;
  icon: GtkStock.id option;
  sections: pref_box list;
  children: pref_section list;
}

type pref_widget = { widget: GObj.widget; apply: unit -> unit }

let pref_section label ?icon ?(children = []) sections =
  { label; icon; sections; children }

let create_preferences_box pref_struct current_section =
  let main_box = GPack.hbox () in

  let columns = new GTree.column_list in
  let icon_col = columns#add GtkStock.conv
  and label_col = columns#add Gobject.Data.string
  and box_col = columns#add Gobject.Data.caml in
  columns#lock ();

  let pane = GPack.paned `HORIZONTAL ~packing:main_box#add () in

  (* Tree view part *)
  let scroll = GBin.scrolled_window ~hpolicy:`NEVER ~packing:pane#pack1 ()
  and tree = GTree.tree_store columns in
  let view = GTree.view ~model:tree ~headers_visible:false ~packing:scroll#add_with_viewport () in
  let selection = view#selection in
  selection#set_mode `SINGLE;

  let menu_box = GPack.vbox ~packing:pane#pack2 () in

  let renderer = (GTree.cell_renderer_pixbuf [], ["stock-id", icon_col]) in
  let col = GTree.view_column ~renderer () in
  let _ = view#append_column col in

  let renderer = (GTree.cell_renderer_text [], ["text", label_col]) in
  let col = GTree.view_column ~renderer () in
  let _ = view#append_column col in

  let make_section (main_box : #GPack.box) { label; box; apply } =
    let wf = GBin.frame ~label () in
    box#set_border_width 4;
    wf#add box#coerce;
    let widget = wf#coerce in
    main_box#pack ~expand:true ~padding:2 widget;
    { widget; apply }
  in

  (* Populate the tree *)
  let rec make_tree ?parent { label; icon; sections; children } =
    (* box is not shown at first *)
    let box = GPack.vbox ~packing:(menu_box#pack ~expand:true) ~show:false () in
    box#set_margin_left 4;
    let section_widgets = List.map (make_section box) sections in
    let box_widget = {
      widget = box#coerce;
      apply = fun () -> List.iter (fun { apply } -> apply ()) section_widgets;
    } in
    let new_iter = tree#append ?parent () in
    Option.iter (tree#set ~row:new_iter ~column:icon_col) icon;
    (* Indent labels that are below the top-level *)
    let label = if parent <> None then "  " ^ label else label in
    tree#set ~row:new_iter ~column:label_col label;
    tree#set ~row:new_iter ~column:box_col box_widget;
    List.iter (make_tree ~parent:new_iter) children;
  in

  List.iter make_tree pref_struct;

  (* Dealing with signals *)
  let current_widget : GObj.widget option ref = ref None in

  let select_path path =
    Option.iter (fun widget -> widget#misc#hide ()) !current_widget;
    current_section := Some (GTree.Path.get_indices path);
    let { widget } = tree#get ~row:(tree#get_iter path) ~column:box_col in
    widget#misc#show ();
    current_widget := Some widget;
  in

  let when_selected () =
    match selection#get_selected_rows with
    | row :: _ -> select_path row
    | _ -> ()
  in

  (* Focus on a box when selected *)
  let _ = selection#connect#changed ~callback:when_selected in

  view#expand_all ();
  Option.iter (fun path ->
      selection#select_path (GTree.Path.create (Array.to_list path));
    ) !current_section;

  {
    widget = (main_box :> GObj.widget);
    apply = fun () ->
      let foreach _ iter =
        let { apply } = tree#get ~row:iter ~column:box_col in
        apply ();
        false
      in
      tree#foreach foreach;
  }

let edit_preferences
    ?(apply = fun () -> ())
    ?parent ?width ?height ?(current_section = ref None)
    title pref_struct =
  let dialog = GWindow.dialog
    ~position:`CENTER
    ~modal:true ~title
    ~type_hint:`DIALOG
    ?parent ?height ?width
    ()
  in
  let preferences_box = create_preferences_box pref_struct current_section in

  dialog#vbox#pack ~expand:true preferences_box.widget#coerce;

  dialog#add_button_stock `APPLY `APPLY;
  dialog#add_button_stock `OK `OK;
  dialog#add_button_stock `CANCEL `CANCEL;

  let apply () =
    preferences_box.apply ();
    apply ();
  in

  let rec iter rep =
    try
      match dialog#run () with
        | `APPLY  -> apply (); iter true
        | `OK -> apply (); dialog#destroy (); true
        | _ -> dialog#destroy (); rep
    with exc ->
      GToolbox.message_box ~title:"Error"
          (match exc with Failure str -> str | _ -> Printexc.to_string exc);
      iter rep
  in
  iter false

(** Generic types and functions for preference controls *)

type pref_ui_specific_info =
| PBool of { pref: bool preference }
| PInt of { min: int; max: int; pref: int preference }
| PTextExpr of { initial: string; set: (string -> unit) }
| PCombo of { values: string list; editable: bool; initial: string; set: (int -> string -> unit) }
| PModifiers of {
    allowed_mods: Gdk.Tags.modifier list;
    registerer: ((Gdk.Tags.modifier list -> unit) -> unit) option;
    callback: (Gdk.Tags.modifier list -> unit) option;
    pref: string preference
  }

type pref_ui_info = {
  text: string;
  tooltip: string option;
  specific: pref_ui_specific_info;
}

let string_of_modifier = function
  | `CONTROL -> "<ctrl>"
  | `SHIFT -> "<shift>"
  | `META -> select_arch "<meta>" "<cmd>"
  | `MOD1 -> "<alt>"
  | `MOD2 -> "<mod2>"
  | `MOD3 -> "<mod3>"
  | `MOD4 -> "<mod4>"
  | `MOD5 -> "<mod5>"
  | _  -> ""

let all_modifiers = [`CONTROL; `SHIFT; `META; `MOD1; `MOD2; `MOD3; `MOD4; `MOD5]

let rec find_index_opt elem ?(i = 0) = function
  | [] -> None
  | h :: _ when h = elem -> Some i
  | _ :: t -> find_index_opt elem ~i:(succ i) t

let pbool text ?tooltip pref = { text; tooltip; specific = PBool { pref } }
let pint text ?tooltip ?(min = 0) ?(max = 999_999_999) pref =
  { text; tooltip; specific = PInt { min; max; pref } }
let ptextexpr text ?tooltip initial set = { text; tooltip; specific = PTextExpr { initial; set } }
let pstring text ?tooltip pref = ptextexpr text ?tooltip pref#get pref#set
let pcombo text ?tooltip values ?(editable = false) initial set =
  { text; tooltip; specific = PCombo { values; editable; initial; set } }
let pstringcombo text ?tooltip values ?(editable = false) pref =
  pcombo text ?tooltip values ~editable pref#get (fun _ s -> pref#set s)
let pmodifiers text ?tooltip allowed_mods ?registerer ?callback pref =
  { text; tooltip; specific = PModifiers { allowed_mods; registerer; callback; pref } }

let create_pref_box ?(in_grid = false) label pref_data =
  let box = GPack.vbox () in
  let apply_list = ref [] in
  let add_row =
    let create_label pref_data packing =
      if pref_data.text <> "" then
        let label = GMisc.label ~text:pref_data.text ~packing () in
        label#set_halign `START;
        Option.iter label#set_tooltip_text pref_data.tooltip;
    in
    if in_grid then
      let grid = GPack.grid ~col_spacings:4 ~packing:box#pack () in
      (fun pref_data index ->
        create_label pref_data (grid#attach ~left:0 ~top:index);
        ((grid#attach ~left:1 ~top:index) : (GObj.widget -> unit)))
    else
      (fun pref_data _ ->
        let box = GPack.hbox ~packing:box#pack () in
        create_label pref_data box#pack;
        (box#pack : (GObj.widget -> unit)))
  in
  let add_param index pref_data =
    let setup_input ?(expand = false) input =
      if not in_grid && pref_data.text <> "" then
        input#set_margin_left 4;
      Option.iter input#set_tooltip_text pref_data.tooltip;
      input#set_hexpand expand;
    in
    match pref_data.specific with
    | PBool { pref } ->
        let input = GButton.check_button ~label:pref_data.text ~active:pref#get ~packing:box#pack () in
        apply_list := (fun () -> pref#set input#active) :: !apply_list;
    | PInt { min; max; pref } ->
        let packing = add_row pref_data index in
        let input = GEdit.spin_button
          ~numeric:true ~update_policy:`IF_VALID ~digits:0
          ~packing ()
        in
        setup_input input;
        let lower = float_of_int min and upper = float_of_int max in
        input#adjustment#set_bounds ~lower ~upper ~step_incr:1. ();
        input#set_value (float_of_int pref#get);
        apply_list := (fun () -> pref#set input#value_as_int) :: !apply_list;
    | PTextExpr { initial; set } ->
        let packing = add_row pref_data index in
        let input = GEdit.entry ~text:initial ~packing () in
        setup_input ~expand:true input;
        apply_list := (fun () -> set input#text) :: !apply_list;
    | PCombo { values; editable; initial; set } when editable ->
        let packing = add_row pref_data index in
        let input, _ = GEdit.combo_box_entry_text ~strings:values ~packing () in
        input#entry#set_editable true;
        input#entry#set_text initial;
        setup_input ~expand:true input;
        apply_list := (fun () -> set input#active input#entry#text) :: !apply_list;
    | PCombo { values; editable; initial; set } ->
        let packing = add_row pref_data index in
        let input, _ = GEdit.combo_box_text ~strings:values ?active:(find_index_opt initial values) ~packing () in
        setup_input input;
        let values = Array.of_list values in
        apply_list := (fun () -> set input#active values.(input#active)) :: !apply_list;
    | PModifiers { allowed_mods; registerer; callback; pref } ->
        let packing = add_row pref_data index in
        let hbox = GPack.hbox ~packing () in
        setup_input hbox;
        let filter_mods allowed = List.filter (fun modifier -> List.mem modifier allowed) in
        let value = ref (filter_mods allowed_mods (str_to_mod_list pref#get)) in
        let create_button modifier =
          let but = GButton.toggle_button
            ~label:(string_of_modifier modifier)
            ~active:(List.mem modifier !value)
            ~packing:hbox#pack () in
          ignore (but#connect#toggled ~callback:(fun () ->
              if but#active then (
                value := str_to_mod_list (mod_list_to_str (modifier :: !value));
              ) else value := List.filter ((<>) modifier) !value;
              Option.iter (fun callback -> callback !value) callback;
            ));
          apply_list := (fun () -> pref#set (mod_list_to_str !value)) :: !apply_list;
        in
        List.iter create_button allowed_mods;
        Option.iter (fun registerer ->
            registerer (fun allowed_mods ->
              List.iter hbox#remove hbox#children;
              value := filter_mods allowed_mods !value;
              List.iter create_button allowed_mods;
            );
          ) registerer;
  in
  List.iteri add_param pref_data;
  { label; box; apply = fun () -> List.iter (fun apply -> apply ()) !apply_list }

class tag_button (box : Gtk.box Gtk.obj) =
object (self)

  inherit GObj.widget box

  val fg_color = GButton.color_button ()
  val fg_unset = GButton.toggle_button ()
  val bg_color = GButton.color_button ()
  val bg_unset = GButton.toggle_button ()
  val bold = GButton.toggle_button ()
  val italic = GButton.toggle_button ()
  val underline = GButton.toggle_button ()
  val strikethrough = GButton.toggle_button ()

  method set_tag tag =
    let track c but set = match c with
    | None -> set#set_active true
    | Some c ->
      set#set_active false;
      but#set_color (Gdk.Color.color_parse c)
    in
    track tag.tag_bg_color bg_color bg_unset;
    track tag.tag_fg_color fg_color fg_unset;
    bold#set_active tag.tag_bold;
    italic#set_active tag.tag_italic;
    underline#set_active tag.tag_underline;
    strikethrough#set_active tag.tag_strikethrough;

  method tag =
    let get but set =
      if set#active then None
      else Some (Gdk.Color.color_to_string but#color)
    in
    {
      tag_bg_color = get bg_color bg_unset;
      tag_fg_color = get fg_color fg_unset;
      tag_bold = bold#active;
      tag_italic = italic#active;
      tag_underline = underline#active;
      tag_strikethrough = strikethrough#active;
    }

  initializer
    let box = new GPack.box box in
    let set_stock button stock =
      let stock = GMisc.image ~stock ~icon_size:`BUTTON () in
      button#set_image stock#coerce
    in
    let bprops button ?stock tooltip =
      (button :> GButton.button_skel), stock, tooltip
    in
    List.iter (fun (button, stock, tooltip) ->
        Option.iter (set_stock button) stock;
        button#set_tooltip_text tooltip;
        box#pack button#coerce;
      ) [
        bprops fg_color "Foreground color";
        bprops fg_unset ~stock:`CANCEL "Disable foreground color";
        bprops bg_color "Background color";
        bprops bg_unset ~stock:`CANCEL "Disable background color";
        bprops bold ~stock:`BOLD "Bold";
        bprops italic ~stock:`ITALIC "Italic";
        bprops underline ~stock:`UNDERLINE "Underline";
        bprops strikethrough ~stock:`STRIKETHROUGH "Strikethrough";
      ];
    let cb but obj = obj#set_sensitive (not but#active) in
    let _ = fg_unset#connect#toggled ~callback:(fun () -> cb fg_unset fg_color#misc) in
    let _ = bg_unset#connect#toggled ~callback:(fun () -> cb bg_unset bg_color#misc) in
    ()

end

let tag_button () =
  let box = GPack.hbox () in
  new tag_button (Gobject.unsafe_cast box#as_widget)

let current_section = ref None

let configure ?(apply = fun () -> ()) parent =
  let file_format =
    create_pref_box ~in_grid:true "File format" [
      pcombo "File charset encoding:" ~editable:true
        ("UTF-8" :: "LOCALE" :: match encoding#get with Emanual s -> [s] | _ -> [])
        (encoding#repr#raw_from encoding#get)
        (fun _ s -> encoding#set (encoding#repr#raw_into s));
      let values = [`DEFAULT; `UNIX; `WINDOWS] in
      let labels = ["Default"; {|Linux (\n)|}; {|Windows (\r\n)|}] in
      pcombo "EOL character:" labels
        (List.nth labels (match find_index_opt line_ending#get values with Some i -> i | _ -> 0))
        (fun i _ -> line_ending#set (List.nth values i));
    ]
  in
  let global_auto_reload =
    create_pref_box "Global auto reload" [
      pbool "Enable" global_auto_reload;
      pint "Delay (ms):" global_auto_reload_delay;
    ]
  in
  let auto_save =
    create_pref_box "Auto save" [
      pbool "Enable" auto_save;
      pint "Delay (ms):" auto_save_delay;
    ]
  in

  let project_management =
    create_pref_box "Project management" [
        pstring "Default name for project file:" project_file_name;
        pcombo "Project file options are"
          (List.map read_project#repr#raw_from [Subst_args; Append_args; Ignore_args])
          (read_project#repr#raw_from read_project#get)
          (fun _ s -> read_project#set (read_project#repr#raw_into s));
      ];
  in

  let editor_appearance =
    create_pref_box "Editor appearance" [
        pbool "Dynamic word wrap" dynamic_word_wrap;
        pbool "Show line number" show_line_number;
        pbool "Highlight current line" highlight_current_line;
        pbool "Show right margin" show_right_margin;
        pbool "Show spaces" show_spaces;
        pbool "Show progress bar" show_progress_bar;
      ]
  in
  let editor_behavior =
    create_pref_box "Editor behavior" [
        pbool "Auto indentation" auto_indent;
        pbool "Insert spaces instead of tabs" spaces_instead_of_tabs;
        pbool "Unicode binding completion" unicode_binding;
        pbool "Auto completion" auto_complete;
        pint "Delay (ms):" ~max:5000 auto_complete_delay;
        pbool "Emacs/PG keybindings (μPG mode)" microPG;
      ]
  in

  let config_window =
    create_pref_box ~in_grid:true "Window" [
      pint "Width at startup:" window_width;
      pint "Height at startup:" window_height;
    ]
  in
  let config_document_tabs =
    create_pref_box "Document tabs" [
        let positions = ["top"; "left"; "right"; "bottom"] in
        let labels = ["Top"; "Left"; "Right"; "Bottom"] in
        let initial = List.nth labels
            (match find_index_opt document_tabs_pos#get positions with Some i -> i | _ -> 0) in
        let setter i _ = document_tabs_pos#set (List.nth positions i) in
        pcombo "Position:" labels initial setter;
      ]
  in

  let config_font =
    let preview_text = "Goal (∃n : nat, n ≤ 0)∧(∀x,y,z, x∈y⋃z↔x∈y∨x∈z)." in
    if Coq_config.arch <> "Darwin" then begin
      let box = GPack.hbox () in
      let font_sel = GMisc.font_selection ~preview_text:preview_text () in
      let realized = ref false in (* The font selector does not allow setting its font before it is realized (bug) *)
      box#pack ~expand:true font_sel#coerce;
      let _ = font_sel#misc#connect#realize
                ~callback:(fun () -> font_sel#set_font_name text_font#get; realized := true;) in
      { label = "Text font"; box; apply = (fun () -> if !realized then text_font#set font_sel#font_name;) }
    end else begin
      (* For Darwin: a poor man's font selection. Work around #16136, which is ultimately a GTK bug. *)
      let box = GPack.vbox () in
      box#set_height_request 200;
      box#set_height_request 300;
      let font_sel = GEdit.entry ~text:text_font#get () in
      box#pack ~expand:false font_sel#coerce;
      let text = GMisc.label ~text:preview_text () in
      text#set_ypad 10;
      box#pack ~expand:false text#coerce;
      let set_font () =
        let fd = GPango.font_description_from_string font_sel#text in
        text_font#set fd#to_string;
        text#misc#modify_font_by_name fd#to_string;
        font_sel#set_text fd#to_string;
      in
      text#misc#modify_font_by_name text_font#get;
      let _ = font_sel#connect#activate ~callback:set_font in
      { label = "Text font"; box; apply = set_font }
    end
  in

  let config_highlight =
    let source_param text ids elem_get pref =
      let id_to_name id =
        match elem_get id with
        | Some elem -> elem#name
        | None -> id
      in
      let names = List.map id_to_name ids in
      let ids = Array.of_list ids in
      pcombo text names (id_to_name pref#get) (fun i _ -> pref#set ids.(i))
    in
    create_pref_box ~in_grid:true "Highlight configuration" [
        source_param "Style scheme:" style_manager#style_scheme_ids
          style_manager#style_scheme source_style;
        source_param "Language:"
          (List.filter (CString.is_prefix "coq") lang_manager#language_ids)
          lang_manager#language source_language;
      ]
  in
  let config_color =
    let box = GPack.vbox () in
    let grid = GPack.grid
      ~row_spacings:5
      ~col_spacings:5
      ~border_width:4
      ~packing:(box#pack ~expand:true) ()
    in
    let reset_button = GButton.button ~label:"Reset" ~packing:box#pack () in
    let apply_list = ref [] in
    let _ =
      GMisc.label ~text:"Background" ~packing:(grid#attach ~left:1 ~top: 0) (),
      GMisc.label ~text:"Foreground" ~packing:(grid#attach ~left:2 ~top: 0) ()
    in
    let iter i (text, prefs) =
      let top = i + 1 in
      (GMisc.label ~text ~packing:(grid#attach ~left:0 ~top) ())#set_halign `START;
      List.iteri (fun i pref ->
        let button = GButton.color_button
          ~color:(Gdk.Color.color_parse pref#get)
          ~packing:(grid#attach ~left:(i + 1) ~top) ()
        in
        apply_list := (fun () -> pref#set (Gdk.Color.color_to_string button#color)) :: !apply_list;
        let _ = reset_button#connect#clicked ~callback:(fun () ->
            pref#reset ();
            button#set_color (Gdk.Color.color_parse pref#get);
          )
        in
        ()) prefs;
    in
    let () = Util.List.iteri iter [
      "Processed text", [processed_color];
      "Text being processed", [processing_color];
      "Incompletely processed Qed", [incompletely_processed_color];
      "Unjustified conclusions", [unjustified_conclusion_color];
      "Breakpoints", [breakpoint_color];
      "Debugger stopping point", [db_stopping_point_color];
      "Errors", [error_color; error_fg_color];
    ] in
    let label = "Color configuration" in
    { label; box; apply = fun () -> List.iter (fun apply -> apply ()) !apply_list }
  in

  let config_tags =
    let box = GPack.vbox () in
    let scroll = GBin.scrolled_window
      ~hpolicy:`NEVER
      ~vpolicy:`AUTOMATIC
      ~packing:(box#pack ~expand:true)
      ()
    in
    let grid = GPack.grid
      ~row_spacings:5
      ~col_spacings:5
      ~border_width:2
      ~packing:scroll#add_with_viewport ()
    in
    let i = ref 0 in
    let cb = ref [] in
    let iter text tag =
      (GMisc.label ~text ~packing:(grid#attach ~left:0 ~top:!i) ())#set_halign `START;
      let button = tag_button () in
      let callback () = tag#set button#tag in
      button#set_tag tag#get;
      grid#attach ~left:1 ~top:!i button#coerce;
      incr i;
      cb := callback :: !cb;
    in
    Util.String.Map.iter iter (list_tags ());
    let label = "Tag configuration" in
    let callback () = List.iter (fun f -> f ()) !cb in
    { label; box; apply = callback }
  in

  let modifiers_valid_callbacks = ref [] in
  let modifiers_reg callback =
    modifiers_valid_callbacks := callback :: !modifiers_valid_callbacks
  in
  let allowed_mods = str_to_mod_list modifiers_valid#get in
  let modifiers_valid =
    create_pref_box "Allowed modifiers" [
        pmodifiers "" all_modifiers ~callback:(fun value ->
            List.iter (fun callback -> callback value) !modifiers_valid_callbacks;
          ) modifiers_valid;
      ]
  in
  let config_modifiers =
    create_pref_box ~in_grid:true "Modifiers for menu item shortcuts" [
        pmodifiers "View:" allowed_mods ~registerer:modifiers_reg modifier_for_display;
        pmodifiers "Navigation:" allowed_mods ~registerer:modifiers_reg modifier_for_navigation;
        pmodifiers "Templates:" allowed_mods ~registerer:modifiers_reg modifier_for_templates;
        pmodifiers "Queries:" allowed_mods ~registerer:modifiers_reg modifier_for_queries;
        (* user_queries *)
      ]
  in

  let cmd_editor =
    let predefined = ["gedit %s"; "kate %s"; "emacs %s"; "vi %s"; "notepad %s"; "notepad++ %s"] in
    pstringcombo ~tooltip:"(%s for file name)" "External editor:" ~editable:true
      ((if List.mem cmd_editor#get predefined then [] else [cmd_editor#get]) @ predefined)
      cmd_editor
  in
  let cmd_browse =
    let predefined = [Coq_config.browser; "firefox %s &"; "seamonkey %s &"; "chromium %s &"] in
    pstringcombo ~tooltip:"(%s for url)" "Browser:" ~editable:true
      ((if List.mem cmd_browse#get predefined then [] else [cmd_browse#get]) @ predefined)
      cmd_browse
  in
  let externals_cmds =
    create_pref_box ~in_grid:true "Commands for external programs" [
        ptextexpr "coqidetop:"
          (match cmd_rocqtop#get with | None -> "AUTO" | Some x -> x)
          (fun s -> cmd_rocqtop#set (if s = "AUTO" then None else Some s));
        pstring "coqc:" cmd_rocqc;
        pstring "make:" cmd_make;
        pstring "coqmakefile:" cmd_rocqmakefile;
        pstring "coqdoc:" cmd_rocqdoc;
        pstring "Print ps:" cmd_print;
        cmd_editor;
        cmd_browse;
      ]
  in

  let misc =
    create_pref_box "Miscellaneous" [
        pbool "Stop interpreting before the current point" stop_before;
        pbool "Reset coqtop on tab switch" reset_on_tab_switch;
      ]
  in

(*
  let add_user_query () =
    let input_string l v =
      match GToolbox.input_string ~title:l v with
      | None -> ""
      | Some s -> s
    in
    let q = input_string "User query" "Your query" in
    let k = input_string "Shortcut key" "Shortcut (a single letter)" in
    let q = CString.map (fun c -> if c = '$' then ' ' else c) q in
    (* Anything that is not a simple letter will be ignored. *)
    let k =
      if Int.equal (CString.length k) 1 && Util.is_letter k.[0] then k
      else "" in
    let k = String.uppercase_ascii k in
      [q, k]
  in

  let user_queries =
    list
      ~f:user_queries#set
      (* Disallow same query, key or empty query. *)
      ~eq:(fun (q1, k1) (q2, k2) -> k1 = k2 || q1 = "" || q2 = "" || q1 = q2)
      ~add:add_user_query
      ~titles:["User query"; "Shortcut key"]
      "User queries"
      (fun (q, s) -> [q; s])
      user_queries#get
  in
*)

  let cmds = [
      pref_section "Files" ~icon:`FLOPPY [file_format; global_auto_reload; auto_save] ~children:[
          pref_section "Project" ~icon:`PAGE_SETUP [project_management];
        ];
      pref_section "Editor" ~icon:`EDIT [editor_appearance; editor_behavior];
      pref_section "Appearance" ~icon:`ZOOM_FIT [config_window; config_document_tabs] ~children:[
          pref_section "Font" ~icon:`SELECT_FONT [config_font];
          pref_section "Colors" ~icon:`SELECT_COLOR [config_highlight; config_color];
          pref_section "Tags" ~icon:`SELECT_COLOR [config_tags];
        ];
      pref_section "Shortcuts" ~icon:`MEDIA_FORWARD [modifiers_valid; config_modifiers];
      pref_section "Externals" ~icon:`EXECUTE [externals_cmds];
      pref_section "Misc" ~icon:`PREFERENCES [misc];
    ]
  in

  if edit_preferences ~apply ~parent ~current_section ~width:600 ~height:400 "Preferences" cmds then
    save_pref ()
