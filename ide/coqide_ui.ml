let ui_m = GAction.ui_manager ();;

let no_under = Util.String.map (fun x -> if x = '_' then '-' else x)

let list_items menu li =
  let res_buf = Buffer.create 500 in
  let tactic_item = function
    |[] -> Buffer.create 1
    |[s] -> let b = Buffer.create 16 in
	    let () = Buffer.add_string b ("<menuitem action='"^menu^" "^(no_under s)^"' />\n") in
	    b
    |s::_ as l -> let b = Buffer.create 50 in
		  let () = (Buffer.add_string b ("<menu action='"^menu^" "^(String.make 1 s.[0])^"'>\n")) in
		  let () = (List.iter
			     (fun x -> Buffer.add_string b ("<menuitem action='"^menu^" "^(no_under x)^"' />\n")) l) in
		  let () = Buffer.add_string b"</menu>\n" in
		  b in
  let () = List.iter (fun b -> Buffer.add_buffer res_buf (tactic_item b)) li in
  res_buf

let list_queries menu li =
  let res_buf = Buffer.create 500 in
  let query_item (q, _) =
    let s = "<menuitem action='"^menu^" "^(no_under q)^"' />\n" in
    Buffer.add_string res_buf s
  in
  let () = List.iter query_item li in
  res_buf

let init () =
  let theui = Printf.sprintf "<ui>\
\n<menubar name='CoqIde MenuBar'>\
\n  <menu action='File'>\
\n    <menuitem action='New' />\
\n    <menuitem action='Open' />\
\n    <menuitem action='Save' />\
\n    <menuitem action='Save as' />\
\n    <menuitem action='Save all' />\
\n    <menuitem action='Revert all buffers' />\
\n    <menuitem action='Close buffer' />\
\n    <menuitem action='Print...' />\
\n    <menu action='Export to'>\
\n      <menuitem action='Html' />\
\n      <menuitem action='Latex' />\
\n      <menuitem action='Dvi' />\
\n      <menuitem action='Pdf' />\
\n      <menuitem action='Ps' />\
\n    </menu>\
\n    <menuitem action='Rehighlight' />\
\n    %s\
\n  </menu>\
\n  <menu name='Edit' action='Edit'>\
\n    <menuitem action='Undo' />\
\n    <menuitem action='Redo' />\
\n    <separator />\
\n    <menuitem action='Cut' />\
\n    <menuitem action='Copy' />\
\n    <menuitem action='Paste' />\
\n    <separator />\
\n    <menuitem action='Find' />\
\n    <menuitem action='Find Next' />\
\n    <menuitem action='Find Previous' />\
\n    <separator />\
\n    <menuitem action='External editor' />\
\n    <separator />\
\n    <menuitem name='Prefs' action='Preferences' />\
\n  </menu>\
\n  <menu name='View' action='View'>\
\n    <menuitem action='Previous tab' />\
\n    <menuitem action='Next tab' />\
\n    <separator/>\
\n    <menuitem action='Zoom in' />\
\n    <menuitem action='Zoom out' />\
\n    <menuitem action='Zoom fit' />\
\n    <separator/>\
\n    <menuitem action='Show Toolbar' />\
\n    <menuitem action='Query Pane' />\
\n    <separator/>\
\n    <menuitem action='Display implicit arguments' />\
\n    <menuitem action='Display coercions' />\
\n    <menuitem action='Display raw matching expressions' />\
\n    <menuitem action='Display notations' />\
\n    <menuitem action='Display all basic low-level contents' />\
\n    <menuitem action='Display existential variable instances' />\
\n    <menuitem action='Display universe levels' />\
\n    <menuitem action='Display all low-level contents' />\
\n    <menuitem action='Display unfocused goals' />\
\n    <separator/>\
\n    <menuitem action='Unset diff' />\
\n    <menuitem action='Set diff' />\
\n    <menuitem action='Set removed diff' />\
\n  </menu>\
\n  <menu action='Navigation'>\
\n    <menuitem action='Forward' />\
\n    <menuitem action='Backward' />\
\n    <menuitem action='Go to' />\
\n    <menuitem action='Start' />\
\n    <menuitem action='End' />\
\n    <menuitem action='Interrupt' />\
\n    <menuitem action='Previous' />\
\n    <menuitem action='Next' />\
\n  </menu>\
\n  <menu action='Try Tactics'>\
\n    <menuitem action='auto' />\
\n    <menuitem action='auto with *' />\
\n    <menuitem action='eauto' />\
\n    <menuitem action='eauto with *' />\
\n    <menuitem action='intuition' />\
\n    <menuitem action='omega' />\
\n    <menuitem action='simpl' />\
\n    <menuitem action='tauto' />\
\n    <menuitem action='trivial' />\
\n    <menuitem action='Wizard' />\
\n    <separator />\
\n    %s\
\n  </menu>\
\n  <menu action='Templates'>\
\n    <menuitem action='Lemma' />\
\n    <menuitem action='Theorem' />\
\n    <menuitem action='Definition' />\
\n    <menuitem action='Inductive' />\
\n    <menuitem action='Fixpoint' />\
\n    <menuitem action='Scheme' />\
\n    <menuitem action='match' />\
\n    <separator />\
\n    %s\
\n  </menu>\
\n  <menu action='Queries'>\
\n    <menuitem action='Search' />\
\n    <menuitem action='Check' />\
\n    <menuitem action='Print' />\
\n    <menuitem action='About' />\
\n    <menuitem action='Locate' />\
\n    <menuitem action='Print Assumptions' />\
\n    <separator />\
\n    %s\
\n  </menu>\
\n  <menu name='Tools' action='Tools'>\
\n    <menuitem action='Comment' />\
\n    <menuitem action='Uncomment' />\
\n    <separator />\
\n    <menuitem action='Coqtop arguments' />\
\n  </menu>\
\n  <menu action='Compile'>\
\n    <menuitem action='Compile buffer' />\
\n    <menuitem action='Make' />\
\n    <menuitem action='Next error' />\
\n    <menuitem action='Make makefile' />\
\n  </menu>\
\n  <menu action='Windows'>\
\n    <menuitem action='Detach View' />\
\n  </menu>\
\n  <menu name='Help' action='Help'>\
\n    <menuitem action='Browse Coq Manual' />\
\n    <menuitem action='Browse Coq Library' />\
\n    <menuitem action='Help for keyword' />\
\n    <menuitem action='Help for μPG mode' />\
\n    <separator />\
\n    <menuitem name='Abt' action='About Coq' />\
\n  </menu>\
\n</menubar>\
\n<toolbar name='CoqIde ToolBar'>\
\n  <toolitem action='Save' />\
\n  <toolitem action='Close buffer' />\
\n  <toolitem action='Forward' />\
\n  <toolitem action='Backward' />\
\n  <toolitem action='Go to' />\
\n  <toolitem action='Start' />\
\n  <toolitem action='End' />\
\n  <toolitem action='Force' />\
\n  <toolitem action='Interrupt' />\
\n  <toolitem action='Previous' />\
\n  <toolitem action='Next' />\
\n  <toolitem action='Wizard' />\
\n</toolbar>\
\n</ui>"
    (if Coq_config.gtk_platform <> `QUARTZ then "<menuitem action='Quit' />" else "")
    (Buffer.contents (list_items "Tactic" Coq_commands.tactics))
    (Buffer.contents (list_items "Template" Coq_commands.commands))
    (Buffer.contents (list_queries "User-Query" Preferences.user_queries#get))
 in
  ignore (ui_m#add_ui_from_string theui);
