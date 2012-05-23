let ui_m = GAction.ui_manager ();;

let no_under = Util.string_map (fun x -> if x = '_' then '-' else x)

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

let init () =
  let theui = Printf.sprintf "<ui>
<accelerator action='Close Find' />
<menubar name='CoqIde MenuBar'>
  <menu action='File'>
    <menuitem action='New' />
    <menuitem action='Open' />
    <menuitem action='Save' />
    <menuitem action='Save as' />
    <menuitem action='Save all' />
    <menuitem action='Revert all buffers' />
    <menuitem action='Close buffer' />
    <menuitem action='Print...' />
    <menu action='Export to'>
      <menuitem action='Html' />
      <menuitem action='Latex' />
      <menuitem action='Dvi' />
      <menuitem action='Pdf' />
      <menuitem action='Ps' />
    </menu>
    <menuitem action='Rehighlight' />
    %s
  </menu>
  <menu name='Edit' action='Edit'>
    <menuitem action='Undo' />
    <menuitem action='Redo' />
    <separator />
    <menuitem action='Cut' />
    <menuitem action='Copy' />
    <menuitem action='Paste' />
    <separator />
    <menuitem action='Find' />
    <menuitem action='Find Next' />
    <menuitem action='Find Previous' />
    <menuitem action='Replace' />
    <menuitem action='Complete Word' />
    <separator />
    <menuitem action='External editor' />
    <separator />
    <menuitem name='Prefs' action='Preferences' />
  </menu>
  <menu name='View' action='View'>
    <menuitem action='Previous tab' />
    <menuitem action='Next tab' />
    <separator/>
    <menuitem action='Show Toolbar' />
    <menuitem action='Show Query Pane' />
    <separator/>
    <menuitem action='Display implicit arguments' />
    <menuitem action='Display coercions' />
    <menuitem action='Display raw matching expressions' />
    <menuitem action='Display notations' />
    <menuitem action='Display all basic low-level contents' />
    <menuitem action='Display existential variable instances' />
    <menuitem action='Display universe levels' />
    <menuitem action='Display all low-level contents' />
  </menu>
  <menu action='Navigation'>
    <menuitem action='Forward' />
    <menuitem action='Backward' />
    <menuitem action='Go to' />
    <menuitem action='Start' />
    <menuitem action='End' />
    <menuitem action='Interrupt' />
    <menuitem action='Previous' />
    <menuitem action='Next' />
  </menu>
  <menu action='Try Tactics'>
    <menuitem action='auto' />
    <menuitem action='auto with *' />
    <menuitem action='eauto' />
    <menuitem action='eauto with *' />
    <menuitem action='intuition' />
    <menuitem action='omega' />
    <menuitem action='simpl' />
    <menuitem action='tauto' />
    <menuitem action='trivial' />
    <menuitem action='Wizard' />
    <separator />
    %s
  </menu>
  <menu action='Templates'>
    <menuitem action='Lemma' />
    <menuitem action='Theorem' />
    <menuitem action='Definition' />
    <menuitem action='Inductive' />
    <menuitem action='Fixpoint' />
    <menuitem action='Scheme' />
    <menuitem action='match' />
    <separator />
    %s
  </menu>
  <menu action='Queries'>
    <menuitem action='SearchAbout' />
    <menuitem action='Check' />
    <menuitem action='Print' />
    <menuitem action='About' />
    <menuitem action='Locate' />
    <menuitem action='Whelp Locate' />
  </menu>
  <menu action='Compile'>
    <menuitem action='Compile buffer' />
    <menuitem action='Make' />
    <menuitem action='Next error' />
    <menuitem action='Make makefile' />
  </menu>
  <menu action='Windows'>
    <menuitem action='Detach View' />
  </menu>
  <menu name='Help' action='Help'>
    <menuitem action='Browse Coq Manual' />
    <menuitem action='Browse Coq Library' />
    <menuitem action='Help for keyword' />
    <separator />
    <menuitem name='Abt' action='About Coq' />
  </menu>
</menubar>
<toolbar name='CoqIde ToolBar'>
  <toolitem action='Save' />
  <toolitem action='Close buffer' />
  <toolitem action='Forward' />
  <toolitem action='Backward' />
  <toolitem action='Go to' />
  <toolitem action='Start' />
  <toolitem action='End' />
  <toolitem action='Interrupt' />
  <toolitem action='Previous' />
  <toolitem action='Next' />
  <toolitem action='Wizard' />
</toolbar>
</ui>"
    (if Coq_config.gtk_platform <> `QUARTZ then "<menuitem action='Quit' />" else "")
    (Buffer.contents (list_items "Tactic" Coq_commands.tactics))
    (Buffer.contents (list_items "Template" Coq_commands.commands))
 in
  ignore (ui_m#add_ui_from_string theui);
