let create l = 
  let hbox = GPack.hbox () in
  let columns = new GTree.column_list in
  let command_col =  columns#add GTree.Data.string in
  let coq_col = columns#add GTree.Data.string in
  let store = GTree.list_store columns
  in 
(* populate the store *)
  let _ = List.iter (fun (x,y) -> 
		       let row = store#append () in
		       store#set ~row ~column:command_col x;
		       store#set ~row ~column:coq_col y)
	    l
  in
  let view = GTree.view ~model:store ~packing:hbox#pack () in
  
  let renderer = GTree.cell_renderer_text () in
  GtkText.Tag.set_property renderer (`EDITABLE true);
  let first = 
    GTree.view_column ~title:"Coq Command to try" 
      ~renderer:(renderer,["text",command_col]) 
      () 
  in ignore (view#append_column first);
  let second = 
    GTree.view_column ~title:"Coq Command to insert" 
      ~renderer:(renderer,["text",coq_col]) 
      () 
  in ignore (view#append_column second);

  let vbox = GPack.button_box `VERTICAL ~packing:hbox#pack () in
  let up = GButton.button ~label:"Up" ~packing:(vbox#pack ~expand:true ~fill:false) () in
  let down = GButton.button ~label:"Down" ~packing:(vbox#pack ~expand:true ~fill:false) () in
  let add = GButton.button ~label:"Add" ~packing:(vbox#pack ~expand:true ~fill:false) () in
  let remove = GButton.button ~label:"Remove" ~packing:(vbox#pack ~expand:true ~fill:false) () in
  hbox

