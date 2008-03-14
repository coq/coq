open GTree
open Gobject

let create l = 
  let hbox = GPack.hbox () in
  let scw = GBin.scrolled_window 
	      ~hpolicy:`AUTOMATIC 
	      ~vpolicy:`AUTOMATIC 
	      ~packing:(hbox#pack ~expand:true) () in

  let columns = new GTree.column_list in
  let command_col =  columns#add Data.string in
  let coq_col = columns#add Data.string in
  let store = GTree.list_store columns
  in 

(* populate the store *)
  let _ = List.iter (fun (x,y) -> 
		       let row = store#append () in
		       store#set ~row ~column:command_col x;
		       store#set ~row ~column:coq_col y)
	    l
  in
  let view = GTree.view ~model:store ~packing:scw#add_with_viewport () in

  (* Alternate colors for the rows *)
  view#set_rules_hint true;

  let renderer_comm = GTree.cell_renderer_text [`EDITABLE true]  in
  ignore (renderer_comm#connect#edited 
    ~callback:(fun (path:Gtk.tree_path) (s:string) -> 
		 store#set 
		 ~row:(store#get_iter path) 
		 ~column:command_col s));
  let first = 
    GTree.view_column ~title:"Coq Command to try" 
      ~renderer:(renderer_comm,["text",command_col]) 
      () 
  in ignore (view#append_column first);

  let renderer_coq = GTree.cell_renderer_text [`EDITABLE true] in
  ignore(renderer_coq#connect#edited
	   ~callback:(fun (path:Gtk.tree_path) (s:string) -> 
			store#set 
			~row:(store#get_iter path) 
			~column:coq_col s));
  let second = 
    GTree.view_column ~title:"Coq Command to insert" 
      ~renderer:(renderer_coq,["text",coq_col]) 
      () 
  in ignore (view#append_column second);

  let vbox = GPack.button_box `VERTICAL ~packing:hbox#pack ~layout:`SPREAD () 
  in
  let up = GButton.button  ~stock:`GO_UP ~label:"Up" ~packing:(vbox#pack ~expand:true ~fill:false) () in
  let down = GButton.button 
	       ~stock:`GO_DOWN 
	       ~label:"Down" 
	       ~packing:(vbox#pack ~expand:true ~fill:false) () 
  in
  let add = GButton.button ~stock:`ADD 
	      ~label:"Add" 
	      ~packing:(vbox#pack ~expand:true ~fill:false) 
	      () 
  in
  let remove = GButton.button ~stock:`REMOVE 
		 ~label:"Remove" 
		 ~packing:(vbox#pack ~expand:true ~fill:false) () 
  in

  ignore (add#connect#clicked 
	    ~callback:(fun b ->  
			 let n = store#append () in
			 view#selection#select_iter n));
  ignore (remove#connect#clicked 
	    ~callback:(fun b -> match view#selection#get_selected_rows with 
			 | [] -> ()
			 | path::_ ->
			     let iter = store#get_iter path in
		       	     ignore (store#remove iter);
		      ));
  ignore (up#connect#clicked 
	    ~callback:(fun b ->  
			 match view#selection#get_selected_rows with 
			   | [] -> ()
			   | path::_ ->
			       let iter = store#get_iter path in
			       ignore (GtkTree.TreePath.prev path);
			       let upiter = store#get_iter path in
			       ignore (store#swap iter upiter);
		      ));
  ignore (down#connect#clicked 
	    ~callback:(fun b ->  
			 match view#selection#get_selected_rows with 
			   | [] -> ()
			   | path::_ ->
			       let iter = store#get_iter path in
			       GtkTree.TreePath.next path;
			       try let upiter = store#get_iter path in
			       ignore (store#swap iter upiter)
			       with _ -> ()
		      ));
  let get_data () = 
    let start_path = GtkTree.TreePath.from_string "0" in
    let start_iter = store#get_iter start_path in
    let rec all acc = 
      let new_acc = (store#get ~row:start_iter ~column:command_col,
		     store#get ~row:start_iter ~column:coq_col)::acc
      in      
      if store#iter_next start_iter then all new_acc else List.rev new_acc
    in all []
  in
  (hbox,get_data)

