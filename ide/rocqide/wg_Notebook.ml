(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

class ['a] typed_notebook make_page kill_page nb =
object(self)
  inherit GPack.notebook nb as super

  val mutable term_list = []

  method private get_nth_oid index =
    (super#get_nth_page index)#misc#get_oid

  method private create_term creator (term: 'a) =
    let tab_label, menu_label, page = make_page term in
    (* XXX - Temporary hack to compile with archaic lablgtk *)
    let _ = creator ?tab_label ?menu_label page in
    let real_pos = super#page_num page in
    term_list <- (page#misc#get_oid, term) :: term_list;
    super#set_tab_reorderable page true;
    real_pos

  method append_term = self#create_term super#append_page
  method prepend_term = self#create_term super#prepend_page
  method insert_term ?pos = self#create_term (super#insert_page ?pos)

  method set_term (term: 'a) =
    let tab_label, menu_label, page = make_page term in
    let orig_oid = self#get_nth_oid super#current_page in
    term_list <- List.map
        (fun (oid, sn) -> if oid = orig_oid then page#misc#get_oid, term else oid, sn) term_list;
    super#set_page ?tab_label ?menu_label page

  method get_nth_term index =
    List.assoc (self#get_nth_oid index) term_list

  method pages =
    let terms_count = List.length term_list in
    let oid_to_num = Hashtbl.create terms_count in
    for index = 0 to terms_count - 1 do
      Hashtbl.add oid_to_num (self#get_nth_oid index) index;
    done;
    let term_array = Array.make terms_count None in
    List.iter (fun (oid, sn) -> term_array.(Hashtbl.find oid_to_num oid) <- Some sn) term_list;
    Array.fold_right (fun t l -> Option.get t :: l) term_array []

  method! remove_page index =
    kill_page (self#get_nth_term index);
    term_list <- List.remove_assoc (self#get_nth_oid index) term_list;
    super#remove_page index

  method current_term =
    if super#current_page < 0 then invalid_arg "current_term";
    self#get_nth_term super#current_page

  method goto_term term =
    let rec oid_to_num ?(index = 0) oid =
      if (self#get_nth_oid index) = oid then index else oid_to_num ~index:(index + 1) oid
    in
    List.iter (fun (oid, sn) -> if sn == term then super#goto_page (oid_to_num oid)) term_list

end

let create make kill =
  GtkPack.Notebook.make_params []
    ~cont:(GContainer.pack_container
             ~create:(fun pl ->
                        let nb = GtkPack.Notebook.create pl in
                         (new typed_notebook make kill nb)))
