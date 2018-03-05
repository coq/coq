(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

class ['a] typed_notebook make_page kill_page nb =
object(self)
  inherit GPack.notebook nb as super
  val mutable term_list = []

  method append_term (term:'a) =
    let tab_label,menu_label,page = make_page term in
      (* XXX - Temporary hack to compile with archaic lablgtk *)
    ignore (super#append_page ?tab_label ?menu_label page);
    let real_pos = super#page_num page in
    let lower,higher = Util.List.chop real_pos term_list in
      term_list <- lower@[term]@higher;
      real_pos
(* XXX - Temporary hack to compile with archaic lablgtk
  method insert_term ?(build=default_build) ?pos (term:'a) =
    let tab_label,menu_label,page = build term in
    let real_pos = super#insert_page ?tab_label ?menu_label ?pos page in
    let lower,higher = Util.List.chop real_pos term_list in
      term_list <- lower@[term]@higher;
      real_pos
 *)
  method prepend_term (term:'a) =
    let tab_label,menu_label,page = make_page term in
      (* XXX - Temporary hack to compile with archaic lablgtk *)
    ignore (super#prepend_page ?tab_label ?menu_label page);
    let real_pos = super#page_num page in
    let lower,higher = Util.List.chop real_pos term_list in
      term_list <- lower@[term]@higher;
      real_pos

  method set_term (term:'a) =
    let tab_label,menu_label,page = make_page term in
    let real_pos = super#current_page in
      term_list <- Util.List.map_i (fun i x -> if i = real_pos then term else x) 0 term_list;
      super#set_page ?tab_label ?menu_label page

  method get_nth_term i =
    List.nth term_list i

  method term_num f p =
    Util.List.index0 f p term_list

  method pages = term_list

  method! remove_page index =
    term_list <- Util.List.filteri (fun i x -> if i = index then kill_page x; i <> index) term_list;
    super#remove_page index

  method current_term =
    List.nth term_list super#current_page
end

let create make kill =
  GtkPack.Notebook.make_params []
    ~cont:(GContainer.pack_container
             ~create:(fun pl ->
                        let nb = GtkPack.Notebook.create pl in
                         (new typed_notebook make kill nb)))

