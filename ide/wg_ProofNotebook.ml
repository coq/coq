(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

class proof_notebook nb =
object(self)
  inherit GPack.notebook nb as super
  val mutable proof_list = []

  method append_proof (page: Wg_ProofView.proof_view) =
    ignore (super#append_page page#coerce);
    let real_pos = super#page_num page#coerce in
    let lower,higher = Util.List.chop real_pos proof_list in
      proof_list <- lower@[page]@higher;
      real_pos

  method get_nth_proof i =
    List.nth proof_list i

  method width =
    let cp = self#current_page in
    let wdg = self#get_nth_proof cp in
    wdg#width

  method set_goals =
    let cp = self#current_page in
    let wdg = self#get_nth_proof cp in
    wdg#set_goals

  method set_evars =
    let cp = self#current_page in
    let wdg = self#get_nth_proof cp in
    wdg#set_evars

  method refresh =
    let cp = self#current_page in
    let wdg = self#get_nth_proof cp in
    wdg#refresh

  method clear =
    let cp = self#current_page in
    let wdg = self#get_nth_proof cp in
    wdg#clear

  method buffer =
    let cp = self#current_page in
    let wdg = self#get_nth_proof cp in
    wdg#buffer
end

let create () =
  GtkPack.Notebook.make_params []
    ~cont:(GContainer.pack_container
      ~create:(fun pl ->
        let nb = GtkPack.Notebook.create pl in
          (new proof_notebook nb)))
