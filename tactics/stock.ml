
(* $Id$ *)

open Pp
open Util
open Names
open Library

(* The pattern table for tactics. *)

(* The idea is that we want to write tactic files which are only
   "activated" when certain modules are loaded and imported.  Already,
   the question of how to store the tactics is hard, and we will not
   address that here.  However, the question arises of how to store
   the patterns that we will want to use for term-destructuring, and
   the solution proposed is that we will store patterns with a
   "module-marker", telling us which modules have to be open in order
   to use the pattern.  So we will write:

   let mark = make_module_marker ["<module-name>";<module-name>;...]

   let p1 = put_pat mark "<parseable pattern goes here>"

   And now, we can use:

             (get p1)

   to get the term which corresponds to this pattern, already parsed
   and with the global names adjusted.

   In other words, we will have the term which we would have had if we
   had done an:

        constr_of_com mt_ctxt (initial_sign()) "<text here>"

   except that it will be computed at module-opening time, rather than
   at tactic-application time.  The ONLY difference will be that
   no implicit syntax resolution will happen.

   So the entries we provide are:

   type module_mark

   value make_module_marker : string list -> module_mark

   type marked_term

   value put_pat : module_mark -> string -> marked_term

   value get_pat : marked_term -> constr

 *)

type module_mark = Mmk of int

let path_mark_bij = ref (Bij.empty : (string list,module_mark) Bij.t)

let mmk_ctr = ref 0

let new_mmk () = (incr mmk_ctr; !mmk_ctr)

let make_module_marker stock sl =
  let sorted_sl = Sort.list (<) sl in 
  try 
    Bij.map !path_mark_bij sorted_sl
  with Not_found -> begin
    let mmk = Mmk(new_mmk()) in 
    path_mark_bij := Bij.add !path_mark_bij (sorted_sl,mmk);
    mmk
  end
      
let mark_satisfied mmk =
  let spl = Bij.pam !path_mark_bij mmk in 
  list_subset spl (loaded_modules())

(* src_tab: for each module_mark, stores the tickets of objects which
   need to be compiled when that mark becomes active.

   obj_tab: for each ticket, stores the (possibly nonexistent)
   compiled object

   ticket_tab: for each ticket, stores its module_mark and the string
   (source)

   string_tab: for each string * module_mark, stores the ticket. *)

type 'a stock_args = {
  name : string;
  proc : string -> 'a }

type 'a stock = {
  mutable src_tab : (module_mark,int) Gmapl.t;
  mutable obj_tab : (int,'a) Gmap.t;
  mutable ticket_string_bij : (int,string * module_mark) Bij.t;
  args : 'a stock_args }

type 'a stocked = int

let stock_ctr = ref 0

let new_stock () = (incr stock_ctr; !stock_ctr)

let make_stock args =
  { src_tab = Gmapl.empty;
    obj_tab = Gmap.empty;
    ticket_string_bij = Bij.empty;
    args = args }
  
let stock stock mmk s =
  try 
    Bij.pam stock.ticket_string_bij (s,mmk)
  with Not_found -> begin
    let idx = new_stock() in 
    stock.src_tab <- Gmapl.add mmk idx stock.src_tab;
    stock.ticket_string_bij <- Bij.add stock.ticket_string_bij (idx,(s,mmk));
    idx
  end

let pr_mm mm =
  let sl = Bij.pam !path_mark_bij mm in
  prlist_with_sep pr_spc (fun s -> [< 'sTR s >]) sl

(* TODO: traiter a part les erreurs provenant de stock.args.proc
   ( = parsing quand [so]pattern appelle retrieve)
    -> eviter d'avoir l'erreur stocked datum *)

let retrieve stock idx =
  try 
    Gmap.find idx stock.obj_tab
  with Not_found ->
    let (s,mmk) = Bij.map stock.ticket_string_bij idx in 
    if mark_satisfied mmk then
      try
        let c = stock.args.proc s in 
	stock.obj_tab <- Gmap.add idx c stock.obj_tab;
        c
      with e -> begin
        mSGNL [< 'sTR"Processing of the stocked datum " ; 'sTR s ;
                 'sTR" failed." ; 'fNL;
                 Library.fmt_modules_state() >];
	raise e
      end
    else
      errorlabstrm "Stock.retrieve"
        [< 'sTR"The stocked object "; 'sTR s; 'sTR" was not compilable"; 
	   'fNL; 'sTR"Its module mark was: "; pr_mm mmk ; 'fNL ;
           Library.fmt_modules_state() >]
