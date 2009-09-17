(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util

type ('a,'b,'c) t = {
  mutable focus : 'a option;
  mutable last_focused_stk : 'a list;
  buf : ('a, 'b Bstack.t * 'c) Hashtbl.t }

let empty () = {
  focus = None;
  last_focused_stk = [];
  buf = Hashtbl.create 17 }

let focus e nd =
  if not (Hashtbl.mem e.buf nd) then invalid_arg "Edit.focus";
  begin match e.focus with
    | Some foc when foc <> nd ->
        e.last_focused_stk <- foc::(list_except foc e.last_focused_stk);
    | _ -> ()
  end;
  e.focus <- Some nd

let unfocus e =
  match e.focus with
    | None -> invalid_arg "Edit.unfocus"
    | Some foc ->
	begin
	  e.last_focused_stk <- foc::(list_except foc e.last_focused_stk);
	  e.focus <- None
	end

let last_focused e =
  match e.last_focused_stk with
    | [] -> None
    | f::_ -> Some f

let restore_last_focus e =
  match e.last_focused_stk with
    | [] -> ()
    | f::_ -> focus e f

let focusedp e =
  match e.focus with
    | None -> false
    | _    -> true

let read e =
  match e.focus with
    | None -> None
    | Some d ->
	let (bs,c) = Hashtbl.find e.buf d in
	Some(d,Bstack.top bs,c)

let mutate e f =
  match e.focus with
    | None -> invalid_arg "Edit.mutate"
    | Some d ->
	let (bs,c) = Hashtbl.find e.buf d in
	Bstack.app_push bs (f c)

let rev_mutate e f =
  match e.focus with
    | None -> invalid_arg "Edit.rev_mutate"
    | Some d ->
	let (bs,c) = Hashtbl.find e.buf d in
	Bstack.app_repl bs (f c)

let undo e n =
  match e.focus with
    | None -> invalid_arg "Edit.undo"
    | Some d ->
	let (bs,_) = Hashtbl.find e.buf d in
	if n >= Bstack.size bs then
	  errorlabstrm "Edit.undo" (str"Undo stack exhausted");
        repeat n Bstack.pop bs

(* Return the depth of the focused proof of [e] stack, this is used to
   put informations in coq prompt (in emacs mode). *)
let depth e =
  match e.focus with
    | None -> invalid_arg "Edit.depth"
    | Some d ->
	let (bs,_) = Hashtbl.find e.buf d in
	Bstack.depth bs

(* Undo focused proof of [e] to reach depth [n] *)
let undo_todepth e n =
  match e.focus with
    | None ->
	if n <> 0
	then errorlabstrm "Edit.undo_todepth" (str"No proof in progress")
	else () (* if there is no proof in progress, then n must be zero *)
    | Some d ->
	let (bs,_) = Hashtbl.find e.buf d in
	let ucnt = Bstack.depth bs - n in
	if  ucnt >= Bstack.size bs then
	  errorlabstrm "Edit.undo_todepth" (str"Undo stack would be exhausted");
        repeat ucnt Bstack.pop bs

let create e (d,b,c,usize) =
  if Hashtbl.mem e.buf d then
    errorlabstrm "Edit.create"
      (str"Already editing something of that name");
  let bs = Bstack.create usize b in
  Hashtbl.add e.buf d (bs,c)

let delete e d =
  if not(Hashtbl.mem e.buf d) then
    errorlabstrm "Edit.delete" (str"No such editor");
  Hashtbl.remove e.buf d;
  e.last_focused_stk <- (list_except d e.last_focused_stk);
  match e.focus with
    | Some d' -> if d = d' then (e.focus <- None ; (restore_last_focus e))
    | None -> ()

let dom e =
  let l = ref [] in
  Hashtbl.iter (fun x _ -> l := x :: !l) e.buf;
  !l

let clear e =
  e.focus <- None;
  e.last_focused_stk <- [];
  Hashtbl.clear e.buf
