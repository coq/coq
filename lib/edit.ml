
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
	(match Bstack.top bs with
           | None -> anomaly "Edit.read"
	   | Some v -> Some(d,v,c))

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
	if Bstack.depth bs <= n then
          errorlabstrm "Edit.undo" [< 'sTR"Undo stack would be exhausted" >];
        repeat n (fun () -> let _ = Bstack.pop bs in ()) ()

let create e (d,b,c,udepth) =
  if Hashtbl.mem e.buf d then
    errorlabstrm "Edit.create" 
      [< 'sTR"Already editing something of that name" >];
  let bs = Bstack.create udepth in
  Bstack.push bs b;
  Hashtbl.add e.buf d (bs,c)

let delete e d =
  if not(Hashtbl.mem e.buf d) then
    errorlabstrm "Edit.delete" [< 'sTR"No such editor" >];
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
