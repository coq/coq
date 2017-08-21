Require Import Recdef.

Function dumb_works (a:nat) {struct a} :=
  match (fun x => x) a with O => O | S n' => dumb_works n' end.

Function dumb_nope (a:nat) {struct a} :=
  match (id (fun x => x)) a with O => O | S n' => dumb_nope n' end.

(* This check is just present to ensure Function worked well *)
Check R_dumb_nope_complete. 
