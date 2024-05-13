(* Ltac2 manual tests *)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.
Set Ltac Debug.
Set Ltac Debug History 100.

Ltac2 m s := Message.print (Message.of_string s).
(*
The "(* bp *)" marks selected stopping points (by breakpoint or single step) - verify!
Run code with "Step in" if not otherwise specified.
Generally check that the goal, stack and variables match the stopping point.
*)


(* basics:
  - y stack entry shows variable i and its value
  - zz stack shows 3 stack frames
  - stack frames have function name, correct line number
  - stops in the right places
*)

Module Basics.
Ltac2 zz () := exact I; m "hi".
Ltac2 z () := zz ().
Ltac2 y () := let i := 1 in z ().
Goal True.
(* bp *) y ().
Abort.
End Basics.


(* multimatch:
   output in Messages is: branch 1, after, branch2, after *)
Goal True.
Fail multi_match! 'True with
| True => m "branch 1"
| _ => m "branch 2"
end ;
m "after" ; fail.
Abort.


(* ltac1:() and ltac2:()
  stops at both "ltac1:(X)" on the X
  stack is correct at both of these points
  v1/v2 appear on correct stack frame
 *)
Module Ltac1.
Goal True.
Ltac foomsg := idtac "foo".
Ltac2 t () := m "xxx"; ltac1:( (*bp*) foomsg); m "z".
let v1 := 2 in t ().

Ltac l2msg := let v2 := 456 in (*not bp*)ltac2:((*bp*) m "msg"); idtac.
(*not bp*) ltac1:( (*bp*) l2msg).
print (of_string "x").

(* should stop at both indicated points (single step or bp)
   both points should show t in the variables panel
   check stack is correct
*)
Ltac my_tac := idtac "1".
Ltac2 y () :=
   let t := true in ltac1:((*1*) my_tac); ltac1:((*2*) idtac "2"); m "after".
y ().

(* check goals are saved after ltac1:()
   Should be no goals left at (*bp*)  *)
ltac1:(apply I); (* bp *) m "after".


Abort.
End Ltac1.


(* abbreviations/notations
   a/n name is a stop point as are functions in their defns
   should see a stack frame on the defn line with the a/n name
 *)
Module Abbrev.
Ltac2 y () := m "msg"; apply I.
Ltac2 Notation abbrev := m "msg".
Goal True.
abbrev; m "after".

Ltac2 Notation "notat" x(constr) := print (of_constr x).
notat (1+2).
Abort.
End Abbrev.


(* printing Ltac2 variables:
   stop at (*bp*)
   all values should be printed fully, similar to their form in the Ltac2 code
*)
Module Variables.
Ltac2 Type foo := [ Foot | Fuss (string, int, bool) ].
Ltac2 Type bar := { i:int; s:string }.
Record myrec : Set := mkrec {
 c : bool;
 d : nat
}.
Ltac2 x () :=
  let y := {i:=1; s:="s"} in m "x".
Ltac2 y () :=
  let a := () in
  let b := [] in
  let c := [| |] in
  let d := true in
  let e := 123 in
  let ea := (1,2) in
  let f := [1;2] in
  let g := [| 1;2 |] in
  let h := [| true; false |] in
  let i := [ constr:(true); constr:(false) ] in
  let j := [ [ true ]; [ false ] ] in
  let k := [| [| true |]; [| false |] |] in
  let l := Fuss "fuss arg" 33 true in
  let ma := {i:=1; s:="s"} in
  let n := open_constr:({| c := true; d := 2 |}) in
  (*bp*) m "x".
Goal True.
y ().
Abort.
End Variables.


(* pattern variables and parameters:
   type of "poly" is unknown here
   Bug: variables p and p1 created by Ltac2 should be hidden
*)
Module PatVars.
Ltac2 y (a,poly) :=
   m "enter";
   let (b,(c,d)) := (1, (3, 4)) in
   match (1, 2) with
   | (e, f) => m "abc"
   end;
   let g := c in
   m "x";
   m a.  (* tells that n is string *)
Goal True.
y ("a", "b").
Abort.
End PatVars.



(* ltac1val:()
   bug: "ltac1val:" shouldn't be a stopping point *)
Module Ltac1val.
Goal True.
Ltac y := idtac "y".
Ltac2 z () := Ltac1.run (ltac1val:(x |- y)
  (Ltac1.of_constr constr:(Type))); ltac1:(y).
z ().
Abort.
End Ltac1val.


(*
        **Exceptions and backtracking work as expected
                *And across environments
        Shows reasonable data for multi file case
        open_constr?
History mechanism
        Step back works like step fwd
        Goals match the state
        ?Apply history limits, cleared after exit
          ?Can set limit

        ltac1val.v - ltac1val:() shouldn't be a stopping point
        ltac2_demo_*.v
*)


(* user can select which subgoal to display:
   use View/Next goal and View/Previous goal,
   observe change in Proof panel *)
Goal (False -> True) /\ (False -> True).
split; intros.
(* run to here *)
Abort.

(* user can change View options in the debugger
   toggle View/Display all low-level constructs,
   see change in Proof panel *)
Goal 1 = 0.
(*bp*)m "x".
Abort.


(* background/shelve/give_up
   in the debugger, info on bg/shelved/given_up goals is not shown even if
   all the foreground goals have been solved (at "(*bp*)").  (Todo: show them)
*)

(* shelved (or given up) goals not shown *)
Module Shelved.
Goal True /\ False.
Ltac my_tac := split; only 2: shelve; (* only 2: give_up; *) apply I; (*bp*) idtac.
ltac1:(my_tac).
Abort.

(* bg goals not shown *)
Goal True /\ False.
Ltac my_tac2 := split; only 1: (apply I; (*bp*) idtac).
ltac1:(my_tac2).
Abort.
End Shelved.


(* Set Ltac Debug Enter Library option:
   single step from the (*bp*).  The first
   steps through Ltac2 library code to create
   the array, the second one doesn't.  Stack
   for library code should show Array module
*)
Module EnterLibrary.
Ltac2 a () := let i := [| 1 |] in m "x".
Goal True.
Set Ltac Debug Enter Library.
(*bp*)a ().
Unset Ltac Debug Enter Library.
(*bp*)a ().
Abort.
Module EnterLibrary.


(* Navigation/Interrupt (aborts tactic) and Debug/Break (stops tactic, resumable) *)
Module Interrupt.
Ltac2 n () := ().
Goal True.
do 500 (do 10000 n).
Abort.
End Interrupt.


(* Note: intentionally fails, can't use Fail ...
(* catch top level exception before exiting
   Stop at (*bp*), step forward, see the exception, step back in history,
   then exit by stepping forward at "TCDebug >" or ">History (0) >" prompt.
   bug: the exception is printed a second time after exiting *)

Module Exception.
Ltac2 n () := fail.
Ltac2 m s := Message.print (Message.of_string s).
Goal True.
m "before"; (*bp*) n (); m "after".
End Exception.
*)
