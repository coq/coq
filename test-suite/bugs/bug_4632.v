
(* File reduced by coq-bug-finder from original input, then from 1291 lines to 305 lines, then from 323 lines to 11 lines, then from 86 lines to 13 lines, then from 188 lines to 13 lines, then from 273 lines to 106 lines, then from 166 lines to 106 lines, then from 193 lines to 121 lines, then from 295 lines to 127 lines, then from 226 lines to 167 lines, then from 223 lines to 168 lines, then from 375 lines to 206 lines, then from 246 lines to 209 lines, then from 2028 lines to 210 lines, then from 224 lines to 211 lines, then from 239 lines to 201 lines, then from 215 lines to 201 lines, then from 198 lines to 8 lines, then from 22 lines to 8 lines *)
(* coqc version 8.5 (February 2016) compiled on Feb 21 2016 15:26:16 with OCaml 4.02.3
   coqtop version 8.5 (February 2016) *)
   Require Corelib.Setoids.Setoid.

   Record refineADT {Sig} (A B : Sig) := { AbsR : Prop }.
   Goal forall (T : Type) (a1 a2 : T), @ refineADT T a2 a1.
     intros.
     cut (a2 = a1); [ intro x | ].
     Succeed setoid_rewrite x.
   Abort.
