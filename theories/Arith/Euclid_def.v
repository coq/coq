
(* $Id$ *)

Require Export Mult.

Inductive diveucl [a,b:nat] : Set 
      := divex : (q,r:nat)(gt b r)->(a=(plus (mult q b) r))->(diveucl a b).
