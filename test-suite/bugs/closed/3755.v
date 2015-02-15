(* File reduced by coq-bug-finder from original input, then from 6729 lines to 
411 lines, then from 148 lines to 115 lines, then from 99 lines to 70 lines, 
then from 85 lines to 63 lines, then from 76 lines to 55 lines, then from 61 
lines to 17 lines *)
(* coqc version trunk (January 2015) compiled on Jan 17 2015 21:58:5 with OCaml 
4.01.0
   coqtop version cagnode15:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk 
(9e6b28c04ad98369a012faf3bd4d630cf123a473) *)
Set Printing Universes.
Section param.
  Variable typeD : Set -> Set.
  Variable STex : forall (T : Type) (p : T -> Set), Set.
  Definition existsEach_cons' v (P : @sigT _ typeD -> Set) :=
    @STex _ (fun x => P (@existT _ _ v x)).

  Check @existT _ _ STex STex.
