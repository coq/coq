(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(* Given a DIRECTED graph G represented by a list of 
   (x , [neighbours of x])
   then (have_cycle G) returns true if G has a nontrivial cycle.
   Remark : G is not necessarly connected. *******)
  
type mark = NotMarked | OnThePath | AlreadyVisited;;

let df_cycle v marks g =
  let rec df_cycle_rec x = 
    (List.assoc x marks) := OnThePath;
       let nx  = List.assoc x g
    in let nb_marks = 
           List.fold_left (fun s x -> if !(List.assoc x marks)=OnThePath 
      	       	       	       then s+1 else s) 0 nx
    in if nb_marks>0 
       then true
       else let isc = List.fold_left (fun r y -> if r then true 
      	       	       	       	     else if !(List.assoc y marks)=AlreadyVisited 
      	       	       	       	       	  then false
				          else (df_cycle_rec y)) false nx 
	    in if isc then true
	              else ((List.assoc x marks) := AlreadyVisited; false)
  and df_init ls = match ls with
        (s::lls) -> if (!(List.assoc s marks)=NotMarked)
      	       	       & ((List.length (List.assoc s g))>0)
      	       	    then (if df_cycle_rec s
	                  then true
		          else df_init lls)
		    else df_init lls
      | [] -> false
  in df_init v;;

let have_cycle g =
     let v = List.map (fun (x,_) -> x) g
  in let marks = List.map (fun x -> (x,ref NotMarked)) v
  in if List.length g<2
     then false
     else let x0 = fst (List.hd g)
          in df_cycle v marks g;;

(*  Examples...

  have_cycle [(1,[2;3]); (2,[3]); (3,[])];;    		(false)
  
  have_cycle [(1,[2;3]); (2,[1;3]); (3,[1;2])];;	(true)

  have_cycle [(1 , [6]);
      	      (2 , [3;4;5]);
	      (3 , [2;5]);
	      (4 , [2]);
	      (5 , [2;3]);
	      (6 , [1])];;			    	(true)

  have_cycle [(2,[3]); (4,[]); (1,[4]); (3,[])];;       (false)

  have_cycle [(3,[1;2]); (4,[]); (2,[4]); (1,[4])];;    (false)

*)


