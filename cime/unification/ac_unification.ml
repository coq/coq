(***************************************************************************

(This sentence has been added automatically,
it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Theory

let make_find_th sign f = 
  if sign#is_ac f
  then None, (AC f)
  else 
    if sign#is_commutative f
    then None, (C f)
    else None, (Empty None)
  
let set_of_solutions sign (*i vars i*) t1 t2 =
  Unification.set_of_solutions AC_ONLY sign (*i vars i*) (make_find_th sign) t1 t2

let display_set_of_solutions sign vars t1 t2 =
  let sols = 
    set_of_solutions (sign :> 'symbol Signatures.signature) (*i vars *) t1 t2 
  in
  Format.print_int (List.length sols);
  Format.print_string " solution(s)";
  Format.print_newline();
  if !Unification.verbose > 1
  then
    begin
      let n = ref 1 in
      List.iter 
	(fun sol ->
	   Format.print_string "-----";
	   Format.print_int !n;
	   n := succ !n;
	   Format.print_string "-----";
	   Format.print_newline();
	   Format.print_flush ();
	   if sol = Variables.VarMap.empty
	   then 
	     begin
	       Format.print_string "{}";
	       Format.print_newline()
	     end
	   else Substitution.print sign vars sol;
	   Format.print_flush ())
	sols;
      Format.print_string "-----------";
      Format.print_newline();
      Format.print_flush ()
    end
    
