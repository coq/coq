let main () = begin
  let j = Array.length (Sys.argv) in
  if j>0 then begin
	let s = Sys.argv.(1) in
	let b = Filename.chop_extension (Filename.basename s) in 
	let b0 = String.sub b 0 1 in
	let b1 = String.capitalize b0 in  
	let b = String.sub b 1 ((String.length b) -1) in 
	let d = Filename.dirname s
	in print_string (d^"/["^b0^b1^"]"^b^".v");
	print_newline()
  end;
  exit(0)	
end;;	

main();;
 		
