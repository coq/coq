let main () = begin
  let j = Array.length (Sys.argv) in
  if j>0 then begin
	let s = Sys.argv.(1) in
	let b = Filename.chop_extension (Filename.basename s) in 
	let b = String.uncapitalize b in
	let d = Filename.dirname s
	in print_string (d^"/"^b^".ml");
	print_newline()
  end;
  exit(0)	
end;;	

main();;
 		
