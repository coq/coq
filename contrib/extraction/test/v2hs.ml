let _ = 
  for j = 1 to ((Array.length Sys.argv) -1) do 
    let s = Sys.argv.(j) in
    let b = Filename.chop_extension (Filename.basename s) in 
    let b = String.capitalize b in
    let d = Filename.dirname s in 
    print_string (Filename.concat d (b ^ ".hs "))
  done;	
  print_newline()
