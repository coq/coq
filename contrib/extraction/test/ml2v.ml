let _ =
  for j = 1 to ((Array.length Sys.argv)-1) do
    let fml = Sys.argv.(j) in
    let f = Filename.chop_extension fml in 
    let fv = f ^ ".v" in
    if Sys.file_exists ("../../../" ^ fv) then
      print_string (fv^" ") 
    else
      let d = Filename.dirname f in
      let b = String.capitalize (Filename.basename f) in
      let fv = Filename.concat d (b ^ ".v ") in
      print_string fv
  done;
  print_newline()
