let _ =
  let j = Array.length Sys.argv in
  if j > 0 then
    let fml = Sys.argv.(1) in
    let f = Filename.chop_extension fml in 
    let fv = f ^ ".v" in
    if Sys.file_exists ("../../../" ^ fv) then
      print_endline fv
    else
      let d = Filename.dirname f in
      let b = String.capitalize (Filename.basename f) in
      let fv = Filename.concat d (b ^ ".v") in
      print_endline fv
