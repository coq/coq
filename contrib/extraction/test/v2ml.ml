let _ = 
  let j = Array.length (Sys.argv) in
  if j>0 then 
    let s = Sys.argv.(1) in
    let b = Filename.chop_extension (Filename.basename s) in 
    let b = String.uncapitalize b in
    let d = Filename.dirname s in 
    print_endline (Filename.concat d (b ^ ".ml"))

