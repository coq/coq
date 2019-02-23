(* Little utility to gen the install file for a directory *)
open Format

type install_info =
  { from : string
  ; dest : string
  }

let pp_sep fmt () = fprintf fmt "@;"

let pp_install_info fmt ii =
  Format.fprintf fmt "@[(\"%s\" as \"%s\")@]" ii.from ii.dest

let pp_install fmt ~package ~section files =
  Format.fprintf fmt
    "(install@\n @[(section %s)@\n(package %s)@\n(files @[%a@])@])@\n"
    section package
    (Format.pp_print_list ~pp_sep pp_install_info) files

let rec scan_directory directory =
  if Sys.is_directory directory then
    let files = List.(map Filename.(concat directory) Array.(to_list Sys.(readdir directory))) in
    List.(concat (map scan_directory files))
  else
    [directory]

(* Base case *)
let scan_directory directory =
  Sys.chdir directory;
  let files = Array.to_list Sys.(readdir ".") in
  List.(concat (map scan_directory files))

let gen_install ppf ~package ~section ~directory ~target =
  let files = scan_directory directory in
  let files = List.map (fun from ->
      { from = Filename.concat directory from
      ; dest = Filename.concat target from
      } ) files in
  Format.fprintf ppf "@[%a@]%!" (pp_install ~package ~section) files

let _ =
  Printexc.record_backtrace true;
  if Array.length Sys.argv <> 5 then
    begin
      Format.eprintf "[usage] gen_install package section directory target@\n%!";
      exit 1
    end;
  let package = Sys.argv.(1) in
  let section = Sys.argv.(2) in
  let directory = Sys.argv.(3) in
  let target = Sys.argv.(4) in
  gen_install Format.std_formatter ~package ~section ~directory ~target
