let drop_setup () =
  begin try
    (* Enable rectypes in the toplevel if it has the directive #rectypes *)
    begin match Hashtbl.find Toploop.directive_table "rectypes" with
      | Toploop.Directive_none f -> f ()
      | _ -> ()
    end
    with
    | Not_found -> ()
  end;
  let ppf = Format.std_formatter in
  Mltop.(set_top
           { load_obj = (fun f -> if not (Topdirs.load_file ppf f)
                          then CErrors.user_err Pp.(str ("Could not load plugin "^f))
                        );
             use_file = Topdirs.dir_use ppf;
             add_dir  = Topdirs.dir_directory;
             ml_loop  = (fun () -> Toploop.loop ppf);
           })

let _ = drop_setup ()
