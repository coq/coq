exception Exception of exn
exception Timeout
exception TacticFailure of exn

let _ = Errors.register_handler begin function
  | Timeout -> Errors.errorlabstrm "Some timeout function" (Pp.str"Timeout!")
  | Exception e -> Errors.print e
  | TacticFailure e -> Errors.print e
  | _ -> Pervasives.raise Errors.Unhandled
end


