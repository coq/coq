(* backport of Mutex.protect from OCaml 5.1 *)
external unlock: Mutex.t -> unit = "caml_ml_mutex_unlock"

(* Critical sections :
   - Mutex.lock does not poll on leaving the blocking section
     since 4.12.
   - Never inline, to avoid theoretically-possible reorderings with
     flambda.
   - Inline the call to Mutex.unlock to avoid polling in bytecode.
     (workaround to the lack of masking) *)
let[@inline never] with_lock m ~scope =
  let () = Mutex.lock m (* BEGIN ATOMIC *) in
  match (* END ATOMIC *) scope () with
  | (* BEGIN ATOMIC *) x -> unlock m ; (* END ATOMIC *) x
  | (* BEGIN ATOMIC *) exception e -> unlock m ; (* END ATOMIC *) raise e
