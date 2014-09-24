open Globnames
open Term
open Libobject

(* Union-find structure for references to be considered equivalent *)

module RefUF = Unionfind.Make(Refset)(Refmap)

let keys = (* Summary.ref ( *)RefUF.create ()(* ) ~name:"Keys_decl" *)

let add_key k v = RefUF.union k v keys

let equiv_keys k k' = RefUF.find k keys == RefUF.find k' keys

(** Registration of keys as an object *)

let load_key _ (_,(ref,ref')) =
  add_key ref ref'

let cache_key o =
  load_key 1 o

let subst_key (subst,(ref,ref')) =
  (subst_global_reference subst ref,
   subst_global_reference subst ref')

let discharge_key (_,refs) =
  match refs with 
  | VarRef _, _ | _, VarRef _ -> None
  | ref, ref' -> Some (pop_global_reference ref, pop_global_reference ref')

let rebuild_key (ref,ref') = (ref, ref')

type key_obj = global_reference * global_reference

let inKeys : key_obj -> obj =
  declare_object {(default_object "KEYS") with
    cache_function = cache_key;
    load_function = load_key;
    subst_function = subst_key;
    classify_function = (fun x -> Substitute x);
    discharge_function = discharge_key;
    rebuild_function = rebuild_key }

let declare_keys ref ref' =
  Lib.add_anonymous_leaf (inKeys (ref,ref'))
