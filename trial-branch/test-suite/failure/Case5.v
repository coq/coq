Inductive MS : Set :=
  | X : MS -> MS
  | Y : MS -> MS.
 
Type (fun p : MS => match p return nat with
                    | X x => 0
                    end).
