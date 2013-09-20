Inductive MS : Set :=
  | X : MS -> MS
  | Y : MS -> MS.

Fail Type (fun p : MS => match p return nat with
                    | X x => 0
                    end).
