Require Import TestSuite.list.
Set Debug RAKAM.
Check fun _ => fold_right (fun A B => prod A B) unit _.
