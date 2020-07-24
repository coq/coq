Require Import ssreflect ssrfun ssrbool.


Goal forall b : bool, b -> False.
Set Warnings "+spurious-ssr-injection".
Fail move=> b [].
Set Warnings "-spurious-ssr-injection".
move=> b [].
Abort.
