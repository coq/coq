Fixpoint f n := match n with S n => g n | O => O end
with g n := match n with S n => f n | O => O end.

Print f.
