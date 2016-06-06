
Record TruncType := BuildTruncType {
  trunctype_type : Type
}.

Fail Arguments BuildTruncType _ _ {_}. (* This should fail *)
