- Section data is now part of the kernel. Solves a soundness issue
  in interactive mode where global monomorphic universe constraints would be
  dropped when forcing a delayed opaque proof inside a polymorphic section. Also
  relaxes the nesting criterion for sections, as polymorphic sections can now
  appear inside a monomorphic one
  (#10664, <https://github.com/coq/coq/pull/10664> by Pierre-Marie Pédrot).
