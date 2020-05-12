- **Added:**
  lemmas about lists:

  - properties of ``In``: ``in_elt``, ``in_elt_inv``
  - properties of ``nth``: ``app_nth2_plus``, ``nth_middle``, ``nth_ext``
  - properties of ``last``: ``last_last``, ``removelast_last``
  - properties of ``remove``: ``remove_cons``, ``remove_app``, ``notin_remove``, ``in_remove``, ``in_in_remove``, ``remove_remove_comm``, ``remove_remove_eq``, ``remove_length_le``, ``remove_length_lt``
  - properties of ``concat``: ``in_concat``, ``remove_concat``
  - properties of ``map`` and ``flat_map``: ``map_last``, ``map_eq_cons``, ``map_eq_app``, ``flat_map_app``, ``flat_map_ext``, ``nth_nth_nth_map``
  - properties of ``incl``: ``incl_nil_l``, ``incl_l_nil``, ``incl_cons_inv``, ``incl_app_app``, ``incl_app_inv``, ``remove_incl``, ``incl_map``, ``incl_filter``, ``incl_Forall_in_iff``
  - properties of ``NoDup`` and ``nodup``: ``NoDup_rev``, ``NoDup_filter``, ``nodup_incl``
  - properties of ``Exists`` and ``Forall``: ``Exists_nth``, ``Exists_app``, ``Exists_rev``, ``Exists_fold_right``, ``incl_Exists``, ``Forall_nth``, ``Forall_app``, ``Forall_elt``, ``Forall_rev``, ``Forall_fold_right``, ``incl_Forall``, ``map_ext_Forall``, ``Exists_or``, ``Exists_or_inv``, ``Forall_and``, ``Forall_and_inv``, ``exists_Forall``, ``Forall_image``, ``concat_nil_Forall``, ``in_flat_map_Exists``, ``notin_flat_map_Forall``
  - properties of ``repeat``: ``repeat_cons``, ``repeat_to_concat``
  - definitions and properties of ``list_sum`` and ``list_max``: ``list_sum_app``, ``list_max_app``, ``list_max_le``, ``list_max_lt``
  - misc: ``elt_eq_unit``, ``last_length``, ``rev_eq_app``, ``removelast_firstn_len``, ``cons_seq``, ``seq_S``

  (`#11249 <https://github.com/coq/coq/pull/11249>`_, `#12237 <https://github.com/coq/coq/pull/12237>`_,
  by Olivier Laurent).
