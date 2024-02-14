- **Changed:** names of "push" lemmas for :g:`List.length` to follow the same
  convention as push lemmas for other operations. For example, :g:`app_length`
  became :g:`length_app`. The standard library was migrated using the following
  script:

  .. code-block:: sh

     find theories -name '*.v' | xargs sed -i -E '
       s/\<app_length\>/length_app/g;
       s/\<rev_length\>/length_rev/g;
       s/\<map_length\>/length_map/g;
       s/\<fold_left_length\>/fold_left_S_O/g;
       s/\<split_length_l\>/length_fst_split/g;
       s/\<split_length_r\>/length_snd_split/g;
       s/\<combine_length\>/length_combine/g;
       s/\<prod_length\>/length_prod/g;
       s/\<firstn_length\>/length_firstn/g;
       s/\<skipn_length\>/length_skipn/g;
       s/\<seq_length\>/length_seq/g;
       s/\<concat_length\>/length_concat/g;
       s/\<flat_map_length\>/length_flat_map/g;
       s/\<list_power_length\>/length_list_power/g;
     '

  (`#18564 <https://github.com/coq/coq/pull/18564>`_,
  by Andres Erbsen).
