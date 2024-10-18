/***********************************************************************/
/*                                                                     */
/*                          Rocq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/


value rocq_push_ra(value tcode);

value rocq_push_val(value v);

value rocq_push_arguments(value args);

value rocq_push_vstack(value stk);

value rocq_interprete_ml(value tcode, value a, value t, value g, value e, value ea);
value rocq_interprete_byte(value* argv, int argn);

value rocq_interprete
    (code_t rocq_pc, value rocq_accu, value rocq_atom_tbl, value rocq_global_data, value rocq_env, long rocq_extra_args);
