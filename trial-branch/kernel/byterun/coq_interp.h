/***********************************************************************/
/*                                                                     */
/*                           Coq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/


value coq_push_ra(value tcode);

value coq_push_val(value v);

value coq_push_arguments(value args);

value coq_push_vstack(value stk);

value  coq_interprete_ml(value tcode, value a, value e, value ea);

value coq_interprete
    (code_t coq_pc, value coq_accu, value coq_env, long coq_extra_args);

value coq_eval_tcode (value tcode, value e);


