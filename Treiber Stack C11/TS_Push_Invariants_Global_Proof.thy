theory TS_Push_Invariants_Global_Proof
imports  TS_Proof_Rules
begin



lemma push_inv_gc_pop:
  assumes "wfs ccs"
      and "lib_wfs cls ccs"
      and "pop_inv t' l (pc ps t') cls ccs  ps"
      and "lib_pop t' v ps cls ccs ps' cls' ccs'"
      and "push_inv t v (pc ps t) cls ccs  ps"
      and "push_inv t' v (pc ps t') cls ccs  ps"
      and "glb_inv ps cls"
      and "glb ps cls"
      and "t \<noteq> t'"
      and "to ps cls"
   shows "push_inv t v (pc ps' t) cls' ccs'  ps'"
    proof (cases "pc ps t'")
      case L1
      then show ?thesis                   
          using assms
          apply(cases "pc ps t"; simp ; elim exE conjE; simp)
          apply(cases "pc ps' t", simp_all) 
          apply (intro conjI impI allI) 
          apply (simp_all add: lib_pop_def)
          apply (metis lib_d_obs_pres_read new_node_def)
          apply (metis lib_d_obs_pres_read new_node_def)
          using lib_read_cvd_pres apply blast
          apply (simp add: new_node_def no_Top_n_a_def rd_A_preserves_values read_pres_writes_on_diff_var)          using rd_A_preserves_values rd_A_preserves_writes_on 
          apply metis
                    apply(simp add: cobs_to_def)
          apply (metis agt_pushed_same2rd_before_state lib_c_obs_lib_only_pres_read_var)
                    apply(simp add: cobs_to_def)
                    apply(subgoal_tac "written_addr cls' = written_addr cls")
                     apply(simp add: addr_init_writes_def written_vals_def new_node_def)
          
          apply (metis rd_A_preserves_values read_pres_writes_on_diff_var)
          apply(simp add: written_addr_def)
          
          apply (metis rd_A_preserves_values read_pres_writes_on_diff_var)
         apply auto[]
          apply(cases "pc ps' t", simp_all)         
                  apply auto[1]
                 apply auto[1]
                apply auto[1]
                apply auto[1]
          apply(cases "pc ps' t", simp_all) 
                   apply auto[1] 
                  apply(intro conjI)
          apply (meson lib_d_obs_pres_read)

          apply (meson lib_d_obs_pres_read)
          apply (meson lib_read_cvd_pres)

          
          apply (smt lib_d_obs_pres_read lib_read_cvd_pres no_Top_n_def rd_A_preserves_values read_pres_writes_on_diff_var written_addr_def)
                   apply(simp add: written_addr_def)
          using rd_A_preserves_values rd_A_preserves_writes_on apply auto[1]
                  apply(simp add: cobs_to_def)
          apply(subgoal_tac "written_addr cls' = written_addr cls")
                   apply (metis agt_pushed_same2rd_before_state lib_c_obs_lib_only_pres_read_var)
           apply(simp add: written_addr_def)
                   apply (metis rd_A_preserves_values read_pres_writes_on_diff_var)
                  apply(simp add: written_vals_def)
          
          apply (metis rd_A_preserves_values read_pres_writes_on_diff_var)
      apply auto[2]
               apply auto[1]
              apply auto[1]
             apply(cases "pc ps' t", simp_all) 
          apply(intro conjI)
                      apply auto[6]
                 apply(intro conjI)
          
                        apply auto[1]
          
                       apply auto[1]
          apply auto[1]

  apply (smt lib_d_obs_pres_read lib_read_cvd_pres no_Top_n_def rd_A_preserves_last rd_A_preserves_values read_pres_writes_on_diff_var)
                    apply auto[1]

                   apply auto[1]
          
          apply auto[1]
                 apply auto[1]
          apply(intro conjI)
          using lib_d_obs_pres_read apply blast
          using lib_d_obs_pres_read apply blast
          using lib_read_cvd_pres apply blast
          apply(simp add: no_Top_n_def)
          
          apply (metis lib_read_writes_on_diff_var_pres_backwards rd_A_preserves_values)
          using cobs_to_read_pres apply blast
         apply(simp add: cobs_to_def)
                   apply(subgoal_tac "written_addr cls' = written_addr cls")
                   apply (metis agt_pushed_same2rd_before_state lib_c_obs_lib_only_pres_read_var)
           apply(simp add: written_addr_def)
                 apply (metis rd_A_preserves_values read_pres_writes_on_diff_var)
          apply(simp add: written_addr_def)
          apply(simp add: written_vals_def)
          apply (metis rd_A_preserves_values read_pres_writes_on_diff_var)
                apply auto[1]
              apply auto[1]
          apply auto[1]
            apply(cases "pc ps' t", simp_all) 
          apply(intro conjI)
                     apply auto[7]
          apply(intro conjI)
          using lib_d_obs_pres_read apply blast
          using lib_d_obs_pres_read apply blast
          using lib_read_cvd_pres apply blast
          apply (smt lib_d_obs_pres_read lib_read_cvd_pres no_Top_n_def rd_A_preserves_last rd_A_preserves_values read_pres_writes_on_diff_var)
          apply(simp add: written_addr_def)
          using rd_A_preserves_values rd_A_preserves_writes_on apply auto[1]
          apply(simp add: cobs_to_def)
           apply(subgoal_tac "written_addr cls' = written_addr cls")
                   apply (metis agt_pushed_same2rd_before_state lib_c_obs_lib_only_pres_read_var)
           apply(simp add: written_addr_def)
                apply (metis rd_A_preserves_values read_pres_writes_on_diff_var)
               apply(simp add: written_vals_def)
          
               apply auto[1]
          apply(intro conjI)
          using lib_d_obs_pres_read apply blast
                 using lib_d_obs_pres_read apply blast
                 using lib_read_cvd_pres apply blast
                 apply(simp add: no_Top_n_def)

                          apply (metis rd_A_preserves_values read_pres_writes_on_diff_var)
                         
                         apply(simp add: dobs_to_def)
              apply(simp add: written_addr_def)
                         apply (metis rd_A_preserves_values read_pres_writes_on_diff_var)


           apply(simp add: cobs_to_def)
           apply(subgoal_tac "written_addr cls' = written_addr cls")
                   apply (metis agt_pushed_same2rd_before_state lib_c_obs_lib_only_pres_read_var)
           apply(simp add: written_addr_def)
             apply (metis rd_A_preserves_values read_pres_writes_on_diff_var)
           apply(simp add: dobs_to_def)
              apply (metis agt_pushed_same2rd_before_state lib_d_obs_pres_read)
             apply(simp add: written_addr_def)
             apply (metis lib_read_writes_on_diff_var_pres_backwards rd_A_preserves_values)
                     apply(simp add: written_vals_def)
                 
                 apply (metis rd_A_preserves_values rd_A_preserves_writes_on)
                                          apply(simp add: written_vals_def)
                 
                 
                 apply (metis PC.distinct(25) fun_upd_other neq0_conv)
                   apply(intro allI impI conjI)
                 apply auto[1]
                 apply auto[1]
                  using lib_read_cvd_pres apply blast
            apply auto[1]
           apply(cases "pc ps' t", simp_all) 
          apply auto[1]
          apply auto[1]
          apply auto[1]
                     apply auto[1]
          apply(intro conjI)
             apply (meson lib_d_obs_pres_read lib_read_cvd_pres)
          using lib_d_obs_pres_read apply blast
          using lib_read_cvd_pres apply blast
          
                  apply (metis read_pres_last_val)
          
                 apply (smt no_Top_n_def rd_A_preserves_values rd_A_preserves_writes_on)
          using cobs_to_read_pres apply blast
          apply(simp add: dobs_to_def)
                   apply (metis agt_pushed_same2rd_before_state lib_d_obs_pres_read)
                        apply (metis rd_A_preserves_values rd_A_preserves_writes_on written_addr_def)
                         apply (metis rd_A_preserves_values rd_A_preserves_writes_on written_addr_def)
            apply(simp add: written_vals_def)
            apply (metis rd_A_preserves_values rd_A_preserves_writes_on)

           apply(simp add: cobs_to_def)
          apply (metis PC.distinct(29) fun_upd_other neq0_conv)
          by (smt Null_def PC.simps(36) add.commute cobs_to_read_pres fun_upd_other glb_def lib_d_obs_pres_read lib_read_cvd_pres not_gr_zero plus_1_eq_Suc)
        next
      case L2
      then show ?thesis 
          using assms
          apply(cases "pc ps t"; simp add: glb_inv_def glb_inv14_def; elim exE conjE; simp)
          apply(cases "pc ps' t", simp_all) 
          apply (intro conjI impI allI) 
          apply (simp_all add: lib_pop_def)
          apply (simp add: new_node_def lib_pop_def)
          apply (metis lib_d_obs_pres_read)
          apply (metis lib_d_obs_pres_read new_node_def)
          apply (meson lib_read_cvd_pres)
          apply (simp add: glb_inv1_def glb_inv_def new_node_def no_Top_n_a_def)
                apply (metis lib_read_writes_on_diff_var_pres_backwards read_pres_value)
          apply(simp add: cobs_to_def)
          apply (metis agt_pushed_same2rd_relax_before_state lib_c_obs_lib_only_pres_read_var)
               apply(simp add: addr_init_writes_def written_vals_def new_node_def)
          apply(intro allI impI conjI)
          
          apply (metis (no_types, lifting) image_cong lib_read_writes_on_diff_var_pres_backwards read_pres_value)
        apply (smt image_cong lib_read_writes_on_diff_var_pres_backwards read_pres_value)
               apply(intro conjI)
(*Do a lemma for this*)
               apply (smt lib_d_obs_pres_read lib_read_cvd_pres no_Top_n_def read_pres_value read_pres_writes_on_diff_var)
          apply (smt lib_d_obs_pres_read lib_read_cvd_pres no_Top_n_def read_pres_value read_pres_writes_on_diff_var)
          apply (meson lib_read_cvd_pres)
                       apply (smt no_Top_n_def read_pres_value read_pres_writes_on_diff_var)
                 apply(simp add: written_addr_def)
                 
                      apply (metis image_cong lib_read_writes_on_diff_var_pres_backwards read_pres_value)
                 apply(simp add: cobs_to_def)
                 apply (metis agt_pushed_same2rd_relax_before_state lib_c_obs_lib_only_pres_read_var)
              apply(simp add: written_vals_def)
          apply (smt image_cong lib_read_writes_on_diff_var_pres_backwards read_pres_value)
              
              apply (intro conjI impI allI)
                   apply (meson lib_d_obs_pres_read)
          apply (meson lib_d_obs_pres_read)
          apply (meson lib_read_cvd_pres)
          apply (simp add: no_Top_n_def read_pres_value read_pres_writes_on_diff_var)
          apply (simp add: read_pres_value read_pres_writes_on_diff_var written_addr_def)
          apply (smt lib_d_obs_pres_read lib_read_cvd_pres no_Top_n_def rd_preserves_last read_pres_value read_pres_writes_on_diff_var)          
             apply(simp add: cobs_to_def)
              apply (metis agt_pushed_same2rd_relax_before_state lib_c_obs_lib_only_pres_read_var)
             apply(simp add: written_addr_def)
          apply (metis image_cong lib_read_writes_on_diff_var_pres_backwards read_pres_value)
          apply(simp add: written_vals_def)
          apply (metis (no_types, lifting) image_iff lib_read_writes_on_diff_var_pres_backwards read_pres_value)
            apply(intro conjI)
          apply (meson lib_d_obs_pres_read)
          apply (meson lib_d_obs_pres_read)
          apply (meson lib_read_cvd_pres)
          apply (smt no_Top_n_def read_pres_value read_pres_writes_on_diff_var)
      apply (smt Diff_iff imageE image_eqI read_pres_value read_pres_writes_on_diff_var written_addr_def)
             apply(simp add: cobs_to_def)
             apply (metis agt_pushed_same2rd_relax_before_state lib_c_obs_lib_only_pres_read_var)
              apply(simp add: dobs_to_def)
             apply (metis agt_pushed_same2rd_relax_before_state lib_d_obs_pres_read)
             apply(simp add: written_addr_def)
          apply (metis image_cong lib_read_writes_on_diff_var_pres_backwards read_pres_value)
          apply(simp add: written_vals_def)
          apply (metis (no_types, lifting) image_iff lib_read_writes_on_diff_var_pres_backwards read_pres_value)                 
   apply(intro conjI)
          apply (smt lib_d_obs_pres_read lib_read_cvd_pres no_Top_n_def rd_preserves_last read_pres_value read_pres_writes_on_diff_var)
          apply (meson lib_d_obs_pres_read)
          apply (meson lib_read_cvd_pres)
          using rd_preserves_last apply auto[1]
          apply (smt no_Top_n_def read_pres_value read_pres_writes_on_diff_var)
                 apply(simp add: cobs_to_def)
      apply (metis agt_pushed_same2rd_relax_before_state lib_c_obs_lib_only_pres_read_var)
               apply(simp add: dobs_to_def)
           apply (metis agt_pushed_same2rd_relax_before_state lib_d_obs_pres_read)
            apply(simp add: cobs_to_def dobs_to_def)
             apply(simp add: written_addr_def)
            apply (metis image_cong lib_read_writes_on_diff_var_pres_backwards read_pres_value)
           apply(intro impI)
          apply(simp add: globals written_addr_def)
          apply (metis (no_types, lifting) image_cong lib_read_writes_on_diff_var_pres_backwards read_pres_value)
          apply(simp add: written_vals_def)
           apply (metis (no_types, lifting) image_iff lib_read_writes_on_diff_var_pres_backwards read_pres_value)     
          apply(intro conjI)
         using lib_d_obs_pres_read apply metis
         using lib_d_obs_pres_read apply metis
         using lib_read_cvd_pres apply metis
         apply(simp add: cobs_to_def)
         by (metis agt_pushed_same2rd_relax_before_state lib_c_obs_lib_only_pres_read_var)
    next 
      case L3
      then show ?thesis
        using assms
      proof (cases "res ps' t'")
        case False
        then show ?thesis
           using assms
           apply(cases "pc ps t"; cases "pc ps' t"; cases "pc ps t'")
                               apply (simp_all add: lib_pop_def pop_inv_def L3)
           apply(simp add: cobs_to_def new_node_def no_Top_n_a_def)
        apply (intro conjI impI allI)  
           apply (meson failed_CASR_pres_d_obs_lib)
           apply (meson failed_CASR_pres_d_obs_lib)
           apply (meson cvd_CAS_R_cvd)
           apply (metis CAS_Rel_preserves_value_old failed_CAS_Rel_preserves_writes_on_diff_var)
           using CAS_Rel_preserves_value_old failed_CAS_Rel_preserves_writes_on_diff_var apply auto[1]
           apply (metis agt_def clss_same failed_CASR_pres_c_obs_lib_only failed_cas_preserves_clss)
                 apply(elim conjE disjE exE)
           apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc ad2 =\<^sub>t vl \<rparr> cls")
           apply (meson failed_CASR_pres_c_obs_lib_only)
                    apply (metis agt_pushed_failed_cas_before_state agt_pushed_same2 same_except_for_pc_and_top_def)
           apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc ad2 =\<^sub>t vl \<rparr> cls")
           apply (meson failed_CASR_pres_c_obs_lib_only)
                    apply (metis agt_pushed_failed_cas_before_state agt_pushed_same2 same_except_for_pc_and_top_def)           
           apply (metis failed_CASR_pres_c_obs_lib_only)

                 apply (metis failed_CASR_pres_c_obs_lib_only)
                      apply(elim conjE exE)
                 apply(simp add: addr_init_writes_def written_vals_def new_node_def)
                 apply(intro conjI impI allI)
           apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' a
              = lib_value cls ` lib_writes_on cls a", simp add: globals glb_inv16_def)
           apply (metis CAS_Rel_preserves_value_diff_var failed_CAS_Rel_preserves_writes_on_diff_var image_cong)
                     apply (metis (no_types, lifting) CAS_Rel_preserves_value_diff_var failed_CAS_Rel_preserves_writes_on_diff_var image_cong)
           apply(intro conjI)
                          
           apply (meson failed_CASR_pres_d_obs_lib)
                          
           apply (meson failed_CASR_pres_d_obs_lib)
                          
           apply (meson cvd_CAS_R_cvd)
                                         apply(simp add: cobs_to_def new_node_def no_Top_n_a_def no_Top_n_def)

           using CAS_Rel_preserves_value_old failed_CAS_Rel_preserves_writes_on_diff_var apply force
           
                 apply (metis failed_CAS_Top_written_addr_post written_addr_def)
                apply(elim conjE exE)
                apply (meson cobs_to_CAS_pres)
           apply(simp add: written_vals_def)
           apply (smt CAS_Rel_preserves_value_diff_var failed_CAS_Rel_preserves_writes_on_diff_var image_cong)

        apply (intro conjI impI allI)  
           apply (meson failed_CASR_pres_d_obs_lib)
           apply (meson failed_CASR_pres_d_obs_lib)
                  apply (meson cvd_CAS_R_cvd)
                 apply (smt CAS_Rel_preserves_value_old failed_CAS_Rel_preserves_writes_on_diff_var no_Top_n_def)

           using cobs_to_CAS_pres apply blast
           
           using failed_CAS_Top_written_addr_post2 apply blast
           apply(simp add: written_vals_def)
           apply (smt failed_CAS_Rel_preserves_writes_on_diff_var image_iff write_value_CAS_R_diff_var)

        apply (intro conjI impI allI)  
           apply (meson failed_CASR_pres_d_obs_lib)
           apply (meson failed_CASR_pres_d_obs_lib)
                   apply (meson cvd_CAS_R_cvd)
           apply (smt CAS_Rel_preserves_value_old failed_CAS_Rel_preserves_writes_on_diff_var no_Top_n_def)
           using failed_CAS_Top_written_addr_post2 apply blast
               using cobs_to_CAS_pres apply blast
                   apply (meson failed_cas_dobs_to)
               using failed_CAS_Top_written_addr_post2 apply blast
               apply(simp add: written_vals_def)
               apply (smt failed_CAS_Rel_preserves_writes_on_diff_var image_iff write_value_CAS_R_diff_var)
               apply(intro conjI)
               apply (meson failed_CASR_pres_d_obs_lib)
                
               apply (metis d_obs_post_CAS_R_diff_var_post)

               using cvd_CAS_R_cvd apply blast
               using failed_CAS_preserves_last apply force
               apply (smt CAS_Rel_preserves_value_old failed_CAS_Rel_preserves_writes_on_diff_var no_Top_n_def)
                apply (metis cobs_to_CAS_pres)
                using failed_cas_dobs_to apply blast
                
                using failed_CAS_Top_written_addr_post2 apply blast
                using failed_CAS_Top_written_addr_post2 apply blast
                apply(simp add: written_vals_def)
                apply (smt failed_CAS_Rel_preserves_writes_on_diff_var image_iff write_value_CAS_R_diff_var)
                by (metis cobs_to_CAS_pres cvd_CAS_R_cvd failed_CASR_pres_d_obs_lib)
      next
        case True
        then show ?thesis
          using assms
               apply(subgoal_tac "top ps t'\<in>pushed_addr ps")
             apply(cases "pc ps t"; cases "pc ps' t"; cases "pc ps t'"; simp add: lib_pop_def pop_inv_def L3; elim conjE exE)
                apply(intro conjI)
          apply(simp add: new_node_def)
          apply (meson d_obs_post_CAS_R_diff_var_post)
                   apply (meson cvd_CAS_R_cvd)
                  apply(simp add: no_Top_n_a_def new_node_def)
                  apply(intro conjI impI allI, elim conjE)
          apply(simp add: globals)
          apply (metis CAS_Rel_new_write_value CAS_Rel_preserves_value_old)
          apply(simp add: globals)
                  apply (smt CAS_Rel_new_write_value CAS_Rel_preserves_value_old Zero_not_Suc subset_iff)
(***cobs_to begin***)
                 apply(simp add: cobs_to_def)
                 apply(intro allI impI conjI, elim disjE conjE)
                 apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
          apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_pres)
          apply (metis agt_pop_successful_cas_before3 assms(8) cvd_CAS_R_success_read_val not_gr_zero)
          apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
          apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_pres)
          apply (metis agt_pop_successful_cas_before3 assms(8) cvd_CAS_R_success_read_val not_gr_zero)
          apply(simp add: globals)
                    apply (metis gr_zeroI subsetD)
                   apply(case_tac "ad1 = ntop ps t'", simp)
          apply(subgoal_tac "agt (ntop ps t') ad2 ps cls")
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libad2 =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                       apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
          apply(subgoal_tac "agt (prog_state.top ps t') ad2 ps cls \<and> top ps t' \<noteq> Null")
                        apply(simp add: dobs_to_def)
                       apply(subgoal_tac "xa = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
          apply (metis cvd_CAS_R_success_read_val)
                      apply blast
          apply (metis agt_pop_successful_cas_before3 assms(8) cvd_CAS_R_success_read_val not_gr_zero)
                   apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast

          apply(subgoal_tac "xa = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)   


         (* apply (smt Un_Diff_cancel2 agt_add_n agt_pop_successful_cas_before3 agt_pushed_successful_cas_before assms(8) cvd_CAS_R_success_read_val inf_sup_aci(5) insert_Diff insert_iff insert_is_Un)*)
          apply simp
                   apply(subgoal_tac "agt ad1 (ntop ps t') ps cls")       
                    apply(subgoal_tac "agt  (ntop ps t') ad1 ps cls")
          apply (meson agt_def agt_order to_def to_p4_def)
           apply(subgoal_tac "agt  (top ps t') ad1 ps cls")
          using nothing_between_a_nxt lastNxtVal_def lastVal_def
          apply (metis add.commute assms(8) plus_1_eq_Suc)
          apply (smt Null_def TopLV_agt_others assms(8) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr_zero)
          apply (metis agt_pop_successful_cas_before3 assms(8) cvd_CAS_R_success_read_val not_gr_zero)
                   apply(case_tac "ad1 = ntop ps t'", simp)
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libad2 =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                      apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
                apply(simp add: globals to_simps)
    using dobs_to_def cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write
                   apply (smt Null_def not_gr_zero)
             apply simp
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
            apply blast
    apply(elim conjE disjE)
     apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
               apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
    apply(simp add: globals)
          apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)
          apply (metis agt_pop_successful_cas_before3 assms(8) cvd_CAS_R_success_read_val not_gr_zero)
          apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
               apply(simp add: globals)
     apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)
          apply (metis agt_pop_successful_cas_before3 assms(8) cvd_CAS_R_success_read_val not_gr_zero)
          apply(simp add: globals)
                    apply (metis gr_zeroI subsetD)
                   apply(case_tac "ad1 = ntop ps t'", simp)
          apply(subgoal_tac "agt (ntop ps t') ad2 ps cls")
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
           apply(simp add: globals)
   using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                       apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
          apply(subgoal_tac "agt (prog_state.top ps t') ad2 ps cls \<and> top ps t' \<noteq> Null")
                        apply(simp add: dobs_to_def)
                       apply(subgoal_tac "xa = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
          apply (metis cvd_CAS_R_success_read_val)
                      apply blast
          apply (metis agt_pop_successful_cas_before3 assms(8) cvd_CAS_R_success_read_val not_gr_zero)
                   apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast 
          
          apply(subgoal_tac "xa = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
                   apply (metis cvd_CAS_R_success_read_val)   
                  
                  apply simp
                   apply(subgoal_tac "agt ad1 (ntop ps t') ps cls")       
                    apply(subgoal_tac "agt  (ntop ps t') ad1 ps cls")
          apply (meson agt_def agt_order to_def to_p4_def)
           apply(subgoal_tac "agt  (top ps t') ad1 ps cls")
          using nothing_between_a_nxt lastNxtVal_def lastVal_def
          apply (metis add.commute assms(8) plus_1_eq_Suc)
          apply (smt Null_def TopLV_agt_others assms(8) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr_zero)
          apply (metis agt_pop_successful_cas_before3 assms(8) cvd_CAS_R_success_read_val not_gr_zero)
                   apply(case_tac "ad1 = ntop ps t'", simp)
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                      apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
                apply(simp add: globals to_simps)
    using dobs_to_def cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write
                   apply (smt Null_def not_gr_zero)
             apply simp
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
            apply blast
 (***end cobs_to proof***) 
          apply(simp add: addr_init_writes_def written_vals_def new_node_def globals)
          apply(intro allI impI conjI)
    apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' a = lib_value cls ` lib_writes_on cls a")
    apply metis
    apply (metis (no_types, lifting) CAS_Rel_preserves_writes_on_diff_var image_cong write_value_CAS_R_diff_var)
    apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' (Suc a) = lib_value cls ` lib_writes_on cls (Suc a)")
  apply metis
          apply (metis (no_types, lifting) CAS_Rel_preserves_writes_on_diff_var image_cong write_value_CAS_R_diff_var)
         apply(intro conjI)
    apply (metis d_obs_post_CAS_R_diff_var_post)
    
                apply (metis d_obs_post_CAS_R_diff_var_post)
    apply auto[1]
    apply (meson cvd_CAS_R_cvd)
             apply simp
    apply(simp add: no_Top_n_def globals)
            apply (smt CAS_Rel_new_write_value CAS_Rel_preserves_value_old gr_zeroI)
    apply(simp add: globals)
    apply (metis CAS_Top_written_addr_post gr_zeroI)
          defer   
    apply(simp add: written_vals_def)
          apply (smt CAS_Rel_preserves_value_diff_var CAS_Rel_preserves_writes_on_diff_var image_cong)
         apply(intro conjI allI impI)
                 apply (metis d_obs_post_CAS_R_diff_var_post)
    apply(subgoal_tac "Suc (n_val ps t) \<noteq> Top")
      apply (metis d_obs_post_CAS_R_diff_var_post)
  apply(simp add: globals)
                apply metis
       apply auto[1]
       apply (meson cvd_CAS_R_cvd)
       apply simp
     apply(simp add: no_Top_n_def globals)
            apply (smt CAS_Rel_new_write_value CAS_Rel_preserves_value_old gr_zeroI)
           defer
    apply(simp add:  globals)
   apply (metis CAS_Top_written_addr_post gr_zeroI)
          apply(simp add:  globals written_vals_def glb_inv16_def)
    apply(subgoal_tac "lib_value cls' `
            lib_writes_on cls' (Suc (n_val ps t)) = lib_value cls `
            lib_writes_on cls (Suc (n_val ps t))")
   apply metis
   apply (metis (no_types, lifting) CAS_Rel_preserves_writes_on_diff_var image_cong write_value_CAS_R_diff_var)
          apply(intro conjI allI impI)
  apply (metis d_obs_post_CAS_R_diff_var_post)
    apply(subgoal_tac "Suc (n_val ps t) \<noteq> Top")
      apply (metis d_obs_post_CAS_R_diff_var_post)
  apply(simp add: globals)
                apply metis
  apply simp
  apply (meson cvd_CAS_R_cvd)
               apply auto[1]
    apply(simp add: no_Top_n_def)
              apply(intro  allI impI)
              apply(subgoal_tac "lib_value cls' `(lib_writes_on cls' Top) = lib_value cls `(lib_writes_on cls Top) \<union> {ntop ps t'}")
    apply(simp add: globals written_addr_def)
  apply (metis gr_zeroI image_eqI insert_iff)
              apply (simp add: success_CAS_Top_written_addr_post)
             apply simp 
    apply(case_tac "ntop ps t' = 0")
    apply(subgoal_tac "written_addr cls' = written_addr cls")
              apply blast
              apply(simp add: globals written_addr_def)
    apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' Top = lib_value cls ` lib_writes_on cls Top \<union> {ntop ps t'}")
    apply (metis Diff_insert_absorb Un_Diff Un_empty_right empty_iff)
    apply (metis success_CAS_Top_written_addr_post)
    using success_CAS_Top_written_addr_post2 apply auto[1]
            defer
            apply(simp add: dobs_to_def)
            apply(intro allI impI, elim conjE disjE)
    apply(case_tac "top ps t \<noteq> top ps t'")
               apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
                apply(intro conjI)
                 apply(subgoal_tac " \<exists>vl. [libad =\<^sub>t vl] cls", elim exE, rule_tac x=vl in exI)
    apply(subgoal_tac "ad \<noteq> Top")
    apply (meson d_obs_post_CAS_R_diff_var_post)
                  apply(simp add: globals)    
                  apply (meson subset_iff)
    apply blast
                 apply(subgoal_tac " \<exists>vl. [libSuc(ad) =\<^sub>t vl] cls", elim exE, rule_tac x=vl in exI)
    apply(subgoal_tac "Suc(ad) \<noteq> Top")
    apply (meson d_obs_post_CAS_R_diff_var_post)
                  apply(simp add: globals)    
                   
    apply metis
                apply blast
               apply(simp add: globals) 
                apply(subgoal_tac "top ps t\<in>pushed_addr ps")

    apply (metis agt_pop_successful_cas_before3 assms(10) assms(7) assms(8) cvd_CAS_R_success_read_val)
    apply(subgoal_tac "top ps t \<in> pushed_addr ps'")
                apply (metis DiffE)
  apply(simp add: agt_def clss_def nxt_rel_def trancl_def)
  using converse_tranclpE      
  apply (metis (no_types, lifting))
  apply(simp add: agt_def clss_def nxt_rel_def trancl_def)
  using converse_tranclpE
  apply smt
  apply(subgoal_tac "ad \<noteq> Top \<and> Suc ad \<noteq> Top \<and> (\<exists>vl. [libad =\<^sub>t vl] cls) \<and>
       (\<exists>vl. [libSuc ad =\<^sub>t vl] cls)")
             apply(elim conjE exE, intro conjI)
  apply (meson d_obs_post_CAS_R_diff_var_post)
             apply(rule_tac x=vla in exI)
             apply (meson d_obs_post_CAS_R_diff_var_post)
                apply(simp add: globals) 
 apply(intro conjI)
   apply (metis subset_iff)
            apply metis
(***)
      apply(case_tac "top ps t \<noteq> top ps t'")
               apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
                apply(intro conjI)
                 apply(subgoal_tac " \<exists>vl. [libad =\<^sub>t vl] cls", elim exE, rule_tac x=vl in exI)
    apply(subgoal_tac "ad \<noteq> Top")
    apply (meson d_obs_post_CAS_R_diff_var_post)
                  apply(simp add: globals)    
                  apply (meson subset_iff)
    apply blast
                 apply(subgoal_tac " \<exists>vl. [libSuc(ad) =\<^sub>t vl] cls", elim exE, rule_tac x=vl in exI)
    apply(subgoal_tac "Suc(ad) \<noteq> Top")
    apply (meson d_obs_post_CAS_R_diff_var_post)
                  apply(simp add: globals)    
                   
    apply metis
                apply blast
               apply(simp add: globals) 
    apply(subgoal_tac "top ps t\<in>pushed_addr ps")
  
  apply (metis agt_pop_successful_cas_before3 assms(10) assms(7) assms(8) cvd_CAS_R_success_read_val)
             apply(subgoal_tac "top ps t \<in> pushed_addr ps'")
                apply (metis DiffE)
  apply(simp add: agt_def clss_def nxt_rel_def trancl_def)
  using converse_tranclpE      
  apply (metis (no_types, lifting))
  apply(simp add: agt_def clss_def nxt_rel_def trancl_def)
  using converse_tranclpE
  apply smt
  apply(subgoal_tac "ad \<noteq> Top \<and> Suc ad \<noteq> Top \<and> (\<exists>vl. [libad =\<^sub>t vl] cls) \<and>
       (\<exists>vl. [libSuc ad =\<^sub>t vl] cls)")
             apply(elim conjE exE, intro conjI)
  apply (meson d_obs_post_CAS_R_diff_var_post)
             apply(rule_tac x=vla in exI)
             apply (meson d_obs_post_CAS_R_diff_var_post)
                apply(simp add: globals) 
 apply(intro conjI)
   apply (metis subset_iff)
            apply metis
  apply(simp add: globals)
         apply (metis CAS_Top_written_addr_post gr_zeroI)
        apply(simp add: written_vals_def)
  apply(subgoal_tac "lib_value cls' `
            lib_writes_on cls' (Suc (n_val ps t)) = lib_value cls `
            lib_writes_on cls (Suc (n_val ps t))")
  apply auto[1]
  apply (metis (no_types, lifting) CAS_Rel_preserves_value_diff_var CAS_Rel_preserves_writes_on_diff_var image_cong)
       apply(intro conjI)
  apply (metis d_obs_post_CAS_R_diff_var_post)
   
                 apply (metis d_obs_post_CAS_R_diff_var_post)
  
  apply simp
  
  apply (meson cvd_CAS_R_cvd)
  apply (metis succ_CAS_preserves_last)
             apply simp
    apply(simp add: no_Top_n_def)
              apply(intro  allI impI)
              apply(subgoal_tac "lib_value cls' `(lib_writes_on cls' Top) = lib_value cls `(lib_writes_on cls Top) \<union> {ntop ps t'}")
    apply(simp add: globals written_addr_def)
  apply (metis gr_zeroI image_eqI insert_iff)
              apply (simp add: success_CAS_Top_written_addr_post)
           apply simp 
           defer
(***dobs_to***)
  apply(simp add: dobs_to_def)
            apply(intro allI impI, elim conjE disjE)
    apply(case_tac "top ps t \<noteq> top ps t'")
               apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
                apply(intro conjI)
                 apply(subgoal_tac " \<exists>vl. [libad =\<^sub>t vl] cls", elim exE, rule_tac x=vl in exI)
    apply(subgoal_tac "ad \<noteq> Top")
    apply (meson d_obs_post_CAS_R_diff_var_post)
                  apply(simp add: globals)    
                  apply (meson subset_iff)
    apply blast
                 apply(subgoal_tac " \<exists>vl. [libSuc(ad) =\<^sub>t vl] cls", elim exE, rule_tac x=vl in exI)
    apply(subgoal_tac "Suc(ad) \<noteq> Top")
    apply (meson d_obs_post_CAS_R_diff_var_post)
                  apply(simp add: globals)    
                   
    apply metis
                apply blast
               apply(simp add: globals) 
    apply(subgoal_tac "top ps t\<in>pushed_addr ps")
  
  apply (metis agt_pop_successful_cas_before3 assms(10) assms(7) assms(8) cvd_CAS_R_success_read_val)
               apply(subgoal_tac "top ps t \<in> pushed_addr ps'")
                apply (metis DiffE)
  apply(simp add: agt_def clss_def nxt_rel_def trancl_def)
  using converse_tranclpE      
  apply (metis (no_types, lifting))
  apply(simp add: agt_def clss_def nxt_rel_def trancl_def)
  using converse_tranclpE
  apply smt
  apply(subgoal_tac "ad \<noteq> Top \<and> Suc ad \<noteq> Top \<and> (\<exists>vl. [libad =\<^sub>t vl] cls) \<and>
       (\<exists>vl. [libSuc ad =\<^sub>t vl] cls)")
             apply(elim conjE exE, intro conjI)
  apply (meson d_obs_post_CAS_R_diff_var_post)
             apply(rule_tac x=vla in exI)
             apply (meson d_obs_post_CAS_R_diff_var_post)
                apply(simp add: globals) 
 apply(intro conjI)
   apply (metis subset_iff)
            apply metis
      apply(case_tac "top ps t \<noteq> top ps t'")
               apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
                apply(intro conjI)
                 apply(subgoal_tac " \<exists>vl. [libad =\<^sub>t vl] cls", elim exE, rule_tac x=vl in exI)
    apply(subgoal_tac "ad \<noteq> Top")
    apply (meson d_obs_post_CAS_R_diff_var_post)
                  apply(simp add: globals)    
                  apply (meson subset_iff)
    apply blast
                 apply(subgoal_tac " \<exists>vl. [libSuc(ad) =\<^sub>t vl] cls", elim exE, rule_tac x=vl in exI)
    apply(subgoal_tac "Suc(ad) \<noteq> Top")
    apply (meson d_obs_post_CAS_R_diff_var_post)
                  apply(simp add: globals)    
                   
    apply metis
                apply blast
               apply(simp add: globals) 
    apply(subgoal_tac "top ps t\<in>pushed_addr ps")
  apply (metis agt_pop_successful_cas_before3 assms(10) assms(7) assms(8) cvd_CAS_R_success_read_val)
    apply(subgoal_tac "top ps t \<in> pushed_addr ps'")
                apply (metis DiffE)
  apply(simp add: agt_def clss_def nxt_rel_def trancl_def)
  using converse_tranclpE      
  apply (metis (no_types, lifting))
  apply(simp add: agt_def clss_def nxt_rel_def trancl_def)
  using converse_tranclpE
  apply smt
  apply(subgoal_tac "ad \<noteq> Top \<and> Suc ad \<noteq> Top \<and> (\<exists>vl. [libad =\<^sub>t vl] cls) \<and>
       (\<exists>vl. [libSuc ad =\<^sub>t vl] cls)")
             apply(elim conjE exE, intro conjI)
  apply (meson d_obs_post_CAS_R_diff_var_post)
             apply(rule_tac x=vla in exI)
             apply (meson d_obs_post_CAS_R_diff_var_post)
                apply(simp add: globals) 
 apply(intro conjI)
   apply (metis subset_iff)
            apply metis
  apply(simp add: globals)
          apply (metis CAS_Top_written_addr_post gr_zeroI)
(***end of dobs_to***)
         apply(intro impI)
    apply(case_tac "ntop ps t' = 0")
    apply(subgoal_tac "written_addr cls' = written_addr cls")
              apply blast
              apply(simp add: globals written_addr_def)
    apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' Top = lib_value cls ` lib_writes_on cls Top \<union> {ntop ps t'}")
    apply (metis Diff_insert_absorb Un_Diff Un_empty_right empty_iff)
    apply (metis success_CAS_Top_written_addr_post)
    using success_CAS_Top_written_addr_post2 apply auto[1]
          apply(intro allI impI)
    apply(subgoal_tac "written_vals cls' (Suc (n_val ps t)) = written_vals cls (Suc (n_val ps t))")
           apply simp
    apply(simp add: written_vals_def)
  apply (metis (no_types, lifting) CAS_Rel_preserves_value_diff_var CAS_Rel_preserves_writes_on_diff_var image_cong)
         apply(intro conjI)
  apply (metis d_obs_post_CAS_R_diff_var_post)
  apply (metis d_obs_post_CAS_R_diff_var_post)
  apply simp
  apply (meson cvd_CAS_R_cvd)
          apply simp

(***cobs_to begin***)
                 apply(simp add: cobs_to_def)
                 apply(intro allI impI conjI, elim disjE conjE)
                 apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
          apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_pres)
     
    apply (metis agt_pop_successful_cas_before3 assms(8) cvd_CAS_R_success_read_val not_gr_zero)
    apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
          apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_pres)
  apply (metis agt_pop_successful_cas_before3 assms(10) assms(7) assms(8) cvd_CAS_R_success_read_val)
          apply(simp add: globals)
                    apply (metis gr_zeroI subsetD)
                   apply(case_tac "ad1 = ntop ps t'", simp)
          apply(subgoal_tac "agt (ntop ps t') ad2 ps cls")
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libad2 =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals) 
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                       apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
          apply(subgoal_tac "agt (prog_state.top ps t') ad2 ps cls \<and> top ps t' \<noteq> Null")
                        apply(simp add: dobs_to_def)
                       apply(subgoal_tac "xa = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
          apply (metis cvd_CAS_R_success_read_val)
                      apply blast
  apply (metis agt_pop_successful_cas_before3 assms(10) assms(7) assms(8) cvd_CAS_R_success_read_val)
                   apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                   apply blast
          apply(subgoal_tac "xa = top ps t'")
          using agt_pop_successful_cas_before3[where ccs=ccs and ccs'=ccs' and cls'=cls' and cls=cls] 
          apply(subgoal_tac "xa = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
                   apply (metis cvd_CAS_R_success_read_val)   
                  apply (metis cvd_CAS_R_success_read_val) 
          apply simp
                   apply(subgoal_tac "agt ad1 (ntop ps t') ps cls")       
                    apply(subgoal_tac "agt  (ntop ps t') ad1 ps cls")
          apply (meson agt_def agt_order to_def to_p4_def)
           apply(subgoal_tac "agt  (top ps t') ad1 ps cls")
          using nothing_between_a_nxt lastNxtVal_def lastVal_def
          apply (metis add.commute assms(8) plus_1_eq_Suc)
          apply (smt Null_def TopLV_agt_others assms(8) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr_zero)
          using agt_pop_successful_cas_before3 
          apply (metis assms(8) cvd_CAS_R_success_read_val)
                   apply(case_tac "ad1 = ntop ps t'", simp)
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libad2 =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                      apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
                apply(simp add: globals to_simps)
    using dobs_to_def cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write
                   apply (smt Null_def not_gr_zero)
             apply simp
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
            apply blast
    apply(elim conjE disjE)
     apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
               apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
    apply(simp add: globals)
          apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)
using agt_pop_successful_cas_before3 
  apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)
          apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
               apply(simp add: globals)
     apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)
using agt_pop_successful_cas_before3 
        apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)
       apply(simp add: globals)
                    apply (metis gr_zeroI subsetD)
                   apply(case_tac "ad1 = ntop ps t'", simp)
          apply(subgoal_tac "agt (ntop ps t') ad2 ps cls")
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
           apply(simp add: globals)
   using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                       apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
          apply(subgoal_tac "agt (prog_state.top ps t') ad2 ps cls \<and> top ps t' \<noteq> Null")
                        apply(simp add: dobs_to_def)
                       apply(subgoal_tac "xa = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
          apply (metis cvd_CAS_R_success_read_val)
                      apply blast
          using  agt_pop_successful_cas_before3
          apply (metis assms(8) cvd_CAS_R_success_read_val)
                   apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                  apply blast
          apply(subgoal_tac "xa = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)   

                   apply simp
              apply(subgoal_tac "agt ad1 (ntop ps t') ps cls")       
                    apply(subgoal_tac "agt  (ntop ps t') ad1 ps cls")
          apply (meson agt_def agt_order to_def to_p4_def)
           apply(subgoal_tac "agt  (top ps t') ad1 ps cls")
          using nothing_between_a_nxt lastNxtVal_def lastVal_def
          apply (metis add.commute assms(8) plus_1_eq_Suc)
          apply (smt Null_def TopLV_agt_others assms(8) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr_zero)
          using agt_pop_successful_cas_before3
          apply (metis assms(8) cvd_CAS_R_success_read_val)
                   apply(case_tac "ad1 = ntop ps t'", simp)
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                      apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
                apply(simp add: globals to_simps)
    using dobs_to_def cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write
                   apply (smt Null_def not_gr_zero)
             apply simp
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
            apply blast
 (***end cobs_to proof***) 
    defer
(***cobs_to begin***)
                 apply(simp add: cobs_to_def)
                 apply(intro allI impI conjI, elim disjE conjE)
                 apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
          apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_pres)
    using agt_pop_successful_cas_before3 
    apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)
          apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
          apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_pres)
    using agt_pop_successful_cas_before3 
            apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)
           apply(simp add: globals)
                    apply (metis gr_zeroI subsetD)
                   apply(case_tac "ad1 = ntop ps t'", simp)
          apply(subgoal_tac "agt (ntop ps t') ad2 ps cls")
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libad2 =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                       apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
          apply(subgoal_tac "agt (prog_state.top ps t') ad2 ps cls \<and> top ps t' \<noteq> Null")
                        apply(simp add: dobs_to_def)
                       apply(subgoal_tac "xa = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
                   apply (metis cvd_CAS_R_success_read_val)
          apply auto[1]
    using agt_pop_successful_cas_before3 
    apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)                   apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast
          apply(subgoal_tac "xa = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)   

           apply(subgoal_tac "agt ad1 (ntop ps t') ps cls")       
                    apply(subgoal_tac "agt  (ntop ps t') ad1 ps cls")
          apply (meson agt_def agt_order to_def to_p4_def)
           apply(subgoal_tac "agt  (top ps t') ad1 ps cls")
          using nothing_between_a_nxt lastNxtVal_def lastVal_def
          apply (metis add.commute assms(8) plus_1_eq_Suc)
          apply (smt Null_def TopLV_agt_others assms(8) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr_zero)
    using agt_pop_successful_cas_before3 
    apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)                   apply(case_tac "ad1 = ntop ps t'", simp)
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libad2 =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                      apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
                apply(simp add: globals to_simps)
    using dobs_to_def cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write
                   apply (smt Null_def not_gr_zero)
             apply simp
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
            apply blast
    apply(elim conjE disjE)
     apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
               apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
    apply(simp add: globals)
          apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)
    using agt_pop_successful_cas_before3 
    apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)          apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
               apply(simp add: globals)
     apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)
    using agt_pop_successful_cas_before3 
           apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)
          apply(simp add: globals)
                    apply (metis gr_zeroI subsetD)
                   apply(case_tac "ad1 = ntop ps t'", simp)
          apply(subgoal_tac "agt (ntop ps t') ad2 ps cls")
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
           apply(simp add: globals)
   using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                       apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
          apply(subgoal_tac "agt (prog_state.top ps t') ad2 ps cls \<and> top ps t' \<noteq> Null")
                        apply(simp add: dobs_to_def)
                       apply(subgoal_tac "xa = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
                  apply (metis cvd_CAS_R_success_read_val)
          apply auto[1]
    using agt_pop_successful_cas_before3 
          apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)
         apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast

          apply(subgoal_tac "xa = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)   
          apply simp
                   apply(subgoal_tac "agt ad1 (ntop ps t') ps cls")       
                    apply(subgoal_tac "agt  (ntop ps t') ad1 ps cls")
          apply (meson agt_def agt_order to_def to_p4_def)
           apply(subgoal_tac "agt  (top ps t') ad1 ps cls")
          using nothing_between_a_nxt lastNxtVal_def lastVal_def
          apply (metis add.commute assms(8) plus_1_eq_Suc)
          apply (smt Null_def TopLV_agt_others assms(8) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr_zero)
          using agt_pop_successful_cas_before3
          apply (metis assms(8) cvd_CAS_R_success_read_val)
                   apply(case_tac "ad1 = ntop ps t'", simp)
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                      apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
                apply(simp add: globals to_simps)
    using dobs_to_def cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write
                   apply (smt Null_def not_gr_zero)
             apply simp
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
            apply blast
 (***end cobs_to proof***) 
(***cobs_to begin***)
                 apply(simp add: cobs_to_def)
                 apply(intro allI impI conjI, elim disjE conjE)
                 apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
          apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_pres)
          using agt_pop_successful_cas_before3
          apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)
                  apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
          apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_pres)
          using agt_pop_successful_cas_before3
                 apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)
                apply(simp add: globals)
                    apply (metis gr_zeroI subsetD)
                   apply(case_tac "ad1 = ntop ps t'", simp)
          apply(subgoal_tac "agt (ntop ps t') ad2 ps cls")
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libad2 =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                       apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
          apply(subgoal_tac "agt (prog_state.top ps t') ad2 ps cls \<and> top ps t' \<noteq> Null")
                        apply(simp add: dobs_to_def)
                       apply(subgoal_tac "xb = top ps t'")
          apply(simp add:  to_def to_p2_def )
                   apply (simp add: lastTop_def)
          apply (metis  lib_cvd_exist_last_write)
       apply (metis cvd_CAS_R_success_read_val)
          apply auto[1]
          using agt_pop_successful_cas_before3
          apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)                   apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast
        
                   apply(subgoal_tac "xb = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
                 apply (metis cvd_CAS_R_success_read_val)   

                apply(subgoal_tac "agt ad1 (ntop ps t') ps cls")       
                    apply(subgoal_tac "agt  (ntop ps t') ad1 ps cls")
          apply (meson agt_def agt_order to_def to_p4_def)
           apply(subgoal_tac "agt  (top ps t') ad1 ps cls")
          using nothing_between_a_nxt lastNxtVal_def lastVal_def
          apply (metis add.commute assms(8) plus_1_eq_Suc)
          apply (smt Null_def TopLV_agt_others assms(8) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr_zero)
          using agt_pop_successful_cas_before3
          apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)                   apply(case_tac "ad1 = ntop ps t'", simp)
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libad2 =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                      apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
                apply(simp add: globals to_simps)
    using dobs_to_def cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write
                   apply (smt Null_def not_gr_zero)
             apply simp
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
            apply blast
    apply(elim conjE disjE)
     apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
               apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
    apply(simp add: globals)
          apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)
          using agt_pop_successful_cas_before3
                 apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)
                apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
               apply(simp add: globals)
     apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)
          using agt_pop_successful_cas_before3
          apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)
                apply(simp add: globals)
                    apply (metis gr_zeroI subsetD)
                   apply(case_tac "ad1 = ntop ps t'", simp)
          apply(subgoal_tac "agt (ntop ps t') ad2 ps cls")
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
           apply(simp add: globals)
   using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                       apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
          apply(subgoal_tac "agt (prog_state.top ps t') ad2 ps cls \<and> top ps t' \<noteq> Null")
                        apply(simp add: dobs_to_def)
                       apply(subgoal_tac "xb = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
                  apply (metis cvd_CAS_R_success_read_val)
          apply auto[1]
          using agt_pop_successful_cas_before3
          apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)        
          apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
          apply blast

       apply(subgoal_tac "xb = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
               apply (metis cvd_CAS_R_success_read_val)   

               apply(subgoal_tac "agt ad1 (ntop ps t') ps cls")       
                    apply(subgoal_tac "agt  (ntop ps t') ad1 ps cls")
          apply (meson agt_def agt_order to_def to_p4_def)
           apply(subgoal_tac "agt  (top ps t') ad1 ps cls")
          using nothing_between_a_nxt lastNxtVal_def lastVal_def
          apply (metis add.commute assms(8) plus_1_eq_Suc)
          apply (smt Null_def TopLV_agt_others assms(8) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr_zero)
          using agt_pop_successful_cas_before3
          apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero) 
          apply(case_tac "ad1 = ntop ps t'", simp)
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                      apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
                apply(simp add: globals to_simps)
    using dobs_to_def cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write
                   apply (smt Null_def not_gr_zero)
             apply simp
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
            apply blast
 (***end cobs_to proof***) 
(***cobs_to begin***)
                 apply(simp add: cobs_to_def)
                 apply(intro allI impI conjI, elim disjE conjE)
                 apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
          apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_pres)
          using agt_pop_successful_cas_before3
          apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)
          apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
          apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_pres)
                apply (metis)
               apply(simp add: globals)
                    apply (metis gr_zeroI subsetD)
                   apply(case_tac "ad1 = ntop ps t'", simp)
          apply(subgoal_tac "agt (ntop ps t') ad2 ps cls")
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libad2 =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                       apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
          apply(subgoal_tac "agt (prog_state.top ps t') ad2 ps cls \<and> top ps t' \<noteq> Null")
                        apply(simp add: dobs_to_def)
                       apply(subgoal_tac "xb = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
                   apply (metis cvd_CAS_R_success_read_val)
          apply auto[1]
          using agt_pop_successful_cas_before3
          apply (metis assms(8) cvd_CAS_R_success_read_val not_gr_zero)
                   apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast

       apply(subgoal_tac "xb = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
                 apply (metis cvd_CAS_R_success_read_val)   
               apply(subgoal_tac "agt ad1 (ntop ps t') ps cls")
          apply(subgoal_tac "agt  (ntop ps t') ad1 ps cls")
          apply (meson agt_def agt_order to_def to_p4_def)
           apply(subgoal_tac "agt  (top ps t') ad1 ps cls")
          using nothing_between_a_nxt lastNxtVal_def lastVal_def
          apply (metis add.commute assms(8) plus_1_eq_Suc)
          apply (smt Null_def TopLV_agt_others assms(8) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr_zero)
          apply (metis \<open>\<And>u' u t ps' ps d ca. \<lbrakk>lib_wfs cls ccs; glb_inv ps cls; glb ps cls; to ps cls; cvd[libTop, u] cls; cls ccs CAS\<^sup>R[libTop, True, u, u']\<^sub>t cls' ccs'; u \<noteq> u'; ca \<in> pushed_addr ps; d \<in> pushed_addr ps; u \<noteq> ca; u \<noteq> d; agt ca d ps' cls'; pushed_addr ps' = pushed_addr ps - {u}\<rbrakk> \<Longrightarrow> agt ca d ps cls\<close> assms(8) cvd_CAS_R_success_read_val)
                   apply(case_tac "ad1 = ntop ps t'", simp)
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libad2 =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                      apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
                apply(simp add: globals to_simps)
    using dobs_to_def cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write
                   apply (smt Null_def not_gr_zero)
             apply simp
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
            apply blast
    apply(elim conjE disjE)
     apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
               apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
    apply(simp add: globals)
          apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)                        
    apply (metis \<open>\<And>u' u t ps' ps d ca. \<lbrakk>lib_wfs cls ccs; glb_inv ps cls; glb ps cls; to ps cls; cvd[libTop, u] cls; cls ccs CAS\<^sup>R[libTop, True, u, u']\<^sub>t cls' ccs'; u \<noteq> u'; ca \<in> pushed_addr ps; d \<in> pushed_addr ps; u \<noteq> ca; u \<noteq> d; agt ca d ps' cls'; pushed_addr ps' = pushed_addr ps - {u}\<rbrakk> \<Longrightarrow> agt ca d ps cls\<close> assms(8) cvd_CAS_R_success_read_val neq0_conv)
          apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
               apply(simp add: globals)
     apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)
    apply (metis \<open>\<And>u' u t ps' ps d ca. \<lbrakk>lib_wfs cls ccs; glb_inv ps cls; glb ps cls; to ps cls; cvd[libTop, u] cls; cls ccs CAS\<^sup>R[libTop, True, u, u']\<^sub>t cls' ccs'; u \<noteq> u'; ca \<in> pushed_addr ps; d \<in> pushed_addr ps; u \<noteq> ca; u \<noteq> d; agt ca d ps' cls'; pushed_addr ps' = pushed_addr ps - {u}\<rbrakk> \<Longrightarrow> agt ca d ps cls\<close> assms(8) cvd_CAS_R_success_read_val neq0_conv)
          apply(simp add: globals)
                    apply (metis gr_zeroI subsetD)
                   apply(case_tac "ad1 = ntop ps t'", simp)
          apply(subgoal_tac "agt (ntop ps t') ad2 ps cls")
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
           apply(simp add: globals)
   using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                       apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
          apply(subgoal_tac "agt (prog_state.top ps t') ad2 ps cls \<and> top ps t' \<noteq> Null")
                        apply(simp add: dobs_to_def)
                       apply(subgoal_tac "xb = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
                  apply (metis cvd_CAS_R_success_read_val)
          apply auto[1]
    apply (metis \<open>\<And>u' u t ps' ps d ca. \<lbrakk>lib_wfs cls ccs; glb_inv ps cls; glb ps cls; to ps cls; cvd[libTop, u] cls; cls ccs CAS\<^sup>R[libTop, True, u, u']\<^sub>t cls' ccs'; u \<noteq> u'; ca \<in> pushed_addr ps; d \<in> pushed_addr ps; u \<noteq> ca; u \<noteq> d; agt ca d ps' cls'; pushed_addr ps' = pushed_addr ps - {u}\<rbrakk> \<Longrightarrow> agt ca d ps cls\<close> assms(8) cvd_CAS_R_success_read_val neq0_conv)
                   apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast
                 apply(subgoal_tac "xb = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
                 apply (metis cvd_CAS_R_success_read_val)   
              apply simp
                   apply(subgoal_tac "agt ad1 (ntop ps t') ps cls")       
                    apply(subgoal_tac "agt  (ntop ps t') ad1 ps cls")
          apply (meson agt_def agt_order to_def to_p4_def)
           apply(subgoal_tac "agt  (top ps t') ad1 ps cls")
          using nothing_between_a_nxt lastNxtVal_def lastVal_def
          apply (metis add.commute assms(8) plus_1_eq_Suc)
          apply (smt Null_def TopLV_agt_others assms(8) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr_zero)
          
          apply (metis \<open>\<And>u' u t ps' ps d ca. \<lbrakk>lib_wfs cls ccs; glb_inv ps cls; glb ps cls; to ps cls; cvd[libTop, u] cls; cls ccs CAS\<^sup>R[libTop, True, u, u']\<^sub>t cls' ccs'; u \<noteq> u'; ca \<in> pushed_addr ps; d \<in> pushed_addr ps; u \<noteq> ca; u \<noteq> d; agt ca d ps' cls'; pushed_addr ps' = pushed_addr ps - {u}\<rbrakk> \<Longrightarrow> agt ca d ps cls\<close> assms(8) cvd_CAS_R_success_read_val)
          apply(case_tac "ad1 = ntop ps t'", simp)
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                      apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
                apply(simp add: globals to_simps)
    using dobs_to_def cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write
                   apply (smt Null_def not_gr_zero)
             apply simp
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
            apply blast
 (***end cobs_to proof***) 
(***cobs_to begin***)
                 apply(simp add: cobs_to_def)
                 apply(intro allI impI conjI, elim disjE conjE)
                 apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
          apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_pres)
    
    apply (metis \<open>\<And>u' u t ps' ps d ca. \<lbrakk>lib_wfs cls ccs; glb_inv ps cls; glb ps cls; to ps cls; cvd[libTop, u] cls; cls ccs CAS\<^sup>R[libTop, True, u, u']\<^sub>t cls' ccs'; u \<noteq> u'; ca \<in> pushed_addr ps; d \<in> pushed_addr ps; u \<noteq> ca; u \<noteq> d; agt ca d ps' cls'; pushed_addr ps' = pushed_addr ps - {u}\<rbrakk> \<Longrightarrow> agt ca d ps cls\<close> assms(8) cvd_CAS_R_success_read_val neq0_conv)
    apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
          apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_pres)
    
    apply simp
    apply(simp add: globals)
                    apply (metis gr_zeroI subsetD)
                   apply(case_tac "ad1 = ntop ps t'", simp)
          apply(subgoal_tac "agt (ntop ps t') ad2 ps cls")
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libad2 =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                       apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
          apply(subgoal_tac "agt (prog_state.top ps t') ad2 ps cls \<and> top ps t' \<noteq> Null")
                        apply(simp add: dobs_to_def)
                       apply(subgoal_tac "xa = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
                   apply (metis cvd_CAS_R_success_read_val)
          apply auto[1]
          apply (metis \<open>\<And>u' u t ps' ps d ca. \<lbrakk>lib_wfs cls ccs; glb_inv ps cls; glb ps cls; to ps cls; cvd[libTop, u] cls; cls ccs CAS\<^sup>R[libTop, True, u, u']\<^sub>t cls' ccs'; u \<noteq> u'; ca \<in> pushed_addr ps; d \<in> pushed_addr ps; u \<noteq> ca; u \<noteq> d; agt ca d ps' cls'; pushed_addr ps' = pushed_addr ps - {u}\<rbrakk> \<Longrightarrow> agt ca d ps cls\<close> assms(8) cvd_CAS_R_success_read_val)
          apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
               apply blast

       apply(subgoal_tac "xa = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)   

               apply simp
                   apply(subgoal_tac "agt ad1 (ntop ps t') ps cls")       
                    apply(subgoal_tac "agt  (ntop ps t') ad1 ps cls")
          apply (meson agt_def agt_order to_def to_p4_def)
           apply(subgoal_tac "agt  (top ps t') ad1 ps cls")
          using nothing_between_a_nxt lastNxtVal_def lastVal_def
          apply (metis add.commute assms(8) plus_1_eq_Suc)
          apply (smt Null_def TopLV_agt_others assms(8) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr_zero)
          apply (metis \<open>\<And>u' u t ps' ps d ca. \<lbrakk>lib_wfs cls ccs; glb_inv ps cls; glb ps cls; to ps cls; cvd[libTop, u] cls; cls ccs CAS\<^sup>R[libTop, True, u, u']\<^sub>t cls' ccs'; u \<noteq> u'; ca \<in> pushed_addr ps; d \<in> pushed_addr ps; u \<noteq> ca; u \<noteq> d; agt ca d ps' cls'; pushed_addr ps' = pushed_addr ps - {u}\<rbrakk> \<Longrightarrow> agt ca d ps cls\<close> assms(8) cvd_CAS_R_success_read_val)
                   apply(case_tac "ad1 = ntop ps t'", simp)
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libad2 =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                      apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
                apply(simp add: globals to_simps)
    using dobs_to_def cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write
                   apply (smt Null_def not_gr_zero)
             apply simp
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
            apply blast
    apply(elim conjE disjE)
     apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
               apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
    apply(simp add: globals)
          apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)
          
    apply (metis \<open>\<And>u' u t ps' ps d ca. \<lbrakk>lib_wfs cls ccs; glb_inv ps cls; glb ps cls; to ps cls; cvd[libTop, u] cls; cls ccs CAS\<^sup>R[libTop, True, u, u']\<^sub>t cls' ccs'; u \<noteq> u'; ca \<in> pushed_addr ps; d \<in> pushed_addr ps; u \<noteq> ca; u \<noteq> d; agt ca d ps' cls'; pushed_addr ps' = pushed_addr ps - {u}\<rbrakk> \<Longrightarrow> agt ca d ps cls\<close> assms(8) cvd_CAS_R_success_read_val neq0_conv)
          apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
               apply(simp add: globals)
     apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)

        apply simp
    apply(simp add: globals)
                    apply (metis gr_zeroI subsetD)
                   apply(case_tac "ad1 = ntop ps t'", simp)
          apply(subgoal_tac "agt (ntop ps t') ad2 ps cls")
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
           apply(simp add: globals)
   using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                       apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
          apply(subgoal_tac "agt (prog_state.top ps t') ad2 ps cls \<and> top ps t' \<noteq> Null")
                        apply(simp add: dobs_to_def)
                       apply(subgoal_tac "xa = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
                  apply (metis cvd_CAS_R_success_read_val)
          apply auto[1]
          
          apply (metis \<open>\<And>u' u t ps' ps d ca. \<lbrakk>lib_wfs cls ccs; glb_inv ps cls; glb ps cls; to ps cls; cvd[libTop, u] cls; cls ccs CAS\<^sup>R[libTop, True, u, u']\<^sub>t cls' ccs'; u \<noteq> u'; ca \<in> pushed_addr ps; d \<in> pushed_addr ps; u \<noteq> ca; u \<noteq> d; agt ca d ps' cls'; pushed_addr ps' = pushed_addr ps - {u}\<rbrakk> \<Longrightarrow> agt ca d ps cls\<close> assms(8) cvd_CAS_R_success_read_val)
                   apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast
                 apply(subgoal_tac "xa = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
                 apply (metis cvd_CAS_R_success_read_val)   
                   apply simp
                   apply(subgoal_tac "agt ad1 (ntop ps t') ps cls")       
                    apply(subgoal_tac "agt  (ntop ps t') ad1 ps cls")
          apply (meson agt_def agt_order to_def to_p4_def)
           apply(subgoal_tac "agt  (top ps t') ad1 ps cls")
          using nothing_between_a_nxt lastNxtVal_def lastVal_def
          apply (metis add.commute assms(8) plus_1_eq_Suc)
          apply (smt Null_def TopLV_agt_others assms(8) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr_zero)
          
          apply (metis \<open>\<And>u' u t ps' ps d ca. \<lbrakk>lib_wfs cls ccs; glb_inv ps cls; glb ps cls; to ps cls; cvd[libTop, u] cls; cls ccs CAS\<^sup>R[libTop, True, u, u']\<^sub>t cls' ccs'; u \<noteq> u'; ca \<in> pushed_addr ps; d \<in> pushed_addr ps; u \<noteq> ca; u \<noteq> d; agt ca d ps' cls'; pushed_addr ps' = pushed_addr ps - {u}\<rbrakk> \<Longrightarrow> agt ca d ps cls\<close> assms(8) cvd_CAS_R_success_read_val)
                   apply(case_tac "ad1 = ntop ps t'", simp)
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls")
                       apply(elim exE conjE)
          apply(case_tac "[lib(Top) \<approx>\<^sub>t' (ntop ps t')] cls")
                        apply(subgoal_tac "vla = vl", simp)
                         apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                          apply(subgoal_tac "vlb = vl", simp)
                           apply(rule_tac x=vl in exI)
          apply(subgoal_tac "ad2 \<noteq> Top")
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres
                            apply metis
          apply(simp add: globals)
          apply auto[1]
          apply (simp add: pobs_cobs_same_val)
            apply(rule_tac x=vl in exI)
         
          apply (metis d_obs_p_obs_contradiction lib_d_obs_not_p_obs successful_CAS_lib_c_obs_lib_only_intro)
          
          apply (simp add: dobs_pobs_cobs_same_val)      
            apply(case_tac "[lib(Top) \<approx>\<^sub>t (ntop ps t')] cls")
                        apply(subgoal_tac "vlb=vl", simp)
          apply(simp add: globals)
          using successful_CAS_lib_c_obs_lib_pre_same_value_pres2
          apply (smt subset_iff)
                        apply (simp add: pobs_cobs_dobs_same_val)
                       apply(rule_tac x=vl in exI)
          apply(simp add: globals)
                      apply (metis subsetD successful_CAS_lib_c_obs_lib_only_intro)
                apply(simp add: globals to_simps)
    using dobs_to_def cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write
                   apply (smt Null_def not_gr_zero)
             apply simp
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
            apply blast
 (***end cobs_to proof***) 

           apply(cases "pc ps t"; cases "pc ps' t"; cases "pc ps t'")
                               apply (simp_all add: globals lib_pop_def pop_inv_def L3)
    apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
    apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
    apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
    apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
    apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
    apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
    done
  qed
    next case L4
      then show ?thesis                   
        using assms(4) lib_pop_def by auto
    next case L5
      then show ?thesis                   
        using assms(4) lib_pop_def by auto
    next case L6
      then show ?thesis                   
        using assms(4) lib_pop_def by auto
  qed

lemma "agt ad1  ad ps cls \<Longrightarrow> ad1\<notin>pushed_addr ps \<Longrightarrow> False"
  apply(simp add: agt_def clss_def nxt_rel_def trancl_def)
  using converse_tranclpE apply fastforce
  done


lemma "agt ad1  ad ps cls \<Longrightarrow> ad1\<in>pushed_addr ps"
  apply(simp add: agt_def clss_def nxt_rel_def trancl_def)
  using converse_tranclpE apply fastforce
  done


lemma "lib_wfs cls ccs \<Longrightarrow> wfs ccs \<Longrightarrow> [lib(a)\<approx>\<^sub>t u]cls \<Longrightarrow>
 [lib(a) = u]\<lparr>lib(b) =\<^sub>t u'\<rparr> cls \<Longrightarrow> [lib(b) =\<^sub>t' v'] cls \<Longrightarrow> t\<noteq>t' \<Longrightarrow> u' = v'"
  by (smt lib_c_obs_lib_only_def lib_d_obs_def lib_d_obs_t_def lib_p_obs_def)

lemma "lib_wfs cls ccs \<Longrightarrow> wfs ccs \<Longrightarrow> [lib(a)\<approx>\<^sub>t u]cls \<Longrightarrow> [lib(a)\<approx>\<^sub>t' u]cls \<Longrightarrow>
 [lib(a) = u]\<lparr>lib(b) =\<^sub>t u'\<rparr> cls \<Longrightarrow> [lib(a) = u]\<lparr>lib(b) =\<^sub>t' v'\<rparr> cls \<Longrightarrow> t\<noteq>t' \<Longrightarrow> u' = v'"
  by (smt lib_c_obs_lib_only_def lib_d_obs_def lib_p_obs_def)


lemma "lib_wfs cls ccs \<Longrightarrow> wfs ccs \<Longrightarrow>
   [lib(b) =\<^sub>t v']cls \<Longrightarrow> [lib(a)\<approx>\<^sub>t u]cls \<Longrightarrow> [lib(a) = u]\<lparr>lib(b) =\<^sub>t u'\<rparr> cls  \<Longrightarrow> u' = v'"
  by (smt lib_c_obs_lib_only_def lib_d_obs_def lib_d_obs_t_def lib_p_obs_def)


lemma push_inv_gc_push:
  assumes "wfs ccs"
      and "lib_wfs cls ccs"
      and "lib_push t' v ps cls ccs ps' cls' ccs'"
      and "push_inv t v (pc ps t) cls ccs  ps"
      and "push_inv t' v (pc ps t') cls ccs  ps"
      and "glb_inv ps cls"
      and "t \<noteq> t'"
      and "to ps cls"
    shows "push_inv t v (pc ps' t) cls' ccs'  ps'"
    proof (cases "pc ps t'")
      case L1
      then show ?thesis                   
          using assms
          apply(cases "pc ps t"; simp ; elim exE conjE; simp)
          apply(intro conjI)
          using assms(3) lib_push_L1_new_address_not_null apply blast
                   apply (metis Null_def assms(3) lib_push_L1_new_address_not_null)
          apply(simp add: new_node_def)
                  apply (meson assms(3) in_mono lib_push_L1_addr_sub)
          apply(simp add: no_Top_n_a_def new_node_def)
           apply (smt assms(3) lib_push_L1_addr_sub subsetD)
                apply (simp add: lib_push_L1_pc)
          apply(simp add: cobs_to_def)
                apply (metis agt_pushed_same2 assms(3) lib_push_L1_pushed)
          apply(simp add: addr_init_writes_def written_vals_def new_node_def globals)
            apply (intro conjI impI allI)
        apply (metis assms(3) lib_push_L1_addr_sub subsetD)
             apply (metis assms(3) lib_push_L1_addr_sub subsetD)
              apply (intro conjI impI allI)
          
          apply (meson assms(3) lib_push_L1_new_address_not_null)
          apply (metis Null_def assms(3) lib_push_L1_new_address_not_null)
          apply (metis PC.distinct(1) fun_upd_same prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
          apply(simp add: globals)   
          apply (meson assms(3) lib_push_L1_addr_sub subset_iff)
          apply (metis PC.distinct(1) fun_upd_same prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
          apply (metis PC.distinct(1) fun_upd_same prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
          apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
          apply(simp add: globals)   
                   apply (metis (no_types, lifting) prog_state.ext_inject prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
          apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))          
          apply (metis (no_types, lifting) PC.distinct(1) fun_upd_idem_iff prog_state.ext_inject prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
          apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))          
          apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))          
          apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))          
             apply(intro conjI)
          using assms(3) lib_push_L1_new_address_not_null apply blast          
                    apply (metis Null_def assms(3) lib_push_L1_new_address_not_null)
                   apply(simp add: lib_d_obs_t_def lib_d_obs_def)
          apply (metis (no_types, lifting) prog_state.ext_inject prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
                  apply(simp add: globals)
          apply (metis Set.set_insert assms(3) insert_subset lib_push_L1_addr_sub)
                   apply(simp add: globals)
                 apply (meson assms(3) in_mono lib_push_L1_addr_val)
          using insert_absorb insert_subset prog_state.select_convs(3) prog_state.select_convs(7) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9) subsetI
                apply (smt PC.distinct(1) fun_upd_idem_iff prog_state.ext_inject)
          apply (smt prog_state.select_convs(3) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
          using assms(3) lib_push_L1_pushed apply blast
          apply(simp add: globals)
          apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
               apply(simp add: no_Top_n_def written_addr_def)
          apply(intro allI impI)
          apply (metis prog_state.select_convs(3) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
             apply(simp add: cobs_to_def)
              apply (metis agt_pushed_same2 assms(3) lib_push_L1_pushed)
             apply(simp add: globals written_vals_def glb_inv16_def new_node_def addr_init_writes_def)
             apply(intro allI impI conjI)
          apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))

            apply(simp add: dobs_to_def written_vals_def addr_init_writes_def)
            apply(intro conjI)
          apply (meson assms(3) lib_push_L1_new_address_not_null)
          apply (metis Null_def assms(3) lib_push_L1_new_address_not_null)
                    apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
          apply (meson assms(3) in_mono lib_push_L1_addr_sub)
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
            apply(simp add: dobs_to_def written_vals_def addr_init_writes_def)
            apply(intro conjI)
          apply (meson assms(3) lib_push_L1_new_address_not_null)
          apply (metis Null_def assms(3) lib_push_L1_new_address_not_null)
                    apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
          apply (meson assms(3) in_mono lib_push_L1_addr_sub)
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
          done
    next
      case L2
      then show ?thesis 
          using assms
          apply(cases "pc ps t"; simp add: glb_inv15_def glb_inv_def glb_inv14_def; elim exE conjE; simp)
          apply (intro conjI impI allI) 
          apply (metis d_obs_write_diff_var new_node_def nn_l1)
                 apply (metis d_obs_write_diff_var new_node_def nn_l1)
          apply (metis lib_covered_write_diff_var_pres)
          apply (smt new_node_def no_Top_n_a_def wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
               apply(simp add: cobs_to_def)
          apply(intro allI impI conjI)
          apply (metis agt_pushed_same2wr_before_state lib_c_obs_lib_only_pres_wr_diff_var same_except_for_pc_and_top_def)
          apply(simp add: globals)       
          apply (metis agt_pushed_same2wr_before_state assms(6) lib_c_obs_lib_only_pres_wr_diff_var same_except_for_pc_and_top_def)
          apply(simp add:  addr_init_writes_def written_vals_def globals new_node_def glb_inv16_def)
               apply (intro conjI impI allI) 
          apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' a = lib_value cls ` lib_writes_on cls a")
          apply metis
                apply (metis image_cong wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
          apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' (Suc a) = lib_value cls ` lib_writes_on cls (Suc a)")
           apply metis
             
               apply (metis (no_types, lifting) image_cong wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)      
               apply(intro conjI)
               apply (smt d_obs_write_diff_var glb_inv15_def glb_inv_def lib_covered_write_diff_var_pres no_Top_n_def wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
          apply (smt d_obs_write_diff_var glb_inv15_def glb_inv_def lib_covered_write_diff_var_pres no_Top_n_def wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)  
                  
                 apply (metis lib_covered_write_diff_var_pres)
          
          apply (smt no_Top_n_def wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
          
          apply (metis diff_var_write_written_addr)
              apply(simp add: cobs_to_def)
          apply(intro allI impI conjI)
               apply (metis agt_pushed_same2wr_before_state lib_c_obs_lib_only_pres_wr_diff_var same_except_for_pc_and_top_def)
          apply(simp add: globals)       
              apply (metis agt_pushed_same2wr_before_state assms(6) lib_c_obs_lib_only_pres_wr_diff_var same_except_for_pc_and_top_def) 
              apply(simp add: written_vals_def)
          apply (smt image_cong wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
    apply(intro conjI)
          using d_obs_write_diff_var  apply metis
          apply (metis d_obs_write_diff_var)
          apply (metis lib_covered_write_diff_var_pres)
              apply (smt no_Top_n_def wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
                apply(simp add: cobs_to_def)
          apply(intro allI impI conjI)
               apply (metis agt_pushed_same2wr_before_state lib_c_obs_lib_only_pres_wr_diff_var same_except_for_pc_and_top_def)
          apply(simp add: globals)       
              apply (metis agt_pushed_same2wr_before_state assms(6) lib_c_obs_lib_only_pres_wr_diff_var same_except_for_pc_and_top_def)           
              apply (metis diff_var_write_written_addr)
             apply(intro allI impI conjI)
          apply(simp add: written_vals_def)
          apply (smt image_cong wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
             apply(intro conjI)
          using d_obs_write_diff_var apply auto[1]
          apply (metis d_obs_write_diff_var)
          
          apply (metis lib_covered_write_diff_var_pres)
          
          apply (smt no_Top_n_def wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
              apply (smt Diff_iff imageE image_eqI wr_preserves_value_diff_var wr_preserves_writes_on_diff_var written_addr_def)
                apply(simp add: cobs_to_def)
          apply(intro allI impI conjI)
               apply (metis agt_pushed_same2wr_before_state lib_c_obs_lib_only_pres_wr_diff_var same_except_for_pc_and_top_def)
          apply(simp add: globals)       
              apply (metis agt_pushed_same2wr_before_state assms(6) lib_c_obs_lib_only_pres_wr_diff_var same_except_for_pc_and_top_def)
             apply(simp add: dobs_to_def)
          apply(intro conjI allI impI)
              apply (metis agt_pushed_same2wr_before_state d_obs_write_diff_var same_except_for_pc_and_top_def)
             apply(simp add: globals)     
    apply (metis agt_pushed_same2wr_before_state assms(6) d_obs_write_diff_var same_except_for_pc_and_top_def)
             apply (metis diff_var_write_written_addr)
          apply(simp add: written_vals_def)
                    apply (smt image_iff wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)

                      apply(intro conjI)
          using d_obs_write_diff_var apply auto[1]
          apply (metis d_obs_write_diff_var)
          
          apply (metis lib_covered_write_diff_var_pres)
              apply (metis wr_preserves_last)
          apply (smt no_Top_n_def wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
                apply(simp add: cobs_to_def)
          apply(intro allI impI conjI)
               apply (metis agt_pushed_same2wr_before_state lib_c_obs_lib_only_pres_wr_diff_var same_except_for_pc_and_top_def)
          apply(simp add: globals)       
              apply (metis agt_pushed_same2wr_before_state assms(6) lib_c_obs_lib_only_pres_wr_diff_var same_except_for_pc_and_top_def)
             apply(simp add: dobs_to_def)
          apply(intro conjI allI impI)
              apply (metis agt_pushed_same2wr_before_state d_obs_write_diff_var same_except_for_pc_and_top_def)
             apply(simp add: globals)     
    apply (metis agt_pushed_same2wr_before_state assms(6) d_obs_write_diff_var same_except_for_pc_and_top_def)            apply (metis diff_var_write_written_addr)
          
            apply (metis diff_var_write_written_addr)
          apply(simp add: written_vals_def)
                           apply (smt image_iff wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
     apply(intro conjI)
          using d_obs_write_diff_var apply auto[1]
          apply (metis d_obs_write_diff_var)
          
          apply (metis lib_covered_write_diff_var_pres)
                apply(simp add: cobs_to_def)
          apply(intro allI impI conjI)
               apply (metis agt_pushed_same2wr_before_state lib_c_obs_lib_only_pres_wr_diff_var same_except_for_pc_and_top_def)
          apply(simp add: globals)       
              by (metis agt_pushed_same2wr_before_state assms(6) lib_c_obs_lib_only_pres_wr_diff_var same_except_for_pc_and_top_def)          
      next
      case L3
      then show ?thesis    
        using assms
        apply(cases "pc ps t"; simp add: glb_inv14_def; elim exE conjE; simp)
        apply (intro conjI impI allI) 
        apply (metis lib_d_obs_pres_read new_node_def)      
        apply (metis lib_d_obs_pres_read new_node_def)        
        apply (meson lib_read_cvd_pres)
              apply (metis (no_types, lifting) lib_read_writes_on_diff_var_pres_backwards new_node_def nn_l5 no_Top_n_a_def rd_A_preserves_values)
        apply(simp add: cobs_to_def)
             apply (metis agt_pushed_same2rd_before_state lib_c_obs_lib_only_pres_read_var)
             apply(simp add: addr_init_writes_def written_vals_def new_node_def)
        apply (metis lib_read_writes_on_diff_var_pres_backwards rd_A_preserves_values)
             apply (intro conjI)
        apply (smt lib_d_obs_pres_read lib_read_cvd_pres no_Top_n_def rd_A_preserves_values read_pres_writes_on_diff_var) 
        apply (smt lib_d_obs_pres_read lib_read_cvd_pres no_Top_n_def rd_A_preserves_values read_pres_writes_on_diff_var)
        apply (smt lib_d_obs_pres_read lib_read_cvd_pres no_Top_n_def rd_A_preserves_values read_pres_writes_on_diff_var written_addr_def)
        apply (smt lib_d_obs_pres_read lib_read_cvd_pres no_Top_n_def rd_A_preserves_last rd_A_preserves_values read_pres_writes_on_diff_var)        
        apply(simp add: written_addr_def globals)      
        apply (metis lib_read_writes_on_diff_var_pres_backwards rd_A_preserves_values)
        apply(simp add: cobs_to_def)
            apply (metis agt_pushed_same2rd_before_state lib_c_obs_lib_only_pres_read_var)
             apply (simp add: rd_A_preserves_values rd_A_preserves_writes_on written_vals_def)
   apply(intro conjI)
                       
        using lib_d_obs_pres_read apply blast
                  using lib_d_obs_pres_read apply blast
                  using lib_read_cvd_pres apply blast
                  apply(simp add: no_Top_n_def)
                   using rd_A_preserves_values rd_A_preserves_writes_on apply auto[1]
                      apply(simp add: cobs_to_def)
                       apply (metis agt_pushed_same2rd_before_state lib_c_obs_lib_only_pres_read_var)
                   apply(simp add: written_addr_def)
                       apply (simp add: rd_A_preserves_values rd_A_preserves_writes_on)
             apply (simp add: rd_A_preserves_values rd_A_preserves_writes_on written_vals_def)
        apply(intro conjI)
                       
        using lib_d_obs_pres_read apply blast
                  using lib_d_obs_pres_read apply blast
                  using lib_read_cvd_pres apply blast
                  apply(simp add: no_Top_n_def)
                  using rd_A_preserves_values rd_A_preserves_writes_on apply auto[1]
           apply(simp add: written_addr_def globals)      
               apply (metis lib_read_writes_on_diff_var_pres_backwards rd_A_preserves_values)
                      apply(simp add: cobs_to_def)
                     apply (metis agt_pushed_same2rd_before_state lib_c_obs_lib_only_pres_read_var)
                  apply(simp add: dobs_to_def)
               apply (metis agt_pushed_same2rd_before_state lib_d_obs_pres_read)
                            apply(simp add: written_addr_def)
                    apply (simp add: rd_A_preserves_values rd_A_preserves_writes_on)
             apply (simp add: rd_A_preserves_values rd_A_preserves_writes_on written_vals_def)

        apply(intro conjI)
                       
        using lib_d_obs_pres_read apply blast
                  using lib_d_obs_pres_read apply blast
                  using lib_read_cvd_pres apply blast
                  apply (simp add: rd_A_preserves_last)

                  apply(simp add: no_Top_n_def)
                  using rd_A_preserves_values rd_A_preserves_writes_on apply auto[1]
                      apply(simp add: cobs_to_def)
                     apply (metis agt_pushed_same2rd_before_state lib_c_obs_lib_only_pres_read_var)
                  apply(simp add: dobs_to_def)
               apply (metis agt_pushed_same2rd_before_state lib_d_obs_pres_read)                  
                                        apply(simp add: cobs_to_def)
                  using agt_pushed_same2rd_before_state lib_c_obs_lib_only_pres_read_var
                    apply(simp add: written_addr_def)
                    apply (simp add: rd_A_preserves_values read_pres_writes_on_diff_var)                    apply(simp add: written_addr_def)
                    apply (simp add: rd_A_preserves_values read_pres_writes_on_diff_var)
                  apply(simp add: written_vals_def)        
                  apply (metis lib_read_writes_on_diff_var_pres_backwards rd_A_preserves_values)
   by (smt agt_pushed_same2rd_before_state cobs_to_def lib_c_obs_lib_only_pres_read_var lib_d_obs_pres_read lib_read_cvd_pres)
    next
      case L4
      then show ?thesis using assms
        apply(cases "pc ps t"; simp add: glb_inv15_def glb_inv_def glb_inv14_def; elim exE conjE; simp)
        apply (intro conjI impI allI) 
        apply (metis d_obs_write_diff_var new_node_def nn_l1)
        apply (metis d_obs_write_diff_var new_node_def nn_l1)
        apply (metis lib_covered_write_diff_var_pres)
        apply (smt new_node_def nn_l5 no_Top_n_a_def wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
             apply(simp add: cobs_to_def)
             apply(intro allI impI, elim disjE conjE)
              apply(subgoal_tac "agt ad1 ad2 ps' cls' =agt ad1 ad2 ps cls")
        apply(intro conjI)
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
        apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc ad2 =\<^sub>t vl \<rparr> cls")
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var old.nat.inject)
       apply blast
                apply (simp add: agt_def clss_def nxt_rel_def)
              apply (smt Collect_cong Suc_inject write_diff_var_last_val)
        apply(intro conjI)
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
        apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc ad2 =\<^sub>t vl \<rparr> cls")
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var old.nat.inject)
              apply blast
             apply(simp add: addr_init_writes_def written_vals_def new_node_def)
        apply(intro conjI impI allI)
        apply (smt image_cong wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
        apply (smt image_cong wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
     apply(intro conjI)
             apply (smt d_obs_write_diff_var lib_covered_write_diff_var_pres no_Top_n_def wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
                apply (smt d_obs_write_diff_var lib_covered_write_diff_var_pres no_Top_n_def wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
                apply (smt d_obs_write_diff_var lib_covered_write_diff_var_pres no_Top_n_def wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
                apply (smt d_obs_write_diff_var lib_covered_write_diff_var_pres no_Top_n_def wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
             apply (metis (full_types) diff_var_write_written_addr)

             apply(simp add: cobs_to_def)
             apply(intro allI impI, elim disjE conjE)
        apply(subgoal_tac "agt ad1 ad2 ps' cls' =agt ad1 ad2 ps cls")
        apply(intro conjI)
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
        apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc ad2 =\<^sub>t vl \<rparr> cls")
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var old.nat.inject)
               apply auto[1]

              apply (simp add: agt_def clss_def nxt_rel_def)
              apply (smt Collect_cong Suc_inject write_diff_var_last_val)
        apply(intro conjI)
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
        apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc ad2 =\<^sub>t vl \<rparr> cls")
              apply (metis lib_c_obs_lib_only_pres_wr_diff_var old.nat.inject)
             apply simp
            apply(simp add: written_vals_def)
        apply (smt image_cong wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
              apply(simp add: written_vals_def)
        apply (intro conjI impI allI) 
        apply (metis d_obs_write_diff_var)          
        apply (metis d_obs_write_diff_var)
        apply (metis lib_covered_write_diff_var_pres)
            apply (smt no_Top_n_def wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)    

             apply(simp add: cobs_to_def)
             apply(intro allI impI, elim disjE conjE)
        apply(subgoal_tac "agt ad1 ad2 ps' cls' =agt ad1 ad2 ps cls")
        apply(intro conjI)
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
        apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc ad2 =\<^sub>t vl \<rparr> cls")
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var old.nat.inject)
       apply blast
              apply (simp add: agt_def clss_def nxt_rel_def)
              apply (smt Collect_cong Suc_inject write_diff_var_last_val)
        apply(intro conjI)
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
        apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc ad2 =\<^sub>t vl \<rparr> cls")
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var old.nat.inject)
       apply blast
            apply (metis diff_var_write_written_addr)
        
        apply (smt image_iff wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
          apply(intro conjI)
                apply (metis d_obs_write_diff_var)
        apply (metis d_obs_write_diff_var)
        apply (metis lib_covered_write_diff_var_pres)
        apply (smt no_Top_n_def wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)

        apply (smt Diff_iff imageE image_eqI wr_preserves_value_diff_var wr_preserves_writes_on_diff_var written_addr_def)

                        apply(simp add: cobs_to_def)
             apply(intro allI impI, elim disjE conjE)
        apply(subgoal_tac "agt ad1 ad2 ps' cls' =agt ad1 ad2 ps cls")
        apply(intro conjI)
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
        apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc ad2 =\<^sub>t vl \<rparr> cls")
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var old.nat.inject)
               apply blast
              apply (simp add: agt_def clss_def nxt_rel_def)
              apply (smt Collect_cong Suc_inject write_diff_var_last_val)
        apply(intro conjI)
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
        apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc ad2 =\<^sub>t vl \<rparr> cls")
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var old.nat.inject)
       apply blast
          apply(simp add: dobs_to_def)
             apply(intro allI impI, elim disjE conjE)
      apply(subgoal_tac "agt (prog_state.top ps t) ad ps' cls' = agt (prog_state.top ps t) ad ps cls")
        apply(intro conjI)
              apply (metis d_obs_write_diff_var)
        apply (metis d_obs_write_diff_var old.nat.inject)
           apply (simp add: agt_def clss_def nxt_rel_def)
            apply (smt Collect_cong Suc_inject write_diff_var_last_val)
        apply(intro conjI)
        apply (smt d_obs_write_diff_var lib_covered_write_diff_var_pres no_Top_n_def wr_preserves_last wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
        apply (metis d_obs_write_diff_var old.nat.inject)
           apply (metis (full_types) diff_var_write_written_addr)
          apply(simp add: written_vals_def)
        
        apply (smt image_iff wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
          apply(intro conjI)
                apply (metis d_obs_write_diff_var)
        apply (metis d_obs_write_diff_var)
        apply (metis lib_covered_write_diff_var_pres)
        using write_diff_var_last_val apply auto[1]
        apply (smt no_Top_n_def wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)

                       apply(simp add: cobs_to_def)
             apply(intro allI impI, elim disjE conjE)
        apply(subgoal_tac "agt ad1 ad2 ps' cls' =agt ad1 ad2 ps cls")
        apply(intro conjI)
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
        apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc ad2 =\<^sub>t vl \<rparr> cls")
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var old.nat.inject)
       apply blast
              apply (simp add: agt_def clss_def nxt_rel_def)
              apply (smt Collect_cong Suc_inject write_diff_var_last_val)
        apply(intro conjI)
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
        apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc ad2 =\<^sub>t vl \<rparr> cls")
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var old.nat.inject)
       apply blast
          apply(simp add: dobs_to_def)
             apply(intro allI impI, elim disjE conjE)
      apply(subgoal_tac "agt (prog_state.top ps t) ad ps' cls' = agt (prog_state.top ps t) ad ps cls")
        apply(intro conjI)
              apply (metis d_obs_write_diff_var)
        apply (metis d_obs_write_diff_var old.nat.inject)
           apply (simp add: agt_def clss_def nxt_rel_def)
              apply (smt Collect_cong Suc_inject write_diff_var_last_val)
        apply(intro conjI)
        apply (smt d_obs_write_diff_var lib_covered_write_diff_var_pres no_Top_n_def wr_preserves_last wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
           apply (metis d_obs_write_diff_var old.nat.inject)
     apply (metis diff_var_write_written_addr)
          apply (metis diff_var_write_written_addr)
        apply(simp add: written_vals_def)
        apply (smt image_iff wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
          apply(intro conjI)
                apply (metis d_obs_write_diff_var)
        apply (metis d_obs_write_diff_var)
        apply (metis lib_covered_write_diff_var_pres)
                       apply(simp add: cobs_to_def)
             apply(intro allI impI, elim disjE conjE)
         apply(subgoal_tac "agt ad1 ad2 ps' cls' =agt ad1 ad2 ps cls")
        apply(intro conjI)
           apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
        apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc ad2 =\<^sub>t vl \<rparr> cls")
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var old.nat.inject)
       apply blast
              apply (simp add: agt_def clss_def nxt_rel_def)
              apply (smt Collect_cong Suc_inject write_diff_var_last_val)
              apply(intro conjI)
           apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
        apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc ad2 =\<^sub>t vl \<rparr> cls")
                apply (metis lib_c_obs_lib_only_pres_wr_diff_var old.nat.inject)
        by blast
    next
      case L5
      then show ?thesis
      proof (cases "res ps' t'")
        case True
        then show ?thesis        
          using assms
            apply(cases "pc ps t"; simp add: glb_inv15_def glb_inv_def; elim exE conjE; simp)
            apply(cases "pc ps t'"; cases "pc ps t'"; elim exE conjE; simp add: L5)
            apply (intro conjI impI allI)
            apply (metis d_obs_post_CAS_R_diff_var_post new_node_def nn_l4)
            apply (metis d_obs_post_CAS_R_diff_var_post new_node_def nn_l4)
          using cvd_CAS_R_cvd apply auto[1]
               apply(simp add: no_Top_n_a_def globals) 
            apply(cases "pc ps t'"; cases "pc ps t'"; elim exE conjE; simp add: L5)
                       apply(simp add: new_node_def)
  apply (intro conjI impI allI) 
                apply (metis CAS_Rel_new_write_value CAS_Rel_preserves_value_old)
                apply (metis CAS_Rel_new_write_value CAS_Rel_preserves_value_old)
               apply(simp add: cobs_to_def)
               apply(intro allI impI, elim conjE)
               apply(case_tac "ad1 = n_val ps t'")
                apply(subgoal_tac "ad1 \<notin> pushed_addr ps")
                 apply(elim disjE)
          apply (metis lib_not_pobs_cobs no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_pre_same_value_pres)
          
                       apply (metis lib_not_pobs_cobs no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_pre_same_value_pres)
                      apply(subgoal_tac "top ps t' \<noteq> Null")
                       apply(case_tac "ad2 = prog_state.top ps t'")
                        (*begin*)
                        apply(intro conjI)
                         apply (metis cvd_CAS_R_success_read_val dobs_to_def glb_inv1_def lib_cvd_exist_write no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
                        apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc ad2 =\<^sub>t vl \<rparr> cls ")
                         apply(subgoal_tac "(\<exists>vl. [libSuc ad2 =\<^sub>t' vl] cls) \<and> \<not>[lib(Top)\<approx>\<^sub>t ad1] cls")
            apply(subgoal_tac "Suc ad2 \<noteq> Top")
        apply(elim conjE exE, rule_tac x=vla in exI)
          using successful_CAS_lib_c_obs_lib_only_intro apply auto[1]
          apply(simp add: globals)
                  apply metis
                  apply (simp add: dobs_to_def no_Top_n_implies_no_p_obs)
                        apply (simp add: lib_not_pobs_cobs no_Top_n_implies_no_p_obs)
                        (*end*)

                       apply(subgoal_tac "(\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and> (\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and>  \<not>[lib(Top) \<approx>\<^sub>t ad1] cls")
                        apply(elim conjE exE, intro conjI)
          apply(rule_tac x = vl in exI)
                         apply (metis glb_inv5_def in_mono successful_CAS_lib_c_obs_lib_only_intro)
          apply(rule_tac x = vla in exI)
             apply(subgoal_tac "Suc ad2 \<noteq> Top")
          using successful_CAS_lib_c_obs_lib_only_intro apply auto[1]
          apply(simp add: globals)
                  apply metis
                       apply(intro conjI)
                        apply(simp add: dobs_to_def)
          apply(subgoal_tac "agt (prog_state.top ps t') ad2 ps cls")
                         apply auto[1]
                        apply(simp add: to_simps)
                        apply(subgoal_tac "lastTop cls = top ps t'")
          apply(simp add: lastTop_def)
                         apply (metis cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write)
                        apply(subgoal_tac "Suc ad2 \<noteq> Top")
          apply (smt cvd_CAS_R_success_read_val dobs_to_def lastTop_def lib_cvd_exist_last_write to_def to_p2_def)
          apply(simp add: globals)
                  apply metis
          apply (simp add: no_Top_n_implies_no_p_obs)
          apply (metis (no_types, lifting) Null_def TopLV_Null_pushed_empty cvd_CAS_R_success_read_val empty_iff glb_def lastTop_def lib_cvd_exist_last_write)
          apply blast
          apply blast
          apply linarith
          apply linarith
          apply blast
                apply blast
          apply(case_tac "ad2 = n_val ps t'"; case_tac "ad2 \<in> pushed_addr ps")
                  apply blast
                 apply simp
          apply(subgoal_tac "\<not>agt ad1 (n_val ps t') ps' cls'")
          
                  apply blast
                 apply(simp add: agt_def clss_def)
         apply(case_tac "lastTop cls = Null")
         apply(subgoal_tac "pushed_addr ps = {}")
           apply simp
                  apply (simp add: TopLV_Null_pushed_empty)
         apply(subgoal_tac "n_val ps t' \<notin> Domain (nxt_rel ps cls) \<union> Range (nxt_rel ps cls)")
         apply(subgoal_tac "n_val ps t' \<notin> Range (nxt_rel ps' cls')")
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                  apply (metis Range.intros trancl_range)
                   apply (metis Range.intros trancl_range)
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                   apply (metis A_sub_b Range_Un_eq Range_empty Range_insert UnI2 cvd_CAS_R_success_read_val lib_cvd_exist_write no_Top_n_def)
          apply(simp add: nxt_rel_def globals written_addr_def to_simps)
                  apply safe
                             apply (metis succ_CAS_preserves_last)
          apply simp
                              apply (metis succ_CAS_preserves_last)
                              apply simp

          apply simp

                          apply (metis succ_CAS_preserves_last)
          apply simp
          apply simp
                       apply (metis succ_CAS_preserves_last)
          apply simp
          apply simp

                    apply (metis succ_CAS_preserves_last)
                              apply (metis succ_CAS_preserves_last)

          apply simp

          apply simp

          apply simp

          apply simp

                    apply (metis succ_CAS_preserves_last)

          apply (metis succ_CAS_preserves_last)
          apply (metis)
          apply (metis)
          apply (metis succ_CAS_preserves_last)
          apply (metis succ_CAS_preserves_last)
          apply (metis)
          apply (metis)
                            apply (simp add: a_not_in_pushed_nxt_rel)
          apply (simp add: a_not_in_pushed_nxt_rel)
              
                          apply (metis Null_def cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write)
          
          apply (metis Null_def Range.intros not_range)
          apply (metis (no_types, lifting) Null_def TopLV_Null_pushed_empty cvd_CAS_R_success_read_val empty_iff glb_def lastTop_def lib_cvd_exist_last_write)
          
          apply (metis (no_types, lifting) Null_def TopLV_Null_pushed_empty cvd_CAS_R_success_read_val empty_iff glb_def lastTop_def lib_cvd_exist_last_write)


                 apply(subgoal_tac "agt ad1 ad2 ps' cls' = agt ad1 ad2 ps cls")
                       apply(subgoal_tac "(\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls)")
          apply(simp add: globals)
          apply (metis subset_eq successful_CAS_lib_c_obs_lib_diff_value_pres)
                         apply (metis)

         apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
          using  agt_pushed_successful_cas_before
          apply (metis Null_def glb_def insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
                         apply (metis no_nxt_no_agt)
                        apply(intro allI impI)
          apply (simp add: globals)
          apply (metis neq0_conv succ_CAS_preserves_last)

                       (*apply (metis Un_commute agt_pushed_successful_cas_before insert_is_Un)*)
          apply(subgoal_tac "agt ad1 ad2 ps' cls' = agt ad1 ad2 ps cls")
                       apply(subgoal_tac "(\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
          apply(simp add: globals)
          apply (metis subset_eq successful_CAS_lib_c_obs_lib_diff_value_pres)
                        apply (metis)

       apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
          using  agt_pushed_successful_cas_before
          apply (metis Null_def glb_def insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
                         apply (metis no_nxt_no_agt)
                        apply(intro allI impI)
          apply (simp add: globals)
          apply (metis neq0_conv succ_CAS_preserves_last)

            apply (metis (no_types, lifting) Null_def TopLV_Null_pushed_empty cvd_CAS_R_success_read_val empty_iff glb_def lastTop_def lib_cvd_exist_last_write)
             apply (metis (no_types, lifting) Null_def TopLV_Null_pushed_empty cvd_CAS_R_success_read_val empty_iff glb_def lastTop_def lib_cvd_exist_last_write)
                         
       apply(subgoal_tac " \<exists>vl. [libTop = ad2]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                 apply(elim exE)
                 apply(rule_tac x=vl in exI)
                    apply(simp add: no_Top_n_def no_Top_n_a_def globals)
          apply (metis subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
          apply blast


    apply(subgoal_tac " \<exists>vl. [libTop = ad2]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                 apply(elim exE)
                 apply(rule_tac x=vl in exI)
                    apply(simp add: no_Top_n_def no_Top_n_a_def globals)
          
          apply (metis successful_CAS_lib_c_obs_lib_diff_value_pres)
                   apply blast
          apply(simp add: addr_init_writes_def written_vals_def new_node_def)
                      apply(intro allI impI conjI)
     apply (smt CAS_Rel_preserves_writes_on_diff_var image_cong write_value_CAS_R_diff_var)
     apply (smt CAS_Rel_preserves_writes_on_diff_var image_cong write_value_CAS_R_diff_var)


          apply(simp add: addr_init_writes_def written_vals_def new_node_def)
                      apply(intro allI impI conjI)
     apply (smt CAS_Rel_preserves_writes_on_diff_var image_cong write_value_CAS_R_diff_var)
     apply (smt CAS_Rel_preserves_writes_on_diff_var image_cong write_value_CAS_R_diff_var)
         apply(cases "pc ps t'"; cases "pc ps t'"; simp)
                   apply(intro conjI)
          using L5 apply auto[1]
          using L5 apply auto[1]
          using L5 apply auto[1]
          using L5 apply auto[1]
          using L5 apply auto[1]
          using L5 apply auto[1]
          using L5 apply auto[1]
          using L5 apply auto[1]
          using L5 apply auto[1]
          using L5 apply auto[1]
          using L5 apply auto[1]
          using L5 apply auto[1]
          using L5 apply auto[1]
          using L5 apply auto[1]
          using L5 apply auto[1]
                    using L5 apply auto[1]
       apply(intro conjI)
          
     apply (metis d_obs_post_CAS_R_diff_var_post)
             apply (metis d_obs_post_CAS_R_diff_var_post)
             using cvd_CAS_R_cvd apply metis
                  apply metis
             apply(simp add: no_Top_n_def)
                    apply (metis (no_types, lifting) CAS_Rel_new_write_value CAS_Rel_preserves_value_old)
                   apply (meson CAS_Top_written_addr_post)
(*******)
             apply(simp add: cobs_to_def)
               apply(intro allI impI, elim conjE)
               apply(case_tac "ad1 = n_val ps t'")
                apply(subgoal_tac "ad1 \<notin> pushed_addr ps")
                 apply(elim disjE)
          apply (metis lib_not_pobs_cobs no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_pre_same_value_pres)
          
                       apply (metis lib_not_pobs_cobs no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_pre_same_value_pres)
          apply(subgoal_tac "top ps t' \<noteq> Null")
                           apply(case_tac "ad2 = prog_state.top ps t'")
             apply(intro conjI)
                             apply (metis cvd_CAS_R_success_read_val dobs_to_def glb_inv1_def lib_cvd_exist_write no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
                            apply(subgoal_tac "Suc(ad2) \<noteq> Top \<and> (\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and> \<not>[lib(Top) \<approx>\<^sub>t ad1] cls")
             apply(elim conjE exE)
                             apply (metis successful_CAS_lib_c_obs_lib_only_intro)
             apply(simp add: globals)
             apply (metis Null_def dobs_to_def neq0_conv no_Top_n_implies_no_p_obs)

                       apply(subgoal_tac "Suc(ad2) \<noteq> Top \<and>  (\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and> (\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and> \<not>[lib(Top) \<approx>\<^sub>t ad1] cls")
                            apply(elim conjE exE)
             apply(intro conjI)
          apply(rule_tac x = vl in exI)
                        apply (metis glb_inv5_def in_mono successful_CAS_lib_c_obs_lib_only_intro)
             
                            apply (metis successful_CAS_lib_c_obs_lib_only_intro)

                           apply(intro conjI)
              apply(simp add: globals)
            apply metis
                        apply(simp add: dobs_to_def)
          apply(subgoal_tac "agt (prog_state.top ps t') ad2 ps cls")
                         apply auto[1]
                        apply(simp add: to_simps)
                        apply(subgoal_tac "lastTop cls = top ps t'")
          apply(simp add: lastTop_def)
                             apply (metis cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write)
             
             apply (smt Null_def TopLV_agt_others cvd_CAS_R_success_read_val dobs_to_def glb_def lastTop_def lib_cvd_exist_last_write)
                            apply (simp add: no_Top_n_implies_no_p_obs)

          apply (metis (no_types, lifting) Null_def TopLV_Null_pushed_empty cvd_CAS_R_success_read_val empty_iff glb_def lastTop_def lib_cvd_exist_last_write)
          apply blast
          apply blast
          apply linarith
          apply linarith
          apply blast
                apply blast
          apply(case_tac "ad2 = n_val ps t'"; case_tac "ad2 \<in> pushed_addr ps")
                  apply blast
                 apply simp
          apply(subgoal_tac "\<not>agt ad1 (n_val ps t') ps' cls'")
          
                  apply blast
                 apply(simp add: agt_def clss_def)
         apply(case_tac "lastTop cls = Null")
         apply(subgoal_tac "pushed_addr ps = {}")
           apply simp
                  apply (simp add: TopLV_Null_pushed_empty)
         apply(subgoal_tac "n_val ps t' \<notin> Domain (nxt_rel ps cls) \<union> Range (nxt_rel ps cls)")
         apply(subgoal_tac "n_val ps t' \<notin> Range (nxt_rel ps' cls')")
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                  apply (metis Range.intros trancl_range)
                   apply (metis Range.intros trancl_range)
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                   apply (metis A_sub_b Range_Un_eq Range_empty Range_insert UnI2 cvd_CAS_R_success_read_val lib_cvd_exist_write no_Top_n_def)
             apply (metis Null_def Un_commute glb_def insert_is_Un nxt_rel_after_successful_CAS)
                    apply (metis Null_def Un_iff not_dom not_range)
                   apply(elim disjE)
             
             apply blast
             apply blast
             apply blast
             apply blast
                      apply blast 
                     apply blast
                 apply(subgoal_tac "agt ad1 ad2 ps' cls' = agt ad1 ad2 ps cls")
                  apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                     apply(simp add: globals)
                      apply (smt subset_eq successful_CAS_lib_c_obs_lib_diff_value_pres)
                       apply blast

       apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
          using  agt_pushed_successful_cas_before
          apply (metis Null_def glb_def insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
                         apply (metis no_nxt_no_agt)
                        apply(intro allI impI)
          apply (simp add: globals)
          apply (metis neq0_conv succ_CAS_preserves_last)

             apply(intro conjI)
             apply simp
                   apply(subgoal_tac " \<exists>vl. [libTop = ad2]\<lparr>libad2 =\<^sub>t vl \<rparr> cls") 
                    apply(elim exE, rule_tac x = vl in exI)
             apply(simp add: globals)
             
             apply (metis subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                     apply blast


                   apply(subgoal_tac " \<exists>vl. [libTop = ad2]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls") 
                    apply(elim exE, rule_tac x = vl in exI)
             apply(simp add: globals)
             apply (metis successful_CAS_lib_c_obs_lib_diff_value_pres)
                     apply blast
                  apply linarith
                   apply(simp add: written_vals_def)
             apply (smt CAS_Rel_preserves_writes_on_diff_var image_cong write_value_CAS_R_diff_var)

                  apply(cases "pc ps t'"; cases "pc ps t'")
             apply(simp_all add: L5)
          apply(intro conjI)
      apply (metis d_obs_post_CAS_R_diff_var_post)
             apply (metis d_obs_post_CAS_R_diff_var_post)
             using cvd_CAS_R_cvd apply metis
                   apply metis
                   apply(simp add: no_Top_n_def)
                  apply (metis (no_types, lifting) CAS_Rel_new_write_value CAS_Rel_preserves_value_old)
(******)
             apply(simp add: cobs_to_def)
               apply(intro allI impI, elim conjE)
               apply(case_tac "ad1 = n_val ps t'")
                apply(subgoal_tac "ad1 \<notin> pushed_addr ps")
                   apply(elim disjE)
             apply (metis no_Top_n_def no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro surj_pair)
             apply (metis no_Top_n_def no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro surj_pair)          
         apply(subgoal_tac "top ps t' \<noteq> Null")
                         apply(case_tac "ad2 = prog_state.top ps t'")
             apply(simp add: dobs_to_def)
                       apply(subgoal_tac "Suc(ad2) \<noteq> Top \<and> (\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and> (\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and> \<not>[lib(Top) \<approx>\<^sub>t ad1] cls")
                        apply(elim conjE exE, intro conjI)
          apply(rule_tac x = vl in exI)
                              apply (metis glb_inv5_def in_mono successful_CAS_lib_c_obs_lib_only_intro)
             apply (metis successful_CAS_lib_c_obs_lib_only_intro)
                            apply(intro conjI)
             apply(simp add: globals)
             
             apply metis

                        apply(simp add: dobs_to_def)
                        apply(simp add: to_simps globals)
                            apply (meson no_Top_n_implies_no_p_obs)

                       apply(subgoal_tac "Suc(ad2) \<noteq> Top \<and> (\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and> (\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and> \<not>[lib(Top) \<approx>\<^sub>t ad1] cls")
                        apply(elim conjE exE, intro conjI)
          apply(rule_tac x = vl in exI)
                          apply (metis glb_inv5_def in_mono successful_CAS_lib_c_obs_lib_only_intro)
             apply (metis successful_CAS_lib_c_obs_lib_only_intro)
             apply(intro conjI)
             apply(simp add: globals)
             
                              apply metis
                             apply (smt cvd_CAS_R_success_read_val dobs_to_def lastTop_def lib_cvd_exist_last_write to_def to_p2_def)
             apply (smt cvd_CAS_R_success_read_val dobs_to_def lastTop_def lib_cvd_exist_last_write to_def to_p2_def)
             apply (simp add: no_Top_n_implies_no_p_obs)
          apply (metis (no_types, lifting) Null_def TopLV_Null_pushed_empty cvd_CAS_R_success_read_val empty_iff glb_def lastTop_def lib_cvd_exist_last_write)
          apply blast
          apply blast
          apply linarith
          apply linarith
          apply blast
                apply blast
          apply(case_tac "ad2 = n_val ps t'"; case_tac "ad2 \<in> pushed_addr ps")
                  apply blast
                 apply simp
          apply(subgoal_tac "\<not>agt ad1 (n_val ps t') ps' cls'")
          
                  apply blast
                 apply(simp add: agt_def clss_def)
         apply(case_tac "lastTop cls = Null")
         apply(subgoal_tac "pushed_addr ps = {}")
           apply simp
                  apply (simp add: TopLV_Null_pushed_empty)
         apply(subgoal_tac "n_val ps t' \<notin> Domain (nxt_rel ps cls) \<union> Range (nxt_rel ps cls)")
         apply(subgoal_tac "n_val ps t' \<notin> Range (nxt_rel ps' cls')")
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                  apply (metis Range.intros trancl_range)
                   apply (metis Range.intros trancl_range)
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                   apply (metis A_sub_b Range_Un_eq Range_empty Range_insert UnI2 cvd_CAS_R_success_read_val lib_cvd_exist_write no_Top_n_def)
             using nxt_rel_after_successful_CAS
             apply (metis Null_def glb_def inf_sup_aci(5) insert_is_Un)
                          apply (metis Null_def Un_iff not_dom not_range)

             
                    apply(subgoal_tac "(\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls) \<and>
                        (\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                     apply(simp add: globals)
             apply(intro conjI)
                      apply (metis subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
             apply (metis successful_CAS_lib_c_obs_lib_diff_value_pres)
       apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
          using  agt_pushed_successful_cas_before
          apply (metis Null_def glb_def insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
                         apply (metis no_nxt_no_agt)
                        apply(intro allI impI)
          apply (simp add: globals)
          apply (metis neq0_conv succ_CAS_preserves_last)


                  apply (metis)
                   apply (meson CAS_Top_written_addr_post)
                  apply(simp add: written_vals_def)
             apply (smt CAS_Rel_preserves_writes_on_diff_var image_iff write_value_CAS_R_diff_var)
                apply(intro conjI)
             apply (metis d_obs_post_CAS_R_diff_var_post)
                      apply (metis d_obs_post_CAS_R_diff_var_post)
             using cvd_CAS_R_cvd apply auto[1]
             
                   apply metis
             apply(simp add: no_Top_n_def)
             
             apply (metis (no_types, lifting) CAS_Rel_new_write_value CAS_Rel_preserves_value_old)
(****)
                   apply(simp add: cobs_to_def)
               apply(intro allI impI, elim conjE)
               apply(case_tac "ad1 = n_val ps t'")
                apply(subgoal_tac "ad1 \<notin> pushed_addr ps")
                   apply(elim disjE)
             apply (metis no_Top_n_def no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro surj_pair)
             apply (metis no_Top_n_def no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro surj_pair)          
         apply(subgoal_tac "top ps t' \<noteq> Null")
                         apply(case_tac "ad2 = prog_state.top ps t'")
             apply(simp add: dobs_to_def)
                       apply(subgoal_tac "Suc(ad2) \<noteq> Top \<and> (\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and> (\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and>  \<not>[lib(Top) \<approx>\<^sub>t ad1] cls")
                             apply(elim conjE exE)
             apply(intro conjI)
          apply(rule_tac x = vl in exI)
                              apply (metis glb_inv5_def in_mono successful_CAS_lib_c_obs_lib_only_intro)
             
             apply (metis successful_CAS_lib_c_obs_lib_only_intro)
                            apply(intro conjI)
                               apply(simp add: globals)
                               apply metis
                              apply(simp add: dobs_to_def)
                        apply(simp add: to_simps globals)
             apply (meson no_Top_n_implies_no_p_obs)
                       apply(subgoal_tac "Suc(ad2) \<noteq> Top \<and> (\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and> (\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and>  \<not>[lib(Top) \<approx>\<^sub>t ad1] cls")
                        apply(elim conjE exE, intro conjI)
          apply(rule_tac x = vl in exI)
                          apply (metis glb_inv5_def in_mono successful_CAS_lib_c_obs_lib_only_intro)
                            apply (metis successful_CAS_lib_c_obs_lib_only_intro)
                                       apply(intro conjI)
                               apply(simp add: globals)
                              apply metis
             apply (smt cvd_CAS_R_success_read_val dobs_to_def lastTop_def lib_cvd_exist_last_write to_def to_p2_def)
             apply (smt cvd_CAS_R_success_read_val dobs_to_def lastTop_def lib_cvd_exist_last_write no_Top_n_implies_no_p_obs to_def to_p2_def)
             apply (simp add: no_Top_n_implies_no_p_obs)
             apply (metis (no_types, lifting) Null_def TopLV_Null_pushed_empty cvd_CAS_R_success_read_val empty_iff glb_def lastTop_def lib_cvd_exist_last_write)
          apply blast
          apply blast
          apply linarith
          apply linarith
          apply blast
                apply blast
          apply(case_tac "ad2 = n_val ps t'"; case_tac "ad2 \<in> pushed_addr ps")
                  apply blast
                 apply simp
          apply(subgoal_tac "\<not>agt ad1 (n_val ps t') ps' cls'")
          
                  apply blast
                 apply(simp add: agt_def clss_def)
         apply(case_tac "lastTop cls = Null")
         apply(subgoal_tac "pushed_addr ps = {}")
           apply simp
                  apply (simp add: TopLV_Null_pushed_empty)
         apply(subgoal_tac "n_val ps t' \<notin> Domain (nxt_rel ps cls) \<union> Range (nxt_rel ps cls)")
         apply(subgoal_tac "n_val ps t' \<notin> Range (nxt_rel ps' cls')")
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                  apply (metis Range.intros trancl_range)
                   apply (metis Range.intros trancl_range)
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                   apply (metis A_sub_b Range_Un_eq Range_empty Range_insert UnI2 cvd_CAS_R_success_read_val lib_cvd_exist_write no_Top_n_def)
             using nxt_rel_after_successful_CAS
             apply (metis Null_def glb_def inf_sup_aci(5) insert_is_Un)
                          apply (metis Null_def Un_iff not_dom not_range)

             
                    apply(subgoal_tac "(\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls) \<and>
                              (\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                     apply(simp add: globals)
             apply(intro conjI)
                      apply (metis subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
             apply (metis successful_CAS_lib_c_obs_lib_diff_value_pres)
       apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
          using  agt_pushed_successful_cas_before
          apply (metis Null_def glb_def insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
                         apply (metis no_nxt_no_agt)
                        apply(intro allI impI)
          apply (simp add: globals)
          apply (metis neq0_conv succ_CAS_preserves_last)

                 apply (metis)
             apply (simp add: dobs_to_def)
             apply (meson CAS_Top_written_addr_post)
             apply(simp add: written_vals_def)
             
             apply (smt CAS_Rel_preserves_writes_on_diff_var image_iff write_value_CAS_R_diff_var)
             apply(intro conjI)
             apply (metis d_obs_post_CAS_R_diff_var_post)
             apply (metis d_obs_post_CAS_R_diff_var_post)
             apply (metis cvd_CAS_R_success_post cvd_CAS_R_success_read_val)
             
             apply metis
             apply(simp add: no_Top_n_def)
             
             apply (metis (no_types, lifting) CAS_Rel_new_write_value CAS_Rel_preserves_value_old)
                 apply(simp add: written_addr_def)
                 apply (simp add: success_CAS_Top_written_addr_post)
(***)
                   apply(simp add: cobs_to_def)
               apply(intro allI impI, elim conjE)
               apply(case_tac "ad1 = n_val ps t'")
                apply(subgoal_tac "ad1 \<notin> pushed_addr ps")
                   apply(elim disjE)
             apply (metis no_Top_n_def no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro surj_pair)
             apply (metis no_Top_n_def no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro surj_pair)          
         apply(subgoal_tac "top ps t' \<noteq> Null")
                         apply(case_tac "ad2 = prog_state.top ps t'")
             apply(simp add: dobs_to_def)
                       apply(subgoal_tac "Suc(ad2) \<noteq> Top \<and> (\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and> (\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and> \<not>[lib(Top) \<approx>\<^sub>t ad1] cls")
                        apply(elim conjE exE, intro conjI)
          apply(rule_tac x = vl in exI)
                             apply (metis glb_inv5_def in_mono successful_CAS_lib_c_obs_lib_only_intro)
             apply (metis successful_CAS_lib_c_obs_lib_only_intro)
                           apply(intro conjI)
             apply(simp add: globals)              
             apply metis

                        apply(simp add: dobs_to_def)
                        apply(simp add: to_simps globals)
             apply (meson no_Top_n_implies_no_p_obs)
                       apply(subgoal_tac "Suc(ad2) \<noteq> Top \<and> (\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and> (\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and> \<not>[lib(Top) \<approx>\<^sub>t ad1] cls")
                        apply(elim conjE exE)
                          apply (metis glb_inv5_def in_mono successful_CAS_lib_c_obs_lib_only_intro)
                                   apply(intro conjI)
             apply(simp add: globals)              
                             apply metis
             apply (smt cvd_CAS_R_success_read_val dobs_to_def lastTop_def lib_cvd_exist_last_write to_def to_p2_def)
     apply (smt cvd_CAS_R_success_read_val dobs_to_def lastTop_def lib_cvd_exist_last_write no_Top_n_implies_no_p_obs to_def to_p2_def)
             apply (simp add: no_Top_n_implies_no_p_obs)
                          apply (metis (no_types, lifting) Null_def TopLV_Null_pushed_empty cvd_CAS_R_success_read_val empty_iff glb_def lastTop_def lib_cvd_exist_last_write)
          apply blast
          apply blast
          apply linarith
          apply linarith
          apply blast
                apply blast
          apply(case_tac "ad2 = n_val ps t'"; case_tac "ad2 \<in> pushed_addr ps")
                  apply blast
                 apply simp
          apply(subgoal_tac "\<not>agt ad1 (n_val ps t') ps' cls'")
          
                  apply blast
                 apply(simp add: agt_def clss_def)
         apply(case_tac "lastTop cls = Null")
         apply(subgoal_tac "pushed_addr ps = {}")
           apply simp
                  apply (simp add: TopLV_Null_pushed_empty)
         apply(subgoal_tac "n_val ps t' \<notin> Domain (nxt_rel ps cls) \<union> Range (nxt_rel ps cls)")
         apply(subgoal_tac "n_val ps t' \<notin> Range (nxt_rel ps' cls')")
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                  apply (metis Range.intros trancl_range)
                   apply (metis Range.intros trancl_range)
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                   apply (metis A_sub_b Range_Un_eq Range_empty Range_insert UnI2 cvd_CAS_R_success_read_val lib_cvd_exist_write no_Top_n_def)
             using nxt_rel_after_successful_CAS
             apply (metis Null_def glb_def inf_sup_aci(5) insert_is_Un)
                          apply (metis Null_def Un_iff not_dom not_range)

             
                   apply(subgoal_tac "(\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls) \<and>
                          (\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                         apply(simp add: globals)
          apply (metis subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
       apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
          using  agt_pushed_successful_cas_before
          apply (metis Null_def glb_def insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
                         apply (metis no_nxt_no_agt)
                        apply(intro allI impI)
          apply (simp add: globals)
          apply (metis neq0_conv succ_CAS_preserves_last)


                apply (metis)

               apply(simp add: dobs_to_def)
               apply(intro allI impI conjI, elim conjE disjE)

                              apply(simp add: agt_def clss_def)
         apply(case_tac "lastTop cls = Null")
         apply(subgoal_tac "pushed_addr ps = {}")
                  apply (simp add: TopLV_Null_pushed_empty)
         apply(subgoal_tac "n_val ps t' \<notin> Domain (nxt_rel ps cls) \<union> Range (nxt_rel ps cls)")
         apply(subgoal_tac "n_val ps t' \<notin> Range (nxt_rel ps' cls')")
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                  apply (metis Range.intros trancl_range)
                   apply (metis Range.intros trancl_range)
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                   apply (metis A_sub_b Range_Un_eq Range_empty Range_insert UnI2 cvd_CAS_R_success_read_val lib_cvd_exist_write no_Top_n_def)
             using nxt_rel_after_successful_CAS [where a = "n_val ps t'" and b = "top ps t'"
and cls=cls and cls'=cls' and ps = ps and ps'=ps']
                     apply (simp add: TopLV_Null_pushed_empty)
             apply (metis Null_def TopLV_Null_pushed_empty Un_iff empty_iff glb_def not_dom not_range)
                          apply (simp add: TopLV_Null_pushed_empty)

                      apply(subgoal_tac "n_val ps t' \<notin> Domain (nxt_rel ps cls) \<union> Range (nxt_rel ps cls)")
         apply(subgoal_tac "n_val ps t' \<notin> Range (nxt_rel ps' cls')")
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                  apply (metis Range.intros trancl_range)
                   apply (metis Range.intros trancl_range)
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                   apply (metis A_sub_b Range_Un_eq Range_empty Range_insert UnI2 cvd_CAS_R_success_read_val lib_cvd_exist_write no_Top_n_def)
             apply (metis Null_def glb_def insert_is_Un nxt_rel_after_successful_CAS sup_commute)
                   apply (metis Null_def Un_iff not_dom not_range)
                  apply simp
                  apply(subgoal_tac "\<exists>vl. [libad =\<^sub>t vl] cls")
                   apply(elim exE, rule_tac x=vl in exI)
             apply(subgoal_tac "ad \<noteq> Top")
                    apply (metis d_obs_post_CAS_R_diff_var_post)
             apply(simp add: globals)
                  apply blast
                 apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
                  apply blast
                 apply(simp add: no_Top_n_def)
                 apply(subgoal_tac " n_val ps t' \<noteq> top ps t  \<and>  n_val ps t' \<noteq> ad")
             apply(elim conjE)

             using agt_pushed_successful_cas_before[where cls=cls and t=t' and ccs=ccs and cls'=cls'
                 and ps=ps and ps'=ps' and u'="n_val ps t'" and u="top ps t'" and c="top ps t" and ccs'=ccs']


             apply(subgoal_tac "top ps t \<noteq> n_val ps t' \<and>  ad \<noteq> n_val ps t' \<and> top ps t \<in> pushed_addr ps")
                  apply(case_tac "ad \<noteq> top ps t ")

       apply(subgoal_tac "\<not> agt (top ps t) (n_val ps t') ps' cls'")
          using  agt_pushed_successful_cas_before
          apply (metis Null_def glb_def insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
                         apply (metis no_nxt_no_agt)
                        apply(intro allI impI)
          apply (simp add: globals)
          apply (metis neq0_conv succ_CAS_preserves_last)


       apply(subgoal_tac "\<not> agt (top ps t) (n_val ps t') ps' cls'")
          using  agt_pushed_successful_cas_before
          apply (metis Null_def glb_def insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
                         apply (metis no_nxt_no_agt)
                        apply(intro allI impI)
          apply (simp add: globals)
          apply (metis neq0_conv succ_CAS_preserves_last)
          apply (metis agt_ad1_not_in_pushed_False insert_iff)
                 apply auto[1]
           (*  apply(intro conjI)

                    apply linarith
                   apply blast
             apply(subgoal_tac "top ps t \<in> pushed_addr ps'")
                   apply simp
                  apply(simp add: agt_def clss_def nxt_rel_def)
apply(subgoal_tac "top ps t \<noteq> n_val ps t'")
                   apply(simp add: trancl_def)
    using converse_tranclpE 
          apply smt 
         apply linarith
        apply auto[1]
*)
    apply(simp add:globals)
         apply (metis d_obs_post_CAS_R_diff_var_post in_mono)
        apply(elim conjE disjE)
           apply(subgoal_tac "\<not>agt (prog_state.top ps t) ad ps' cls'")
            apply blast
    apply(simp add: agt_def clss_def)
                      apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
             apply(subgoal_tac "n_val ps t' \<notin> Domain (nxt_rel ps cls) \<union> Range (nxt_rel ps cls)")
         apply(subgoal_tac "n_val ps t' \<notin> Range (nxt_rel ps' cls')")
              apply (metis Range.intros trancl_range)
    apply auto[1]
    apply (metis Null_def Un_iff not_dom not_range)
    apply (metis Null_def Un_commute glb_def insert_is_Un nxt_rel_after_successful_CAS)
          apply simp
    apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
    apply(subgoal_tac "(\<exists>vl. [libSuc ad =\<^sub>t vl] cls) \<and> Suc ad \<noteq> Top")
           apply (metis d_obs_post_CAS_R_diff_var_post)
    apply(simp add: globals)
          apply metis
         apply(case_tac "ad \<noteq> top ps t ")
    apply(subgoal_tac "top ps t \<noteq> n_val ps t' \<and> top ps t\<in>pushed_addr ps")
       apply(subgoal_tac "\<not> agt (top ps t) (n_val ps t') ps' cls'")
          using  agt_pushed_successful_cas_before
          apply (metis Null_def glb_def insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
                         apply (metis no_nxt_no_agt)
                        apply(intro allI impI)
          apply (simp add: globals)
          apply (metis neq0_conv succ_CAS_preserves_last)

  apply(intro conjI)
        apply auto[1]
  apply(subgoal_tac "top ps t \<in> pushed_addr ps'")

        apply auto[1]
  apply(simp add: agt_def clss_def )
       apply(intro disjI2)
       apply(subgoal_tac "Domain ((nxt_rel ps' cls')\<^sup>+) = Domain (nxt_rel ps' cls')")
        apply simp
  apply (metis a_not_in_pushed_nxt_rel converse_tranclE insert_iff)
  apply auto[1]
       apply(subgoal_tac "\<not> agt (top ps t) (n_val ps t') ps' cls'")
          using  agt_pushed_successful_cas_before
          apply (metis Null_def glb_def insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
                         apply (metis no_nxt_no_agt)
                        apply(intro allI impI)
          apply (simp add: globals)
          apply (metis neq0_conv succ_CAS_preserves_last)
  apply(subgoal_tac "Suc ad \<noteq> Top")
      apply (metis d_obs_post_CAS_R_diff_var_post)
  apply(simp add: globals)
  apply metis
  apply (meson CAS_Top_written_addr_post)
    apply(simp add: written_vals_def)
  apply (smt CAS_Rel_preserves_writes_on_diff_var image_iff write_value_CAS_R_diff_var)
     apply(intro conjI allI impI)
    apply (metis d_obs_post_CAS_R_diff_var_post)
    apply (metis d_obs_post_CAS_R_diff_var_post)
     
    using cvd_CAS_R_cvd apply auto[1]
    apply (metis succ_CAS_preserves_last)
         apply metis
                   apply(simp add: no_Top_n_def)
    apply (metis (no_types, lifting) CAS_Rel_new_write_value CAS_Rel_preserves_value_old)

(*************)
                   apply(simp add: cobs_to_def)
               apply(intro allI impI, elim conjE)
               apply(case_tac "ad1 = n_val ps t'")
                apply(subgoal_tac "ad1 \<notin> pushed_addr ps")
                   apply(elim disjE)
             apply (metis no_Top_n_def no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro surj_pair)
             apply (metis no_Top_n_def no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro surj_pair)          
         apply(subgoal_tac "top ps t' \<noteq> Null")
                         apply(case_tac "ad2 = prog_state.top ps t'")
             apply(simp add: dobs_to_def)
                       apply(subgoal_tac "Suc(ad2) \<noteq> Top \<and> (\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and>(\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and> \<not>[lib(Top) \<approx>\<^sub>t ad1] cls")
                        apply(elim conjE exE, intro conjI)
          apply(rule_tac x = vl in exI)
                        apply (metis glb_inv5_def in_mono successful_CAS_lib_c_obs_lib_only_intro)
    apply (metis successful_CAS_lib_c_obs_lib_only_intro)
                 apply(intro conjI)
                    apply(simp add: globals)
    apply metis
                        apply(simp add: dobs_to_def)
                        apply(simp add: to_simps globals)
             apply (meson no_Top_n_implies_no_p_obs)
                       apply(subgoal_tac "Suc(ad2) \<noteq> Top \<and> (\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and>(\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and> \<not>[lib(Top) \<approx>\<^sub>t ad1] cls")
                        apply(elim conjE exE, intro conjI)
          apply(rule_tac x = vl in exI)
                          apply (metis glb_inv5_def in_mono successful_CAS_lib_c_obs_lib_only_intro)
                 apply (metis successful_CAS_lib_c_obs_lib_only_intro)
    apply(intro conjI)
                   apply(simp add: globals)
    
                   apply metis
    apply (smt cvd_CAS_R_success_read_val dobs_to_def lastTop_def lib_cvd_exist_last_write to_def to_p2_def)
              apply (smt cvd_CAS_R_success_read_val dobs_to_def lastTop_def lib_cvd_exist_last_write no_Top_n_implies_no_p_obs to_def to_p2_def)
          apply (simp add: no_Top_n_implies_no_p_obs)
       apply (metis (no_types, lifting) Null_def TopLV_Null_pushed_empty cvd_CAS_R_success_read_val empty_iff glb_def lastTop_def lib_cvd_exist_last_write)
          apply blast
          apply blast
          apply linarith
          apply linarith
          apply blast
                apply blast
          apply(case_tac "ad2 = n_val ps t'"; case_tac "ad2 \<in> pushed_addr ps")
                  apply blast
                 apply simp
          apply(subgoal_tac "\<not>agt ad1 (n_val ps t') ps' cls'")
          
                  apply blast
                 apply(simp add: agt_def clss_def)
         apply(case_tac "lastTop cls = Null")
         apply(subgoal_tac "pushed_addr ps = {}")
           apply simp
                  apply (simp add: TopLV_Null_pushed_empty)
         apply(subgoal_tac "n_val ps t' \<notin> Domain (nxt_rel ps cls) \<union> Range (nxt_rel ps cls)")
         apply(subgoal_tac "n_val ps t' \<notin> Range (nxt_rel ps' cls')")
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                  apply (metis Range.intros trancl_range)
                   apply (metis Range.intros trancl_range)
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                   apply (metis A_sub_b Range_Un_eq Range_empty Range_insert UnI2 cvd_CAS_R_success_read_val lib_cvd_exist_write no_Top_n_def)
             using nxt_rel_after_successful_CAS
             apply (metis Null_def glb_def inf_sup_aci(5) insert_is_Un)
                          apply (metis Null_def Un_iff not_dom not_range)
                  apply(subgoal_tac "(\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls) \<and>
                              (\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                   apply(simp add: globals)
             apply(intro conjI)
                    apply (metis subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply (metis successful_CAS_lib_c_obs_lib_diff_value_pres)
                   apply(elim conjE disjE)
             apply blast
                    
             apply linarith
             
             apply blast
             
                       apply linarith
             apply blast
                     apply blast
             apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast
       apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
          using  agt_pushed_successful_cas_before
          apply (metis Null_def glb_def insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
                         apply (metis no_nxt_no_agt)
                        apply(intro allI impI)
          apply (simp add: globals)
          apply (metis neq0_conv succ_CAS_preserves_last)
      apply blast
             apply (metis)
             
             apply (simp add: dobs_to_def)
                apply (meson CAS_Top_written_addr_post)
               apply(simp add: written_vals_def)
             apply (smt CAS_Rel_preserves_writes_on_diff_var image_iff write_value_CAS_R_diff_var)
          apply(simp add: dobs_to_def)
               apply(intro allI impI conjI, elim conjE disjE)
        apply (metis d_obs_post_CAS_R_diff_var_post)
        apply (metis d_obs_post_CAS_R_diff_var_post)
             using cvd_CAS_R_cvd apply auto[1]
             apply (metis succ_CAS_preserves_last)
                   apply metis
apply(simp add: no_Top_n_def)                             
                  apply (metis (no_types, lifting) CAS_Rel_new_write_value CAS_Rel_preserves_value_old)
 
(********)             
                   apply(simp add: cobs_to_def)
               apply(intro allI impI , elim conjE)
               apply(case_tac "ad1 = n_val ps t'")
                apply(subgoal_tac "ad1 \<notin> pushed_addr ps")
                   apply(elim disjE)
             apply (metis no_Top_n_def no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro surj_pair)
             apply (metis no_Top_n_def no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro surj_pair)          
         apply(subgoal_tac "top ps t' \<noteq> Null")
                         apply(case_tac "ad2 = prog_state.top ps t'")
             apply(simp add: dobs_to_def)
                       apply(subgoal_tac "Suc(ad2)\<noteq>Top \<and> (\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and> (\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and> \<not>[lib(Top) \<approx>\<^sub>t ad1] cls")
                        apply(elim conjE exE, intro conjI)
          apply(rule_tac x = vl in exI)
                             apply (metis glb_inv5_def in_mono successful_CAS_lib_c_obs_lib_only_intro)
             apply (metis successful_CAS_lib_c_obs_lib_only_intro)
                           apply(intro conjI)
                              apply(simp add: globals)
             apply metis
                        apply(simp add: dobs_to_def)
                        apply(simp add: to_simps globals)
             apply (meson no_Top_n_implies_no_p_obs)
                       apply(subgoal_tac "Suc(ad2)\<noteq>Top \<and> (\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and> (\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and> \<not>[lib(Top) \<approx>\<^sub>t ad1] cls")
                        apply(elim conjE exE, intro conjI)
          apply(rule_tac x = vl in exI)
                          apply (metis glb_inv5_def in_mono successful_CAS_lib_c_obs_lib_only_intro)
                           apply (metis successful_CAS_lib_c_obs_lib_only_intro)
                          apply(intro conjI)
                             apply(simp add: globals)
                             apply metis
             apply (metis Null_def TopLV_agt_others cvd_CAS_R_success_read_val glb_def lastTop_def lib_cvd_exist_last_write neq0_conv)
                      
             apply (metis Null_def TopLV_agt_others cvd_CAS_R_success_read_val glb_def lastTop_def lib_cvd_exist_last_write neq0_conv)
                       apply (simp add: no_Top_n_implies_no_p_obs)
          apply (metis (no_types, lifting) Null_def TopLV_Null_pushed_empty cvd_CAS_R_success_read_val empty_iff glb_def lastTop_def lib_cvd_exist_last_write)
          apply blast
          apply blast
          apply linarith
          apply linarith
          apply blast
                apply blast
          apply(case_tac "ad2 = n_val ps t'"; case_tac "ad2 \<in> pushed_addr ps")
                  apply blast
                 apply simp
          apply(subgoal_tac "\<not>agt ad1 (n_val ps t') ps' cls'")
          
                  apply blast
                 apply(simp add: agt_def clss_def)
         apply(case_tac "lastTop cls = Null")
         apply(subgoal_tac "pushed_addr ps = {}")
           apply simp
                  apply (simp add: TopLV_Null_pushed_empty)
         apply(subgoal_tac "n_val ps t' \<notin> Domain (nxt_rel ps cls) \<union> Range (nxt_rel ps cls)")
         apply(subgoal_tac "n_val ps t' \<notin> Range (nxt_rel ps' cls')")
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                  apply (metis Range.intros trancl_range)
                   apply (metis Range.intros trancl_range)
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                   apply (metis A_sub_b Range_Un_eq Range_empty Range_insert UnI2 cvd_CAS_R_success_read_val lib_cvd_exist_write no_Top_n_def)
             using nxt_rel_after_successful_CAS
             apply (metis Null_def glb_def inf_sup_aci(5) insert_is_Un)
                    apply (metis Null_def Un_iff not_dom not_range)
             
                   apply(subgoal_tac "(\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls) \<and>
                          (\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                         apply(simp add: globals)
          apply (metis subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                apply(elim conjE disjE)
             apply blast
                    
             apply linarith
             
             apply blast
             
                       apply linarith
             apply blast
                     apply blast
             apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast
       apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
          using  agt_pushed_successful_cas_before
          apply (metis Null_def glb_def insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
                         apply (metis no_nxt_no_agt)
                        apply(intro allI impI)
          apply (simp add: globals)
          apply (metis neq0_conv succ_CAS_preserves_last)
      apply blast
                 apply (metis)
                apply(elim conjE)

                apply(elim disjE conjE)
                   apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
             apply(simp add:globals)
             apply(subgoal_tac "\<not>agt (prog_state.top ps t) (n_val ps t') ps' cls'")
                     apply blast
                 apply(simp add: agt_def clss_def)
         apply(subgoal_tac "n_val ps t' \<notin> Domain (nxt_rel ps cls) \<union> Range (nxt_rel ps cls)")
         apply(subgoal_tac "n_val ps t' \<notin> Range (nxt_rel ps' cls')")
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                  apply (metis Range.intros trancl_range)
                      apply (metis Range.intros trancl_range)
                     apply (metis Range.intros UnI2 trancl_range)
                    apply(simp add:globals no_Top_n_def)
                    apply (metis Null_def Range.intros assms(6) not_range trancl_range)

                   apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                    apply simp

                 apply(simp add: agt_def clss_def)
         apply(subgoal_tac "n_val ps t' \<notin> Domain (nxt_rel ps cls) \<union> Range (nxt_rel ps cls)")
         apply(subgoal_tac "n_val ps t' \<notin> Range (nxt_rel ps' cls')")
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                  apply (metis Range.intros trancl_range)
                      apply (metis Range.intros trancl_range)
                     apply auto[1]
                          apply (metis Null_def Un_iff not_dom not_range)
                          apply (metis Null_def Un_commute glb_def insert_is_Un nxt_rel_after_successful_CAS)
                          apply simp
                 apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
                  apply(subgoal_tac "\<exists>vl. [libad =\<^sub>t vl] cls") 
                   apply(elim conjE exE)
             apply(rule_tac x= vl in exI)
                   apply(simp add: globals)
             apply (metis d_obs_post_CAS_R_diff_var_post in_mono)
                  apply blast
             apply(subgoal_tac "n_val ps t' \<noteq> prog_state.top ps t \<and> prog_state.top ps t \<in> pushed_addr ps")


       apply(subgoal_tac "\<not> agt (top ps t) (n_val ps t') ps' cls' \<and> glb_inv ps cls \<and>
               to ps cls")
          using  agt_pushed_successful_cas_before[where ccs=ccs and cls=cls and ps=ps and
ps'=ps' and cls'=cls' and ccs'=ccs' and c="top ps t" and u'="(n_val ps t')" and t=t']
          apply simp
                  apply (metis Un_commute agt_pushed_successful_cas assms(6) insert_is_Un)
                 apply (simp add: globals)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
                         apply (metis no_nxt_no_agt)
                        apply(intro allI impI)
                 apply (simp add: globals)
          
          apply (metis neq0_conv succ_CAS_preserves_last)

          apply(intro conjI)
  apply force
  apply(simp add: agt_def clss_def nxt_rel_def)
  apply(simp add: trancl_def)
    using converse_tranclpE 
        apply smt 
    apply(simp add: globals)
       apply (metis d_obs_post_CAS_R_diff_var_post in_mono)
(**)
        apply(elim conjE disjE)
           apply(subgoal_tac "\<not>agt (prog_state.top ps t) ad ps' cls'")
            apply blast
    apply(simp add: agt_def clss_def)
                      apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
             apply(subgoal_tac "n_val ps t' \<notin> Domain (nxt_rel ps cls) \<union> Range (nxt_rel ps cls)")
         apply(subgoal_tac "n_val ps t' \<notin> Range (nxt_rel ps' cls')")
              apply (metis Range.intros trancl_range)
    apply auto[1]
    apply (metis Null_def Un_iff not_dom not_range)
    apply (metis Null_def Un_commute glb_def insert_is_Un nxt_rel_after_successful_CAS)
          apply simp
    apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
    apply(subgoal_tac "(\<exists>vl. [libSuc ad =\<^sub>t vl] cls) \<and> Suc ad \<noteq> Top")
           apply (metis d_obs_post_CAS_R_diff_var_post)
    apply(simp add: globals)
          apply metis
         apply(case_tac "ad \<noteq> top ps t ")
    apply(subgoal_tac "top ps t \<noteq> n_val ps t' \<and> top ps t\<in>pushed_addr ps")
       apply(subgoal_tac "\<not> agt (top ps t) (n_val ps t') ps' cls'")
          using  agt_pushed_successful_cas_before
          apply (metis Null_def glb_def insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
                         apply (metis no_nxt_no_agt)
                        apply(intro allI impI)
          apply (simp add: globals)
          apply (metis neq0_conv succ_CAS_preserves_last)
  apply(intro conjI)
        apply auto[1]
  apply(subgoal_tac "top ps t \<in> pushed_addr ps'")

        apply auto[1]
  apply(simp add: agt_def clss_def )
       apply(intro disjI2)
       apply(subgoal_tac "Domain ((nxt_rel ps' cls')\<^sup>+) = Domain (nxt_rel ps' cls')")
        apply simp
  apply (metis a_not_in_pushed_nxt_rel converse_tranclE insert_iff)
  apply auto[1]
       apply(subgoal_tac "\<not> agt (top ps t) (n_val ps t') ps' cls'")
          using  agt_pushed_successful_cas_before
          apply (metis Null_def glb_def insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
                         apply (metis no_nxt_no_agt)
                        apply(intro allI impI)
          apply (simp add: globals)
               apply (metis neq0_conv succ_CAS_preserves_last)
              apply(subgoal_tac "Suc ad \<noteq> Top")
      apply (metis d_obs_post_CAS_R_diff_var_post)
  apply(simp add: globals)
  apply metis
(**)
    apply (meson CAS_Top_written_addr_post)
    
    apply (metis Null_def Un_iff success_CAS_Top_written_addr_post2)
  apply(simp add: written_vals_def)
  apply (smt CAS_Rel_preserves_writes_on_diff_var image_iff write_value_CAS_R_diff_var)

     apply(intro conjI allI impI)
    apply (metis d_obs_post_CAS_R_diff_var_post)
    apply (metis d_obs_post_CAS_R_diff_var_post)
     
    using cvd_CAS_R_cvd apply auto[1]
    
     apply metis


(************)
                   apply(simp add: cobs_to_def)
               apply(intro allI impI, elim conjE)
               apply(case_tac "ad1 = n_val ps t'")
                apply(subgoal_tac "ad1 \<notin> pushed_addr ps")
                   apply(elim disjE)
             apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro )
             apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro )          
    apply(subgoal_tac "top ps t' \<noteq> Null")
                         apply(case_tac "ad2 = prog_state.top ps t'")
             apply(simp add: dobs_to_def) 
          apply(subgoal_tac "Suc(ad2) \<noteq> Top \<and> (\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and> (\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and> \<not>[lib(Top) \<approx>\<^sub>t ad1] cls")
                        apply(elim conjE exE, intro conjI)
          apply(rule_tac x = vl in exI)
               apply (metis glb_inv5_def in_mono successful_CAS_lib_c_obs_lib_only_intro)
    apply (metis successful_CAS_lib_c_obs_lib_only_intro)
             apply(intro conjI)
    apply(simp add: globals)
    apply metis
                        apply(simp add: dobs_to_def)
                        apply(simp add: to_simps globals)
             apply (meson no_Top_n_implies_no_p_obs)

          apply(subgoal_tac "Suc(ad2) \<noteq> Top \<and> (\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and> (\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and> \<not>[lib(Top) \<approx>\<^sub>t ad1] cls")
                        apply(elim conjE exE, intro conjI)
          apply(rule_tac x = vl in exI)
                          apply (metis glb_inv5_def in_mono successful_CAS_lib_c_obs_lib_only_intro)
             apply (metis successful_CAS_lib_c_obs_lib_only_intro) 
            apply(intro conjI)
    apply(simp add: globals)
    
    apply metis
    apply (smt cvd_CAS_R_success_read_val dobs_to_def lastTop_def lib_cvd_exist_last_write to_def to_p2_def)
    apply (smt cvd_CAS_R_success_read_val dobs_to_def lastTop_def lib_cvd_exist_last_write to_def to_p2_def)
    apply (simp add: no_Top_n_implies_no_p_obs)
    apply (metis (no_types, lifting) Null_def TopLV_Null_pushed_empty cvd_CAS_R_success_read_val empty_iff glb_def lastTop_def lib_cvd_exist_last_write)
          apply blast
          apply blast
          apply linarith
          apply linarith
          apply blast
                apply blast
          apply(case_tac "ad2 = n_val ps t'"; case_tac "ad2 \<in> pushed_addr ps")
                  apply blast
                 apply simp
          apply(subgoal_tac "\<not>agt ad1 (n_val ps t') ps' cls'")
          
                  apply blast
                 apply(simp add: agt_def clss_def)
         apply(case_tac "lastTop cls = Null")
         apply(subgoal_tac "pushed_addr ps = {}")
           apply simp
                  apply (simp add: TopLV_Null_pushed_empty)
         apply(subgoal_tac "n_val ps t' \<notin> Domain (nxt_rel ps cls) \<union> Range (nxt_rel ps cls)")
         apply(subgoal_tac "n_val ps t' \<notin> Range (nxt_rel ps' cls')")
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                  apply (metis Range.intros trancl_range)
                   apply (metis Range.intros trancl_range)
              apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t', top ps t')}")
                   apply (metis A_sub_b Range_Un_eq Range_empty Range_insert UnI2 cvd_CAS_R_success_read_val lib_cvd_exist_write no_Top_n_def)
             using nxt_rel_after_successful_CAS
             apply (metis Null_def glb_def inf_sup_aci(5) insert_is_Un)
                          apply (metis Null_def Un_iff not_dom not_range)
              apply(subgoal_tac "(\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls) \<and>
                              (\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)")
                         apply(simp add: globals)
          apply (metis subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
          (*   using agt_pushed_successful_cas_before          
             apply (metis Un_insert_right sup_bot.right_neutral)*)

                   apply(elim conjE disjE)
             apply blast
                    
             apply linarith
             
             apply blast
             
                       apply linarith
             apply blast
                     apply blast
             apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast
       apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
          using  agt_pushed_successful_cas_before
          apply (metis Null_def glb_def insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
                         apply (metis no_nxt_no_agt)
                        apply(intro allI impI)
          apply (simp add: globals)
          apply (metis neq0_conv succ_CAS_preserves_last)
      apply blast
                 apply (metis)
             done
         next
        case False
        then show ?thesis
          using assms
          apply simp
          apply(cases "pc ps t'"; simp add: L5; cases "pc ps t"; simp add: no_Top_n_a_def new_node_def no_Top_n_def)
          apply(intro conjI)
          apply (meson failed_CASR_pres_d_obs_lib)
          apply (meson cvd_CAS_R_cvd)
          using CAS_Rel_preserves_value_old failed_CAS_Rel_preserves_writes_on_diff_var apply force
          apply(simp add: cobs_to_def)       
               apply (metis agt_def clss_same failed_CASR_pres_c_obs_lib_only failed_cas_preserves_clss)
               apply(simp add: addr_init_writes_def written_vals_def new_node_def)
               apply(intro conjI allI impI)

          apply (metis (no_types, lifting) failed_CAS_Rel_preserves_writes_on_diff_var image_cong write_value_CAS_R_diff_var)
                   apply (metis (no_types, lifting) failed_CAS_Rel_preserves_writes_on_diff_var image_cong write_value_CAS_R_diff_var)
      apply(intro conjI)
          apply (meson failed_CASR_pres_d_obs_lib)
          apply (metis failed_CASR_pres_d_obs_lib)
          using CAS_Rel_preserves_value_old failed_CAS_Rel_preserves_writes_on_diff_var apply force
          
          apply (meson cvd_CAS_R_cvd)      
                            
                 apply auto[1]                           
          using CAS_Rel_preserves_value_old failed_CAS_Rel_preserves_writes_on_diff_var apply force
          using failed_CAS_Top_written_addr_post2 apply auto[1]

                apply(simp add: cobs_to_def)     
   apply (metis agt_def clss_same failed_CASR_pres_c_obs_lib_only failed_cas_preserves_clss)
              apply(simp add: written_vals_def)
          apply (smt failed_CAS_Rel_preserves_writes_on_diff_var image_cong write_value_CAS_R_diff_var)



             apply(intro allI impI conjI)
          apply (metis d_obs_post_CAS_R_diff_var_post)
          apply (metis d_obs_post_CAS_R_diff_var_post)
                 apply metis
          using cvd_CAS_R_cvd apply blast
          apply metis
          using CAS_Rel_preserves_value_old failed_CAS_Rel_preserves_writes_on_diff_var apply metis
          using CAS_Rel_preserves_value_old failed_CAS_Rel_preserves_writes_on_diff_var apply metis
                         apply(simp add: cobs_to_def)     
              apply (metis agt_def clss_same failed_CASR_pres_c_obs_lib_only failed_cas_preserves_clss)
          
          using failed_CAS_Top_written_addr_post2 apply blast
              apply(simp add: written_vals_def)
             apply (smt failed_CAS_Rel_preserves_writes_on_diff_var image_iff write_value_CAS_R_diff_var)
   apply(intro allI impI conjI)
          apply (metis d_obs_post_CAS_R_diff_var_post)
          apply (metis d_obs_post_CAS_R_diff_var_post)               
                 apply metis
          using cvd_CAS_R_cvd apply blast          
          apply metis
          using CAS_Rel_preserves_value_old failed_CAS_Rel_preserves_writes_on_diff_var apply metis
          
          using CAS_Rel_preserves_value_old failed_CAS_Rel_preserves_writes_on_diff_var apply metis
               apply (metis (full_types) failed_CAS_Top_written_addr_post written_addr_def)
                            apply(simp add: cobs_to_def)     
              apply (metis agt_def clss_same failed_CASR_pres_c_obs_lib_only failed_cas_preserves_clss)
          using failed_cas_dobs_to
             apply blast
          using failed_CAS_Top_written_addr_post2 apply blast
          apply(simp add: written_vals_def)
          
          apply (smt failed_CAS_Rel_preserves_writes_on_diff_var image_iff write_value_CAS_R_diff_var)

             apply(intro allI impI conjI)
          apply (metis d_obs_post_CAS_R_diff_var_post)               
          apply (metis d_obs_post_CAS_R_diff_var_post)           
                 apply metis
          using cvd_CAS_R_cvd apply blast
                         using failed_CAS_preserves_last apply metis
          apply metis
          using CAS_Rel_preserves_value_old failed_CAS_Rel_preserves_writes_on_diff_var apply metis          
          using CAS_Rel_preserves_value_old failed_CAS_Rel_preserves_writes_on_diff_var apply metis
              apply(simp add: cobs_to_def)
          apply (metis agt_def clss_same failed_CASR_pres_c_obs_lib_only failed_cas_preserves_clss)
          using failed_cas_dobs_to apply blast
          using failed_CAS_Top_written_addr_post2 apply blast
          
          using failed_CAS_Top_written_addr_post2 apply blast
          apply(simp add: written_vals_def)
          apply (smt failed_CAS_Rel_preserves_writes_on_diff_var image_iff write_value_CAS_R_diff_var)
              apply(intro allI impI conjI)
          apply (metis d_obs_post_CAS_R_diff_var_post)              
          apply (metis d_obs_post_CAS_R_diff_var_post)             
                 apply metis
          using cvd_CAS_R_cvd apply blast
          using failed_CAS_preserves_last apply metis
          apply(simp add: cobs_to_def)
           apply (metis agt_def clss_same failed_CASR_pres_c_obs_lib_only failed_cas_preserves_clss)
          done
         qed
      then have "push_inv t v (pc ps' t) cls' ccs' ps'"
        using assms
        by(cases "pc ps t"; simp add: glb_inv14_def; elim exE conjE; simp)
    next
      case L6
      then show ?thesis           
        using assms
        by(cases "pc ps t"; simp add: glb_inv14_def; elim exE conjE; simp)
    qed
end
