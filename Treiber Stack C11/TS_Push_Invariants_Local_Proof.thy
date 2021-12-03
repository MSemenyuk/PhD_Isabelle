theory TS_Push_Invariants_Local_Proof
imports  TS_Proof_Rules
begin



(*mma nxt_rel_after_successful_CAS: "glb ps cls \<Longrightarrow> glb_inv ps cls \<Longrightarrow> to ps cls \<Longrightarrow> 
        cls ccs CAS\<^sup>R[lib(Top), True, b, a]\<^sub>t cls' ccs' \<Longrightarrow> lib_value cls
        (lib_lastWr cls (Suc (a))) =
       b \<Longrightarrow>a\<in>addr_val ps \<Longrightarrow> a\<notin>pushed_addr ps \<Longrightarrow>
         pushed_addr ps' = pushed_addr ps \<union> {a} \<Longrightarrow> nxt_rel ps' cls' =
       nxt_rel ps cls \<union>
       {(a, b)}"
  apply(simp add: nxt_rel_def globals to_simps)
  apply safe
  apply (metis (full_types) succ_CAS_preserves_last)
  apply (metis (full_types) succ_CAS_preserves_last)
  apply (metis (full_types) succ_CAS_preserves_last)
  apply (metis (full_types) succ_CAS_preserves_last)
  apply (metis (full_types) succ_CAS_preserves_last)
  apply (metis (full_types) succ_CAS_preserves_last)
  apply (metis (full_types) succ_CAS_preserves_last)
  apply (metis (full_types) succ_CAS_preserves_last)
  apply (metis (full_types) succ_CAS_preserves_last)
  apply (metis (full_types) succ_CAS_preserves_last)
  done



lemma written_vals_write: "cls ccs [lib(x) := v]\<^sub>t cls' ccs' \<Longrightarrow> written_vals cls' x =  written_vals cls x \<union> {v}"
  apply(simp add: lib_write_step_def written_vals_def, elim exE conjE)
  apply(simp add: lib_write_def all_updates_l lib_writes_on_def var_def tst_def lib_value_def)
  apply safe
     apply simp
  apply auto[1]
  apply (smt Lib.lib_write_record.select_convs(1) a_is_x fst_conv image_iff mem_Collect_eq)
  by (smt fresh_ts_not_in_writes image_iff mem_Collect_eq)

lemma written_vals_write_diff_var: "cls ccs [lib(y) := v]\<^sub>t cls' ccs' \<Longrightarrow> x\<noteq>y \<Longrightarrow> written_vals cls' x =  written_vals cls x"
  apply(simp add: lib_write_step_def written_vals_def, elim exE conjE)
  apply(simp add: lib_write_def all_updates_l lib_writes_on_def var_def tst_def lib_value_def)
  apply safe
     apply simp
  apply auto[1]
    apply (smt Lib.lib_write_record.select_convs(1) a_is_x fst_conv image_iff mem_Collect_eq)
  apply (smt fresh_ts_not_in_writes image_iff mem_Collect_eq)
  by (smt fresh_ts_not_in_writes image_iff mem_Collect_eq)


lemma written_vals_CAS_Rel_diff_var: "cls ccs CAS\<^sup>R[lib(y), b, v, v']\<^sub>t cls' ccs' \<Longrightarrow> x\<noteq>y \<Longrightarrow> written_vals cls' x =  written_vals cls x"
  apply(simp add: lib_CAS_Rel_step_def written_vals_def, elim exE conjE)
  apply(case_tac "lib_value cls (a, ba) = v", simp_all)
  apply(simp add: lib_update_r_def all_updates_l lib_writes_on_def var_def tst_def lib_value_def)
  apply safe
     apply simp
  apply auto[1]
    apply (smt Lib.lib_write_record.select_convs(1) a_is_x fst_conv image_iff mem_Collect_eq)
  apply (smt fresh_ts_not_in_writes image_iff mem_Collect_eq)
    apply (smt fresh_ts_not_in_writes image_iff mem_Collect_eq)
  apply(simp add: lib_read_def all_updates_l lib_writes_on_def var_def tst_def lib_value_def)
  apply auto[1]
  apply(simp add: lib_read_def all_updates_l lib_writes_on_def var_def tst_def lib_value_def)
  apply auto[1]
  done*)

lemma push_inv:
  assumes "wfs ccs"
      and "lib_wfs cls ccs"
      and "lib_push t v ps cls ccs ps' cls' ccs'"
      and "push_inv t v (pc ps t) cls ccs  ps"
      and "glb_inv ps cls"
      and "to ps cls"
      and "glb ps cls"
    shows "push_inv t v (pc ps' t) cls' ccs'  ps'"
    proof (cases "pc ps' t")
      case L5
      then show ?thesis
                  using assms
          apply(cases "pc ps t"; simp; elim exE conjE; simp)
               apply(simp add: globals)
                   apply(intro conjI impI allI, elim conjE exE)
                  apply (meson d_obs_write_diff_var n_not_Suc_n)
                      using d_obs_write apply auto[1]
                         apply (metis lib_covered_write_diff_var_pres)
                        apply(subgoal_tac " [libSuc (n_val ps t) =\<^sub>t (top ps t)] cls'")
                      apply(simp add: lib_d_obs_def lib_d_obs_t_def)
                      using d_obs_write apply auto[1]
                       apply(simp add: no_Top_n_def)
                       apply(intro allI impI conjI)
                    apply(simp add: lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
                     apply(simp add: lib_writes_on_def lib_value_def)
                        apply (metis a_is_x)
                    apply(simp add: lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
                     apply(simp add: lib_writes_on_def lib_value_def)
                         apply (metis a_is_x)
                      defer
                         defer
                          apply (metis diff_var_write_written_addr)         
                          apply (metis diff_var_write_written_addr)
                      using written_vals_write apply auto[1]
                       apply fastforce
                      apply(simp add: cobs_to_def)
                      apply(intro conjI impI allI, elim conjE exE disjE)
                   apply(subgoal_tac "written_addr cls' = written_addr cls")
                        apply(subgoal_tac "agt ad1 ad2 ps cls = agt ad1 ad2 ps' cls'", simp)
   apply (smt image_cong lib_c_obs_lib_only_pres_wr_diff_var wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
     using agt_pushed_same2wr_nxt_before_state[where a="n_val ps t" and ccs=ccs 
          and cls=cls and cls'=cls' and ccs'=ccs' and ps=ps and ps'=ps' and t=t and v="prog_state.top ps t"]    
       apply (simp add: assms(5))
     apply(subgoal_tac "Top \<noteq> Suc (n_val ps t)")
     apply(simp add: no_Top_n_def globals)
     using diff_var_write_written_addr
       apply force
     apply fastforce
      apply (metis  lib_c_obs_lib_only_pres_wr_diff_var)
      apply(simp add: dobs_to_def)
     apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc ad2 =\<^sub>t vl \<rparr> cls")
     apply (metis Suc_eq_plus1 add_right_imp_eq lib_c_obs_lib_only_pres_wr_diff_var)

       apply (metis add.commute agt_pushed_same2wr_nxt_before_state assms(5) plus_1_eq_Suc same_except_for_pc_and_top_def)
     apply(simp add: dobs_to_def)
     apply(intro conjI allI impI)
      apply (metis \<open>\<And>d ca. \<lbrakk>glb_inv ps cls; n_val ps t \<notin> pushed_addr ps; n_val ps t \<in> addr_val ps; cls ccs [lib(n_val ps t + 1) := prog_state.top ps t]\<^sub>t cls' ccs'; agt ca d ps' cls'; same_except_for_pc_and_top ps ps'\<rbrakk> \<Longrightarrow> agt ca d ps cls\<close> add.commute assms(5) d_obs_write_diff_var plus_1_eq_Suc same_except_for_pc_and_top_def)
     by (metis Suc_inject \<open>\<And>d ca. \<lbrakk>glb_inv ps cls; n_val ps t \<notin> pushed_addr ps; n_val ps t \<in> addr_val ps; cls ccs [lib(n_val ps t + 1) := prog_state.top ps t]\<^sub>t cls' ccs'; agt ca d ps' cls'; same_except_for_pc_and_top ps ps'\<rbrakk> \<Longrightarrow> agt ca d ps cls\<close> add.commute assms(5) d_obs_write_diff_var plus_1_eq_Suc same_except_for_pc_and_top_def)
  next
      case L1
      then show ?thesis
          using assms
          apply(cases "pc ps t"; simp; elim exE conjE; simp)
          apply(intro conjI)
               apply fastforce
          apply auto[1]
          using fun_upd_def by auto
    next
      case L2
      then show ?thesis
              using assms
          apply(cases "pc ps t"; simp; elim exE conjE; simp)
               apply(simp add: globals)
               apply(intro conjI impI allI, elim conjE exE)             
                       apply (meson assms(3) lib_push_L1_new_address_not_null)            
              apply (metis Null_def assms(3) lib_push_L1_new_address_not_null)              
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
              apply(simp add: cobs_to_def)
                apply (metis agt_pushed_same2 assms(3) lib_push_L1_pushed)
              apply (simp add: addr_init_writes_def)
              by auto
    next
      case L3
      then show ?thesis
                  using assms
          apply(cases "pc ps t"; simp; elim exE conjE; simp)
               apply(simp add: globals)
                   apply(intro conjI impI allI; elim conjE exE)
                  using d_obs_write apply auto[1]
                  apply (metis d_obs_write_diff_var n_not_Suc_n)
                    apply (metis lib_covered_write_diff_var_pres)
                   apply(simp add: no_Top_n_def)
                   apply(intro conjI impI allI)
                    apply(simp add: lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
                     apply(simp add: lib_writes_on_def lib_value_def)
                  apply (metis a_is_x)
                        apply(simp add: lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
                     apply(simp add: lib_writes_on_def lib_value_def)
                    apply (metis a_is_x)
                   apply(simp add: cobs_to_def)
                   apply(intro conjI impI allI; elim conjE exE disjE)
                   apply(subgoal_tac "written_addr cls' = written_addr cls")
                     apply(subgoal_tac "agt ad1 ad2 ps cls = agt ad1 ad2 ps' cls'", simp)               
                       apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
                  apply simp
                  apply (simp add: agt_pushed_same2wr_before_state assms(5))
                    apply (metis diff_var_write_written_addr)
                    apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
                  apply (metis agt_pushed_same2wr_before_state assms(5) lib_c_obs_lib_only_pres_wr_diff_var same_except_for_pc_and_top_def)
                  apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
                  apply (metis diff_var_write_written_addr)
                  using written_vals_write_diff_var
                  apply auto[1]
      apply(simp add: globals)
                    apply(intro conjI impI allI; elim conjE exE)
             apply (metis d_obs_CAS_R_diff_var)
             apply (metis d_obs_CAS_R_diff_var)
                           apply (meson cvd_CAS_R_cvd)
             apply auto[1]
                   apply auto[1]
                  apply(simp add: no_Top_n_def)
                  apply(intro conjI impI allI)
                   apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
                  apply(case_tac "lib_value cls (aa, ba) = prog_state.top ps t", simp_all)
                     apply(simp add: lib_writes_on_def lib_value_def lib_read_def all_updates_l)
                    apply blast
                   apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
                  apply(case_tac "lib_value cls (aa, ba) = prog_state.top ps t", simp_all)
                     apply(simp add: lib_writes_on_def lib_value_def lib_read_def all_updates_l)
                   apply blast
                  apply(case_tac "\<not> res ps' t")
                    apply(simp add: cobs_to_def;intro conjI impI allI ; elim exE conjE disjE)
                  apply(subgoal_tac "agt ad1 ad2 ps' cls' = agt ad1 ad2 ps cls")
                  apply (metis failed_CASR_pres_c_obs_lib_only)
                  apply (metis agt_pushed_failed_cas_before_state agt_pushed_same2 assms(5) same_except_for_pc_and_top_def)
                     apply (metis failed_CASR_pres_c_obs_lib_only)
                      apply(subgoal_tac "agt ad1 ad2 ps' cls' = agt ad1 ad2 ps cls")
                  apply (metis failed_CASR_pres_c_obs_lib_only)
                  apply (metis agt_pushed_failed_cas_before_state agt_pushed_same2 assms(5) same_except_for_pc_and_top_def)
                            apply (metis failed_CASR_pres_c_obs_lib_only)
                    apply(simp add: cobs_to_def; elim exE conjE disjE)
                  apply (metis (mono_tags, lifting) PC.distinct(23) failed_CAS_Top_written_addr_post2 fun_upd_same)
                  using written_vals_CAS_Rel_diff_var  
                  by (metis (mono_tags, lifting) )
              next
      case L4
      then show ?thesis
                      using assms
          apply(cases "pc ps t"; simp; elim exE conjE; simp)
               apply(simp add: globals)
                       apply(intro conjI impI allI; elim conjE exE)
                          apply (meson lib_d_obs_pres_read)
                         apply (meson lib_d_obs_pres_read)
                      apply (meson lib_read_cvd_pres)
                      apply (simp add: lib_value_read_pres no_Top_n_def read_pres_writes_on_diff_var)
                       apply(simp add: written_addr_def)
                      apply(subgoal_tac "lib_writes_on cls' Top =lib_writes_on cls Top", simp)
                        apply(subgoal_tac "lib_value cls' = lib_value cls", simp)
                      defer
                      using rd_A_preserves_values apply auto[1]                                    
                      using rd_A_preserves_writes_on apply auto[1]
                        apply(simp add:  cobs_to_def)    
                         defer
                      defer
                          defer
                           defer
                      
                      apply (metis PC.distinct(19) PC.distinct(27) fun_upd_apply)
                         apply (simp add: read_value_in_written)
                         defer defer defer
                         apply(subgoal_tac "u \<in> written_vals cls (Suc (n_val ps t))")
                      
                          apply blast
                      apply (simp add: rd_A_preserves_values rd_A_preserves_writes_on written_vals_def)
                      apply(intro allI impI, elim conjE exE disjE)
                       apply(subgoal_tac "written_addr cls' = written_addr cls")
                  apply(subgoal_tac "agt ad1 ad2 ps' cls' = agt ad1 ad2 ps cls")
                         apply (metis lib_c_obs_lib_only_pres_read_var)
                        apply (simp add: no_Top_n_def)
                        apply (simp add: agt_pushed_same2rd_before_state)
                      apply(simp add: written_addr_def)
                      using rd_A_preserves_values rd_A_preserves_writes_on apply auto[1]
                 apply(subgoal_tac "written_addr cls' = written_addr cls")
                      apply (metis lib_c_obs_lib_only_pres_read_var)
                      apply(simp add: written_addr_def)
                      using rd_A_preserves_values rd_A_preserves_writes_on apply auto[1]
                      apply(simp add: dobs_to_def cobs_to_def)
                      apply(intro allI impI, elim conjE exE disjE)
                       apply(subgoal_tac "written_addr cls' = written_addr cls")
                        apply(subgoal_tac "agt (prog_state.top ps' t) ad ps' cls' = agt (prog_state.top ps' t) ad ps cls")
                         apply(subgoal_tac "top ps' t\<in>written_addr cls")
                          apply(simp add: globals to_p2_def to_p3_def to_p4_def)
                      apply (metis a_not_in_pushed_clss agt_def lib_read_transfer)
                      apply(simp add: globals written_addr_def)
                      apply (simp add: read_value_in_written)
                        apply simp
                        apply (simp add: agt_pushed_same2rd_before_state)
                      apply(simp add: globals written_addr_def)
                      using rd_A_preserves_values rd_A_preserves_writes_on apply auto[1]

                       apply(subgoal_tac "written_addr cls' = written_addr cls")
                        apply(subgoal_tac "agt (prog_state.top ps' t) ad ps' cls' = agt (prog_state.top ps' t) ad ps cls")
                      apply(subgoal_tac "top ps' t\<in>written_addr cls")
                          apply (metis lib_read_transfer)
                      apply(simp add: globals written_addr_def)
                      apply (simp add: read_value_in_written)
                        apply simp
                      apply(simp add: globals written_addr_def)
                       apply (meson agt_pushed_same2rd agt_pushed_same2rd_before_state)
                      apply(simp add: globals written_addr_def)
                      using rd_A_preserves_values rd_A_preserves_writes_on apply auto[1]                    
                      by (metis rd_A_preserves_values rd_A_preserves_writes_on written_addr_def)
                    next
      case L6
      then show ?thesis
        using assms
          apply(cases "pc ps t"; simp; elim exE conjE; simp)
        apply(simp add: globals)    
        apply(intro conjI)
        apply (metis d_obs_post_CAS_R_diff_var_post)
        apply (metis d_obs_CAS_R_diff_var)
         using cvd_CAS_R_cvd apply auto[1]
          apply auto[1]
         apply(case_tac "\<not>res ps' t", simp_all)
         apply(subgoal_tac "written_addr cls' = written_addr cls \<union> {n_val ps t}") defer
         apply(subgoal_tac "n_val ps t \<noteq> Null")
         using success_CAS_Top_written_addr_post2
           apply simp
        apply force
         apply(simp add: cobs_to_def dobs_to_def)
         apply(intro impI allI, elim conjE exE disjE)
          apply simp
         apply (metis cvd_CAS_R_success_read_val lib_d_obs_same_t_c_obs)
               apply (metis cvd_CAS_R_success_read_val lib_d_obs_same_t_c_obs)


              apply(subgoal_tac "\<exists>vl. [libad2 =\<^sub>t vl] cls")
              apply(subgoal_tac "\<exists>vl. [libSuc(ad2) =\<^sub>t vl] cls")
         apply(elim exE, intro conjI)
               apply(rule_tac x=vl in exI)
         apply (metis cvd_CAS_R_success_read_val lib_d_obs_same_t_c_obs subsetD)
                apply(rule_tac x=vla in exI)
                apply (metis cvd_CAS_R_success_read_val lib_d_obs_same_t_c_obs subsetD)    
               apply(case_tac "ad2 = top ps t")
               apply (metis (full_types) insert_subset neq0_conv subsetI subset_antisym)
         apply(case_tac "top ps t \<noteq> Null")
              apply(subgoal_tac "agt (top ps t) ad2 ps cls \<and> top ps t \<in> written_addr cls" )
                apply (metis in_mono neq0_conv)
         apply (metis Null_def TopLV_agt_others assms(5) assms(6) assms(7) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write neq0_conv)
              apply(simp add: globals)
              apply(subgoal_tac " top ps t = lastTop cls")
         apply(subgoal_tac "pushed_addr ps = {}")
                apply auto[1]
         apply (metis Null_def TopLV_Null_pushed_empty assms(5) assms(6) assms(7))
               apply (metis cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write)
         apply (metis (no_types, lifting) Null_def TopLV_Null_pushed_empty assms(5) assms(6) assms(7) cvd_CAS_R_success_read_val empty_iff lastTop_def lib_cvd_exist_last_write neq0_conv to_p2_def)
             apply blast

(**)
         apply(subgoal_tac "\<not>agt ad1 ad2 ps' cls'")
          apply blast      
         apply(case_tac "lastTop cls = Null")

         apply(subgoal_tac "pushed_addr ps = {}")
           apply simp
         using TopLV_Null_pushed_empty
          apply (metis Null_def assms(5) assms(6) assms(7) lastTop_def)
         apply(subgoal_tac "n_val ps t \<notin> Domain (nxt_rel ps cls) \<union> Range (nxt_rel ps cls)")
          defer
          apply (metis Null_def Un_iff assms(5) not_dom not_range)
         apply(subgoal_tac "n_val ps t \<notin> Range (nxt_rel ps' cls')")
         defer
          apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t, top ps t)}")
         using UnE apply auto[1]
         apply(simp add: nxt_rel_def)
      
           apply(subgoal_tac "(\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls) \<and> (\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls)") 
            apply(elim exE conjE, intro conjI)
            apply(rule_tac x="vl" in exI)
            apply(subgoal_tac "ad1 \<noteq> n_val ps t")
         using successful_CAS_lib_c_obs_lib_diff_value_press
         apply (metis subsetD)
         apply(simp add: no_Top_n_def)
              apply blast

            apply(rule_tac x="vla" in exI)
             apply(subgoal_tac "ad1 \<noteq> n_val ps t")
              apply (metis successful_CAS_lib_c_obs_lib_diff_value_press)
         apply blast


            apply(subgoal_tac "agt ad1 ad2 ps' cls' = agt ad1 ad2 ps cls")
         apply blast
          defer
          apply (metis subset_eq successful_CAS_lib_c_obs_lib_diff_value_press)
         apply(subgoal_tac "\<exists>vl. [libad1 =\<^sub>t vl] cls")
          defer
         apply(case_tac "ad1 = top ps t")
           apply (metis (full_types) bot.extremum_strict bot_nat_def in_mono neqE)
          apply(subgoal_tac "agt (top ps t) ad1 ps cls \<and> top ps t \<noteq> Null")
             apply fastforce
            apply (metis cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write to_p2_def)
         apply blast
         apply(subgoal_tac "lastNxtVal cls (n_val ps t) = lastNxtVal cls' (n_val ps' t)") defer
           apply simp
         apply (metis succ_CAS_preserves_last)         

           apply simp
      
         apply(subgoal_tac "\<not>agt ad1 ad2 ps' cls'")
           apply blast      

         apply(case_tac "lastTop cls = Null")
         apply(subgoal_tac "pushed_addr ps = {}")
           apply simp
         using TopLV_Null_pushed_empty
           apply (metis Null_def assms(5) assms(6) assms(7) lastTop_def)
                  apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t, top ps t)}")
  apply(subgoal_tac "n_val ps t \<notin> Domain (nxt_rel ps cls) \<union> Range (nxt_rel ps cls)")
         apply(subgoal_tac "n_val ps t \<notin> Range (nxt_rel ps' cls')")
             apply(simp add: agt_def clss_def)
             apply (metis Range.intros Range_insert insert_iff trancl_range)
         apply simp
                         apply auto[1]
         
         apply blast
         apply (metis Un_empty_right Un_insert_right assms(5) assms(6) assms(7) nxt_rel_after_successful_CAS)
         apply simp
         apply(subgoal_tac "glb_inv ps cls \<and>
    to ps cls \<and>
    glb ps cls")defer 
         using assms(5) assms(6) assms(7) apply blast
         apply(subgoal_tac "n_val ps t \<noteq> Top \<and>
               Suc (n_val ps t) \<noteq> Top")
          defer
          apply metis
         apply(subgoal_tac "\<not> agt ad1 (n_val ps t) ps' cls'")
         using  agt_pushed_successful_cas_before
          apply (metis Un_commute assms(5) insert_is_Un)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t")
          apply (metis no_nxt_no_agt)
         by (metis gr0I insert_iff succ_CAS_preserves_last)
  qed






lemma push_globals_total_order:
  assumes "wfs ccs"
      and "lib_wfs cls ccs"
      and "lib_push t v ps cls ccs ps' cls' ccs'"
      and "push_inv t v (pc ps t) cls ccs  ps"
      and "glb_inv ps cls"
      and "glb ps cls"
      and "to ps cls"
    shows "to ps' cls'"
  apply(simp add: to_def)
proof(intro conjI)
  show "to_p1 ps' cls'"
  proof (cases "pc ps t")
    case L1
    then show ?thesis
      using assms
      apply(simp add: globals)
      by (metis agt_pushed_same2 assms(3) lib_push_L1_pushed)
  next
    case L2
    then show ?thesis 
      using assms
      apply (simp add: to_simps)
      by (metis (full_types) agt_pushed_same2wr same_except_for_pc_and_top_def)
  next
    case L3
    then show ?thesis
       using assms
       apply(simp add: globals)
       by (metis agt_pushed_same2rd)
  next
    case L4
    then show ?thesis 
     using assms
     apply (simp add: to_simps no_Top_n_def, elim exE conjE )
     apply(subgoal_tac "n_nxt ps' t \<notin> pushed_addr ps")
      defer
      apply simp
     apply(intro allI impI, elim conjE)
     using agt_pushed_same2wr_nxt[where a="n_val ps t" and ccs=ccs 
          and cls=cls and cls'=cls' and ccs'=ccs' and ps=ps and ps'=ps' and t=t and v="prog_state.top ps t"] 
     by (metis One_nat_def add.right_neutral add_Suc_right  assms(5) old.nat.inject same_except_for_pc_and_top_def)
    next
    case L5
    then show ?thesis
      using assms
      apply(simp add: globals to_p2_def to_p3_def to_p4_def)
      apply(case_tac "\<not>res ps' t", simp_all)  
      apply(intro allI conjI impI)
      apply (metis (no_types, lifting) agt_def clss_same failed_cas_preserves_clss)
           apply(intro allI conjI impI, elim conjE disjE exE)
         apply linarith
      apply safe     
                 apply (metis (full_types) a_not_in_pushed_clss agt_def)
      apply (metis cvd_CAS_R_success_read_val in_mono lib_cvd_exist_last_write)
      apply (metis cvd_CAS_R_success_read_val in_mono lib_cvd_exist_last_write)
      defer  
              apply (metis (full_types) a_not_in_pushed_clss agt_def)
      apply (metis cvd_CAS_R_success_read_val in_mono lib_cvd_exist_last_write)
      apply (metis cvd_CAS_R_success_read_val in_mono lib_cvd_exist_last_write)
      defer
         apply (metis (full_types) a_not_in_pushed_clss agt_def)
      apply (metis cvd_CAS_R_success_read_val in_mono lib_cvd_exist_last_write)
      apply (metis cvd_CAS_R_success_read_val in_mono lib_cvd_exist_last_write)                   
     apply(subgoal_tac "n_val ps t \<notin> pushed_addr ps") 
         apply(simp add: agt_def clss_def)
        apply(subgoal_tac "nxt_rel ps cls \<subseteq> nxt_rel ps' cls'")
      apply(case_tac "a = b")
           apply blast
      apply(subgoal_tac "(a, b) \<in> (nxt_rel ps cls)\<^sup>+ \<or> (b, a) \<in> (nxt_rel ps cls)\<^sup>+")
      apply (meson trancl_mono)
           apply blast
          apply(simp add: nxt_rel_def) apply safe
          apply (metis succ_CAS_preserves_last)

    apply(simp add:  agt_def clss_def)
    apply(case_tac "top ps t \<noteq> b")
           apply(subgoal_tac "agt (top ps t) b ps' cls'")
         apply(subgoal_tac "(n_val ps t, top ps t)\<in>nxt_rel ps' cls'")
        apply(simp add: agt_def clss_def)
      apply(simp add: nxt_rel_def)
       apply (metis succ_CAS_preserves_last)
       apply(simp add: agt_def clss_def)
        apply(subgoal_tac "(prog_state.top ps t, b) \<in> (nxt_rel ps cls)\<^sup>+")
      apply(simp add: nxt_rel_def ) 
      apply(subgoal_tac "{(a, lib_value cls'
                    (lib_lastWr cls' (Suc a))) |
               a. a = n_val ps t \<or>
                  a \<in> pushed_addr ps} = {(a, lib_value cls
                    (lib_lastWr cls (Suc a))) | a.  a \<in> pushed_addr ps} \<union> {(n_val ps t, lib_value cls' (lib_lastWr cls' (Suc (n_val ps t))))}")
              apply (metis (no_types, lifting) Un_upper1 trancl_mono)
      apply(subgoal_tac "{(a, lib_value cls'
                 (lib_lastWr cls' (Suc a))) |
            a. a \<in> pushed_addr ps} = {(a, lib_value cls
                 (lib_lastWr cls (Suc a))) |
            a. a \<in> pushed_addr ps}", simp)
          apply (simp add: or_union_eq')
      apply safe[1]
          apply (metis succ_CAS_preserves_last)    
      apply (metis succ_CAS_preserves_last)
      apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
       apply(simp add: no_Top_n_def lib_d_obs_t_def lib_d_obs_def written_addr_def)
       apply safe[1]
      apply(simp add: nxt_rel_def)
       apply(subgoal_tac "lib_value cls'
                  (lib_lastWr cls' (Suc (n_val ps t))) = top ps t")
      apply (smt mem_Collect_eq r_into_trancl')
        apply (metis succ_CAS_preserves_last)

       apply simp
      apply(case_tac "a = top ps t", simp)
       apply(subgoal_tac "(n_val ps t, top ps t)\<in>nxt_rel ps' cls'")
      apply (simp add: agt_def clss_def)
       apply auto[1]
      apply(simp add: nxt_rel_def)
       apply (metis succ_CAS_preserves_last)
      apply(subgoal_tac "agt (top ps t) a ps cls") defer
       apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
      apply(subgoal_tac "agt (n_val ps t) (top ps t) ps' cls'")
      apply(subgoal_tac "agt (n_val ps t) a ps' cls'")
        apply blast
      apply(subgoal_tac "agt (top ps t) a ps' cls'")
      apply (meson agt_order)
       apply (simp add: agt_def clss_def no_Top_n_def nxt_rel_def)
      apply(subgoal_tac "{(a, lib_value cls'
                    (lib_lastWr cls' (Suc a))) |
               a. a = n_val ps t \<or>
                  a \<in> pushed_addr ps} = {(a, lib_value cls
                    (lib_lastWr cls (Suc a))) | a.  a \<in> pushed_addr ps} \<union> {(n_val ps t, lib_value cls' (lib_lastWr cls' (Suc (n_val ps t))))}")
      apply (metis (no_types, lifting) Un_upper1 trancl_mono)
      apply(subgoal_tac "{(a, lib_value cls'
                 (lib_lastWr cls' (Suc a))) |
            a. a \<in> pushed_addr ps} = {(a, lib_value cls
                 (lib_lastWr cls (Suc a))) |
            a. a \<in> pushed_addr ps}", simp)
          apply (simp add: or_union_eq')
      apply safe[1]
        apply (metis succ_CAS_preserves_last)    
      apply (metis succ_CAS_preserves_last)
       apply (simp add: agt_def clss_def no_Top_n_def nxt_rel_def)
      apply(subgoal_tac "{(a, lib_value cls'
                    (lib_lastWr cls' (Suc a))) |
               a. a = n_val ps t \<or>
                  a \<in> pushed_addr ps} = {(a, lib_value cls
                    (lib_lastWr cls (Suc a))) | a.  a \<in> pushed_addr ps} \<union> {(n_val ps t, lib_value cls' (lib_lastWr cls' (Suc (n_val ps t))))}")
       apply (metis (no_types, lifting) Un_insert_right insert_iff r_into_trancl' succ_CAS_preserves_last)
      apply(subgoal_tac "{(a, lib_value cls'
                 (lib_lastWr cls' (Suc a))) |
            a. a \<in> pushed_addr ps} = {(a, lib_value cls
                 (lib_lastWr cls (Suc a))) |
            a. a \<in> pushed_addr ps}", simp)
          apply (simp add: or_union_eq')
      apply safe[1]
        apply (metis succ_CAS_preserves_last)    
      by (metis succ_CAS_preserves_last)
  next
    case L6
    then show ?thesis
      using assms
      by(simp add: globals)    
  qed
next  show "to_p2 ps' cls'"
  proof (cases "pc ps t")
    case L5
    then show ?thesis
      using assms
       apply(simp add: globals to_p2_def to_p3_def to_p4_def)
  apply(case_tac "\<not>res ps' t", simp_all)
   apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = lib_value cls (lib_lastWr cls Top)")
  apply(intro allI impI, simp add: agt_def)
      apply (metis failed_cas_preserves_clss)
       apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
      apply(case_tac "lib_value cls (a, b) = prog_state.top ps t", simp_all)
       apply(simp add: tst_def var_def lib_read_def all_updates_l lib_value_def lib_writes_on_def lib_lastWr_def)
        apply(subgoal_tac "[lib(Top) =\<^sub>t (n_val ps t)] cls'")
       defer
      using cvd_CAS_R_success_d_obs_post apply auto[1]
  apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = n_val ps t", simp)
   defer
   apply(simp add: lib_d_obs_t_def lib_d_obs_def)
  apply(intro allI impI, elim conjE disjE)
   apply blast
      apply(subgoal_tac "\<forall> a . a\<in>pushed_addr ps \<and> a \<noteq> top ps t \<longrightarrow> agt (top ps t) a ps cls")
   defer
       apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
  apply(subgoal_tac "lastNxtVal cls (n_val ps t) = top ps t") defer
   apply simp
      apply(simp add: agt_def clss_def)
      apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t, lib_value cls (lib_lastWr cls (Suc (n_val ps t))))}")
       defer
       apply(simp add: nxt_rel_def)
      defer
      apply (metis Un_upper1 Un_upper2 r_into_trancl' singletonI trancl_mono trancl_trans)    
      apply(subgoal_tac "\<forall> a . a\<in>pushed_addr ps \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc a)) = lib_value cls (lib_lastWr cls (Suc a))")
       defer
       apply(intro allI impI conjI)
       apply(subgoal_tac "Suc aa \<noteq> Top")
      apply(subgoal_tac "lib_lastWr cls' (Suc aa) = lib_lastWr cls (Suc aa)") defer
      using last_CAS_R_diff_var
                apply meson
                apply metis defer
       apply(simp add: lib_CAS_Rel_step_def,elim exE conjE)
       apply(case_tac "lib_value cls (ab, b) = prog_state.top ps t", simp_all)
  apply(simp add: lib_update_r_def all_updates_l lib_value_def)
       apply (metis a_is_x lib_last_in_visible_writes)
      apply(subgoal_tac "finite (pushed_addr ps)") defer
      apply blast
      apply(subgoal_tac "{(a, lib_value cls' (lib_lastWr cls' (Suc a))) |a.
          a = n_val ps t \<or> a \<in> pushed_addr ps} = insert (n_val ps t, lib_value cls' (lib_lastWr cls' (Suc (n_val ps t))))
          {(a, lib_value cls' (lib_lastWr cls' (Suc a))) | a.
           a \<in> pushed_addr ps}", simp) defer
       apply blast
      apply(subgoal_tac "(n_val ps t,
           lib_value cls'
            (lib_lastWr cls' (Suc (n_val ps t)))) = (n_val ps t,
           lib_value cls
            (lib_lastWr cls (Suc (n_val ps t))))")
      apply(subgoal_tac " {(a, lib_value cls' (lib_lastWr cls' (Suc a))) |a.
           a \<in> pushed_addr ps} =  {(a, lib_value cls (lib_lastWr cls (Suc a))) |a.
           a \<in> pushed_addr ps}", simp)
       apply (metis (no_types, hide_lams))
      apply safe
         apply (metis (no_types, lifting) trancl_trans)   
      apply (metis succ_CAS_preserves_last)
       apply (metis succ_CAS_preserves_last)
     by (metis succ_CAS_preserves_last)
  next
    case L1
    then show ?thesis
      using assms
  apply(simp add: globals to_p2_def to_p3_def to_p4_def)
        apply(intro allI impI)
      apply (metis agt_pushed_same2 assms(3) lib_push_L1_pushed )
    done
  next
    case L2
    then show ?thesis
      using assms
       apply(simp add: globals to_p2_def to_p3_def to_p4_def)
      apply(intro allI impI)
     apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = lib_value cls (lib_lastWr cls Top)")  
      using agt_pushed_same2wr      
      apply (metis assms(5) same_except_for_pc_and_top_def)      
     apply(simp add: lib_write_step_def lib_write_def all_updates_l , elim exE conjE)
     apply clarsimp
      apply(simp add: lib_value_def lib_lastWr_def lib_writes_on_def var_def tst_def) 
      apply (smt Collect_cong a_is_x fst_conv)
      done

  next
    case L3
    then show ?thesis
      using assms
             apply(simp add: globals to_p2_def to_p3_def to_p4_def)
        apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = lib_value cls (lib_lastWr cls Top)")
     apply (metis agt_pushed_same2rd) 
     apply(simp add: lib_read_step_def lib_read_def all_updates_l , elim exE conjE)
     apply clarsimp
    apply(simp add: lib_value_def lib_lastWr_def lib_writes_on_def var_def tst_def)  
      done
  next
    case L4
    then show ?thesis
      using assms
       apply(simp add: globals to_p2_def to_p3_def to_p4_def)
        apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = lib_value cls (lib_lastWr cls Top)")
       apply (subgoal_tac "n_nxt ps' t \<notin> pushed_addr ps", simp)
      using agt_pushed_same2wr_nxt[where a="n_val ps t" and ccs=ccs 
          and cls=cls and cls'=cls' and ccs'=ccs' and ps=ps and ps'=ps' and t=t and v="prog_state.top ps t"] 
      apply (metis Suc_eq_plus1 assms(5) same_except_for_pc_and_top_def)
   
      apply(case_tac "\<not>res ps' t")
    apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = lib_value cls (lib_lastWr cls Top)")
    apply metis
       apply blast  
         apply auto[1]
     apply(simp add:lib_write_step_def lib_write_def all_updates_l, elim exE conjE)  
     apply clarsimp
    apply(simp add: lib_lastWr_def lib_writes_on_def lib_value_def var_def tst_def)
    apply (smt Collect_cong a_is_x fst_conv)
      done

  next
    case L6
    then show ?thesis
      using assms
      apply simp
      done
  qed 
next  show "to_p3 ps' cls'"
  proof (cases "pc ps t")
    case L1
    then show ?thesis
      using assms
      apply(simp add: globals to_p2_def to_p3_def to_p4_def)         
      by (metis agt_pushed_same2 assms(3) lib_push_L1_pushed)
  next
    case L2
    then show ?thesis
    using assms
    apply(simp add: to_simps)
    by (meson agt_pushed_same2wr same_except_for_pc_and_top_def)

  next
    case L3
    then show ?thesis
    using assms
    apply(simp add: globals to_p2_def to_p3_def to_p4_def)                     
    by (meson agt_pushed_same2rd)
  next
    case L4
    then show ?thesis
    using assms
    apply(simp add: to_simps)
      using agt_pushed_same2wr_nxt[where a="n_val ps t" and ccs=ccs 
          and cls=cls and cls'=cls' and ccs'=ccs' and ps=ps and ps'=ps' and t=t and v="prog_state.top ps t"] 
      by (metis Suc_eq_plus1 assms(5) same_except_for_pc_and_top_def)
next
  case L5
    then show ?thesis
    using assms
    apply(simp add: globals to_p2_def to_p3_def to_p4_def)
    apply(case_tac "\<not>res ps' t", simp_all)   
    apply (metis (no_types) agt_def failed_cas_preserves_clss)
    apply(intro allI impI)
        apply(simp add: no_Top_n_def)
   apply safe
   apply(case_tac "a \<in> pushed_addr ps")
     apply(subgoal_tac "agt a 0 ps cls")
        apply (metis (full_types) a_not_in_pushed_clss agt_def)
        apply blast
       apply(simp add: agt_def clss_def nxt_rel_def)
       apply(subgoal_tac "pushed_addr ps = {}", simp)
          
    apply (metis singletonI succ_CAS_preserves_last trancl.r_into_trancl)
       apply (metis Null_def TopLV_Null_pushed_empty assms(5) assms(6) assms(7) lastTop_def)    
      apply (metis (full_types) a_not_in_pushed_clss agt_def)
     
    apply (metis cvd_CAS_R_success_read_val in_mono lib_cvd_exist_last_write)
    apply (metis cvd_CAS_R_success_read_val in_mono lib_cvd_exist_last_write)
    apply (metis cvd_CAS_R_success_read_val in_mono lib_cvd_exist_last_write)
    apply (metis cvd_CAS_R_success_read_val in_mono lib_cvd_exist_last_write)
    apply(subgoal_tac "agt (top ps t) 0 ps' cls'")
     apply(subgoal_tac "agt (n_val ps t) (top ps t) ps' cls'")
    apply (meson agt_order)
      apply(simp add: written_addr_def agt_def clss_def no_Top_n_def  nxt_rel_def)
        apply(subgoal_tac "{(a, lib_value cls'
                    (lib_lastWr cls' (Suc a))) |
               a. a = n_val ps t \<or>
                  a \<in> pushed_addr ps} = {(a, lib_value cls
                    (lib_lastWr cls (Suc a))) | a.  a \<in> pushed_addr ps} \<union> {(n_val ps t, lib_value cls' (lib_lastWr cls' (Suc (n_val ps t))))}")
       apply (metis (no_types, lifting) Un_insert_right insert_iff r_into_trancl' succ_CAS_preserves_last)
      apply(subgoal_tac "{(a, lib_value cls'
                 (lib_lastWr cls' (Suc a))) |
            a. a \<in> pushed_addr ps} = {(a, lib_value cls
                 (lib_lastWr cls (Suc a))) |
            a. a \<in> pushed_addr ps}", simp)
          apply (simp add: or_union_eq')
      apply safe[1]
        apply (metis succ_CAS_preserves_last)    
        apply (metis )  
    
    apply (metis succ_CAS_preserves_last)
        apply simp
       
    apply(subgoal_tac "agt (prog_state.top ps t) 0 ps cls")
      apply(simp add: written_addr_def agt_def clss_def no_Top_n_def )
      apply(subgoal_tac "nxt_rel ps cls \<subseteq> nxt_rel ps' cls'")

       apply (meson trancl_mono)
          apply(simp add: nxt_rel_def) apply safe
       apply (metis succ_CAS_preserves_last)    
    apply simp
     apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
    apply(subgoal_tac " agt a 0 ps cls") defer    
    apply blast
          apply(simp add: agt_def clss_def nxt_rel_def) 
         apply(subgoal_tac "{(a, lib_value cls'
                    (lib_lastWr cls' (Suc a))) |
               a. a = n_val ps t \<or>
                  a \<in> pushed_addr ps} = {(a, lib_value cls
                    (lib_lastWr cls (Suc a))) | a.  a \<in> pushed_addr ps} \<union> {(n_val ps t, lib_value cls' (lib_lastWr cls' (Suc (n_val ps t))))}")    
    apply (metis (no_types, lifting) Un_upper1 trancl_mono)
      apply(subgoal_tac "{(a, lib_value cls'
                 (lib_lastWr cls' (Suc a))) |
            a. a \<in> pushed_addr ps} = {(a, lib_value cls
                 (lib_lastWr cls (Suc a))) |
            a. a \<in> pushed_addr ps}", simp)
          apply (simp add: or_union_eq')
      apply safe[1]
        apply (metis succ_CAS_preserves_last)    
      by (metis succ_CAS_preserves_last)     
  next
    case L6
    then show ?thesis
    using assms
    by simp                                           
  qed 
next  show "to_p4 ps' cls'"
  proof (cases "pc ps t")
    case L1
      then show ?thesis 
        using assms
        apply(simp add: globals to_p3_def to_p4_def)
        by (metis agt_def agt_pushed_same2 assms(3) lib_push_L1_pushed)
    next
      case L2
      then show ?thesis
      using assms
      apply(simp add: globals to_p3_def to_p4_def clss_def nxt_rel_def)
      apply(intro allI impI)
      apply(subgoal_tac "{(a, lib_value cls' (lib_lastWr cls' (Suc a))) |a.
           a \<in> pushed_addr ps} = {(a, lib_value cls (lib_lastWr cls (Suc a))) |a.
           a \<in> pushed_addr ps}")
       apply simp
      apply safe
      apply (metis Null_def TopLV_Null_pushed_empty assms(5) assms(6) assms(7) ex_in_conv lastTop_def)
                apply (metis write_diff_var_last_val)        
      apply (metis Null_def TopLV_Null_pushed_empty assms(5) assms(6) assms(7) ex_in_conv lastTop_def)
      by (metis wr_preserves_last)
    next
      case L3
      then show ?thesis
        using assms
        apply(simp add: globals  to_p2_def to_p3_def to_p4_def)
        apply(intro conjI allI impI, elim conjE exE)
        apply(simp add: clss_def nxt_rel_def no_Top_n_def)
        apply(subgoal_tac "{(a, lib_value cls'
                    (lib_lastWr cls' (Suc a))) |
               a. a \<in> pushed_addr ps} = {(a, lib_value cls
                    (lib_lastWr cls (Suc a))) |
               a. a \<in> pushed_addr ps}")
         apply simp
            using rd_A_preserves_last by auto
    next
      case L4
      then show ?thesis
        using assms
         apply(simp add: globals  to_p2_def to_p3_def to_p4_def)
        apply(intro conjI allI impI, elim conjE exE)
        apply(simp add: clss_def nxt_rel_def no_Top_n_def)
        apply(subgoal_tac "{(a, lib_value cls'
                (lib_lastWr cls' (Suc a))) |
           a. a \<in> pushed_addr ps} = {(a, lib_value cls
                (lib_lastWr cls (Suc a))) |
           a. a \<in> pushed_addr ps}")
         apply auto[1]
        apply safe
        apply (metis Suc_inject write_diff_var_last_val)
        apply (metis old.nat.inject write_diff_var_last_val)        
        apply (metis Suc_inject write_diff_var_last_val)        
        apply (metis Suc_inject write_diff_var_last_val)    
        apply (metis Suc_inject wr_preserves_last)
        apply (metis Suc_inject wr_preserves_last)       
        apply (metis Suc_inject wr_preserves_last)      
        by (metis Suc_inject wr_preserves_last)
    next
      case L5
      then show ?thesis
        using assms
        apply(simp add: globals  to_p2_def to_p3_def to_p4_def)
        apply(intro conjI allI impI, elim conjE exE)
        apply(case_tac "\<not>res ps' t", simp_all)
         apply (simp add: failed_cas_preserves_clss)
              apply(subgoal_tac "(a, a) \<notin> clss ps cls")
         defer      
        apply (meson a_not_in_pushed_clss)
         apply(elim disjE)
        defer
         apply(simp add: clss_def  no_Top_n_def written_addr_def)
        apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t, lib_value cls
            (lib_lastWr cls (Suc (n_val ps t))))}", simp)
          apply(subgoal_tac "n_val ps t \<noteq> a")
        using transcl_fresh[where f = "nxt_rel ps cls" and a = "n_val ps t" and a' = "top ps t"
            and g= "insert (n_val ps t, prog_state.top ps t)
                (nxt_rel ps cls)"]
        apply simp
        apply (metis Domain.simps Null_def assms(5) assms(6) assms(7) clss_def domain_clss not_dom not_range)
          apply blast
         apply(simp add: nxt_rel_def)
        apply safe[1]
                            apply (metis succ_CAS_preserves_last)   
        apply simp_all
        apply (metis succ_CAS_preserves_last)        
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
                   apply (metis succ_CAS_preserves_last)
        
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply(simp add: clss_def no_Top_n_def)
        apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls \<union> {(n_val ps t, lib_value cls
            (lib_lastWr cls (Suc (n_val ps t))))}", simp)
        using transcl_fresh_new[where f = "nxt_rel ps cls" and a = "n_val ps t" and a' = "top ps t"
              and g= "insert (n_val ps t, prog_state.top ps t) (nxt_rel ps cls)"]
              apply simp       
         apply (metis a_not_in_pushed_nxt_rel assms(5) assms(6) converse_tranclE glb_def not_dom not_range)
         apply(simp add: nxt_rel_def)
        apply safe[1]
        apply (metis succ_CAS_preserves_last)         
        apply (metis succ_CAS_preserves_last)        
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
          apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
        apply (metis succ_CAS_preserves_last)
       by (metis succ_CAS_preserves_last)
    next
      case L6
      then show ?thesis
      using assms
      by simp
    qed
  qed

lemma push_gloabals_inv:
  assumes "wfs ccs"
      and "lib_wfs cls ccs"
      and "lib_push t v ps cls ccs ps' cls' ccs'"
      and "push_inv t v (pc ps t) cls ccs  ps"
      and "glb_inv ps cls"
    shows "glb_inv ps' cls'"
  apply(simp add: glb_inv_def)
proof (intro conjI) 
  show "glb_inv1 ps' cls'"
  using assms
  apply(simp add: glb_inv_def)
  apply(elim conjE)
           apply(case_tac "pc ps t"; simp; elim exE conjE)
      apply(simp add: globals)
  apply (meson assms(3) in_mono lib_push_L1_addr_sub)
              apply(simp add: globals)
              apply(subgoal_tac "(n_val ps t) \<noteq> Top")
               apply(subgoal_tac "lib_writes_on cls' Top = lib_writes_on cls Top")
  apply(intro allI impI conjI)
                apply(subgoal_tac "lib_value cls' (a, b) = lib_value cls (a, b)")
                 apply simp
                apply simp
  apply(simp add: var_def tst_def lib_writes_on_def lib_visible_writes_def lib_write_step_def lib_write_def all_updates_l lib_value_def, elim exE conjE)
  apply(subgoal_tac "lib_mods cls' (Top, b) = lib_mods cls (Top, b)")
                 apply simp
  apply simp
  apply(simp add: var_def tst_def lib_writes_on_def lib_visible_writes_def lib_write_step_def lib_write_def all_updates_l lib_value_def, elim exE conjE)
               apply simp
  apply auto[1]
  apply auto[1]
  apply(simp add: globals)
  apply (metis assms(1) assms(2) read_pres_value read_pres_writes_on_diff_var )
   apply(simp add: globals)
           apply(intro allI impI conjI)
           apply(case_tac " (a, b) \<in> lib_writes_on cls Top")
  apply(subgoal_tac "lib_value cls' (a,b) = lib_value cls (a,b)")
     apply auto[1]
  apply(simp add: var_def tst_def lib_writes_on_def lib_visible_writes_def lib_write_step_def lib_write_def all_updates_l lib_value_def, elim exE conjE)
    apply clarsimp
  apply metis
      apply(simp add: var_def tst_def lib_writes_on_def lib_visible_writes_def lib_write_step_def lib_write_def all_updates_l lib_value_def, elim exE conjE)
   apply clarsimp
  apply metis
   apply(simp add: globals)
  apply(intro allI impI conjI)
             apply(simp add: lib_CAS_Rel_step_def lib_update_r_def all_updates_l, elim exE conjE)
  apply(case_tac "lib_value cls (aa, ba) = prog_state.top ps t", simp_all)
             apply(simp add: lib_CAS_Rel_step_def lib_update_r_def all_updates_l, elim exE conjE) 
  apply(simp add: lib_writes_on_def lib_value_def)
   apply force
             apply (simp add:  lib_read_def all_updates_l lib_syncing_def)
  apply(simp add: lib_writes_on_def lib_value_def)
  by blast
next 
next show "glb_inv3 ps' cls'" 
  using assms
  apply(simp add: glb_inv_def)
  apply(elim conjE)
  apply(case_tac "pc ps t", simp_all add: globals; elim exE conjE)
  apply (metis assms(3) lib_push_L1_pushed)
  apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = lib_value cls (lib_lastWr cls Top)")
            apply auto[1]
           apply(subgoal_tac "lib_lastWr cls' Top = lib_lastWr cls Top", simp)
            apply(simp add:glb_inv10_def lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
            apply clarsimp
  apply(simp add: lib_value_def)
  apply (metis a_is_x assms(1) assms(2) lib_last_in_visible_writes)
             apply(simp add:glb_inv10_def lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
           apply clarsimp
  apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def)
           apply (metis (mono_tags, hide_lams) a_is_x fst_conv)
          apply(intro impI)
  apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = lib_value cls (lib_lastWr cls Top)")
  apply simp
          apply(simp add: lib_read_step_def lib_read_def all_updates_l, elim exE conjE)
          apply(case_tac "lib_syncing cls (a, b) True", simp_all)
           apply(simp add: lib_value_def lib_lastWr_def lib_writes_on_def var_def tst_def)
          apply(simp add: lib_value_def lib_lastWr_def lib_writes_on_def var_def tst_def)
         apply(intro impI)
   apply(case_tac "res ps' t", simp_all)
  apply(subgoal_tac " (lib_lastWr cls' Top) = (lib_lastWr cls Top)")
     apply(simp add: lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
  apply clarsimp
  apply(simp add: lib_lastWr_def lib_value_def lib_writes_on_def var_def tst_def)  
     apply (intro conjI impI)
  apply (metis a_is_x)
  apply fastforce
     apply(simp add: lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
   apply(simp add: lib_lastWr_def lib_value_def lib_writes_on_def var_def tst_def)  
    apply (metis  a_is_x fst_conv)
  apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = lib_value cls (lib_lastWr cls Top)")
   apply simp
      apply(simp add: lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
   apply(simp add: lib_lastWr_def lib_value_def lib_writes_on_def var_def tst_def)  
     apply (intro conjI impI)
  apply (metis a_is_x)
   apply (metis a_is_x fst_eqD)
  apply(case_tac "\<not>res ps' t", simp_all)
  apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = lib_value cls (lib_lastWr cls Top)", simp_all)
  apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
   apply(case_tac "lib_value cls (a, b) = prog_state.top ps t")  
  apply simp
   apply(case_tac "lib_value cls (a, b) = prog_state.top ps t")  
    apply linarith
   apply (simp add: lib_read_def all_updates_l)
  apply(intro conjI impI)
    apply (simp add: lib_syncing_def)
   apply(simp add: lib_lastWr_def lib_writes_on_def lib_value_def)
  apply(subgoal_tac "[lib(Top) =\<^sub>t (n_val ps t)] cls'")
  apply(simp add: lib_d_obs_def lib_d_obs_t_def)
  by (simp add: cvd_CAS_R_success_d_obs_post)
next show "glb_inv4 ps' cls'" 
  using assms
  apply(simp add: glb_inv_def)
  apply(elim conjE)
          apply(case_tac "pc ps t", simp_all add: globals; elim exE conjE)
      apply(case_tac "pc ps t"; simp add: globals)
      apply(intro conjI impI allI)
  apply(case_tac "a \<in> addr_val ps")
      apply metis
       apply(subgoal_tac " a \<noteq> 0")
  apply(subgoal_tac "lib_value cls (lib_lastWr cls (Suc a)) = 0")
         apply linarith
        apply(subgoal_tac "Suc a \<noteq> Top \<and> Suc a \<notin> addr ps")
  apply(simp add: lib_d_obs_t_def lib_d_obs_def)
        apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
  apply(intro conjI)
  apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
        apply(subgoal_tac "a \<notin> addr ps")
         apply(subgoal_tac "(n_val ps' t) = a")
          apply(subgoal_tac "(n_nxt ps' t) = Suc a")
  apply simp
           apply (metis PC.distinct(1) fun_upd_def)
  apply (metis Suc_eq_plus1 new_node_def)
  apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
  apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
  apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
  apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
  apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
  apply(intro conjI impI allI)
  apply(case_tac "n_val ps t = a")
  using write_diff_var_last_val apply auto[1]
  apply(subgoal_tac "Suc a \<notin> addr_val ps")
      apply (metis write_diff_var_last_val)
          apply blast
  using rd_A_preserves_last apply auto[1]
   apply(intro conjI impI allI)
   apply(case_tac "Suc a = n_nxt ps' t")
    apply(subgoal_tac " a = n_val ps t")
  apply(subgoal_tac "n_val ps t \<in> addr ps")
     apply(subgoal_tac "[lib(n_nxt ps' t) =\<^sub>t (top ps t)] cls'")
      apply(case_tac "top ps t = Null")
        apply simp
  apply(subgoal_tac "lib_value cls' (lib_lastWr cls' (Suc (n_val ps t))) = 0")
         apply force
        apply(simp add: lib_d_obs_t_def lib_d_obs_def)
       apply simp
  apply(subgoal_tac "lib_value cls' (lib_lastWr cls' (Suc (n_val ps t))) = top ps t", simp)
        apply(simp add: no_Top_n_def)
  apply(simp add: written_addr_def)
        apply (metis (no_types, hide_lams))
        apply(simp add: lib_d_obs_t_def lib_d_obs_def)
  apply (metis d_obs_write)
  apply blast 
     apply auto[1]
using write_diff_var_last_val apply auto[1]
  by (metis succ_CAS_preserves_last)
next show "glb_inv5 ps' cls'" 
  using assms
  apply(simp add: glb_inv_def)
  apply(elim conjE)
          apply(case_tac "pc ps t", simp_all add: globals; elim exE conjE)
   apply(case_tac "pc ps t"; simp add: globals)
  apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
  apply auto[1]
  done 
next show "glb_inv6 ps' cls'" 
  using assms
  apply(simp add: glb_inv_def)
  apply(elim conjE)
          apply(case_tac "pc ps t", simp_all add: globals; elim exE conjE)
      apply (metis assms(3) lib_push_L1_pushed)
     apply(intro allI conjI impI, elim conjE)
     apply (metis write_diff_var_last_val)
  using rd_A_preserves_last apply auto[1]
  apply (metis old.nat.inject write_diff_var_last_val)
  by (smt cvd_CAS_R_success_read_val insert_iff lib_cvd_exist_last_write succ_CAS_preserves_last)
next show "glb_inv7 ps' cls'" 
  using assms
  apply(simp add: glb_inv_def)
  apply(elim conjE)
          apply(case_tac "pc ps t", simp_all add: globals; elim exE conjE)
       apply(intro allI impI)
       apply(subgoal_tac "lib_writes_on cls' Top = lib_writes_on cls Top \<and>
lib_value cls' (a, b) = lib_value cls (a, b) \<and> lib_releasing cls' (a, b) = lib_releasing cls (a, b)")
        apply simp
       apply(simp add: lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
       apply clarsimp
  apply(simp add: lib_visible_writes_def lib_writes_on_def lib_value_def lib_releasing_def var_def tst_def)
       apply(intro conjI)
  apply (metis)
       apply auto[1]
       apply(intro allI impI)
       apply(subgoal_tac "lib_writes_on cls' Top = lib_writes_on cls Top \<and>
lib_value cls' (a, b) = lib_value cls (a, b) \<and> lib_releasing cls' (a, b) = lib_releasing cls (a, b)")
       apply simp
       apply(simp add: lib_read_step_def lib_read_def all_updates_l, elim exE conjE)
       apply clarsimp
  apply(simp add: lib_visible_writes_def lib_writes_on_def lib_value_def lib_releasing_def var_def tst_def)
   apply(intro allI impI)
  apply (metis wr_preserves_releasing_diff_var wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
  apply(intro allI impI, elim conjE)
  apply(case_tac "(a, b) \<in> lib_writes_on cls Top")
  apply(subgoal_tac "lib_value cls' (a, b) = lib_value cls (a, b)", simp)
  apply (simp add: CAS_Rel_preserves_releasing_same_var)
  using CAS_Rel_preserves_value_old apply auto[1]
   by (simp add: CAS_Rel_preserves_releasing_new)
next show "glb_inv8 ps' cls'" 
  using assms
  apply(simp add: glb_inv_def)
  apply(elim conjE)
          apply(case_tac "pc ps t", simp_all add: globals; elim exE conjE)
      apply (metis assms(3) lib_push_L1_pushed)  
  apply (metis write_diff_var_last_val)
  using rd_A_preserves_last apply auto[1]  
  apply (metis old.nat.inject write_diff_var_last_val)
  by (smt cvd_CAS_R_success_read_val insert_iff lib_cvd_exist_last_write succ_CAS_preserves_last)
next show "glb_inv9 ps'" 
  using assms
  apply(simp add: glb_inv_def)
  apply(elim conjE)
          apply(case_tac "pc ps t", simp_all add: globals; elim exE conjE)
  by (metis assms(3) in_mono lib_push_L1_addr_sub lib_push_L1_ntop)
next show "glb_inv10 ps' cls'" 
  using assms
  apply(simp add: glb_inv_def)
  apply(elim conjE)
          apply(case_tac "pc ps t", simp_all add: globals; elim exE conjE)
      apply (metis assms(3) lib_push_L1_pushed)
  apply (metis write_diff_var_last_val)
  using rd_A_preserves_last apply auto[1]
   apply (metis old.nat.inject write_diff_var_last_val)
  apply(intro allI impI)
  apply(case_tac "\<not>res ps' t")
  using failed_CAS_preserves_last apply auto[1]
  apply simp
  apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = n_val ps t", simp)
  apply (elim disjE) defer
    apply (metis gr0I succ_CAS_preserves_last)
   apply(subgoal_tac "x = top ps t", simp)
    apply(subgoal_tac "[lib(Top) =\<^sub>t (n_val ps t)] cls'")
  apply(simp add: lib_d_obs_def lib_d_obs_t_def)
  using cvd_CAS_R_success_d_obs_post apply auto[1]
  apply (metis cvd_CAS_R_success_read_val)
  by (metis succ_CAS_preserves_last)
next show "glb_inv12 ps' cls'" 
  using assms
  apply(simp add: glb_inv_def)
  apply(elim conjE)
  apply(case_tac "pc ps t", simp_all add: globals; elim exE conjE) 
   apply (metis assms(3) lib_push_L1_pushed)  
  by (metis finite_insert)
next show "glb_inv11 ps' cls'" 
  using assms
  apply(simp add: glb_inv_def)
  apply(elim conjE)
          apply(case_tac "pc ps t", simp_all add: globals; elim exE conjE)
  apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9)) 
  by (metis insertE)
next show "glb_inv13 ps' cls'" 
  using assms
  apply(simp add: glb_inv_def)
  apply(elim conjE)
  apply(case_tac "pc ps t", simp_all add: globals; elim exE conjE)
  apply (metis PC.distinct(1) fun_upd_idem_iff prog_state.select_convs(1) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
    apply(simp add: written_addr_def)
  apply (smt image_cong wr_preserves_value_diff_var wr_preserves_writes_on_diff_var write_diff_var_last_val)
    apply(simp add: written_addr_def) 
  apply (metis lib_read_writes_on_diff_var_pres_backwards rd_A_preserves_last rd_A_preserves_values)
    apply(simp add: written_addr_def) 
  apply (smt image_iff no_Top_n_def old.nat.inject wr_preserves_value_diff_var wr_preserves_writes_on_diff_var write_diff_var_last_val)
  apply(intro allI impI conjI)
   apply(simp add: written_addr_def, elim conjE)
   apply(case_tac "res ps' t", simp_all)
  apply(case_tac "ad \<in> lib_value cls `
             lib_writes_on cls Top")
     apply (metis succ_CAS_preserves_last)
  apply(subgoal_tac "ad = n_val ps t", simp)
     apply (metis cvd_CAS_R_success_read_val image_eqI lib_cvd_exist_write neq0_conv succ_CAS_preserves_last)
  using  CAS_Top_written_addr_post2[where b = "n_val ps t" and cls' = cls' and cls=cls
          and a = "top ps t" and t=t]
  apply (simp add: not_gr0)
  apply (metis failed_CAS_Top_written_addr_post succ_CAS_preserves_last)
    apply(simp add: written_addr_def, elim conjE)
   apply(case_tac "ad \<in> lib_value cls `
             lib_writes_on cls Top")
  apply simp
  apply(subgoal_tac "ad = n_val ps t", simp)
  using  CAS_Top_written_addr_post2[where b = "n_val ps t" and cls' = cls' and cls=cls
          and a = "top ps t" and t=t]
  apply (simp add: not_gr0)  
  by (metis (full_types) failed_CAS_Top_written_addr_post)
next show "glb_inv14 ps' cls'" 
  using assms
  apply(simp add: glb_inv_def )
  apply(elim conjE)
  apply(case_tac "pc ps t", simp_all add: globals written_addr_def; elim exE conjE)
  apply (smt image_cong wr_preserves_value_diff_var wr_preserves_writes_on_diff_var write_diff_var_last_val)
  apply (metis lib_read_writes_on_diff_var_pres_backwards rd_A_preserves_last rd_A_preserves_values)
   apply (smt image_iff no_Top_n_def old.nat.inject wr_preserves_value_diff_var wr_preserves_writes_on_diff_var write_diff_var_last_val)
  apply(case_tac "res ps' t", simp_all) defer
   apply (metis failed_CAS_Top_written_addr_post succ_CAS_preserves_last)
  apply(intro allI impI conjI, elim conjE)
  apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' Top = lib_value cls ` lib_writes_on cls Top \<union> {n_val ps t}")
  apply(case_tac "ad \<in> lib_value cls ` lib_writes_on cls Top", simp_all)
  apply (metis succ_CAS_preserves_last)
  apply (metis cvd_CAS_R_success_read_val image_eqI lib_cvd_exist_write succ_CAS_preserves_last)
  using success_CAS_Top_written_addr_post
  by (metis Un_insert_right sup_bot.right_neutral)
next show "glb_inv15 ps'" 
    using assms
  apply(simp add: glb_inv_def )
  apply(elim conjE)
    apply(case_tac "pc ps t", simp_all)
    apply(simp add: glb_inv15_def)
     apply (metis (no_types, lifting) PC.distinct(1) fun_upd_idem_iff prog_state.ext_inject prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
    apply(simp add: glb_inv15_def)
     apply (simp add: glb_inv15_def)
     apply (simp add: glb_inv15_def)
     apply (simp add: glb_inv15_def)
    done

next show "glb_inv16 ps' cls'" 
    using assms
    apply(case_tac "pc ps t", simp_all)
        apply(elim conjE)
  apply(simp add: glb_inv_def glb_inv16_def)
        apply (intro conjI impI allI, elim conjE exE)
    apply(subgoal_tac "lib_value cls ` lib_writes_on cls (Suc ad)
            \<subseteq> insert 0 (addr_val ps)")
    apply(subgoal_tac "addr_val ps' = addr_val ps \<union> {n_val ps' t}")
          apply (metis insert_is_Un sup.absorb_iff2 sup_assoc)
        apply (meson assms(3) lib_push_L1_addr_val2)
        apply simp
       apply(elim conjE)
       apply(simp add:glb_inv_def glb_inv16_def)
       apply (intro conjI impI allI, elim conjE exE)
       apply(subgoal_tac "written_addr cls' = written_addr cls")
    apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' (Suc ad)
=lib_value cls ` lib_writes_on cls (Suc ad)")
         apply simp
    apply(subgoal_tac "Suc ad \<noteq> n_val ps t")
         apply (metis (no_types, lifting) image_cong wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
    apply(simp add: no_Top_n_def no_Top_n_a_def globals)
        apply metis
       using diff_var_write_written_addr apply fastforce


       apply(simp add:glb_inv_def glb_inv16_def)
       apply (intro conjI impI allI, elim conjE exE)
       apply(subgoal_tac "written_addr cls' = written_addr cls")
    apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' (Suc ad)
=lib_value cls ` lib_writes_on cls (Suc ad)")
           apply simp
          apply (metis lib_read_writes_on_diff_var_pres_backwards rd_A_preserves_values)
         apply (metis lib_read_writes_on_diff_var_pres_backwards rd_A_preserves_values written_addr_def)
       apply(simp add:glb_inv_def glb_inv16_def)
       apply (intro conjI impI allI, elim conjE exE)
       apply(subgoal_tac "written_addr cls' = written_addr cls")
    apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' (Suc ad)
=lib_value cls ` lib_writes_on cls (Suc ad)")
          apply simp
       apply (smt image_cong old.nat.inject wr_preserves_value_diff_var wr_preserves_writes_on_diff_var)
        apply (metis diff_var_write_written_addr)
       apply(case_tac "\<not>res ps' t", simp_all)

       apply(simp add:glb_inv_def glb_inv16_def)
       apply (intro conjI impI allI, elim conjE exE)
       apply(subgoal_tac "written_addr cls' = written_addr cls")
        apply simp
      apply (smt failed_CAS_Rel_preserves_writes_on_diff_var failed_CAS_Top_written_addr_post image_subset_iff write_value_CAS_R_diff_var)  
       using failed_CAS_Top_written_addr_post2 apply auto[1]
       apply(simp add:glb_inv_def glb_inv16_def)
       apply (intro conjI impI allI, elim conjE exE)
       apply(simp add: written_vals_def)
       apply safe
        defer        
       apply(subgoal_tac "lib_writes_on cls' (Suc ad) =lib_writes_on cls (Suc ad)", simp)
        apply (smt CAS_Rel_preserves_value_old CAS_Top_written_addr_post image_eqI insert_iff subsetD write_value_CAS_R_diff_var)
        apply(simp add: globals)
        apply (metis CAS_Rel_preserves_writes_on_diff_var CAS_Top_written_addr_post)
        apply(simp add: globals)
            apply(subgoal_tac "lib_writes_on cls' (Suc ad) =lib_writes_on cls (Suc ad)", simp)
        apply (smt CAS_Top_written_addr_post image_eqI image_subset_iff insert_iff write_value_CAS_R_diff_var)
       by (metis CAS_Rel_preserves_writes_on_diff_var CAS_Top_written_addr_post)
       qed


lemma "cls ccs[n \<leftarrow> lib(x)]\<^sub>t cls' ccs' \<Longrightarrow> n\<in> lib_value cls `(lib_writes_on cls (x))"
  apply(simp add: lib_read_step_def lib_read_def all_updates_l lib_visible_writes_def)
  apply blast
  done


end
