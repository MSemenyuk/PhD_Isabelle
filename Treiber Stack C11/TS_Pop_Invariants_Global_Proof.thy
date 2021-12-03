theory TS_Pop_Invariants_Global_Proof
imports  TS_Proof_Rules
begin

lemmas [simp] = pop_inv_def new_node_def

lemmas [simp] = lib_pop_def



declare [[ smt_timeout = 800 ]]


lemma pop_inv_gc_push:
  assumes "wfs ccs"
      and "lib_wfs cls ccs"
      and "pop_inv t' l (pc ps t') cls ccs  ps"
      and "pop_inv t l (pc ps t) cls ccs  ps"
      and "lib_push t' v ps cls ccs ps' cls' ccs'"
      and "push_inv t' v (pc ps t') cls ccs  ps"
      and "glb_inv ps cls"
      and "t \<noteq> t'"
      and "glb ps cls"
      and "to ps cls"
    shows "pop_inv t l (pc ps' t) cls' ccs'  ps'"
    proof (cases "pc ps t'")
      case L5
      then show ?thesis
        using assms
        apply simp
        apply(case_tac "\<not> res ps' t'")
         apply(cases "pc ps' t"; cases "pc ps t"; simp; elim exE conjE)
        apply(subgoal_tac "written_addr cls' = written_addr cls")
             apply(intro allI conjI impI)
        using cobs_to_CAS_pres apply blast
        using cvd_CAS_R_cvd apply blast
             apply(simp add: written_addr_def)
        using failed_CAS_Top_written_addr_post2 apply blast
                  apply(simp add: written_addr_def)
             apply(intro allI conjI impI)
        
        using cobs_to_CAS_pres apply blast
        using failed_cas_dobs_to apply blast
        using cvd_CAS_R_cvd apply blast
        using failed_CASR_pres_d_obs_lib apply blast
        using failed_CASR_pres_d_obs_lib apply blast
        apply (simp add: failed_CAS_Top_written_addr_post)
          apply(intro conjI)
        using cobs_to_CAS_pres apply blast
        
        using failed_cas_dobs_to apply blast
        using cvd_CAS_R_cvd apply blast
        using failed_CASR_pres_d_obs_lib apply blast
        using failed_CAS_preserves_last apply auto[1]
        apply (simp add: failed_CAS_Top_written_addr_post2)
        using failed_CASR_pres_d_obs_lib apply blast
        apply (metis cvd_CAS_R_cvd failed_CASR_pres_d_obs_lib failed_CAS_Top_written_addr_post2)
          (*CAS success case*)
        apply(subgoal_tac "written_addr cls' = written_addr cls \<union> {n_val ps t'}")
         defer
         apply (smt Null_def success_CAS_Top_written_addr_post2)
        apply(cases "pc ps' t"; cases "pc ps t"; simp; elim exE conjE)
           apply(intro conjI)
            defer
        using cvd_CAS_R_cvd apply blast
           apply(intro conjI impI allI)
               defer
        defer
        using cvd_CAS_R_cvd apply blast
               apply(case_tac "top ps t \<in> pushed_addr ps", simp)
                apply(subgoal_tac "\<exists> v.  [lib(top ps t) =\<^sub>t v] cls")
                 apply(elim exE)
                 apply(rule_tac x = vaa in exI)
        apply(intro conjI impI)
                  apply simp
        apply(simp add: globals)
        apply (metis d_obs_post_CAS_R_diff_var_post in_mono)
        apply blast
               apply metis

               apply(case_tac "top ps t \<in> pushed_addr ps", simp)
                apply(subgoal_tac "\<exists> v.  [libSuc(top ps t) =\<^sub>t v] cls")
                 apply(elim exE)
                 apply(rule_tac x = vaa in exI)
        apply(intro conjI impI)
                  apply simp
                  apply(simp add: globals)
        apply(subgoal_tac "Suc (prog_state.top ps t) \<noteq> Top")
                  apply (metis d_obs_post_CAS_R_diff_var_post )
                   apply(simp add: globals)
       apply metis
       using lib_d_obs_cont apply blast

        apply blast
        apply metis


        
           apply(intro conjI impI allI)
               defer
        defer
        using cvd_CAS_R_cvd apply blast
               apply(case_tac "top ps t \<in> pushed_addr ps", simp)
                apply(subgoal_tac "\<exists> v.  [lib(top ps t) =\<^sub>t v] cls")
                 apply(elim exE)
                 apply(rule_tac x = va in exI)
        apply(intro conjI impI)
                  apply simp
        apply(simp add: globals)
        apply (metis d_obs_post_CAS_R_diff_var_post in_mono)
        apply blast
                  apply metis
        apply simp
          apply(simp add: globals)
      apply (metis succ_CAS_preserves_last)

               apply(case_tac "top ps t \<in> pushed_addr ps", simp)
                apply(subgoal_tac "\<exists> v.  [libSuc(top ps t) =\<^sub>t v] cls")
                 apply(elim exE)
                 apply(rule_tac x = va in exI)
        apply(intro conjI impI)
                  apply simp
                  apply(simp add: globals)
        apply(subgoal_tac "Suc (prog_state.top ps t) \<noteq> Top")
                  apply (metis d_obs_post_CAS_R_diff_var_post )
       apply metis
       using lib_d_obs_cont apply blast
              apply auto[1]
       apply(intro conjI)
       using cvd_CAS_R_cvd apply blast       
          apply(simp add: globals)
       apply (metis d_obs_post_CAS_R_diff_var_post subset_eq)

(***cobs_to begin***)
                 apply(simp add: cobs_to_def)
                 apply(intro allI impI conjI, elim disjE conjE)
                 apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
                    apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
       apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
       apply (simp add: lib_not_pobs_cobs no_Top_n_implies_no_p_obs)
                    apply(simp add: globals)
                     apply (metis gr_zeroI)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
                   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
       apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
       using lib_not_pobs_cobs no_Top_n_implies_no_p_obs apply blast
          apply(simp add: globals)
                  apply (metis gr_zeroI)
                 apply(subgoal_tac "\<not>[lib(Top) \<approx>\<^sub>t (n_val ps t')] cls")
       apply(subgoal_tac "(\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and> ad2 \<noteq> Top")
                   apply (metis successful_CAS_lib_c_obs_lib_only_intro)
       apply(intro conjI, simp add: dobs_to_def)
       apply (metis Null_def TopLV_Null_pushed_empty TopLV_agt_others assms(9) cvd_CAS_R_success_read_val empty_iff lastTop_def lib_cvd_exist_last_write neq0_conv)
           apply(simp add: globals)
      apply (meson in_mono)
      apply (simp add: no_Top_n_implies_no_p_obs)
                apply auto[1]
       apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
               apply (meson agt_n_val_False)
       apply(simp add: globals)
               apply (metis gr0I succ_CAS_preserves_last)
              apply blast
       apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls", elim exE)
              apply(rule_tac x= vl in exI) 
       apply(simp add: globals)
       apply(subgoal_tac "n_val ps t' \<notin> pushed_addr ps \<union> {Top}")
       apply (metis insert_absorb insert_subset successful_CAS_lib_c_obs_lib_diff_value_pres)
              apply force



             apply(subgoal_tac "agt ad1 ad2 ps cls")
              apply (metis)
         apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
       using  agt_pushed_successful_cas_before
       apply (metis (no_types, lifting) assms(9) insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
              apply (metis no_nxt_no_agt)
             apply(intro allI impI)
       apply(simp add: globals)
       using succ_CAS_preserves_last
         apply (metis gr0I)
         
         apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls", elim exE)
              apply(rule_tac x= vl in exI) 
       apply(simp add: globals)
             apply(subgoal_tac "n_val ps t' \<notin> pushed_addr ps \<union> {Top}")
       apply (metis subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
        apply force
            apply blast
       apply(elim conjE disjE)
        apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
                   apply (meson agt_n_val_False)
                  apply(intro allI impI)
       apply(simp, elim disjE)
                   apply (metis gr0I succ_CAS_preserves_last)
        apply(simp add: globals)
      
       apply (metis gr0I succ_CAS_preserves_last)
        apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
                  apply(subgoal_tac "\<not>[lib(Top) \<approx>\<^sub>t (Suc (n_val ps t'))] cls")
       apply(subgoal_tac "(\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and> Suc ad2 \<noteq> Top")
                  apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
       apply(intro conjI)
                  apply(simp add: dobs_to_def)
       apply(subgoal_tac "Suc ad2 \<noteq> Top")
       apply (smt Null_def TopLV_Null_pushed_empty TopLV_agt_others assms(9) cvd_CAS_R_success_read_val empty_iff lastTop_def lib_cvd_exist_last_write neq0_conv)

        apply(simp add: globals)
       apply metis
        apply(simp add: globals)
                 apply metis
                apply (metis no_Top_n_implies_no_p_obs)
       apply auto[1]
          apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
     apply (meson agt_n_val_False)
                   apply(intro allI impI)
       apply(simp, elim disjE)
                   apply (metis gr0I succ_CAS_preserves_last)
        apply(simp add: globals)
      
       apply (metis gr0I succ_CAS_preserves_last)
             apply simp
            apply(subgoal_tac "agt ad1 ad2 ps cls")
       apply(simp add: globals)
    apply (metis successful_CAS_lib_c_obs_lib_diff_value_pres)

  apply(subgoal_tac "agt ad1 ad2 ps cls")
              apply (metis)
         apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
       using  agt_pushed_successful_cas_before
       apply (metis (no_types, lifting) assms(9) insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
              apply (metis no_nxt_no_agt)
             apply(intro allI impI)
       apply(simp add: globals)
       using succ_CAS_preserves_last
         apply (metis gr0I)
       
       apply(simp add: globals)
       apply (metis successful_CAS_lib_c_obs_lib_diff_value_pres)
(****end cobs_to proof*****)


(***cobs_to begin***)
                 apply(simp add: cobs_to_def)
                 apply(intro allI impI conjI, elim disjE conjE)
                 apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
                    apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
       apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
       apply (simp add: lib_not_pobs_cobs no_Top_n_implies_no_p_obs)
                    apply(simp add: globals)
                     apply (metis gr_zeroI)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
                   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
       apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
       using lib_not_pobs_cobs no_Top_n_implies_no_p_obs apply blast
          apply(simp add: globals)
                  apply (metis gr_zeroI)
                 apply(subgoal_tac "\<not>[lib(Top) \<approx>\<^sub>t (n_val ps t')] cls")
       apply(subgoal_tac "(\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and> ad2 \<noteq> Top")
                   apply (metis successful_CAS_lib_c_obs_lib_only_intro)
       apply(intro conjI, simp add: dobs_to_def)
       apply (metis Null_def TopLV_Null_pushed_empty TopLV_agt_others assms(9) cvd_CAS_R_success_read_val empty_iff lastTop_def lib_cvd_exist_last_write neq0_conv)
           apply(simp add: globals)
      apply (meson in_mono)
      apply (simp add: no_Top_n_implies_no_p_obs)
                apply auto[1]
       apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
               apply (meson agt_n_val_False)
       apply(simp add: globals)
               apply (metis gr0I succ_CAS_preserves_last)
              apply blast
       apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls", elim exE)
              apply(rule_tac x= vl in exI) 
       apply(simp add: globals)
       apply(subgoal_tac "n_val ps t' \<notin> pushed_addr ps \<union> {Top}")
       apply (metis insert_absorb insert_subset successful_CAS_lib_c_obs_lib_diff_value_pres)
       apply force
  apply(subgoal_tac "agt ad1 ad2 ps cls")
              apply (metis)
         apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
       using  agt_pushed_successful_cas_before
       apply (metis (no_types, lifting) assms(9) insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
              apply (metis no_nxt_no_agt)
             apply(intro allI impI)
       apply(simp add: globals)
       using succ_CAS_preserves_last
       apply (metis gr0I)
       apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls", elim exE)
              apply(rule_tac x= vl in exI) 
       apply(simp add: globals)
             apply(subgoal_tac "n_val ps t' \<notin> pushed_addr ps \<union> {Top}")
       apply (metis subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
        apply force
            apply blast
       apply(elim conjE disjE)
        apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
                   apply (meson agt_n_val_False)
                  apply(intro allI impI)
       apply(simp, elim disjE)
                   apply (metis gr0I succ_CAS_preserves_last)
        apply(simp add: globals)
      
       apply (metis gr0I succ_CAS_preserves_last)
        apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
                  apply(subgoal_tac "\<not>[lib(Top) \<approx>\<^sub>t (Suc (n_val ps t'))] cls")
       apply(subgoal_tac "(\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and> Suc ad2 \<noteq> Top")
                  apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
       apply(intro conjI)
                 apply(simp add: dobs_to_def lastTop_def) 
       using TopLV_Null_pushed_empty TopLV_agt_others cvd_CAS_R_success_read_val
      apply (smt Null_def assms(9) empty_iff lastTop_def lib_cvd_exist_last_write neq0_conv)


        apply(simp add: globals)
       apply metis
       apply (metis no_Top_n_implies_no_p_obs)
       apply auto[1]
          apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
     apply (meson agt_n_val_False)
                   apply(intro allI impI)
       apply(simp, elim disjE)
                   apply (metis gr0I succ_CAS_preserves_last)
        apply(simp add: globals)
      
       apply (metis gr0I succ_CAS_preserves_last)
             apply simp
            apply(subgoal_tac "agt ad1 ad2 ps cls")
       apply(simp add: globals)
    apply (metis successful_CAS_lib_c_obs_lib_diff_value_pres)
  apply(subgoal_tac "agt ad1 ad2 ps cls")
              apply (metis)
         apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
       using  agt_pushed_successful_cas_before
       apply (metis (no_types, lifting) assms(9) insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
              apply (metis no_nxt_no_agt)
             apply(intro allI impI)
       apply(simp add: globals)
       using succ_CAS_preserves_last
           apply (metis gr0I)
          apply(simp add: globals)
    apply (metis successful_CAS_lib_c_obs_lib_diff_value_pres)
(****end cobs_to proof*****)
       defer
(***cobs_to begin***)
                 apply(simp add: cobs_to_def)
                 apply(intro allI impI conjI, elim disjE conjE)
                 apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
                    apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
       apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
       apply (simp add: lib_not_pobs_cobs no_Top_n_implies_no_p_obs)
                    apply(simp add: globals)
                     apply (metis gr_zeroI)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
                   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
       apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
       using lib_not_pobs_cobs no_Top_n_implies_no_p_obs apply blast
          apply(simp add: globals)
                  apply (metis gr_zeroI)
                 apply(subgoal_tac "\<not>[lib(Top) \<approx>\<^sub>t (n_val ps t')] cls")
       apply(subgoal_tac "(\<exists>vl. [libad2 =\<^sub>t' vl] cls) \<and> ad2 \<noteq> Top")
                   apply (metis successful_CAS_lib_c_obs_lib_only_intro)
       apply(intro conjI, simp add: dobs_to_def)
       apply (metis Null_def TopLV_Null_pushed_empty TopLV_agt_others assms(9) cvd_CAS_R_success_read_val empty_iff lastTop_def lib_cvd_exist_last_write neq0_conv)
           apply(simp add: globals)
      apply (meson in_mono)
      apply (simp add: no_Top_n_implies_no_p_obs)
                apply auto[1]
       apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
               apply (meson agt_n_val_False)
       apply(simp add: globals)
               apply (metis gr0I succ_CAS_preserves_last)
              apply blast
       apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls", elim exE)
              apply(rule_tac x= vl in exI) 
       apply(simp add: globals)
       apply(subgoal_tac "n_val ps t' \<notin> pushed_addr ps \<union> {Top}")
       apply (metis insert_absorb insert_subset successful_CAS_lib_c_obs_lib_diff_value_pres)
       apply force
  apply(subgoal_tac "agt ad1 ad2 ps cls")
              apply (metis)
         apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
       using  agt_pushed_successful_cas_before
       apply (metis (no_types, lifting) assms(9) insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
              apply (metis no_nxt_no_agt)
             apply(intro allI impI)
       apply(simp add: globals)
       using succ_CAS_preserves_last
                   apply (metis gr0I)
                  apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls", elim exE)
              apply(rule_tac x= vl in exI) 
       apply(simp add: globals)
             apply(subgoal_tac "n_val ps t' \<notin> pushed_addr ps \<union> {Top}")
       apply (metis subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
        apply force
            apply blast
        apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
                   apply (meson agt_n_val_False)
                  apply(intro allI impI)
       apply(simp, elim disjE)
                   apply (metis gr0I succ_CAS_preserves_last)
        apply(simp add: globals)
      
       apply (metis gr0I succ_CAS_preserves_last)
        apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
                  apply(subgoal_tac "\<not>[lib(Top) \<approx>\<^sub>t ((n_val ps t'))] cls")
                apply(subgoal_tac "(\<exists>vl. [lib(ad2) =\<^sub>t' vl] cls) \<and>  ad2 \<noteq> Top")
                  apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
       apply(intro conjI)
        apply(simp add: dobs_to_def)
  apply (smt Null_def TopLV_Null_pushed_empty TopLV_agt_others assms(9) cvd_CAS_R_success_read_val empty_iff lastTop_def lib_cvd_exist_last_write neq0_conv)(*too slow*)

                apply(simp add: globals)
       apply (metis in_mono)
       apply (metis no_Top_n_implies_no_p_obs)
       apply auto[1]
          apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
     apply (meson agt_n_val_False)
                   apply(intro allI impI)
       apply(simp, elim disjE)
                   apply (metis gr0I succ_CAS_preserves_last)
        apply(simp add: globals)
      
       apply (metis gr0I succ_CAS_preserves_last)
            apply simp
           apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls", elim exE)
       apply(simp add: globals)
                 apply (smt subset_eq successful_CAS_lib_c_obs_lib_diff_value_pres)
            apply(subgoal_tac "agt ad1 ad2 ps cls")
    apply (metis)
  apply(subgoal_tac "agt ad1 ad2 ps cls")
              apply (metis)
         apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
       using  agt_pushed_successful_cas_before
       apply (metis (no_types, lifting) assms(9) insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
              apply (metis no_nxt_no_agt)
             apply(intro allI impI)
       apply(simp add: globals)
       using succ_CAS_preserves_last
           apply (metis gr0I)
          apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls", elim exE)
      apply(simp add: globals) 
       apply (smt subset_eq successful_CAS_lib_c_obs_lib_diff_value_pres)
          apply(simp add: globals)

       apply(elim disjE conjE)

(****)
                 apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
                    apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
       apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
       apply (simp add: lib_not_pobs_cobs no_Top_n_implies_no_p_obs)
                    apply(simp add: globals)
                     apply (metis gr_zeroI)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
                   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
       apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
       using lib_not_pobs_cobs no_Top_n_implies_no_p_obs apply blast
          apply(simp add: globals)
                  apply (metis gr_zeroI)
                 apply(subgoal_tac "\<not>[lib(Top) \<approx>\<^sub>t (n_val ps t')] cls")
       apply(subgoal_tac "(\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and> Suc(ad2) \<noteq> Top")
                   apply (metis successful_CAS_lib_c_obs_lib_only_intro)
       apply(intro conjI, simp add: dobs_to_def)
       apply (metis Null_def TopLV_Null_pushed_empty TopLV_agt_others assms(9) cvd_CAS_R_success_read_val empty_iff lastTop_def lib_cvd_exist_last_write neq0_conv)
                       apply(simp add: globals)

       apply metis
      apply (simp add: no_Top_n_implies_no_p_obs)
                apply auto[1]
       apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
               apply (meson agt_n_val_False)
       apply(simp add: globals)
               apply (metis gr0I succ_CAS_preserves_last)
              apply blast
       apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls", elim exE)
              apply(rule_tac x= vl in exI) 
       apply(simp add: globals)
       apply(subgoal_tac "n_val ps t' \<notin> pushed_addr ps \<union> {Top}")
       apply (metis insert_absorb insert_subset successful_CAS_lib_c_obs_lib_diff_value_pres)
       apply force
  apply(subgoal_tac "agt ad1 ad2 ps cls")
              apply (metis)
         apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
       using  agt_pushed_successful_cas_before
       apply (metis (no_types, lifting) assms(9) insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
              apply (metis no_nxt_no_agt)
             apply(intro allI impI)
       apply(simp add: globals)
       using succ_CAS_preserves_last
                  apply (metis gr0I)
                 apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls", elim exE)
              apply(rule_tac x= vl in exI) 
       apply(simp add: globals)
             apply(subgoal_tac "n_val ps t' \<notin> pushed_addr ps \<union> {Top}")
       apply (metis subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
        apply force
            apply blast
        apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
                   apply (meson agt_n_val_False)
                  apply(intro allI impI)
       apply(simp, elim disjE)
                   apply (metis gr0I succ_CAS_preserves_last)
        apply(simp add: globals)
      
       apply (metis gr0I succ_CAS_preserves_last)
        apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
                  apply(subgoal_tac "\<not>[lib(Top) \<approx>\<^sub>t ((n_val ps t'))] cls")
                apply(subgoal_tac "(\<exists>vl. [libSuc(ad2) =\<^sub>t' vl] cls) \<and>  Suc(ad2) \<noteq> Top")
                  apply (metis no_Top_n_implies_no_p_obs successful_CAS_lib_c_obs_lib_only_intro)
       apply(intro conjI)
        apply(simp add: dobs_to_def)
  apply (smt Null_def TopLV_Null_pushed_empty TopLV_agt_others assms(9) cvd_CAS_R_success_read_val empty_iff lastTop_def lib_cvd_exist_last_write neq0_conv)(*too slow*)

                apply(simp add: globals)
       apply (metis in_mono)
       apply (metis no_Top_n_implies_no_p_obs)
       apply auto[1]
          apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
     apply (meson agt_n_val_False)
                   apply(intro allI impI)
       apply(simp, elim disjE)
                   apply (metis gr0I succ_CAS_preserves_last)
        apply(simp add: globals)
      
       apply (metis gr0I succ_CAS_preserves_last)
            apply simp
           apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls", elim exE)
       apply(simp add: globals)
                 apply (smt subset_eq successful_CAS_lib_c_obs_lib_diff_value_pres)
            apply(subgoal_tac "agt ad1 ad2 ps cls")
    apply (metis)
  apply(subgoal_tac "agt ad1 ad2 ps cls")
              apply (metis)
         apply(subgoal_tac "\<not> agt ad1 (n_val ps t') ps' cls'")
       using  agt_pushed_successful_cas_before
       apply (metis (no_types, lifting) assms(9) insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
              apply (metis no_nxt_no_agt)
             apply(intro allI impI)
       apply(simp add: globals)
       using succ_CAS_preserves_last
          apply (metis gr0I)
         apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls", elim exE)
      apply(simp add: globals)
       apply (smt subset_eq successful_CAS_lib_c_obs_lib_diff_value_pres)
          apply(simp add: globals)

(****end cobs_to proof*****)
(****beging dobs_to proof *)
        apply(simp add: dobs_to_def, intro allI impI conjI)
         apply(elim disjE conjE)
          apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
    apply (meson agt_n_val_False)
                   apply(intro allI impI)
       apply(simp, elim disjE)
                   apply (metis gr0I succ_CAS_preserves_last)
        apply(simp add: globals)
      
       apply (metis gr0I succ_CAS_preserves_last)
               apply simp        
       apply(subgoal_tac " (\<exists>vl. [libad =\<^sub>t vl] cls)", elim exE)
        apply(simp add: globals)
               apply (metis d_obs_post_CAS_R_diff_var_post in_mono)
       apply(case_tac "top ps t\<in>pushed_addr ps")
        apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
                apply blast


         apply(subgoal_tac "\<not> agt (prog_state.top ps t) (n_val ps t') ps' cls'")
       using  agt_pushed_successful_cas_before
       apply (metis (no_types, lifting) assms(9) insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
              apply (metis no_nxt_no_agt)
             apply(intro allI impI)
       apply(simp add: globals)
       using succ_CAS_preserves_last
         apply (metis gr0I)



              apply(subgoal_tac "prog_state.top ps t \<notin> pushed_addr ps'")
               apply (meson agt_ad1_not_in_pushed_False)
       apply auto[1]
       apply(subgoal_tac "\<exists>vl. [libad =\<^sub>t vl] cls", elim exE)
                apply(simp add: globals)
  apply (metis assms(1) assms(2) cvd_CAS_R_success_read_val d_obs_post_CAS_R_diff_var_post equalityE insert_subset subset_trans)
  apply blast
          apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
    apply (meson agt_n_val_False)
                   apply(intro allI impI)
       apply(simp, elim disjE)
                   apply (metis gr0I succ_CAS_preserves_last)
        apply(simp add: globals)
      
       apply (metis gr0I succ_CAS_preserves_last)
               apply simp        

       
       apply(case_tac "top ps t\<in>pushed_addr ps")
           apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
       apply(subgoal_tac "\<exists>vl. [libad =\<^sub>t vl] cls", elim exE)
                apply(simp add: globals)
  apply (metis assms(1) assms(2) cvd_CAS_R_success_read_val d_obs_post_CAS_R_diff_var_post equalityE insert_subset subset_trans)
  apply blast
   apply(subgoal_tac "\<not> agt (prog_state.top ps t) (n_val ps t') ps' cls'")
       using  agt_pushed_successful_cas_before
       apply (metis (no_types, lifting) assms(9) insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
              apply (metis no_nxt_no_agt)
             apply(intro allI impI)
       apply(simp add: globals)
       using succ_CAS_preserves_last
         apply (metis gr0I)
       
       apply (metis agt_ad1_not_in_pushed_False insert_iff)
        apply(subgoal_tac "\<exists>vl. [libad =\<^sub>t vl] cls", elim exE)
         apply(simp add: globals)
     apply (metis assms(1) assms(2) cvd_CAS_R_success_read_val d_obs_post_CAS_R_diff_var_post equalityE insert_subset subset_trans)
          apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
                   apply (metis)
        apply(simp add: globals)
         apply (metis gr0I succ_CAS_preserves_last)

(****)
         apply(elim disjE conjE)
          apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
    apply (meson agt_n_val_False)
                   apply(intro allI impI)
       apply(simp, elim disjE)
                   apply (metis gr0I succ_CAS_preserves_last)
        apply(simp add: globals)
      
       apply (metis gr0I succ_CAS_preserves_last)
               apply simp        
       apply(subgoal_tac " (\<exists>vl. [libSuc(ad) =\<^sub>t vl] cls)", elim exE)
        apply(simp add: globals)
               apply (metis d_obs_post_CAS_R_diff_var_post in_mono)
       apply(case_tac "top ps t\<in>pushed_addr ps")
        apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
    apply blast
   apply(subgoal_tac "\<not> agt (prog_state.top ps t) (n_val ps t') ps' cls'")
       using  agt_pushed_successful_cas_before
       apply (metis (no_types, lifting) assms(9) insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
              apply (metis no_nxt_no_agt)
             apply(intro allI impI)
       apply(simp add: globals)
       using succ_CAS_preserves_last
         apply (metis gr0I)
              apply(subgoal_tac "prog_state.top ps t \<notin> pushed_addr ps'")
               apply (meson agt_ad1_not_in_pushed_False)
       apply auto[1]
       apply(subgoal_tac "\<exists>vl. [libSuc(ad) =\<^sub>t vl] cls", elim exE)
                apply(simp add: globals)
  apply (metis assms(1) assms(2) cvd_CAS_R_success_read_val d_obs_post_CAS_R_diff_var_post equalityE insert_subset subset_trans)
  apply blast
          apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
    apply (meson agt_n_val_False)
                   apply(intro allI impI)
       apply(simp, elim disjE)
                   apply (metis gr0I succ_CAS_preserves_last)
        apply(simp add: globals)
      
       apply (metis gr0I succ_CAS_preserves_last)
               apply simp        

       
       apply(case_tac "top ps t\<in>pushed_addr ps")
           apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
       apply(subgoal_tac "\<exists>vl. [libSuc(ad) =\<^sub>t vl] cls", elim exE)
                apply(simp add: globals)
  apply (metis assms(1) assms(2) cvd_CAS_R_success_read_val d_obs_post_CAS_R_diff_var_post equalityE insert_subset subset_trans)
  apply blast
   apply(subgoal_tac "\<not> agt (prog_state.top ps t) (n_val ps t') ps' cls'")
       using  agt_pushed_successful_cas_before
       apply (metis (no_types, lifting) assms(9) insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
              apply (metis no_nxt_no_agt)
             apply(intro allI impI)
       apply(simp add: globals)
       using succ_CAS_preserves_last
         apply (metis gr0I)
       
       apply (metis agt_ad1_not_in_pushed_False insert_iff)
        apply(subgoal_tac "\<exists>vl. [libSuc(ad) =\<^sub>t vl] cls", elim exE)
         apply(simp add: globals)
     apply (metis assms(1) assms(2) cvd_CAS_R_success_read_val d_obs_post_CAS_R_diff_var_post equalityE insert_subset subset_trans)
          apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
                   apply (metis)
        apply(simp add: globals)
         apply (metis gr0I succ_CAS_preserves_last)
(***end dobs_to proof***)

(****beging dobs_to proof *)
        apply(simp add: dobs_to_def, intro allI impI conjI)
         apply(elim disjE conjE)
          apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
    apply (meson agt_n_val_False)
                   apply(intro allI impI)
       apply(simp, elim disjE)
                   apply (metis gr0I succ_CAS_preserves_last)
        apply(simp add: globals)
      
       apply (metis gr0I succ_CAS_preserves_last)
               apply simp        
       apply(subgoal_tac " (\<exists>vl. [libad =\<^sub>t vl] cls)", elim exE)
        apply(simp add: globals)
               apply (metis d_obs_post_CAS_R_diff_var_post in_mono)
       apply(case_tac "top ps t\<in>pushed_addr ps")
        apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
    apply blast
   apply(subgoal_tac "\<not> agt (prog_state.top ps t) (n_val ps t') ps' cls'")
       using  agt_pushed_successful_cas_before
       apply (metis (no_types, lifting) assms(9) insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
              apply (metis no_nxt_no_agt)
             apply(intro allI impI)
       apply(simp add: globals)
       using succ_CAS_preserves_last
         apply (metis gr0I)
              apply(subgoal_tac "prog_state.top ps t \<notin> pushed_addr ps'")
               apply (meson agt_ad1_not_in_pushed_False)
       apply auto[1]
       apply(subgoal_tac "\<exists>vl. [libad =\<^sub>t vl] cls", elim exE)
                apply(simp add: globals)
  apply (metis assms(1) assms(2) cvd_CAS_R_success_read_val d_obs_post_CAS_R_diff_var_post equalityE insert_subset subset_trans)
        apply blast







(****)
         apply(elim disjE conjE)
          apply(subgoal_tac "\<forall>p. p \<in> pushed_addr ps' \<longrightarrow>  lastVal cls' (Suc p) \<noteq> (n_val ps t')")
    apply (meson agt_n_val_False)
                   apply(intro allI impI)
       apply(simp, elim disjE)
                   apply (metis gr0I succ_CAS_preserves_last)
        apply(simp add: globals)
      
       apply (metis gr0I succ_CAS_preserves_last)
               apply simp        
       apply(subgoal_tac " (\<exists>vl. [libSuc(ad) =\<^sub>t vl] cls)", elim exE)
        apply(simp add: globals)
               apply (metis d_obs_post_CAS_R_diff_var_post in_mono)
       apply(case_tac "top ps t\<in>pushed_addr ps")
        apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
    apply blast
   apply(subgoal_tac "\<not> agt (prog_state.top ps t) (n_val ps t') ps' cls'")
       using  agt_pushed_successful_cas_before
       apply (metis (no_types, lifting) assms(9) insert_is_Un sup_commute)
         apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps' \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) \<noteq> n_val ps t'")
              apply (metis no_nxt_no_agt)
             apply(intro allI impI)
       apply(simp add: globals)
       using succ_CAS_preserves_last
         apply (metis gr0I)
              apply(subgoal_tac "prog_state.top ps t \<notin> pushed_addr ps'")
               apply (meson agt_ad1_not_in_pushed_False)
       apply auto[1]
       apply(subgoal_tac "\<exists>vl. [libSuc(ad) =\<^sub>t vl] cls", elim exE)
                apply(simp add: globals)
  apply (metis assms(1) assms(2) cvd_CAS_R_success_read_val d_obs_post_CAS_R_diff_var_post equalityE insert_subset subset_trans)
       by blast
    next
      case L1
      then show ?thesis                   
          using assms
          apply(cases "pc ps t"; simp ; elim exE conjE; simp)
          apply(intro conjI)
                apply (meson lib_push_L1_new_address_not_null)     
          apply (meson assms(5) lib_push_L1_new_address_not_null)
                apply (meson assms(5) lib_push_L1_new_address_not_null)
               apply (metis Null_def assms(5) lib_push_L1_new_address_not_null)
          apply(simp add: cobs_to_def)
              apply (metis agt_pushed_same2 assms(5) lib_push_L1_pushed)
                apply (metis assms(5) lib_push_L1_pc)
           apply(intro conjI)
                apply (meson lib_push_L1_new_address_not_null)     
          apply (meson assms(5) lib_push_L1_new_address_not_null)
                apply (meson assms(5) lib_push_L1_new_address_not_null)
                      apply (metis  assms(5) lib_push_L1_new_address_not_null)
                     apply (meson assms(5) lib_push_L1_new_address_not_null)
                     apply (meson assms(5) lib_push_L1_new_address_not_null)
  apply (meson assms(5) lib_push_L1_new_address_not_null)
  apply (metis Null_def assms(5) lib_push_L1_new_address_not_null)
          apply(simp add: cobs_to_def)
                 apply (metis agt_pushed_same2 assms(5) lib_push_L1_pushed)
          apply(simp add: dobs_to_def)
          apply (metis agt_pushed_same2 assms(5) lib_push_L1_pc lib_push_L1_pushed)
          apply (metis assms(5) lib_push_L1_pc)
          apply (metis assms(5) lib_push_L1_pc lib_push_L1_pushed)

          apply (metis Un_empty_right Un_insert_right assms(5) insertCI lib_push_L1_addr_val2 lib_push_L1_pc lib_push_L1_pushed)
          apply (metis assms(5) lib_push_L1_pc)
          apply (metis (no_types, lifting) PC.distinct(1) fun_upd_idem_iff prog_state.ext_inject prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
          apply (metis (no_types, lifting) PC.distinct(1) fun_upd_idem_iff prog_state.ext_inject prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))
          done
        next
      case L2
      then show ?thesis 
          using assms
          by(cases "pc ps t"; simp ; elim exE conjE)      
    next 
      case L3
      then show ?thesis
        using assms
       apply(cases "pc ps t"; simp add: glb_inv14_def; elim exE conjE; simp)
        apply(cases "pc ps' t", simp_all) 
           apply (intro conjI impI allI)
        using cobs_to_read_pres apply blast
        using lib_read_cvd_pres apply blast
        apply(simp add: written_addr_def)    
        apply (simp add: rd_A_preserves_values read_pres_writes_on_diff_var)
          apply(intro allI conjI impI)
               apply (simp add: cobs_to_read_pres)
        apply(simp add: dobs_to_def globals)
            apply(intro allI conjI impI)
      apply (metis agt_pushed_same2rd_before_state lib_d_obs_pres_read)
          apply (metis agt_pushed_same2rd_before_state lib_d_obs_pres_read)
    using lib_read_cvd_pres apply blast
        using lib_d_obs_pres_read apply blast
        using lib_d_obs_pres_read apply blast
        apply(simp add: written_addr_def)
          apply (metis lib_read_writes_on_diff_var_pres_backwards rd_A_preserves_values)
         apply(intro allI conjI impI)
               apply (simp add: cobs_to_read_pres)
        apply(simp add: dobs_to_def globals)
            apply(intro allI conjI impI)
      apply (metis agt_pushed_same2rd_before_state lib_d_obs_pres_read)
          apply (metis agt_pushed_same2rd_before_state lib_d_obs_pres_read)
    using lib_read_cvd_pres apply blast
    using lib_d_obs_pres_read apply blast
    apply (simp add: rd_A_preserves_last)
        apply(simp add: written_addr_def)
      apply (metis lib_read_writes_on_diff_var_pres_backwards rd_A_preserves_values)
    using lib_d_obs_pres_read apply blast
    apply(intro allI conjI)
    using lib_read_cvd_pres apply blast
    using lib_d_obs_pres_read apply blast
    by (simp add: rd_A_preserves_values rd_A_preserves_writes_on written_addr_def)
    next
      case L4
      then show ?thesis using assms
       apply(cases "pc ps t"; simp add: glb_inv14_def; elim exE conjE; simp)
           apply(intro conjI)
             apply(simp add: cobs_to_def )
        apply(intro allI impI conjI, elim conjE disjE)
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>lib(ad2) =\<^sub>t vl \<rparr> cls")
                apply(elim exE, rule_tac x=vl in exI)
        apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
               apply(simp add: globals)
               apply(subgoal_tac "agt ad1 ad2 ps cls")
                apply simp
        using agt_pres_diff_write no_Top_n_def
        apply (smt Suc_inject) (*too slow*)
        apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
        apply(elim conjE disjE)
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
              apply(elim exE, rule_tac x=vl in exI)
        apply (metis Suc_inject lib_c_obs_lib_only_pres_wr_diff_var)
               apply(simp add: globals)
               apply(subgoal_tac "agt ad1 ad2 ps cls")
                apply simp
        using agt_pres_diff_write no_Top_n_def
              apply (smt Suc_inject) (*too slow*)
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
              apply(elim exE, rule_tac x=vl in exI)
        apply (metis Suc_inject lib_c_obs_lib_only_pres_wr_diff_var)        
        apply (metis )
            apply (metis lib_covered_write_diff_var_pres)
        using diff_var_write_written_addr apply fastforce
        apply(intro conjI)
             apply(simp add: cobs_to_def )
        apply(intro allI impI conjI, elim conjE disjE)
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>lib(ad2) =\<^sub>t vl \<rparr> cls")
                apply(elim exE, rule_tac x=vl in exI)
        apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
               apply(simp add: globals)
               apply(subgoal_tac "agt ad1 ad2 ps cls")
                apply simp
        using agt_pres_diff_write no_Top_n_def
        apply (smt Suc_inject) (*too slow*)
        apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
        apply(elim conjE disjE)
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
              apply(elim exE, rule_tac x=vl in exI)
        apply (metis Suc_inject lib_c_obs_lib_only_pres_wr_diff_var)
               apply(simp add: globals)
               apply(subgoal_tac "agt ad1 ad2 ps cls")
                apply simp
        using agt_pres_diff_write no_Top_n_def
              apply (smt Suc_inject) (*too slow*)
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
              apply(elim exE, rule_tac x=vl in exI)
        apply (metis Suc_inject lib_c_obs_lib_only_pres_wr_diff_var)        
               apply (metis )
              apply(simp add: globals dobs_to_def, intro conjI impI allI; elim disjE conjE)
        apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
                  apply (metis assms(2) d_obs_write_diff_var)
         using agt_pres_diff_write no_Top_n_def
       apply (smt Suc_inject)(*too slow*)

                 apply (metis d_obs_write_diff_var)
         apply(subgoal_tac " Ex (lib_d_obs_t cls t (Suc ad)) \<and> Suc (n_val ps
                         t') \<noteq> Suc ad")
                 apply (metis d_obs_write_diff_var)
         apply(intro conjI)
       apply (smt Suc_inject agt_pres_diff_write)
       apply blast
       apply (metis d_obs_write_diff_var old.nat.inject)
       apply (metis lib_covered_write_diff_var_pres)
       apply (metis d_obs_write_diff_var)
       apply (metis Suc_inject d_obs_write_diff_var)
           apply (metis diff_var_write_written_addr)
          apply(intro allI impI conjI)

             apply(simp add: cobs_to_def )
        apply(intro allI impI conjI, elim conjE disjE)
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>lib(ad2) =\<^sub>t vl \<rparr> cls")
                apply(elim exE, rule_tac x=vl in exI)
        apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
               apply(simp add: globals)
               apply(subgoal_tac "agt ad1 ad2 ps cls")
                apply simp
        using agt_pres_diff_write no_Top_n_def
        apply (smt Suc_inject) (*too slow*)
        apply (metis lib_c_obs_lib_only_pres_wr_diff_var)
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>lib(ad2) =\<^sub>t vl \<rparr> cls")
              apply(elim exE, rule_tac x=vl in exI)
        apply (metis Suc_inject lib_c_obs_lib_only_pres_wr_diff_var)
               apply(simp add: globals)
               apply(subgoal_tac "agt ad1 ad2 ps cls")
                apply simp
        using agt_pres_diff_write no_Top_n_def
              apply (smt Suc_inject) (*too slow*)
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>lib(ad2) =\<^sub>t vl \<rparr> cls")
              apply(elim exE, rule_tac x=vl in exI)
        apply (metis Suc_inject lib_c_obs_lib_only_pres_wr_diff_var)        
                apply (metis )
               apply(elim conjE disjE)
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                   apply(elim exE, rule_tac x=vl in exI)
        apply (metis (no_types, lifting) Suc_inject lib_c_obs_lib_only_pres_wr_diff_var)
               apply(simp add: globals)
               apply(subgoal_tac "agt ad1 ad2 ps cls")
                apply simp
        using agt_pres_diff_write no_Top_n_def
                  apply (smt Suc_inject) (*too slow*)

          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
              apply(elim exE, rule_tac x=vl in exI)
        apply (metis Suc_inject lib_c_obs_lib_only_pres_wr_diff_var)
               apply(simp add: globals)
               apply(subgoal_tac "agt ad1 ad2 ps cls")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
              apply(elim exE, rule_tac x=vl in exI)
        apply (metis Suc_inject lib_c_obs_lib_only_pres_wr_diff_var)        
               apply (metis )
        using agt_pres_diff_write no_Top_n_def
                apply (smt Suc_inject) (*too slow*)     
                  apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
              apply(elim exE, rule_tac x=vl in exI)
        apply (metis Suc_inject lib_c_obs_lib_only_pres_wr_diff_var)        
               apply (metis )

              apply(simp add: globals dobs_to_def, intro conjI impI allI; elim disjE conjE)
        apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
                  apply (metis assms(2) d_obs_write_diff_var)
         using agt_pres_diff_write no_Top_n_def
       apply (smt Suc_inject)(*too slow*)

                 apply (metis d_obs_write_diff_var)
         apply(subgoal_tac " Ex (lib_d_obs_t cls t ( ad)) \<and> Suc (n_val ps
                         t') \<noteq>  ad")
                 apply (metis d_obs_write_diff_var)
         apply(intro conjI)
       apply (smt Suc_inject agt_pres_diff_write)
       apply blast
                   apply (metis d_obs_write_diff_var)
          apply(subgoal_tac " Ex (lib_d_obs_t cls t (Suc ad)) \<and> Suc (n_val ps
                         t') \<noteq> Suc ad")
                   apply (metis d_obs_write_diff_var)
                  apply(intro conjI)
         apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
         apply blast
         using agt_pres_diff_write no_Top_n_def
                   apply (smt Suc_inject)(*too slow*)
                  apply blast
           apply(subgoal_tac " Ex (lib_d_obs_t cls t (Suc ad)) \<and> Suc (n_val ps
                         t') \<noteq> Suc ad")
                  apply (metis d_obs_write_diff_var)
                 apply blast

          apply(subgoal_tac " Ex (lib_d_obs_t cls t (Suc ad)) \<and> Suc (n_val ps
                         t') \<noteq> Suc ad")
                   apply (metis d_obs_write_diff_var)
                  apply(intro conjI)
         apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
         apply blast
         using agt_pres_diff_write no_Top_n_def
                   apply (smt Suc_inject)(*too slow*)
                  apply blast
           apply(subgoal_tac " Ex (lib_d_obs_t cls t (Suc ad)) \<and> Suc (n_val ps
                         t') \<noteq> Suc ad")
                  apply (metis d_obs_write_diff_var)
         apply blast

       apply (metis lib_covered_write_diff_var_pres)
             apply (metis d_obs_write_diff_var)

       apply (metis Suc_inject wr_preserves_last)
       apply (metis diff_var_write_written_addr)
       apply (metis d_obs_write_diff_var old.nat.inject)
       by (metis d_obs_write_diff_var diff_var_write_written_addr lib_covered_write_diff_var_pres no_Top_n_written_addr)

    next
      case L6
      then show ?thesis           
        using assms
        by(cases "pc ps t"; simp add: lib_pop_def glb_inv_def glb_inv14_def; elim exE conjE; simp)
    qed




lemma pop_inv_gc_pop:
  assumes "wfs ccs"
      and "lib_wfs cls ccs"
      and "pop_inv t' l (pc ps t') cls ccs  ps"
      and "pop_inv t l (pc ps t) cls ccs  ps"
      and "lib_pop t' l ps cls ccs ps' cls' ccs'"
      and "glb_inv ps cls"
      and "t \<noteq> t'"
      and "glb ps cls"
      and "to ps cls"
   shows "pop_inv t l (pc ps' t) cls' ccs'  ps'"
    proof (cases "pc ps t'")
        case L3
      then show ?thesis  
        using assms
        apply(case_tac "\<not> res ps' t'")
          apply(cases "pc ps t"; cases "pc ps' t"; simp ; elim exE conjE)
            apply(intro conjI)
        using cobs_to_CAS_pres apply blast
        using cvd_CAS_R_cvd apply blast
        using failed_CAS_Top_written_addr_post2 apply blast
           apply(intro conjI)
        using cobs_to_CAS_pres apply blast
        
        using failed_cas_dobs_to apply blast
                using cvd_CAS_R_cvd apply blast
      using failed_CASR_pres_d_obs_lib apply blast
      using failed_CASR_pres_d_obs_lib apply blast
        using failed_CAS_Top_written_addr_post2 apply blast        
                apply(intro conjI)

                apply (metis cobs_to_CAS_pres)
        apply (metis failed_cas_dobs_to)
            using cvd_CAS_R_cvd apply blast
      using failed_CASR_pres_d_obs_lib apply blast
      apply (simp add: failed_CAS_preserves_last)
      using failed_CAS_Top_written_addr_post2 apply blast
        apply (metis  failed_CASR_pres_d_obs_lib)
      apply (metis cvd_CAS_R_cvd failed_CASR_pres_d_obs_lib failed_CAS_Top_written_addr_post2)
        (*CAS success case*)
      apply(subgoal_tac "top ps t' \<in> pushed_addr ps") defer
       apply(cases "pc ps t"; cases "pc ps' t"; simp ; elim exE conjE)
      apply(simp add: globals)
      apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
       apply(simp add: globals)
           apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
            apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
            apply(simp add: globals)
      apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
            apply(simp add: globals)
      apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
            apply(simp add: globals)
       apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
      apply(cases "pc ps t"; cases "pc ps' t"; simp ; elim exE conjE)
         apply(intro conjI)
           defer
           apply (meson cvd_CAS_R_cvd)
          apply(intro impI)
          apply(case_tac "ntop ps t' = 0")
      apply(subgoal_tac "written_addr cls' = written_addr cls")
            apply simp
      apply(simp add:written_addr_def)
      using inf_sup_aci(5) insert_Diff success_CAS_Top_written_addr_post apply auto[1]
      using success_CAS_Top_written_addr_post2 apply force
         apply(intro conjI impI)
      defer defer
              apply (metis cvd_CAS_R_success_post cvd_CAS_R_success_read_val)
      apply(simp add: globals)
     apply (metis d_obs_post_CAS_R_diff_var_post subsetD)
      apply(simp add: globals)
     apply (metis d_obs_post_CAS_R_diff_var_post)
          apply(case_tac "ntop ps t' = 0")
      apply(subgoal_tac "written_addr cls' = written_addr cls")
            apply simp
      apply(simp add:written_addr_def)
      using inf_sup_aci(5) insert_Diff success_CAS_Top_written_addr_post apply auto[1]
      using success_CAS_Top_written_addr_post2 apply force 
          apply(intro conjI impI)
      defer defer
      apply (metis cvd_CAS_R_cvd)
      apply(simp add: globals)
          apply (metis d_obs_post_CAS_R_diff_var_post subset_iff)
        apply(simp add: globals)
        apply (metis succ_CAS_preserves_last)
          apply(case_tac "ntop ps t' = 0")
      apply(subgoal_tac "written_addr cls' = written_addr cls")
            apply simp
      apply(simp add:written_addr_def)
      using inf_sup_aci(5) insert_Diff success_CAS_Top_written_addr_post apply auto[1]
      using success_CAS_Top_written_addr_post2 apply force 
      apply(subgoal_tac "Ex (lib_d_obs_t cls t
              (Suc (prog_state.top ps t)))")
      apply(subgoal_tac "Suc (prog_state.top ps t) \<noteq> Top")
              apply (meson d_obs_post_CAS_R_diff_var_post)
      apply(simp add: globals)
      apply metis
      apply auto[1]
          apply(intro conjI impI)
      apply (meson cvd_CAS_R_cvd)
      apply(subgoal_tac "Ex (lib_d_obs_t cls t
              ((prog_state.top ps t)))")
             apply(subgoal_tac "(prog_state.top ps t) \<noteq> Top")
      apply (meson d_obs_post_CAS_R_diff_var_post)
      apply(simp add: globals)
      apply (metis subset_iff)
      apply blast
          apply(case_tac "ntop ps t' = 0")
      apply(subgoal_tac "written_addr cls' = written_addr cls")
            apply simp
      apply(simp add:written_addr_def)
      using inf_sup_aci(5) insert_Diff success_CAS_Top_written_addr_post apply auto[1]
      using success_CAS_Top_written_addr_post2 apply force 
(***cobs_to begin***)
                 apply(simp add: cobs_to_def)
                 apply(intro allI impI conjI, elim disjE conjE)
                 apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
          apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_pres)
      using agt_pop_successful_cas_before3
               apply (metis assms(8) cvd_CAS_R_success_read_val neq0_conv)
              apply(simp add: globals)
      apply (metis gr_zeroI subsetD)
          apply(simp add: globals)

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
                       apply(subgoal_tac "x = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
                   apply (metis cvd_CAS_R_success_read_val)
                  apply auto[1]
                 apply (metis agt_pop_successful_cas_before3 assms(8) cvd_CAS_R_success_read_val)
                   apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                  apply(elim exE, rule_tac x=vl in exI)
          apply(subgoal_tac "ad1 \<noteq> ntop ps t'  \<and> Top \<noteq> ad2")
          using successful_CAS_lib_c_obs_lib_diff_value_pres[where  ls'=cls' and ls=cls and cs=ccs and cs'=ccs'
and x=Top and t=t' and t'=t and l="top ps t'" and k="ntop ps t'"]
                   apply simp
          apply(simp add: globals)
           apply (meson subset_iff)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                  apply blast

          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
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
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
                apply (metis cvd_CAS_R_success_read_val)  
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
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
                  apply (metis cvd_CAS_R_success_read_val)  
                 apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
               apply(simp add: globals)
     apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
                 apply (metis cvd_CAS_R_success_read_val)  
          
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
                       apply(subgoal_tac "x = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
                  apply (metis cvd_CAS_R_success_read_val)
          apply auto[1]
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
                apply (metis cvd_CAS_R_success_read_val)  
               apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
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
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
               apply (metis cvd_CAS_R_success_read_val)  
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
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
                  apply (metis cvd_CAS_R_success_read_val)  
                 apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
          apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_pres)
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
                 apply (metis cvd_CAS_R_success_read_val)  
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
                       apply(subgoal_tac "x = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
                   apply (metis cvd_CAS_R_success_read_val)
          apply auto[1]
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
                apply (metis cvd_CAS_R_success_read_val)  
               apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
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
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)                     apply(case_tac "ad1 = ntop ps t'", simp)
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
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)            apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
               apply(simp add: globals)
     apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)            apply(simp add: globals)
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
                       apply(subgoal_tac "x = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
                  apply (metis cvd_CAS_R_success_read_val)
          apply auto[1]
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)                     apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)                     apply simp
                   apply(subgoal_tac "agt ad1 (ntop ps t') ps cls")       
                    apply(subgoal_tac "agt  (ntop ps t') ad1 ps cls")
          apply (meson agt_def agt_order to_def to_p4_def)
           apply(subgoal_tac "agt  (top ps t') ad1 ps cls")
          using nothing_between_a_nxt lastNxtVal_def lastVal_def
          apply (metis add.commute assms(8) plus_1_eq_Suc)
          apply (smt Null_def TopLV_agt_others assms(8) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr_zero)
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)                     apply(case_tac "ad1 = ntop ps t'", simp)
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
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)            apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
          apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_pres)
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)            apply(simp add: globals)
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
                       apply(subgoal_tac "x = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
                   apply (metis cvd_CAS_R_success_read_val)
          apply auto[1]
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)                     apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
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
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)  
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
      apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
         apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>lib(ad2) =\<^sub>t vl \<rparr> cls")
            apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_pres)
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)            apply(simp add: globals)
    apply (metis gr_zeroI subsetD)
     apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
               apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
    apply(simp add: globals)
          apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)  
          apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)

                   apply(case_tac "ad1 = ntop ps t'", simp)
          apply(subgoal_tac "agt (ntop ps t') ad2 ps cls")
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>libad2 =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>lib(ad2) =\<^sub>t vl \<rparr> cls)")

                   apply(subgoal_tac "\<exists>vl. [lib(ad2) =\<^sub>t' vl] cls")
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
                       apply(subgoal_tac "x = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
                  apply (metis cvd_CAS_R_success_read_val)
          apply auto[1]
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)                     apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>lib(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)                     apply simp
                   apply(subgoal_tac "agt ad1 (ntop ps t') ps cls")       
                    apply(subgoal_tac "agt  (ntop ps t') ad1 ps cls")
          apply (meson agt_def agt_order to_def to_p4_def)
           apply(subgoal_tac "agt  (top ps t') ad1 ps cls")
          using nothing_between_a_nxt lastNxtVal_def lastVal_def
          apply (metis add.commute assms(8) plus_1_eq_Suc)
          apply (smt Null_def TopLV_agt_others assms(8) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr_zero)
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
              apply (metis cvd_CAS_R_success_read_val)  
             apply(case_tac "ad1 = ntop ps t'", simp)
                     apply(subgoal_tac "(\<exists>vl. [libTop = (ntop ps t')]\<lparr>lib(ad2) =\<^sub>t' vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (ntop ps t')]\<lparr>lib(ad2) =\<^sub>t vl \<rparr> cls)")
                   apply(subgoal_tac "\<exists>vl. [lib(ad2) =\<^sub>t' vl] cls")
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
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>lib(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
       apply blast
    apply(elim disjE conjE)
     apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
               apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
        apply(simp add: globals)
          apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)            apply(simp add: globals)
                     apply (metis gr_zeroI subsetD)
                apply(subgoal_tac "ad1\<notin>{Top, Null} \<and> ad2\<notin>{Top, Null}")
   apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
               apply(simp add: globals)
     apply (metis  successful_CAS_lib_c_obs_lib_diff_value_pres)
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)            apply(simp add: globals)
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
                       apply(subgoal_tac "x = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
                  apply (metis cvd_CAS_R_success_read_val)
          apply auto[1]
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)                     apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)                     apply simp
                   apply(subgoal_tac "agt ad1 (ntop ps t') ps cls")       
                    apply(subgoal_tac "agt  (ntop ps t') ad1 ps cls")
          apply (meson agt_def agt_order to_def to_p4_def)
           apply(subgoal_tac "agt  (top ps t') ad1 ps cls")
          using nothing_between_a_nxt lastNxtVal_def lastVal_def
          apply (metis add.commute assms(8) plus_1_eq_Suc)
          apply (smt Null_def TopLV_agt_others assms(8) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr_zero)
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)                     apply(case_tac "ad1 = ntop ps t'", simp)
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
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
          apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)  
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
         apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
        apply blast
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
                       apply(subgoal_tac "x = top ps t'")
          apply(simp add:  to_def to_p2_def )
                         apply (simp add: lastTop_def)
                        apply (metis lib_cvd_exist_last_write)
                  apply (metis cvd_CAS_R_success_read_val)
          apply auto[1]
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
              apply (metis cvd_CAS_R_success_read_val)  
             apply(case_tac "ad2 \<noteq> ntop ps t'")
          apply(subgoal_tac " \<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
                                      apply(elim exE, rule_tac x=vl in exI)
          apply(simp add: globals)
    apply (smt subsetD successful_CAS_lib_c_obs_lib_diff_value_pres)
                    apply(subgoal_tac "agt ad1 ad2 ps cls")
                     apply blast
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)                     apply simp
                   apply(subgoal_tac "agt ad1 (ntop ps t') ps cls")       
                    apply(subgoal_tac "agt  (ntop ps t') ad1 ps cls")
          apply (meson agt_def agt_order to_def to_p4_def)
           apply(subgoal_tac "agt  (top ps t') ad1 ps cls")
          using nothing_between_a_nxt lastNxtVal_def lastVal_def
          apply (metis add.commute assms(8) plus_1_eq_Suc)
          apply (smt Null_def TopLV_agt_others assms(8) cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr_zero)
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
                      apply simp
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)  
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
          apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
          apply metis  
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)  


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
  
        apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
          
          apply (metis assms(6) assms(8) assms(9))  
                apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)  
          
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
 apply(intro conjI)
       apply(simp add: globals)
  apply (metis subset_iff)
         apply(simp add: globals)
         apply metis
        apply blast
       apply blast
    apply(subgoal_tac "ad \<noteq> Top \<and> Suc ad \<noteq> Top \<and> (\<exists>vl. [libad =\<^sub>t vl] cls) \<and>
       (\<exists>vl. [libSuc ad =\<^sub>t vl] cls)")
             apply(elim conjE exE, intro conjI)
  apply (meson d_obs_post_CAS_R_diff_var_post)
  apply (meson d_obs_post_CAS_R_diff_var_post)
 apply(intro conjI)
       apply(simp add: globals)
  apply (metis subset_iff)
         apply(simp add: globals)
        apply metis
  apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
  
  apply blast
       apply(subgoal_tac "top ps t\<in>pushed_addr ps'")

        apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
          apply (metis assms(8) not_gr_zero)
         apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)  


  apply(simp add: agt_def clss_def nxt_rel_def trancl_def)
  using converse_tranclpE   
       apply smt

  apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
  
  apply blast
       apply(subgoal_tac "top ps t\<in>pushed_addr ps'")
      apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
          apply (metis assms(8) not_gr_zero)
         apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)  
  apply(simp add: agt_def clss_def nxt_rel_def trancl_def)
  using converse_tranclpE   
      apply smt
  apply(subgoal_tac "(\<exists>vl. [libad =\<^sub>t vl] cls) \<and>
            (\<exists>vl. [libSuc ad =\<^sub>t vl] cls)")
      apply(elim conjE)
  apply(simp add: globals)
  apply (metis d_obs_post_CAS_R_diff_var_post subset_iff)
     apply blast
    apply(subgoal_tac "top ps t\<in>pushed_addr ps'")
  apply(subgoal_tac "agt (prog_state.top ps t) ad ps cls")
      apply(subgoal_tac "(\<exists>vl. [libad =\<^sub>t vl] cls) \<and>
            (\<exists>vl. [libSuc ad =\<^sub>t vl] cls)")
      apply(elim conjE)
  apply(simp add: globals)
  apply (metis d_obs_post_CAS_R_diff_var_post subset_iff)
     apply blast
        apply(simp add: globals)
      apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
          
          apply (metis assms(6) assms(8) assms(9)) 
          apply (metis cvd_CAS_R_success_read_val)  
  apply(simp add: agt_def clss_def nxt_rel_def trancl_def)
  using converse_tranclpE   
    apply smt

      apply(subgoal_tac "(\<exists>vl. [libad =\<^sub>t vl] cls) \<and>
            (\<exists>vl. [libSuc ad =\<^sub>t vl] cls)")
      apply(elim conjE)
  apply(simp add: globals)
  apply (metis d_obs_post_CAS_R_diff_var_post subset_iff)
     apply blast
(***end of dobs_to***)
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
      apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
          
          apply (metis assms(6) assms(8) assms(9))         apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)  
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
  
      apply(subgoal_tac "x = top ps t' \<and> prog_state.top ps t' \<noteq> ntop ps t'", simp)
          using agt_pop_successful_cas_before3 [where cls=cls and ccs=ccs and cls'=cls' and ps=ps
              and ps'=ps' and u="top ps t'" and t=t' and ccs'=ccs' and u'="ntop ps t'"]
          
          apply (metis assms(6) assms(8) assms(9))
          apply(simp add: globals)
          apply (metis cvd_CAS_R_success_read_val)  

          
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
 apply(intro conjI)
       apply(simp add: globals)
  apply (metis subset_iff)
         apply(simp add: globals)
         apply metis
        apply blast
       apply blast
(***end of dobs_to***)
    done
    next
    case L1
      then show ?thesis                   
          using assms
          apply(cases "pc ps t"; cases "pc ps' t"; simp ; elim exE conjE; simp)
                              apply(intro conjI allI impI)
          using cobs_to_read_pres apply blast
          using lib_read_cvd_pres apply blast
     apply(simp add: written_addr_def)
                    using rd_A_preserves_values rd_A_preserves_writes_on apply auto[1]
                                        apply(intro conjI allI impI)
                    using cobs_to_read_pres apply blast
                          apply auto[1]
                           apply auto[1]
                            using lib_read_cvd_pres apply blast
                                                apply auto[1]
                            apply auto[1]
                            
                            apply auto[1]
                            
                            apply (metis PC.distinct(3) fun_upd_other neq0_conv)
                            apply auto[1]
                            apply auto[1]
                            apply auto[1]
                                                apply auto[1]
                            apply(intro conjI)
                            
                            using cobs_to_read_pres apply blast
                            apply(simp add: dobs_to_def)
                                                apply (metis agt_pushed_same2rd_before_state lib_d_obs_pres_read)
                            
                            using lib_read_cvd_pres apply blast
                            
                            using lib_d_obs_pres_read apply blast
                            
                            using lib_d_obs_pres_read apply blast
            apply(simp add: written_addr_def)
                  apply (simp add: rd_A_preserves_values read_pres_writes_on_diff_var)
                  apply (metis PC.distinct(11) fun_upd_other neq0_conv)
                                     
                            apply (metis PC.distinct(13) fun_upd_other less_antisym zero_less_Suc)
                          apply auto[1]
                                                apply auto[1]
                                                               
                                               apply (metis PC.distinct(3) fun_upd_other neq0_conv)
                            apply (metis PC.distinct(11) fun_upd_other neq0_conv)
                            apply(intro conjI)
                            using cobs_to_read_pres apply blast
                                              apply(simp add: dobs_to_def)
                                                apply (metis agt_pushed_same2rd_before_state lib_d_obs_pres_read)
                            using lib_read_cvd_pres apply blast
                            using lib_d_obs_pres_read apply blast
                                                        apply (simp add: read_pres_last_val)
               apply(simp add: written_addr_def)
                  apply (simp add: rd_A_preserves_values read_pres_writes_on_diff_var)                                                     
                            
                            using lib_d_obs_pres_read apply blast
                            apply(simp add: written_addr_def)
               apply (metis PC.distinct(19) fun_upd_other neq0_conv)
               apply (metis PC.distinct(21) fun_upd_apply neq0_conv)
               apply (metis PC.distinct(23) fun_upd_other neq0_conv)
               apply auto[1]
               apply auto[1]
               apply (metis PC.distinct(19) fun_upd_other neq0_conv)
                apply(simp add: written_addr_def)
              apply (metis lib_d_obs_pres_read lib_read_cvd_pres rd_A_preserves_values read_pres_writes_on_diff_var)
              using fun_upd_other apply auto[1]
              apply auto[1]
              apply auto[1]
              apply auto[1]
              apply (metis PC.distinct(21) fun_upd_other neq0_conv)
              apply auto[1]
              apply auto[1]
              using fun_upd_apply neq0_conv apply auto[1]
              apply (metis PC.distinct(23) fun_upd_other neq0_conv)
              by auto
        next
      case L2
      then show ?thesis 
          using assms
          apply(cases "pc ps t"; cases "pc ps' t"; simp ; elim exE conjE; simp)
                    apply(intro conjI)
          using cobs_to_read_pres apply blast
          using lib_read_cvd_pres apply blast
                    apply(subgoal_tac "written_addr cls' = written_addr cls")
              apply blast
          apply(simp add: written_addr_def)
          apply (metis (no_types, lifting) image_cong lib_read_writes_on_diff_var_pres_backwards read_pres_value)
            apply(intro conjI)
          using cobs_to_read_pres apply blast
          apply(simp add: dobs_to_def)
                apply (metis agt_pushed_same2rd_relax_before_state lib_d_obs_pres_read)
          using lib_read_cvd_pres apply blast
          
          using lib_d_obs_pres_read apply blast
          using lib_d_obs_pres_read apply blast
          apply(simp add: written_addr_def)
            apply (metis (no_types, lifting) image_cong lib_read_writes_on_diff_var_pres_backwards read_pres_value)
            apply(intro conjI)
          using cobs_to_read_pres apply blast
          apply(simp add: dobs_to_def)
                apply (metis agt_pushed_same2rd_relax_before_state lib_d_obs_pres_read)
          using lib_read_cvd_pres apply blast
          
          using lib_d_obs_pres_read apply blast
          
          using rd_preserves_last apply auto[1]
          apply(simp add: written_addr_def)
            apply (metis (no_types, lifting) image_cong lib_read_writes_on_diff_var_pres_backwards read_pres_value)
          using lib_d_obs_pres_read apply blast
          apply(simp add: written_addr_def)
          by (smt image_iff lib_d_obs_pres_read lib_read_cvd_pres read_pres_value read_pres_writes_on_diff_var)

    next
      case L4
      then show ?thesis using assms
        apply(cases "pc ps t"; simp add: glb_inv15_def glb_inv_def glb_inv14_def; elim exE conjE; simp)
        done
    next
      case L5
      then show ?thesis
        using assms
        by simp
    next
      case L6
      then show ?thesis
        using assms
        by simp
    qed




end
