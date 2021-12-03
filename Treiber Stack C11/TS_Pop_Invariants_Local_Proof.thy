theory TS_Pop_Invariants_Local_Proof
imports  TS_Proof_Rules
begin

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
  done


lemma pop_globals_inv:
  assumes "wfs ccs"
      and "lib_wfs cls ccs"
      and "lib_pop t v ps cls ccs ps' cls' ccs'"
      and "pop_inv t l (pc ps t) cls ccs  ps"
      and "glb_inv ps cls"
      and "glb ps cls"
    shows "glb_inv ps' cls'"
  apply(simp add: glb_inv_def)
proof (intro conjI)
  show "glb_inv9 ps'"
        using assms 
  apply(simp add: glb_inv_def)
  apply(elim conjE)
    apply(simp add: lib_pop_def pop_inv_def glb_inv9_def; case_tac "pc ps t"; simp_all; elim exE conjE)
        apply(simp add: globals glb_inv16_def)
        apply(intro allI impI) 
        apply(case_tac "t \<noteq> ta") 
         apply auto[1]
        apply(subgoal_tac "ntop ps' ta\<in>addr_val ps")
         apply blast
        apply(subgoal_tac "ntop ps' ta \<in> lib_value cls ` lib_writes_on cls (Suc (top ps t))")
         apply (metis gr_implies_not_zero insertE subsetD)
        apply simp
    apply(simp add: lib_read_step_def lib_read_def all_updates_l lib_visible_writes_def)
    apply blast
        done
    next 
  show "glb_inv1 ps' cls'"
    using assms 
  apply(simp add: glb_inv_def)
  apply(elim conjE)
  apply(simp add: lib_pop_def pop_inv_def glb_inv1_def; case_tac "pc ps t"; simp_all; elim exE conjE)
  apply(simp_all add: globals) 
  apply (metis lib_read_writes_on_diff_var_pres_backwards read_pres_value)
  apply (metis lib_read_writes_on_diff_var_pres_backwards read_pres_value)
  apply(simp add: globals lib_CAS_Rel_step_def, elim exE conjE)
  apply(case_tac "lib_value cls (a, b) = prog_state.top ps t", simp_all) 
  apply(simp add: lib_update_r_def all_updates_l lib_value_def lib_writes_on_def) 
  apply(intro allI conjI impI)
  apply blast 
  apply(simp add: lib_read_def all_updates_l lib_syncing_def)
  apply(intro allI impI conjI) 
  apply(simp add: lib_value_def lib_writes_on_def)
  by blast
next  
  show "glb_inv3 ps' cls'"
        using assms 
  apply(simp add: glb_inv_def)
  apply(elim conjE)
    apply(simp add: lib_pop_def pop_inv_def; case_tac "pc ps t"; simp_all; elim exE conjE)
           apply(simp add: globals) 
        apply (metis (no_types, lifting) lib_lastWr_def lib_last_in_visible_writes lib_visible_writes_def mem_Collect_eq read_pres_value read_pres_writes_on_diff_var)
         apply(simp_all add: globals)
        apply (simp add: rd_preserves_last)
        by (smt Diff_iff cvd_CAS_R_success_d_obs_post cvd_CAS_R_success_read_val empty_iff failed_CAS_preserves_last insert_iff lib_cvd_exist_last_write lib_d_obs_def lib_d_obs_t_def)
next 
  show "glb_inv4 ps' cls'"
        using assms 
  apply(simp add: glb_inv_def)
        apply(elim conjE) 
        apply (simp add: lib_pop_def pop_inv_def glb_inv4_def; case_tac "pc ps t"; simp_all; elim exE conjE)
          apply(simp add: globals)  
          apply (simp add: rd_A_preserves_last)
          using rd_preserves_last apply auto[1]
          by (metis succ_CAS_preserves_last)
    next 
  show "glb_inv5 ps' cls'"
        using assms 
  apply(simp add: glb_inv_def) 
  apply(elim conjE)
    apply(simp add: lib_pop_def pop_inv_def glb_inv5_def; case_tac "pc ps t"; simp_all; elim exE conjE)
        apply (metis Diff_subset le_less psubsetI psubset_subset_trans)  
        done
  show "glb_inv6 ps' cls'"
        using assms 
  apply(simp add: glb_inv_def)
  apply(elim conjE)
    apply(simp add: lib_pop_def pop_inv_def glb_inv6_def; case_tac "pc ps t"; simp_all; elim exE conjE)
        apply(simp add: globals)
        using rd_A_preserves_last apply auto[1]
        using rd_preserves_last apply auto[1]
        by (metis Diff_iff Suc_eq_plus1 glb_inv11_def succ_CAS_preserves_last)
  show "glb_inv7 ps' cls'"
        using assms 
  apply(simp add: glb_inv_def) 
    apply(simp add: lib_pop_def pop_inv_def glb_inv7_def; case_tac "pc ps t"; simp_all; elim exE conjE)
      apply(simp add: globals)
          apply(intro allI impI conjI) 
      apply(subgoal_tac "lib_writes_on cls' Top = lib_writes_on cls Top")
  apply(subgoal_tac "lib_releasing cls' (a, b) = lib_releasing cls (a, b)") 
        apply (metis (full_types)  assms(1) assms(2) read_pres_value)
       apply(simp add: lib_read_step_def lib_read_def all_updates_l, elim conjE exE)
       apply(simp add:lib_releasing_def) 
          apply (metis (full_types) read_pres_writes_on_diff_var)
         apply(simp add: lib_read_step_def lib_read_def all_updates_l, elim conjE exE)
         apply (case_tac "lib_syncing cls (a, b) False", simp_all)
        apply (simp add: lib_syncing_def)
         apply(intro allI conjI impI)  
                 apply(simp add:lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def lib_read_step_def lib_read_def all_updates_l lib_writes_on_def lib_releasing_def)  
      apply blast   
         apply(simp add: lib_CAS_Rel_step_def lib_read_def all_updates_l, elim conjE exE)
  apply(case_tac "lib_value cls (a, b) = prog_state.top ps t", simp_all)
         apply(simp add:lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def lib_read_def all_updates_l lib_writes_on_def lib_releasing_def)  
       apply(case_tac "(a, b) \<in> lib_writes_on cls Top")
       apply(simp add:lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def lib_update_r_def all_updates_l lib_writes_on_def lib_releasing_def)
        apply(simp add:lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def lib_update_r_def all_updates_l lib_writes_on_def lib_releasing_def)    
        by(simp add:lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def lib_read_step_def lib_read_def all_updates_l lib_writes_on_def lib_releasing_def)  
      next
  show "glb_inv8 ps' cls'"
        using assms 
  apply(simp add: glb_inv_def)
    apply(simp add: lib_pop_def pop_inv_def glb_inv8_def; case_tac "pc ps t"; simp_all; elim exE conjE; simp add: globals)
        using rd_A_preserves_last apply auto[1]
        using rd_preserves_last apply auto[1]       
        by (smt Diff_iff cvd_CAS_R_success_read_val empty_iff insert_iff lib_cvd_exist_last_write succ_CAS_preserves_last)
    next 
  show "glb_inv10 ps' cls'"
        using assms 
  apply(simp add: glb_inv_def)
  apply(elim conjE)
    apply(simp add: lib_pop_def pop_inv_def glb_inv10_def; case_tac "pc ps t"; simp_all; elim exE conjE)
  apply(simp add: globals) 
        using rd_A_preserves_last apply auto[1]
         apply (simp add: lastTop_def rd_preserves_last)
        apply(intro conjI impI allI, simp add: globals)
        apply(case_tac "\<not>res ps' t", simp_all)

        using failed_CAS_preserves_last apply metis
        apply(elim conjE)
        apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = ntop ps t")
         apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write succ_CAS_preserves_last)
        apply(subgoal_tac "[lib Top =\<^sub>t (ntop ps t)] cls'")
        apply(simp add: lib_d_obs_def lib_d_obs_t_def)
              using cvd_CAS_R_success_d_obs_post by metis
    next 
      show "glb_inv11 ps' cls'"
        using assms 
        apply(simp add: glb_inv_def)
        apply(elim conjE)
    apply(simp add: lib_pop_def pop_inv_def glb_inv11_def; case_tac "pc ps t"; simp_all; elim exE conjE)  
  apply(simp add: globals) 
        by (metis Diff_iff)
  show "glb_inv12 ps' cls'"
        using assms 
  apply(simp add: glb_inv_def)
  apply(elim conjE)
    apply(simp add: lib_pop_def pop_inv_def glb_inv12_def; case_tac "pc ps t"; simp_all; elim exE conjE)
  apply(simp add: globals pop_inv_def)
  apply(case_tac "pc ps t"; simp add: lib_pop_def globals pop_inv_def)
        by (metis finite_Diff)
    next 
      show "glb_inv13 ps' cls'"
        using assms 
  apply(simp add: glb_inv_def)
  apply(elim conjE)
      apply(simp add: lib_pop_def pop_inv_def glb_inv12_def; case_tac "pc ps t"; simp_all; elim exE conjE)
  apply(simp add: globals pop_inv_def)
          apply(case_tac "pc ps t"; simp add: lib_pop_def globals pop_inv_def)
        apply (metis lib_read_pres_last rd_A_preserves_values rd_A_preserves_writes_on written_addr_def)
         apply(simp add: globals pop_inv_def)
          apply(simp add: written_addr_def)
       apply(intro allI impI conjI)
         apply (metis (no_types, lifting) image_cong lib_read_writes_on_diff_var_pres_backwards rd_preserves_last read_pres_value)
         apply (metis image_cong lib_read_writes_on_diff_var_pres_backwards read_pres_value)
         apply(simp add: globals pop_inv_def)
  apply(case_tac "res ps' t", simp_all)
     apply(intro allI impI conjI)
    apply(simp add: written_addr_def, elim conjE)
  apply(case_tac " ad \<in> lib_value cls `
             lib_writes_on cls Top")
           apply (metis succ_CAS_preserves_last)
          apply(subgoal_tac "ntop ps t = ad", simp)
           apply(case_tac "ntop ps t = Null")
            apply auto[1]
           apply(intro disjI2)
           apply(subgoal_tac "x = top ps t", simp)
            apply(subgoal_tac "top ps t\<in>pushed_addr ps \<and> top ps t \<noteq> Null")
             apply(subgoal_tac "Suc ad \<noteq> Top")
              apply(subgoal_tac "lib_value cls' (lib_lastWr cls' (Suc ad)) = lib_value cls (lib_lastWr cls (Suc ad))", simp)
        apply (metis)
          apply (metis succ_CAS_preserves_last)
            
        apply metis
        apply (smt lib_cvd_exist_last_write)
           apply (metis cvd_CAS_R_success_read_val)
  using  CAS_Top_written_addr_post2[where b = "n_val ps t" and cls' = cls' and cls=cls
          and a = "ntop ps t" and t=t]
  apply (smt CAS_Top_written_addr_post2 Diff_empty Diff_insert0 Null_def insert_Diff insert_iff nat_less_le)
          apply (metis CAS_Top_written_addr_post Diff_iff Null_def singletonI written_addr_def)
       apply(intro allI impI conjI)
   apply(simp add: written_addr_def, elim conjE)
  apply (metis failed_CAS_Top_written_addr_post succ_CAS_preserves_last)
   apply(simp add: written_addr_def, elim conjE)
  by (metis (full_types) failed_CAS_Top_written_addr_post)
    next 
      show "glb_inv14 ps' cls'"
        using assms 
        apply(simp add: glb_inv_def)
        apply(elim conjE)
    apply(simp add: lib_pop_def pop_inv_def glb_inv11_def; case_tac "pc ps t"; simp_all; elim exE conjE)  
  apply(simp add: globals) 
         apply(intro allI impI conjI)
          apply(simp add: written_addr_def, elim conjE)
          apply (metis lib_read_writes_on_diff_var_pres_backwards rd_A_preserves_last rd_A_preserves_values)
  apply(simp add: globals) 
         apply(intro allI impI conjI)
         apply(simp add: written_addr_def, elim conjE)
        apply (metis (no_types, lifting) image_cong lib_read_writes_on_diff_var_pres_backwards rd_preserves_last read_pres_value)
        apply(simp add: globals) 
        apply(case_tac "\<not>res ps' t", simp_all)
           apply(intro allI impI conjI)
         apply(simp add: written_addr_def, elim conjE)
        apply (metis failed_CAS_Top_written_addr_post succ_CAS_preserves_last)
           apply(intro allI impI conjI)
        apply(simp add: written_addr_def, elim conjE)
        apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' Top = lib_value cls ` lib_writes_on cls Top \<union> {ntop ps t}", simp_all)
        apply (smt cvd_CAS_R_success_read_val lib_cvd_exist_last_write succ_CAS_preserves_last)  
        using success_CAS_Top_written_addr_post   
        by (metis Un_commute insert_is_Un)
    next show "glb_inv15 ps'" 
    using assms
  apply(simp add: glb_inv_def )
  apply(elim conjE)
     apply (simp add: lib_pop_def)
   apply(case_tac "pc ps t", simp_all)
         apply(simp add: glb_inv15_def)
    apply(simp add: glb_inv15_def)
     apply (simp add: glb_inv15_def)
    done

next
  show "glb_inv16 ps' cls'" 
    using assms
  apply(simp add:  globals glb_inv16_def)
      apply (simp add: lib_pop_def)
    apply(elim conjE)
   apply(case_tac "pc ps t", simp_all)
    apply(intro conjI impI allI)
      apply (metis rd_A_preserves_values rd_A_preserves_writes_on written_addr_def)
     apply(intro conjI impI allI)
    apply(subgoal_tac "written_addr cls' = written_addr cls \<and>  lib_value cls' ` lib_writes_on cls' (Suc ad) = lib_value cls ` lib_writes_on cls (Suc ad)", elim conjE, simp)
     apply(intro conjI impI allI)
      apply(simp add: written_addr_def)
    apply (metis image_cong lib_read_writes_on_diff_var_pres_backwards lib_value_read_pres)
    apply (metis image_cong lib_read_writes_on_diff_var_pres_backwards read_pres_value)
    apply(case_tac "\<not>res ps' t", simp_all)
  apply (smt failed_CAS_Rel_preserves_writes_on_diff_var failed_CAS_Top_written_addr_post2 image_subset_iff write_value_CAS_R_diff_var)
    apply(intro allI impI, elim conjE)
    apply(case_tac "ntop ps t = 0")
     apply(subgoal_tac "written_addr cls' = written_addr cls", simp)
    apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' (Suc ad) =
          lib_value cls ` lib_writes_on cls (Suc ad)", simp)
    apply(subgoal_tac "Suc ad \<noteq> Top", simp)

    using CAS_Rel_preserves_writes_on_diff_var write_value_CAS_R_diff_var apply auto[1]
      apply auto[1]
     apply(simp add: written_addr_def)
    apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' Top = 
lib_value cls ` lib_writes_on cls Top \<union> {ntop ps t}")
    apply simp
     apply (simp add: success_CAS_Top_written_addr_post)
    apply(subgoal_tac "written_addr cls' = written_addr cls \<union> {ntop ps t}", simp)
     apply(elim disjE)
    apply(subgoal_tac "top ps t \<in> pushed_addr ps")
      apply(simp add: pop_inv_def; elim conjE exE)
     apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' (Suc ad) =
          lib_value cls ` lib_writes_on cls (Suc ad)", simp)
  apply metis
  
    apply (metis (no_types, lifting) CAS_Rel_preserves_value_diff_var CAS_Rel_preserves_writes_on_diff_var image_cong)
    apply(simp add: pop_inv_def, elim conjE)
    apply (metis (no_types, lifting) cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
        apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' (Suc ad) =
          lib_value cls ` lib_writes_on cls (Suc ad)", simp)
     apply(subgoal_tac "Suc ad \<noteq> Top", simp)
   using CAS_Rel_preserves_writes_on_diff_var write_value_CAS_R_diff_var apply auto[1]
    apply auto[1]
   using success_CAS_Top_written_addr_post2 by auto
qed



lemma cobs_to_failed_cas_pres:
  assumes "wfs ccs"
      and "lib_wfs cls ccs"
      and "cobs_to t ps cls ccs"
      and "cls ccs CAS\<^sup>R[lib(x), False, a, b]\<^sub>t' cls' ccs' "
      and "pushed_addr ps' = pushed_addr ps"
    shows "cobs_to t ps' cls' ccs'"
  using assms
  apply(simp add: cobs_to_def)
  apply safe
     apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
      apply(elim exE conjE)
      apply(rule_tac x=vl in exI)
  using failed_CASR_pres_c_obs_lib_only apply blast
  apply(subgoal_tac "agt ad1 ad2 ps' cls' = agt ad1 ad2 ps cls")
      apply simp
     apply(simp add: agt_def clss_def nxt_rel_def)
  apply(subgoal_tac "{(a, lib_value cls' (lib_lastWr cls' (Suc a))) |a.
           a \<in> pushed_addr ps} = {(a, lib_value cls (lib_lastWr cls (Suc a))) |a.
           a \<in> pushed_addr ps}")
      apply simp
     apply(subgoal_tac "\<forall> a . a\<in>pushed_addr ps \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc a)) = lib_value cls (lib_lastWr cls (Suc a))")
      apply auto[1]
     apply safe
  apply (simp add: failed_CAS_preserves_last)
     apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
      apply(elim exE conjE)
     apply(rule_tac x=vl in exI)
  using failed_CASR_pres_c_obs_lib_only apply blast
  apply(subgoal_tac "agt ad1 ad2 ps' cls' = agt ad1 ad2 ps cls")
      apply simp
     apply(simp add: agt_def clss_def nxt_rel_def)
  apply(subgoal_tac "{(a, lib_value cls' (lib_lastWr cls' (Suc a))) |a.
           a \<in> pushed_addr ps} = {(a, lib_value cls (lib_lastWr cls (Suc a))) |a.
           a \<in> pushed_addr ps}")
      apply simp
     apply(subgoal_tac "\<forall> a . a\<in>pushed_addr ps \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc a)) = lib_value cls (lib_lastWr cls (Suc a))")
     apply auto[1]
  apply (simp add: failed_CAS_preserves_last)
  using failed_CASR_pres_c_obs_lib_only apply blast
  using failed_CASR_pres_c_obs_lib_only by blast




lemma pop_inv:
  assumes "wfs ccs"
      and "lib_wfs cls ccs"
      and "lib_pop t v ps cls ccs ps' cls' ccs'"
      and "pop_inv t l (pc ps t) cls ccs  ps"
      and "glb_inv ps cls"
    shows "pop_inv t l (pc ps' t) cls' ccs'  ps'"
  proof(cases "pc ps t")
    case L1
    then show ?thesis
      using assms
      apply(case_tac "pc ps' t"; simp)
      apply(simp add: lib_pop_def pop_inv_def; elim exE conjE)
           apply(intro conjI)
             apply(simp add: cobs_to_def)
      apply (metis agt_pushed_same2rd_before_state lib_c_obs_lib_only_pres_read_var)
      using lib_read_cvd_pres apply blast
      apply auto[1]
      apply(simp add: lib_pop_def pop_inv_def; elim exE conjE; intro conjI)
              apply(simp add: cobs_to_def)
      apply (metis agt_pushed_same2rd_before_state lib_c_obs_lib_only_pres_read_var)
               apply(simp add: dobs_to_def)

               apply(intro allI impI)
               apply(elim disjE conjE)
                apply(subgoal_tac "agt (prog_state.top ps' t) ad ps cls")
                 apply(case_tac "ad = top ps' t")
      apply(simp add:  agt_def to_p4_def)
      apply (meson cobs_to_def lib_read_transfer)
                 apply(subgoal_tac "top ps' t\<in>pushed_addr ps")
                  apply(subgoal_tac "(\<exists>vl. [libTop = (top ps' t)]\<lparr>lib(ad) =\<^sub>t vl \<rparr> cls)
\<and> (\<exists>vl. [libTop = (top ps' t)]\<lparr>libSuc(ad) =\<^sub>t vl \<rparr> cls)")
      apply(elim conjE, intro conjI)
      using lib_read_transfer apply blast
      using lib_read_transfer apply blast
                  apply (simp add: cobs_to_def)
  apply(simp add: agt_def clss_def nxt_rel_def trancl_def)
  using converse_tranclpE 
      apply (metis (no_types, lifting))
      using agt_pushed_same2rd_before_state apply blast

               apply(subgoal_tac "(\<exists>vl. [libTop = (ad)]\<lparr>lib(ad) =\<^sub>t vl \<rparr> cls) \<and>
                      (\<exists>vl. [libTop = (ad)]\<lparr>libSuc(ad) =\<^sub>t vl \<rparr> cls)")
      using lib_read_transfer apply blast
      apply (simp add: cobs_to_def)
            apply auto[1]
      using lib_read_cvd_pres apply blast
            apply (meson cobs_to_def lib_read_transfer)
           apply(simp add: cobs_to_def)
           apply(intro conjI impI)
   apply(subgoal_tac "(\<exists>vl. [libTop = (top ps' t)]\<lparr>libSuc
      (top ps' t) =\<^sub>t vl \<rparr> cls)", elim exE conjE)
      apply(rule_tac x="vl" in exI)
        apply(intro conjI)
             apply (simp add: lib_read_transfer)
            apply(subgoal_tac "[libSuc (prog_state.top ps' t) =\<^sub>t vl] cls'")
             apply(simp add: lib_d_obs_t_def lib_d_obs_def, elim conjE)
      apply(subgoal_tac "lib_value cls'
        (lib_lastWr cls' (Suc (prog_state.top ps' t))) =
       lib_value cls
        (lib_lastWr cls (Suc (prog_state.top ps' t)))")
      apply(subgoal_tac "top ps' t\<in>written_addr cls")
      apply(simp add: globals)
               apply blast 
      apply(simp add: written_addr_def)
      using read_value_in_written apply auto[1]
      apply (simp add: rd_A_preserves_last)
      apply (simp add: lib_read_transfer)
      apply blast
      apply(simp add: written_addr_def)
      using rd_A_preserves_values rd_A_preserves_writes_on read_value_in_written apply auto[1]
      apply(case_tac "pc ps' t"; simp)
         apply(simp add: globals lib_pop_def pop_inv_def; elim exE conjE)  
         apply (metis PC.distinct(11) PC.distinct(3) fun_upd_same neq0_conv)
            apply(simp add: globals lib_pop_def pop_inv_def; elim exE conjE)  
   apply (metis PC.distinct(13) PC.distinct(5) fun_upd_same neq0_conv)
            apply(simp add: globals lib_pop_def pop_inv_def; elim exE conjE)  
       apply auto[1]
            apply(simp add: globals lib_pop_def pop_inv_def; elim exE conjE)  
      by auto
  next
    case L2
    then show ?thesis
      using assms
      apply(simp add: lib_pop_def pop_inv_def; elim exE conjE)
      apply(case_tac "pc ps' t"; simp)
      apply(intro conjI impI)
             apply (simp add: cobs_to_read_pres)  
            apply (simp add: dobs_to_def)
            apply (metis agt_pushed_same2rd_relax_before_state lib_d_obs_pres_read)
      apply(case_tac "top ps t \<in> pushed_addr ps ", simp_all)
      using read_lib_d_obs apply blast
           apply(subgoal_tac "glb_inv16 ps cls" , simp add: glb_inv16_def)
            apply(subgoal_tac "ntop ps' t \<in> lib_value cls`(lib_writes_on cls (Suc (prog_state.top ps t)))")
      apply blast
  apply(simp add: lib_read_step_def lib_read_def all_updates_l lib_visible_writes_def)
  apply blast
        apply(simp add: globals)
      using lib_read_cvd_pres apply blast
      using lib_d_obs_pres_read apply blast
       apply (metis lib_d_obs_def lib_d_obs_t_def rd_preserves_last read_lib_d_obs)
       apply(simp add: written_addr_def)

       apply (metis image_cong lib_read_writes_on_diff_var_pres_backwards read_pres_value)
      using lib_d_obs_pres_read apply blast
      done
  next
    case L3
    then show ?thesis
      using assms
      apply(case_tac "\<not> res ps' t")
      apply(simp add: lib_pop_def pop_inv_def; elim exE conjE)
      apply (metis cobs_to_failed_cas_pres cvd_CAS_R_cvd failed_CAS_Top_written_addr_post2)
      apply(subgoal_tac "top ps t \<in> pushed_addr ps")
      apply(simp add: lib_pop_def pop_inv_def; elim exE conjE; intro conjI impI)

          apply (meson cvd_CAS_R_cvd)  
         apply (metis cvd_CAS_R_success_d_obs_post d_obs_post_CAS_R_diff_var_post)
        apply(simp add: written_addr_def)
     using success_CAS_Top_written_addr_post apply auto[1]
      defer
           apply(simp add: lib_pop_def pop_inv_def globals; elim exE conjE)
     apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
(*
     apply(simp add: cobs_to_def)
     apply(intro conjI impI allI)
     apply(elim disjE conjE)
           apply(subgoal_tac "ad1 \<notin>{Top, Null} \<and> ad2 \<notin>{Top, Null}")
    apply(subgoal_tac "agt ad1 ad2 ps cls") 
    apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
            apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_press)
     apply blast
      apply (simp add: agt_pop_successful_cas_before)
    apply(simp add: globals)
         apply (metis gr_zeroI subsetD)
            apply(subgoal_tac "ad1 \<notin>{Top, Null} \<and> ad2 \<notin>{Top, Null}")
      apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
   apply (metis Null_def insertCI successful_CAS_lib_c_obs_lib_diff_value_press)
            apply(simp add: globals)
            apply(simp add: globals)
        apply (metis gr_zeroI subsetD)
       apply(subgoal_tac "ntop ps t \<in> pushed_addr ps")
        apply(case_tac "ad1 = ntop ps t")
         apply(subgoal_tac "agt ad1 ad2 ps cls")
          apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
     apply(elim exE)
sledgehammer
     defer     
     apply blast
     oops
        defer
     apply(simp add: globals)
     apply (metis gr_zeroI subsetD)
*)
     done
  next
    case L4 
    then show ?thesis
    using assms
    by(simp add: lib_pop_def pop_inv_def; elim exE conjE)
  next
    case L5
    then show ?thesis
    using assms
    by(simp add: lib_pop_def pop_inv_def; elim exE conjE)
  next
    case L6
    then show ?thesis
      using assms
      by(simp add: lib_pop_def pop_inv_def; elim exE conjE)
  qed


lemma "cls ccs[n \<leftarrow> lib(x)]\<^sub>t cls' ccs' \<Longrightarrow> n\<in> lib_value cls `(lib_writes_on cls (x))"
  apply(simp add: lib_read_step_def lib_read_def all_updates_l lib_visible_writes_def)
  apply blast
  done


lemma "agt ad1 ad ps cls \<Longrightarrow>
       ad1 \<in> pushed_addr ps"
  apply(simp add: agt_def clss_def nxt_rel_def trancl_def)
  using converse_tranclpE apply fastforce
  done



lemma dd:
  assumes "(a,b)\<in>f\<^sup>+"
      and "(t,d)\<in>f"
      and "(a,t)\<notin>f\<^sup>+"
      and "a \<noteq> t"
      and "\<forall> e . (e,e)\<notin>f\<^sup>+"
      and "\<forall> e. (a,e)\<in>f\<^sup>+ \<and> (e,b)\<in>f\<^sup>+ \<longrightarrow> e \<noteq> t"
      and "f' = f - {(t,d)}"
    shows "(a,b)\<in>f'\<^sup>+"
  using assms
  apply(induction a b rule: trancl.induct)
   apply simp
   apply auto[1]
  by (metis Pair_inject insertE insert_Diff trancl.trancl_into_trancl)



lemma pop_gloabals_total_order:
  assumes "wfs ccs"
      and "lib_wfs cls ccs"
      and "lib_pop t v ps cls ccs ps' cls' ccs'"
      and "pop_inv t l (pc ps t) cls ccs  ps"
      and "glb_inv ps cls"
      and "glb ps cls"
      and "to ps cls"
    shows "to ps' cls'"
  apply(simp add: to_def)
  proof(intro conjI)
    show "to_p1 ps' cls'"
    proof(cases "pc ps t")
      case L1
      then show ?thesis
        using assms
        apply(simp add: globals to_p4_def to_p3_def lib_pop_def pop_inv)
        apply(intro allI impI)
        by (metis agt_pushed_same2rd)
    next
      case L2
      then show ?thesis
        using assms
        apply(simp add: globals lib_pop_def pop_inv)
        apply(intro allI impI, elim conjE)                        
        by (metis agt_pushed_same2rd_relax)
    next
      case L3
      then show ?thesis
      using assms
      apply(simp add: globals lib_pop_def pop_inv to_p4_def)
      apply(intro allI impI conjI, elim conjE)
      apply(case_tac "\<not>res ps' t", simp_all)
       apply (simp add: agt_def failed_cas_preserves_clss)
      apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls - {(top ps t, ntop ps t)}")
       defer
       apply(simp add: nxt_rel_def)
      apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) = lib_value cls (lib_lastWr cls (Suc e))")
      apply safe
      apply simp
       apply simp
             apply simp
      apply(subgoal_tac "pushed_addr ps = {}")
             apply simp
      apply(simp add: to_simps)
       apply (metis a_not_in_pushed_clss agt_def lastTop_def)
       apply simp
      apply(simp add:pop_inv_def to_simps)
       apply (metis succ_CAS_preserves_last)
       apply (metis succ_CAS_preserves_last)
      apply(simp add:pop_inv_def to_simps)
       apply (metis a_not_in_pushed_clss agt_def lastTop_def)
      apply(case_tac "agt a b ps cls")
      apply(subgoal_tac "\<not>agt a (top ps t) ps cls ")
       apply(subgoal_tac "\<forall> e. (a,e)\<in>(nxt_rel ps cls)\<^sup>+ \<and> (e,b)\<in>(nxt_rel ps cls)\<^sup>+ \<longrightarrow> e \<noteq> (top ps t)")
        apply(simp add: agt_def clss_def)
         apply (metis (no_types, lifting) dd Diff_empty Diff_insert0 a_not_in_pushed_nxt_rel converse_tranclE)
        apply (metis agt_def clss_def)
      apply(simp add: pop_inv_def to_simps globals )
       apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write no_nxt_no_agt)
      apply(subgoal_tac "agt  b a ps cls")
      apply(subgoal_tac "agt  b a ps' cls'")
        apply blast

      apply(subgoal_tac "\<not>agt b (top ps t) ps cls ")
       apply(subgoal_tac "\<forall> e. (b,e)\<in>(nxt_rel ps cls)\<^sup>+ \<and> (e,a)\<in>(nxt_rel ps cls)\<^sup>+ \<longrightarrow> e \<noteq> (top ps t)")
        apply(simp add: agt_def clss_def)
         apply (metis (no_types, lifting) dd Diff_empty Diff_insert0 a_not_in_pushed_nxt_rel converse_tranclE)
        apply (metis agt_def clss_def)
       apply(simp add: pop_inv_def to_simps globals )
      apply (metis assms(2) cvd_CAS_R_success_read_val lib_cvd_exist_last_write no_nxt_no_agt)
      by blast
    next
      case L4
      then show ?thesis
      using assms
      by(simp add: globals lib_pop_def pop_inv)
    next
      case L5
      then show ?thesis
      using assms
      by(simp add: globals lib_pop_def pop_inv)
    next
      case L6
      then show ?thesis   
        using assms
      by(simp add: globals lib_pop_def pop_inv)
    qed
    next  show "to_p2 ps' cls'"
    proof(cases "pc ps t")
      case L1
      then show ?thesis
        using assms
        apply(simp add: globals lib_pop_def pop_inv)
        by (metis (no_types, lifting) agt_pushed_same2rd lastTop_def rd_A_preserves_last to_p2_def)

    next
      case L2
      then show ?thesis
        using assms
        apply(simp add: globals lib_pop_def pop_inv)              
        by (metis (no_types, lifting) agt_pushed_same2rd_relax lastTop_def rd_preserves_last to_p2_def)
    next
      case L3
      then show ?thesis
        using assms
        apply(simp add: globals lib_pop_def pop_inv to_simps)     
        apply(intro conjI impI allI)
        apply(case_tac "\<not> res ps' t", simp_all)
         apply (metis (no_types, lifting) agt_def failed_CAS_preserves_last failed_cas_preserves_clss)
      apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls - {(top ps t, ntop ps t)}")
       defer
       apply(simp add: nxt_rel_def)
      apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) = lib_value cls (lib_lastWr cls (Suc e))")
      apply safe
      apply simp
       apply simp
             apply simp
      apply(subgoal_tac "pushed_addr ps = {}")
             apply simp
      apply(simp add: to_simps)
       apply (metis a_not_in_pushed_clss agt_def)
       apply simp
      apply(simp add:pop_inv_def to_simps)
       apply (metis succ_CAS_preserves_last)
       apply (metis succ_CAS_preserves_last)
      apply(simp add:pop_inv_def to_simps)
       apply (metis a_not_in_pushed_clss agt_def)

        apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = ntop ps t")
         defer
        apply(simp add: pop_inv_def)
         apply (metis cvd_CAS_R_success_read_val succ_CAS_last_value)
        apply simp
        apply(case_tac "ntop ps t = Null")
        apply(subgoal_tac "pushed_addr ps = {top ps t}")
          apply simp
         apply(simp add:pop_inv_def )
        apply(subgoal_tac "lastTop cls \<noteq> Null \<and>
  lastVal cls (lastTop cls + 1) = Null \<and> to ps cls \<and> glb_inv ps cls \<and> glb ps cls")
        using l5[where cls=cls  and ps=ps]
        apply (simp add: glb_inv_def)
              apply (metis cvd_CAS_R_success_read_val empty_iff lastTop_def lib_cvd_exist_last_write subset_singleton_iff)
          apply(simp add:pop_inv_def to_simps globals)
         apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
        apply(simp add: agt_def clss_def)
        apply(subgoal_tac "agt (ntop ps t) a ps cls")
        apply(subgoal_tac " \<forall>e. (ntop ps t, e) \<in> (nxt_rel ps cls)\<^sup>+ \<and>
      (e, a) \<in> (nxt_rel ps cls)\<^sup>+ \<longrightarrow>
      e \<noteq> prog_state.top ps t")
          apply(subgoal_tac "(ntop ps t, a) \<in> (nxt_rel ps cls)\<^sup>+ \<and>
  (top ps t, ntop ps t) \<in> nxt_rel ps cls \<and> (ntop ps t, prog_state.top ps t) \<notin> (nxt_rel ps cls)\<^sup>+")
        apply(elim conjE, simp add: pop_inv_def, elim conjE exE)
        using  dd[where a = "ntop ps t" and t = "top ps t" and f = "nxt_rel ps cls"  and f' = "nxt_rel ps' cls'"]
           apply (metis a_not_in_pushed_nxt_rel converse_tranclE)
          apply(intro conjI)
            apply (simp add: agt_def clss_def)
        apply(simp add: agt_def clss_def to_simps globals pop_inv_def, elim conjE exE)
        apply (metis Diff_empty Diff_insert0 Diff_insert_absorb a_not_in_pushed_nxt_rel converse_tranclE cvd_CAS_R_success_read_val lib_cvd_exist_last_write mk_disjoint_insert)
        apply(simp add: agt_def clss_def to_simps globals pop_inv_def, elim conjE exE)
          apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
        apply(simp add: agt_def clss_def to_simps globals pop_inv_def, elim conjE exE)
        apply(intro allI impI)
        apply (smt cvd_CAS_R_success_read_val lib_cvd_exist_last_write trancl_trans)
        apply(simp add: agt_def clss_def to_simps globals pop_inv_def, elim conjE exE)
        apply(subgoal_tac " (top ps t, a) \<in> (nxt_rel ps cls)\<^sup>+ \<and>  (top ps t, ntop ps t) \<in> (nxt_rel ps cls)")
        using nothing_between_a_nxt[where a = "top ps t" and cls=cls  and ps=ps]   
        apply (simp add: globals to_simps agt_def clss_def)
        apply (metis a_not_in_pushed_nxt_rel)
        by (smt Diff_empty Diff_insert0 Diff_insert_absorb a_not_in_pushed_nxt_rel converse_tranclE cvd_CAS_R_success_read_val lib_cvd_exist_last_write mk_disjoint_insert)
    next
      case L4
      then show ?thesis 
        using assms
        by(simp add: globals lib_pop_def pop_inv)     
    next
      case L5
      then show ?thesis 
        using assms
        by(simp add: globals lib_pop_def pop_inv)     
    next
      case L6
      then show ?thesis 
        using assms
        by(simp add: globals lib_pop_def pop_inv)     
    qed 
  next  show "to_p3 ps' cls'"
    proof(cases "pc ps t")
      case L1
      then show ?thesis 
        using assms
        apply(simp add: globals lib_pop_def pop_inv)     
        by (metis agt_pushed_same2rd to_p3_def)
    next
      case L2
      then show ?thesis 
        using assms
        apply(simp add: globals lib_pop_def pop_inv)     
        by (metis agt_pushed_same2rd_relax to_p3_def)
    next
      case L3
      then show ?thesis
        using assms
                apply(simp add: globals lib_pop_def pop_inv to_simps)     
        apply(case_tac "\<not> res ps' t", simp_all)
         apply (metis (no_types, lifting) agt_def failed_cas_preserves_clss)
      apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls - {(top ps t, ntop ps t)}")
       defer
       apply(simp add: nxt_rel_def)
      apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) = lib_value cls (lib_lastWr cls (Suc e))")
      apply safe
      apply simp
       apply simp
             apply simp
      apply(subgoal_tac "pushed_addr ps = {}")
             apply simp
      apply(simp add: to_simps)
       apply (metis a_not_in_pushed_clss agt_def)
       apply simp
      apply(simp add:pop_inv_def to_simps)
       apply (metis succ_CAS_preserves_last)
       apply (metis succ_CAS_preserves_last)
      apply(simp add:pop_inv_def to_simps)
         apply (metis a_not_in_pushed_clss agt_def)
        apply(case_tac "ntop ps t = Null")
        apply(subgoal_tac "pushed_addr ps = {top ps t}")
          apply simp
         apply(simp add:pop_inv_def )
        apply(subgoal_tac "lastTop cls \<noteq> Null \<and>
  lastVal cls (lastTop cls + 1) = Null \<and> to ps cls \<and> glb_inv ps cls \<and> glb ps cls")
        using l5[where cls=cls  and ps=ps]
        apply (simp add: glb_inv_def)
              apply (metis cvd_CAS_R_success_read_val empty_iff lastTop_def lib_cvd_exist_last_write subset_singleton_iff)
          apply(simp add:pop_inv_def to_simps globals)
         apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
        apply(subgoal_tac "agt a 0 ps cls") defer
         apply auto[1]
        apply (simp add: pop_inv_def, elim conjE exE)
        apply(simp add: agt_def clss_def)
        apply(subgoal_tac "(a, 0) \<in> (nxt_rel ps cls)\<^sup>+")
         apply(subgoal_tac "(a, prog_state.top ps t) \<notin> (nxt_rel ps cls)\<^sup>+")
          apply(subgoal_tac "a \<noteq> prog_state.top ps t")
        apply(subgoal_tac "\<forall>e. (a, e) \<in> (nxt_rel ps cls)\<^sup>+ \<and>
      (e, 0) \<in> (nxt_rel ps cls)\<^sup>+ \<longrightarrow>
      e \<noteq> prog_state.top ps t")
        using  dd[where  t = "top ps t" and f = "nxt_rel ps cls" 
                  and f' = "nxt_rel ps' cls'" and b=0 and d="ntop ps t"]
      apply (metis Diff_empty Diff_insert0 a_not_in_pushed_nxt_rel converse_tranclE)
      apply blast
        apply blast
      apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write trancl_trans)
      by meson
    next
      case L4
      then show ?thesis 
        using assms
        by(simp add: globals lib_pop_def pop_inv)     
    next
      case L5
      then show ?thesis 
        using assms
        by(simp add: globals lib_pop_def pop_inv)     
    next
      case L6
      then show ?thesis 
        using assms
        by(simp add: globals lib_pop_def pop_inv)     
    qed 
  next  show "to_p4 ps' cls'"
    proof(cases "pc ps t")
      case L1
      then show ?thesis 
        using assms
        apply(simp add: globals lib_pop_def pop_inv to_p4_def)     
        by (metis (full_types) agt_def agt_pushed_same2rd_before_state)
    next
      case L2
      then show ?thesis 
        using assms
        apply(simp add: globals lib_pop_def pop_inv to_p4_def)     
        by (meson agt_def agt_pushed_same2rd_relax_before_state)
    next
      case L3
      then show ?thesis 
        using assms
        apply(simp add: globals lib_pop_def pop_inv to_p4_def)  
        apply(case_tac "\<not> res ps' t", simp_all)
         apply (metis failed_cas_preserves_clss)
   apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls - {(top ps t, ntop ps t)}")
       defer
       apply(simp add: nxt_rel_def)
      apply(subgoal_tac "\<forall> e . e\<in>pushed_addr ps \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc e)) = lib_value cls (lib_lastWr cls (Suc e))")
      apply safe
      apply simp
       apply simp
             apply simp
      apply(subgoal_tac "pushed_addr ps = {}")
             apply simp
              apply(simp add: to_simps)
        apply (metis nat_less_le no_nxt_no_agt)
       apply simp
      apply(simp add:pop_inv_def to_simps)
       apply (metis succ_CAS_preserves_last)
       apply (metis succ_CAS_preserves_last)
      apply(simp add:pop_inv_def to_simps)
        apply (metis nat_less_le no_nxt_no_agt)
        apply(simp add: clss_def)
             by (meson Diff_subset trancl_mono)
    next
      case L4
      then show ?thesis 
        using assms
        by(simp add: globals lib_pop_def )     
    next
      case L5
      then show ?thesis 
        using assms
        by(simp add: globals lib_pop_def )     
    next
      case L6
      then show ?thesis 
        using assms
        by(simp add: globals lib_pop_def )     
    qed
  qed



end
