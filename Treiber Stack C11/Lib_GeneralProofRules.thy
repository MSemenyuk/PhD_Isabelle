theory Lib_GeneralProofRules
imports Lib_ProofRules
begin 

lemma lib_writes_on_after_write:
 "lib_wfs ls cs \<Longrightarrow> w\<in>lib_visible_writes ls t x \<Longrightarrow> lib_valid_fresh_ts ls w ts' \<Longrightarrow>
ls' = lib_write t b w v ls cs ts' \<Longrightarrow> lib_writes_on ls' x = lib_writes_on ls x \<union> {(x,ts')}"
  apply(simp add: lib_write_def all_updates_l)
  apply(simp add: lib_wfs_def lib_lastWr_def lib_writes_on_def lib_value_def lib_visible_writes_def lib_valid_fresh_ts_def var_def tst_def)
  by (simp add: writes_ts_rewrite)


lemma lib_d_obs_ts'_gt_max:
 "lib_wfs ls cs \<Longrightarrow> [lib(x) =\<^sub>t u] ls \<Longrightarrow> w\<in>lib_visible_writes ls t x \<Longrightarrow> lib_valid_fresh_ts ls w ts'
 \<Longrightarrow> ts' > Max  (snd`(lib_writes_on ls x))"
  apply(simp add: lib_write_def all_updates_l)
   apply(simp add: lib_d_obs_t_def lib_d_obs_def )
 apply(simp add: lib_wfs_def lib_lastWr_def lib_writes_on_def lib_value_def lib_visible_writes_def lib_valid_fresh_ts_def var_def tst_def)
  done


lemma lib_covered_ts'_gt_max:
 "lib_wfs ls cs \<Longrightarrow> cvd[lib(x), u] ls\<Longrightarrow> w\<notin>lib_covered ls  \<Longrightarrow> w\<in>lib_visible_writes ls t x \<Longrightarrow> lib_valid_fresh_ts ls w ts'
 \<Longrightarrow> ts' > Max  (snd`(lib_writes_on ls x))"
   apply(simp add: lib_covered_v_def )
  apply(simp add: lib_wfs_def lib_lastWr_def lib_writes_on_def lib_value_def lib_visible_writes_def lib_valid_fresh_ts_def var_def tst_def)
  apply safe
  apply(subgoal_tac "finite(snd ` {wa. fst wa = fst w \<and> wa \<in> lib_writes ls})")
   apply (metis (no_types, lifting) prod.collapse)
  by blast


lemma d_obs_write: 
  assumes "lib_wfs ls cs"
      and "wfs cs"
      and "[lib(x) =\<^sub>t u] ls"
      and "ls cs [lib(x) := v]\<^sub>t ls' cs'"
    shows "[lib(x) =\<^sub>t v] ls'"
  using assms
  apply(simp add: lib_d_obs_t_def lib_d_obs_def )
  apply(simp add: lib_write_step_def, elim exE conjE)
  apply(subgoal_tac " ts' > Max  (snd`(lib_writes_on ls x)) \<and> lib_writes_on ls' x = lib_writes_on ls x \<union> {(x,ts')}") defer
  using assms(3) lib_d_obs_ts'_gt_max lib_writes_on_after_write apply blast
  apply(intro conjI)
   apply(simp add: lib_write_def all_updates_l)
  apply(simp add: lib_lastWr_def lib_writes_on_def lib_value_def lib_visible_writes_def lib_valid_fresh_ts_def var_def tst_def)
   apply clarsimp
  apply(subgoal_tac "finite(snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
    apply simp
  apply (smt Max.coboundedI Max_insert2 dual_order.strict_trans less_eq_rat_def)
  apply(simp add:lib_wfs_def lib_lastWr_def lib_writes_on_def lib_value_def lib_visible_writes_def lib_valid_fresh_ts_def var_def tst_def)
   apply(simp add: lib_write_def all_updates_l)
  apply(simp add: lib_lastWr_def lib_writes_on_def lib_value_def lib_visible_writes_def lib_valid_fresh_ts_def var_def tst_def)
  apply safe
  apply(subgoal_tac "Max (insert ts'
                    (snd `
                     {w. fst w = x \<and> w \<in> lib_writes ls})) = ts'")
  apply blast
  apply(subgoal_tac "finite(snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
    apply simp
  apply (smt Max.coboundedI Max_insert2 dual_order.strict_trans less_eq_rat_def)
  apply(simp add:lib_wfs_def lib_lastWr_def lib_writes_on_def lib_value_def lib_visible_writes_def lib_valid_fresh_ts_def var_def tst_def)
  done


lemma d_obs_write_diff_var: 
  assumes "lib_wfs ls cs"
      and "wfs cs"
      and "[lib(x) =\<^sub>t u] ls"
      and "ls cs [lib(y) := v]\<^sub>t' ls' cs'"
      and "x \<noteq> y"
    shows "[lib(x) =\<^sub>t u] ls'"
  using assms
  apply(simp add: lib_d_obs_t_def lib_d_obs_def )
  apply(simp add: lib_write_step_def, elim exE conjE)
   apply(simp add: lib_write_def all_updates_l)
  apply(simp add: lib_lastWr_def lib_writes_on_def lib_value_def lib_visible_writes_def lib_valid_fresh_ts_def var_def tst_def)
  apply safe
  apply (smt Collect_cong fst_conv)
    apply(subgoal_tac "finite(snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
  apply (smt Collect_cong fst_conv)
  apply(simp add:lib_wfs_def lib_lastWr_def lib_writes_on_def lib_value_def lib_visible_writes_def lib_valid_fresh_ts_def var_def tst_def)
  apply (metis fst_conv)
    apply(subgoal_tac "finite(snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
  apply (smt Collect_cong fst_conv)
  apply(simp add:lib_wfs_def lib_lastWr_def lib_writes_on_def lib_value_def lib_visible_writes_def lib_valid_fresh_ts_def var_def tst_def)  
  done


lemma d_obs_CAS_R_diff_var: 
  assumes "lib_wfs ls cs"
      and "wfs cs"
      and "[lib(x) =\<^sub>t v] ls"
      and "x \<noteq> y"
      and "ls cs CAS\<^sup>R[lib(y), res, u, u']\<^sub>t ls' cs'"
    shows "[lib(x) =\<^sub>t v] ls'"
  using assms
  apply(simp add: lib_d_obs_t_def lib_d_obs_def )
  apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
  apply(case_tac "lib_value ls (a, b) = u", simp_all)
   defer
   apply(simp add: lib_read_def all_updates_l)
  apply safe
           apply (simp_all add: lib_syncing_def)
  using a_is_x apply blast
  using a_is_x apply blast
     apply(simp add: lib_lastWr_def lib_writes_on_def tst_def )
    apply(simp add: lib_lastWr_def lib_writes_on_def tst_def lib_value_def)
  apply(simp add: lib_update_r_def all_updates_l)
  apply(simp add: lib_lastWr_def lib_writes_on_def tst_def lib_value_def)
  apply safe
  using a_is_x apply blast
  apply (metis fst_conv var_def)
  apply(simp add: lib_update_r_def all_updates_l)
  apply(simp add: lib_lastWr_def lib_writes_on_def tst_def lib_value_def)
  apply safe
  using a_is_x apply blast
  apply (metis fst_conv var_def)  
  by (metis a_is_x fst_conv var_def)


lemma cvd_CAS_R_cvd: 
  assumes "lib_wfs ls cs"
      and "wfs cs"
      and "\<exists> u . cvd[lib(x), u] ls"
      and "ls cs CAS\<^sup>R[lib(x), res, v, v']\<^sub>t ls' cs'"
    shows "\<exists> u . cvd[lib(x), u] ls'"
  using assms
  apply(elim exE)
  apply(case_tac "res = True", simp_all)
   apply(rule_tac x = v' in exI)
   apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
  apply(subgoal_tac " ts' > Max  (snd`(lib_writes_on ls x))")
    defer
  using lib_covered_ts'_gt_max apply blast defer
  apply(case_tac "lib_value ls (a, b) = v", simp_all)
  apply(simp add: lib_update_r_def all_updates_l)
   apply(simp add: lib_lastWr_def lib_writes_on_def  lib_value_def lib_covered_v_def var_def tst_def lib_visible_writes_def)
   apply(intro allI impI conjI)
     apply(subgoal_tac "finite(snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
  apply(subgoal_tac "{w. fst w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)} = {w. fst w = x \<and> ( w \<in> lib_writes ls)} \<union> {(x,ts')}")
      apply simp
  apply (smt Max.coboundedI Max_insert2 dual_order.strict_trans less_eq_rat_def)
      apply(simp add: lib_wfs_def lib_lastWr_def lib_writes_on_def  lib_value_def lib_covered_v_def var_def tst_def lib_visible_writes_def)
      apply (simp add: writes_ts_rewrite)
      apply(simp add: lib_wfs_def lib_lastWr_def lib_writes_on_def  lib_value_def lib_covered_v_def var_def tst_def lib_visible_writes_def)
  apply blast
   apply blast
    apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
  apply(case_tac "lib_value ls (a, b) = v", simp_all)
  using lib_read_cvd_pres lib_read_step_def by blast


lemma last_CAS_R_diff_var: 
  assumes "lib_wfs ls cs"
      and "wfs cs"
      and "x \<noteq> y"
      and "ls cs CAS\<^sup>R[lib(y), res, u, u']\<^sub>t ls' cs'"
    shows "lib_lastWr ls' x = lib_lastWr ls x"
  using assms
  apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
  apply(case_tac "lib_value ls (a, b) = u", simp_all)
  apply(simp add: lib_update_r_def all_updates_l)
   apply(simp add: lib_lastWr_def lib_writes_on_def  lib_value_def lib_covered_v_def var_def tst_def lib_visible_writes_def)
   apply (metis fst_conv)
  by (metis lib_read_last_diff_var_pres lib_read_step_def)


lemma write_value_CAS_R_diff_var: 
  assumes "lib_wfs ls cs"
      and "wfs cs"
      and "x \<noteq> y"
      and "ls cs CAS\<^sup>R[lib(y), res, u, u']\<^sub>t ls' cs'"
      and "w \<in> lib_writes_on ls x"
    shows "lib_value ls' w = lib_value ls w"
  using assms
  apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
  apply(case_tac "lib_value ls (a, b) = u", simp_all)
  apply(simp add: lib_update_r_def all_updates_l)
   apply(simp add: lib_lastWr_def lib_writes_on_def  lib_value_def lib_covered_v_def var_def tst_def lib_visible_writes_def)
   apply (metis fst_conv)
  using lib_read_step_def lib_value_read_pres by blast


lemma d_obs_post_CAS_R_diff_var_pre: 
  assumes "lib_wfs ls cs"
      and "wfs cs"
      and "[lib(x) =\<^sub>t v] ls'"
      and "x \<noteq> y"
      and "ls cs CAS\<^sup>R[lib(y), res, u, u']\<^sub>t' ls' cs'"
    shows "[lib(x) =\<^sub>t v] ls"
  using assms
  apply(simp add: lib_d_obs_t_def lib_d_obs_def lib_CAS_Rel_step_def)
  apply(elim exE conjE, intro conjI)
   apply(case_tac "lib_value ls (a, b) = u", simp_all)
  apply(simp_all add: lib_update_r_def all_updates_l lib_lastWr_def lib_value_def lib_read_def)
  apply (smt a_is_x assms(5) fun_upd_other last_CAS_R_diff_var lib_lastWr_def)
  apply (smt a_is_x assms(5) fun_upd_other last_CAS_R_diff_var lib_lastWr_def lib_syncing_def)
  apply(simp add: lib_writes_on_def lib_visible_writes_def)
   apply(case_tac "lib_value ls (a, b) = u", simp_all)
  apply(simp_all add: lib_update_r_def all_updates_l lib_lastWr_def lib_value_def lib_read_def)
  apply(case_tac " x = a", simp_all)
  by (smt Collect_cong fst_conv var_def)

lemma d_obs_post_CAS_R_diff_var_post: 
  assumes "lib_wfs ls cs"
      and "wfs cs"
      and "[lib(x) =\<^sub>t v] ls"
      and "x \<noteq> y"
      and "ls cs CAS\<^sup>R[lib(y), res, u, u']\<^sub>t' ls' cs'"
    shows "[lib(x) =\<^sub>t v] ls'"
  using assms
  apply(simp add: lib_d_obs_t_def lib_d_obs_def lib_CAS_Rel_step_def)
  apply(elim exE conjE, intro conjI)
   apply(case_tac "lib_value ls (a, b) = u", simp_all)
  apply(simp_all add: lib_update_r_def all_updates_l lib_lastWr_def lib_value_def lib_read_def)
  apply (metis a_is_x assms(1) assms(2) assms(4) assms(5) last_CAS_R_diff_var lib_lastWr_def snd_conv tst_def)
  apply (smt Collect_cong a_is_x lib_state.select_convs(1) lib_state.surjective lib_state.update_convs(2) lib_syncing_def lib_writes_on_def)
   apply(case_tac "lib_value ls (a, b) = u", simp_all)
  apply(simp_all add: lib_update_r_def all_updates_l lib_lastWr_def lib_value_def lib_read_def)
  apply (smt a_is_x assms(5) fun_upd_other last_CAS_R_diff_var lib_lastWr_def)
  by (simp add: lib_writes_on_def)


lemma cvd_CAS_R_success_read_val: 
  assumes "lib_wfs ls cs"
      and "wfs cs"
      and "cvd[lib(x), v] ls"
      and "ls cs CAS\<^sup>R[lib(x), True, u, u']\<^sub>t ls' cs'"
    shows "u = v"
  using assms
  apply(simp add: lib_d_obs_t_def lib_d_obs_def lib_CAS_Rel_step_def)
  apply safe
  apply(case_tac "lib_value ls (a, b) = u", simp_all)
  using cvd_vw_val by blast


lemma cvd_CAS_R_success_post: 
  assumes "lib_wfs ls cs"
      and "wfs cs"
      and "cvd[lib(x), u] ls"
      and "ls cs CAS\<^sup>R[lib(x), True, u, u']\<^sub>t ls' cs'"
    shows "cvd[lib(x), u'] ls'"
  using assms
  apply(subgoal_tac "\<exists>u . cvd[lib(x), u] ls")
   apply(subgoal_tac "\<exists>u . cvd[lib(x), u] ls'")
    defer
  apply (simp add: cvd_CAS_R_cvd)
  apply auto[1]
    apply(elim exE)
  apply(simp add: lib_d_obs_t_def lib_d_obs_def lib_CAS_Rel_step_def lib_update_r_def, elim exE conjE)
    apply(case_tac "lib_value ls (a, b) = u", simp_all)
  apply(simp add:  lib_update_r_def all_updates_l lib_covered_v_def)
   apply safe
   apply(simp add: lib_writes_on_def)
  using a_is_x apply blast
    apply(simp add: lib_writes_on_def)
  apply (smt lib_visible_writes_def lib_writes_on_def mem_Collect_eq)
    apply(simp add: lib_writes_on_def)
  using a_is_x apply blast
  apply(simp add:lib_value_def lib_lastWr_def lib_writes_on_def)
  apply(elim conjE disjE)
  apply auto[1]
  by (smt a_is_x lib_visible_writes_def lib_writes_on_def mem_Collect_eq)


lemma cvd_CAS_R_success_d_obs_post: 
  assumes "lib_wfs ls cs"
      and "wfs cs"
      and "cvd[lib(x), v] ls"
      and "ls cs CAS\<^sup>R[lib(x), True, u, u']\<^sub>t ls' cs'"
    shows "[lib(x) =\<^sub>t u'] ls'"
  using assms
  apply(subgoal_tac "v = u")
  defer
  using cvd_CAS_R_success_read_val apply blast
    apply(simp add: lib_covered_v_def lib_d_obs_def lib_d_obs_t_def)
  apply(intro conjI)
   apply(simp add: lib_CAS_Rel_step_def lib_update_r_def)
   apply(elim exE conjE)
   apply(subgoal_tac "lib_lastWr ls' x = (x, ts') ")
    apply(case_tac "lib_value ls (a, b) = u", simp_all)
  apply(simp add: all_updates_l lib_update_r_def)
  using a_is_x apply blast
    apply(case_tac "lib_value ls (a, b) = u", simp_all)
   apply(simp add: all_updates_l lib_update_r_def lib_lastWr_def lib_writes_on_def)
   apply(elim conjE)
   apply(subgoal_tac "{w. var w = x \<and> (w = (a, ts') \<or> w \<in> lib_writes ls)} = {w. var w = x \<and> ( w \<in> lib_writes ls)} \<union> { (a, ts')}")
    defer
    apply(simp add: var_def)
  apply(subgoal_tac "finite({w. fst w = x \<and> w \<in> lib_writes ls})")
  using a_is_x writes_ts_rewrite apply blast
    apply(simp add: lib_wfs_def lib_writes_on_def var_def)
   defer
   apply (simp add: tst_def var_def)
  apply(subgoal_tac " b = Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}) ", simp_all)
    defer
    apply(subgoal_tac "a = x", simp) 
  apply(simp add: lib_visible_writes_def lib_writes_on_def)
  using a_is_x apply blast
   defer
   apply(subgoal_tac "ts' > b")
    apply(subgoal_tac "finite(snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
  apply(simp add: lib_valid_fresh_ts_def lib_visible_writes_def lib_writes_on_def tst_def var_def)
  apply (metis (no_types, lifting) Max_ge Max_insert2 dual_order.strict_trans less_eq_rat_def)
     apply(simp add: lib_wfs_def lib_writes_on_def var_def)
  apply (simp add: lib_valid_fresh_ts_def)
  apply(simp add: lib_CAS_Rel_step_def lib_update_r_def)
  apply(elim exE conjE)
   apply(subgoal_tac "lib_lastWr ls' x = (x, ts') ")
     apply(case_tac "lib_value ls (a, b) = u", simp_all)
   apply(simp add: all_updates_l lib_update_r_def lib_lastWr_def lib_writes_on_def)
   apply(simp add: lib_value_def)
  using a_is_x apply blast
     apply(case_tac "lib_value ls (a, b) = u", simp_all)
    apply(simp add: all_updates_l lib_update_r_def lib_lastWr_def lib_writes_on_def)
   apply(subgoal_tac "{w. var w = x \<and> (w = (a, ts') \<or> w \<in> lib_writes ls)} = {w. var w = x \<and> ( w \<in> lib_writes ls)} \<union> { (a, ts')}")
    defer
    apply(simp add: var_def)
  apply(subgoal_tac "finite({w. fst w = x \<and> w \<in> lib_writes ls})")
  using a_is_x writes_ts_rewrite apply blast
      apply(simp add: lib_wfs_def lib_writes_on_def var_def)
   apply (simp add: tst_def var_def)
  apply(subgoal_tac " b = Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}) ", simp_all)
    defer
    apply(subgoal_tac "a = x", simp) 
  apply(simp add: lib_visible_writes_def lib_writes_on_def)
  using a_is_x apply blast
   apply(subgoal_tac "ts' > b")
    apply(subgoal_tac "finite(snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
  apply(simp add: lib_valid_fresh_ts_def lib_visible_writes_def lib_writes_on_def tst_def var_def)
  apply (metis (no_types, lifting) Max_ge Max_insert2 dual_order.strict_trans less_eq_rat_def)
     apply(simp add: lib_wfs_def lib_writes_on_def var_def)  
  by (simp add: lib_valid_fresh_ts_def)



lemma lib_read_pres_last:
  assumes "lib_wfs ls cs"
      and "wfs cs"
      and "lib_read_step t x b ls cs ls' cs' v "
      shows "lib_lastWr ls y = lib_lastWr ls' y"
  using assms
  apply(simp add: lib_read_step_def lib_read_def lib_lastWr_def all_updates_l)
  apply(elim exE conjE)
  apply(simp add: lib_writes_on_def)
  done


lemma lib_read_transfer:
  assumes "lib_wfs ls cs"
      and "wfs cs"
      and "[lib(x) = a]\<lparr>lib(y) =\<^sub>t b\<rparr> ls"
      and "lib_read_step t x True ls cs ls' cs' a "
    shows "[lib(y) =\<^sub>t b] ls'"
  using assms
  apply(simp add: lib_read_step_def lib_c_obs_lib_only_def lib_d_obs_t_def lib_d_obs_def)
  apply(elim exE conjE, intro conjI)
   apply(simp add: lib_read_def all_updates_l)
   apply(intro conjI impI allI)
      apply(simp add: ts_oride_def lib_lastWr_def lib_writes_on_def var_def tst_def lib_value_def lib_visible_writes_def)
  apply safe
  apply blast
  apply (simp add: lib_wfs_def)
  using lib_syncing_def apply blast
       apply(simp add: ts_oride_def lib_lastWr_def lib_writes_on_def var_def tst_def lib_value_def lib_visible_writes_def)
  apply safe
  apply blast
       apply(simp add:lib_wfs_def lib_syncing_def ts_oride_def lib_lastWr_def lib_writes_on_def var_def tst_def lib_value_def lib_visible_writes_def)
  apply clarsimp
  using lib_syncing_def apply blast
   apply(simp add: lib_read_def all_updates_l)
   apply(intro conjI impI allI)
   apply(simp add: ts_oride_def lib_lastWr_def lib_writes_on_def var_def tst_def lib_value_def lib_visible_writes_def)
   apply blast
  using lib_syncing_def by blast



lemma write_diff_var_last_val:
  assumes "cls ccs [lib(x) := v]\<^sub>t cls' ccs'"
    and "lib_wfs cls ccs"
    and "x \<noteq> y"
  shows "lib_value cls' (lib_lastWr cls' y) = lib_value cls (lib_lastWr cls y)"
  using assms
  apply(simp add: lib_write_def lib_write_step_def all_updates_l, elim exE conjE)
  apply clarsimp
  apply(simp add: lib_value_def lib_lastWr_def lib_writes_on_def var_def tst_def)
  apply safe
  using a_is_x apply blast  
  apply (metis fst_conv)  
  by (metis a_is_x fst_conv)

lemma rd_preserves_last:
"cls ccs [r \<leftarrow> lib a]\<^sub>t cls' ccs' 
  \<Longrightarrow> (lib_value cls (lib_lastWr cls b) = lib_value cls' (lib_lastWr cls' b))"
  apply (simp add: lib_read_step_def lib_read_def, safe)
  apply (case_tac "lib_syncing cls (aa, ba) False", simp_all)
  apply (simp add: lib_syncing_def)
  by (simp add: lib_value_def lib_update_thrView_def lib_lastWr_def tst_def lib_writes_on_def)

 lemma rd_A_preserves_last:
"cls ccs [r \<leftarrow>\<^sup>A lib a]\<^sub>t cls' ccs' 
  \<Longrightarrow> (lib_value cls (lib_lastWr cls b) = lib_value cls' (lib_lastWr cls' b))"
  apply (simp add: lib_read_step_def lib_read_def, safe)
  apply (case_tac "lib_syncing cls (aa, ba) False", simp_all)
  apply (simp add: lib_syncing_def)
  by (simp add: lib_value_def lib_update_thrView_def lib_lastWr_def tst_def lib_writes_on_def)


lemma failed_CAS_preserves_last: 
"cls ccs CAS\<^sup>R[lib a, False, b, b']\<^sub>t cls' ccs'
  \<Longrightarrow> (lib_value cls (lib_lastWr cls c) = lib_value cls' (lib_lastWr cls' c))" 
  apply (simp add: lib_CAS_Rel_step_def, safe)
  apply (case_tac "lib_value cls (aa, ba) = b", safe)
  apply (simp add: lib_value_def lib_update_thrView_def lib_lastWr_def tst_def lib_writes_on_def)
  using lib_read_step_def rd_preserves_last by fastforce


lemma succ_CAS_preserves_last:
"cls ccs CAS\<^sup>R[lib x, rv, y, y']\<^sub>t cls' ccs'\<Longrightarrow> x \<noteq> b
  \<Longrightarrow> lib_value cls' (lib_lastWr cls' b) = lib_value cls (lib_lastWr cls b)"
  apply (simp add: lib_CAS_Rel_step_def, safe)
  apply (case_tac "lib_value cls (a, ba) = y", safe)
  apply (simp add: var_def lib_value_def lib_update_r_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def)
  apply (smt Collect_cong a_is_x fst_conv)
  using lib_read_step_def rd_preserves_last by fastforce


lemma ts'_gt_max_writes_on: "cvd[lib(x), y] cls \<Longrightarrow> w\<in>lib_visible_writes cls t x \<Longrightarrow> w\<notin>lib_covered cls \<Longrightarrow> lib_valid_fresh_ts cls w ts'
\<Longrightarrow> ts' > Max (snd `lib_writes_on cls x)"
  apply(simp add: lib_covered_v_def lib_visible_writes_def lib_valid_fresh_ts_def)
  by (metis lib_lastWr_def sndI surj_pair tst_def)

lemma succ_CAS_last_value:
"lib_wfs cls css \<Longrightarrow> wfs ccs \<Longrightarrow>  cls ccs CAS\<^sup>R[lib x, True, y, y']\<^sub>t cls' ccs'\<Longrightarrow> cvd[lib(x), y] cls
  \<Longrightarrow> lib_value cls' (lib_lastWr cls' x) = y'"
  apply (simp add: lib_CAS_Rel_step_def, elim exE conjE)
  apply (case_tac "lib_value cls (a, b) = y", simp_all)
  apply(subgoal_tac "lib_lastWr cls' x = (x,ts')")

  apply (simp add: lib_covered_v_def var_def lib_value_def lib_update_r_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def)
  apply safe
   apply (smt Collect_cong a_is_x fst_conv)
  apply(simp add: lib_wfs_def lib_update_r_def all_updates_l lib_valid_fresh_ts_def lib_lastWr_def lib_writes_on_def tst_def var_def)
   apply(simp add: lib_valid_fresh_ts_def lib_visible_writes_def lib_writes_on_def var_def tst_def)
  apply(subgoal_tac "a = x", simp)
   apply(subgoal_tac "{w. fst w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes cls)} = {w. fst w = x \<and> w \<in> lib_writes cls} \<union> {(x, ts')}")
    defer
    apply fastforce
   apply blast
  apply (simp add: lib_covered_v_def)
  apply(subgoal_tac "ts' > Max (snd `(lib_writes_on cls x))")
   apply(unfold  lib_writes_on_def var_def tst_def)[1]
  apply(subgoal_tac "{w. fst w = x \<and> w \<in> lib_writes cls} \<noteq> {} \<and> finite({w. fst w = x \<and> w \<in> lib_writes cls})")
  apply (smt Max_in Max_less_iff finite_imageI finite_insert image_is_empty insertE insertI1 insert_not_empty not_max)
  
   apply blast+
  using ts'_gt_max_writes_on lib_visible_writes_def lib_valid_fresh_ts_def
  by (smt lib_lastWr_def lib_writes_on_def mem_Collect_eq snd_conv tst_def var_def)


 lemma wr_preserves_last:
"cls ccs [lib x := v]\<^sub>t cls' ccs' \<Longrightarrow> x \<noteq> b 
  \<Longrightarrow> (lib_value cls (lib_lastWr cls b) = lib_value cls' (lib_lastWr cls' b))"
  apply (simp add: lib_write_step_def lib_write_def, safe)
   apply (simp add: all_updates_l var_def lib_value_def  lib_lastWr_def tst_def lib_writes_on_def)
   by (smt Collect_cong a_is_x fst_conv)
 

 lemma wr_R_preserves_last:
"cls ccs [lib x :=\<^sup>R v]\<^sub>t cls' ccs' \<Longrightarrow> x \<noteq> b 
  \<Longrightarrow> (lib_value cls (lib_lastWr cls b) = lib_value cls' (lib_lastWr cls' b))"
  apply (simp add: lib_write_step_def lib_write_def, safe)
   apply (simp add: all_updates_l var_def lib_value_def  lib_lastWr_def tst_def lib_writes_on_def)
   by (smt Collect_cong a_is_x fst_conv)


 lemma wr_R_preserves_writes_on_diff_var:
"cls ccs [lib x :=\<^sup>R v]\<^sub>t cls' ccs' \<Longrightarrow> x \<noteq> b 
  \<Longrightarrow> lib_writes_on cls' b = lib_writes_on cls b"
  apply (simp add: lib_write_step_def lib_write_def, safe)
    apply (simp add: all_updates_l var_def lib_value_def  lib_lastWr_def tst_def lib_writes_on_def)
   using a_is_x apply blast
   apply(simp add: lib_writes_on_def all_updates_l)
   by blast

lemma wr_preserves_writes_on_diff_var:
"cls ccs [lib x := v]\<^sub>t cls' ccs' \<Longrightarrow> x \<noteq> b 
  \<Longrightarrow> lib_writes_on cls' b = lib_writes_on cls b"
  apply (simp add: lib_write_step_def lib_write_def, safe)
    apply (simp add: all_updates_l var_def lib_value_def  lib_lastWr_def tst_def lib_writes_on_def)
   using a_is_x apply blast
   apply(simp add: lib_writes_on_def all_updates_l)
   by blast

lemma wr_preserves_value_diff_var:
"cls ccs [lib x := v]\<^sub>t cls' ccs' \<Longrightarrow> x \<noteq> b \<Longrightarrow> w\<in>lib_writes_on cls b
  \<Longrightarrow> lib_value cls' w = lib_value cls w"
  apply (simp add: lib_write_step_def lib_write_def, safe)
    apply (simp add: all_updates_l var_def lib_value_def  lib_lastWr_def tst_def lib_writes_on_def)
  using fresh_ts_not_in_writes by blast


lemma wr_preserves_mView_diff_var:
"cls ccs [lib x := v]\<^sub>t cls' ccs' \<Longrightarrow> x \<noteq> b \<Longrightarrow> w\<in>lib_writes_on cls b
  \<Longrightarrow> lib_modView cls' w = lib_modView cls w"
  apply (simp add: lib_write_step_def lib_write_def, safe)
    apply (simp add: all_updates_l var_def lib_value_def  lib_lastWr_def tst_def lib_writes_on_def)
  using fresh_ts_not_in_writes by blast



lemma wr_R_preserves_value_diff_var:
"cls ccs [lib x :=\<^sup>R v]\<^sub>t cls' ccs' \<Longrightarrow> x \<noteq> b \<Longrightarrow> w\<in>lib_writes_on cls b
  \<Longrightarrow> lib_value cls' w = lib_value cls w"
  apply (simp add: lib_write_step_def lib_write_def, safe)
    apply (simp add: all_updates_l var_def lib_value_def  lib_lastWr_def tst_def lib_writes_on_def)
  using fresh_ts_not_in_writes by blast

lemma wr_preserves_releasing_diff_var:
"cls ccs [lib x := v]\<^sub>t cls' ccs' \<Longrightarrow> x \<noteq> b \<Longrightarrow> w\<in>lib_writes_on cls b
  \<Longrightarrow> lib_releasing cls' w = lib_releasing cls w"
  apply (simp add: lib_write_step_def lib_write_def, safe)
    apply (simp add:lib_releasing_def all_updates_l var_def lib_value_def  lib_lastWr_def tst_def lib_writes_on_def)
  using   fresh_ts_not_in_writes
  apply (metis (full_types))
    apply (simp add:lib_releasing_def all_updates_l var_def lib_value_def  lib_lastWr_def tst_def lib_writes_on_def) 
  using a_is_x by fastforce

lemma wr_R_preserves_releasing_diff_var:
"cls ccs [lib x :=\<^sup>R v]\<^sub>t cls' ccs' \<Longrightarrow> x \<noteq> b \<Longrightarrow> w\<in>lib_writes_on cls b
  \<Longrightarrow> lib_releasing cls' w = lib_releasing cls w"
  apply (simp add: lib_write_step_def lib_write_def, safe)
    apply (simp add:lib_releasing_def all_updates_l var_def lib_value_def  lib_lastWr_def tst_def lib_writes_on_def)
  using   fresh_ts_not_in_writes
   apply (metis (full_types))
  by (simp add:lib_releasing_def all_updates_l var_def lib_value_def  lib_lastWr_def tst_def lib_writes_on_def) 


 lemma CAS_Rel_preserves_writes_on_diff_var:
"cls ccs CAS\<^sup>R[lib x, rv, y, y']\<^sub>t cls' ccs' \<Longrightarrow> x \<noteq> b 
  \<Longrightarrow> lib_writes_on cls' b = lib_writes_on cls b"
  apply (simp add: lib_CAS_Rel_step_def, elim exE conjE)
   apply (case_tac "lib_value cls (a, ba) = y", safe) 
  apply (simp add: var_def lib_value_def lib_update_r_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def)
     apply (smt Collect_cong a_is_x fst_conv)
  apply (simp add: var_def lib_value_def lib_update_r_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def)
     apply (smt Collect_cong a_is_x fst_conv)
  apply (simp add: var_def lib_value_def lib_update_r_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def)
    apply(simp add: lib_read_def all_updates_l)
   apply blast
     apply(simp add: lib_read_def all_updates_l lib_writes_on_def)
   by blast


lemma CAS_Rel_preserves_releasing_diff_var:
"cls ccs CAS\<^sup>R[lib x, rv, y, y']\<^sub>t cls' ccs' \<Longrightarrow> x \<noteq> b \<Longrightarrow> w\<in>lib_writes_on cls b
  \<Longrightarrow> lib_releasing cls' w = lib_releasing cls w"
  apply (simp add: lib_CAS_Rel_step_def, elim exE conjE)
   apply (case_tac "lib_value cls (a, ba) = y", safe) 
  apply (simp add: var_def lib_value_def lib_update_r_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def lib_releasing_def)
     apply (smt Collect_cong a_is_x fst_conv)
    apply (simp add: var_def lib_value_def lib_update_r_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def lib_releasing_def)
    apply (simp add: var_def lib_value_def lib_read_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def lib_releasing_def)
    by (simp add: var_def lib_value_def lib_read_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def lib_releasing_def)


lemma CAS_Rel_preserves_value_diff_var:
"cls ccs CAS\<^sup>R[lib x, rv, y, y']\<^sub>t cls' ccs' \<Longrightarrow> x \<noteq> b \<Longrightarrow> w\<in>lib_writes_on cls b
  \<Longrightarrow> lib_value cls' w = lib_value cls w"
  apply (simp add: lib_CAS_Rel_step_def, elim exE conjE)
   apply (case_tac "lib_value cls (a, ba) = y", safe) 
  apply (simp add: var_def lib_value_def lib_update_r_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def lib_releasing_def)
     apply (smt Collect_cong a_is_x fst_conv)
    apply (simp add: var_def  lib_update_r_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def lib_value_def)
    apply (simp add: var_def lib_value_def lib_read_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def lib_releasing_def)
done


lemma CAS_Rel_preserves_releasing_same_var:
"cls ccs CAS\<^sup>R[lib x, rv, y, y']\<^sub>t cls' ccs' \<Longrightarrow>  w\<in>lib_writes_on cls x
  \<Longrightarrow> lib_releasing cls' w = lib_releasing cls w"
  apply (simp add: lib_CAS_Rel_step_def, elim exE conjE)
   apply (case_tac "lib_value cls (a, b) = y", safe) 
  apply (simp add: var_def lib_value_def lib_update_r_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def lib_releasing_def) 
  using   fresh_ts_not_in_writes
     apply (metis (full_types))
  apply (simp add: var_def lib_value_def lib_update_r_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def lib_releasing_def) 
    apply (simp add: var_def lib_value_def lib_read_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def lib_releasing_def)
    apply (simp add: var_def lib_value_def lib_read_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def lib_releasing_def)
  done

lemma CAS_Rel_preserves_releasing_new:
"cls ccs CAS\<^sup>R[lib x, rv, y, y']\<^sub>t cls' ccs' \<Longrightarrow>  w\<notin>lib_writes_on cls x \<Longrightarrow> w \<in> lib_writes_on cls' x
  \<Longrightarrow> lib_releasing cls' w"
 apply(case_tac "rv", simp_all)
  apply (simp add: lib_CAS_Rel_step_def, elim exE conjE)
   apply (case_tac "lib_value cls (a, b) = y", simp_all) 
  apply(subgoal_tac "w = (x, ts')")
    defer
  apply(simp add: lib_valid_fresh_ts_def lib_visible_writes_def)
    apply(simp add: lib_update_r_def all_updates_l lib_writes_on_def lib_releasing_def)
  defer
   apply(simp add: lib_update_r_def all_updates_l lib_releasing_def)
  using a_is_x apply blast
  apply (simp add: lib_CAS_Rel_step_def, elim exE conjE)
  apply (case_tac "lib_value cls (a, b) = y", simp_all) 
    by (simp add: var_def lib_value_def lib_read_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def lib_releasing_def)


lemma CAS_Rel_preserves_releasing_old:
"cls ccs CAS\<^sup>R[lib x, rv, y, y']\<^sub>t cls' ccs' \<Longrightarrow>  w\<in>lib_writes_on cls x 
  \<Longrightarrow> lib_releasing cls' w = lib_releasing cls w"
  by (simp add: CAS_Rel_preserves_releasing_same_var)

lemma CAS_Rel_preserves_value_old:
"cls ccs CAS\<^sup>R[lib x, rv, y, y']\<^sub>t cls' ccs' \<Longrightarrow>  w\<in>lib_writes_on cls x 
  \<Longrightarrow> lib_value cls' w = lib_value cls w"
 apply(case_tac "rv", simp_all)
  apply (simp add: lib_CAS_Rel_step_def, elim exE conjE)
   apply (case_tac "lib_value cls (a, b) = y", simp_all) 
   apply(simp add: lib_update_r_def all_updates_l lib_writes_on_def lib_value_def)
  using fresh_ts_not_in_writes apply blast
  apply (simp add: lib_CAS_Rel_step_def, elim exE conjE)
   apply (case_tac "lib_value cls (a, b) = y", simp_all) 
 by (simp add: var_def lib_value_def lib_read_def all_updates_l lib_lastWr_def tst_def lib_writes_on_def lib_releasing_def)


lemma rd_A_preserves_values:
"cls ccs [r \<leftarrow>\<^sup>A lib a]\<^sub>t cls' ccs' 
  \<Longrightarrow> lib_value cls  = lib_value cls' "
  apply (simp add: lib_read_step_def lib_read_def all_updates_l, elim exE conjE)
  apply (case_tac "lib_syncing cls (aa, b) False", simp_all)
   apply (simp add: lib_syncing_def)
  apply (unfold lib_value_def)
 by simp


 lemma rd_A_preserves_writes_on:
"cls ccs [r \<leftarrow>\<^sup>A lib a]\<^sub>t cls' ccs' 
  \<Longrightarrow> lib_writes_on cls' b = lib_writes_on cls b"
  apply (simp add: lib_read_step_def lib_read_def, safe)
  apply (case_tac "lib_syncing cls (aa, ba) False", simp_all)
  apply (simp add: lib_syncing_def)
   apply (simp add: lib_value_def  all_updates_l  lib_lastWr_def tst_def lib_writes_on_def)
   apply blast
 by (smt lib_state.select_convs(1) lib_state.surjective lib_state.update_convs(2) lib_update_thrView_def lib_writes_on_def mem_Collect_eq)




 lemma failed_CAS_Rel_preserves_writes_on_diff_var:
"cls ccs CAS\<^sup>R[lib x, False, y, y']\<^sub>t cls' ccs' 
  \<Longrightarrow> lib_writes_on cls' b = lib_writes_on cls b"
  apply (simp add: lib_CAS_Rel_step_def, elim exE conjE)
   apply (case_tac "lib_value cls (a, ba) = y", simp_all) 
  apply (simp add:lib_read_def var_def lib_value_def lib_update_r_def all_updates_l lib_lastWr_def tst_def lib_writes_on_def)
   done


 lemma CAS_Rel_new_write_value:
"cls ccs CAS\<^sup>R[lib x, b, y, y']\<^sub>t cls' ccs' \<Longrightarrow> w\<notin>lib_writes_on cls x \<Longrightarrow> w\<in>lib_writes_on cls' x
  \<Longrightarrow> lib_value cls' w = y'"
   apply(case_tac "\<not>b", simp_all)
   using failed_CAS_Rel_preserves_writes_on_diff_var apply metis
  apply (simp add: lib_CAS_Rel_step_def, elim exE conjE)
   apply (case_tac "lib_value cls (a, ba) = y", simp_all) 
    apply (simp add: var_def lib_value_def lib_update_r_def all_updates_l  lib_lastWr_def tst_def lib_writes_on_def)
   done

lemma lib_c_obs_lib_only_pres_wr_diff_var:  "lib_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> [lib(x) = u]\<lparr>lib(y) =\<^sub>t v\<rparr> \<sigma>  \<Longrightarrow> lib_write_step t' z b \<sigma> \<sigma>\<^sub>C  \<sigma>' \<sigma>\<^sub>C' n 
\<Longrightarrow> z \<noteq> x \<Longrightarrow> z \<noteq> y \<Longrightarrow> [lib(x) = u]\<lparr>lib(y) =\<^sub>t v\<rparr> \<sigma>'"
  apply(simp add: lib_c_obs_lib_only_def lib_write_step_def lib_visible_writes_def, elim exE conjE)
  apply(simp add: lib_write_def all_updates_l)
  apply(intro allI impI conjI)
  apply(simp_all add: lib_d_obs_def lib_lastWr_def lib_writes_on_def lib_value_def var_def tst_def lib_releasing_def)
     apply (smt Collect_cong fst_conv)
    apply blast
  apply (smt Collect_cong fst_conv)
  by blast


lemma lib_c_obs_lib_only_pres_read_var:  "lib_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> [lib(x) = u]\<lparr>lib(y) =\<^sub>t v\<rparr> \<sigma>  \<Longrightarrow>  lib_read_step t' m b \<sigma> \<sigma>\<^sub>C \<sigma>' \<sigma>\<^sub>C' n 
\<Longrightarrow> [lib(x) = u]\<lparr>lib(y) =\<^sub>t v\<rparr> \<sigma>'"
  apply(simp add: lib_c_obs_lib_only_def lib_read_step_def lib_visible_writes_def, elim exE conjE)
  apply(simp add: lib_read_def all_updates_l)
  apply(intro conjI impI allI)
         apply(simp_all add: ts_oride_def lib_syncing_def lib_d_obs_def lib_lastWr_def lib_writes_on_def lib_value_def var_def tst_def lib_releasing_def)
  apply (smt dual_order.trans fun_upd_same snd_conv)
  using dual_order.trans apply force  
  using order_trans apply blast
  using order.trans apply blast
  apply (smt fun_upd_other order.trans)  
    apply (smt fun_upd_other order.trans)
           apply blast
  apply blast
  apply (smt fun_upd_other order.trans)
  apply (smt fun_upd_other order.trans)
  apply (smt fun_upd_other order.trans)
  apply blast
  apply blast
  apply blast
  apply blast
  by blast

lemma failed_CASR_pres_c_obs_lib_only : "[lib(x) = m]\<lparr>lib(y) =\<^sub>t n \<rparr> cls \<Longrightarrow>
   cls ccs CAS\<^sup>R[lib z, False, l, k]\<^sub>t' cls' ccs' \<Longrightarrow>
   [lib(x) = m]\<lparr>lib(y) =\<^sub>t n \<rparr> cls'"
  apply(simp add: lib_c_obs_lib_only_def lib_CAS_Rel_step_def lib_visible_writes_def, elim exE conjE)
  apply(case_tac "lib_value cls (a, b) = l", simp_all)
  apply(simp add: lib_read_def all_updates_l lib_d_obs_def lib_writes_on_def lib_lastWr_def lib_syncing_def lib_value_def tst_def var_def)
  apply(intro conjI impI allI)
  using dual_order.trans apply blast  
  using dual_order.trans apply blast  
     apply (simp_all add: lib_releasing_def)
  done


lemma failed_CASR_pres_d_obs_lib : "lib_wfs cls css \<Longrightarrow>[lib(x) =\<^sub>t m] cls \<Longrightarrow>
   cls ccs CAS\<^sup>R[lib z, False, l, k]\<^sub>t' cls' ccs' \<Longrightarrow>
   [lib(x) =\<^sub>t m] cls'"
  apply(simp add:  lib_CAS_Rel_step_def lib_visible_writes_def, elim exE conjE)
  apply(case_tac "lib_value cls (a, b) = l", simp_all)
  apply(case_tac "t=t'")
   apply(simp add: lib_read_def all_updates_l lib_d_obs_t_def lib_d_obs_def)
  apply (intro allI impI conjI)
          apply (simp_all add: lib_syncing_def)
      apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def)
  apply(subgoal_tac "finite(snd ` {w. fst w = z \<and> w \<in> lib_writes cls})")
  apply (metis (mono_tags, lifting) Max.coboundedI dual_order.antisym fst_conv mem_Collect_eq rev_image_eqI snd_conv)
      apply(simp add: lib_wfs_def lib_writes_on_def lib_lastWr_def tst_def var_def)
      apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def lib_value_def)
      apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def lib_value_def)
      apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def lib_value_def)
  apply(simp add: lib_read_def all_updates_l lib_d_obs_def lib_d_obs_t_def lib_writes_on_def lib_lastWr_def lib_syncing_def lib_value_def tst_def var_def)
  done



lemma successful_CAS_lib_c_obs_lib_only_intro:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "\<not>[lib(x) \<approx>\<^sub>t' u] ls"
  and "[lib(y) =\<^sub>t v] ls"
  and "ls cs CAS\<^sup>R[lib(x), True, l, u]\<^sub>t ls' cs'"
  and "t \<noteq> t'"
  and "x \<noteq> y"
shows "[lib(x) = u]\<lparr>lib(y) =\<^sub>t' v\<rparr> ls'"
  using assms
  apply(simp add: lib_c_obs_lib_only_def lib_visible_writes_def)
  apply(simp add: lib_CAS_Rel_step_def, elim exE conjE, case_tac "lib_value ls (a, b) = l", simp_all)
  apply(simp add: lib_update_r_def all_updates_l)
  apply(intro allI impI conjI)
  apply(simp add: lib_d_obs_def lib_d_obs_t_def lib_p_obs_def lib_writes_on_def lib_lastWr_def lib_value_def tst_def var_def lib_visible_writes_def lib_valid_fresh_ts_def lib_releasing_def)
  apply safe
        apply (metis fst_conv) 
       apply (metis fst_conv)
  apply(simp add: lib_writes_on_def lib_value_def lib_releasing_def)
  apply(simp add: lib_writes_on_def lib_value_def lib_releasing_def)
    using a_is_x apply blast
  apply(simp add: lib_writes_on_def lib_value_def lib_releasing_def lib_d_obs_def lib_lastWr_def tst_def var_def)
      apply safe
    using a_is_x apply blast
    using a_is_x apply blast
  apply(simp add: lib_d_obs_def lib_d_obs_t_def lib_p_obs_def lib_writes_on_def lib_lastWr_def lib_value_def tst_def var_def lib_visible_writes_def lib_valid_fresh_ts_def lib_releasing_def )
    apply blast
   apply(simp add: lib_d_obs_def lib_d_obs_t_def lib_p_obs_def lib_writes_on_def lib_lastWr_def lib_value_def tst_def var_def lib_visible_writes_def lib_valid_fresh_ts_def lib_releasing_def )
   apply blast
   apply(simp add: lib_d_obs_def lib_d_obs_t_def lib_p_obs_def lib_writes_on_def lib_lastWr_def lib_value_def tst_def var_def lib_visible_writes_def lib_valid_fresh_ts_def lib_releasing_def )
   apply blast
   apply(simp add: lib_d_obs_def lib_d_obs_t_def lib_p_obs_def lib_writes_on_def lib_lastWr_def lib_value_def tst_def var_def lib_visible_writes_def lib_valid_fresh_ts_def lib_releasing_def )
   apply blast
    apply(simp add: lib_d_obs_def lib_d_obs_t_def lib_p_obs_def lib_writes_on_def lib_lastWr_def lib_value_def tst_def var_def lib_visible_writes_def lib_valid_fresh_ts_def lib_releasing_def )
    apply(simp add: lib_writes_on_def lib_value_def lib_releasing_def) 
    apply(simp add: lib_d_obs_def lib_d_obs_t_def lib_p_obs_def lib_writes_on_def lib_lastWr_def lib_value_def tst_def var_def lib_visible_writes_def lib_valid_fresh_ts_def lib_releasing_def )
  by blast



lemma successful_CAS_lib_c_obs_lib_diff_value_pres:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and  "[lib(x) = u]\<lparr>lib(y) =\<^sub>t' v\<rparr> ls"
  and "ls cs CAS\<^sup>R[lib(x), True, l, k]\<^sub>t ls' cs'"
  and "k \<noteq> u"
  and "t \<noteq> t'"
  and "x \<noteq> y"
shows "[lib(x) = u]\<lparr>lib(y) =\<^sub>t' v\<rparr> ls'"
  using assms
  apply(simp add: lib_c_obs_lib_only_def lib_visible_writes_def)
  apply(simp add: lib_CAS_Rel_step_def, elim exE conjE, case_tac "lib_value ls (a, b) = l", simp_all)
  apply(simp add: lib_update_r_def all_updates_l)
  apply(intro allI impI conjI)
  apply(simp add: lib_d_obs_def lib_d_obs_t_def lib_p_obs_def lib_writes_on_def lib_lastWr_def lib_value_def tst_def var_def lib_visible_writes_def lib_valid_fresh_ts_def lib_releasing_def)
    apply safe
  apply(simp add: lib_writes_on_def lib_value_def lib_releasing_def)
  apply(simp add: lib_writes_on_def lib_value_def lib_releasing_def)
    using a_is_x apply blast
  apply(simp add: lib_writes_on_def lib_value_def lib_releasing_def lib_d_obs_def lib_lastWr_def tst_def var_def)
      apply safe
    using a_is_x apply blast
    using a_is_x apply blast
  apply(simp add: lib_d_obs_def lib_d_obs_t_def lib_p_obs_def lib_writes_on_def lib_lastWr_def lib_value_def tst_def var_def lib_visible_writes_def lib_valid_fresh_ts_def lib_releasing_def)
    apply (metis fst_conv)
        apply (smt Collect_cong fst_conv)
   apply(simp add: lib_d_obs_def lib_d_obs_t_def lib_p_obs_def lib_writes_on_def lib_lastWr_def lib_value_def tst_def var_def lib_visible_writes_def lib_valid_fresh_ts_def lib_releasing_def )
    apply (metis fst_conv)
    apply(simp add: lib_d_obs_def lib_d_obs_t_def lib_p_obs_def lib_writes_on_def lib_lastWr_def lib_value_def tst_def var_def lib_visible_writes_def lib_valid_fresh_ts_def lib_releasing_def)
    apply (smt Collect_cong fst_conv)
    apply (metis CAS_Rel_preserves_releasing_new CAS_Rel_preserves_releasing_same_var CAS_Rel_preserves_value_old assms(4))
    by (metis CAS_Rel_preserves_releasing_new CAS_Rel_preserves_releasing_same_var CAS_Rel_preserves_value_old assms(4))



lemma successful_CAS_lib_c_obs_lib_pre_same_value_pres:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[lib(x) = u]\<lparr>lib(y) =\<^sub>t' v\<rparr> ls"
  and "[lib(y) =\<^sub>t v] ls"
  and "ls cs CAS\<^sup>R[lib(x), True, l, u]\<^sub>t ls' cs'"
  and "t \<noteq> t'"
  and "x \<noteq> y"
shows "[lib(x) = u]\<lparr>lib(y) =\<^sub>t' v\<rparr> ls'"
  using assms
  apply(simp add: lib_c_obs_lib_only_def lib_d_obs_t_def lib_visible_writes_def)
  apply(subgoal_tac "tst (lib_thrView ls' t' x) = tst (lib_thrView ls t' x)") defer
   apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
   apply(case_tac "lib_value ls (a, b) = l", simp_all)
  apply(simp add: lib_wfs_def lib_releasing_def lib_visible_writes_def var_def tst_def lib_valid_fresh_ts_def lib_update_r_def all_updates_l lib_writes_on_def lib_d_obs_def lib_value_def lib_lastWr_def)
   apply(intro  allI impI)
   apply(case_tac "(a, b) \<in> lib_writes_on ls x")
   apply(subgoal_tac "lib_value ls' (a, b) = lib_value ls (a, b) \<and> lib_modView ls' (a, b) LVARS = lib_modView ls (a, b) LVARS")
  apply(intro conjI)
  apply (smt last_CAS_R_diff_var lib_d_obs_def succ_CAS_preserves_last)
  using CAS_Rel_preserves_releasing_same_var apply auto[1]
  apply(intro conjI)
  using CAS_Rel_preserves_value_old apply blast
   apply(simp add: lib_CAS_Rel_step_def, elim exE conjE, case_tac "lib_value ls (aa, ba) = l", simp_all)
  apply(simp add: lib_update_r_def all_updates_l)
  using fresh_ts_not_in_writes lib_writes_on_def apply blast
   apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
   apply(case_tac "lib_value ls (aa, ba) = l", simp_all)
  apply(simp add:  lib_releasing_def lib_visible_writes_def var_def tst_def lib_valid_fresh_ts_def lib_update_r_def all_updates_l lib_writes_on_def lib_d_obs_def lib_value_def lib_lastWr_def)
  apply clarsimp
  apply(subgoal_tac "{w. fst w = y \<and>
                       (w = (x, ts') \<or>
                        w \<in> lib_writes ls)} = {w. fst w = y \<and>
                       (w \<in> lib_writes ls)}", simp)
    by auto


lemma "(x, b) \<in> lib_visible_writes cls t x \<Longrightarrow> (x, c) \<in> lib_visible_writes cls t x \<Longrightarrow>
     cvd[libx, m] cls \<Longrightarrow> (x, b) \<notin> lib_covered cls \<Longrightarrow> (x, c) \<notin> lib_covered cls \<Longrightarrow> b = c"
  apply(simp add:lib_wfs_def lib_update_r_def all_updates_l lib_lastWr_def lib_value_def lib_visible_writes_def  lib_covered_v_def )
  by blast


lemma visible_writes_singleton:
  assumes "lib_wfs cls ccs "
          and "cvd[libx, m] cls"
          and "(a, b) \<in> lib_visible_writes cls t x "
          and "(a, b) \<notin> lib_covered cls "
          and "lib_valid_fresh_ts cls (a, b) ts' "
          and "cls' =fst (lib_update_r t (a, b) u cls ccs ts')"
        shows "lib_visible_writes cls' t x = {(x, ts')}"
  using assms
  apply(subgoal_tac "b = Max (snd`lib_writes_on cls x)")
  defer
  apply(simp add:lib_wfs_def lib_update_r_def all_updates_l lib_lastWr_def lib_value_def   lib_covered_v_def )
    apply(simp add: lib_writes_on_def tst_def var_def lib_valid_fresh_ts_def lib_visible_writes_def)
  apply auto[1]
  apply(subgoal_tac "a = x") defer
  using a_is_x apply blast
  apply simp

  apply(simp add: lib_visible_writes_def)
  apply(subgoal_tac "tst (lib_thrView (fst (lib_update_r t (x, Max (snd ` lib_writes_on cls x)) u cls ccs ts')) t x) = ts'")
  defer
  apply(simp add: lib_update_r_def all_updates_l lib_lastWr_def lib_value_def   lib_covered_v_def )
  apply simp
  apply(subgoal_tac "lib_writes_on
           (fst (lib_update_r t (x, Max (snd ` lib_writes_on cls x)) u cls ccs ts')) x = 
lib_writes_on cls x \<union> {(x,ts')}") defer
  apply(simp add: lib_writes_on_def lib_update_r_def all_updates_l lib_lastWr_def lib_value_def   lib_covered_v_def )
  using Collect_cong var_def apply auto[1]
  apply simp
  apply(subgoal_tac "ts' > Max (snd`lib_writes_on cls x)")
  defer
  using assms(3) ts'_gt_max_writes_on apply blast
  apply(subgoal_tac "  {w. (w \<in> lib_writes_on cls x) \<and> ts' \<le> tst w} = {}")
   apply auto[1]
  apply(subgoal_tac "\<forall> w . w\<in>lib_writes_on cls x \<longrightarrow> tst w < ts'")
   apply force
  apply(intro allI impI)
  apply(subgoal_tac "tst w \<le> Max (snd ` lib_writes_on cls x)")
  using dual_order.strict_trans2 apply blast
  apply (simp add: tst_def lib_wfs_def)
  done



lemma lib_d_obs_same_t_c_obs:  "lib_wfs cls ccs \<Longrightarrow> x\<noteq>y \<Longrightarrow> [lib(y) =\<^sub>t v] cls \<Longrightarrow> cvd[libx, m] cls \<Longrightarrow> cls ccs CAS\<^sup>R[libx, True, m, u]\<^sub>t cls' ccs' \<Longrightarrow>[libx = u]\<lparr>liby =\<^sub>t v \<rparr> cls'"
 apply(simp add:  lib_d_obs_def lib_d_obs_t_def lib_c_obs_lib_only_def )
  apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
  apply(case_tac "lib_value cls (a, b) = m", simp_all)
  apply(subgoal_tac "a = x",simp)
  apply(subgoal_tac "lib_visible_writes (fst (lib_update_r t (a, b) u cls ccs ts')) t x = {(x,ts')}") defer
  using visible_writes_singleton  
  apply blast
   apply (simp add: a_is_x)
  apply simp
  apply(intro conjI impI)
  apply(simp add: lib_wfs_def lib_update_r_def all_updates_l lib_writes_on_def lib_value_def lib_lastWr_def
        var_def tst_def lib_visible_writes_def lib_valid_fresh_ts_def )
    apply (metis old.prod.inject prod.collapse)
  apply(simp add: lib_wfs_def lib_update_r_def all_updates_l lib_writes_on_def lib_value_def lib_lastWr_def
        var_def tst_def lib_visible_writes_def lib_valid_fresh_ts_def )
  apply (smt Collect_cong fst_conv)
  apply(simp add: lib_wfs_def lib_update_r_def all_updates_l lib_writes_on_def lib_value_def lib_lastWr_def
        var_def tst_def lib_visible_writes_def lib_valid_fresh_ts_def lib_releasing_def)
  done



lemma successful_CAS_lib_c_obs_lib_diff_value_press:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and  "[lib(x) = u]\<lparr>lib(y) =\<^sub>t v\<rparr> ls"
  and "ls cs CAS\<^sup>R[lib(x), True, l, k]\<^sub>t ls' cs'"
  and "k \<noteq> u"
  and "x \<noteq> y"
shows "[lib(x) = u]\<lparr>lib(y) =\<^sub>t v\<rparr> ls'"
  using assms
  apply(simp add: lib_CAS_Rel_step_def lib_c_obs_lib_only_def, elim exE conjE)
  apply(case_tac "lib_value ls (a, b) = l", simp_all)
  apply(simp add: lib_update_r_def all_updates_l lib_d_obs_def)
  apply safe
  using a_is_x apply blast
  using a_is_x apply blast
  using a_is_x apply blast
  using a_is_x apply blast
  using a_is_x apply blast
  using a_is_x apply blast
  using a_is_x apply blast
  using a_is_x apply blast
  using a_is_x apply blast
  apply(simp_all add: lib_valid_fresh_ts_def lib_lastWr_def lib_writes_on_def lib_value_def tst_def var_def lib_visible_writes_def)
  apply (smt Collect_cong dual_order.trans fst_conv leD linear)
   apply (smt Collect_cong dual_order.trans fst_conv leD linear)
  apply(simp add: lib_releasing_def)
  by auto

end