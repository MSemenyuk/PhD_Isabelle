theory AbstractLock_Proof_Rules
  imports AbstractLock_Lib OpSem_Proof_Rules Lib_ProofRules
begin


lemma lock_acqure_wfs_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "lock_acquire_step t x ls cs  ls' cs' res ver"
    shows "wfs cs'"
  using assms
  apply(simp add: lock_acquire_step_def lock_acquire_def lib_update_def lib_read_def)
  apply(elim exE conjE)
  apply(subgoal_tac "a = x", simp)
   defer
   apply(simp add:  lib_writes_on_def lib_visible_writes_def)
  apply(case_tac "even (lib_value ls (x, b))", simp_all)
   apply(simp add:  lib_writes_on_def lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def)
   apply(unfold wfs_def lib_update_def, simp)
     apply(simp add: lib_add_cv_def lib_update_thrView_def lib_update_modView_def lib_update_mods_def lib_lastWr_def lib_writes_on_def)
   apply(elim conjE)
   apply(case_tac "\<not>lib_releasing ls (x, b)", simp_all)
  apply(simp add: update_thrView_def)
  apply(simp add: update_thrView_def)
   apply(unfold writes_on_def ts_oride_def, simp)
   apply(intro allI impI conjI)
  apply(simp add: var_def lib_wfs_def)
  apply (simp add: var_def writes_on_def)
  apply(simp add:  lib_wfs_def)
  by (metis (no_types, lifting) mem_Collect_eq writes_on_def)


lemma lock_release_lib_wfs_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "lock_release_step t x ls cs  ls' cs'"
    shows "lib_wfs ls' cs'"
  using assms
  apply(simp add: lib_wfs_def lock_release_step_def lib_writes_on_def lock_release_def lib_write_def)
  apply(elim exE conjE)
  apply(simp add: lib_update_mods_def lib_update_modView_def lib_update_thrView_def lib_lastWr_def lib_writes_on_def)
  apply(intro conjI allI impI)
  apply(case_tac "xa=a", simp_all)
  using finite_lib_writes apply blast
  
  using finite_lib_writes_2 apply blast
    apply blast
  apply(case_tac "aa=a", simp_all)
    apply(case_tac "lib_lastWr ls a = (a, b)")
  apply(subgoal_tac "Max (tst `
                {w. var w = a \<and> (w = (a, ts') \<or> w \<in> lib_writes ls)}) = ts'", simp_all)
  apply(simp add: lib_valid_fresh_ts_def lib_writes_on_def)
  apply blast
     apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def)
     apply(subgoal_tac "finite ({w. fst w = a \<and> w \<in> lib_writes ls})")
      apply(subgoal_tac "{w. fst w = a \<and> w \<in> lib_writes ls} \<noteq> {}")
  apply(subgoal_tac "{w. fst w = a \<and> (w = (a, ts') \<or> w \<in> lib_writes ls)} = {w. fst w = a \<and> (w \<in> lib_writes ls)} \<union> {(a,ts')}")
        apply simp
  apply(subgoal_tac "ts' > Max (snd ` {w. fst w = a \<and> w \<in> lib_writes ls}) ")
         apply linarith
        apply(simp add: lib_valid_fresh_ts_def lib_writes_on_def)
  apply simp
  apply auto[1]
      apply blast+
    defer
  apply(simp add: tst_def var_def)
  apply(subgoal_tac "{w. fst w = aa \<and> (w = (a, ts') \<or> w \<in> lib_writes ls)} = {w. fst w = aa \<and> ( w \<in> lib_writes ls)}")  
     apply auto[1]
    apply auto[1]
   apply(simp add: tst_def var_def)
  apply(unfold wfs_def writes_on_def lastWr_def)
  using tst_def apply auto[1]

  apply(simp add: var_def tst_def lib_lastWr_def lib_valid_fresh_ts_def lib_writes_on_def)

  apply(subgoal_tac " Max (snd `
                {w. fst w = a \<and> (w = (a, ts') \<or> w \<in> lib_writes ls)}) =  Max (snd `
                {w. fst w = a \<and> (w \<in> lib_writes ls)})")
   apply simp
  apply(subgoal_tac "{w. fst w = a \<and> (w = (a, ts') \<or> w \<in> lib_writes ls)} = {w. fst w = a \<and> (w \<in> lib_writes ls)} \<union> {(a,ts')}")
   defer
  apply auto[1]
  apply simp
     apply(subgoal_tac "b < Max (snd ` {w. fst w = a \<and> w \<in> lib_writes ls}) ")
   defer
   apply(subgoal_tac "snd ` {w. fst w = a \<and> w \<in> lib_writes ls} \<noteq> {}")
    apply(subgoal_tac "finite (snd ` {w. fst w = a \<and> w \<in> lib_writes ls})")
     apply(subgoal_tac "b \<in>  (snd ` {w. fst w = a \<and> w \<in> lib_writes ls}) ")
      apply (simp add: member_less_max)
     apply(simp add: lib_visible_writes_def lib_writes_on_def) 
  defer  apply simp
   apply blast
     apply(subgoal_tac "ts' < Max (snd ` {w. fst w = a \<and> w \<in> lib_writes ls}) ")
   apply(subgoal_tac "snd ` {w. fst w = a \<and> w \<in> lib_writes ls} \<noteq> {}")
    apply(subgoal_tac "finite (snd ` {w. fst w = a \<and> w \<in> lib_writes ls})")
  apply auto[1]
  apply auto[1]
   apply blast
  apply(elim conjE)
  apply(erule_tac x = " Max (snd ` {w. fst w = a \<and> w \<in> lib_writes ls})" in allE)
  apply(subgoal_tac " (a, Max (snd ` {w. fst w = a \<and> w \<in> lib_writes ls}))
       \<in> lib_writes ls")
   apply blast
   apply(subgoal_tac "snd ` {w. fst w = a \<and> w \<in> lib_writes ls} \<noteq> {}")
   apply(subgoal_tac "finite (snd ` {w. fst w = a \<and> w \<in> lib_writes ls})")
  apply(subgoal_tac "Max (snd ` {w. fst w = a \<and> w \<in> lib_writes ls}) \<in> (snd ` {w. fst w = a \<and> w \<in> lib_writes ls})")
    apply force    
  apply auto[1]   
    apply blast+
proof -
fix a :: nat and b :: rat and ts' :: rat and aa :: nat
assume a1: "a = x \<and> (a, b) \<in> lib_writes ls \<and> tst (lib_thrView ls t x) \<le> b"
  assume "\<forall>a b. (a, b) \<in> lib_writes ls \<longrightarrow> lib_modView ls (a, b) LVARS a = (a, b)"
  assume "\<forall>a b x. fst (lib_modView ls (a, b) LVARS x) = x \<and> lib_modView ls (a, b) LVARS x \<in> lib_writes ls"
  have "(x, b) \<in> {p. fst p = x \<and> p \<in> lib_writes ls}"
    using a1 by auto
  then show "b \<in> snd ` {p. fst p = x \<and> p \<in> lib_writes ls}"
    by (metis (no_types) rev_image_eqI snd_conv)
qed



lemma lock_release_wfs_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "lock_release_step t x ls cs  ls' cs'"
    shows "wfs cs"
  using assms
  apply(simp add: lib_wfs_def lock_release_step_def lib_writes_on_def lock_release_def lib_write_def)
  done


lemma lock_acqure_unsuccessfulib_pres_d_obs:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "[lib(x) =\<^sub>t u] ls"
      and "lock_acquire_step t x ls cs  ls' cs' False ver"
  shows "[lib(x) =\<^sub>t u] ls'"
  using assms
 apply (simp add: lock_acquire_step_def lock_acquire_def lib_d_obs_t_def lib_d_obs_def)
  apply(elim exE conjE)
  apply(subgoal_tac "a = x", simp_all)
  apply safe
   apply(case_tac "even (lib_value ls (x, b))", simp)
   apply simp
  apply(simp add: lib_read_def lib_value_def  lib_update_thrView_def)
  by(simp add: lib_visible_writes_def lib_writes_on_def)
 

lemma lock_acqure_successful_pres_d_obs:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "[lib(x) =\<^sub>t u] ls"
      and "lock_acquire_step t x ls cs  ls' cs' True ver"
    shows "[lib(x) =\<^sub>t (u + 1) ] ls'"
  using assms
  apply(simp add: lib_d_obs_t_def lib_d_obs_def lock_acquire_step_def lock_acquire_def lib_update_def)
  apply(elim conjE exE)
  apply(simp add: lib_update_def all_updates_l var_def tst_def lib_lastWr_def lib_writes_on_def)
  apply(case_tac "even (lib_value ls (a, b))", simp_all)
  apply(subgoal_tac "finite {w. fst w = a \<and>  w \<in> lib_writes ls}")
   apply(subgoal_tac " {w. fst w = a \<and> w \<in> lib_writes ls} \<noteq> {}")
  apply(subgoal_tac " {w. fst w = a \<and> (w = (a, ts') \<or> w \<in> lib_writes ls)} =  {w. fst w = a \<and>  w \<in> lib_writes ls} \<union> {(a, ts')}")
     defer
  apply(simp add: lib_wfs_def lib_writes_on_def)
  using Collect_cong apply auto[1]
  apply(simp add: lib_wfs_def lib_writes_on_def)
  apply (metis prod.collapse var_def)
  apply(simp add: lib_wfs_def lib_writes_on_def) 
  using var_def apply auto[1]
  apply(subgoal_tac "lib_visible_writes ls t x = {lib_lastWr ls x}")
  apply(simp add: lib_value_def ts_oride_def lib_releasing_def tst_def var_def lib_visible_writes_def lib_writes_on_def lib_valid_fresh_ts_def )
  apply(intro conjI impI allI)
  apply(simp_all add: lib_wfs_def lib_writes_on_def var_def tst_def)
  using max.absorb2 apply auto[1]
  apply auto[1]
  using less_eq_rat_def apply auto[1]
      defer
  using less_eq_rat_def apply auto[1]
  using less_eq_rat_def apply auto[1]
  using less_eq_rat_def apply auto[1]
   apply (metis (no_types, lifting) max.absorb1 max.coboundedI2 max.strict_order_iff)  
   apply (meson assms(2) assms(3) d_obs_vw)
  apply(simp add: lib_lastWr_def lib_writes_on_def)
  apply(case_tac "b =  Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})", simp_all)
  
  apply(simp add: tst_def var_def)
  by (metis (no_types, lifting) antisym mem_Collect_eq singletonI snd_conv)

lemma lock_acqure_unsuccessful_client_pres_d_obs:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "[x =\<^sub>t v] cs"
      and "lock_acquire_step t y ls cs  ls' cs' False ver"
    shows "[x =\<^sub>t v ] cs'"
  using assms
  apply (simp add: lock_acquire_step_def lock_acquire_def )
  apply (elim exE conjE)
  apply(subgoal_tac "a = y", simp_all)
   apply (case_tac "even (lib_value ls (y, b))", simp_all)
  by (simp add: lib_visible_writes_def lib_writes_on_def)


lemma last_client_lock_acquire:
 assumes "wfs cs"
      and "lib_wfs ls cs"
      and "lock_acquire_step t y ls cs  ls' cs' res ver"
    shows "lastWr cs' x = lastWr cs x"
  using assms
  apply(simp add: lock_acquire_step_def lastWr_def)
  apply(simp add: lock_acquire_def)
  apply(elim exE conjE)
  apply(case_tac " even (lib_value ls (a, b))", simp_all)
  apply(simp add: lib_update_def)
  apply(simp add: update_thrView_def lib_add_cv_def lib_update_thrView_def lib_update_modView_def lib_update_mods_def  lib_writes_on_def)
  apply safe
  apply(case_tac "lib_releasing ls (a, b)", simp_all)
   apply(unfold writes_on_def)[1]
   by simp
  

lemma writes_client_lock_acquire:
 assumes "wfs cs"
      and "lib_wfs ls cs"
      and "lock_acquire_step t y ls cs  ls' cs' res ver"
    shows "writes_on cs x = writes_on cs' x"
  using assms
  apply(simp add: lock_acquire_step_def)
  apply (elim exE conjE)
  apply(simp add: lock_acquire_def)
  apply(case_tac " even (lib_value ls (a,b))", simp_all)
   apply(simp add: lib_update_def)
  apply(unfold writes_on_def)
  by(simp add: update_thrView_def lib_add_cv_def lib_update_thrView_def lib_update_modView_def lib_update_mods_def  lib_writes_on_def)


lemma mods_client_lock_acquire:
 assumes "wfs cs"
      and "lib_wfs ls cs"
      and "lock_acquire_step t y ls cs  ls' cs' res ver"
    shows "mods cs  = mods cs'"
  using assms
  apply(simp add: lock_acquire_step_def)
  apply (elim exE conjE)
  apply(simp add: lock_acquire_def)
  apply(case_tac " even (lib_value ls (a,b))", simp_all)
   by(simp add: lib_update_def update_thrView_def)

lemma lock_acqure_successfulib_client_pres_d_obs:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "[x =\<^sub>t v] cs"
      and "lock_acquire_step t y ls cs  ls' cs' True ver"
    shows "[x =\<^sub>t v ] cs'"
  using assms
  apply(simp add: d_obs_t_def d_obs_def)
  apply safe
  apply(simp add: lastWr_def)
   apply(subgoal_tac "writes_on cs' x = writes_on cs x")
  defer
  using writes_client_lock_acquire apply blast
   apply (simp add: last_client_lock_acquire mods_client_lock_acquire value_def)
  apply simp
  apply (simp add: lock_acquire_step_def lock_acquire_def lib_update_def)
  apply (elim conjE exE)
  apply(case_tac "even (lib_value ls (a, b))", simp_all)
  apply(simp add: lib_update_def all_updates_l)
  apply(case_tac "lib_releasing ls (a, b)", simp_all)
  apply(subgoal_tac "tst (thrView cs t x) \<ge> tst ((lib_modView ls (a, b) CVARS) x)")
  defer
   apply (simp add: lib_wfs_def)
  apply(subgoal_tac "ts_oride (thrView cs t) (lib_modView ls (a, b) CVARS) x = thrView cs t x")  
   apply simp
  apply(simp add: ts_oride_def)
  apply(intro impI)
  apply(unfold wfs_def writes_on_def, simp) 
  by (metis (no_types, lifting) antisym assms(1) lib_pair lib_wfs_def writes_on_var)


lemma lock_acquire_unsuccessful_p_obs:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "[lib(x) =\<^sub>t v] ls"
      and "\<not>[lib(x) \<approx>\<^sub>t' u] ls"
      and "u\<noteq>v "
      and "lock_acquire_step t x ls cs  ls' cs' False ver"
    shows "\<not>[lib(x) \<approx>\<^sub>t' u] ls'"
  using assms
    apply (simp add: lock_acquire_step_def lib_read_def lock_acquire_def)
  apply safe
 by(case_tac "even (lib_value ls (a, b))", simp_all)


lemma lock_acquire_unsuccessful_d_obs_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "[lib(x) =\<^sub>t' v] ls"
      and "lock_acquire_step t x ls cs  ls' cs' False ver"
    shows "[lib(x) =\<^sub>t' v] ls'"
  using assms
    apply (simp add: lock_acquire_step_def lib_read_def lock_acquire_def)
  apply(elim exE conjE)
  by(case_tac "even (lib_value ls (a,b))", simp_all)



lemma lock_acquire_unsuccessfulib_c_obs_pres:
  assumes "wfs cs"
  and "lib_wfs ls cs"
and "[lib(y) = v]\<lparr>x =\<^sub>t u\<rparr> ls cs"
      and "lock_acquire_step t' y ls cs  ls' cs' False ver"
    shows "[lib(y) = v]\<lparr>x =\<^sub>t u\<rparr> ls' cs'"
  using assms
      apply (simp add: lock_acquire_step_def lib_read_def lock_acquire_def)
  apply safe
  by(case_tac "even (lib_value ls (a,b))", simp_all)

lemma lock_acquire_successfulib_version:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "odd m"
      and "even n"
      and "\<forall> z . z\<notin>{m,n} \<longrightarrow> \<not>[lib(x) \<approx>\<^sub>t z] ls "
      and "lock_acquire_step t x ls cs  ls' cs' True ver"
    shows "ver = n"
  using assms
  apply (simp add: lock_acquire_step_def lock_acquire_def)
  apply safe
  apply(case_tac "even (lib_value ls (a,b))", simp_all)
  apply(simp add: lib_update_def)
  apply(case_tac "lib_releasing ls (a,b)", simp_all)
  apply(simp add: lib_add_cv_def lib_update_modView_def lib_update_mods_def lib_update_thrView_def update_thrView_def)
  apply(simp add: lib_visible_writes_def lib_valid_fresh_ts_def lib_writes_on_def lib_p_obs_def lib_value_def)
  apply safe
  apply metis
  by (metis lib_p_obs_def)


lemma lock_acquire_successful_c_o_s:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "[lib(y) = n]\<lparr>x =\<^sub>t u\<rparr> ls cs"
      and "lock_acquire_step t y ls cs  ls' cs' True n"
    shows "[x =\<^sub>t u] cs'"
  using assms
  apply (simp add: lock_acquire_step_def lock_acquire_def)
  apply safe
  apply(case_tac "even (lib_value ls (a,b))", simp_all)
  apply(simp add: lib_update_def)
  apply(simp add: lib_add_cv_def lib_update_modView_def lib_update_mods_def lib_update_thrView_def update_thrView_def)
   apply(simp add: lib_visible_writes_def lib_valid_fresh_ts_def lib_writes_on_def lib_p_obs_def lib_value_def lib_c_obs_def d_obs_def d_obs_t_def)
  apply(simp add: lastWr_def lib_writes_on_def ts_oride_def)
  apply safe
   apply(unfold writes_on_def)
   apply simp_all
    apply(simp_all add: value_def)
  apply(simp add: lib_wfs_def lib_writes_on_def)
  apply(simp add: tst_def var_def)
  apply(unfold wfs_def writes_on_def, simp)
  apply clarsimp
  apply(subgoal_tac "tst (thrView cs t x) \<le> tst (lastWr cs x)")
   defer
  apply (meson assms(1) last_write_max wfs_def)
  by(simp add: tst_def var_def lastWr_def)

lemma lock_acquire_successful_c_o:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "odd m"
      and "even n"
      and "\<forall> z . z\<notin>{m,n} \<longrightarrow> \<not>[lib(x) \<approx>\<^sub>t z] ls "
      and "lock_acquire_step t x ls cs  ls' cs' True ver"
      and "[lib(x) = n]\<lparr>x =\<^sub>t u\<rparr> ls cs"
    shows "[x =\<^sub>t u] cs'"
  using assms
  apply (simp add: lock_acquire_step_def lock_acquire_def)
  apply safe
  apply(case_tac "even (lib_value ls (a,b))", simp_all)
  apply(simp add: lib_update_def)
  apply(case_tac "ver \<noteq> n", simp_all)
  apply (metis OpSem.null_def assms(3)  lib_p_obs_def numeral_2_eq_2)
  apply(case_tac "lib_releasing ls (a,b)", simp_all) 
  using assms(6) lock_acquire_successful_c_o_s apply blast
  using lib_c_obs_def by blast


lemma lock_acquire_successful_not_p_obs_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
and "\<not>[lib(x) \<approx>\<^sub>t u] ls"
 and "lock_acquire_step t x ls cs  ls' cs' False ver"
shows "\<not>[lib(x) \<approx>\<^sub>t u] ls'"
  using assms
  apply (simp add: lock_acquire_step_def lock_acquire_def)
  apply safe
  by(case_tac "even (lib_value ls (a,b))", simp_all)


lemma lock_acquire_unsuccessful_diff_t_d_p_obs_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
and "[x =\<^sub>t u] cs"
and "t \<noteq> t'"
 and "lock_acquire_step t' y ls cs  ls' cs' False ver"
shows "[x =\<^sub>t u] cs'"
  using assms
  apply (simp add: lock_acquire_step_def lock_acquire_def)
  apply safe
  by(case_tac "even (lib_value ls (a,b))", simp_all)



  lemma lock_acquire_successfulib_diff_t_d_p_obs_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "[x =\<^sub>t u] cs"
      and "t \<noteq> t'"
      and "lock_acquire_step t' y ls cs  ls' cs' True ver"
    shows "[x =\<^sub>t u] cs'"
  using assms
  apply (simp add: lock_acquire_step_def lock_acquire_def)
  apply safe
  apply(case_tac "even (lib_value ls (a,b))", simp_all)
  apply(simp add: d_obs_t_def d_obs_def lastWr_def lib_read_def)
  apply safe
   apply(simp_all add: lib_update_def update_thrView_def)
   apply safe
   apply(unfold writes_on_def)
   apply(case_tac "lib_releasing ls (a,b)", simp_all)
  by (simp add: value_def)


lemma lock_acquire_unsuccessfulib_cvd_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "cvd[lib(x), u] ls"
      and "lock_acquire_step t' x ls cs  ls' cs' False ver"
    shows "cvd[lib(x), u] ls'"
  using assms
  apply(simp add: lock_acquire_step_def lock_acquire_def)
  apply(elim exE)
  by(case_tac "even (lib_value ls (a,b))", simp_all)


lemma lock_acquire_successfulib_cvd:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "cvd[lib(x), u] ls"
      and "lock_acquire_step t' x ls cs  ls' cs' True ver"
    shows "cvd[lib(x), (u+1)] ls'"
   using assms
  apply(simp add: lock_acquire_step_def lock_acquire_def)
   apply(elim exE conjE)
   apply(case_tac "(a, b) \<noteq> lib_lastWr ls a")
   apply(simp add: lib_update_def all_updates_l lib_covered_v_def lib_visible_writes_def lib_writes_on_def lib_lastWr_def)
   apply blast
   apply(case_tac "even (lib_value ls (a, b))", simp_all)
   apply(simp add: lib_update_def all_updates_l lib_covered_v_def)
   apply(simp_all add: lib_writes_on_def lib_lastWr_def var_def tst_def lib_valid_fresh_ts_def)
   apply(subgoal_tac "a = x", simp_all)
   apply(subgoal_tac "finite {w. fst w = x \<and> w \<in> lib_writes ls}")
     apply(subgoal_tac "{w. fst w = x \<and> w \<in> lib_writes ls} \<noteq> {}")
      defer
   apply(simp add: lib_visible_writes_def lib_writes_on_def)
   apply blast
   apply(simp add: lib_wfs_def lib_writes_on_def)
   using var_def apply auto[1]
   apply(simp add: lib_visible_writes_def lib_writes_on_def)
   apply(subgoal_tac "{w. fst w = x \<and>
                      (w = (x, ts') \<or> w \<in> lib_writes ls)} = {w. fst w = x \<and>
                      (w \<in> lib_writes ls)} \<union> {(x, ts')}")
   defer
    apply auto[1]
   apply simp
   apply(intro allI conjI impI, case_tac "lib_releasing ls
                 (x, Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}))", simp_all)
      apply(elim conjE)
   apply(subgoal_tac "Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}) < ts'")
   apply(subgoal_tac "Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}) \<in> (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
   
        apply (meson max.strict_order_iff)
   apply(subgoal_tac "finite (snd `{w. fst w = x \<and> w \<in> lib_writes ls})")
   apply(subgoal_tac "(snd `{w. fst w = x \<and> w \<in> lib_writes ls}) \<noteq> {}")
   apply (meson Max_in)   
   apply force   
       apply blast
   apply(subgoal_tac "Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}) \<in> (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
   apply simp
   apply(subgoal_tac "finite (snd `{w. fst w = x \<and> w \<in> lib_writes ls})")
       apply(subgoal_tac "(snd `{w. fst w = x \<and> w \<in> lib_writes ls}) \<noteq> {}")
   apply auto[1]   
   apply simp   
      apply blast
     apply(simp add: lib_value_def lib_wfs_def lib_writes_on_def lib_visible_writes_def )
   apply(intro conjI impI, elim conjE)
     apply blast
   apply(elim conjE disjE)
     apply(simp add: lib_value_def lib_wfs_def lib_writes_on_def lib_visible_writes_def )
   apply (simp add: max.strict_order_iff)
     apply(simp add: lib_value_def lib_wfs_def lib_writes_on_def lib_visible_writes_def )
     apply(simp add: lib_value_def lib_wfs_def lib_writes_on_def lib_visible_writes_def )
   by auto
    


lemma lock_acquire_cvd_odd_false:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "cvd[lib(x), u] ls"
      and "odd u"
      and "lock_acquire_step t' x ls cs  ls' cs' res ver"
    shows "\<not>res"
  using assms
  apply(simp add: lock_acquire_step_def lib_covered_v_def lock_acquire_def)
  apply(elim conjE exE)
  apply(case_tac "even (lib_value ls (a,b))")
  apply(simp add: lib_visible_writes_def lib_writes_on_def lib_value_def)
  by auto


lemma lock_rel_c_obs_intro:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "\<not> [lib(y) \<approx>\<^sub>t' u] ls"
      and "[x =\<^sub>t m] cs"
      and "cvd[lib(y), v] ls"
      and "t \<noteq> t'"
      and "lock_release_step t y ls cs ls' cs'"
    shows "[lib(y) = u]\<lparr>x =\<^sub>t' m\<rparr> ls' cs'"
  using assms
  apply(simp add: lock_release_step_def lib_p_obs_def lib_d_obs_def lib_d_obs_t_def d_obs_def d_obs_t_def)
  apply(elim exE conjE)
  apply(simp add: lock_release_def lib_write_def lib_update_mods_def lib_update_modView_def lib_update_thrView_def)
  apply(simp add: lib_valid_fresh_ts_def lib_writes_on_def lib_visible_writes_def lib_c_obs_def d_obs_def)
  apply safe
    apply(simp add: lib_releasing_def)
   apply(simp add: lastWr_def value_def lib_value_def)
   apply(unfold writes_on_def)
   apply blast
    apply(simp add: lib_releasing_def lib_value_def)  
  by blast


lemma lock_acqure_lib_wfs_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "lock_acquire_step t x ls cs  ls' cs' res ver"
    shows "lib_wfs ls' cs'"
  using assms
  apply(simp add: lock_acquire_step_def)
  apply(elim exE conjE)
  apply(simp add: lock_acquire_def)
  apply(case_tac "even (lib_value ls (a, b))")
  apply(simp add: lib_update_def all_updates_l)
  apply(case_tac "lib_releasing ls (a, b)")
   apply(simp add: lib_wfs_def lib_writes_on_def)
   apply(intro allI conjI impI)
  apply(simp add: var_def ts_oride_def)
                 apply (simp add: ts_oride_def)
  apply(unfold writes_on_def var_def wfs_def ts_oride_def, simp)[1]
  apply(unfold writes_on_def var_def wfs_def ts_oride_def, simp)[1]
  apply(simp add: var_def ts_oride_def)
             apply (simp add: ts_oride_def)
  defer
  apply (metis (no_types, lifting) lib_visible_writes_def lib_writes_on_def mem_Collect_eq)
  
           apply blast
          apply(simp add: lib_valid_fresh_ts_def ts_oride_def)
          apply(intro impI)
          apply(subgoal_tac "lib_modView ls (a, b) LVARS a = (a,b)")
  apply(simp add: tst_def)
  apply (metis (no_types, lifting) lib_visible_writes_def lib_writes_on_def mem_Collect_eq)
          apply(simp add: lib_valid_fresh_ts_def ts_oride_def)
          apply(intro impI)
          apply(subgoal_tac "lib_modView ls (a, b) LVARS a = (a,b)")
  apply(simp add: tst_def)
  apply (metis (no_types, lifting) lib_visible_writes_def lib_writes_on_def mem_Collect_eq)
        apply blast
       apply(simp add: lib_lastWr_def lib_writes_on_def)
       apply(intro impI)
       apply(subgoal_tac "ts'>b")
  apply(subgoal_tac "ts' \<in> tst ` {w. var w = a \<and> (w = (a, ts') \<or> w \<in> lib_writes ls)}")
         apply(subgoal_tac "finite (tst ` {w. var w = a \<and> (w = (a, ts') \<or> w \<in> lib_writes ls)})")
  apply(simp add: var_def tst_def)
  using Max_less_iff not_max apply blast
         apply (simp add: finite_lib_writes)
        apply(simp add: tst_def var_def)
  apply(subgoal_tac " (a, ts')\<in>{w. fst w = a \<and> (w = (a, ts') \<or> w \<in> lib_writes ls)}")
  apply (simp add: image_iff)
        apply auto[1]
       apply(simp add: lib_valid_fresh_ts_def)
      apply(simp add: lib_lastWr_def lib_writes_on_def)
      apply(case_tac "xa \<noteq> a", simp_all)
  apply(subgoal_tac "{w. var w = xa \<and> (w = (a, ts') \<or> w \<in> lib_writes ls)} = {w. var w = xa \<and> w \<in> lib_writes ls}")
        apply simp
  apply(simp add: var_def)
       apply auto[1]
      defer
      apply(simp add: tst_def lastWr_def ts_oride_def var_def)
      apply(unfold writes_on_def var_def wfs_def, simp)[1] 
     apply(simp add: tst_def lastWr_def ts_oride_def var_def)
     apply(unfold writes_on_def var_def wfs_def, simp)[1]
  apply(simp add: lib_wfs_def lib_writes_on_def)
    apply(intro conjI impI allI)
         defer
  apply(simp add: lib_visible_writes_def)
  using lib_writes_on_def apply auto[1]
        apply blast
       apply(simp add: lib_lastWr_def lib_writes_on_def)
       apply(intro impI)
       apply(simp add: tst_def var_def lib_visible_writes_def lib_writes_on_def)
  defer
       apply(simp add: lib_lastWr_def lib_writes_on_def)
       apply(simp add: tst_def var_def lib_visible_writes_def lib_writes_on_def)
       defer
  apply(unfold wfs_def writes_on_def, simp)[1]
       apply (meson assms(1) last_write_max wfs_def)
      defer
      apply(case_tac "lib_lastWr ls a = (a,b)")
  apply(subgoal_tac "b = Max (tst ` {w. var w = a \<and>  w \<in> lib_writes ls})", simp_all)
        apply(subgoal_tac "ts' > b", simp_all)
         apply(subgoal_tac "ts'= Max (tst ` {w. var w = a \<and> (w = (a, ts') \<or> w \<in> lib_writes ls)})", simp_all)
  apply(simp add: lib_valid_fresh_ts_def lib_writes_on_def)
          apply blast
  apply(simp add: lib_valid_fresh_ts_def lib_writes_on_def)
        apply(subgoal_tac "ts' > Max (tst ` {w. var w = a \<and>  w \<in> lib_writes ls})", simp_all)
  apply(subgoal_tac " {w. var w = a \<and> (w = (a, ts') \<or> w \<in> lib_writes ls)} =  {w. var w = a \<and> ( w \<in> lib_writes ls)} \<union> {(a, ts')}")
          apply(subgoal_tac " finite {w. var w = a \<and> ( w \<in> lib_writes ls)}")
          apply(subgoal_tac "{w. var w = a \<and> ( w \<in> lib_writes ls)} \<noteq> {}")
          apply simp
  apply (metis (no_types, lifting) lib_visible_writes_def lib_writes_on_def max.strict_order_iff mem_Collect_eq)
  apply blast
  apply blast
  apply(simp add: var_def lib_valid_fresh_ts_def lib_writes_on_def)
  apply auto[1]
  apply(simp add: var_def lib_valid_fresh_ts_def lib_writes_on_def)
       apply (simp add: lib_lastWr_def lib_writes_on_def)
      apply(subgoal_tac "lib_lastWr ls a \<in> lib_writes_on ls a")
      apply(subgoal_tac "b < tst (lib_lastWr ls a)")
      apply(subgoal_tac "ts' < tst (lib_lastWr ls a)")
         apply(simp add: lib_valid_fresh_ts_def lib_writes_on_def)
  apply(subgoal_tac "Max (tst ` {w. var w = a \<and> (w = (a, ts') \<or> w \<in> lib_writes ls)})
= Max (tst ` {w. var w = a \<and>  w \<in> lib_writes ls})")
          apply simp
  apply(subgoal_tac " {w. var w = a \<and> (w = (a, ts') \<or> w \<in> lib_writes ls)} =  {w. var w = a \<and> ( w \<in> lib_writes ls)} \<union> {(a, ts')}")
          apply(subgoal_tac " finite {w. var w = a \<and> ( w \<in> lib_writes ls)}")
           apply(subgoal_tac "{w. var w = a \<and> ( w \<in> lib_writes ls)} \<noteq> {}")
apply (simp add: var_def tst_def lib_lastWr_def lib_writes_on_def)
apply (simp add: var_def tst_def lib_lastWr_def lib_writes_on_def)  
  apply blast
  apply blast
apply (simp add: var_def tst_def lib_lastWr_def lib_writes_on_def)  
  using Collect_cong apply auto[1]
        apply (simp add: var_def tst_def lib_lastWr_def lib_writes_on_def lib_valid_fresh_ts_def)
       apply (simp add: var_def tst_def lib_visible_writes_def  lib_lastWr_def lib_writes_on_def lib_valid_fresh_ts_def)

       apply(elim conjE, simp add: lib_value_def)
  apply(erule_tac x = "Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})" in allE, simp)
  apply(subgoal_tac "finite {w. fst w = x \<and> w \<in> lib_writes ls}")
  apply(subgoal_tac "{w. fst w = x \<and> w \<in> lib_writes ls} \<noteq> {}")
  apply(subgoal_tac "b \<in> snd `{w. fst w = x \<and> w \<in> lib_writes ls}")
  apply(subgoal_tac "Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}) \<in> snd `{w. fst w = x \<and> w \<in> lib_writes ls}")
  apply simp
           apply (simp add: member_less_max)
  using Max_in apply blast
  
  apply (simp add: image_iff)
  apply blast

       apply blast
      apply(simp add: lib_lastWr_def lib_writes_on_def)
      apply(simp add: var_def tst_def lib_visible_writes_def lib_writes_on_def)
      apply(elim conjE)
  apply(subgoal_tac "finite( snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
  apply(subgoal_tac "snd ` {w. fst w = x \<and> w \<in> lib_writes ls} \<noteq> {}")
        defer  
  apply blast
       apply blast
  apply(case_tac "xa = a", simp_all)
  apply (simp add: finite_lib_writes)
      apply (simp add: finite_lib_writes_2)
     apply(simp add: lib_valid_fresh_ts_def lib_writes_on_def)
     apply(elim conjE)
      apply(case_tac "lib_lastWr ls x = (x,b)")
  apply(subgoal_tac "b = Max (tst ` {w. var w = x \<and>  w \<in> lib_writes ls})", simp_all)
        apply(subgoal_tac "ts' > b")
       apply(subgoal_tac "ts'= Max (tst ` {w. var w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)})", simp_all)
  
  using tst_def var_def apply force

        apply(subgoal_tac "ts' > Max (tst ` {w. var w = x \<and>  w \<in> lib_writes ls})")
  apply(subgoal_tac " {w. var w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)} =  {w. var w = x \<and> ( w \<in> lib_writes ls)} \<union> {(x, ts')}")
          apply(subgoal_tac " finite {w. var w = x \<and> ( w \<in> lib_writes ls)}")
          apply(subgoal_tac "{w. var w = x \<and> ( w \<in> lib_writes ls)} \<noteq> {}")
          apply simp
          apply (metis (no_types, lifting) max.strict_order_iff )
  apply auto[1]
  using var_def apply auto[1]
       apply(simp add: var_def tst_def)
  apply auto[1]
      apply(simp add: var_def tst_def)
  apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def)
      apply(subgoal_tac "lib_lastWr ls x \<in> lib_writes_on ls x")
      apply(subgoal_tac "b < tst (lib_lastWr ls x)")
      apply(subgoal_tac "ts' < tst (lib_lastWr ls x)")
         apply(simp add: lib_valid_fresh_ts_def lib_writes_on_def)
  apply(subgoal_tac "Max (tst ` {w. var w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)})
= Max (tst ` {w. var w = x \<and>  w \<in> lib_writes ls})")
          apply simp
  apply(subgoal_tac " {w. var w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)} =  {w. var w = x \<and> ( w \<in> lib_writes ls)} \<union> {(x, ts')}")
          apply(subgoal_tac " finite {w. var w = x \<and> ( w \<in> lib_writes ls)}")
           apply(subgoal_tac "{w. var w = x \<and> ( w \<in> lib_writes ls)} \<noteq> {}")
apply (simp add: var_def tst_def lib_lastWr_def lib_writes_on_def)
apply (simp add: var_def tst_def lib_lastWr_def lib_writes_on_def)  
           apply blast       
  apply(simp add: var_def) apply auto[1]
  apply(subgoal_tac " {w. var w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)} =  {w. var w = x \<and> ( w \<in> lib_writes ls)} \<union> {(x, ts')}")
          apply(subgoal_tac " finite {w. var w = x \<and> ( w \<in> lib_writes ls)}")
          apply(subgoal_tac "{w. var w = x \<and> ( w \<in> lib_writes ls)} \<noteq> {}")
apply (simp add: var_def tst_def lib_lastWr_def lib_writes_on_def)  
          apply blast+
  apply (simp add: var_def)
apply (simp add: var_def tst_def )  
        apply auto[1]
apply (simp add: var_def tst_def lib_lastWr_def lib_writes_on_def)  

      apply(simp add:  tst_def lib_lastWr_def lib_writes_on_def var_def)
          apply(subgoal_tac " finite {w. fst w = x \<and> ( w \<in> lib_writes ls)}")
          apply(subgoal_tac "{w. fst w = x \<and> ( w \<in> lib_writes ls)} \<noteq> {}")
  apply (simp add: image_iff member_less_max)
       apply blast+
     apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def)
  apply(subgoal_tac "finite ( (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}))")
      apply(subgoal_tac " (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}) \<noteq> {}")
       defer
       apply blast+

     apply(case_tac "xa = x")
      apply(elim conjE, simp)
  apply(subgoal_tac "finite ((snd ` {w. fst w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)}))")
  apply(subgoal_tac "((snd ` {w. fst w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)})) \<noteq> {}")
    apply(subgoal_tac " {w. var w = x \<and>  (w = (x, ts') \<or> w \<in> lib_writes ls)} =  {w. var w = x \<and> ( w \<in> lib_writes ls)} \<union> {(x, ts')}")
      apply(case_tac "lib_lastWr ls x = (x, b)", simp_all)
  apply(case_tac "ts' = Max (snd ` {w. fst w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)})", simp_all)
  apply(simp add: lib_valid_fresh_ts_def lib_writes_on_def)
           apply blast
          apply(simp add: lib_valid_fresh_ts_def lib_writes_on_def)
          apply(case_tac "ts' < Max (snd ` {w. fst w = x \<and>  w \<in> lib_writes ls})")
  apply(simp add: lib_lastWr_def lib_writes_on_def var_def tst_def)
          apply (simp add: var_def tst_def lib_lastWr_def lib_writes_on_def)
apply(subgoal_tac "ts' > Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})", simp) 
  apply(subgoal_tac "ts' = Max (insert ts' (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}))")
              apply linarith
  using max_of_union [where s = "(snd ` {w. fst w = x \<and> w \<in> lib_writes ls})"]
  apply simp
  apply (metis (no_types, lifting) Max_insert Max_singleton finite_imageI)  
          apply blast+
  apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def)
  apply(subgoal_tac "Max (insert ts' (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})) = Max  (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
          apply simp
  apply(subgoal_tac "ts' <  Max  (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
  apply(subgoal_tac "finite ( (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}))")
  apply(subgoal_tac " (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}) \<noteq> {}")  
  using member_less_max apply auto[1]
           apply blast+
         apply(simp add: lib_valid_fresh_ts_def lib_writes_on_def)
         apply(elim conjE)
         apply(erule_tac x = "Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})" in allE)
         apply simp
         apply(subgoal_tac " (x, Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})) \<in> lib_writes ls")
         apply(subgoal_tac " b < Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
   apply(subgoal_tac "finite ( (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}))")
            apply(subgoal_tac " (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}) \<noteq> {}")
             apply blast
  using image_is_empty apply blast

           apply blast
   apply(subgoal_tac "b\<in> (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
   apply(subgoal_tac "finite ( (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}))")
            apply(subgoal_tac " (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}) \<noteq> {}")

  apply (simp add: member_less_max)

  apply blast+
  apply(subgoal_tac "(x,b)\<in> {w. fst w = x \<and> w \<in> lib_writes ls} ")
  apply (simp add: image_iff)
  
          apply simp
   apply(subgoal_tac "finite ( (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}))")
            apply(subgoal_tac " (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}) \<noteq> {}")
  apply(subgoal_tac "(x, Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}))\<in>{w. fst w = x \<and> w \<in> lib_writes ls}")
            apply blast
   apply(subgoal_tac "finite ( ( {w. fst w = x \<and> w \<in> lib_writes ls}))")
            apply(subgoal_tac " ( {w. fst w = x \<and> w \<in> lib_writes ls}) \<noteq> {}")
  apply(subgoal_tac "Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})\<in>snd ` {w. fst w = x \<and> w \<in> lib_writes ls}")
              apply (simp add: image_iff)
   apply(subgoal_tac "finite ( (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}))")
            apply(subgoal_tac " (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}) \<noteq> {}")
  apply simp  
              apply blast+ 
        apply(simp add: var_def tst_def lib_valid_fresh_ts_def lib_writes_on_def)
  apply auto[1]
       apply blast
  apply auto[1]
        apply(simp add: var_def tst_def lib_valid_fresh_ts_def lib_writes_on_def)
      defer
  apply(subgoal_tac "{w. fst w = xa \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)} = {w. fst w = xa \<and> (w \<in> lib_writes ls)}")
  apply simp
      apply auto[1]
  apply(case_tac "xa = a")
  apply (simp add: finite_lib_writes) 
     apply (simp add: finite_lib_writes_2)
  defer
    defer
    apply(subgoal_tac "finite (snd `{w. fst w = x \<and> (w \<in> lib_writes ls)})")
  apply(case_tac "(x, ts')\<in>{w. fst w = x \<and> (w \<in> lib_writes ls)}")
      apply blast
      apply(subgoal_tac " {w. var w = x \<and>  (w = (x, ts') \<or> w \<in> lib_writes ls)} =  {w. var w = x \<and> ( w \<in> lib_writes ls)} \<union> {(x, ts')}")
  apply simp
  using var_def apply auto[1]
apply auto[1]
    apply blast
  apply(subgoal_tac "(x, Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}))\<in> {w. fst w = x \<and> w \<in> lib_writes ls}")
    apply blast
   apply(subgoal_tac "finite ( snd`{w. fst w = x \<and> w \<in> lib_writes ls})")
  apply(subgoal_tac "snd` {w. fst w = x \<and> w \<in> lib_writes ls}\<noteq>{}")
  defer
  apply blast+
   apply(subgoal_tac "finite ( snd`{w. fst w = x \<and> w \<in> lib_writes ls})")
  apply(subgoal_tac "snd` {w. fst w = x \<and> w \<in> lib_writes ls}\<noteq>{}")
  defer
     apply blast+
   defer
  proof -
    fix a :: nat and b :: rat and ts' :: rat and aa :: nat and ba :: rat and xa :: nat
    assume a1: "finite (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})"
    assume a2: "snd ` {w. fst w = x \<and> w \<in> lib_writes ls} \<noteq> {}"
    obtain pp :: "(nat \<times> rat) set \<Rightarrow> (nat \<times> rat \<Rightarrow> rat) \<Rightarrow> rat \<Rightarrow> nat \<times> rat" where
      "\<forall>x0 x1 x2. (\<exists>v3. x2 = x1 v3 \<and> v3 \<in> x0) = (x2 = x1 (pp x0 x1 x2) \<and> pp x0 x1 x2 \<in> x0)"
      by moura
    then have f3: "Max (snd ` {p. fst p = x \<and> p \<in> lib_writes ls}) = snd (pp {p. fst p = x \<and> p \<in> lib_writes ls} snd (Max (snd ` {p. fst p = x \<and> p \<in> lib_writes ls}))) \<and> pp {p. fst p = x \<and> p \<in> lib_writes ls} snd (Max (snd ` {p. fst p = x \<and> p \<in> lib_writes ls})) \<in> {p. fst p = x \<and> p \<in> lib_writes ls}"
      using a2 a1 by (meson Max_in imageE)
    then have "fst (pp {p. fst p = x \<and> p \<in> lib_writes ls} snd (Max (snd ` {p. fst p = x \<and> p \<in> lib_writes ls}))) = x \<and> pp {p. fst p = x \<and> p \<in> lib_writes ls} snd (Max (snd ` {p. fst p = x \<and> p \<in> lib_writes ls})) \<in> lib_writes ls"
      by blast
    then show "(x, Max (snd ` {p. fst p = x \<and> p \<in> lib_writes ls})) \<in> lib_writes ls"
      using f3 by (metis (no_types) prod.collapse)
  next
    fix a :: nat and b :: rat and ts' :: rat and aa :: nat and ba :: rat and xa :: nat
    assume a1: "finite (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})"
    assume a2: "snd ` {w. fst w = x \<and> w \<in> lib_writes ls} \<noteq> {}"
    obtain pp :: "(nat \<times> rat) set \<Rightarrow> (nat \<times> rat \<Rightarrow> rat) \<Rightarrow> rat \<Rightarrow> nat \<times> rat" where
      "\<forall>x0 x1 x2. (\<exists>v3. x2 = x1 v3 \<and> v3 \<in> x0) = (x2 = x1 (pp x0 x1 x2) \<and> pp x0 x1 x2 \<in> x0)"
  by moura
  then have f3: "Max (snd ` {p. fst p = x \<and> p \<in> lib_writes ls}) = snd (pp {p. fst p = x \<and> p \<in> lib_writes ls} snd (Max (snd ` {p. fst p = x \<and> p \<in> lib_writes ls}))) \<and> pp {p. fst p = x \<and> p \<in> lib_writes ls} snd (Max (snd ` {p. fst p = x \<and> p \<in> lib_writes ls})) \<in> {p. fst p = x \<and> p \<in> lib_writes ls}"
  using a2 a1 by (meson Max_in imageE)
  then have "fst (pp {p. fst p = x \<and> p \<in> lib_writes ls} snd (Max (snd ` {p. fst p = x \<and> p \<in> lib_writes ls}))) = x \<and> pp {p. fst p = x \<and> p \<in> lib_writes ls} snd (Max (snd ` {p. fst p = x \<and> p \<in> lib_writes ls})) \<in> lib_writes ls"
  by blast
  then have "(x, Max (snd ` {p. fst p = x \<and> p \<in> lib_writes ls})) = pp {p. fst p = x \<and> p \<in> lib_writes ls} snd (Max (snd ` {p. fst p = x \<and> p \<in> lib_writes ls}))"
    using f3 by (metis (no_types) prod.collapse)
    then show "(x, Max (snd ` {p. fst p = x \<and> p \<in> lib_writes ls})) \<in> {p. fst p = x \<and> p \<in> lib_writes ls}"
      using f3 by presburger
  qed







lemma lock_acquire_successful_p_obs:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "[lib(x) =\<^sub>t v] ls"
      and "\<not>[lib(x) \<approx>\<^sub>t' u] ls"
      and "u \<ge> v + 2 "
      and "lock_acquire_step t x ls cs  ls' cs' True ver"
    shows "\<not>[lib(x) \<approx>\<^sub>t' u] ls'"
  using assms
  apply(subgoal_tac "[lib(x) =\<^sub>t (v+1)] ls'")
   defer 
  using lock_acqure_successful_pres_d_obs apply blast
  apply (case_tac "t = t'", simp_all)
  using d_obs_vw [where ls = ls' and t = t and x = x and u = "(Suc v)" and cs = cs'] 
  apply simp
    apply(simp add: lib_d_obs_t_def lib_d_obs_def lib_p_obs_def)
   apply(intro allI impI, elim conjE)
  apply(case_tac "(a, b) = lib_lastWr ls' x")
    apply simp
  using lock_acqure_lib_wfs_pres lock_acqure_wfs_pres apply blast
  apply(simp add: lock_acquire_step_def lock_acquire_def)
  apply(elim conjE exE)
  apply(case_tac "even (lib_value ls (a, b))")
  apply(simp add: lib_update_def all_updates_l)
  apply(case_tac "lib_releasing ls (a, b)", simp_all)
   apply(simp add: lib_p_obs_def lib_visible_writes_def lib_writes_on_def)
  apply(simp add: lib_value_def lib_d_obs_t_def lib_d_obs_def)
   apply(intro  impI)
  apply(subgoal_tac "(x, b) = lib_lastWr ls x")
    apply simp
   apply(elim conjE, simp)
  using ts_ge_last_is_last  apply blast
   apply(simp add: lib_p_obs_def lib_visible_writes_def lib_writes_on_def)
  apply(simp add: lib_value_def lib_d_obs_t_def lib_d_obs_def)
   apply(intro  impI)
  apply(subgoal_tac "(x, b) = lib_lastWr ls x")
    apply simp
   apply(elim conjE, simp)
  using ts_ge_last_is_last  by blast


lemma cvd_cvv_val:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "cvd[lib(l),x] ls"
      and "lock_acquire_step t l ls cs  ls' cs' True ver"
    shows "cvv[lib(l),x] ls'"
  using assms
 apply (simp add: lock_acquire_step_def lock_acquire_def all_updates_l lib_covered_v_def lib_covered_val_def lib_d_obs_t_def lib_d_obs_def)
  apply(elim exE conjE)
  apply(case_tac "even (lib_value ls (a, b))", simp_all)
  apply(simp add: lib_update_def)
  apply(simp add: all_updates_l  lib_lastWr_def lib_writes_on_def)
  apply(case_tac "lib_releasing ls (a,b)", simp_all)
   apply(intro conjI)
    apply(simp add: lib_value_def)
    apply(rule_tac x="b" in exI)
  apply(intro conjI impI)
   apply(simp add: lib_valid_fresh_ts_def)
      apply(simp add: lib_visible_writes_def)
  apply (metis (no_types, lifting) assms(3) lib_covered_v_def lib_lastWr_def lib_writes_on_def mem_Collect_eq prod.inject)
    apply(simp add: lib_visible_writes_def)
  apply (metis assms(3) lib_covered_v_def lib_lastWr_def lib_value_def prod.inject)
  apply(intro allI conjI impI)
   apply(simp add: lib_value_def)
  apply(intro conjI impI)
   apply(simp add: lib_visible_writes_def)
  using lib_writes_on_def apply blast
   apply(simp add: lib_visible_writes_def lib_writes_on_def)
  using lib_writes_on_def apply blast
   apply(intro conjI)
    apply(simp add: lib_value_def)
    apply(rule_tac x=b in exI)
  apply(intro conjI impI)
   apply(simp add: lib_valid_fresh_ts_def)
   apply(simp add: lib_visible_writes_def lib_writes_on_def)
  using lib_writes_on_def apply blast
   apply(simp add: lib_visible_writes_def lib_writes_on_def)
  using lib_writes_on_def apply blast
  apply(intro allI conjI impI)
   apply(simp add: lib_value_def)
  apply(intro conjI impI)
   apply(simp add: lib_visible_writes_def)
  using lib_writes_on_def apply blast
   apply(simp add: lib_visible_writes_def lib_writes_on_def)
  using lib_writes_on_def by blast

lemma cvv_lock_acquire_pres:
  assumes "wfs cs"
      and "l_wfs ls cs"
      and "cvv[lib(l),x] ls"
      and "lock_acquire_step t l ls cs  ls' cs' b ver"
    shows "cvv[lib(l),x] ls'"
  using assms
 apply (simp add: lock_acquire_step_def lock_acquire_def lib_update_def lib_covered_v_def lib_covered_val_def lib_d_obs_t_def lib_d_obs_def)
  apply(elim exE conjE)
  apply(case_tac "even (lib_value ls (a, ba))", simp_all)
  apply(simp add: lib_update_def)
   apply(simp add: all_updates_l   lib_lastWr_def lib_writes_on_def)
   apply(case_tac "lib_releasing ls (a, ba)", simp_all)
  apply(intro conjI)
     apply(rule_tac x = baa in exI)
  apply(intro conjI)
      apply blast
     apply(simp add: lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def lib_writes_on_def)
  apply(intro impI)
  using lib_writes_on_def apply blast
  apply(intro allI impI conjI)
     apply(simp add: lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def)
   using lib_writes_on_def less_Suc_eq apply blast
  apply(intro allI impI conjI)
     apply(rule_tac x = baa in exI)
  apply(intro conjI)
      apply blast
     apply(simp add: lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def lib_writes_on_def)
  apply(intro impI)
  using lib_writes_on_def apply blast
     apply(simp add: lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def)
   using lib_writes_on_def less_Suc_eq apply blast
   by blast


  lemma lock_acquire_successful_rv:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "[lib(l) =\<^sub>t u] ls"
      and "lock_acquire_step t l ls cs  ls' cs' True ver"
    shows "ver = u"
  using assms
  apply (simp add: lock_acquire_step_def lock_acquire_def)
  apply safe
  apply(case_tac "even (lib_value ls (a,b))", simp_all)
  apply(simp_all add: lib_update_def update_thrView_def)
  apply(case_tac "lib_releasing ls (a,b)", simp_all)
  apply(simp_all add:all_updates_l  lib_value_def   )
   apply(simp_all add: lib_d_obs_t_def lib_d_obs_def lastWr_def lib_read_def)
  apply (metis assms(3) lib_dobs_visible_writes_last lib_value_def)
  by (metis assms(3) lib_dobs_visible_writes_last lib_value_def)


lemma cvv_val:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "cvv[lib(l),x] ls"
      and "lock_acquire_step t l ls cs  ls' cs' True ver"
    shows "ver \<noteq> x"
  using assms
  apply (simp add: lock_acquire_step_def lock_acquire_def lib_d_obs_t_def lib_d_obs_def)
  apply(simp add: lib_covered_val_def)
  apply (elim exE conjE)
  apply(case_tac "even (lib_value ls (a,b))", simp_all)
  apply(simp add: lib_update_def)
  apply(simp add: all_updates_l lib_lastWr_def lib_writes_on_def)
  apply(case_tac "lib_releasing ls (a,b)", simp_all)
  apply(simp add: lib_value_def lib_visible_writes_def lib_writes_on_def)
  using lib_writes_on_def apply blast
  apply(case_tac "lib_releasing ls (a,b)", simp_all)
  apply(simp add: lib_value_def lib_visible_writes_def lib_writes_on_def)
    using lib_writes_on_def by blast



lemma cvv_release:
  assumes "lib_wfs ls cs"
      and "wfs cs" 
      and "cvv[lib(l),x] ls"
      and "lock_release_step t l ls cs ls' cs'"
    shows "cvv[lib(l),x] ls'"
  using assms
 apply (simp add: lock_release_step_def lock_release_def lib_covered_val_def lib_d_obs_t_def lib_d_obs_def)
  apply(elim conjE exE, intro conjI allI)
   apply(rule_tac x = a in exI)
   apply(rule_tac x = ba in exI)
   apply(intro conjI)
    apply(simp add: lib_write_def all_updates_l)
  apply(simp add:  lib_lastWr_def lib_writes_on_def)
    apply(simp add: lib_value_def  lib_lastWr_def lib_writes_on_def)
  using a_is_x lib_visible_writes_def lib_writes_on_def apply blast
     apply(simp add: lib_write_def all_updates_l)
  apply(simp add: lib_valid_fresh_ts_def lib_writes_on_def lib_value_def lib_visible_writes_def tst_def var_def)
   apply safe
  using lib_writes_on_def apply blast
     apply(simp add: lib_write_def all_updates_l)
  apply(simp add: lib_valid_fresh_ts_def lib_writes_on_def lib_value_def lib_visible_writes_def tst_def var_def)
  using less_SucI by blast




end