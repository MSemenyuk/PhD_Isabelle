theory Lib_ProofRules
imports Lib
begin 
 
lemmas [simp] = rev_app_def Let_def


lemma lib_dobs_visible_writes: "lib_wfs ls cs \<Longrightarrow> [lib(x) =\<^sub>t u] ls \<Longrightarrow> w\<in>lib_visible_writes ls t x \<Longrightarrow> lib_value ls w = u"
  apply(simp add: lib_visible_writes_def lib_value_def lib_d_obs_t_def lib_d_obs_def lib_lastWr_def)
  apply(simp add: lib_writes_on_def tst_def var_def)
  apply(elim conjE)
  apply(subgoal_tac "Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}) = snd w") 
   apply auto[1]
  apply(simp add: lib_wfs_def)
  apply(elim conjE)
  by (metis Max.coboundedI dual_order.antisym finite_imageI image_eqI lib_writes_on_def prod.collapse var_def)



lemma finite_lib_writes: "finite {w. var w = x \<and> w \<in> lib_writes ls} \<Longrightarrow>
         finite {w. var w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)}"
  apply(case_tac "(x, ts')\<in> lib_writes ls")
   apply (smt Collect_cong)
  apply(subgoal_tac " {w. var w = x \<and>
         (w = (x, ts') \<or> w \<in> lib_writes ls)} = {w. var w = x \<and> w \<in> lib_writes ls} \<union> {(x, ts')}")
   apply simp
  apply (simp add: var_def)
  using fstI by auto

lemma finite_lib_writes_2: "xa \<noteq> x \<Longrightarrow> finite  {w. var w = xa \<and> w \<in> lib_writes ls} \<Longrightarrow>
 finite  {w. var w = xa \<and>  (w = (x, ts') \<or> w \<in> lib_writes ls)}"
  apply(subgoal_tac "(x, ts') \<notin> {w. var w = xa \<and>  (w = (x, ts') \<or> w \<in> lib_writes ls)}")
   apply(simp add: var_def)
   apply (smt Collect_cong fstI)
  by(simp add: var_def)

lemma not_max: "finite s \<Longrightarrow> a \<in> s \<Longrightarrow> b \<in> s \<Longrightarrow> a < b \<Longrightarrow> Max s \<noteq> a"
  using Max_gr_iff by auto


lemma max_of_union: "s \<noteq> {} \<Longrightarrow> finite s \<Longrightarrow> (a::rat) > Max s \<Longrightarrow> Max (s \<union> {a}) = a "
  by (metis  Sup_fin.insert Sup_fin_Max Un_insert_right sup.strict_order_iff sup_bot.right_neutral)

lemma member_less_max: "finite s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> a \<in> s \<Longrightarrow> a \<noteq> Max s \<Longrightarrow> a < Max s"
  by (simp add: le_neq_trans)



lemma d_obs_vw: "wfs cs \<Longrightarrow> lib_wfs ls cs \<Longrightarrow> [lib(x) =\<^sub>t u] ls \<Longrightarrow> lib_visible_writes ls t x = {lib_lastWr ls x}"
 apply (simp add:  lib_d_obs_t_def lib_d_obs_def lib_visible_writes_def lib_writes_on_def lib_lastWr_def)
  apply(simp add: lib_value_def lib_wfs_def lib_writes_on_def tst_def var_def)
  apply safe
      apply simp
  defer
     apply simp_all
   apply metis
  apply(subgoal_tac "b\<in>snd ` {w. fst w = a \<and> w \<in> lib_writes ls}")
  apply (meson Max_ge eq_iff finite_imageI)
  by (simp add: image_iff)




lemma lib_pair: "lib_wfs ls cs \<Longrightarrow> wfs cs \<Longrightarrow> lib_modView ls w CVARS x = (var (lib_modView ls w CVARS x), tst (lib_modView ls w CVARS x))"
  apply(simp add: lib_wfs_def tst_def var_def)
  done



lemma d_obs_visible_writes: "wfs cs \<Longrightarrow> lib_wfs ls cs \<Longrightarrow> [lib(x) =\<^sub>t u] ls \<Longrightarrow> lib_visible_writes ls t x = {lib_lastWr ls x}"
  by (simp add: d_obs_vw)




lemma step_pres_lib_wfs:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "step t a cs cs'"
    shows "lib_wfs ls cs'"
  apply(rule step_cases[OF assms(3)])
 using assms(1,2)
    apply(simp add: read_trans_def lib_wfs_def update_thrView_def)
    apply(unfold wfs_def writes_on_def, simp)[1]
     apply(simp add: lastWr_def)
     apply(unfold wfs_def writes_on_def, simp)[1]   
  using assms(1,2)
 apply clarsimp
  apply(subgoal_tac "aa = x", simp_all)
    apply(simp add: lib_wfs_def)
    apply(intro allI impI)
    apply(simp add: lastWr_def)
    apply(unfold wfs_def  writes_on_def write_trans_def all_updates_c tst_def var_def, simp)[1]
    apply(case_tac "x \<noteq> l", simp_all)
     apply(subgoal_tac "{w. fst w = l \<and>
                   (w = (x, ts') \<or> w \<in> surrey_state.writes cs)} = {w. fst w = l \<and>
                    w \<in> surrey_state.writes cs}")
  apply simp
     apply auto[1]
  apply(subgoal_tac "{w. fst w = l \<and>
                   (w = (l, ts') \<or> w \<in> surrey_state.writes cs)} = {w. fst w = l \<and>
                   (w \<in> surrey_state.writes cs)} \<union> { (l, ts')}")
     apply simp
  apply(subgoal_tac "{w. fst w = l \<and>
                   (w \<in> surrey_state.writes cs)} \<noteq> {}") 
     apply(subgoal_tac "finite {w. fst w = l \<and>
                   (w \<in> surrey_state.writes cs)}")
  apply auto[1]
  apply simp 
  apply (metis (mono_tags, lifting) empty_iff mem_Collect_eq)
  using visible_var apply fastforce
  using assms(1,2)
 apply clarsimp
  apply(subgoal_tac "aa = x", simp_all)
    apply(simp add: lib_wfs_def)
    apply(intro conjI allI impI)
    apply(simp add: lastWr_def)
    apply(unfold wfs_def  writes_on_def update_trans_def all_updates_c tst_def var_def, simp)[1]
    apply(unfold wfs_def  writes_on_def update_trans_def all_updates_c tst_def var_def, simp)[1]

    apply(case_tac "x \<noteq> l", case_tac "releasing cs (x, b)", simp_all)
     apply(subgoal_tac "{w. fst w = l \<and>
                   (w = (x, ts') \<or> w \<in> surrey_state.writes cs)} = {w. fst w = l \<and>
                    w \<in> surrey_state.writes cs}")
      apply (simp add: lastWr_def)
  apply(unfold writes_on_def var_def tst_def , simp)[1]
     apply auto[1]
      apply (simp add: lastWr_def)
    apply(unfold writes_on_def var_def tst_def , simp)[1]
     apply(subgoal_tac "{w. fst w = l \<and>
                   (w = (x, ts') \<or> w \<in> surrey_state.writes cs)} = {w. fst w = l \<and>
                    w \<in> surrey_state.writes cs}")
     apply auto[1]
  apply auto[1]
   apply(case_tac "releasing cs (l, b)", simp_all add: lastWr_def)
    apply(unfold writes_on_def var_def tst_def , simp)[1]
    apply(subgoal_tac "{w. fst w = l \<and>
                   (w = (l, ts') \<or> w \<in> surrey_state.writes cs)} = {w. fst w = l \<and>
                   (w \<in> surrey_state.writes cs)} \<union> { (l, ts')}")
     apply simp
  apply(subgoal_tac "{w. fst w = l \<and>
                   (w \<in> surrey_state.writes cs)} \<noteq> {}") 
     apply(subgoal_tac "finite {w. fst w = l \<and>
                   (w \<in> surrey_state.writes cs)}")
  apply auto[1]
     apply simp 
  apply(simp add: visible_writes_def lib_writes_on_def)
  using writes_on_def apply auto[1]
    apply(unfold writes_on_def var_def tst_def , simp)[1]
    apply(subgoal_tac "{w. fst w = l \<and>
                   (w = (l, ts') \<or> w \<in> surrey_state.writes cs)} = {w. fst w = l \<and>
                   (w \<in> surrey_state.writes cs)} \<union> { (l, ts')}")
     apply simp
  apply(subgoal_tac "{w. fst w = l \<and>
                   (w \<in> surrey_state.writes cs)} \<noteq> {}") 
     apply(subgoal_tac "finite {w. fst w = l \<and>
                   (w \<in> surrey_state.writes cs)}")
  apply auto[1]
     apply simp   
  apply(simp add: visible_writes_def lib_writes_on_def)
  using writes_on_def apply auto[1]
  using visible_var by fastforce




lemma lib_p_obs_read:
  assumes "wfs cs"
and "lib_wfs ls cs"
and "lib_read_step t x b ls cs ls' cs' v"
shows "[lib(x) \<approx>\<^sub>t v] ls'"
  using assms
  apply(simp add: lib_read_step_def lib_read_def lib_p_obs_def)
  apply (elim exE conjE)
  apply(case_tac "lib_syncing ls (a, ba) b")
   defer
  apply(rule_tac x = a in exI)
   apply(rule_tac x = ba in exI)
  apply(simp add: lib_visible_writes_def lib_writes_on_def)
   apply(simp add: lib_update_thrView_def update_thrView_def lib_value_def lib_visible_writes_def)
  apply auto[1]
  apply(subgoal_tac "a = x")
   apply simp
  apply(simp add: lib_visible_writes_def)
     apply(rule_tac x = a in exI)
   apply(rule_tac x = ba in exI)
   apply simp
   apply (intro conjI)
     apply (simp add: lib_update_thrView_def lib_writes_on_def)
    defer
    apply (simp add: lib_update_thrView_def lib_value_def)  
  apply (simp add: lib_visible_writes_def lib_writes_on_def)
  apply(elim conjE)
  apply(simp add: lib_update_thrView_def lib_wfs_def lib_writes_on_def)
  apply(elim conjE)
  apply(simp add: ts_oride_def)
  done

lemma lib_p_obs_read_prestate:
  assumes "wfs cs"
and "lib_wfs ls cs"
and "lib_read_step t x b ls cs ls' cs' v"
and "[lib(x) \<approx>\<^sub>t v] ls'"
shows "[lib(x) \<approx>\<^sub>t v] ls"
  using assms
  using lib_p_obs_def lib_read_step_def by blast


lemma ts_ge_last_is_last: "wfs cs \<Longrightarrow> lib_wfs ls cs \<Longrightarrow> (x, b) \<in> lib_writes ls \<Longrightarrow>
      tst (lib_lastWr ls x) \<le> b \<Longrightarrow> (x,b) = lib_lastWr ls x"
  apply(simp add: lib_writes_on_def lib_lastWr_def tst_def lib_wfs_def)
  apply(subgoal_tac "{w. var w = x \<and> w \<in> lib_writes ls} \<noteq> {}") 
   apply(subgoal_tac "finite {w. var w = x \<and> w \<in> lib_writes ls}")
  apply (metis (mono_tags, lifting) Max.coboundedI antisym finite_imageI image_iff mem_Collect_eq snd_eqD)
  apply blast
  by blast



(****************Covered Lemmas*********************)

lemma cvd_vw_val:  "wfs cs \<Longrightarrow> lib_wfs ls cs \<Longrightarrow> cvd[lib(x), v] ls \<Longrightarrow> w \<in> lib_visible_writes ls t x \<Longrightarrow>
       w \<notin> lib_covered ls \<Longrightarrow> lib_value ls w = v"
  apply(simp add: lib_visible_writes_def lib_value_def)
  by (metis lib_covered_v_def lib_value_def)

lemma write_sets_eq: "finite ({w. fst w = x \<and>  w \<in> s}) \<Longrightarrow>
  (x, ts')\<notin>{w. fst w = x \<and>  w \<in> s}  \<Longrightarrow> 
  {w. fst w = x \<and> (w = (x, ts') \<or> w \<in> s)} = {w. fst w = x \<and> w \<in> s} \<union> {(x, ts')}"
  apply(case_tac "{w. fst w = x \<and>  w \<in> s} = {}", simp)
   apply auto[1]
  by auto[1]

lemma finite_set_union_finite: "finite ({w. fst w = x \<and>  w \<in> s}) \<Longrightarrow>
  finite {w. fst w = x \<and> (w = (x, ts') \<or> w \<in> s)}"
  apply(subgoal_tac "{w. fst w = x \<and> (w = (x, ts') \<or> w \<in> s)} = {w. fst w = x \<and> w \<in> s} \<union> {(x, ts')}")
  using write_sets_eq
   apply simp
  apply(case_tac " (x, ts')\<notin>{w. fst w = x \<and>  w \<in> s}")
  apply (simp add: write_sets_eq)
  by blast

lemma "finite s \<Longrightarrow> m = Max s \<Longrightarrow> ts' > m \<Longrightarrow> Max( s \<union> {ts'}) = ts'"
  by (metis Max_insert Max_singleton Un_empty_right Un_insert_right max.strict_order_iff)

lemma lib_cvd_update_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "cvd[lib(x), v] ls"
      and "ls cs RMW[lib(x), v, v']\<^sub>t ls' cs'"
    shows "cvd[lib(x), v'] ls'"
  using assms
  apply(simp add: lib_update_step_def lib_update_def all_updates_l lib_covered_v_def )
  apply(elim conjE exE)
  apply(erule_tac x = a in allE)
  apply(erule_tac x = b in allE)
  apply(subgoal_tac "(a, b) \<in> lib_writes_on ls x") defer
  using lib_visible_writes_def apply blast
  apply simp
  apply(case_tac "lib_releasing ls (lib_lastWr ls x)", simp_all)
   apply(intro allI impI conjI, elim conjE)
    apply(simp add: lib_writes_on_def lib_lastWr_def)
  apply(simp add: lib_valid_fresh_ts_def lib_visible_writes_def lib_writes_on_def)
    apply(elim conjE disjE, simp)
     apply(simp add: var_def tst_def)
     apply(subgoal_tac "finite({w. fst w = x \<and> (w \<in> lib_writes ls)})")
     apply(subgoal_tac "finite({w. fst w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)})")
  apply(subgoal_tac " {w. fst w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)} =  ({w. fst w = x \<and> (w \<in> lib_writes ls)}) \<union> {(x,ts')}", simp)
      apply(subgoal_tac "ts'>b")
  apply (smt Max.coboundedI Max_insert2 dual_order.strict_trans finite_imageI less_eq_rat_def)
           apply linarith
  using finite_set_union_finite 
  apply auto[1]
      apply (simp add: finite_set_union_finite)
     apply(simp add: lib_wfs_def lib_writes_on_def var_def tst_def)
    apply(simp add: var_def tst_def)
  using assms(3) 
    apply(simp add: lib_covered_v_def)  
  apply(erule_tac x = "x" in allE)
  apply(erule_tac x = "ba" in allE)
    apply(erule_tac x = "ba" in allE)
    apply(simp add: lib_writes_on_def lib_lastWr_def)
  apply (simp add: tst_def var_def)
   apply(simp add: lib_writes_on_def lib_lastWr_def lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def)
  apply safe
  using assms(3) 
    apply(simp add: lib_covered_v_def)  
  apply(erule_tac x = "x" in allE)
  apply(erule_tac x = "ba" in allE)
    apply(erule_tac x = "ba" in allE)
    apply(simp add: lib_writes_on_def lib_lastWr_def)
   apply (simp add: tst_def var_def lib_lastWr_def lib_writes_on_def lib_value_def lib_visible_writes_def)
  using assms(3) 
    apply(simp add: lib_covered_v_def)  
  apply(erule_tac x = "x" in allE)
  apply(erule_tac x = "ba" in allE)
   apply(simp add: lib_writes_on_def lib_lastWr_def lib_value_def lib_valid_fresh_ts_def)
  apply(elim conjE disjE)
     apply(simp add: var_def tst_def)
     apply(subgoal_tac "finite({w. fst w = x \<and> (w \<in> lib_writes ls)})")
     apply(subgoal_tac "finite({w. fst w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)})")
  apply(subgoal_tac " {w. fst w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)} =  ({w. fst w = x \<and> (w \<in> lib_writes ls)}) \<union> {(x,ts')}", simp)
      apply(subgoal_tac "ts'>b")
  apply (smt Max.coboundedI Max_insert2 dual_order.strict_trans finite_imageI less_eq_rat_def)
           apply linarith
  using finite_set_union_finite 
  apply auto[1]
      apply (simp add: finite_set_union_finite)
  apply(simp add: lib_wfs_def lib_writes_on_def var_def tst_def)
  using tst_def var_def apply auto[1]
   apply(simp add: lib_writes_on_def lib_lastWr_def lib_value_def lib_valid_fresh_ts_def)
     apply(simp add: var_def tst_def)
  using assms(3) 
    apply(simp add: lib_covered_v_def) 
  apply(erule_tac x = "x" in allE)
  apply(erule_tac x = "ba" in allE)
  apply(simp add: lib_writes_on_def lib_lastWr_def lib_value_def lib_valid_fresh_ts_def)
  using tst_def var_def by auto


lemma f_a_i_cvd_pres:
  assumes "wfs (cs::surrey_state)"
      and "lib_wfs ls cs"
      and "cvd[lib(x), v] ls"
      and "lib_fetch_and_inc_step t x ls cs  ls' cs' res"
    shows "cvd[lib(x), (v+1)] ls'"
  using assms
  apply(simp add: lib_update_step_def lib_fetch_and_inc_step_def lib_update_def all_updates_l lib_covered_v_def )
  apply(elim conjE exE)
  apply(erule_tac x = a in allE)
  apply(erule_tac x = b in allE)
  apply(subgoal_tac "(a, b) \<in> lib_writes_on ls x") defer
  using lib_visible_writes_def apply blast
  apply simp
  apply(case_tac "lib_releasing ls (lib_lastWr ls x)", simp_all)
   apply(intro allI impI conjI, elim conjE)
    apply(simp add: lib_writes_on_def lib_lastWr_def)
  apply(simp add: lib_valid_fresh_ts_def lib_visible_writes_def lib_writes_on_def)
    apply(elim conjE disjE, simp)
     apply(simp add: var_def tst_def)
     apply(subgoal_tac "finite({w. fst w = x \<and> (w \<in> lib_writes ls)})")
     apply(subgoal_tac "finite({w. fst w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)})")
  apply(subgoal_tac " {w. fst w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)} =  ({w. fst w = x \<and> (w \<in> lib_writes ls)}) \<union> {(x,ts')}", simp)
      apply(subgoal_tac "ts'>b")
  apply (smt Max.coboundedI Max_insert2 dual_order.strict_trans finite_imageI less_eq_rat_def)
           apply linarith
  using finite_set_union_finite 
  apply auto[1]
      apply (simp add: finite_set_union_finite)
     apply(simp add: lib_wfs_def lib_writes_on_def var_def tst_def)
    apply(simp add: var_def tst_def)
  using assms(3) 
    apply(simp add: lib_covered_v_def)  
  apply(erule_tac x = "x" in allE)
  apply(erule_tac x = "ba" in allE)
    apply(erule_tac x = "ba" in allE)
    apply(simp add: lib_writes_on_def lib_lastWr_def)
  apply (simp add: tst_def var_def)
   apply(simp add: lib_writes_on_def lib_lastWr_def lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def)
  apply safe
  using assms(3) 
    apply(simp add: lib_covered_v_def)  
  apply(erule_tac x = "x" in allE)
  apply(erule_tac x = "ba" in allE)
    apply(erule_tac x = "ba" in allE)
    apply(simp add: lib_writes_on_def lib_lastWr_def)
   apply (simp add: tst_def var_def lib_lastWr_def lib_writes_on_def lib_value_def lib_visible_writes_def)
  using assms(3) 
    apply(simp add: lib_covered_v_def)  
  apply(erule_tac x = "x" in allE)
  apply(erule_tac x = "ba" in allE)
   apply(simp add: lib_writes_on_def lib_lastWr_def lib_value_def lib_valid_fresh_ts_def)
  apply(elim conjE disjE)
     apply(simp add: var_def tst_def)
     apply(subgoal_tac "finite({w. fst w = x \<and> (w \<in> lib_writes ls)})")
     apply(subgoal_tac "finite({w. fst w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)})")
  apply(subgoal_tac " {w. fst w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)} =  ({w. fst w = x \<and> (w \<in> lib_writes ls)}) \<union> {(x,ts')}", simp)
      apply(subgoal_tac "ts'>b")
  apply (smt Max.coboundedI Max_insert2 dual_order.strict_trans finite_imageI less_eq_rat_def)
           apply linarith
  using finite_set_union_finite 
  apply auto[1]
      apply (simp add: finite_set_union_finite)
  apply(simp add: lib_wfs_def lib_writes_on_def var_def tst_def)
  using tst_def var_def apply auto[1]
   apply(simp add: lib_writes_on_def lib_lastWr_def lib_value_def lib_valid_fresh_ts_def)
     apply(simp add: var_def tst_def)
  using assms(3) 
    apply(simp add: lib_covered_v_def) 
  apply(erule_tac x = "x" in allE)
  apply(erule_tac x = "ba" in allE)
  apply(simp add: lib_writes_on_def lib_lastWr_def lib_value_def lib_valid_fresh_ts_def)
  using tst_def var_def by auto

lemma lib_read_cvd_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "cvd[lib(x), v] ls"
      and "lib_read_step t y b ls cs ls' cs' u"
    shows "cvd[lib(x), v] ls'"
  using assms
  apply(simp add: lib_covered_v_def lib_read_step_def lib_read_def all_updates_l)
  apply(elim conjE exE, intro conjI impI allI, simp)
  apply(simp add: lib_writes_on_def lib_value_def lib_lastWr_def)
  apply blast
  apply(simp add: lib_writes_on_def lib_value_def lib_lastWr_def)
  by blast  

lemma lib_cvd_exist_write: "wfs cs \<Longrightarrow> lib_wfs ls cs \<Longrightarrow> cvd[lib(x), v] ls \<Longrightarrow> 
    \<exists> w . w\<in>lib_writes_on ls x \<and> lib_value ls w = v"
  apply(simp add: lib_covered_v_def)
  apply(subgoal_tac "\<exists>a b . lib_lastWr ls x = (a,b)")
  defer
   apply (metis surj_pair)
  apply(elim exE)
  apply(erule_tac x = a in allE)
  apply(erule_tac x = b in allE)
  apply(case_tac "(a,b) \<in>lib_covered ls")
   apply(simp add: lib_wfs_def)
  apply metis
  apply simp
  apply(subgoal_tac "(a, b) \<in> lib_writes_on ls x")
   apply auto[1]
  apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def lib_wfs_def)
  apply(elim conjE)
 apply(subgoal_tac " b \<in> tst ` {w. var w = x \<and> w \<in> lib_writes ls}") 
   apply (simp add: image_iff)
  apply(simp add: var_def tst_def)
  apply(subgoal_tac "finite (snd ` {w. fst w = a \<and> w \<in> lib_writes ls})")
  apply(subgoal_tac " (snd ` {w. fst w = a \<and> w \<in> lib_writes ls}) \<noteq> {}")
  using eq_Max_iff apply blast
  by blast+


lemma lib_cvd_exist_last_write: "wfs cs \<Longrightarrow> lib_wfs ls cs \<Longrightarrow> cvd[lib(x), v] ls \<Longrightarrow> 
    \<exists> w . w = lib_lastWr ls x \<and> lib_value ls w = v"
  apply(simp add: lib_covered_v_def )
  apply(subgoal_tac "\<exists> a b . (a,b) = lib_lastWr ls x")
   apply(elim exE conjE)
  apply(subgoal_tac "(a, b) \<in> lib_writes_on ls x \<and>
                 (a, b) \<notin> lib_covered ls")
    apply simp
   apply(simp add: lib_wfs_def lib_lastWr_def lib_writes_on_def tst_def var_def)
  apply(subgoal_tac "finite (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
    apply(subgoal_tac "(snd ` {w. fst w = x \<and> w \<in> lib_writes ls} \<noteq> {})")
  apply (smt Max_in image_iff mem_Collect_eq prod.collapse)
  apply blast
  apply blast 
  by (metis surj_pair)


lemma lib_last_in_visible_writes : "wfs cs \<Longrightarrow> lib_wfs ls cs \<Longrightarrow> lib_lastWr ls x \<in> lib_visible_writes ls t x"
  apply(simp add: lib_lastWr_def lib_visible_writes_def lib_wfs_def lib_writes_on_def  var_def tst_def)
  apply(subgoal_tac "finite (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
   apply(subgoal_tac "(snd ` {w. fst w = x \<and> w \<in> lib_writes ls} \<noteq> {})")
  apply (smt Max_in image_iff mem_Collect_eq prod.collapse)
  apply blast
  by blast 

lemma lib_cvd_exist_visible_write:
  assumes "wfs cs"
and " lib_wfs ls cs"
and " cvd[lib(x), v] ls"
shows"\<exists> w . w\<in>lib_visible_writes ls t x \<and> lib_value ls w = v"
  using assms
  apply(simp add: lib_covered_v_def)
  apply(subgoal_tac "\<exists>a b . lib_lastWr ls x = (a,b)")
  defer
   apply (metis surj_pair)
  apply(elim exE)
  apply(erule_tac x = a in allE)
  apply(erule_tac x = b in allE)
  apply(case_tac "(a,b) \<in>lib_covered ls")
   apply(simp add: lib_wfs_def)
  apply metis
  apply simp
  apply(subgoal_tac "(a, b) \<in> lib_writes_on ls x")
   apply auto[1]
  apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def lib_wfs_def)
  apply(elim conjE)
 apply(subgoal_tac " b \<in> tst ` {w. var w = x \<and> w \<in> lib_writes ls}") 
    apply (simp add: image_iff)
  apply(simp add: lib_visible_writes_def)
  apply(simp add: var_def tst_def)
  apply(subgoal_tac "finite (snd ` {w. fst w = a \<and> w \<in> lib_writes ls})")
     apply(subgoal_tac " (snd ` {w. fst w = a \<and> w \<in> lib_writes ls}) \<noteq> {}")
      apply(subgoal_tac "\<exists> w . w = lib_lastWr ls x \<and> lib_value ls w = v", elim exE)
  apply(simp add: lib_lastWr_def)
  apply (metis (mono_tags, lifting) Collect_cong Max_ge finite_imageI image_eqI lib_writes_on_def mem_Collect_eq var_def)
  using  lib_cvd_exist_last_write  
  using assms(2) assms(3) apply fastforce
  using eq_Max_iff apply blast
  apply blast
  apply (metis (mono_tags, lifting) mem_Collect_eq rev_image_eqI snd_conv tst_def var_def)
  apply(simp add: lib_lastWr_def lib_writes_on_def)
  apply(subgoal_tac "finite (snd ` {w. fst w = a \<and> w \<in> lib_writes ls})")
   apply(subgoal_tac " (snd ` {w. fst w = a \<and> w \<in> lib_writes ls}) \<noteq> {}")
  apply(subgoal_tac "b\<in>(snd ` {w. var w = x \<and> w \<in> lib_writes ls})")
  apply (simp add: image_iff)
    apply (metis (full_types)  Max_in tst_def var_def)  
  apply (metis empty_iff empty_is_image lib_covered_v_def lib_cvd_exist_write lib_writes_on_def var_def)
  by(simp add: lib_wfs_def var_def tst_def lib_writes_on_def)
  
lemma lib_enc_exist_visible_write:
  assumes "wfs cs"
and " lib_wfs ls cs"
and "en[lib(x), v]\<^sub>t ls"
shows"\<exists> w . w\<in>lib_writes_on ls x \<and> lib_value ls w = v"
  using assms
  apply(simp add: lib_covered_v_def lib_enc_def lib_enc_t_def)
  apply(subgoal_tac "\<exists>a b . lib_lastWr ls x = (a,b)")
  defer
   apply (metis surj_pair)
  apply(elim exE)
  by auto

(****************HELPER LEMMAS**********************)


lemma ts_eq_lastWr: "wfs cs \<Longrightarrow> lib_wfs ls cs \<Longrightarrow> (x, ts) \<in> lib_writes_on ls x \<Longrightarrow> tst (lib_lastWr ls x) \<le> ts \<Longrightarrow> ts = tst (lib_lastWr ls x)"
  apply(simp add: lib_lastWr_def lib_writes_on_def lib_value_def lib_wfs_def)
  apply(subgoal_tac "ts\<in> (tst ` {w. var w = x \<and> w \<in> lib_writes ls})")
   defer
  apply(simp add: var_def tst_def image_iff)
  by (meson Max_ge antisym finite_imageI)  



lemma exists_a_fresh_element: "finite s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> (a::rat) \<in> s \<Longrightarrow> \<exists>b . b > a \<and> (\<forall> c . c\<in>s \<and> c > a \<longrightarrow> b < c)"
  apply(case_tac "a = Max s")  
   apply (meson Max_gr_iff gt_ex)
  apply(case_tac "s = {a}")
   apply simp
  apply(subgoal_tac "\<exists> e1 . e1\<in>s \<and> e1>a \<and> \<not>(\<exists> e2. e2\<in>s \<and> e2>a \<and> e2<e1)")
  using dense apply auto[1]
   apply (metis antisym_conv3 dense less_trans)
  apply(case_tac "{e .e\<in>s \<and> e>a \<and> e<Max s} = {}")
   apply (metis (no_types, lifting) Max_gr_iff Max_in empty_Collect_eq less_le neqE)
  apply(rule_tac x = "Min {e .e\<in>s \<and> e>a \<and> e<Max s}" in exI)
  apply (intro conjI)
  apply (metis (no_types, lifting) Diff_eq_empty_iff Min_in finite_Diff2 mem_Collect_eq subsetI)
   apply simp
  apply simp 
  by (meson Max_gr_iff less_le)

lemma exist_lib_valid_fresh_ts: "wfs cs \<Longrightarrow> lib_wfs ls cs \<Longrightarrow> w\<in>lib_writes_on ls x \<Longrightarrow>  \<exists>ts'. lib_valid_fresh_ts ls w ts'"
  apply(simp add: lib_wfs_def  lib_valid_fresh_ts_def lib_writes_on_def  lib_lastWr_def)
  apply(elim conjE)
  apply(subgoal_tac "finite(snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
   defer
   apply (simp add: var_def)
  apply(subgoal_tac "tst w \<in> (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
  defer
   apply (simp add: tst_def var_def)
  apply(subgoal_tac "(snd ` {w. fst w = x \<and> w \<in> lib_writes ls}) \<noteq> {}")
   defer
  apply blast
  using exists_a_fresh_element [where s = "snd ` {w. fst w = x \<and> w \<in> lib_writes ls}" and
      a = "tst w"]
  apply simp
  apply(elim exE conjE)
    by (metis (mono_tags, lifting) fst_conv mem_Collect_eq rev_image_eqI snd_conv)

lemma f_a_i_pres_writes_on_diff_var: "wfs cs \<Longrightarrow> lib_wfs ls cs \<Longrightarrow> ls cs fetch-and-inc[v \<leftarrow> lib(x)]\<^sub>t ls' cs' \<Longrightarrow> x\<noteq>y \<Longrightarrow>
lib_writes_on ls y = lib_writes_on ls' y"
  apply(simp add: lib_fetch_and_inc_step_def lib_update_def all_updates_l lib_writes_on_def)
  apply(elim exE conjE) 
  apply(subgoal_tac "a = x", simp)
  apply(case_tac "lib_releasing ls (x, b)", simp_all)
  apply(simp add: var_def tst_def)
    apply auto[1]
  apply(simp add: var_def tst_def)
   apply auto[1]
  by(simp add: lib_visible_writes_def lib_writes_on_def)

lemma write_writes_on_diff_var: "wfs cs \<Longrightarrow> lib_wfs ls cs \<Longrightarrow> ls cs [lib(x) :=\<^sup>R v]\<^sub>t ls' cs' \<Longrightarrow> x\<noteq>y \<Longrightarrow>
lib_writes_on ls y = lib_writes_on ls' y"
  apply(simp add: lib_write_step_def lib_write_def all_updates_l lib_writes_on_def)
  apply(elim exE conjE) 
  apply(subgoal_tac "a = x", simp)
  apply(simp add: var_def tst_def)
    apply auto[1]
  by(simp add: lib_visible_writes_def lib_writes_on_def)

lemma f_a_i_pres_value: "wfs cs \<Longrightarrow> lib_wfs ls cs \<Longrightarrow> ls cs fetch-and-inc[v \<leftarrow> lib(x)]\<^sub>t ls' cs' \<Longrightarrow> w\<in>lib_writes_on ls y \<Longrightarrow>
lib_value ls w = lib_value ls' w"
  apply(simp add: lib_fetch_and_inc_step_def lib_update_def all_updates_l lib_writes_on_def)
  apply(elim exE conjE) 
  apply(subgoal_tac "a = x", simp)
   apply(case_tac "lib_releasing ls (x, b)", simp_all)
  apply(simp add: lib_value_def)
    apply(simp add: var_def tst_def lib_valid_fresh_ts_def lib_writes_on_def)
    apply(intro impI)
  apply blast
    apply auto[1]
    apply(simp add: var_def tst_def lib_valid_fresh_ts_def lib_writes_on_def lib_value_def)
    apply(intro impI)
  apply blast
  apply auto[1]
  by(simp add:lib_visible_writes_def lib_writes_on_def)


lemma write_pres_value: "wfs cs \<Longrightarrow> lib_wfs ls cs \<Longrightarrow> ls cs [lib(x) :=\<^sup>R v]\<^sub>t ls' cs' \<Longrightarrow> w\<in>lib_writes_on ls y \<Longrightarrow>
lib_value ls w = lib_value ls' w"
  apply(simp add: lib_write_step_def lib_write_def all_updates_l lib_writes_on_def)
  apply(elim exE conjE) 
  apply(subgoal_tac "a = x", simp)
  apply(simp add: lib_value_def)
    apply(simp add: var_def tst_def lib_valid_fresh_ts_def lib_writes_on_def)
    apply(intro impI)
  apply blast
    apply auto[1]
    apply(simp add: var_def tst_def lib_valid_fresh_ts_def lib_writes_on_def lib_value_def)
  apply auto[1]
  by(simp add:lib_visible_writes_def lib_writes_on_def)


lemma read_pres_writes_on_diff_var: "wfs cs \<Longrightarrow> lib_wfs ls cs \<Longrightarrow> lib_read_step t x b ls cs ls' cs' r  \<Longrightarrow>
lib_writes_on ls y = lib_writes_on ls' y"
  apply(simp add: lib_read_step_def lib_read_def all_updates_l lib_writes_on_def)
  apply(elim exE conjE) 
  apply(subgoal_tac "a = x", simp)
  by(simp add: lib_visible_writes_def lib_writes_on_def)


lemma read_pres_value: "wfs cs \<Longrightarrow> lib_wfs ls cs \<Longrightarrow> lib_read_step t x b ls cs ls' cs' r \<Longrightarrow> w\<in>lib_writes_on ls y \<Longrightarrow>
lib_value ls w = lib_value ls' w"
  apply(simp add: lib_read_step_def lib_read_def all_updates_l lib_writes_on_def lib_value_def)
  apply(elim exE conjE) 
  apply(subgoal_tac "a = x", simp)
  by(simp add:lib_visible_writes_def lib_writes_on_def)

lemma lib_f_a_i_last_diff_var_pres:
  assumes "lib_wfs ls cs" 
      and "wfs cs "
      and "w = lib_lastWr ls x"
      and "ls cs fetch-and-inc[v \<leftarrow> lib(y)]\<^sub>t ls' cs'"
      and "x \<noteq> y"
    shows "w = lib_lastWr ls' x"
  using assms
  apply(simp add: lib_fetch_and_inc_step_def lib_update_def all_updates_l)
  apply (elim conjE exE)
  apply(subgoal_tac "a = y", simp)
   apply(case_tac "lib_releasing ls (y, b)", simp_all)
    apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def)
  apply (metis fst_conv)
    apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def)
   apply (metis fst_conv)
  by(simp add: lib_visible_writes_def lib_writes_on_def)


lemma lib_read_last_diff_var_pres:
  assumes "lib_wfs ls cs" 
      and "wfs cs "
      and "w = lib_lastWr ls x"
      and "lib_read_step t y b ls cs ls' cs'' r"
    shows "w = lib_lastWr ls' x"
  using assms
  apply(simp add: lib_read_step_def lib_read_def all_updates_l)
  apply (elim conjE exE)
  apply(subgoal_tac "a = y", simp)
   apply(case_tac "lib_syncing ls (y, ba) b", simp_all)
    apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def)
    apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def)
  by(simp add: lib_visible_writes_def lib_writes_on_def)

lemma lib_f_a_i_writes_on_diff_var_pres:
  assumes "lib_wfs ls cs" 
      and "wfs cs "
      and "w \<in> lib_visible_writes ls' t x"
      and "ls cs fetch-and-inc[v \<leftarrow> lib(y)]\<^sub>t ls' cs'"
      and "x \<noteq> y"
    shows "w \<in> lib_visible_writes ls t x"
  using assms
  apply(simp add: lib_fetch_and_inc_step_def lib_update_def all_updates_l lib_visible_writes_def)
  apply (elim conjE exE)
  apply(subgoal_tac "a = y", simp)
   apply(case_tac "lib_releasing ls (y, b)", simp_all)
    apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def ts_oride_def)
  apply (smt fst_conv fun_upd_other order.trans)
   apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def ts_oride_def)
  apply auto[1]
  by(simp add: lib_visible_writes_def lib_writes_on_def)

lemma lib_f_a_i_writes_on_diff_var_pres_backwards:
  assumes "lib_wfs ls cs" 
      and "wfs cs "
      and "w = lib_writes_on ls' x"
      and "ls cs fetch-and-inc[v \<leftarrow> lib(y)]\<^sub>t ls' cs'"
      and "x \<noteq> y"
    shows "w = lib_writes_on ls x"
  using assms
  apply(simp add: lib_fetch_and_inc_step_def lib_update_def all_updates_l)
  apply (elim conjE exE)
  apply(subgoal_tac "a = y", simp)
   apply(case_tac "lib_releasing ls (y, b)", simp_all)
    apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def)
  apply auto[1]
    apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def)
   apply auto[1]
  by(simp add: lib_visible_writes_def lib_writes_on_def)


lemma lib_f_a_i_writes_on_diff_var_pres_backwards:
  assumes "lib_wfs ls cs" 
      and "wfs cs "
      and "w \<in> lib_writes_on ls' x"
      and "ls cs fetch-and-inc[v \<leftarrow> lib(y)]\<^sub>t ls' cs'"
    shows "w \<in> lib_writes_on ls x"
  using assms
  apply(simp add: lib_fetch_and_inc_step_def lib_update_def all_updates_l)
  apply (elim conjE exE)
  apply(subgoal_tac "a = y", simp)
   apply(case_tac "lib_releasing ls (y, b)", simp_all)
    apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def)
    apply auto[1]
  oops


lemma lib_read_writes_on_diff_var_pres_backwards:
  assumes "lib_wfs ls cs" 
      and "wfs cs "
      and "w = lib_writes_on ls' x"
      and "lib_read_step t y b ls cs ls' cs'' r"
    shows "w = lib_writes_on ls x"
  using assms
  apply(simp add: lib_read_step_def lib_read_def all_updates_l)
  apply (elim conjE exE)
  apply(subgoal_tac "a = y", simp)
   apply(case_tac "lib_syncing ls (y, ba) b", simp_all)
    apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def)
    apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def)
  by(simp add: lib_visible_writes_def lib_writes_on_def)


lemma lib_read_visible_writes_pres_backwards:
  assumes "lib_wfs ls cs" 
      and "wfs cs "
      and "w \<in> lib_visible_writes ls' t x"
      and "lib_read_step t y b ls cs ls' cs'' r"
    shows "w \<in> lib_visible_writes ls t x"
  using assms
  apply(simp add: lib_read_step_def lib_read_def all_updates_l)
  apply (elim conjE exE)
  apply(subgoal_tac "a = y", simp)
   apply(case_tac "lib_syncing ls (y, ba) b", simp_all)
  apply(simp add: lib_visible_writes_def lib_writes_on_def tst_def var_def)
    apply (smt dual_order.trans fun_upd_other fun_upd_same snd_conv ts_oride_def tst_def)
  apply(simp add: lib_visible_writes_def lib_writes_on_def tst_def var_def)
  apply (metis (mono_tags, hide_lams) order.trans snd_conv)
  by(simp add: lib_visible_writes_def lib_writes_on_def)


lemma lib_value_f_a_i_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "ls cs fetch-and-inc[u \<leftarrow> lib(y)]\<^sub>t ls' cs'"
      and "w\<in> lib_writes_on ls x"
      and "lib_value ls w = v"
    shows "lib_value ls' w = v"
  using assms
  apply(simp add: lib_fetch_and_inc_step_def lib_update_def all_updates_l lib_value_def lib_writes_on_def)
  apply(elim exE conjE)
   apply(simp add: lib_valid_fresh_ts_def lib_writes_on_def)
  apply(intro  impI)
  by blast


lemma lib_value_read_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "lib_read_step t y b ls cs ls' cs' r"
      and "w\<in> lib_writes_on ls x"
      and "lib_value ls w = v"
    shows "lib_value ls' w = v"
  using assms
  apply(simp add: lib_read_step_def lib_read_def all_updates_l lib_value_def lib_writes_on_def)
  apply(elim exE conjE)
   by(simp add: lib_valid_fresh_ts_def lib_writes_on_def)




lemma lib_w_in_writes_pres: "w\<in>lib_writes_on ls x \<Longrightarrow>  w\<in>lib_writes_on ls' x"
  oops

lemma lib_w_in_writes_f_a_i_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "ls cs fetch-and-inc[u \<leftarrow> lib(y)]\<^sub>t ls' cs'"
      and "w\<in>lib_writes_on ls x"
    shows "w\<in>lib_writes_on ls' x"
  using assms
  apply(simp add: lib_fetch_and_inc_step_def lib_update_def all_updates_l lib_value_def lib_writes_on_def)
  apply(elim exE conjE)
   apply(simp add: lib_valid_fresh_ts_def lib_writes_on_def)
  done


lemma lib_w_in_writes_read_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "lib_read_step t y b ls cs ls' cs' r"
      and "w\<in>lib_writes_on ls x"
    shows "w\<in>lib_writes_on ls' x"
  using assms
  apply(simp add: lib_read_step_def lib_read_def all_updates_l lib_value_def lib_writes_on_def)
  apply(elim exE conjE)
   by(simp add: lib_valid_fresh_ts_def lib_writes_on_def)




(*TODO: instantiate ls*)
lemma lib_enc_pres: "en[lib(x), u]\<^sub>t ls \<Longrightarrow> en[lib(x), u]\<^sub>t ls'"
  oops

lemma lib_enc_f_a_i_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "ls cs fetch-and-inc[v \<leftarrow> lib(y)]\<^sub>t' ls' cs'"
      and "en[lib(x), u]\<^sub>t ls"
    shows "en[lib(x), u]\<^sub>t ls'"
  using assms
  apply(simp add: lib_enc_t_def lib_enc_def)
  apply(elim exE conjE)
  apply(rule_tac x="a" in exI)
  apply(rule_tac x="b" in exI)
  apply(intro conjI)
  using lib_w_in_writes_f_a_i_pres apply auto[1]
   defer
   apply (simp add: f_a_i_pres_value)
  apply(simp add: lib_fetch_and_inc_step_def lib_update_def all_updates_l lib_writes_on_def)
  apply(elim exE conjE)
  apply(case_tac "lib_releasing ls (aa, ba)", simp_all)
   apply(simp add: ts_oride_def valid_fresh_ts_def tst_def lib_visible_writes_def lib_wfs_def lib_writes_on_def)
  apply(intro conjI impI)
  apply auto[1]
   apply force
    apply(simp add:  lib_valid_fresh_ts_def lib_writes_on_def lib_visible_writes_def)
   apply blast
  apply safe
    by(simp add:  lib_valid_fresh_ts_def lib_writes_on_def lib_visible_writes_def)


lemma lib_enc_read_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "lib_read_step t' y b ls cs ls' cs' r"
      and "en[lib(x), u]\<^sub>t ls"
    shows "en[lib(x), u]\<^sub>t ls'"
  using assms
  apply(simp add: lib_enc_t_def lib_enc_def)
  apply(elim exE conjE)
  apply(rule_tac x="a" in exI)
  apply(rule_tac x="ba" in exI)
  apply(intro conjI)
  using lib_w_in_writes_read_pres apply blast
  defer   
   apply (simp add: read_pres_value)
  apply(simp add: lib_read_step_def lib_read_def all_updates_l)
  apply(elim exE conjE)
  apply(case_tac "lib_syncing ls (aa, baa) b", simp_all)
   apply(simp add: ts_oride_def lib_writes_on_def tst_def lib_visible_writes_def)
  apply(intro impI conjI)
  apply auto[1]
  using dual_order.trans apply blast
    apply(simp add: ts_oride_def lib_writes_on_def tst_def lib_visible_writes_def)
  apply blast
    apply(simp add: ts_oride_def lib_writes_on_def tst_def lib_visible_writes_def)
  by auto


lemma lib_enc_read_intro:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "lib_read_step t x b ls cs ls' cs' r"
    shows "en[lib(x), r]\<^sub>t ls'"
  using assms
  apply(simp add: lib_enc_t_def lib_enc_def)
  apply(simp add: lib_read_step_def lib_read_def all_updates_l)
  apply(elim exE conjE)
  apply(case_tac "lib_syncing ls (a, ba) b", simp_all)
    apply(simp add: ts_oride_def lib_writes_on_def tst_def lib_visible_writes_def lib_value_def)
   apply blast
    apply(simp add: ts_oride_def lib_writes_on_def tst_def lib_visible_writes_def lib_value_def)
   apply blast
  done



lemma lib_enc_write_pres:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "lib_write_step t' y b ls cs ls' cs' r"
      and "en[lib(x), u]\<^sub>t ls"
    shows "en[lib(x), u]\<^sub>t ls'"
  using assms
  apply(simp add: lib_write_step_def lib_write_def all_updates_l)
  apply (elim conjE exE)
  apply(simp add: lib_enc_t_def lib_enc_def lib_visible_writes_def lib_valid_fresh_ts_def
        lib_writes_on_def lib_value_def, elim conjE exE)
  apply safe
  apply (metis dual_order.strict_implies_order dual_order.strict_trans2 leD)  
   apply (metis dual_order.strict_implies_not_eq)
  by blast


lemma lib_update_enc_intro:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "lib_update_step t x ls cs  ls' cs' v v'"
    shows "en[lib(x), v']\<^sub>t ls'"
  using assms
  apply(simp add: lib_update_step_def lib_update_def lib_p_obs_def all_updates_l)
  apply(elim exE conjE)
  apply(case_tac "lib_releasing ls (a, b)", simp_all)
   apply(simp add: lib_enc_t_def lib_enc_def)
  apply(rule_tac x = a in exI)
   apply(rule_tac x = ts' in exI)
   apply(simp add: lib_writes_on_def lib_value_def ts_oride_def lib_valid_fresh_ts_def lib_visible_writes_def) 
  apply(simp add: lib_enc_t_def lib_enc_def)
  apply(intro conjI impI)
  apply(rule_tac x = a in exI)
   apply(rule_tac x = ts' in exI)
   apply(simp add: lib_writes_on_def lib_value_def ts_oride_def lib_valid_fresh_ts_def lib_visible_writes_def) 
    apply(rule_tac x = a in exI)
   apply(rule_tac x = ts' in exI)
   apply(simp add: lib_writes_on_def lib_value_def ts_oride_def lib_valid_fresh_ts_def lib_visible_writes_def) 
  done


lemma lib_update_enc_intro2:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "lib_update_step t x ls cs  ls' cs' v v'"
    shows "en[lib(x), v]\<^sub>t ls'"
  using assms
  apply(case_tac "v = v'")
  apply(simp add: lib_update_step_def lib_update_def lib_p_obs_def all_updates_l)
  apply(elim exE conjE)
  apply(case_tac "lib_releasing ls (a, b)", simp_all)
   apply(simp add: lib_enc_t_def lib_enc_def)
  apply(rule_tac x = a in exI)
   apply(rule_tac x = ts' in exI)
   apply(simp add: lib_writes_on_def lib_value_def ts_oride_def lib_valid_fresh_ts_def lib_visible_writes_def) 
  apply(simp add: lib_enc_t_def lib_enc_def)
  apply(intro conjI impI)
  apply(rule_tac x = a in exI)
   apply(rule_tac x = ts' in exI)
   apply(simp add: lib_writes_on_def lib_value_def ts_oride_def lib_valid_fresh_ts_def lib_visible_writes_def) 
    apply(rule_tac x = a in exI)
   apply(rule_tac x = ts' in exI)
   apply(simp add: lib_writes_on_def lib_value_def ts_oride_def lib_valid_fresh_ts_def lib_visible_writes_def) 
  apply(simp add: lib_update_step_def lib_update_def lib_p_obs_def all_updates_l)
  apply(elim exE conjE)
  apply(case_tac "lib_releasing ls (a, b)", simp_all)
  apply(simp add: lib_enc_t_def lib_enc_def lib_writes_on_def lib_value_def)
   apply(rule_tac x = b in exI)
  apply(simp add: lib_visible_writes_def lib_writes_on_def lib_valid_fresh_ts_def ts_oride_def)
   apply blast
  apply(simp add: lib_enc_t_def lib_enc_def lib_writes_on_def lib_value_def)
     apply(case_tac "x = a", simp_all)
  apply(rule_tac x = b in exI)
  apply(simp add: lib_visible_writes_def lib_writes_on_def lib_valid_fresh_ts_def ts_oride_def)
  apply(simp add: lib_visible_writes_def lib_writes_on_def lib_valid_fresh_ts_def ts_oride_def)
  done

lemma a_is_x: "(a,b)\<in>lib_visible_writes ls t x \<Longrightarrow> a = x"
 by(simp add: lib_visible_writes_def lib_writes_on_def)


lemma lib_update_p_obs_intro:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "lib_update_step t x ls cs  ls' cs' v v'"
    shows "[lib(x) \<approx>\<^sub>t v'] ls'"
  using assms
  apply(simp add: lib_update_step_def lib_update_def lib_p_obs_def all_updates_l)
  apply(elim conjE exE)
  apply (subgoal_tac "a = x", simp_all)
  apply(case_tac "lib_releasing ls (x, b)", simp_all)
  apply(rule_tac x = x in exI)
   apply(rule_tac x = ts' in exI)
   apply(intro conjI)
    apply(simp add: lib_visible_writes_def)
   apply(intro conjI)
     apply(simp add: lib_writes_on_def)
  apply(simp add: tst_def var_def ts_oride_def lib_wfs_def lib_valid_fresh_ts_def)
    apply(intro impI)
  apply(subgoal_tac "lib_modView ls (x, b) LVARS x = (x, b)", simp)
    apply (simp add: lib_writes_on_def)
  apply(simp add: lib_value_def)
  apply(rule_tac x = x in exI)
  apply(rule_tac x = ts' in exI)
   apply(intro conjI)
    apply(simp add: lib_visible_writes_def)
     apply(simp add: lib_writes_on_def)
  apply(simp add: tst_def var_def ts_oride_def lib_wfs_def lib_valid_fresh_ts_def)
   apply (simp add: lib_writes_on_def)
   apply(simp add: lib_value_def )
  using a_is_x  
  by blast


lemma lib_read_diff_var_p_obs_prs:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "[lib(x) \<approx>\<^sub>t v'] ls"
      and "lib_read_step t' y b ls cs  ls' cs' v"
      and "y \<noteq> x"
      and "t \<noteq> t'"
    shows "[lib(x) \<approx>\<^sub>t v'] ls'"
  using assms
  apply(simp add: lib_read_step_def lib_read_def lib_p_obs_def all_updates_l) 
  apply(elim exE conjE)
  apply(subgoal_tac "a = x \<and> aa = y", simp) defer
   apply(unfold lib_visible_writes_def lib_writes_on_def, simp)[1]
  apply(case_tac "lib_syncing ls (y, baa) b", simp_all)
  apply(rule_tac x = x in exI)
   apply(rule_tac x = ba in exI)
   apply(intro conjI)
    apply(simp add: lib_visible_writes_def)
         apply(unfold  lib_writes_on_def, simp)[1]
  using assms(4) lib_visible_writes_def read_pres_value apply fastforce
   apply(rule_tac x = x in exI)
   apply(rule_tac x = ba in exI)
   apply(intro conjI)
    apply(simp add: lib_visible_writes_def)
         apply(unfold  lib_writes_on_def, simp)[1]
  using assms(4) lib_visible_writes_def read_pres_value 
  by fastforce


lemma lib_update_diff_var_no_val_prs:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "[\<zero>lib(x), v]\<^sub>i ls"
      and "lib_update_step  t y ls cs  ls' cs' u u'"
      and "y \<noteq> x"
    shows "[\<zero>lib(x), v]\<^sub>i ls'"
  using assms
  apply(simp add: lib_update_step_def lib_update_def lib_no_val_def all_updates_l
        lib_init_val_def)
  apply(elim conjE exE, intro conjI)
   apply(case_tac "lib_releasing ls (a, b)", simp_all)
  apply(simp add: lib_writes_on_def lib_value_def)
    apply (metis (full_types, hide_lams) a_is_x assms(5))
  apply(simp add: lib_writes_on_def lib_value_def)
   apply (metis a_is_x assms(5))
  apply(intro conjI impI allI)
  apply(simp add: lib_p_vorder_def lib_writes_on_def lib_value_def)
  using a_is_x apply blast
  apply(simp add: lib_p_vorder_def lib_writes_on_def lib_value_def)
  using a_is_x 
  by blast


lemma fresh_ts_not_in_writes:  "lib_valid_fresh_ts ls (x,ts) ts' \<Longrightarrow> (x, ts')\<notin>lib_writes ls"
  apply(simp add: lib_valid_fresh_ts_def lib_writes_on_def)
  by auto

lemma writes_ts_rewrite: "finite {w. fst w = x \<and> w \<in> lib_writes al} \<Longrightarrow> {w. fst w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes al)} =
       insert (x, ts') {w. fst w = x \<and> w \<in> lib_writes al}"
  using fstI by auto

lemma ts_not_in_writes_on: "(x, b)\<in>lib_writes_on s x \<Longrightarrow> lib_valid_fresh_ts s (x,b) ts' \<Longrightarrow> (x,ts')\<notin>lib_writes_on s x"
    apply (simp add: lib_writes_on_def var_def lib_valid_fresh_ts_def tst_def)
  by blast


lemma new_ts_is_the_same: "tst `lib_writes_on cl xc = tst `lib_writes_on al xa \<Longrightarrow> (xc, b)\<in>lib_writes_on cl xc \<Longrightarrow> lib_valid_fresh_ts cl (xc, b) ts' \<Longrightarrow> lib_valid_fresh_ts al (xa, b) ts'"
  apply(simp add: lib_writes_on_def tst_def lib_valid_fresh_ts_def var_def)
  apply(elim conjE, intro conjI allI impI)
  apply(subgoal_tac "(xc, ba) \<in> lib_writes cl", simp_all)
  apply(subgoal_tac "ba\<in>snd ` {w. fst w = xa \<and> w \<in> lib_writes al}")
   defer
  apply (simp add: image_iff)
proof -
fix ba :: rat
  assume a1: "snd ` {w. fst w = xc \<and> w \<in> lib_writes cl} = snd ` {w. fst w = xa \<and> w \<in> lib_writes al}"
  assume "ba \<in> snd ` {w. fst w = xa \<and> w \<in> lib_writes al}"
  then have "ba \<in> snd ` {p. fst p = xc \<and> p \<in> lib_writes cl}"
    using a1 by (metis (lifting))
  then show "(xc, ba) \<in> lib_writes cl"
    by force
next
qed

lemma tst_eq_writes_on:  " tst ` {w. var w = xc \<and> w \<in> lib_writes cl} =
       tst ` {w. var w = xa \<and> w \<in> lib_writes al} \<Longrightarrow> (xc, b)\<in>lib_writes cl \<Longrightarrow> (xa, b)\<in>lib_writes al "
  apply(simp add: tst_def var_def lib_writes_on_def)
  apply(subgoal_tac "b\<in> snd ` {w. fst w = xc \<and> w \<in> lib_writes cl}")
   apply auto[1]
  by (metis (mono_tags, lifting) fst_conv image_eqI mem_Collect_eq snd_conv)


lemma tst_eq_writes_on_not:  " tst ` {w. var w = xc \<and> w \<in> lib_writes cl} =
       tst ` {w. var w = xa \<and> w \<in> lib_writes al} \<Longrightarrow> (xc, b)\<notin>lib_writes cl \<Longrightarrow> (xa, b)\<notin>lib_writes al "
  apply(simp add: tst_def var_def lib_writes_on_def)
  apply(subgoal_tac "b\<notin> snd ` {w. fst w = xc \<and> w \<in> lib_writes cl}")
   apply auto[1]
  apply (metis (mono_tags, lifting) fst_conv image_eqI mem_Collect_eq snd_conv)
  by force


lemma lib_d_obs_cont:
  assumes "lib_wfs ls cs" 
  and "[lib(x) =\<^sub>t u] ls"
  and "[lib(x) =\<^sub>t' v] ls"
  and "u \<noteq> v"
shows "False"
  using assms
  apply(simp add: lib_d_obs_def lib_d_obs_t_def)
  done

lemma lib_not_p_obs_pres_diff_var:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "\<not>[lib(x) \<approx>\<^sub>t u] ls"
  and "lib_update_step t' y ls cs ls' cs' v v'"
  and "x \<noteq> y"
shows "\<not>[lib(x) \<approx>\<^sub>t u] ls'"
  using assms
  apply(simp add: lib_update_step_def lib_update_def all_updates_l)
  apply(elim conjE exE)
  apply(simp add: lib_p_obs_def lib_visible_writes_def lib_writes_on_def lib_value_def)
  apply(case_tac "lib_releasing ls (a, b)", simp_all)
  by (smt dual_order.trans fun_upd_other ts_oride_def)


lemma lib_not_p_obs_read_pres_diff_var:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "\<not>[lib(x) \<approx>\<^sub>t u] ls"
  and "lib_read_step t' y b ls cs ls' cs' v"
shows "\<not>[lib(x) \<approx>\<^sub>t u] ls'"
  using assms
  apply(simp add: lib_read_step_def lib_read_def all_updates_l)
  apply(elim conjE exE)
  apply(simp add: lib_p_obs_def lib_visible_writes_def lib_writes_on_def lib_value_def lib_syncing_def ts_oride_def)
  apply safe
       apply (metis order.trans)  
  using order.trans apply blast  
  using order.trans apply auto[1]  
  using order.trans apply auto[1]  
  using order.trans apply blast  
  using order.trans by blast



lemma lib_no_val_read_pres_diff_var:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[\<zero>lib(x), u]\<^sub>z ls"
  and "lib_read_step t' y b ls cs ls' cs' v"
shows "[\<zero>lib(x), u]\<^sub>z ls'"
  using assms
  apply(simp add: lib_read_step_def lib_read_def all_updates_l)
  apply(elim conjE exE)
  apply(simp add: lib_p_obs_def lib_p_vorder_def lib_no_val_def lib_init_val_def lib_visible_writes_def lib_writes_on_def lib_value_def lib_syncing_def ts_oride_def)
  done

lemma lib_no_val_write_pres_diff_var_diff_val:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[\<zero>lib(x), u]\<^sub>z ls"
  and "lib_write_step t' y b ls cs ls' cs' v"
  and "x \<noteq> y \<or> v \<noteq> u" 
shows "[\<zero>lib(x), u]\<^sub>z ls'"
  using assms
  apply(simp add: lib_write_step_def lib_write_def all_updates_l)
  apply(elim conjE exE)
  apply(simp add: lib_p_obs_def lib_valid_fresh_ts_def lib_p_vorder_def lib_no_val_def lib_init_val_def lib_visible_writes_def lib_writes_on_def lib_value_def lib_syncing_def ts_oride_def)
  apply safe
    apply blast 
  apply (metis (full_types)  dual_order.strict_trans less_le not_less_iff_gr_or_eq)
  by blast

lemma lib_no_val_update_pres_diff_var_diff_val:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[\<zero>lib(x), u]\<^sub>z ls"
  and "lib_update_step t' y ls cs ls' cs' v v'"
  and "x \<noteq> y \<or> v' \<noteq> u" 
shows "[\<zero>lib(x), u]\<^sub>z ls'"
  using assms
  apply(simp add: lib_update_step_def lib_update_def all_updates_l)
  apply(elim conjE exE)
  apply(simp add: lib_p_obs_def lib_valid_fresh_ts_def lib_p_vorder_def lib_no_val_def lib_init_val_def lib_visible_writes_def lib_writes_on_def lib_value_def lib_syncing_def ts_oride_def)
  apply safe
    apply blast 
  apply (metis (full_types)  dual_order.strict_trans  not_less_iff_gr_or_eq)
  by blast  


lemma no_val_not_p_obs: "[\<zero>lib(x), u]\<^sub>z ls \<Longrightarrow> u \<noteq> z \<Longrightarrow> \<not>[lib(x) \<approx>\<^sub>t u] ls"
  apply(simp add: lib_no_val_def lib_init_val_def lib_p_vorder_def lib_p_obs_def lib_visible_writes_def)
  apply(intro allI impI, elim conjE exE)
  apply(simp add: lib_writes_on_def lib_value_def)
  by auto

lemma lib_d_vorder_update_pres_diff_var:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and " [a lib\<hookrightarrow>\<^sub>x  b] ls"
  and "lib_update_step t' y ls cs ls' cs' v v'"
  and "x \<noteq> y"
shows "[a lib\<hookrightarrow>\<^sub>x  b] ls'"
  using assms
  apply(simp add: lib_update_step_def lib_update_def all_updates_l)
  apply(elim conjE exE)
  apply(simp add: lib_p_obs_def lib_valid_fresh_ts_def lib_p_vorder_def  lib_d_vorder_def lib_no_val_def lib_init_val_def lib_visible_writes_def lib_writes_on_def lib_value_def lib_syncing_def ts_oride_def)
  apply safe
  by (metis dual_order.strict_implies_not_eq)

lemma lib_d_vorder_read_pres:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and " [a lib\<hookrightarrow>\<^sub>x  b] ls"
  and "lib_read_step t y c ls cs ls' cs' v"
shows "[a lib\<hookrightarrow>\<^sub>x  b] ls'"
  using assms
  apply(simp add: lib_read_step_def lib_read_def all_updates_l)
  apply(elim conjE exE)
  apply(simp add: lib_p_obs_def lib_valid_fresh_ts_def lib_p_vorder_def  lib_d_vorder_def lib_no_val_def lib_init_val_def lib_visible_writes_def lib_writes_on_def lib_value_def lib_syncing_def ts_oride_def)
  done

lemma lib_c_obs_diff_var_fai_pres:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[lib(x) = v]\<lparr>lib(x) =\<^sub>t v\<rparr> ls"
  and "lib_fetch_and_inc_step t' y ls cs ls' cs' v"
  and "y \<noteq> x"
shows "[lib(x) = v]\<lparr>lib(x) =\<^sub>t v\<rparr> ls'"
  using assms
  apply(simp add:lib_fetch_and_inc_step_def  lib_update_step_def lib_update_def all_updates_l)
  apply(elim conjE exE)
  apply(simp add: lib_p_obs_def lib_valid_fresh_ts_def lib_d_obs_def  lib_releasing_def lib_lastWr_def lib_c_obs_lib_only_def lib_visible_writes_def lib_writes_on_def lib_value_def lib_syncing_def ts_oride_def)
  apply(case_tac "lib_rel (lib_mods ls (y, b))", simp_all)
  apply(simp add: tst_def var_def ts_oride_def)
   apply(case_tac "t = t'", simp_all)
  apply (smt Collect_cong fst_conv order_trans)
  apply (smt Collect_cong fst_conv)
  apply(simp add: tst_def var_def ts_oride_def)
  apply(case_tac "t = t'", simp_all)
  apply(intro allI impI conjI)
  apply (metis assms(5) eq_fst_iff)
  apply (smt Collect_cong fst_conv)
  apply(intro allI impI conjI)
  apply (metis assms(5) eq_fst_iff)
  by (smt Collect_cong fst_conv)

lemma lib_c_obs_diff_var_read_pres:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[lib(x) = v]\<lparr>lib(x) =\<^sub>t v\<rparr> ls"
  and "lib_read_step t' y  b ls cs ls' cs' z"
shows "[lib(x) = v]\<lparr>lib(x) =\<^sub>t v\<rparr> ls'"
  using assms
  apply(simp add:lib_read_step_def  lib_read_def all_updates_l)
  apply(elim conjE exE)
  apply(simp add: lib_p_obs_def lib_valid_fresh_ts_def lib_d_obs_def  lib_releasing_def lib_lastWr_def lib_c_obs_lib_only_def lib_visible_writes_def lib_writes_on_def lib_value_def lib_syncing_def ts_oride_def)
  by (smt Collect_cong order.trans)


lemma lib_c_obs_transfer:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[lib(x) = v]\<lparr>lib(x) =\<^sub>t v\<rparr> ls"
  and "lib_read_step t x  b ls cs ls' cs' v"
  shows "[lib(x) =\<^sub>t v] ls'"
  using assms
  apply(simp add:lib_read_step_def  lib_read_def all_updates_l)
  apply(elim conjE exE)
  apply(simp add: lib_p_obs_def lib_valid_fresh_ts_def lib_d_obs_def  lib_releasing_def lib_lastWr_def lib_c_obs_lib_only_def lib_visible_writes_def lib_writes_on_def lib_value_def lib_syncing_def ts_oride_def)
  apply(case_tac "lib_rel (lib_mods ls (x, ba)) \<and> b", simp_all)
  apply(simp add: tst_def var_def lib_d_obs_t_def lib_d_obs_def ts_oride_def lib_value_def lib_lastWr_def lib_writes_on_def)
  apply (metis (no_types, lifting) eq_snd_iff fst_conv lib_wfs_def var_def)
  apply(intro conjI)
  apply blast
  apply(simp add: tst_def var_def lib_d_obs_t_def lib_d_obs_def ts_oride_def lib_value_def lib_lastWr_def lib_writes_on_def)
  using lib_wfs_def by fastforce


lemma lib_init_val_read_pres:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[init lib(x) u] ls "
  and "lib_read_step t y  b ls cs ls' cs' v"
shows "[init lib(x) u] ls'"
  using assms
  apply(simp add: lib_init_val_def)  
  by (metis read_pres_value read_pres_writes_on_diff_var)

lemma lib_init_val_update_pres:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[init lib(x) u] ls "
  and "lib_update_step t y  ls cs ls' cs' v v'"
shows "[init lib(x) u] ls'"
  using assms
  apply(simp add: lib_init_val_def lib_update_step_def lib_update_def all_updates_l)  
  apply(simp add: lib_p_obs_def lib_valid_fresh_ts_def lib_d_obs_def  lib_releasing_def lib_lastWr_def lib_c_obs_lib_only_def lib_visible_writes_def lib_writes_on_def lib_value_def lib_syncing_def ts_oride_def)
  apply(elim exE conjE)
  apply(case_tac "lib_rel (lib_mods ls (y, ba))", simp_all)
  apply (metis (full_types, hide_lams)  dual_order.strict_trans not_less_iff_gr_or_eq)
    by (metis dual_order.strict_trans neq_iff)


lemma lib_init_val_fai_pres:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[init lib(x) u] ls "
  and "lib_fetch_and_inc_step t y ls cs ls' cs' v"
shows "[init lib(x) u] ls'"
  using assms
  apply(simp add: lib_init_val_def lib_fetch_and_inc_step_def lib_update_def all_updates_l)  
  apply(simp add: lib_p_obs_def lib_valid_fresh_ts_def lib_d_obs_def  lib_releasing_def lib_lastWr_def lib_c_obs_lib_only_def lib_visible_writes_def lib_writes_on_def lib_value_def lib_syncing_def ts_oride_def)
  apply(elim exE conjE)
  apply(case_tac "lib_rel (lib_mods ls (y, ba))", simp_all)
  apply (metis (full_types, hide_lams)  dual_order.strict_trans not_less_iff_gr_or_eq)
    by (metis dual_order.strict_trans neq_iff)

lemma lib_init_val_write_pres:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[init lib(x) u] ls "
  and "lib_write_step t y  b ls cs ls' cs' v"
shows "[init lib(x) u] ls'"
  using assms
  apply(simp add: lib_init_val_def lib_write_step_def lib_write_def all_updates_l)  
  apply(simp add: lib_p_obs_def tst_def lib_valid_fresh_ts_def lib_d_obs_def  lib_releasing_def lib_lastWr_def lib_c_obs_lib_only_def lib_visible_writes_def lib_writes_on_def lib_value_def lib_syncing_def ts_oride_def)
  apply(elim exE conjE)
 apply(case_tac "x = y", simp_all)   
   apply (metis (no_types, lifting) dual_order.strict_trans neq_iff)
  by blast


lemma lib_covered_write_diff_var_pres:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "cvd[lib(x), v] ls"
  and "lib_write_step t y  b ls cs ls' cs' u"
  and "y \<noteq> x"
  shows "cvd[lib(x), v] ls'"
  using assms
  apply(simp add: lib_covered_v_def lib_write_step_def lib_write_def all_updates_l)  
  apply(simp add: lib_wfs_def lib_p_obs_def tst_def lib_valid_fresh_ts_def lib_d_obs_def  lib_releasing_def lib_lastWr_def lib_c_obs_lib_only_def lib_visible_writes_def lib_writes_on_def lib_value_def lib_syncing_def ts_oride_def)
  apply(elim exE conjE)
  apply(simp add: var_def tst_def)
  apply(intro conjI impI allI, simp)
  by (smt Collect_cong fst_conv)

lemma d_obs_p_obs_contradiction: "lib_wfs ls cs \<Longrightarrow> \<not>[lib(x) \<approx>\<^sub>t u] ls \<Longrightarrow> [lib(x) =\<^sub>t' u ] ls \<Longrightarrow> False"
  apply(simp add:  lib_d_obs_t_def lib_d_obs_def lib_p_obs_def   lib_visible_writes_def lib_value_def lib_lastWr_def lib_writes_on_def tst_def)
  apply(elim conjE)
  apply(subgoal_tac "(x, Max (snd ` {w. var w = x \<and> w \<in> lib_writes ls}))\<in>lib_writes ls", simp)
  apply(subgoal_tac "snd (lib_thrView ls t x) \<le>  Max (snd ` {w. var w = x \<and> w \<in> lib_writes ls})", simp)
    apply blast
  apply(simp add:lib_wfs_def)
  apply (simp add: lib_writes_on_def)
  apply(simp add:lib_wfs_def)
  by (metis (no_types, lifting) lib_writes_on_def mem_Collect_eq)

lemma lib_dobs_visible_writes_last: "lib_wfs ls cs \<Longrightarrow> [lib(x) =\<^sub>t u] ls \<Longrightarrow> w\<in>lib_visible_writes ls t x \<Longrightarrow> w = lib_lastWr ls x"
  apply(simp add: lib_visible_writes_def lib_value_def lib_d_obs_t_def lib_d_obs_def lib_lastWr_def)
  apply(simp add: lib_writes_on_def tst_def var_def)
  apply(elim conjE)
  apply(subgoal_tac "Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls}) = snd w") 
   apply auto[1]
  apply(simp add: lib_wfs_def)
  apply(elim conjE)
  by (metis Max.coboundedI dual_order.antisym finite_imageI image_eqI lib_writes_on_def prod.collapse var_def)


lemma lib_c_obs_intro:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "\<not>[lib(x) \<approx>\<^sub>t u] ls"
  and "[lib(x) =\<^sub>t' v ] ls"
  and "lib_write_step t' x True ls cs ls' cs' u"
  and "t \<noteq> t'"
shows "[lib(x) = u]\<lparr>lib(x) =\<^sub>t u\<rparr> ls'"
  using assms
  apply(case_tac "u = v", simp_all)
  using d_obs_p_obs_contradiction apply blast
  apply(simp add: lib_covered_v_def lib_write_step_def lib_write_def all_updates_l)  
  apply(elim exE conjE)
  apply(subgoal_tac "(a, b) = lib_lastWr ls x")
   defer
  using lib_dobs_visible_writes_last apply blast
  apply(simp add: lib_c_obs_lib_only_def lib_visible_writes_def)
  apply(intro conjI impI allI) 
     apply(simp add: lib_wfs_def var_def tst_def lib_d_obs_def lib_writes_on_def lib_value_def lib_lastWr_def lib_valid_fresh_ts_def)
  apply(subgoal_tac "{w. fst w = x \<and>
                (w = (x, ts') \<or> w \<in> lib_writes ls)} = {w. fst w = x \<and>
                (w \<in> lib_writes ls)} \<union> {(x, ts')}", simp)
  apply(subgoal_tac " {w. fst w = x \<and>
                (w \<in> lib_writes ls)} \<noteq> {}") 
       apply(subgoal_tac "finite {w. fst w = x \<and>
                (w \<in> lib_writes ls)}")
  using insert_compr max_of_union apply auto[1]
  apply (simp add: writes_ts_rewrite)
  apply blast  
     apply (simp add:  writes_ts_rewrite)
    apply(simp add: lib_releasing_def)
  apply(simp add: lib_d_obs_def)
   apply(intro impI conjI, elim conjE)
    apply (simp add: lib_writes_on_def)
    apply(elim disjE conjE, simp)
    apply(subgoal_tac "a = x", simp)
  apply(simp add: lib_value_def lib_p_obs_def lib_visible_writes_def lib_writes_on_def)
     apply blast  
  apply (metis fst_eqD var_def)
   apply(simp add: lib_value_def lib_lastWr_def lib_writes_on_def lib_valid_fresh_ts_def)
  apply(subgoal_tac "Max (tst `
            {w. var w = x \<and>
                (w = (x, ts') \<or> w \<in> lib_writes ls)}) =
       ts'", simp)
  apply(simp add: var_def tst_def lib_wfs_def lib_writes_on_def)
  apply(subgoal_tac "{w. fst w = x \<and>
                (w = (x, ts') \<or> w \<in> lib_writes ls)} = {w. fst w = x \<and>
                (w \<in> lib_writes ls)} \<union> {(x, ts')}", simp)
  apply(subgoal_tac " {w. fst w = x \<and>
                (w \<in> lib_writes ls)} \<noteq> {}") 
       apply(subgoal_tac "finite {w. fst w = x \<and>
                (w \<in> lib_writes ls)}")
      apply auto[1]
     apply blast+
  apply(elim conjE)
  apply (simp add:  subset_antisym subset_refl writes_ts_rewrite)
  apply(subgoal_tac "a = x \<and> aa = x", simp)
  defer
  apply(simp add: lib_releasing_def lib_writes_on_def lib_value_def)
  using a_is_x d_obs_visible_writes apply blast
  apply(simp add: lib_p_obs_def lib_visible_writes_def lib_writes_on_def lib_value_def)
  by blast

lemma lib_c_obs_pres_write_diff_var:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[lib(x) = u]\<lparr>lib(x) =\<^sub>t u\<rparr> ls"
  and "lib_write_step t' y b ls cs ls' cs' u"
  and "x \<noteq> y"
shows "[lib(x) = u]\<lparr>lib(x) =\<^sub>t u\<rparr> ls'"
  using assms
  apply(simp add: lib_covered_v_def lib_write_step_def lib_write_def all_updates_l lib_c_obs_lib_only_def lib_visible_writes_def)  
    apply(simp add: lib_wfs_def lib_d_obs_def lib_writes_on_def lib_value_def lib_valid_fresh_ts_def lib_lastWr_def lib_releasing_def tst_def var_def)
  apply(elim exE conjE)
  apply clarsimp
  apply (smt Collect_cong fst_conv fun_upd_apply)
  done


lemma lib_c_obs_pres_read_diff_var:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[lib(x) = u]\<lparr>lib(x) =\<^sub>t u\<rparr> ls"
  and "lib_read_step t' y b ls cs ls' cs' u"
shows "[lib(x) = u]\<lparr>lib(x) =\<^sub>t u\<rparr> ls'"
  using assms(1) assms(2) assms(3) assms(4) lib_c_obs_diff_var_read_pres by blast


lemma lib_c_obs_pres_fai_diff_var:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[lib(x) = u]\<lparr>lib(x) =\<^sub>t u\<rparr> ls"
  and "lib_fetch_and_inc_step t' y ls cs ls' cs' v"
  and "x \<noteq> y"
shows "[lib(x) = u]\<lparr>lib(x) =\<^sub>t u\<rparr> ls'"
  using assms
  apply(simp add: lib_covered_v_def lib_fetch_and_inc_step_def lib_update_def all_updates_l lib_c_obs_lib_only_def lib_visible_writes_def)  
    apply(simp add: lib_wfs_def lib_d_obs_def lib_writes_on_def lib_value_def lib_valid_fresh_ts_def lib_lastWr_def lib_releasing_def tst_def var_def)
  apply(elim exE conjE, intro allI impI conjI)
    apply clarsimp
    apply(case_tac "t = t'", simp_all)
     apply(case_tac "lib_rel (lib_mods ls (y, b))", simp_all)
   apply(simp add: ts_oride_def)
 apply(subgoal_tac "{w. fst w = x \<and>
                (w = (y, ts') \<or> w \<in> lib_writes ls)} = {w. fst w = x \<and>
                ( w \<in> lib_writes ls)}", simp)
       apply (smt fun_upd_other order.trans tst_def)
  apply auto[1]
  
  apply (smt Collect_cong fst_conv)
  
    apply (smt Collect_cong fst_conv)
  apply clarsimp
 apply(subgoal_tac "{w. fst w = x \<and>
                (w = (y, ts') \<or> w \<in> lib_writes ls)} = {w. fst w = x \<and>
                ( w \<in> lib_writes ls)}", simp)
      apply(case_tac "t = t'", simp_all)
     apply(case_tac "lib_rel (lib_mods ls (y, b))", simp_all)
   apply(simp add: ts_oride_def)
  apply (smt fun_upd_other order.trans tst_def)
   apply auto[1]
      apply(case_tac "t = t'", simp_all)
  apply(case_tac "lib_rel (lib_mods ls (y, b))", simp_all)
  apply clarsimp
   apply(simp add: ts_oride_def)
  by (smt fun_upd_other order.trans tst_def)

lemma tst_w_leq_last:  "finite (lib_writes_on ls x) \<Longrightarrow> w\<in>lib_writes_on ls x \<Longrightarrow> tst w \<le> tst (lib_lastWr ls x)"
  apply(simp add: lib_writes_on_def tst_def var_def lib_lastWr_def)
  done


lemma lib_d_obs_pres_fai_diff_var:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[lib(x) =\<^sub>t u] ls"
  and "lib_fetch_and_inc_step t' y ls cs ls' cs' v"
  and "x \<noteq> y"
shows "[lib(x) =\<^sub>t u] ls'"
  using assms
  apply(simp add: lib_covered_v_def lib_fetch_and_inc_step_def lib_update_def all_updates_l lib_c_obs_lib_only_def lib_visible_writes_def)  
  apply(simp add: lib_wfs_def lib_d_obs_t_def  lib_d_obs_def lib_writes_on_def lib_value_def lib_valid_fresh_ts_def lib_lastWr_def lib_releasing_def tst_def var_def)
  apply(elim exE conjE)
  apply(case_tac "lib_rel (lib_mods ls (y, b))", simp_all)
  apply(case_tac "t \<noteq> t'", simp_all)
  apply clarsimp
    apply (smt Collect_cong fst_conv)
   apply(simp add: ts_oride_def)
   apply(intro conjI impI)
      apply(simp add: tst_def)
  apply(subgoal_tac "snd `
                {w. fst w = x \<and>
                    (w = (y, ts') \<or> w \<in> lib_writes ls)} = snd `
                {w. fst w = x \<and>
                    ( w \<in> lib_writes ls)}", simp)
apply(case_tac "Max (snd ` {w. fst w = x \<and> w \<in> lib_writes ls})
       = snd (lib_modView ls (y, b) LVARS x)", simp_all)
        apply (metis prod.collapse)     apply(subgoal_tac "lib_modView ls (y, b) LVARS x\<in>lib_writes_on ls x")
   apply(subgoal_tac "finite (lib_writes_on ls x)")
    using tst_w_leq_last
  apply (metis (no_types, lifting) Collect_cong dual_order.antisym lib_lastWr_def lib_writes_on_def snd_conv tst_def var_def)
    apply(simp add: lib_writes_on_def var_def tst_def)
    apply(simp add: lib_writes_on_def var_def tst_def)
        apply auto[1]
  apply (smt Collect_cong fst_conv)
  apply (metis assms(5) fst_eqD)
  apply (smt Collect_cong fst_conv)
  by (smt Collect_cong fst_conv)

lemma lib_d_obs_pres_read:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[lib(x) =\<^sub>t u] ls"
  and "lib_read_step t' y b ls cs ls' cs' v"
shows "[lib(x) =\<^sub>t u] ls'"
  using assms
  apply(simp add: lib_wfs_def lib_read_step_def lib_syncing_def lib_releasing_def lib_read_def all_updates_l lib_d_obs_t_def lib_d_obs_def lib_value_def lib_lastWr_def lib_writes_on_def var_def tst_def)
  apply(elim exE conjE, clarsimp)
  apply(intro conjI impI )
     apply(simp add: ts_oride_def  tst_def var_def)
  apply safe
  apply (metis (no_types, lifting) a_is_x assms(2) assms(3) lib_d_obs_def lib_d_obs_t_def lib_dobs_visible_writes_last)  
  apply (metis (no_types, lifting) Pair_inject a_is_x assms(2) assms(3) lib_d_obs_def lib_d_obs_t_def lib_dobs_visible_writes_last)
  apply(case_tac "lib_rel (lib_mods ls (x, ba)) \<and> b", simp_all)
  apply (metis (no_types, lifting) Pair_inject a_is_x assms(2) assms(3) lib_d_obs_def lib_d_obs_t_def lib_dobs_visible_writes_last)  
  apply (metis (no_types, lifting) Pair_inject a_is_x assms(2) assms(3) lib_d_obs_def lib_d_obs_t_def lib_dobs_visible_writes_last) 
  by (smt assms(2) assms(3) fun_upd_other lib_d_obs_def lib_d_obs_t_def prod.collapse ts_ge_last_is_last ts_oride_def tst_def)

lemma lib_not_pobs_cobs: "\<not> [lib(x) \<approx>\<^sub>t v] ls \<Longrightarrow> [lib(x) = v]\<lparr>lib(y) =\<^sub>t u \<rparr> ls"
  apply(simp add: lib_p_obs_def lib_c_obs_lib_only_def)
  by auto


lemma no_val_no_value: "lib_wfs ls cs \<Longrightarrow> u > i   \<Longrightarrow> [\<zero>lib(sn), u]\<^sub>i ls \<Longrightarrow> \<forall> w . w\<in>lib_writes_on ls sn \<longrightarrow> lib_value ls w \<noteq> u"      
  apply(simp add: lib_no_val_def, elim conjE)
  apply(simp add:  lib_init_val_def lib_p_vorder_def )
  apply(intro allI impI,elim exE conjE)
  apply(simp add: lib_writes_on_def lib_value_def)
  by blast

lemma lib_d_obs_not_p_obs: "lib_wfs cls ccs \<Longrightarrow> u\<noteq>v \<Longrightarrow> [lib(x) =\<^sub>t u] cls \<Longrightarrow> \<not>[lib(x) \<approx>\<^sub>t v] cls"
  apply(simp add: lib_wfs_def lib_d_obs_t_def lib_d_obs_def lib_p_obs_def lib_visible_writes_def lib_lastWr_def)
  apply(simp add: lib_writes_on_def lib_value_def var_def tst_def)
  apply safe
  by (metis (mono_tags, lifting) Max_ge antisym finite_imageI image_eqI mem_Collect_eq snd_conv)


end