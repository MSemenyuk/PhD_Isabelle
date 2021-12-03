theory TS_Proof_Rules
imports  TS_Model
begin
lemmas [simp] = push_inv_def


lemma CAS_Top_written_addr_post: "cls ccs CAS\<^sup>R[libTop, True, a , b]\<^sub>t cls' ccs'
 \<Longrightarrow> c \<in> written_addr cls' \<Longrightarrow> c \<notin> written_addr cls \<Longrightarrow> c = b "
  apply(simp add: written_addr_def)
  apply(subgoal_tac "lib_value cls' ` lib_writes_on cls' Top = lib_value cls ` lib_writes_on cls Top \<union> {b}")
   apply simp
  apply(simp add: lib_CAS_Rel_step_def,elim exE conjE)
  apply(case_tac "lib_value cls (aa, ba) = a", simp_all)
  apply(simp add: lib_update_r_def all_updates_l lib_writes_on_def var_def tst_def lib_value_def)
  apply safe
  apply simp_all
       apply auto[3]
    apply (smt Lib.lib_write_record.select_convs(1) fst_conv image_iff mem_Collect_eq)
   apply safe
  apply clarsimp
  apply (smt fresh_ts_not_in_writes fst_conv imageI less_numeral_extra(3) lib_value_def mem_Collect_eq var_def)
  apply clarsimp
  apply (smt fresh_ts_not_in_writes fst_conv imageI less_numeral_extra(3) lib_value_def mem_Collect_eq var_def)  
  done

lemma CAS_Top_written_addr_post2: "cls ccs CAS\<^sup>R[libTop, True, a , b]\<^sub>t cls' ccs' \<Longrightarrow>
 c \<in> lib_value cls' `(lib_writes_on cls' Top) - {Null} \<Longrightarrow>
 c \<notin> lib_value cls `(lib_writes_on cls Top) - {Null} \<Longrightarrow>  c = b "
  using CAS_Top_written_addr_post written_addr_def
      by blast


lemma failed_CAS_Top_written_addr_post: "cls ccs CAS\<^sup>R[libTop, False, a , b]\<^sub>t cls' ccs'
 \<Longrightarrow> lib_value cls' `lib_writes_on cls' Top = lib_value cls `lib_writes_on cls Top"
  apply(simp add: lib_CAS_Rel_step_def,elim exE conjE)
  apply(case_tac "lib_value cls (aa, ba) = a", simp_all)
  apply(simp add: lib_read_def all_updates_l lib_writes_on_def var_def tst_def lib_value_def)
  done

lemma failed_CAS_Top_written_addr_post2: "cls ccs CAS\<^sup>R[libTop, False, a , b]\<^sub>t cls' ccs'
 \<Longrightarrow> written_addr cls' = written_addr cls"
  apply(simp add: written_addr_def)
  using failed_CAS_Top_written_addr_post apply metis
  done


lemma diff_var_write_written_addr: "lib_wfs cls ccs \<Longrightarrow>
 cls ccs [lib(x) := b]\<^sub>t cls' ccs' \<Longrightarrow> x \<noteq>Top \<Longrightarrow> written_addr cls' = written_addr cls"
  apply(simp add: written_addr_def lib_write_step_def, elim exE conjE)
  apply(simp add: lib_write_def all_updates_l lib_writes_on_def var_def tst_def lib_visible_writes_def
      lib_valid_fresh_ts_def) 
  apply safe
       apply simp
  apply(simp add: lib_value_def)
  apply linarith
  apply linarith
   apply(simp add: lib_value_def)
   apply(simp add: lib_wfs_def)
  apply(simp add: lib_write_def all_updates_l lib_writes_on_def var_def tst_def lib_visible_writes_def
      lib_valid_fresh_ts_def) 
  apply safe
  apply (smt image_iff mem_Collect_eq)
  by linarith


lemma success_CAS_Top_written_addr_post: "cls ccs CAS\<^sup>R[libTop, True, a , b]\<^sub>t cls' ccs'
 \<Longrightarrow> lib_value cls' `lib_writes_on cls' Top = lib_value cls `lib_writes_on cls Top \<union> {b}"
  apply(simp add: lib_CAS_Rel_step_def,elim exE conjE)
  apply(case_tac "lib_value cls (aa, ba) = a", simp_all)
  apply(simp add: lib_update_r_def all_updates_l lib_writes_on_def var_def tst_def lib_value_def)
  apply safe  
     apply auto[1]
  apply auto[1]
  apply (smt Lib.lib_write_record.select_convs(1) a_is_x fst_conv image_iff mem_Collect_eq)
   by (smt fresh_ts_not_in_writes image_iff mem_Collect_eq)


lemma success_CAS_Top_written_addr_post2: "cls ccs CAS\<^sup>R[libTop, True, a , b]\<^sub>t cls' ccs'
 \<Longrightarrow> b \<noteq> Null \<Longrightarrow>  written_addr  cls' = written_addr cls \<union> {b}"
  using success_CAS_Top_written_addr_post written_addr_def
  by (simp add: written_addr_def insert_Diff_if)


lemma read_value_in_written: "cls ccs [r \<leftarrow>\<^sup>A lib x]\<^sub>t cls' ccs' \<Longrightarrow>
 r \<in> lib_value cls ` lib_writes_on cls x"
  apply(simp add: lib_writes_on_def  lib_value_def lib_read_step_def lib_read_def all_updates_l, elim exE conjE)
  by (smt image_iff lib_visible_writes_def lib_writes_on_def mem_Collect_eq)

     



lemma c_obs_Top_read:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "c_obs_Top t ps cls ccs"
      and "lib_read_step t' x b cls ccs cls' ccs' v "
    shows "c_obs_Top t ps' cls' ccs'"
  using assms
  apply(simp add: c_obs_Top_def)
  apply(intro conjI allI impI)
  apply(erule_tac x=ad in allE)
  apply(subgoal_tac "written_addr cls' = written_addr cls")
   defer
     apply(simp add:  written_addr_def  , elim exE conjE)
   apply(subgoal_tac "lib_writes_on cls' Top = lib_writes_on cls Top", simp)
  apply(simp add: lib_value_def)
  apply(subgoal_tac "\<forall> w . w\<in>lib_writes_on cls Top \<longrightarrow> lib_mods cls w = lib_mods cls' w")
     apply (metis (no_types, lifting) image_cong)
    apply(intro allI impI)
  apply(simp add: lib_read_step_def lib_read_def all_updates_l)
    apply auto[1]
  apply(simp add: lib_read_step_def lib_read_def all_updates_l lib_writes_on_def var_def tst_def)
  apply auto[1]
  apply (simp, elim conjE exE)
  apply(rule_tac x=xa in exI)
  apply(simp add: lib_c_obs_lib_only_def)
  apply(simp add: lib_visible_writes_def lib_d_obs_def, intro allI impI conjI)
    apply(simp add: lib_read_step_def lib_visible_writes_def lib_read_def all_updates_l, elim conjE exE)
    apply(case_tac "lib_syncing cls (aa, baa) b", simp_all)
     apply(simp add: lib_writes_on_def lib_lastWr_def var_def tst_def)
  apply(unfold lib_wfs_def lib_writes_on_def var_def tst_def lib_value_def lib_lastWr_def, simp)[1]
  apply (smt dual_order.trans fun_upd_other fun_upd_same snd_conv ts_oride_def tst_def)
  apply(unfold lib_wfs_def lib_writes_on_def var_def tst_def lib_value_def lib_lastWr_def, simp)[1]
  apply (smt dual_order.trans fun_upd_apply snd_conv)   
    apply(simp add: lib_read_step_def lib_visible_writes_def lib_read_def all_updates_l, elim conjE exE)
  apply(unfold lib_wfs_def lib_writes_on_def var_def tst_def lib_value_def lib_lastWr_def, simp)[1]
   apply(case_tac "lib_syncing cls (x, baa) b", simp_all, elim conjE exE)
  apply (smt dual_order.trans fst_conv fun_upd_other fun_upd_same snd_conv ts_oride_def tst_def)
  apply (smt dual_order.trans fst_conv fun_upd_other fun_upd_same snd_conv ts_oride_def tst_def)
  apply(simp add: lib_read_step_def lib_visible_writes_def lib_read_def all_updates_l, elim conjE exE)
  apply(unfold lib_wfs_def lib_writes_on_def var_def tst_def lib_value_def lib_lastWr_def, simp)[1]
  apply(case_tac "lib_syncing cls (x, baa) b", simp_all, elim conjE exE)
   apply(simp_all add: lib_releasing_def)  
  apply (smt dual_order.trans fst_conv fun_upd_other fun_upd_same snd_conv ts_oride_def tst_def)
  by (smt dual_order.trans fst_conv fun_upd_apply snd_conv)

lemma c_obs_TopNxt_read:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "c_obs_TopNxt t ps cls ccs"
      and "lib_read_step t' x b cls ccs cls' ccs' v "
    shows "c_obs_TopNxt t ps' cls' ccs'"
  using assms
  apply(simp add: c_obs_TopNxt_def)
  apply(intro conjI allI impI)
  apply(erule_tac x=ad in allE)
  apply(subgoal_tac "written_addr cls' = written_addr cls")
   defer
     apply(simp add:  written_addr_def  , elim exE conjE)
   apply(subgoal_tac "lib_writes_on cls' Top = lib_writes_on cls Top", simp)
  apply(simp add: lib_value_def)
  apply(subgoal_tac "\<forall> w . w\<in>lib_writes_on cls Top \<longrightarrow> lib_mods cls w = lib_mods cls' w")
     apply (metis (no_types, lifting) image_cong)
    apply(intro allI impI)
  apply(simp add: lib_read_step_def lib_read_def all_updates_l)
    apply auto[1]
  apply(simp add: lib_read_step_def lib_read_def all_updates_l lib_writes_on_def var_def tst_def)
  apply auto[1]
  apply (simp, elim conjE exE)
  apply(rule_tac x=xa in exI)
  apply(simp add: lib_c_obs_lib_only_def)
  apply(simp add: lib_visible_writes_def lib_d_obs_def, intro allI impI conjI)
    apply(simp add: lib_read_step_def lib_visible_writes_def lib_read_def all_updates_l, elim conjE exE)
    apply(case_tac "lib_syncing cls (aa, baa) b", simp_all)
     apply(simp add: lib_writes_on_def lib_lastWr_def var_def tst_def)
  apply(unfold lib_wfs_def lib_writes_on_def var_def tst_def lib_value_def lib_lastWr_def, simp)[1]
  apply (smt dual_order.trans fun_upd_other fun_upd_same snd_conv ts_oride_def tst_def)
  apply(unfold lib_wfs_def lib_writes_on_def var_def tst_def lib_value_def lib_lastWr_def, simp)[1]
  
  apply (smt dual_order.trans fun_upd_apply snd_conv)
    apply(simp add: lib_read_step_def lib_visible_writes_def lib_read_def all_updates_l, elim conjE exE)
  apply(unfold lib_wfs_def lib_writes_on_def var_def tst_def lib_value_def lib_lastWr_def, simp)[1]
  apply(case_tac "lib_syncing cls (x, baa) b", simp_all, elim conjE exE)
  
  apply (smt dual_order.trans fst_conv fun_upd_other fun_upd_same snd_conv ts_oride_def tst_def)
  apply (smt dual_order.trans fst_conv fun_upd_other fun_upd_same snd_conv ts_oride_def tst_def)
  apply(unfold lib_wfs_def lib_writes_on_def var_def tst_def lib_value_def lib_lastWr_def, simp)[1]
     apply(simp add: lib_read_step_def lib_visible_writes_def lib_read_def all_updates_l, elim conjE exE)
 apply(simp_all add: lib_releasing_def)
  by (smt fun_upd_other fun_upd_same lib_writes_on_def mem_Collect_eq order.trans snd_conv ts_oride_def tst_def)



lemma c_obs_Top_CASR_unsuccessful:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "c_obs_Top t ps cls ccs"
      and "cls ccs CAS\<^sup>R[lib(x), False, u , u']\<^sub>t' cls' ccs' "
    shows "c_obs_Top t ps' cls' ccs'"
  using assms
  apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
  apply(case_tac "lib_value cls (a, b) = u", simp_all)
  by (meson  c_obs_Top_read lib_read_step_def)


lemma c_obs_TopNxt_CASR_unsuccessful:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "c_obs_TopNxt t ps cls ccs"
      and "cls ccs CAS\<^sup>R[lib(x), False, u , u']\<^sub>t' cls' ccs' "
    shows "c_obs_TopNxt t ps' cls' ccs'"
  using assms
  apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
  apply(case_tac "lib_value cls (a, b) = u", simp_all)
  by (meson  c_obs_TopNxt_read lib_read_step_def)


lemma last_the_same1: "lib_wfs cls als \<Longrightarrow> w \<in> lib_visible_writes cls t Top \<Longrightarrow>
       w \<notin> lib_covered cls \<Longrightarrow>
       lib_valid_fresh_ts cls w ts' \<Longrightarrow> cls' = fst (lib_update_r t w u cls ccs
                  ts') \<Longrightarrow> ts' < tst (lib_lastWr cls Top) \<Longrightarrow> lib_lastWr cls' Top = lib_lastWr cls Top"
  apply(simp add: lib_visible_writes_def lib_valid_fresh_ts_def lib_lastWr_def lib_writes_on_def all_updates_l lib_update_r_def)
  apply(simp add:  var_def tst_def)
  apply safe
  apply(subgoal_tac "ts' < Max (snd ` {w. fst w = Top \<and> w \<in> lib_writes cls})") defer
   apply blast
  apply(subgoal_tac "{w. fst w = Top \<and>
             (w = (Top, ts') \<or> w \<in> lib_writes cls)} = {w. fst w = Top \<and>
             (w \<in> lib_writes cls)} \<union> {(Top, ts')}")
  defer
  apply safe
   apply simp
  apply simp
  apply(subgoal_tac " Max (insert ts'
          (snd ` {w. fst w = Top \<and> w \<in> lib_writes cls})) \<in> {ts',     Max (snd ` {w. fst w = Top \<and> w \<in> lib_writes cls})}")
   defer
  apply(subgoal_tac "finite(snd ` {w. fst w = Top \<and> w \<in> lib_writes cls})")
  apply (metis (no_types, lifting) Max_in finite.insertI infinite_growing insertCI insertE insert_not_empty member_less_max)
   apply(simp add: lib_wfs_def lib_writes_on_def var_def tst_def)
  apply(subgoal_tac "Max ((snd ` {w. fst w = Top \<and> w \<in> lib_writes cls}))
    \<noteq> ts'") defer
   apply linarith
  apply simp 
   apply(simp add: lib_wfs_def lib_writes_on_def var_def tst_def)
  apply(subgoal_tac "ts'\<notin> snd ` {w. fst w = Top \<and> w \<in> lib_writes cls}") defer
   apply(elim disjE)
  apply safe
    apply auto[1]
   apply auto[1]
  apply(subgoal_tac "snd ` {w. fst w = Top \<and> w \<in> lib_writes cls} \<noteq> {}") defer
   apply blast
  by auto

lemma last_the_same2: "lib_wfs cls als \<Longrightarrow> w \<in> lib_visible_writes cls t Top \<Longrightarrow>
       w \<notin> lib_covered cls \<Longrightarrow>
       lib_valid_fresh_ts cls w ts' \<Longrightarrow> cls' = fst (lib_update_r t w u cls ccs
                  ts') \<Longrightarrow> ts' > tst (lib_lastWr cls Top) \<Longrightarrow> lib_lastWr cls' Top = (Top, ts')"
  apply(simp add: lib_visible_writes_def lib_valid_fresh_ts_def lib_lastWr_def lib_writes_on_def all_updates_l lib_update_r_def)
  apply(simp add:  var_def tst_def)
  apply safe
   apply(subgoal_tac "ts' > Max (snd ` {w. fst w = Top \<and> w \<in> lib_writes cls})") defer
   apply blast
   apply(subgoal_tac "{w. fst w = Top \<and> w \<in> lib_writes cls} \<noteq> {}")
   apply(subgoal_tac "finite({w. fst w = Top \<and> w \<in> lib_writes cls})")
    apply(subgoal_tac "{w. fst w = Top \<and>
             (w = (Top, ts') \<or> w \<in> lib_writes cls)} = {w. fst w = Top \<and>
             (w \<in> lib_writes cls)} \<union> {(Top, ts')}")

  using max_of_union apply auto[1]
    apply(simp add: lib_wfs_def lib_writes_on_def var_def)
  apply (simp add: writes_ts_rewrite)
     apply(simp add: lib_wfs_def lib_writes_on_def var_def)
  by blast



lemma nxt_rel_subset: "a \<notin> pushed_addr ps \<Longrightarrow> b\<in>pushed_addr ps 
       \<Longrightarrow>  pushed_addr ps' = pushed_addr ps \<union> {a} \<Longrightarrow> nxt_rel ps cls \<subseteq> nxt_rel ps' cls"
  apply(simp add: nxt_rel_def)
  by auto

lemma nxt_rel_subset1: "a\<notin>pushed_addr ps \<Longrightarrow>  pushed_addr ps' = pushed_addr ps  
      \<Longrightarrow> nxt_rel ps cls\<subseteq> nxt_rel ps' cls"
  by(simp add: nxt_rel_def)


lemma agt_add_n: "a \<in> pushed_addr ps \<Longrightarrow> b\<in>pushed_addr ps \<Longrightarrow> 
   agt a b ps cls \<Longrightarrow>  pushed_addr ps' = pushed_addr ps \<union> {c} \<Longrightarrow>
     c\<notin>pushed_addr ps \<Longrightarrow> agt a b ps' cls"
  apply(simp add: agt_def clss_def)
  apply(subgoal_tac "nxt_rel ps cls\<subseteq> nxt_rel ps' cls")
  using trancl_mono apply blast
  using nxt_rel_subset
  by (simp add: nxt_rel_subset)



lemma agt_pushed_same: "a\<notin>pushed_addr ps \<Longrightarrow> agt a b ps cls \<Longrightarrow>
  pushed_addr ps' = pushed_addr ps \<Longrightarrow> agt a b ps' cls"
  apply(simp add: agt_def clss_def)
  apply(subgoal_tac "nxt_rel ps cls \<subseteq> nxt_rel ps' cls")
  using trancl_mono apply blast
  using nxt_rel_subset
  by (simp add: nxt_rel_subset1)


(*nxt ps' = (nxt ps) (a := b) \<Longrightarrow>*)
lemma agt_pushed_same2: "agt c d ps cls \<Longrightarrow> 
   pushed_addr ps' = pushed_addr ps \<Longrightarrow>
   agt c d ps' cls"
  apply(simp add: agt_def clss_def)
  apply(subgoal_tac "nxt_rel ps cls\<subseteq> nxt_rel ps' cls")
  using trancl_mono apply blast
  using nxt_rel_subset
  by (simp add: nxt_rel_def)



lemma agt_pushed_failed_cas: " glb_inv ps cls \<Longrightarrow>
               cls ccs CAS\<^sup>R[lib a, False, u, u']\<^sub>t cls' ccs'\<Longrightarrow>
               agt c d ps cls \<Longrightarrow>  
               same_except_for_pc_and_top ps ps' \<Longrightarrow>
               agt c d ps' cls'"
  apply(simp add: agt_def clss_def)
  apply(subgoal_tac "nxt_rel ps cls \<subseteq> nxt_rel ps' cls'")
   apply (simp add: nxt_rel_def)
  apply (simp add: trancl_mono)
  apply (simp add: nxt_rel_def)
  apply safe
  apply(rule_tac x= aaa in exI)
  apply safe
  apply(simp add: globals)
  using failed_CAS_preserves_last by auto

lemma agt_pushed_successful_cas: " glb_inv ps cls \<Longrightarrow>
               cls ccs CAS\<^sup>R[lib Top, True, u, u']\<^sub>t cls' ccs'\<Longrightarrow>
               u' \<noteq> c \<Longrightarrow> u' \<noteq> d \<Longrightarrow>
               agt c d ps cls \<Longrightarrow>  
               pushed_addr ps' = pushed_addr ps \<union> {u'} \<Longrightarrow>
               agt c d ps' cls'"
  apply(simp add: agt_def clss_def)
  apply(subgoal_tac "nxt_rel ps cls \<subseteq> nxt_rel ps' cls'")
   apply (simp add: nxt_rel_def)
  apply (simp add: trancl_mono)
  apply (simp add: nxt_rel_def)
  apply(simp add: globals)
  by (smt Collect_mono_iff succ_CAS_preserves_last)


lemma cls_after_new_before:
  assumes "(a,b)\<in>f'\<^sup>+"
      and "(a,c)\<notin>f'\<^sup>+"
      and "c \<noteq> a"
      and "f' = f \<union> {(c,d)}"
    shows "(a,b)\<in>f\<^sup>+"
  using assms
  apply(induction a b rule: trancl.induct)
   apply auto[1]
  by (metis Un_insert_right insert_iff old.prod.inject sup_bot.right_neutral trancl.trancl_into_trancl)

lemma no_nxt_no_agt: "\<forall> e . e\<in>pushed_addr ps \<longrightarrow> lib_value cls (lib_lastWr cls (Suc e)) \<noteq> b 
\<Longrightarrow> \<not> agt a b ps cls"
  apply(simp add: agt_def clss_def nxt_rel_def)
  apply(case_tac "a \<in> pushed_addr ps")
  apply(simp add: trancl_def )
  apply (smt tranclp.cases)
  apply(simp add: trancl_def )
  using converse_tranclpE by fastforce


lemma agt_pushed_successful_cas_before: " glb_inv ps cls \<Longrightarrow> to ps cls \<Longrightarrow> glb ps cls \<Longrightarrow>
               cls ccs CAS\<^sup>R[lib Top, True, u, u']\<^sub>t cls' ccs'\<Longrightarrow> u' \<notin> pushed_addr ps \<Longrightarrow>
               u' \<noteq> c \<Longrightarrow> u' \<noteq> d \<Longrightarrow> c\<in>pushed_addr ps \<Longrightarrow> d\<in>pushed_addr ps \<Longrightarrow>
               agt c d ps' cls' \<Longrightarrow> \<not>agt c u' ps' cls' \<Longrightarrow> u' \<noteq> Top \<Longrightarrow> Suc u' \<noteq> Top \<Longrightarrow>
               pushed_addr ps' = pushed_addr ps \<union> {u'} \<Longrightarrow>
               agt c d ps cls"
  apply(simp add: agt_def clss_def)  
  apply(subgoal_tac " nxt_rel ps' cls' =  nxt_rel ps cls \<union> {(u', lib_value cls (lib_lastWr cls (Suc (u'))))}", simp)
   apply (metis Un_empty_right Un_insert_right cls_after_new_before)
  apply(simp add: nxt_rel_def)
        apply(subgoal_tac "\<forall> p . p\<in>pushed_addr ps \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc p)) = lib_value cls (lib_lastWr cls (Suc p))")
   defer
  apply(simp add: globals)
  apply (metis succ_CAS_preserves_last)

  apply safe
  using succ_CAS_preserves_last apply auto[1]
  defer
     apply blast
    using succ_CAS_preserves_last apply auto[1]
    apply simp
    by blast





lemma aa:  "finite (A::((nat \<times> nat) set)) \<Longrightarrow> A \<noteq> {} \<Longrightarrow> Max (snd `A) \<in> snd `A"
  using Max_in by blast

lemma aa1:  "finite (A::((nat \<times> nat) set)) \<Longrightarrow> A \<noteq> {} \<Longrightarrow> Max (snd `A) \<in> snd `A"
  using Max_in by blast


lemma lib_lastWr_in_lib_writes_on: 
"finite(lib_writes_on cls Top) \<Longrightarrow> lib_writes_on cls Top \<noteq> {} \<Longrightarrow> lib_lastWr cls Top \<in> lib_writes_on cls Top"
  apply(simp add: lib_lastWr_def ) 
  apply safe
  apply(subgoal_tac "a = Top", simp)
   defer
   apply(simp add: lib_writes_on_def)
  apply(subgoal_tac "b \<in> (tst ` lib_writes_on cls Top)")
   defer
     apply(simp add: lib_writes_on_def var_def tst_def)
   apply (simp add: image_iff)
  apply(subgoal_tac "Max (tst ` lib_writes_on cls Top) \<notin> tst ` lib_writes_on cls Top")
   defer
       apply(simp add: lib_writes_on_def var_def tst_def)
   apply (simp add: image_iff)
       apply(simp add: lib_writes_on_def var_def tst_def)
  by (metis (no_types, lifting) Max_eq_iff empty_iff finite_imageI)




lemma agt_pop_successful_cas_before3: "lib_wfs cls ccs \<Longrightarrow> glb_inv ps cls \<Longrightarrow>
glb ps cls \<Longrightarrow> to ps cls \<Longrightarrow>
               cvd[lib(Top), u] cls \<Longrightarrow>
               cls ccs CAS\<^sup>R[lib Top, True, u, u']\<^sub>t cls' ccs'\<Longrightarrow>
               u \<noteq> u' \<Longrightarrow> c\<in>pushed_addr ps \<Longrightarrow> d\<in>pushed_addr ps \<Longrightarrow>
                u \<noteq> c \<Longrightarrow>  u\<noteq>d \<Longrightarrow>
               agt c d ps' cls' \<Longrightarrow>
               pushed_addr ps' = pushed_addr ps - {u} \<Longrightarrow>
               agt c d ps cls"
        apply(subgoal_tac "lastTop cls = u") defer
         apply(simp add: lastTop_def lib_covered_v_def)
         apply safe
        apply(subgoal_tac "\<exists> w . w\<in>lib_writes_on cls Top \<and> w = lib_lastWr cls Top")
          apply(elim exE conjE)
        apply(subgoal_tac "w \<notin> lib_covered cls")
           apply fastforce
        apply(simp add: lib_wfs_def)
          apply auto[1]
         apply(subgoal_tac "lib_lastWr cls Top\<in>lib_writes_on cls Top")
          apply blast
         apply(simp add: lib_wfs_def )
        using lib_lastWr_in_lib_writes_on apply fastforce
        apply(simp add: agt_def)
        apply(subgoal_tac " agt u c ps cls \<and> agt u d ps cls") defer
         apply (simp add: globals to_p2_def)
        apply(simp add: agt_def clss_def)
        apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls - {(u, lib_value cls (lib_lastWr cls (Suc u)))}")
         apply (simp add: trancl_mono)
        apply(simp add: nxt_rel_def)
        apply(subgoal_tac "\<forall> p . p\<in>pushed_addr ps \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc p)) = lib_value cls (lib_lastWr cls (Suc p))")
        apply(subgoal_tac "{(a, lib_value cls' (lib_lastWr cls' (Suc a))) |a.
           a \<in> pushed_addr ps \<and> a \<noteq> lastTop cls} = {(a, lib_value cls' (lib_lastWr cls' (Suc a))) |a.
           a \<in> pushed_addr ps} - {(lastTop cls, lib_value cls' (lib_lastWr cls' (Suc (lastTop cls))))} ") 
          apply(simp add: lastTop_def)
        apply safe
        apply blast
        apply blast
        apply simp
        apply simp
        apply blast
        apply blast
         apply blast
        apply(simp add: globals)
        by (metis succ_CAS_preserves_last)



lemma agt_pushed_failed_cas_before_state: " glb_inv ps cls \<Longrightarrow>
               cls ccs CAS\<^sup>R[lib a, False, u, u']\<^sub>t cls' ccs'\<Longrightarrow>
               agt c d ps' cls' \<Longrightarrow>  
               same_except_for_pc_and_top ps ps' \<Longrightarrow>
               agt c d ps cls"
  apply(simp add: agt_def clss_def)
  apply(subgoal_tac "nxt_rel ps cls = nxt_rel ps' cls'")
   apply (simp add: nxt_rel_def)
  apply (simp add: nxt_rel_def)
  apply safe
  apply(rule_tac x= aaa in exI)
  apply safe
  apply(simp add: globals)
  using failed_CAS_preserves_last by auto




lemma agt_pushed_same2wr: " glb_inv ps cls \<Longrightarrow>
a \<notin> pushed_addr ps \<Longrightarrow> a\<in>addr_val ps \<Longrightarrow>
               cls ccs [lib a := v]\<^sub>t cls' ccs'\<Longrightarrow>
               agt c d ps cls \<Longrightarrow>  
               same_except_for_pc_and_top ps ps' \<Longrightarrow>
               agt c d ps' cls'"
  apply(simp add: agt_def clss_def)
  apply(subgoal_tac "nxt_rel ps cls \<subseteq> nxt_rel ps' cls'")
   apply (simp add: nxt_rel_def)
  apply (simp add: trancl_mono)
  apply (simp add: nxt_rel_def)
  apply safe
  apply(rule_tac x= aaa in exI)
  apply safe
  apply(simp add: globals)
   by (metis wr_preserves_last)


lemma agt_pushed_same2wr_before_state: " glb_inv ps cls \<Longrightarrow>
                a \<notin> pushed_addr ps \<Longrightarrow> a\<in>addr_val ps \<Longrightarrow>
               cls ccs [lib a := v]\<^sub>t cls' ccs'\<Longrightarrow>
               agt c d ps' cls' \<Longrightarrow>  
               same_except_for_pc_and_top ps ps' \<Longrightarrow>
               agt c d ps cls"
  apply(simp add: agt_def clss_def)
  apply(subgoal_tac "nxt_rel ps cls = nxt_rel ps' cls'")
   apply simp
  apply (simp add: nxt_rel_def written_addr_def globals)
  apply safe
  apply (metis wr_preserves_last)
  apply (metis wr_preserves_last)
  apply (metis wr_preserves_last)
  by (metis wr_preserves_last)



lemma agt_pushed_same2wr_nxt: " glb_inv ps cls \<Longrightarrow>
a \<notin> pushed_addr ps \<Longrightarrow> a\<in>addr_val ps \<Longrightarrow>
               cls ccs [lib (a+1) := v]\<^sub>t cls' ccs'\<Longrightarrow>
               agt c d ps cls \<Longrightarrow>  
               same_except_for_pc_and_top ps ps' \<Longrightarrow>
               agt c d ps' cls'"
  apply(simp add: agt_def clss_def)
  apply(subgoal_tac "nxt_rel ps cls \<subseteq> nxt_rel ps' cls'")
   apply (simp add: nxt_rel_def)
  apply (simp add: trancl_mono)
  apply (simp add: nxt_rel_def)
  apply safe
  apply(rule_tac x= aaa in exI)
  apply safe
  apply(simp add: globals)
  by (metis Suc_inject wr_preserves_last)



lemma agt_pushed_same2wr_nxt_before_state: " glb_inv ps cls \<Longrightarrow>
a \<notin> pushed_addr ps \<Longrightarrow> a\<in>addr_val ps \<Longrightarrow>
               cls ccs [lib (a+1) := v]\<^sub>t cls' ccs'\<Longrightarrow>
               agt c d ps' cls' \<Longrightarrow>  
               same_except_for_pc_and_top ps ps' \<Longrightarrow>
               agt c d ps cls"
  apply(simp add: agt_def clss_def)
  apply(subgoal_tac "nxt_rel ps cls \<subseteq> nxt_rel ps' cls'")
   apply (simp add: nxt_rel_def)
  apply (smt Collect_cong nat.inject wr_preserves_last)
  apply (simp add: nxt_rel_def)
  apply safe
  apply(rule_tac x= aaa in exI)
  apply safe
  apply(simp add: globals)
  by (metis Suc_inject wr_preserves_last)


lemma agt_pushed_same2rd: "cls ccs [a \<leftarrow>\<^sup>A lib b]\<^sub>t cls' ccs' \<Longrightarrow>
   agt c d ps cls \<Longrightarrow>  pushed_addr ps' = pushed_addr ps
 \<Longrightarrow> agt c d ps' cls'"
  apply(simp add: agt_def clss_def)
  apply(subgoal_tac "nxt_rel ps cls \<subseteq> nxt_rel ps' cls'")
  using trancl_mono apply blast
  apply (simp add: nxt_rel_def)
  by (simp add: rd_A_preserves_last)

lemma agt_pushed_same2rd_relax: "cls ccs [a \<leftarrow> lib b]\<^sub>t cls' ccs' \<Longrightarrow>  
 agt c d ps cls \<Longrightarrow>  pushed_addr ps' = pushed_addr ps \<Longrightarrow> agt c d ps' cls'"
  apply(simp add: agt_def clss_def)
  apply(subgoal_tac "nxt_rel ps cls \<subseteq> nxt_rel ps' cls'")
  using trancl_mono apply blast
  apply (simp add: nxt_rel_def)
  by (simp add: rd_preserves_last)


lemma agt_pushed_same2rd_before_state: "cls ccs [a \<leftarrow>\<^sup>A lib b]\<^sub>t cls' ccs' \<Longrightarrow> 
  agt c d ps' cls' \<Longrightarrow>  pushed_addr ps' = pushed_addr ps \<Longrightarrow> agt c d ps cls"
  apply(simp add: agt_def clss_def)
  apply(subgoal_tac "nxt_rel ps cls = nxt_rel ps' cls'")
  using trancl_mono apply blast
  apply (simp add: nxt_rel_def)
  by (simp add: rd_A_preserves_last)

lemma agt_pushed_same2rd_relax_before_state: "cls ccs [a \<leftarrow> lib b]\<^sub>t cls' ccs' \<Longrightarrow> 
  agt c d ps' cls' \<Longrightarrow>  pushed_addr ps' = pushed_addr ps \<Longrightarrow> agt c d ps cls"
  apply(simp add: agt_def clss_def)
  apply(subgoal_tac "nxt_rel ps cls = nxt_rel ps' cls'")
  using trancl_mono apply blast
  apply (simp add: nxt_rel_def)
  by (simp add: rd_preserves_last)


lemma agt_pushed_same3: "a\<notin>pushed_addr ps \<Longrightarrow>  b\<in>pushed_addr ps \<Longrightarrow> 
 agt b c ps cls \<Longrightarrow>  pushed_addr ps' = pushed_addr ps \<union> {a} \<Longrightarrow> agt b c ps' cls"
  apply(simp add: agt_def clss_def)
  apply(subgoal_tac "nxt_rel ps cls\<subseteq> nxt_rel ps' cls")
  using trancl_mono apply blast
  apply(simp add: nxt_rel_def)
  by auto

lemma clss_same: "a\<notin>pushed_addr ps \<Longrightarrow> pushed_addr ps' = pushed_addr ps 
      \<Longrightarrow> clss ps' cls = clss ps cls"
  apply(simp add: clss_def)
  by (metis (full_types) nxt_rel_subset1 subset_antisym)


lemma a_not_in_pushed_nxt_rel:  "a \<notin> pushed_addr ps \<Longrightarrow> (a,b)\<notin>nxt_rel ps cls"
   apply(simp add: clss_def nxt_rel_def)
  done

lemma a_not_in_pushed_clss:  "a \<notin> pushed_addr ps \<Longrightarrow> (a,b)\<notin>clss ps cls"
  apply(simp add: clss_def)
  by (meson a_not_in_pushed_nxt_rel tranclD)


lemma not_dom: "glb_inv ps cls \<Longrightarrow>  a\<notin>pushed_addr ps \<Longrightarrow> a \<noteq> Null \<Longrightarrow> a \<notin> Domain (nxt_rel ps cls)"
  apply (simp add: agt_def clss_def nxt_rel_def)
  by auto

lemma not_range: "glb_inv ps cls \<Longrightarrow>  a\<notin>pushed_addr ps \<Longrightarrow> a \<noteq> Null \<Longrightarrow> a \<notin> Range (nxt_rel ps cls)"
  apply (simp add: agt_def globals  clss_def nxt_rel_def)
  by auto

lemma a_not_in_range: "glb_inv ps cls \<Longrightarrow> a \<noteq> Null 
    \<Longrightarrow>   a\<notin>pushed_addr ps \<Longrightarrow> pushed_addr ps' = pushed_addr ps \<union> {a} 
    \<Longrightarrow> lastNxtVal cls a \<noteq> a \<Longrightarrow> a\<notin>Range (clss ps' cls)"
  apply (simp add:  clss_def)
  apply (simp add:  clss_def nxt_rel_def)
  using not_range 
  by (smt Null_def RangeE Suc_eq_plus1 glb_inv8_def globals(1) lastVal_def mem_Collect_eq neq0_conv prod.sel(2))

lemma a_not_in_clss_prime: "glb_inv ps cls \<Longrightarrow> a \<noteq> Null \<Longrightarrow>  a\<notin>pushed_addr ps \<Longrightarrow> pushed_addr ps' = pushed_addr ps \<union> {a} \<Longrightarrow> lastNxtVal cls a \<noteq> a \<Longrightarrow> (a,a)\<notin>clss ps' cls"
  by (meson Range_iff a_not_in_range)


lemma failed_cas_preserves_clss: "cls ccs CAS\<^sup>R[lib(x), False, v, u]\<^sub>t cls' ccs' \<Longrightarrow> 
    pushed_addr ps' = pushed_addr ps \<Longrightarrow>
   clss ps' cls' = clss ps cls"
  apply(simp add: clss_def nxt_rel_def)
  by (simp add: failed_CAS_preserves_last)

lemma or_union_eq: "finite P \<Longrightarrow>
        {(x, f x) | x . x\<in>P \<or> x = a} = insert (a, f a) {(x, f x) | x . x\<in>P}"
  apply safe
      apply simp
    apply simp
   apply simp
  by simp

lemma or_union_eq': "finite (pushed_addr ps)  \<Longrightarrow>
  {(a, lib_value cls' (lib_lastWr cls' (Suc a))) |a.
          a = n_val ps t \<or> a \<in> pushed_addr ps} =
         insert (n_val ps t, lib_value cls' (lib_lastWr cls' (Suc (n_val ps t))))
          {(a, lib_value cls' (lib_lastWr cls' (Suc a))) | a.
           a \<in> pushed_addr ps}"
  using or_union_eq[where a = "n_val ps t" and P = "pushed_addr ps"]
  by blast


lemma tc1: "a\<in>f \<Longrightarrow> f' = f - {a} \<Longrightarrow> f'\<^sup>+\<subseteq>f\<^sup>+" 
  by (simp add: subrelI trancl_mono)

lemma to1: "to ps cls \<Longrightarrow> glb ps cls \<Longrightarrow>
       glb_inv ps cls \<Longrightarrow> Null \<notin> Domain (nxt_rel ps cls)"
  by (meson Domain.simps a_not_in_pushed_nxt_rel agt_def to_def to_p3_def to_p4_def)

lemma to2: "to ps cls \<Longrightarrow> glb ps cls \<Longrightarrow>
       glb_inv ps cls \<Longrightarrow> Null \<notin> Domain (clss ps cls)"
  by (metis clss_def to1 trancl_domain)

lemma a_nxt_null_smallest: "to ps cls \<Longrightarrow> glb ps cls \<Longrightarrow>
       glb_inv ps cls \<Longrightarrow> a\<in>pushed_addr ps \<Longrightarrow> b\<in>pushed_addr ps \<Longrightarrow> a\<noteq>b \<Longrightarrow>
       lastNxtVal cls a = Null \<Longrightarrow> agt b a ps cls"
  apply(simp add: agt_def)
  apply(subgoal_tac "(a,Null)\<in>clss ps cls") defer  
   apply (simp add: agt_def to_def to_p3_def)
  apply(subgoal_tac "(a, Null)\<in>nxt_rel ps cls") defer
   apply(simp add: nxt_rel_def)
  apply(subgoal_tac "\<forall> add. add\<in>pushed_addr ps \<and> add \<noteq> a \<longrightarrow> (add, Null)\<notin>nxt_rel ps cls")
  defer apply (intro allI impI)
   apply(simp add: nxt_rel_def globals)
   apply (metis bot.not_eq_extremum bot_nat_def)
  apply(simp add:  globals to_p2_def to_p3_def to_p4_def agt_def clss_def)
  by (metis (no_types, hide_lams)  a_not_in_pushed_nxt_rel trancl.cases)


lemma nothing_between_a_nxt: "to ps cls \<Longrightarrow> glb ps cls \<Longrightarrow>
       glb_inv ps cls \<Longrightarrow> a\<in>pushed_addr ps \<Longrightarrow>
      x\<in>pushed_addr ps \<Longrightarrow> agt a x ps cls \<Longrightarrow> x\<noteq> lastNxtVal cls a \<Longrightarrow> x\<noteq>a \<Longrightarrow> agt (lastNxtVal cls a) x ps cls"
    apply(simp add:  globals to_p2_def to_p3_def to_p4_def)
  apply safe
     apply (metis a_not_in_pushed_clss agt_def )
  by (smt Suc_eq_plus1 agt_def clss_def converse_tranclE fst_conv lastVal_def mem_Collect_eq nxt_rel_def prod.sel(2))


lemmas to_simps = to_def to_p1_def to_p2_def to_p4_def to_p3_def
definition "rel_img r e \<equiv> {a . (e, a)\<in>r}"
definition "rel_dr r e \<equiv> {(e,a) | a . (e, a)\<in>r}"

lemma domain_clss: "to ps cls \<Longrightarrow> glb ps cls \<Longrightarrow> glb_inv ps cls
     \<Longrightarrow> Domain (clss ps cls) = pushed_addr ps"
  apply(simp add: clss_def nxt_rel_def globals )
  apply safe
     apply auto[1]
  by blast


lemma range_clss: "to ps cls \<Longrightarrow> glb ps cls \<Longrightarrow> glb_inv ps cls
     \<Longrightarrow> Range (clss ps cls) = (pushed_addr ps \<union> {Null}) - {lastTop cls}"
  apply(simp add: clss_def nxt_rel_def globals to_p2_def to_p3_def to_p4_def)
  apply safe
                 apply auto[2]
               apply(simp_all) 
     apply fastforce   apply(simp add: agt_def clss_def nxt_rel_def)
  apply (meson Range.intros trancl.cases)
  apply (meson a_not_in_pushed_clss agt_def subset_iff)
  apply(simp add: agt_def clss_def nxt_rel_def)
  by (metis (mono_tags, lifting) Range.intros trancl_range)


lemma ntop_other_stable: 
    "t \<noteq> ta \<Longrightarrow> lib_pop t v ps cls ccs ps' cls' ccs' \<Longrightarrow>
 pc ps t = L2  \<Longrightarrow> ntop ps' ta = ntop ps ta"
  apply (subgoal_tac "ta \<noteq> t \<longrightarrow> ntop ps' ta = ntop ps ta")
  apply simp
  by (simp add: lib_pop_def)

lemma read_lib_d_obs: "lib_wfs cls ccs \<Longrightarrow> cls ccs [ r \<leftarrow> lib x]\<^sub>t cls' ccs'
 \<Longrightarrow> [lib x =\<^sub>t n] cls \<Longrightarrow> r = n"
  apply(simp add: lib_read_step_def lib_d_obs_def lib_d_obs_t_def, elim exE conjE)
  apply(simp add: lib_read_def all_updates_l)
  apply(case_tac "lib_syncing cls (a, b) False", simp_all)
   apply (simp add: lib_syncing_def)
  apply(simp add: lib_wfs_def lib_syncing_def lib_visible_writes_def lib_writes_on_def lib_value_def tst_def var_def lib_lastWr_def)
  apply clarsimp
  by (metis (mono_tags, lifting) Max.coboundedI antisym finite_imageI image_eqI mem_Collect_eq snd_conv)


lemma l5: "glb ps cls \<Longrightarrow> glb_inv12 ps cls \<Longrightarrow> glb_inv10 ps cls \<Longrightarrow> 
glb_inv6 ps cls \<Longrightarrow> glb_inv3 ps cls \<Longrightarrow> glb_inv4 ps cls \<Longrightarrow> glb_inv5 ps cls
 \<Longrightarrow> to ps cls \<Longrightarrow> lastTop cls \<noteq> Null \<Longrightarrow> lastVal cls ((lastTop cls) + 1) = Null  \<Longrightarrow> pushed_addr ps \<subseteq> {lastTop cls}"
  apply (simp add: globals  agt_def clss_def nxt_rel_def to_p3_def)
  apply safe
     apply simp  
  apply(subgoal_tac "Null\<notin>pushed_addr ps") defer
   apply auto[1]
  apply simp
  by (smt mem_Collect_eq old.prod.inject tranclE)


lemma Top_next_not_null: "glb ps cls \<Longrightarrow> to ps cls \<Longrightarrow>  glb_inv ps cls \<Longrightarrow> 
  e\<in>pushed_addr ps \<Longrightarrow> e \<noteq> lastTop cls \<Longrightarrow> lastTop cls \<noteq> Null \<Longrightarrow> 
  lastNxtVal cls (lastTop cls) \<noteq> Null"
  apply(simp add: glb_inv_def)
  using TS_Proof_Rules.l5 by auto


lemma TopLV_Null_pushed_empty: 
  "to ps cls \<Longrightarrow> glb_inv ps cls \<Longrightarrow> glb ps cls \<Longrightarrow> lastTop cls = Null
 \<Longrightarrow> pushed_addr ps = {}"
  apply (simp add: globals to_p3_def  agt_def clss_def nxt_rel_def)
  apply safe
  by (smt Collect_empty_eq Collect_empty_eq_bot bot_set_def empty_Collect_eq ex_in_conv exists_least_iff less_numeral_extra(3) mem_Collect_eq neq0_conv neqE not_less_zero of_nat_0_less_iff of_nat_eq_iff of_nat_less_0_iff of_nat_less_iff old.prod.exhaust old.prod.inject  singleton_conv singleton_conv2 surj_pair tranclE trancl_trans zero_less_imp_eq_int)

lemma agt_order: "agt a b ps cls \<Longrightarrow> agt b c ps  cls \<Longrightarrow> agt a c ps cls "
  apply(simp add:  agt_def clss_def nxt_rel_def)
  done


lemma TopLV_agt_others: 
  "to ps cls \<Longrightarrow> glb_inv ps cls \<Longrightarrow> glb ps cls \<Longrightarrow> b \<noteq> lastTop cls 
       \<Longrightarrow> lastTop cls \<noteq> Null \<Longrightarrow> b\<in>pushed_addr ps
       \<Longrightarrow> agt (lastTop cls) b ps cls"
  apply (simp add: globals to_p3_def  agt_def clss_def nxt_rel_def)
  apply safe
  by (smt Collect_empty_eq Collect_empty_eq_bot bot_set_def empty_Collect_eq ex_in_conv exists_least_iff less_numeral_extra(3) mem_Collect_eq neq0_conv neqE not_less_zero of_nat_0_less_iff of_nat_eq_iff of_nat_less_0_iff of_nat_less_iff old.prod.exhaust old.prod.inject  singleton_conv singleton_conv2 surj_pair tranclE trancl_trans zero_less_imp_eq_int)


lemma failed_CAS_R_preserves_dobs:
  assumes "[lib(x) =\<^sub>t u] cls"
    and "cls ccs CAS\<^sup>R[lib(y), False, u, u']\<^sub>t' cls' ccs'"
    and "lib_wfs cls ccs"
    and "wfs ccs"
  shows "[lib(x) =\<^sub>t u] cls'"
  using assms
  apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
  apply(case_tac "lib_value cls (a, b) = u", simp_all)
   using failed_CASR_pres_d_obs_lib by blast


lemma failed_cas_dobs_to:
"lib_wfs cls ccs \<Longrightarrow> wfs ccs \<Longrightarrow>
 dobs_to t ps cls ccs \<Longrightarrow> pushed_addr ps' = pushed_addr ps \<Longrightarrow> top ps' = top ps \<Longrightarrow>
 cls ccs CAS\<^sup>R[lib Top, False, u, u']\<^sub>t' cls' ccs'\<Longrightarrow>
 dobs_to t ps' cls' ccs'"
  apply(simp add: dobs_to_def same_except_for_pc_and_top_def)
  apply(intro conjI allI impI)
  apply(subgoal_tac "\<exists>vl. [libad =\<^sub>t vl] cls") 
  apply(elim exE, rule_tac x=vl in exI)
  using failed_CAS_R_preserves_dobs   
   apply (meson failed_CASR_pres_d_obs_lib)
  apply(subgoal_tac "agt (prog_state.top ps t) ad ps' cls' = agt (prog_state.top ps t) ad ps cls")
  apply blast
   apply(simp add: agt_def clss_def)
  apply (metis clss_def failed_cas_preserves_clss)
   apply(simp add: agt_def clss_def)
  by (smt clss_def failed_CASR_pres_d_obs_lib failed_cas_preserves_clss)


lemma read_pres_last_val:
  assumes "wfs ccs"
      and "lib_wfs cls ccs"
      and "lib_read_step t' x b cls ccs cls' ccs' v "
    shows "lib_value cls' (lib_lastWr cls' y) = lib_value cls (lib_lastWr cls y)"
  using assms
  apply(simp add: lib_read_step_def lib_value_def lib_lastWr_def, elim exE)
  apply(simp add: lib_read_def all_updates_l)
  by (simp add: read_pres_writes_on_diff_var)

lemma cobs_to_read_pres:
  assumes "wfs ccs"
      and "lib_wfs cls ccs"
      and "cobs_to t ps cls ccs"
      and "lib_read_step t' x b cls ccs cls' ccs' v "
      and "pushed_addr ps' = pushed_addr ps"
    shows "cobs_to t ps' cls' ccs'"
  using assms
  apply(simp add: cobs_to_def)
  apply safe
     apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libad2 =\<^sub>t vl \<rparr> cls")
      apply(elim exE conjE)
      apply(rule_tac x=vl in exI)
  using lib_c_obs_lib_only_pres_read_var apply blast
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
     apply (simp add: read_pres_last_val)
     apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
      apply(elim exE conjE)
      apply(rule_tac x=vl in exI)
  using lib_c_obs_lib_only_pres_read_var apply blast
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
  apply (simp add: read_pres_last_val)
 using lib_c_obs_lib_only_pres_read_var apply blast
  using lib_c_obs_lib_only_pres_read_var by blast


lemma cobs_to_CAS_pres:
  assumes "wfs ccs"
      and "lib_wfs cls ccs"
      and "cobs_to t ps cls ccs"
      and "cls ccs CAS\<^sup>R[lib Top, False, u, u']\<^sub>t' cls' ccs'"
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
  apply (simp add: failed_CAS_preserves_last)
     apply(subgoal_tac "\<exists>vl. [libTop = ad1]\<lparr>libSuc(ad2) =\<^sub>t vl \<rparr> cls")
      apply(elim exE conjE)
     apply(rule_tac x=vl in exI)
  using failed_CASR_pres_c_obs_lib_only apply auto[1]
  apply(subgoal_tac "agt ad1 ad2 ps' cls' = agt ad1 ad2 ps cls")
      apply simp
     apply(simp add: agt_def clss_def nxt_rel_def)
  apply(subgoal_tac "{(a, lib_value cls' (lib_lastWr cls' (Suc a))) |a.
           a \<in> pushed_addr ps} = {(a, lib_value cls (lib_lastWr cls (Suc a))) |a.
           a \<in> pushed_addr ps}")
      apply simp
     apply(subgoal_tac "\<forall> a . a\<in>pushed_addr ps \<longrightarrow> lib_value cls' (lib_lastWr cls' (Suc a)) = lib_value cls (lib_lastWr cls (Suc a))")
     apply auto[1]
  using failed_CAS_preserves_last apply auto[1]
  using failed_CASR_pres_c_obs_lib_only apply blast
  using failed_CASR_pres_c_obs_lib_only apply blast
  done

lemma no_Top_n_written_addr: "no_Top_n t ps cls \<longrightarrow> n_val ps t \<notin> written_addr cls
        \<and> n_nxt ps t \<notin> written_addr cls"
  apply(simp add: no_Top_n_def written_addr_def)
  by fastforce

lemma pobs_cobs_same_val: "lib_wfs cls ccs \<Longrightarrow> wfs ccs \<Longrightarrow> [lib(a)\<approx>\<^sub>t u]cls \<Longrightarrow> [lib(a)\<approx>\<^sub>t' u]cls \<Longrightarrow> [lib(a) = u]\<lparr>lib(b) =\<^sub>t u'\<rparr> cls \<Longrightarrow> [lib(a) = u]\<lparr>lib(b) =\<^sub>t' v'\<rparr> cls \<Longrightarrow> t\<noteq>t' \<Longrightarrow> u' = v'"
  by (smt lib_c_obs_lib_only_def lib_d_obs_def lib_p_obs_def)


lemma dobs_pobs_cobs_same_val: "lib_wfs cls ccs \<Longrightarrow> wfs ccs \<Longrightarrow>
   [lib(b) =\<^sub>t v']cls \<Longrightarrow> [lib(a)\<approx>\<^sub>t u]cls \<Longrightarrow> [lib(a) = u]\<lparr>lib(b) =\<^sub>t u'\<rparr> cls  \<Longrightarrow> u' = v'"
  by (smt lib_c_obs_lib_only_def lib_d_obs_def lib_d_obs_t_def lib_p_obs_def)


lemma pobs_cobs_dobs_same_val: "lib_wfs cls ccs \<Longrightarrow> wfs ccs \<Longrightarrow> [lib(a)\<approx>\<^sub>t u]cls \<Longrightarrow> 
 [lib(a) = u]\<lparr>lib(b) =\<^sub>t u'\<rparr> cls \<Longrightarrow> [lib(b) =\<^sub>t' v'] cls \<Longrightarrow> t\<noteq>t' \<Longrightarrow> u' = v'"
  by (smt lib_c_obs_lib_only_def lib_d_obs_def lib_d_obs_t_def lib_p_obs_def)

lemma successful_CAS_lib_c_obs_lib_pre_same_value_pres2:
  assumes "wfs cs"
  and "lib_wfs ls cs" 
  and "[lib(x) = u]\<lparr>lib(y) =\<^sub>t v \<rparr> cls"
  and "[lib(y) =\<^sub>t' v] cls"
  and "[lib(x) \<approx>\<^sub>t u] cls"
  and "\<not>[lib(x) \<approx>\<^sub>t' u] cls"
  and "cls ccs CAS\<^sup>R[lib(x), True, m, u]\<^sub>t' cls' ccs'"
  and "t \<noteq> t'"
  and "x \<noteq> y"
shows "[lib(x) = u]\<lparr>lib(y) =\<^sub>t v \<rparr> cls'"
  using assms
  apply(simp add: lib_c_obs_lib_only_def lib_visible_writes_def)
  apply(intro allI impI conjI, elim conjE)
  apply(simp add: lib_d_obs_def lib_d_obs_t_def)
   apply(intro conjI, elim conjE)
    apply(simp add: lib_CAS_Rel_step_def, elim conjE exE)
    apply(case_tac "lib_value cls (aa, ba) = m", simp_all)
    apply(simp add: lib_update_r_def all_updates_l)
  apply safe
  using a_is_x apply blast
  using a_is_x apply blast
  using a_is_x apply blast
  apply(simp add: lib_lastWr_def)
  using CAS_Rel_preserves_writes_on_diff_var assms(7) apply auto[1]
  apply(simp add: lib_lastWr_def lib_writes_on_def)
  using a_is_x apply blast
    apply(simp add: lib_visible_writes_def lib_lastWr_def lib_writes_on_def lib_valid_fresh_ts_def tst_def var_def lib_value_def)
  apply safe
  apply (smt Collect_cong fst_conv)
  using succ_CAS_preserves_last apply blast
    apply(simp add: lib_CAS_Rel_step_def, elim conjE exE)
    apply(case_tac "lib_value cls (aa, ba) = m", simp_all)
    apply(simp add: lib_update_r_def all_updates_l lib_releasing_def)
 apply safe
  by (smt CAS_Rel_preserves_releasing_new CAS_Rel_preserves_value_old a_is_x assms(7) fun_upd_other lib_releasing_def lib_state.ext_inject lib_state.surjective lib_state.update_convs(1) lib_state.update_convs(2) lib_state.update_convs(3) lib_state.update_convs(4) lib_state.update_convs(5) lib_visible_writes_def mem_Collect_eq ts_not_in_writes_on)


lemma nxt_a_b_not_agt_b_a: "glb_inv ps cls \<Longrightarrow> to ps cls \<Longrightarrow> a\<in>pushed_addr ps \<Longrightarrow> b\<in>pushed_addr ps \<Longrightarrow>
 lastNxtVal cls a = b \<Longrightarrow> \<not>agt b a ps cls"
  apply simp
  apply(simp add: globals to_p2_def to_p3_def to_p4_def agt_def clss_def nxt_rel_def )
  apply safe
   apply (metis (no_types, lifting) trancl_trans)
  by (metis (mono_tags, lifting) mem_Collect_eq trancl_into_trancl2)


lemma nxt_rel_after_successful_CAS: "glb ps cls \<Longrightarrow> glb_inv ps cls \<Longrightarrow> to ps cls \<Longrightarrow> 
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
  done

lemma "no_Top_n t' ps cls \<Longrightarrow> \<not>[lib(Top) \<approx>\<^sub>t (n_val ps t')] cls"
  apply(simp add: no_Top_n_def)
  by (simp add: no_Top_n_def no_Top_n_implies_no_p_obs)





lemma agt_pres_diff_write:  "cls ccs [lib(a) := b]\<^sub>t cls' ccs' \<Longrightarrow> a \<notin> pushed_addr ps \<Longrightarrow>  pushed_addr ps' = pushed_addr ps
\<Longrightarrow> (\<forall> e . e\<in>pushed_addr ps \<longrightarrow> Suc e \<noteq> a)
\<Longrightarrow> agt c d ps cls = agt c d ps' cls'"
  apply(simp add : agt_def clss_def)
  apply(subgoal_tac "nxt_rel ps' cls' = nxt_rel ps cls")
   apply auto[1]
   apply(simp add: nxt_rel_def)
  using wr_preserves_last by auto


lemma agt_ad2_pushed_or_null: "glb_inv ps cls \<Longrightarrow> to ps cls \<Longrightarrow> agt ad1 ad2 ps cls \<Longrightarrow> ad2\<in>pushed_addr ps \<union> {Null}"
  apply(simp add: agt_def clss_def)
  by (metis Null_def Range.intros not_range trancl_range)


lemma agt_n_val_False: "(\<forall> p . p\<in>pushed_addr ps \<longrightarrow> lastVal cls (Suc p)  \<noteq> ad2) \<Longrightarrow>
 agt ad1 ad2 ps cls \<Longrightarrow> False"
  apply(simp add: agt_def clss_def )
  apply(subgoal_tac "ad2\<notin>Range (nxt_rel ps cls)")
   apply (metis Range.intros trancl_range)
  apply(simp add: nxt_rel_def)
  by blast


lemma agt_ad1_not_in_pushed_False: "ad1\<notin>pushed_addr ps \<Longrightarrow>
 agt ad1 ad2 ps cls \<Longrightarrow> False"
  apply(simp add: agt_def clss_def nxt_rel_def)
  by (smt Pair_inject converse_tranclE mem_Collect_eq)




end
