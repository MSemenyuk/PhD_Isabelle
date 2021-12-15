theory RCU_Lems imports OpSem_ProofRules "HOL-Hoare_Parallel.OG_Syntax"
begin


(*
lemma d_obs_diff_false [simp]:
  assumes  "[x =\<^sub>t u] \<sigma>"
and "[x =\<^sub>t' v] \<sigma>"
and "u \<noteq> v"
shows "False"
  using assms
  by (simp add: d_obs_def d_obs_t_def)  
*)

lemma p_obs_contradiction_2 :
  assumes "wfs \<sigma>"
  and "\<not> [x \<approx>\<^sub>t v] \<sigma>"
  and " getVW \<sigma> t' y = w"
shows "\<not> [x \<approx>\<^sub>t v] (read_trans t' b w \<sigma>)"
  using OpSemExtProof.p_obs_contradiction assms(1) assms(2) assms(3) by blast


lemma not_p_obs_other_value  :
  assumes "wfs \<sigma>"
      and "\<not>[x \<approx>\<^sub>t u] \<sigma>"
      and "var w = x"
      and "ts' = getTS \<sigma> w"
      and "u \<noteq> v"
      and "t \<noteq> t'"
    shows "\<not>[x \<approx>\<^sub>t u] (write_trans t' b w v \<sigma> ts')"
  using assms
  apply simp
  apply(unfold  write_trans_def rev_app_def update_wa_def update_thrView_def update_modView_def update_mods_def)
  apply simp
  apply (unfold p_obs_def)
  apply safe
  apply(simp add: value_def)

  apply(case_tac "a = var w \<and> ba = getTS \<sigma> w", simp_all)
  apply(simp add: visible_writes_def)
  unfolding writes_on_def apply clarsimp 
  by blast

lemma c_obs_same_var_read_pres[simp]:
  assumes "wfs \<sigma>"
and " [x = u]\<lparr>x =\<^sub>t u\<rparr> \<sigma>"
and "w = getVW \<sigma> t' y"
shows "[x = u]\<lparr>x =\<^sub>t u\<rparr> (read_trans t' b w \<sigma>)"
  using assms
  apply (case_tac "x \<noteq> y")
  apply(simp add: c_obs_def visible_writes_def value_def d_obs_def)
  apply(simp add: read_trans_def rev_app_def)
  apply(unfold  writes_on_def lastWr_def, simp)
  apply(simp add: update_wa_def update_thrView_def update_mods_def update_modView_def)
  apply(case_tac "x = var (getVW \<sigma> t y)", simp_all)
   apply (simp add: getVW_var)
  apply safe
  apply(simp_all add:releasing_def)
     apply (smt fun_upd_other order.trans ts_oride_def)
    apply (smt fun_upd_other order.trans ts_oride_def)
  apply (smt fun_upd_other order.trans ts_oride_def)
  apply(simp add: c_obs_def visible_writes_def value_def d_obs_def)
  apply(simp add: read_trans_def  rev_app_def)
  apply(unfold  writes_on_def lastWr_def, simp)
  apply(simp add: update_wa_def update_thrView_def update_mods_def update_modView_def)
  apply safe
  apply(simp_all add:releasing_def visible_writes_def)
  apply (smt CollectD dual_order.trans getVW_in_vw ts_oride_same_var visible_writes_def)
  apply (smt CollectD dual_order.trans getVW_in_vw ts_oride_same_var visible_writes_def)
  apply (smt CollectD dual_order.trans getVW_in_vw ts_oride_same_var visible_writes_def)
  apply (smt CollectD dual_order.trans getVW_in_vw ts_oride_same_var visible_writes_def)
  apply (smt CollectD dual_order.trans getVW_in_vw ts_oride_same_var visible_writes_def)
  apply (smt CollectD dual_order.trans getVW_in_vw ts_oride_same_var visible_writes_def)
  by (simp add: getVW_var)+

(*"x = var w"*)
lemma c_obs_same_var_write_pres[simp]:
  assumes "wfs \<sigma>"
and "[x =\<^sub>t u] \<sigma>"
and "\<not> [x \<approx>\<^sub>t' u] \<sigma>"
and "w = getVWNC \<sigma> t x" 
and "ts' = getTS \<sigma> w"
shows "[x = u]\<lparr>x =\<^sub>t' u\<rparr> (write_trans t b w u \<sigma> ts')"
  using assms
  apply(simp add: c_obs_def visible_writes_def value_def d_obs_def)
  apply(simp add: write_trans_def rev_app_def)
  apply(unfold  writes_on_def lastWr_def, simp)
  apply(simp add: update_wa_def update_thrView_def update_mods_def update_modView_def)
  by (metis d_obs_def d_obs_t_def lastWr_visible p_obs_def)



lemma c_obs_same_var_write_pres_diff[simp]:
  assumes "wfs \<sigma>"
and "[x =\<^sub>t v] \<sigma>"
and "\<not> [x \<approx>\<^sub>t' u] \<sigma>"
and "getVWNC \<sigma> t x = w"
and "ts' = getTS \<sigma> w"
shows "[x = u]\<lparr>x =\<^sub>t' u\<rparr> (write_trans t True w u \<sigma> ts')"
proof - 
  from assms have a1: "[x =\<^sub>t u] (write_trans t True w u \<sigma> ts')"
    using OpSemExtProof.ext_d_obs_d_obs by blast
  show ?thesis
  using assms a1
  apply(simp add: c_obs_def p_obs_def d_obs_t_def visible_writes_def value_def d_obs_def)
  apply(simp add: write_trans_def rev_app_def)
  apply(unfold  writes_on_def lastWr_def, simp)
  apply(simp add: update_wa_def update_thrView_def update_mods_def update_modView_def)
  apply safe
  apply (simp_all add: getVW_var releasing_def)
         apply auto[2]
  apply (metis (no_types, lifting) assms(2) d_obs_def d_obs_t_def dual_order.trans getTS_w_greater_tst_w getVWNC_lastWr less_eq_rat_def snd_conv)
  apply (metis (no_types, lifting) assms(2) d_obs_def d_obs_t_def dual_order.trans getTS_w_greater_tst_w getVWNC_lastWr less_eq_rat_def snd_conv)
  by blast+
qed




lemma c_obs_same_var_write_same_var_pres[simp]:
  assumes "wfs \<sigma>"
and " [x = u]\<lparr>x =\<^sub>t u\<rparr> \<sigma>"
and "w = getVWNC \<sigma> t' x"
and "ts' = getTS \<sigma> w"
and "[x =\<^sub>t' z] \<sigma>"
and "v \<noteq> u"
and "z \<noteq> u"
shows "[x = u]\<lparr>x =\<^sub>t u\<rparr> (write_trans t' b w v \<sigma> ts')"
  using assms
  apply(simp add: c_obs_def visible_writes_def value_def d_obs_def d_obs_t_def)
  apply(simp add: write_trans_def  rev_app_def)
  apply(unfold  writes_on_def lastWr_def, simp)
  apply(simp add: update_wa_def update_thrView_def update_mods_def update_modView_def)
  apply(case_tac "x \<noteq> var (getVWNC \<sigma> t' x)", simp_all)
   apply (simp add: getVWNC_var)
  apply(case_tac "t = t'", simp_all)
  apply(simp_all add: releasing_def)
  apply(intro conjI impI allI)
  apply (metis (no_types, lifting) assms(5) d_obs_def d_obs_t_def dual_order.strict_trans getVWNC_in_writes_on getVWNC_lastWr getTS_w_greater_tst_w last_write_max2 not_le_imp_less order.not_eq_order_implies_strict) 
  apply (metis (no_types, lifting) assms(5) d_obs_def d_obs_t_def dual_order.strict_trans getVWNC_in_writes_on getVWNC_lastWr getTS_w_greater_tst_w last_write_max2 not_le_imp_less order.not_eq_order_implies_strict)
  apply (metis (no_types, lifting) assms(5) d_obs_def d_obs_t_def dual_order.strict_trans getVWNC_in_writes_on getVWNC_lastWr getTS_w_greater_tst_w last_write_max2 not_le_imp_less order.not_eq_order_implies_strict)
  by (metis (no_types, lifting) assms(5) d_obs_def d_obs_t_def dual_order.strict_trans getVWNC_in_writes_on getVWNC_lastWr getTS_w_greater_tst_w last_write_max2 not_le_imp_less order.not_eq_order_implies_strict)



lemma c_obs_write_diff_var_pres[simp]:
  assumes "wfs \<sigma>"
and " [x = u]\<lparr>x =\<^sub>t u\<rparr> \<sigma>"
and " y \<noteq>x"
and "w = getVWNC \<sigma> t' y"
and "ts' = getTS \<sigma> w"
shows "[x = u]\<lparr>x =\<^sub>t u\<rparr> (write_trans t' b w v \<sigma> ts')"
  using assms
  apply(simp add: c_obs_def visible_writes_def value_def d_obs_def d_obs_t_def)
  apply(simp add: write_trans_def  rev_app_def)
  apply(unfold  writes_on_def lastWr_def, simp)
  apply(simp add: update_wa_def update_thrView_def update_mods_def update_modView_def)
  apply(case_tac "x \<noteq> var (getVWNC \<sigma> t' x)", simp_all)
   apply (simp add: getVWNC_var)
  apply(case_tac "t = t'", simp_all)
  apply(simp_all add: releasing_def)
   apply(intro conjI impI allI)
  apply (simp_all add: getVWNC_var) 
  apply (metis fst_conv)
  apply (smt Collect_cong fst_conv)
  apply (metis fst_conv)
  apply (smt Collect_cong fst_conv)
  by (smt Collect_cong fst_conv)

  
lemma no_val_maintain:
  assumes "wfs \<sigma>"
and "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
and "getVWNC \<sigma> t y = w"
and "y \<noteq> x"
and "getTS \<sigma> w = ts'"
shows "[\<zero>\<^sub>x u]\<^sub>i (write_trans t b w v \<sigma> ts')"
  using assms
  apply(simp add: no_val_def p_vorder_def value_def mo_def init_val_def)
  apply(elim conjE impE exE)
  apply (simp add: write_trans_def)
  apply safe
   apply(subgoal_tac "var w = y", simp)
  prefer 2
    apply (simp add: getVWNC_var)
    apply (simp add: rev_app_def update_wa_def update_mods_def update_thrView_def update_modView_def)
  apply (unfold writes_on_def, clarsimp)
    apply metis
    apply (simp add: rev_app_def update_wa_def update_mods_def update_thrView_def update_modView_def)
  apply (clarsimp)    
  by (simp add: getVWNC_var)

lemma d_order_stable:
  assumes "wfs \<sigma>"
and "[i \<hookrightarrow>\<^sub>x u] \<sigma>"
shows "[i \<hookrightarrow>\<^sub>x u] (read_trans t' b w \<sigma>)"
  using assms
  by(simp add: d_vorder_def p_vorder_def value_def)

(*
lemma dvorder_intro:
  assumes "wfs \<sigma>"
    and "[\<one>\<^sub>x u] \<sigma>"
    and "[\<zero>\<^sub>x v]\<^sub>i \<sigma>"
and "[x =\<^sub>t u] \<sigma>"
and "w = getVWNC \<sigma> t x"
and "ts' = getTS \<sigma> w"
and "v \<noteq> u"
and "i \<noteq> u"
and "i \<noteq> v"
shows "[u \<hookrightarrow>\<^sub>x v] (write_trans t b w v \<sigma> ts')"
*)

lemma no_val_d_order:
  assumes "wfs \<sigma>"
and "[x =\<^sub>t i] \<sigma>"
and "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
and "getVWNC \<sigma> t x = w"
and "getTS \<sigma> w = ts'"
and "u \<noteq> i"
shows "[i \<hookrightarrow>\<^sub>x u] (write_trans t b w u \<sigma> ts')"
proof - 
  have a1: "[en x i]\<^sub>t \<sigma>"
  using assms
  apply(simp add: no_val_def enc_t_def enc_def value_def mo_def init_val_def d_vorder_def d_obs_t_def d_obs_def)
  by (metis eq_iff less_imp_le sndI wfs_def)  
  show ?thesis
  using assms a1
    apply(subgoal_tac "var w = x") 
   defer
  using getVWNC_var apply blast
  apply(simp add: d_obs_def no_val_def init_val_def enc_t_def enc_def amo_def d_vorder_def p_vorder_def mo_def d_obs_t_def)
  apply(intro conjI allI impI)
  apply (metis w_in_writes_on_var)
   apply(elim conjE exE)
   apply (unfold writes_on_def value_def, clarsimp)
     apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
   apply (case_tac "a = x \<and> ba = getTS \<sigma> (getVWNC \<sigma> t x)", simp_all)
  apply (case_tac "aa = x \<and> baa = getTS \<sigma> (getVWNC \<sigma> t x)", simp_all)
  apply (metis dual_order.strict_trans fst_conv getTS_w_greater_tst_w getVWNC_lastWr in_writes_onI last_write_max2 less_linear)
  apply blast
   apply(elim conjE exE)
  apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
  by (metis dual_order.strict_trans2 getVWNC_lastWr getts_greater_than leD)
qed



lemma d_order_write_twice:
  assumes "wfs \<sigma>"
and "[u \<hookrightarrow>\<^sub>x v] \<sigma>"
and "[x =\<^sub>t v] \<sigma>"
and "getVWNC \<sigma> t x = w"
and "getTS \<sigma> w = ts'"
shows "[u \<hookrightarrow>\<^sub>x v] (write_trans t b w v \<sigma> ts')"
  using assms 
    apply(subgoal_tac "var w = x") 
   defer
  using getVWNC_var apply blast
  apply(unfold d_obs_def no_val_def init_val_def enc_t_def enc_def amo_def d_vorder_def p_vorder_def mo_def d_obs_t_def)
  apply(intro conjI allI impI)
    apply(elim conjE exE)
  apply (metis writes_on_var)
   apply (unfold writes_on_def value_def, clarsimp)
     apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
   apply (case_tac "baa = getTS \<sigma> (getVWNC \<sigma> t x)", simp_all)
    apply (case_tac "ba = getTS \<sigma> (getVWNC \<sigma> t x)", simp_all)
  apply blast 
  apply (metis fst_conv getVWNC_lastWr getts_greater_than less_le_not_le less_trans modView_lte_last neqE own_ModView sndI)
  apply (case_tac "ba = getTS \<sigma> (getVWNC \<sigma> t x)", simp_all)
  apply blast
  apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
  by (metis fst_conv in_writes_onI w_not_in_writes_on)


lemma no_val_d_order_one:
  assumes "wfs \<sigma>"
and "[\<one>\<^sub>x i] \<sigma>"
and "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
and "getVWNC \<sigma> t x = w"
and "getTS \<sigma> w = ts'"
and "u \<noteq> i"
shows "[i \<hookrightarrow>\<^sub>x u] (write_trans t b w u \<sigma> ts')"
proof - 
  have a1: "[en x i]\<^sub>t \<sigma>"
  using assms
  apply(simp add: no_val_def enc_t_def enc_def value_def mo_def init_val_def d_vorder_def)
  by (metis eq_iff less_imp_le sndI wfs_def)  
  show ?thesis
  using assms a1
    apply(subgoal_tac "var w = x") 
   defer
  using getVWNC_var apply blast
  apply(simp add: d_obs_def no_val_def init_val_def enc_t_def enc_def amo_def d_vorder_def p_vorder_def mo_def d_obs_t_def)
  apply(intro conjI allI impI)
  apply (metis w_in_writes_on_var)
   apply(elim conjE exE)
   apply (unfold writes_on_def value_def, clarsimp)
     apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
   apply (case_tac "a = x \<and> ba = getTS \<sigma> (getVWNC \<sigma> t x)", simp_all)
  apply (case_tac "aa = x \<and> baa = getTS \<sigma> (getVWNC \<sigma> t x)", simp_all)
  apply (smt CollectD getTS_w_greater_tst_w getVWNC_in_visible_writes less_le_trans not_le visible_writes_def)
  apply blast
   apply(elim conjE exE)
     apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
  by (metis Set.basic_monos(7) getTS_w_greater_tst_w getVWNC_in_visible_writes le_less_trans less_eq_rat_def prod.exhaust_sel visible_writes_in_writes)
qed
(*
  sledgehammer
  apply (simp add: w_in_writes_on_var)
  sorry
     apply (metis dual_order.trans getVWNC_lastWr getTS_w_greater_tst_w last_write_max2 less_eq_rat_def not_less_iff_gr_or_eq)
  apply (meson w_in_writes_on_var)
   apply(simp add: value_def)
     apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
  apply(case_tac "a = x \<and>
               ba = getTS \<sigma> (getVWNC \<sigma> t x)", simp)
  apply(case_tac "aa = x \<and>
               baa = getTS \<sigma> (getVWNC \<sigma> t x)", simp) 
    apply (metis getVWNC_lastWr getts_greater_than last_write_max2)
  apply simp 
   apply (metis w_in_writes_on_var w_is)
  apply (simp add: value_def)
  apply(rule_tac x = x in exI)
  apply simp
       apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
  by (metis getVWNC_in_writes_on getVWNC_lastWr getts_greater_than w_is)
*)

(*

       [0 \<hookrightarrow>\<^sub>x Suc 0] \<sigma> xa \<or> [x =\<^sub>3 0] \<sigma> xa \<Longrightarrow>
       wfs (\<sigma> xa) \<Longrightarrow>
       w \<noteq> x \<Longrightarrow>
       r xa = Suc 0 \<Longrightarrow>
       \<forall>j. 0 < j \<and> j \<noteq> Suc 0 \<longrightarrow> \<not> [x \<approx>\<^sub>2 j] \<sigma> xa \<Longrightarrow>
       [en x Suc 0]\<^sub>2 \<sigma> xa \<Longrightarrow>
       j \<noteq> Suc 0 \<Longrightarrow>
       [x \<approx>\<^sub>2 j] \<sigma> xa \<Longrightarrow> [x =\<^sub>3 Suc 0] \<sigma> xa \<Longrightarrow> False
*)

lemma d_vorder_not_pobs: 
  assumes "wfs \<sigma>"
and "[u \<hookrightarrow>\<^sub>x v] \<sigma>"
and "[en x v]\<^sub>t \<sigma>"
shows "\<not> [x \<approx>\<^sub>t u] \<sigma>"
  using assms 
  apply(simp add: p_obs_def enc_def enc_t_def d_vorder_def p_vorder_def) 
  by (metis (mono_tags) dual_order.trans leD mem_Collect_eq mo_def snd_conv visible_writes_def writes_on_def)


lemma c_obs_pres_write_diff_var_ext_2  :
  assumes "wfs \<sigma>"
      and "[x = u]\<lparr>y =\<^sub>t v\<rparr> \<sigma>"
      and "getVWNC \<sigma> t' z = w"
      and "x \<noteq> z"
      and "y \<noteq> z" 
      and "t \<noteq> t'"
      and " getTS \<sigma> w = ts'"
    shows "[x = u]\<lparr>y =\<^sub>t v\<rparr> (write_trans t' b w v' \<sigma> ts')"
  using assms
  apply(simp add: p_obs_def d_obs_def d_obs_t_def c_obs_def visible_writes_def value_def)
  apply(intro conjI impI allI, elim conjE)
    apply (unfold writes_on_def write_trans_def rev_app_def update_wa_def
        update_mods_def getVWNC_var lastWr_def update_modView_def update_thrView_def value_def, simp)
    apply safe[1]
  using getVWNC_var apply (blast+)[3]
  using getVWNC_var apply (blast+)[3]
  apply (case_tac "x = var (getVWNC \<sigma> t' z) \<and> ba = getTS \<sigma> (getVWNC \<sigma> t' z)", simp_all)
  apply (metis eq_fst_iff)
  apply (metis eq_fst_iff)
    apply safe[1]
  using getVWNC_var apply (blast+)[3]
  apply (case_tac "x = var (getVWNC \<sigma> t' z) \<and> ba = getTS \<sigma> (getVWNC \<sigma> t' z)", simp_all)
  using getVWNC_var apply (blast+)[2]
  apply (case_tac "x = var (getVWNC \<sigma> t' z) \<and> ba = getTS \<sigma> (getVWNC \<sigma> t' z)", simp_all)
  using getVWNC_var apply blast
  apply (smt Collect_cong fst_conv)
  apply (case_tac "x = var (getVWNC \<sigma> t' z) \<and> ba = getTS \<sigma> (getVWNC \<sigma> t' z)", simp_all)
  using getVWNC_var apply blast
  apply (smt Collect_cong fst_conv getVWNC_var)
    apply safe[1]
  using getVWNC_var apply blast
  apply (case_tac "x = var (getVWNC \<sigma> t' z) \<and> ba = getTS \<sigma> (getVWNC \<sigma> t' z)", simp_all)
  using getVWNC_var apply blast
  apply (clarsimp)
  by (metis (no_types, lifting) Pair_inject fun_upd_same fun_upd_triv fun_upd_twist releasing_def surrey_state.select_convs(4) surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(4) surrey_state.update_convs(5))

end