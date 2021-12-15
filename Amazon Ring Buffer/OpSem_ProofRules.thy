theory OpSem_ProofRules
imports Main OpSemSyntax_Def
begin

lemmas defs [simp] =  Rd_def Let_def Wr_def Upd_def st_rd_def val_rd_def


lemma read_pres_d_obs [simp]:
  assumes "wfs \<sigma>"
    and "[x =\<^sub>t u] \<sigma>"
  shows "[x =\<^sub>t u] (st_rd(Rd y t' b \<sigma>))"
 apply simp
  using assms(1) assms(2) ext_d_obs_rd_pres3 by blast


lemma read_pres_wfs [simp]:
  assumes "wfs \<sigma>"
  shows "wfs (st_rd(Rd x t b \<sigma>))"
  by (simp add: assms read_pres_wfs)

lemma write_pres_wfs [simp]:
  assumes "wfs \<sigma>"
  shows "wfs (Wr x v t b \<sigma>)"
  by (simp add: assms write_pres_wfs)


lemma update_pres_wfs [simp]:
  assumes "wfs \<sigma>"
  shows "wfs (st_rd(Upd x u t \<sigma>))"
  by (simp add: assms update_pres_wfs)


lemma ext_d_obs_d_obs [simp]:
  assumes "wfs \<sigma>"
      and "[x =\<^sub>t v] \<sigma>"
    shows"[x =\<^sub>t u] (Wr x u t b \<sigma>)"
  using assms
  apply simp
  using assms(1) assms(2) ext_d_obs_d_obs by blast

  
lemma ext_upd_d_obs_d_obs [simp]:
  assumes "wfs \<sigma>"
      and "[x =\<^sub>t v] \<sigma>"
    shows"[x =\<^sub>t u] (st_rd(Upd x u t \<sigma>))"
  apply simp 
  using assms ext_upd_d_obs_d_obs by blast

lemma d_obs_read_value [simp]:
  assumes "wfs \<sigma>"
    and "[x =\<^sub>t u] \<sigma>"
  shows "val_rd(Rd x t False \<sigma>) = u"
  apply simp  
  using assms(1) assms(2) d_obs_value by auto
  
lemma d_obs_diff_false [simp]:
  assumes  "[x =\<^sub>t u] \<sigma>"
and "[x =\<^sub>t' v] \<sigma>"
and "u \<noteq> v"
shows "False"
  using assms
  by (simp add: d_obs_def d_obs_t_def)  


lemma OG_14 [simp]:
  assumes "wfs \<sigma>"
  and "[x =\<^sub>t u] \<sigma>"
  and "[x =\<^sub>t' v] \<sigma>"
   and "t \<noteq> t'"
  and "v \<noteq> u"
shows "[x =\<^sub>t u] (Wr x u t' False \<sigma>)"
  apply simp
  using OpSemExtProof.d_obs_diff_false assms(1) assms(2) assms(3) assms(5) by blast
 

lemma ext_write_other_pres_d_obs [simp]:
  assumes "wfs \<sigma>"
      and "[x =\<^sub>t u] \<sigma>"
      and "y \<noteq> x"
    shows"[x =\<^sub>t u] (Wr y v t' b \<sigma>)"
  by (simp add: assms(1) assms(2) assms(3) ext_write_other_pres_d_obs)
  

lemma not_p_obs_other_pres_not_p_obs [simp]:
  assumes "wfs \<sigma>"
      and "\<not>[x \<approx>\<^sub>t u] \<sigma>"
      and "y \<noteq> x"
    shows "\<not>[x \<approx>\<^sub>t u] (Wr y v t' b \<sigma>)"
  by (simp add: assms(1) assms(2) assms(3) not_p_obs_other_pres_not_p_obs)


lemma not_p_obs_write_pres_c_obs_diff_var [simp]:
  assumes "wfs \<sigma>"
  and "\<not>[x \<approx>\<^sub>t u] \<sigma>"
   and "t \<noteq> t'"
  and "x \<noteq> y"
  shows "[x = u]\<lparr>y =\<^sub>t v\<rparr> (Wr y z t' b \<sigma>)"
  by (simp add: assms(1) assms(2) assms(3) assms(4) not_p_obs_write_pres_c_obs_diff_var)


lemma ext_c_obs_intro [simp]:
  assumes "wfs \<sigma>"
  and "[y =\<^sub>t v] \<sigma>"
  and "\<not>[x \<approx>\<^sub>t' u] \<sigma>"
  and "x \<noteq> y"
  and "t \<noteq> t'"
  shows "[x = u]\<lparr>y =\<^sub>t' v\<rparr> (Wr x u t True \<sigma>)"
  by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) ext_c_obs_intro)

lemma c_obs_read_pres [simp]:
  assumes "wfs \<sigma>"
  and "[x = u]\<lparr>y =\<^sub>t v\<rparr> \<sigma>"
  shows "[x = u]\<lparr>y =\<^sub>t v\<rparr> (st_rd(Rd x t b \<sigma>))"
  by (simp add: assms(1) assms(2) c_obs_read_pres)


lemma c_obs_read_d_obs [simp]:
  assumes "wfs \<sigma>"
      and "[x = u]\<lparr>y =\<^sub>t v\<rparr> \<sigma>"
      and "val_rd(Rd x t True \<sigma>) = u"
    shows "[y =\<^sub>t v] (st_rd(Rd x t True \<sigma>))"
  using assms
  apply simp
  by (simp add: c_obs_read_d_obs)


lemma p_obs_write_2 [simp]:
  assumes "wfs \<sigma>"
  shows "[x \<approx>\<^sub>t u] (Wr x u t b \<sigma>)"
  using assms by simp 



lemma not_p_obs_read [simp]:
  assumes "wfs \<sigma>"
and "\<not>[x \<approx>\<^sub>t u] \<sigma>"
shows "\<not>[x \<approx>\<^sub>t u] (st_rd(Rd y t b \<sigma>))"
  by (simp add: assms(1) assms(2)  not_p_obs_read)

lemma d_obs_diff_c_obs [simp]:
  assumes "[x =\<^sub>t z] \<sigma>"
    and "wfs \<sigma>"
  and "z \<noteq> u"
shows "[x = u]\<lparr>y =\<^sub>t v\<rparr> \<sigma>"
  using assms
  using d_obs_p_obs_agree not_p_obs_implies_c_obs by blast

lemma d_obs_not_p_obs [simp]:
  assumes "wfs \<sigma>"
and "[x =\<^sub>t z] \<sigma>"
  and "z \<noteq> u"
  shows "\<not>[x \<approx>\<^sub>t u] \<sigma>"
  using assms(1) assms(2) assms(3) d_obs_p_obs_agree by auto


lemma init_rd_pres [simp]:
  assumes "wfs \<sigma>"
  and " [init x u] \<sigma>"
    shows "[init x u]  (st_rd(Rd y t b \<sigma>))"
  by (simp add: assms(1) assms(2)  init_rd_pres)


lemma init_wr_pres [simp]:
  assumes "wfs \<sigma>"
  and " [init x u] \<sigma>"
    shows "[init x u] (Wr y v t b \<sigma>)"
    by (simp add: assms(1) assms(2)  init_wr_pres)



lemma init_upd_pres [simp]:
  assumes "wfs \<sigma>"
  and " [init x u] \<sigma>"
    shows "[init x u]  (st_rd(Upd y v t \<sigma>))"
  by (simp add: assms(1) assms(2) init_upd_pres)

lemma covered_wr_diif_var_pres [simp]:
  assumes "wfs \<sigma>"
  and "cvd[x, u] \<sigma>"
  and "x \<noteq> y"
  shows "cvd[x, u] (Wr y v t b \<sigma>)"
  by (simp add: assms(1) assms(2) assms(3)  covered_wr_diif_var_pres)


lemma c_obs_pres_write_diff_var_ext [simp]:
  assumes "wfs \<sigma>"
      and "[x = u]\<lparr>y =\<^sub>t v\<rparr> \<sigma>"    
      and "x \<noteq> z"
      and "y \<noteq> z"   
    shows "[x = u]\<lparr>y =\<^sub>t v\<rparr> (Wr z v t b \<sigma>)"
  by (simp add: assms(1) assms(2) assms(3) assms(4) c_obs_pres_write_diff_var_ext)


lemma covered_update_pres_ext [simp]:
  assumes "cvd[x, u] \<sigma>"
  and "wfs \<sigma>"
shows "cvd[x, v] (st_rd(Upd x v t \<sigma>))"
  apply simp 
  using assms(1) assms(2) ext_cvd_update_cvd by auto

lemma update_diff_var_pres_dobs_ext [simp]:
  assumes "[x =\<^sub>t u] \<sigma>"
  and "wfs \<sigma>"
  and "y \<noteq> x"
shows "[x =\<^sub>t u] (st_rd(Upd y v t' \<sigma>))"
  by (simp add: assms(1) assms(2) assms(3) update_diff_var_pres_dobs_ext)


lemma ext_cvd_update_d_obs [simp]:
  assumes "wfs \<sigma>"
      and "[x = u]\<lparr>y =\<^sub>t v\<rparr> \<sigma>"
      and "cvd[x, u] \<sigma>"
      and "x \<noteq> y"
    shows "[y =\<^sub>t v] (st_rd(Upd x m t \<sigma>))"
  apply simp 
  using assms(1) assms(2) assms(3) assms(4) ext_cvd_update_d_obs by blast  

lemma ext_cvd_up_dobs [simp]: 
  assumes  "cvd[x, u] \<sigma>"
    and "wfs \<sigma>"
    shows "[x =\<^sub>t v] (st_rd(Upd x v t \<sigma>))"
  apply simp 
  using assms(1) assms(2) ext_cvd_up_dobs by blast

lemma ext_cvd_rd_pres [simp]:
     assumes  "cvd[x, u] \<sigma>"
    and "wfs \<sigma>"
    shows "cvd[x, u]  (st_rd(Rd y t b \<sigma>))"  
  by (simp add: assms(1) assms(2)  ext_cvd_rd_pres)



lemma ext_c_obs_Up_intro [simp]: 
  assumes  "wfs \<sigma>"
  and  "[y =\<^sub>t v] \<sigma>"
  and  " \<not> [x \<approx>\<^sub>t' u] \<sigma>"
  and  "x \<noteq> y"  
  and "t' \<noteq> t"
shows "[x = u]\<lparr>y =\<^sub>t' v\<rparr> (st_rd(Upd x u t \<sigma>))"
  apply simp  
  by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) ext_c_obs_Up_intro)



lemma ext_c_obs_rdx_pres [simp]:
  assumes  "wfs \<sigma>"
  and  "[x = u]\<lparr>y =\<^sub>t' v\<rparr> \<sigma>"
  and  "y \<noteq> x"  
  and "t \<noteq> t'"
shows "[x = u]\<lparr>y =\<^sub>t' v\<rparr> (st_rd(Rd z t b \<sigma>))"
  by (simp add: assms(1) assms(2) assms(3) assms(4)  ext_c_obs_rdx_pres)


lemma ext_p_obs_contradiction [simp]:
  assumes "wfs \<sigma>"
and "\<not>[x \<approx>\<^sub>t u] \<sigma>"
and "x \<noteq> y"
and "[x \<approx>\<^sub>t u] (st_rd(Rd y t' b \<sigma>))"
shows "False"
  using assms apply simp  
  using ext_p_obs_contradiction by blast
  

lemma ext_d_obs_rd_pres [simp]:
  assumes "wfs \<sigma>"
and "[x =\<^sub>t u] \<sigma>"
shows "[x =\<^sub>t u] (st_rd(Rd y t' b \<sigma>))"
  apply simp
  using assms(1) assms(2) ext_d_obs_rd_pres3 by auto



lemma ext_p_obs_rd_pres [simp]:
  assumes "wfs \<sigma>"
and "[x \<approx>\<^sub>t u] \<sigma>"
and " getVW \<sigma> t' y = w"
and "t \<noteq> t'"
shows "[x \<approx>\<^sub>t u] (st_rd(Rd y t' b \<sigma>))"
  using assms
  apply simp
  apply(unfold p_obs_def read_trans_def)
  apply(unfold rev_app_def Let_def update_thrView_def)
  apply(simp add: value_def)
  apply(case_tac "syncing \<sigma> w b")
   apply simp
   apply(unfold visible_writes_def writes_on_def, simp)
  by simp


lemma p_obs_contradiction [simp]:
  assumes "wfs \<sigma>"
  and "\<not> [x \<approx>\<^sub>t v] \<sigma>"
  and  "[x \<approx>\<^sub>t v] (st_rd(Rd y t' b \<sigma>))"
  shows "False"
  using assms
  apply simp
  apply(unfold p_obs_def read_trans_def)
  apply(unfold rev_app_def Let_def update_thrView_def)
  apply(simp add: value_def)
  using assms(2) assms(3) p_obs_contradiction by fastforce

lemma amo_intro:
  assumes "wfs \<sigma>"
    and "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
    and "getVWNC \<sigma> t x = w"
    and "getTS \<sigma> w = ts'"
    and "u \<noteq> i"
  shows "[\<one>\<^sub>x u] (write_trans t b w u \<sigma> ts')"
  using assms
  apply(simp add: no_val_def amo_def p_vorder_def value_def init_val_def)
  apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
  apply(intro allI impI)
  apply(simp add: mo_def)
  apply(intro conjI impI allI)
    apply (subgoal_tac "var w = x")
     apply simp
     apply(elim conjE exE)
     apply(unfold writes_on_def)
 apply simp 
     apply blast 
    apply simp
  apply simp
   apply auto[1]
  apply simp
  by blast


lemma amo_intro_n [simp]:
  assumes "wfs \<sigma>"
    and "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
    and "u \<noteq> i"
  shows "[\<one>\<^sub>x u] (Wr x u t b \<sigma>)"
  apply simp   
  using amo_intro assms(1) assms(2) assms(3) by auto

lemma amo_wr_pres :
  assumes "wfs \<sigma>"
    and "[\<one>\<^sub>x u] \<sigma>"
    and "w = getVWNC \<sigma> t x "
    and "ts' = getTS \<sigma> w"
    and "u \<noteq> v"
  shows "[\<one>\<^sub>x u] (write_trans t b w v \<sigma> ts')"
  using assms
  apply(simp add: no_val_def amo_def p_vorder_def value_def init_val_def)
  apply(intro allI impI)
  apply(simp add: mo_def)
  apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
     apply(unfold writes_on_def)
  apply simp 
  by (smt write_record.select_convs(1))

lemma amo_wr_pres_n [simp] :
  assumes "wfs \<sigma>"
    and "[\<one>\<^sub>x u] \<sigma>"
    and "u \<noteq> v"
  shows "[\<one>\<^sub>x u] (Wr x v t b \<sigma>)"
  apply simp 
  by (simp add: amo_wr_pres assms(1) assms(2) assms(3))


lemma no_val_contradition:
  assumes "wfs \<sigma>"
and "[init x i] \<sigma>"
and "\<not>[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
and "u \<noteq> i"
and "getVWNC \<sigma> t x = w"
and "getTS \<sigma> w = ts'"
and "[\<zero>\<^sub>x u]\<^sub>i (write_trans t b w v \<sigma> ts')"
shows "False"
  using assms
  apply(simp add: no_val_def p_vorder_def value_def mo_def init_val_def)
  apply(elim conjE exE impE)
  apply(subgoal_tac "var w = x")
  apply simp
   apply(elim disjE conjE)
    apply (metis  getVWNC_in_writes_on getTS_w_greater_tst_w order.asym w_in_writes_on_var w_not_in_writes_on)
  apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
   apply(case_tac "bb = ts'")
  apply simp  
  apply (meson w_not_in_writes_on)  
   apply simp 
   apply (smt w_not_in_writes_on)  
  by (meson getVWNC_in_writes_on writes_on_var)


lemma no_val_contradition_n [simp]:
  assumes "wfs \<sigma>"
and "[init x i] \<sigma>"
and "\<not>[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
and "u \<noteq> i"
and "[\<zero>\<^sub>x u]\<^sub>i (Wr x v t b \<sigma>)"
shows "False"
  using assms
  apply simp
  using no_val_contradition by blast

lemma no_val_contradition_auto [simp]:
  assumes "wfs \<sigma>"
and "[init x i] \<sigma>"
and "\<not>[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
and "u \<noteq> i"
and "w = getVWNC \<sigma> t x "
and "ts' = getTS \<sigma> w "
and "[\<zero>\<^sub>x u]\<^sub>i (Wr x j t b \<sigma>)"
shows "[x  =\<^sub>t' z] (Wr x j t b \<sigma>)"
  using assms
  apply simp
  using no_val_contradition by blast


lemma no_val_contradiction2:
assumes "wfs \<sigma>"
and "[\<zero>\<^sub>x  u]\<^sub>i \<sigma>" 
and "w = getVWNC \<sigma> t x"
and "ts'=  getTS \<sigma> w"
and "[\<zero>\<^sub>x u]\<^sub>i (write_trans t b w u \<sigma> ts')"
shows "False"
  using assms 
  apply (simp add: no_val_def p_vorder_def mo_def value_def init_val_def)
  apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
  apply (unfold writes_on_def, simp)
  apply(subgoal_tac "var w = x")
   apply simp
   apply(elim conjE exE)
   apply(case_tac "ba = ts'")
  apply simp  
  apply (metis w_in_writes_on_var w_not_in_writes_on wfs_def)
   apply simp 
   defer
   apply (simp add: getVWNC_var)
proof -
fix ba :: rat and baa :: rat
assume a1: "ts' = getTS \<sigma> (getVWNC \<sigma> t x)"
  assume a2: "w = getVWNC \<sigma> t x"
  assume a3: "\<forall>ba. (ba = getTS \<sigma> (getVWNC \<sigma> t x) \<longrightarrow> (\<forall>ba. val (if ba = getTS \<sigma> (getVWNC \<sigma> t x) then \<lparr>val = u, is_releasing = b\<rparr> else mods \<sigma> (x, ba)) = u \<longrightarrow> u = i \<longrightarrow> (x, ba) \<in> surrey_state.writes \<sigma> \<longrightarrow> \<not> getTS \<sigma> (getVWNC \<sigma> t x) < ba)) \<and> ((x, ba) \<in> surrey_state.writes \<sigma> \<longrightarrow> (\<forall>bb. val (if bb = getTS \<sigma> (getVWNC \<sigma> t x) then \<lparr>val = u, is_releasing = b\<rparr> else mods \<sigma> (x, bb)) = u \<longrightarrow> val (if ba = getTS \<sigma> (getVWNC \<sigma> t x) then \<lparr>val = u, is_releasing = b\<rparr> else mods \<sigma> (x, ba)) = i \<longrightarrow> (bb = getTS \<sigma> (getVWNC \<sigma> t x) \<longrightarrow> \<not> ba < getTS \<sigma> (getVWNC \<sigma> t x)) \<and> ((x, bb) \<in> surrey_state.writes \<sigma> \<longrightarrow> \<not> ba < bb)))"
  assume a4: "val (if baa = getTS \<sigma> (getVWNC \<sigma> t x) then \<lparr>val = u, is_releasing = b\<rparr> else mods \<sigma> (x, baa)) = i"
  assume a5: "\<forall>b. (b = getTS \<sigma> (getVWNC \<sigma> t x) \<longrightarrow> baa \<noteq> getTS \<sigma> (getVWNC \<sigma> t x) \<longrightarrow> baa < getTS \<sigma> (getVWNC \<sigma> t x)) \<and> ((x, b) \<in> surrey_state.writes \<sigma> \<longrightarrow> baa \<noteq> b \<longrightarrow> baa < b)"
  assume a6: "baa = getTS \<sigma> (getVWNC \<sigma> t x) \<or> (x, baa) \<in> surrey_state.writes \<sigma>"
  assume a7: "ba \<noteq> getTS \<sigma> (getVWNC \<sigma> t x)"
  assume a8: "(x, ba) \<in> surrey_state.writes \<sigma>"
  assume a9: "val (mods \<sigma> (x, ba)) = i"
  obtain bb :: bool where
    f10: "(\<not> bb) = (\<forall>X2. X2 \<noteq> ts' \<or> val (if X2 = ts' then \<lparr>val = u, is_releasing = b\<rparr> else mods \<sigma> (x, X2)) \<noteq> u)"
    by moura
have f11: "getTS \<sigma> w = ts'"
  using a2 a1 by meson
  obtain bba :: bool where
    f12: "(\<not> bba) = (\<forall>X1. (\<not> X1 < ts' \<or> (x, X1) \<notin> surrey_state.writes \<sigma>) \<or> val (if X1 = ts' then \<lparr>val = u, is_releasing = b\<rparr> else mods \<sigma> (x, X1)) \<noteq> i)"
    by moura
  then have f13: "\<not> bba \<or> \<not> bb"
    using f11 f10 a3 a2 by blast
  have f14: "val (if baa = ts' then \<lparr>val = u, is_releasing = b\<rparr> else mods \<sigma> (x, baa)) = i"
    using f11 a4 a2 by meson
  have "\<not> bba"
    using f13 f10 by simp
  then have f15: "ts' = baa"
    using f14 f12 f11 a6 a5 a2 by (metis (no_types))
  obtain bbb :: bool where
    f16: "(\<not> bbb) = (\<forall>X1. ((\<not> ts' < X1 \<or> (x, X1) \<notin> surrey_state.writes \<sigma>) \<or> i \<noteq> u) \<or> val (if X1 = ts' then \<lparr>val = u, is_releasing = b\<rparr> else mods \<sigma> (x, X1)) \<noteq> u)"
    by moura
then have "\<not> bbb"
using f11 a3 a2 by meson
  then show ?thesis
    using f16 f15 f14 f11 a9 a8 a7 a5 a2 by auto
qed



lemma no_val_contradition_auto2 [simp]:
assumes "wfs \<sigma>"
and "[\<zero>\<^sub>x  u]\<^sub>i \<sigma>" 
and "w = getVWNC \<sigma> t x"
and "ts'=  getTS \<sigma> w"
and "[\<zero>\<^sub>x u]\<^sub>i (Wr x u t b \<sigma>)"
shows "[x  =\<^sub>t' z]  (Wr x u t b \<sigma>)"
  using assms
  apply simp
  using no_val_contradiction2 by blast

lemma amo_wr_pres_diff_var:
  assumes "wfs \<sigma>"
    and "[\<one>\<^sub>x u] \<sigma>"
    and "w = getVWNC \<sigma> t y "
    and "ts' = getTS \<sigma> w"
    and "y \<noteq> x"
  shows "[\<one>\<^sub>x u] (write_trans t b w v \<sigma> ts')"
  using assms
  apply(simp add: amo_def p_vorder_def value_def mo_def)
  apply(intro allI impI)
  apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
  apply(unfold writes_on_def, simp)
  apply(subgoal_tac "var w = y", simp)
   apply blast
  using getVWNC_var by blast

lemma amo_wr_pres_diff_var_n [simp]:
  assumes "wfs \<sigma>"
    and "[\<one>\<^sub>x u] \<sigma>"
    and "y \<noteq> x"
  shows "[\<one>\<^sub>x u] (Wr y v t b \<sigma>)"
  apply simp 
  using amo_wr_pres_diff_var assms(1) assms(2) assms(3) by auto

lemma amo_rd_pres [simp]:
  assumes "wfs \<sigma>"
    and "[\<one>\<^sub>x u] \<sigma>"
  shows "[\<one>\<^sub>x u] (st_rd(Rd y t b \<sigma>))"
  using assms
  by(simp add: amo_def p_vorder_def value_def)
  

lemma w_is: "wfs \<sigma> \<Longrightarrow> tst w = ts \<Longrightarrow> var w = x \<Longrightarrow> w = (x, ts)"  
  using prod.exhaust_sel by blast


lemma enc_intro:
  assumes "wfs \<sigma>"
and "w = getVW \<sigma> t x"
and "value \<sigma> w = u"
shows "[en x u]\<^sub>t (read_trans t b w \<sigma>)"
  using assms
  apply (simp add: enc_t_def enc_def value_def)
  apply(subgoal_tac "var w  = x")
   defer
  using getVW_var apply blast
  apply(subgoal_tac "tst w =  tst (getVW \<sigma> t x)")
   defer
   apply clarsimp
    apply(subgoal_tac "w = (x, tst (getVW \<sigma> t x))")
   defer
    using w_is apply blast
  apply(rule_tac x = x in exI)
  apply(rule_tac x = "tst w" in exI)
    apply(intro conjI)
   using getVW_in_writes_on apply auto[1]
  apply(simp add: read_trans_def  rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)    
     apply (simp add: ts_oride_def) 
    by simp

lemma enc_intro_n [simp]:
  assumes "wfs \<sigma>"
and " (val_rd(Rd x t b \<sigma>)) = u"
shows "[en x u]\<^sub>t (st_rd(Rd x t b \<sigma>))"
  apply simp
  using assms(1) assms(2) enc_intro by auto

lemma enc_c_obs_intro:
  assumes "wfs \<sigma>"
and "w = getVW \<sigma> t y"
and "[y = u]\<lparr>x =\<^sub>t v\<rparr> \<sigma>"
and "value \<sigma> w = u"
and "x \<noteq> y"
shows "[en x v]\<^sub>t (read_trans t True w \<sigma>)"
  using assms
  apply(simp add: c_obs_def enc_def enc_t_def value_def)  
proof -
  assume a1: "w = getVW \<sigma> t y"
assume a2: "wfs \<sigma>"
  assume a3: "\<forall>w\<in>visible_writes \<sigma> t y. val (mods \<sigma> w) = u \<longrightarrow> d_obs \<sigma> (modView \<sigma> w) x v \<and> releasing \<sigma> w"
  assume a4: "val (mods \<sigma> (getVW \<sigma> t y)) = u"
  then have "\<exists>n. [x =\<^sub>t n] (read_trans t True w \<sigma>)"
    using a2 a1 OpSemExtProof.c_obs_read_d_obs assms(3) value_def by blast
  then show "\<exists>n r. (n, r) \<in> writes_on \<sigma> x \<and> r \<le> tst (thrView (read_trans t True (getVW \<sigma> t y) \<sigma>) t x) \<and> val (mods \<sigma> (n, r)) = v"
    using a4 a3 a2 a1 by (metis (no_types) d_obs_def d_obs_t_def getVW_in_vw lastWr_read_pres last_write_write_on old.prod.exhaust order_refl snd_conv value_def)
qed
 

lemma enc_c_obs_intro_n [simp]:
  assumes "wfs \<sigma>"
and "[y = u]\<lparr>x =\<^sub>t v\<rparr> \<sigma>"
and " (val_rd(Rd y t True \<sigma>)) = u"
and "x \<noteq> y"
shows "[en x v]\<^sub>t (st_rd(Rd y t True \<sigma>))"
  apply simp
  using assms(1) assms(2) assms(3) assms(4) enc_c_obs_intro by auto

lemma no_val_read_pres :
  assumes "wfs \<sigma>"
  and "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
  and "w = getVW \<sigma> t y"
shows "[\<zero>\<^sub>x u]\<^sub>i (read_trans t b w \<sigma>)"
  using assms
  apply(simp add: no_val_def p_vorder_def init_val_def mo_def value_def)
  done

lemma no_val_read_pres_n [simp] :
  assumes "wfs \<sigma>"
  and "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
  shows "[\<zero>\<^sub>x u]\<^sub>i (st_rd(Rd y t b \<sigma>))"
  apply simp 
  by (simp add: assms(1) assms(2) no_val_read_pres)

lemma no_val_write_pres [simp]:
  assumes "wfs \<sigma>"
  and "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
  and "v \<noteq> u"
and "w = getVWNC \<sigma> t y"
and "ts' = getTS \<sigma> w"
 shows "[\<zero>\<^sub>x u]\<^sub>i (write_trans t b w v \<sigma> ts')"
  using assms 
  apply(simp add: no_val_def p_vorder_def init_val_def mo_def value_def)
  apply(elim conjE exE, intro conjI)
   apply(rule_tac x = a in exI)
   apply(rule_tac x = ba in exI)
   apply(intro conjI)
  apply(case_tac "x = y")
      apply simp
     apply(unfold writes_on_def)

     apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
     apply blast
     apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
    apply (metis dual_order.strict_trans getVWNC_in_visible_writes getTS_w_greater_tst_w subsetD visible_writes_in_writes w_is)
     apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
  
   apply (metis getVWNC_var w_in_writes_on_var w_not_in_writes_on wfs_def)
  apply(intro allI impI)
     apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
  by (smt write_record.select_convs(1))  



lemma no_val_write_pres_n [simp]:
  assumes "wfs \<sigma>"
      and "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
      and "v \<noteq> u"
  shows "[\<zero>\<^sub>x u]\<^sub>i (Wr y v t b \<sigma>)"
  apply simp  
  by (simp add: assms(1) assms(2) assms(3))



lemma dvorder_intro:
  assumes "wfs \<sigma>"
and "[init x i] \<sigma>"
    and "[\<one>\<^sub>x u] \<sigma>"
    and "[en x u]\<^sub>t \<sigma>"
    and "[\<zero>\<^sub>x v]\<^sub>i \<sigma>"
and "[x =\<^sub>t u] \<sigma>"
and "w = getVWNC \<sigma> t x"
and "ts' = getTS \<sigma> w"
and "v \<noteq> u"
and "i \<noteq> u"
and "i \<noteq> v"
shows "[u \<hookrightarrow>\<^sub>x v] (write_trans t b w v \<sigma> ts')"
  using assms
    apply(subgoal_tac "var w = x")
   defer
   apply (simp add: getVWNC_var)
  apply(simp add: no_val_def init_val_def enc_t_def enc_def amo_def d_vorder_def p_vorder_def mo_def d_obs_t_def)
  apply(simp add: d_obs_def)
  apply(intro conjI allI impI)
    apply (metis w_in_writes_on_var)
  apply(elim conjE disjE)  
      apply simp
  apply(simp add: value_def)
    apply(simp add: value_def)
     apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
    apply(subgoal_tac "a = x")
     apply simp
  apply(case_tac "ba = getTS \<sigma> (getVWNC \<sigma> t x)") 
      apply simp
  apply simp  
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



lemma dvorder_intro_n [simp]:
  assumes "wfs \<sigma>"
and "[init x i] \<sigma>"
    and "[\<one>\<^sub>x u] \<sigma>"
    and "[en x u]\<^sub>t \<sigma>"
    and "[\<zero>\<^sub>x v]\<^sub>i \<sigma>"
and "[x =\<^sub>t u] \<sigma>"
and "v \<noteq> u"
and "i \<noteq> u"
and "i \<noteq> v"
shows "[u \<hookrightarrow>\<^sub>x v] (Wr x v t b \<sigma>)"
  apply simp  
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) dvorder_intro by auto

lemma pvorder_intro:
  assumes "wfs \<sigma>"
    and "[en x u]\<^sub>t \<sigma>"
and "w = getVW \<sigma> t x"
and "value \<sigma> w \<noteq> u"
shows "[u \<leadsto>\<^sub>x (value \<sigma> w)] (read_trans t b w \<sigma>)"
  using assms
  apply(simp add: enc_t_def enc_def p_vorder_def  mo_def)
  apply (subgoal_tac "var w = x")
  defer
  using getVW_var apply blast
  apply(elim exE conjE)
  apply (subgoal_tac "a = x")
  defer
  
  using w_in_writes_on_var apply blast
  apply simp
  apply(rule_tac x = x in exI)
  apply(rule_tac x = "ba" in exI)
  apply(intro conjI)
  
  apply blast
  apply(rule_tac x = "tst w" in exI)
  apply(simp add: value_def)
  apply(intro conjI)
  
  using getVW_in_writes_on w_is apply fastforce
  
  using w_is apply fastforce
  apply(simp add: getVW_def obsW_def visible_writes_def)
  by (smt assms(3) dual_order.antisym dual_order.trans getVW_in_vw mem_Collect_eq not_le_imp_less prod.collapse val_rd_def visible_writes_def writes_on_var)


lemma pvorder_intro_n [simp]:
  assumes "wfs \<sigma>"
    and "[en x u]\<^sub>t \<sigma>"
and "(val_rd(Rd x t b \<sigma>)) \<noteq> u"
shows "[u \<leadsto>\<^sub>x (val_rd(Rd x t b \<sigma>))](st_rd(Rd x t b \<sigma>))"
  using assms 
  apply simp 
  using pvorder_intro by blast


lemma no_val_contradiction:
  assumes "wfs \<sigma>"
and "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
and "w = getVWNC \<sigma> t x"
and "ts' = getTS \<sigma> w"
and "[\<zero>\<^sub>x u]\<^sub>i (write_trans t b w u \<sigma> ts')"
shows "False"
  using assms
  apply(simp add: no_val_def p_vorder_def init_val_def value_def mo_def)
  apply(elim conjE exE)
  apply(unfold writes_on_def)
 apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
  apply(subgoal_tac "var w = x", simp)
   apply(case_tac "ba = ts'")
    apply simp
   apply(case_tac "baa = ts'")
  apply simp
     apply (metis w_in_writes_on_var w_not_in_writes_on wfs_def)
    apply force
   apply(case_tac "baa = ts'")
  apply simp
    apply force
   apply simp
  apply(elim conjE)
   defer  
  apply (simp add: getVWNC_var)
proof -
fix a :: nat and aa :: nat and ba :: rat and baa :: rat
  assume a1: "ts' = getTS \<sigma> (getVWNC \<sigma> t x)"
  assume "w = getVWNC \<sigma> t x"
  assume a2: "\<forall>ba. (ba = getTS \<sigma> (getVWNC \<sigma> t x) \<longrightarrow> (\<forall>ba. val (if ba = getTS \<sigma> (getVWNC \<sigma> t x) then \<lparr>val = u, is_releasing = b\<rparr> else mods \<sigma> (x, ba)) = u \<longrightarrow> u = i \<longrightarrow> (x, ba) \<in> surrey_state.writes \<sigma> \<longrightarrow> \<not> getTS \<sigma> (getVWNC \<sigma> t x) < ba)) \<and> ((x, ba) \<in> surrey_state.writes \<sigma> \<longrightarrow> (\<forall>bb. val (if bb = getTS \<sigma> (getVWNC \<sigma> t x) then \<lparr>val = u, is_releasing = b\<rparr> else mods \<sigma> (x, bb)) = u \<longrightarrow> val (if ba = getTS \<sigma> (getVWNC \<sigma> t x) then \<lparr>val = u, is_releasing = b\<rparr> else mods \<sigma> (x, ba)) = i \<longrightarrow> (bb = getTS \<sigma> (getVWNC \<sigma> t x) \<longrightarrow> \<not> ba < getTS \<sigma> (getVWNC \<sigma> t x)) \<and> ((x, bb) \<in> surrey_state.writes \<sigma> \<longrightarrow> \<not> ba < bb)))"
  assume a3: "\<forall>b. (b = getTS \<sigma> (getVWNC \<sigma> t x) \<longrightarrow> baa < getTS \<sigma> (getVWNC \<sigma> t x)) \<and> ((x, b) \<in> surrey_state.writes \<sigma> \<longrightarrow> baa \<noteq> b \<longrightarrow> baa < b)"
  assume a4: "(aa, baa) \<in> surrey_state.writes \<sigma>"
  assume a5: "aa = x"
  assume a6: "val (mods \<sigma> (x, baa)) = i"
  assume a7: "baa \<noteq> getTS \<sigma> (getVWNC \<sigma> t x)"
  obtain bb :: bool where
    "(\<not> bb) = (\<forall>X2. X2 \<noteq> ts' \<or> val (if X2 = ts' then \<lparr>val = u, is_releasing = b\<rparr> else mods \<sigma> (x, X2)) \<noteq> u)"
    by moura
  then show ?thesis
using a7 a6 a5 a4 a3 a2 a1 by fastforce
qed

lemma no_val_contradiction_n [simp]:
  assumes "wfs \<sigma>"
and "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
and "[\<zero>\<^sub>x u]\<^sub>i (Wr x u t b \<sigma>)"
shows "False"
  using assms apply simp
  using no_val_contradiction2 by blast


lemma no_val_d_vorder_contradiction [simp]:
  assumes "wfs \<sigma>"
  and "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
  and "[u \<hookrightarrow>\<^sub>x  v] \<sigma>"
  and "u \<noteq> v"
  and "i\<noteq>u" 
  and " i\<noteq>v"
  shows "False"
  using assms
  apply(simp add: no_val_def d_vorder_def p_vorder_def init_val_def value_def)
  apply(elim conjE)  
  by metis

lemma no_val_d_vorder_contradiction_auto [simp]:
  assumes "wfs \<sigma>"
  and "[\<zero>\<^sub>x u]\<^sub>i \<sigma>"
  and "[u \<hookrightarrow>\<^sub>x  v] \<sigma>"
  and "u \<noteq> v"
  and "i\<noteq>u" 
  and " i\<noteq>v"
shows "[u \<hookrightarrow>\<^sub>x v] (Wr y z t b \<sigma>)"
  apply simp
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) no_val_d_vorder_contradiction by blast



lemma d_vorder_wr_diff_var_pres:
  assumes "wfs \<sigma>"
and "w = getVWNC \<sigma> t y"
and "ts' = getTS \<sigma> w"
and "[u \<hookrightarrow>\<^sub>x  v] \<sigma>"
and "x \<noteq> y"
shows "[u \<hookrightarrow>\<^sub>x  v] (write_trans t b w z \<sigma> ts')"
  using assms
  apply(simp add: d_vorder_def p_vorder_def value_def)
  apply(intro conjI allI impI, elim conjE)
   apply(unfold mo_def)
   apply(intro conjI)
    apply (metis writes_on_var)
   apply(subgoal_tac "a = x")
   apply(subgoal_tac "aa = x")
     apply(unfold writes_on_def)
  apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
  apply (simp add: getVWNC_var)
  using w_in_writes_on_var writes_on_def apply blast
  using w_in_writes_on_var writes_on_def apply blast
  apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)  
  by (simp add: getVWNC_var)

lemma d_vorder_wr_diff_var_pres_n [simp]:
  assumes "wfs \<sigma>"
and "w = getVWNC \<sigma> t y"
and "ts' = getTS \<sigma> w"
and "[u \<hookrightarrow>\<^sub>x  v] \<sigma>"
and "x \<noteq> y"
shows "[u \<hookrightarrow>\<^sub>x  v] (Wr y z t b \<sigma>)"
  by (simp add: assms(1) assms(4) assms(5) d_vorder_wr_diff_var_pres)

lemma enc_wr_prs:
  assumes "wfs \<sigma>"
    and "[en x u]\<^sub>t \<sigma>"
    and "w = getVWNC \<sigma> t' y"
    and "ts = getTS \<sigma> w"
  shows "[en x u]\<^sub>t (write_trans t' b w v \<sigma> ts)"
  using assms
  apply(simp add: enc_t_def enc_def value_def)
  apply(elim exE conjE)
   apply(rule_tac x = a in exI)
  apply(rule_tac x = ba in exI)
  apply(intro conjI)
    apply simp
  apply(case_tac "t \<noteq> t'")
   apply simp
   apply simp
  apply(simp add: getVWNC_def getTS_def vws_def vfs_def)
   apply(intro impI)
  apply (smt assms(3) assms(4) dual_order.trans getVWNC_in_visible_writes getVWNC_var getTS_w_greater_tst_w less_imp_le mem_Collect_eq visible_writes_def)
  apply(simp add: getVWNC_def getTS_def vws_def vfs_def)
  apply(case_tac "t \<noteq> t'")
   apply(case_tac "x = y")
    apply simp
  apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
    apply (metis assms(3) assms(4) w_in_writes_on_var w_not_in_writes_on)
  apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
   apply (metis assms(3) getVWNC_var w_in_writes_on_var)
  apply(simp add: write_trans_def rev_app_def update_mods_def update_wa_def update_modView_def update_thrView_def)
  by (metis assms(1) assms(3) assms(4) getVWNC_in_writes_on w_in_writes_on_var w_not_in_writes_on  writes_on_var)
  

lemma enc_wr_prs_n [simp]:
  assumes "wfs \<sigma>"
    and "[en x u]\<^sub>t \<sigma>"
  shows "[en x u]\<^sub>t (Wr y v t' b \<sigma>)"
  apply simp
  by (simp add: assms(1) assms(2) enc_wr_prs)

lemma enc_rd_prs:
  assumes "wfs \<sigma>"
    and "[en x u]\<^sub>t \<sigma>"
    and "getVW \<sigma> t' y = w"
  shows "[en x u]\<^sub>t (read_trans t' b w \<sigma>)"
  using assms
  apply(simp add: enc_t_def enc_def value_def)
  apply(elim exE conjE)
   apply(rule_tac x = a in exI)
  apply(rule_tac x = ba in exI)
  apply(intro conjI)
    apply simp
   defer
   apply simp
  apply(case_tac "t \<noteq> t'")
   apply simp
  apply simp
  apply (case_tac "\<not>syncing \<sigma> w b")
   apply simp
   apply(intro impI)
   apply(simp add: getVW_def obsW_def)
  apply (smt assms(3) dual_order.trans getVW_in_vw getVW_var mem_Collect_eq visible_writes_def)
  apply simp
  apply(simp add: getVW_def obsW_def ts_oride_def)
  
  by (smt assms(3) dual_order.trans getVW_in_vw getVW_var mem_Collect_eq visible_writes_def)


lemma enc_rd_prs_n [simp]:
  assumes "wfs \<sigma>"
    and "[en x u]\<^sub>t \<sigma>"
  shows "[en x u]\<^sub>t (st_rd(Rd y t' b \<sigma>))"
  apply simp
  by (simp add: assms(1) assms(2) enc_rd_prs)


lemma no_val_rd_contradiction [simp]: 
  "wfs \<sigma> \<Longrightarrow>  \<not>[\<zero>\<^sub>x  u]\<^sub>i \<sigma> \<Longrightarrow> [\<zero>\<^sub>x  u]\<^sub>i (st_rd(Rd y t b \<sigma>)) \<Longrightarrow> False"
  apply(simp add: no_val_def init_val_def p_vorder_def value_def)
  by blast

lemma p_vorder_wr_pres:
  assumes "wfs \<sigma>"
and "[u \<leadsto>\<^sub>x v] \<sigma>"
and "w = getVWNC \<sigma> t y"
and "ts' = getTS \<sigma> w"
shows "[u \<leadsto>\<^sub>x v] (write_trans t b w z \<sigma> ts')"
  using assms
  apply(simp add: p_vorder_def mo_def value_def)
  apply(elim exE conjE)
    apply(simp add: write_trans_def rev_app_def update_wa_def update_modView_def update_thrView_def update_mods_def)
   apply(rule_tac x = a in exI)
  apply(rule_tac x = ba in exI)
  apply (intro conjI)

  apply (metis getVWNC_var w_in_writes_on_var w_not_in_writes_on)
  apply(unfold writes_on_def)
  apply simp
  by (metis getVWNC_var w_in_writes_on_var w_not_in_writes_on wfs_def)


lemma p_vorder_wr_pres_n [simp]:
  assumes "wfs \<sigma>"
and "[u \<leadsto>\<^sub>x v] \<sigma>"
shows "[u \<leadsto>\<^sub>x v] (Wr y z t b \<sigma>)"
  apply simp 
  by (simp add: assms(1) assms(2) p_vorder_wr_pres)


lemma p_vorder_rd_pres [simp]:
  assumes "wfs \<sigma>"
and "[u \<leadsto>\<^sub>x v] \<sigma>"
shows "[u \<leadsto>\<^sub>x v] (st_rd(Rd y t b \<sigma>))"
  using assms
  by(simp add: p_vorder_def mo_def value_def)
  


lemma d_vorder_rd_prs [simp]:
  assumes "wfs \<sigma>"
and "[u \<hookrightarrow>\<^sub>x v] \<sigma>"
shows "[u \<hookrightarrow>\<^sub>x v]  (st_rd(Rd y t b \<sigma>))"
  using assms 
  apply(simp add: d_vorder_def p_vorder_def value_def)
  done

lemma dorder_porder_contradiction [simp]:
  assumes "wfs \<sigma>"
  and "u \<noteq> v"
  and " [u \<hookrightarrow>\<^sub>x v] \<sigma>"
  and " [v \<leadsto>\<^sub>x u] \<sigma> "
  shows "False"
  using assms
  apply (simp add: init_val_def amo_def p_vorder_def d_vorder_def)
  apply(unfold  mo_def)
  by (meson not_less_iff_gr_or_eq)



lemma p_obs_contradiction_auto [simp]:
  assumes "wfs \<sigma>"
and "\<not>[x \<approx>\<^sub>t u] \<sigma>"
and "w = getVW \<sigma> t' x"
and "[x \<approx>\<^sub>t u]  (st_rd(Rd x t' b \<sigma>))"
shows "False"
  using assms
  apply simp
  using OpSemExtProof.p_obs_contradiction by blast

lemma wr_enc_intro [simp]:
  assumes "wfs \<sigma>"
shows "[en x u]\<^sub>t (Wr x u t b \<sigma>)"
  using assms
  apply(simp add: enc_t_def enc_def)
    apply(simp add: write_trans_def rev_app_def update_wa_def update_modView_def update_thrView_def update_mods_def value_def)
  apply(intro conjI impI) 
   apply blast  
  by (metis  getVWNC_var)

lemma p_vorder_contradiction [simp]:
  assumes "wfs \<sigma>"
and "[\<one>\<^sub>x u] \<sigma>"
and "[\<one>\<^sub>x v] \<sigma>"
and "[u \<leadsto>\<^sub>x v] \<sigma>"
and "[v \<leadsto>\<^sub>x  u] \<sigma>"
shows " False"
  using assms
  apply(simp add: amo_def p_vorder_def value_def mo_def)
  by (metis dual_order.asym less_linear w_in_writes_on_var)


lemma not_pobs_contradiction [simp]:
  assumes "wfs \<sigma>"
and "\<not>[x \<approx>\<^sub>t u] \<sigma>"
and "val_rd (Rd x t b \<sigma>) = u"
shows "False"
  using assms
  by (simp add: not_p_obs_value)





end