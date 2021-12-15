theory OpSemExtProof
imports Main OpSem_New
begin

(***************Lemmas for WFS***********************)
lemma read_pres_wfs  :
  assumes "wfs \<sigma>"
  and "w = getVW \<sigma> t x"
  shows "wfs (read_trans t b w \<sigma>)"
  using assms
  apply (unfold wfs_def read_trans_def getVW_def obsW_def)
  apply(simp add: Let_def rev_app_def update_wa_def update_mods_def update_thrView_def update_modView_def syncing_def ts_oride_def)
  apply(unfold writes_on_def lastWr_def)
  apply clarsimp
  apply (intro conjI impI allI)
  apply (metis surj_pair)
  apply (metis (full_types) old.prod.exhaust)
  apply (meson assms(1) in_mono lastWr_visible tfl_some visible_writes_in_writes)
  apply (metis old.prod.exhaust)
  apply (metis surj_pair)
  by (meson assms(1) lastWr_visible subset_iff tfl_some visible_writes_in_writes)


lemma write_pres_wfs  :
  assumes "wfs \<sigma>"
      and "getVWNC \<sigma> t x = w"
      and "getTS \<sigma> w = ts'"
    shows "wfs (write_trans t b w v \<sigma> ts')"
  using assms
  apply(unfold wfs_def)
  apply(intro conjI)
  apply (simp add: write_trans_def)
      apply(simp add:  rev_app_def update_wa_def update_mods_def update_thrView_def update_modView_def)
      apply(intro allI conjI impI)
  apply(unfold writes_on_def, clarsimp)
       apply simp+
 apply (simp add: write_trans_def)
      apply(simp add:  rev_app_def update_wa_def update_mods_def update_thrView_def update_modView_def)
    defer
      apply(intro allI conjI impI)
   apply (simp add: write_trans_def)
     apply(simp add:  rev_app_def update_wa_def update_mods_def update_thrView_def update_modView_def)
  using assms(1) own_ModView apply blast

   
   
   apply(intro allI conjI impI)
   apply(case_tac " write_available \<sigma> wa")
   apply (simp add: write_trans_def)
    apply(simp add:  rev_app_def update_wa_def update_mods_def update_thrView_def update_modView_def)
   apply (case_tac "xa \<noteq> x")
    apply simp
      apply (metis assms(1) getVWNC_var wfs_def write_to_different_var)
   apply simp
   apply(case_tac "wa = (x, ts')")
  apply (simp add: write_trans_def)
    apply(simp add:  rev_app_def update_wa_def update_mods_def update_thrView_def update_modView_def)
    apply (metis assms(1) getVWNC_var)
  apply(subgoal_tac "wa = lastWr  \<sigma> x")
  using assms(1) wfs_def apply blast
   apply(simp add: lastWr_def)
  apply(case_tac "w = lastWr \<sigma> x")
    apply (simp add: assms(1))
  using assms(1) w_n_last_ts_less_tst_last [where x=x and \<sigma> = \<sigma> and t = t and w = w and ts'=ts']
   apply(simp add: lastWr_def)
   apply(subgoal_tac " tst ` writes_on (write_trans t b w v \<sigma> ts') x = tst ` writes_on \<sigma> x \<union> {ts'} ")
    apply auto[1]
  using writes_new_writes[where x=x and \<sigma> = \<sigma> and t = t and w = w and ts'=ts']
   apply(simp)
  apply(intro allI)
  using assms(1) writes_new_writes[where x=x and \<sigma> = \<sigma> and t = t and w = w and ts'=ts' and b=b and v=v]
  apply(unfold writes_on_def)
  apply (simp add: write_trans_def)
  apply(simp add:  rev_app_def update_wa_def update_mods_def update_thrView_def update_modView_def)
  apply(subgoal_tac "var w = x")
   apply simp
  apply(subgoal_tac "finite({w. var w = x \<and> w \<in> surrey_state.writes \<sigma>})")
  defer
      apply blast
  using getVWNC_var apply blast
  apply(subgoal_tac "finite( insert (x, ts') {w. var w = x \<and> w \<in> surrey_state.writes \<sigma>})")
  defer  
   apply blast
  apply(case_tac "xa = x")
   apply simp
  apply(case_tac "{w. var w = xa \<and> (w = (x, ts') \<or> w \<in> surrey_state.writes \<sigma>)} = {(x,ts')}")
   apply simp
  apply (case_tac "{w. var w = xa \<and> (w = (x, ts') \<or> w \<in> surrey_state.writes \<sigma>)} = {w. var w = xa \<and>  w \<in> surrey_state.writes \<sigma>}")
   apply simp
  by auto


lemma update_pres_wfs  :
  assumes "wfs \<sigma>"
      and "getVWNC \<sigma> t x = w"
      and "getTS \<sigma> w = ts'"
    shows "wfs (update_trans t w u \<sigma> ts')"
  using assms
  apply(unfold wfs_def)
  apply(intro conjI)
      defer
      apply(intro allI)
      apply(case_tac "var w \<noteq> var wa")
       apply simp
       apply(case_tac "var wa \<noteq> xa")
  apply (metis Un_empty_right Un_insert_right assms(1) insertCI wfs_def writes_new_update writes_new_update_diff_var)
  apply(subgoal_tac "writes_on (update_trans t w u \<sigma> ts') xa = writes_on \<sigma> xa")
        apply auto[1]
  using assms(1)  writes_new_update_diff_var
       apply simp
  apply simp
      apply(case_tac "ts' = tst wa")
       apply(case_tac "releasing \<sigma> w")
        apply simp
  apply(simp add: ts_oride_def)
  using assms(1) apply auto[1]
       apply simp
  apply simp
  apply (metis UnCI assms(1) wfs_def writes_new_update writes_new_update_diff_var)
     apply(intro allI)
  using assms(1) writes_new_update
  apply (metis finite.emptyI finite.insertI finite_UnI writes_new_update_diff_var)
    apply(intro allI impI)
      apply(case_tac "var w \<noteq> var wa")
        apply simp
     apply (elim disjE)
  apply clarsimp
   using assms(1) own_ModView apply blast
    apply simp
    apply (elim disjE)
       apply(subgoal_tac "ts' = tst wa")
    apply(case_tac "releasing \<sigma> w")
  apply simp
       apply (metis (mono_tags, lifting) assms(1) fun_upd_same getTS_valid getVWNC_in_vw leD own_ModView subset_Compl_singleton subset_trans ts_oride_def valid_fresh_ts_def visible_writes_in_writes)
      apply simp
  apply(simp add: sndI)
  using assms(1)
  apply simp
       apply(case_tac "ts' = tst wa")
     apply (metis getVWNC_var imageI ts_not_in_writes_on wfs_def)
    apply (simp add: own_ModView)
apply(intro allI impI)
   apply(case_tac "var w \<noteq> var wa")
  using assms(1)
  apply simp
  apply (simp add: lastWr_def)
  apply simp
  using assms(1)
  apply(case_tac "xa \<noteq> x")
  using getVWNC_var apply blast
   apply simp
  using assms(1)
  apply simp
   apply(subgoal_tac "tst w \<noteq> ts'")
    apply (case_tac "tst wa = ts'")
     apply simp
    apply(simp add: lastWr_def)
  apply(case_tac "w = lastWr \<sigma> x")
  apply (metis getts_greater_than lastWr_def last_write_max2 last_write_write_on max.strict_coboundedI1 max_def_raw)
    apply(subgoal_tac "tst wa \<noteq> tst w")
  apply simp
     apply (metis max_def_raw)
  apply (metis getVWNC_in_writes_on lastWr_def last_write_write_on max_def_raw same_ws)
   apply (metis assms(1) assms(2) assms(3) dual_order.irrefl getTS_valid valid_fresh_ts_def)
  apply(intro allI)
  apply(case_tac "releasing \<sigma> w")
   apply simp
   apply(case_tac "t = ta")
  apply simp
  apply (simp add: getVWNC_var ts_oride_def  writes_new_update writes_new_update_diff_var)
    apply (simp add: assms(1))
   apply simp
  apply (metis Un_iff assms(1) writes_new_update writes_new_update_diff_var)
  apply simp
   apply(case_tac "t = ta")
  apply simp+
  by (metis Un_iff assms(1) writes_new_update writes_new_update_diff_var)
 


(*********** Lemmas for d_obs *************)

lemma d_obs_getVW: " wfs \<sigma> \<Longrightarrow> [x =\<^sub>t u] \<sigma> \<Longrightarrow>
   w =  getVW \<sigma> t x \<Longrightarrow>
  getVW (read_trans t False w \<sigma>) t x =  getVW \<sigma> t x"
  apply (simp add: getVW_def obsW_def visible_writes_def d_obs_t_def  d_obs_def)
  apply(intro impI)
  by (metis (full_types, lifting) dual_order.antisym last_write_max last_write_write_on tfl_some)

 
lemma read_pres_d_obs  :
  assumes "wfs \<sigma>"
    and "[x =\<^sub>t u] \<sigma>"
    and "w = getVW \<sigma> t y"
  shows "[x =\<^sub>t u] (read_trans t b w \<sigma>)"
  using assms 
  apply (simp add:  d_obs_t_def  d_obs_def)
  apply (intro conjI)
   apply(simp add: lastWr_def)
   apply (elim conjE)
   apply(simp add: read_trans_def rev_app_def Let_def update_thrView_def value_def) 
   apply(case_tac "syncing \<sigma> (getVW \<sigma> t y) b")
    apply simp
  using getVW_in_vw [where \<sigma> = \<sigma> and t=t and w =w and x = y]
    getVW_var [where \<sigma> = \<sigma> and t=t and w =w and x = y]
    apply(unfold wfs_def)
    apply clarsimp
  apply(intro conjI impI)
  apply (metis \<open>\<lbrakk>wfs \<sigma>; w = getVW \<sigma> t y\<rbrakk> \<Longrightarrow> var w = y\<close> assms(1) assms(2) d_obs_lastWr_visible lastWr_def ts_oride_same_var)
  using assms(1,2)
  apply(simp add: d_obs_def d_obs_t_def lastWr_def)
    apply (unfold  antisym fun_upd_other lastWr_def modView_lte_last same_ws ts_oride_def wfs_def)
    apply (metis antisym assms(1) lastWr_def modView_lte_last same_ws)
  using assms(1) assms(2)
  apply(simp add: d_obs_t_def d_obs_def lastWr_def)
  apply (metis assms(2) d_obs_lastWr_visible lastWr_def)
   apply(simp add: read_trans_def rev_app_def Let_def update_thrView_def value_def) 
  apply(intro conjI impI)
   apply(unfold writes_on_def)
  apply clarsimp+  
    done


lemma read_pres_d_obs_other_var  :
  assumes "wfs \<sigma>"
    and "[x =\<^sub>t u] \<sigma>"
    and "w = getVW \<sigma> t' y"
    and "t \<noteq> t'"
  shows "[x =\<^sub>t u] (read_trans t' b w \<sigma>)"
  using assms
   apply(simp add:  getVW_def obsW_def)
  apply(subgoal_tac "var w = y")
  defer
   apply (metis (mono_tags) Nitpick.Eps_psimp assms(1) lastWr_visible visible_var)
  apply(simp add: d_obs_t_def d_obs_def)
  apply(intro conjI)
    apply (simp add: lastWr_read_pres)
  apply(elim conjE)
  apply(simp add: value_def)
      by (simp add: lastWr_read_pres)


lemma ext_d_obs_d_obs  :
  assumes "wfs \<sigma>"
      and "[x =\<^sub>t v] \<sigma>"
      and "getVWNC \<sigma> t x = w"
      and " ts' = getTS \<sigma> w"
    shows"[x =\<^sub>t u] (write_trans t b w u \<sigma> ts')"
  using assms
  apply(simp add: d_obs_t_def d_obs_def)
  apply (intro conjI)
   apply (intro impI conjI, elim conjE)   
  apply clarsimp
  apply(simp add: getVWNC_def vws_def)
    defer
    defer
  apply(simp add: getVWNC_def vws_def)
  apply (metis (mono_tags) assms(1)  mem_Collect_eq some_in_eq tfl_some visible_var  vws_def vws_not_empty)
   apply(subgoal_tac "w = lastWr \<sigma> x")
    defer
  using assms(3) getVWNC_lastWr apply fastforce
   apply(elim conjE)
   defer
  apply (metis (no_types, lifting) assms(3) getTS_valid getVWNC_in_visible_writes lastWr_def lastWr_w)
  by (simp add: getVWNC_lastWr value_last)





lemma ext_upd_d_obs_d_obs  :
  assumes "wfs \<sigma>"
      and "[x =\<^sub>t v] \<sigma>"
      and "getVWNC \<sigma> t x = w"
      and "getTS \<sigma> w = ts'"
    shows"[x =\<^sub>t u] (update_trans t w u \<sigma> ts')"
  using assms
  apply(simp add: d_obs_t_def d_obs_def)
  apply(elim conjE, intro conjI)
   apply(case_tac "releasing \<sigma> w")
    apply simp
  apply (smt dual_order.strict_trans2 fun_upd_same getTS_valid getVWNC_in_visible_writes getVWNC_lastWr getVWNC_var getts_greater_than in_mono lastWr_def lastWr_upd last_write_max2 last_write_write_on own_ModView ts_oride_def update_pres_wfs visible_writes_in_writes)
    apply simp
   apply (metis getTS_valid getVWNC_in_vw getVWNC_lastWr getVWNC_var lastWr_def lastWr_upd)
  apply(simp add: value_def)
  apply(subgoal_tac "var (lastWr (update_trans t w u \<sigma> ts') x) = x")
  apply(case_tac "tst (lastWr (update_trans t w u \<sigma> ts') x) \<noteq> ts'")
  using assms (1,2)
    apply(simp add: lastWr_def)  
  apply (metis getTS_valid getVWNC_in_vw getVWNC_lastWr lastWr_def lastWr_upd prod.inject)
   apply simp
   apply(simp add: lastWr_def)  
   apply(subgoal_tac "var w = x")
  apply simp
  using getVWNC_var apply blast
  by simp
  


lemma d_obs_read_value:
  assumes "wfs \<sigma>"
    and "[x =\<^sub>t u] \<sigma>"
  shows "value \<sigma> ((getVW (read_trans t False (getVW \<sigma> t x) \<sigma>) t x)) = u"
  by (metis Collect_mem_eq assms(1) assms(2) d_obs_getVW d_obs_implies_p_obs d_obs_lastWr_visible getVW_def obsW_def p_obs_def tfl_some)
  
lemma d_obs_diff_false  :
  assumes  "wfs \<sigma>"
and " [x =\<^sub>t u] \<sigma>"
and "[x =\<^sub>t' v] \<sigma>"
and "u \<noteq> v"
shows "False"
  using assms
  by (simp add: d_obs_def d_obs_t_def)  


lemma ext_write_other_pres_d_obs  :
  assumes "wfs \<sigma>"
      and "[x =\<^sub>t u] \<sigma>"
      and "getVWNC \<sigma> t' y = w"
      and " getTS \<sigma> w = ts'"
      and "y \<noteq> x"
    shows"[x =\<^sub>t u] (write_trans t' b w v \<sigma> ts')"
  using assms
  apply(simp add: d_obs_t_def d_obs_def)
  apply(intro conjI)
   apply(subgoal_tac "var w = y")
    apply simp
  using assms(1,2)
    apply(case_tac "t = t'")
     apply simp
  apply simp
    using getVWNC_var apply blast
    apply (simp add: value_def)
      apply(subgoal_tac "var w = y")
     apply simp
    using getVWNC_var by blast
  


lemma d_obs_value:
  assumes "wfs \<sigma>"
and  "[x =\<^sub>t u] \<sigma>"
  and "w = getVW \<sigma> t x"
  shows "value \<sigma> w = u"
  using assms
  using d_obs_getVW d_obs_read_value by auto 


lemma update_diff_var_pres_dobs_ext  :
  assumes  "wfs \<sigma>"
  and "[x =\<^sub>t u] \<sigma>"
  and "getVWNC \<sigma> t' y = w"
  and " getTS \<sigma> w = ts'"
  and "y \<noteq> x"
shows "[x =\<^sub>t u] (update_trans t' w v \<sigma> ts')"
  using assms
  apply(simp add: d_obs_t_def)
  apply(simp add: d_obs_def)
  apply(elim conjE, intro conjI)
   apply(subgoal_tac "var w = y")
    apply(case_tac "t = t'")
      apply(case_tac "releasing \<sigma> w")
      apply simp
  apply(simp add: ts_oride_def)
      apply (metis dual_order.antisym lastWr_def modView_lte_last same_ws wfs_def writes_new_update_diff_var)
     apply simp
     apply (simp add: lastWr_def)
    apply simp
    apply (simp add: lastWr_def) 
  using getVWNC_var apply blast
  apply (simp add: value_def)
   apply(subgoal_tac "var w = y")
   apply simp
   apply (simp add: lastWr_def)
  using getVWNC_var by blast

lemma ext_cvd_update_d_obs  :
  assumes "wfs \<sigma>"
      and "[x = u]\<lparr>y =\<^sub>t v\<rparr> \<sigma>"
      and "getVWNC \<sigma> t x = w"
      and "getTS \<sigma> w = ts'"
      and "cvd[x, u] \<sigma>"
      and "x \<noteq> y"
    shows "[y =\<^sub>t v] (update_trans t w m \<sigma> ts')"
  using assms(2)
  apply(simp add: c_obs_def d_obs_t_def d_obs_def)
  apply(subgoal_tac "var w = x") defer 
  using assms(1) assms(3) getVWNC_var apply blast
  apply(subgoal_tac "value \<sigma> w = u") defer 
  apply (metis assms(1) assms(3) assms(5) covered_v_def getVWNC_in_writes_on getVWNC_wa)
  apply(intro conjI)
   apply(case_tac "releasing \<sigma> w")
    apply simp  
    apply(simp add: ts_oride_def)
  apply(intro conjI)  
  using assms(6) apply blast
    apply(intro impI conjI)
  apply(simp add: lastWr_def)    
     apply (metis assms(1) assms(3) getVWNC_in_visible_writes)
  apply(simp add: lastWr_def)  
    apply (metis assms(1) assms(3) getVWNC_in_visible_writes lastWr_def last_write_max wfs_def)
   apply simp
  apply(intro conjI impI)  
  using assms(6) apply blast  
   apply (metis assms(1) assms(3) getVWNC_in_visible_writes)
  apply(simp add: value_def)
  using assms(6)
  apply(case_tac "releasing \<sigma> w")
  apply simp  
   apply (metis assms(1) assms(3) assms(4) getVWNC_in_visible_writes lastWr_def writes_new_update_diff_var)
  apply simp  
  by (metis assms(1) assms(3) getVWNC_in_visible_writes)

lemma ext_cvd_up_dobs  : 
  assumes  "cvd[x, u] \<sigma>"
    and "wfs \<sigma>"
      and " getVWNC \<sigma> t x = w"
      and "getTS \<sigma> w = ts'"
    shows "[x =\<^sub>t v] (update_trans t w v \<sigma> ts')"
  using assms
  apply(simp add: covered_v_def d_obs_t_def)
  apply(simp add:  d_obs_def)
  apply(subgoal_tac "var w = x")
  apply(intro conjI)
    apply(case_tac "releasing \<sigma> w")
     apply simp
     apply(simp add: ts_oride_def)
  apply(intro conjI)
      apply (metis assms(1) covered_v_def getVWNC_in_writes_on getVWNC_wa getts_greater_than leD less_le_trans modView_lte_last) 
  apply (metis (no_types, lifting) assms(1) covered_v_def getTS_valid getVWNC_in_visible_writes getVWNC_in_writes_on getVWNC_wa lastWr_def lastWr_upd)
    apply simp  
    apply (metis (no_types, lifting) assms(1) covered_v_def getTS_valid getVWNC_in_visible_writes getVWNC_in_writes_on getVWNC_wa lastWr_def lastWr_upd)
  apply(simp add: value_def)
  apply(case_tac "tst (lastWr (update_trans t w v \<sigma> ts') x) = ts'")
    apply simp
   apply simp
  apply(simp add: lastWr_def)  
   apply (metis assms(1) covered_v_def getTS_valid getVWNC_in_writes_on getVWNC_wa lastWr_def last_write_max2 less_max_iff_disj max_def valid_fresh_ts_def)
   using getVWNC_var by blast
  


lemma ext_d_obs_rd_pres2  :
  assumes "wfs \<sigma>"
      and "[x =\<^sub>t u] \<sigma>"
      and " getVW \<sigma> t' y = w"
      and "t \<noteq> t'"
      and "\<sigma>' = (read_trans t' b w \<sigma>)"
    shows "[x =\<^sub>t u] \<sigma>'"
  using assms
  apply(simp add: getVW_def obsW_def)
  apply (unfold d_obs_t_def d_obs_def visible_writes_def writes_on_def lastWr_def)
  apply(simp add: read_trans_def Let_def rev_app_def update_thrView_def)
  apply (case_tac "syncing \<sigma> w b")
  apply simp_all
   apply (simp add: value_def)
  apply (simp add: value_def)
done


lemma ext_d_obs_rd_pres  :
  assumes "wfs \<sigma>"
and "[x =\<^sub>t u] \<sigma>"
and " getVW \<sigma> t' y = w"
      and "\<sigma>' = (read_trans t' b w \<sigma>)"
shows "[x =\<^sub>t u] \<sigma>'"
  using assms
  apply (unfold wfs_def d_obs_t_def d_obs_def visible_writes_def writes_on_def lastWr_def)
  apply(simp add: read_trans_def Let_def rev_app_def update_thrView_def)
  apply (case_tac "syncing \<sigma> w b", simp_all)
  apply(elim conjE)
   apply(intro conjI impI)
  apply(simp add: ts_oride_def)
        apply(intro conjI impI)
         apply (metis (no_types, lifting) assms(1) assms(2) d_obs_def d_obs_lastWr_visible d_obs_t_def getVW_in_vw getVW_var)
        apply (metis assms(1) assms(2) d_obs_def d_obs_lastWr_visible d_obs_t_def getVW_in_vw getVW_var)
        apply (metis (no_types, lifting) Collect_cong surrey_state.select_convs(4) surrey_state.surjective surrey_state.update_convs(2) value_def)
      apply (metis (no_types, lifting) Collect_cong surrey_state.select_convs(4) surrey_state.surjective surrey_state.update_convs(2) value_def)
  using  assms(1) assms(2) 
     apply(unfold d_obs_def d_obs_t_def lastWr_def ts_oride_def)
     apply clarsimp
     apply (metis (no_types, lifting) dual_order.antisym lastWr_def modView_lte_last same_ws wfs_def)
  apply(simp_all add: value_def)
  by (metis  assms(2) d_obs_lastWr_visible getVW_in_vw getVW_var lastWr_def)
  


lemma ext_d_obs_rd_pres3  :
  assumes "wfs \<sigma>"
and "[x =\<^sub>t u] \<sigma>"
and " getVW \<sigma> t' y = w"
      and "\<sigma>' = (read_trans t' b w \<sigma>)"
shows "[x =\<^sub>t u] \<sigma>'"
  using assms
  using getVW_var [where \<sigma> = \<sigma> and t = t' and w = w and x = y]
  using getVW_in_vw [where \<sigma> = \<sigma> and t = t' and w = w and x = y]
    apply (unfold wfs_def d_obs_t_def d_obs_def visible_writes_def writes_on_def lastWr_def)
  apply(simp add: read_trans_def Let_def rev_app_def update_thrView_def)
  apply (case_tac "syncing \<sigma> w b", simp_all)
  apply(elim conjE)
   apply(intro conjI impI)
  apply(simp add: ts_oride_def)
        apply(intro conjI impI)
  apply (metis (no_types, lifting) \<open>\<lbrakk>wfs \<sigma>; w = getVW \<sigma> t' y\<rbrakk> \<Longrightarrow> w \<in> visible_writes \<sigma> t' y\<close> assms(1) assms(2) d_obs_def d_obs_lastWr_visible d_obs_t_def)
        apply (metis assms(1) order_refl own_ModView)
  apply(simp_all add: value_def)
     apply(simp add: ts_oride_def)
     apply(intro impI)
  using assms(1,2)
  apply(unfold d_obs_def d_obs_t_def lastWr_def wfs_def)
  apply (metis (mono_tags, lifting) Max_ge Pair_inject antisym assms(1) finite_imageI image_eqI lastWr_def modView_lte_last same_ws)
      apply(simp add: value_def)
        apply(intro conjI impI)
  apply (metis  \<open>\<lbrakk>wfs \<sigma>; w = getVW \<sigma> t' y\<rbrakk> \<Longrightarrow> w \<in> visible_writes \<sigma> t' y\<close> assms(1) assms(2) d_obs_lastWr_visible lastWr_def)
  by(simp_all add: value_def)




(****************Lemmas for p_obs ******************)
lemma not_p_obs_other_pres_not_p_obs  :
  assumes "wfs \<sigma>"
      and "\<not>[x \<approx>\<^sub>t u] \<sigma>"
      and "w = getVWNC \<sigma> t' y"
      and "ts' = getTS \<sigma> w"
      and "y \<noteq> x"
    shows "\<not>[x \<approx>\<^sub>t u] (write_trans t' b w v \<sigma> ts')"
  using assms
  apply simp
  apply(unfold  write_trans_def rev_app_def update_wa_def update_thrView_def update_modView_def update_mods_def)
  apply simp
  apply (unfold p_obs_def)
  apply safe
  apply(simp add: value_def)
  apply(subgoal_tac "var (getVWNC \<sigma> t' y) = y")
   defer
  using getVWNC_var apply blast
  apply clarsimp
  apply(subgoal_tac "a = x")
  defer
   apply(simp add: visible_writes_def)
   apply(unfold writes_on_def)
   apply clarsimp
  apply clarsimp
   apply(simp add: visible_writes_def)
   apply(unfold writes_on_def)
   apply clarsimp
  by (metis (full_types) fun_upd_apply)

lemma w_in_writes_on_var: "(a,b) \<in> writes_on \<sigma> x \<Longrightarrow> a = x"
  apply(unfold writes_on_def)
  by simp

lemma not_p_obs_read  :
  assumes "wfs \<sigma>"
    and "\<not>[x \<approx>\<^sub>t u] \<sigma>"
    and "getVW \<sigma> t y = w"
  shows "\<not>[x \<approx>\<^sub>t u] (read_trans t b w \<sigma>)"
  using assms
  apply(unfold p_obs_def)
  apply(simp add: value_def)
  apply(subgoal_tac "var w = y")
   defer
  using getVW_var apply blast
  apply(intro allI impI)
  apply(subgoal_tac "a = x")
   defer
  apply (metis order.not_eq_order_implies_strict psubsetD read_pres_wfs visible_var visible_writes_in_writes w_in_writes_on_var wfs_def)
  apply simp
  apply(subgoal_tac "(x, ba) \<in> writes_on \<sigma> x")
   defer
  apply(simp add: visible_writes_def)
  apply(simp add: visible_writes_def)
  apply(case_tac "\<not>syncing \<sigma> w b")
   apply simp
   apply(case_tac "x = y", simp)
    defer 
    apply simp
   apply simp
   apply(case_tac "x = y", simp)
    apply(simp add:ts_oride_def)
    apply(case_tac "tst w \<le> tst (modView \<sigma> w y)", simp)
     defer
     apply (metis eq_iff getVW_in_vw own_ModView subsetD visible_writes_in_writes)
    apply (smt dual_order.trans fun_upd_other ts_oride_def)
  apply(simp add: getVW_def obsW_def)
  apply (smt assms(3) dual_order.trans getVW_in_vw mem_Collect_eq visible_writes_def)
  apply(simp add: getVW_def obsW_def) 
proof -
fix a :: nat and ba :: rat
  assume a1: "tst (modView \<sigma> w y) \<le> ba"
  assume a2: "tst w \<le> tst (modView \<sigma> w y)"
  assume a3: "\<forall>a b. (a, b) \<in> writes_on \<sigma> y \<and> tst (thrView \<sigma> t y) \<le> b \<longrightarrow> u \<noteq> val (mods \<sigma> (a, b))"
  assume a4: "(y, ba) \<in> writes_on \<sigma> y"
  assume a5: "(SOME e. e \<in> visible_writes \<sigma> t y) = w"
  assume a6: "wfs \<sigma>"
  have f7: "\<forall>r. r \<le> ba \<or> \<not> r \<le> tst w"
using a2 a1 by (metis dual_order.trans)
have "w \<in> visible_writes \<sigma> t y"
  using a6 a5 by (meson lastWr_visible tfl_some)
  then have "tst (thrView \<sigma> t y) \<le> ba"
using f7 visible_writes_def by fastforce
  then show "u \<noteq> val (mods \<sigma> (y, ba))"
    using a4 a3 by metis
qed


lemma d_obs_not_p_obs:
  assumes "wfs \<sigma>"
and "[x =\<^sub>t z] \<sigma>"
  and "z \<noteq> u"
shows "\<not>[x \<approx>\<^sub>t u] \<sigma>"
  using assms
  using d_obs_p_obs_agree by blast
  

lemma cvd_p_obs: "wfs \<sigma> \<Longrightarrow> cvd[x,u] \<sigma> \<Longrightarrow> [x \<approx>\<^sub>t u] \<sigma>"
  by (metis covered_v_def lastWr_visible last_write_write_on p_obs_def wfs_def)

lemma not_p_obs_value  :
  assumes "wfs \<sigma>"
and "\<not>[x \<approx>\<^sub>t u] \<sigma>"
and "w = getVW \<sigma> t x"
shows "value \<sigma> w \<noteq> u"
  using assms
  using getVW_in_vw p_obs_def by blast

lemma ext_p_obs_contradiction  :
  assumes "wfs \<sigma>"
and "\<not>[x \<approx>\<^sub>t u] \<sigma>"
  and " getVW \<sigma> t' y = w"
and "x \<noteq> y"
and "[x \<approx>\<^sub>t u] (read_trans t' b w \<sigma>)"
shows "False"
  using assms
  apply(unfold read_trans_def)
  apply(unfold rev_app_def Let_def update_thrView_def)
  apply(unfold  p_obs_def)
  apply(case_tac "syncing \<sigma> w b")
   apply(simp add: value_def visible_writes_def)
   apply(unfold writes_on_def)
  apply clarsimp
   apply (smt assms(2) assms(5) not_p_obs_read)
   apply(simp add: value_def visible_writes_def)
  by (smt assms(2) assms(5) mem_Collect_eq not_p_obs_read surrey_state.select_convs(1) surrey_state.surjective surrey_state.update_convs(2) writes_on_def)
  

lemma ext_p_obs_rd_pres  :
  assumes "wfs \<sigma>"
and "[x \<approx>\<^sub>t u] \<sigma>"
and " getVW \<sigma> t' y = w"
and "t \<noteq> t'"
shows "[x \<approx>\<^sub>t u] (read_trans t' b w \<sigma>)"
  using assms
  apply(unfold p_obs_def read_trans_def)
  apply(unfold rev_app_def Let_def update_thrView_def)
  apply(simp add: value_def)
  apply(case_tac "syncing \<sigma> w b")
   apply simp
   apply(unfold visible_writes_def writes_on_def, simp)
  by simp


lemma p_obs_contradiction  :
  assumes "wfs \<sigma>"
  and "\<not> [x \<approx>\<^sub>t v] \<sigma>"
  and " getVW \<sigma> t' y = w"
  and  "[x \<approx>\<^sub>t v] (read_trans t' b w \<sigma>)"
shows "False"
  using assms
  apply(unfold p_obs_def read_trans_def)
  apply(unfold rev_app_def Let_def update_thrView_def)
  apply(simp add: value_def)
  apply(case_tac "syncing \<sigma> w b", clarsimp)
    apply(unfold visible_writes_def writes_on_def, simp)
    apply (smt assms(2) assms(4) not_p_obs_read)
  apply clarsimp
  by (smt assms(2) assms(4) not_p_obs_read)



lemma p_obs_write [simp]:
  assumes "wfs \<sigma>"
      and "w = getVWNC \<sigma> t x"
      and "ts' = getTS \<sigma> w"
    shows "[x \<approx>\<^sub>t u] (write_trans t b w u \<sigma> ts')"
  using assms
  apply simp
  apply(unfold  write_trans_def rev_app_def update_wa_def update_thrView_def update_modView_def update_mods_def)
  apply simp
  apply (unfold p_obs_def visible_writes_def writes_on_def)
  apply clarsimp
  apply safe
  apply (metis (no_types, lifting) fun_upd_same less_eq_rat_def surrey_state.select_convs(4) surrey_state.surjective surrey_state.update_convs(1) surrey_state.update_convs(2) surrey_state.update_convs(3) surrey_state.update_convs(4) surrey_state.update_convs(5) value_def write_record.select_convs(1))
  by (simp add: getVWNC_var)



(****************Lemmas for c_obs ******************)

lemma not_p_obs_write_pres_c_obs_diff_var  :
  assumes "wfs \<sigma>"
  and "\<not>[x \<approx>\<^sub>t u] \<sigma>"
  and "getVWNC \<sigma> t' y = w"
  and "getTS \<sigma> w = ts'"
  and "t \<noteq> t'"
  and "x \<noteq> y"
  shows "[x = u]\<lparr>y =\<^sub>t v\<rparr> (write_trans t' b  w z \<sigma> ts')"
  using assms(2)
 by (metis assms(1) assms(3) assms(4) assms(6) not_p_obs_implies_c_obs not_p_obs_other_pres_not_p_obs)

  

lemma ext_c_obs_intro  :
  assumes "wfs \<sigma>"
  and "[y =\<^sub>t v] \<sigma>"
  and "\<not>[x \<approx>\<^sub>t' u] \<sigma>"
  and "getVWNC \<sigma> t x = w"
  and "getTS \<sigma> w = ts'"
  and "x \<noteq> y"
  and "t \<noteq> t'"
shows "[x = u]\<lparr>y =\<^sub>t' v\<rparr> (write_trans t True w u \<sigma> ts')"
  using assms (2,3)
  apply (simp add: d_obs_t_def p_obs_def d_obs_def c_obs_def)
  apply(simp add: visible_writes_def)
  apply(intro allI impI conjI)
  using assms (4,5,6,7)
    apply simp
    apply(subgoal_tac "var w = x")
     apply simp
     apply(elim conjE)
     apply(subgoal_tac "a = x")
      apply simp
      apply(elim disjE)
  apply simp 
       apply (simp add: assms(1))
      apply(case_tac "b = ts'")
       apply simp
  using assms(1) w_not_in_writes_on apply blast
      apply simp
  apply(simp add: lastWr_def value_def)
      apply blast
  using w_in_writes_on_var apply blast
  using assms(1) getVWNC_in_writes_on writes_on_var apply blast 
   apply (metis assms(1) assms(4) assms(5) assms(6) d_obs_def d_obs_t_def ext_write_other_pres_d_obs w_in_writes_on_var)
  apply(simp add: value_def)
  apply(elim conjE)
     apply(subgoal_tac "a = x")
  apply simp
  apply(subgoal_tac "var w = x")
  apply simp
    apply(elim disjE)
  apply (simp add: releasing_def)
    apply(simp add: write_trans_def update_wa_def update_mods_def update_modView_def update_thrView_def rev_app_def releasing_def)
  using assms(7) apply fastforce  
  using assms(1) assms(4) getVWNC_var apply blast
  using w_in_writes_on_var by blast
  



lemma c_obs_read_pres  :
  assumes "wfs \<sigma>"
  and "[x = u]\<lparr>y =\<^sub>t v\<rparr> \<sigma>"
  and "getVW \<sigma> t x = w"
shows "[x = u]\<lparr>y =\<^sub>t v\<rparr> (read_trans t b w \<sigma>)"
  using assms
  apply(unfold c_obs_def d_obs_def visible_writes_def read_trans_def)
    apply(unfold rev_app_def Let_def update_thrView_def)
  apply (simp add: value_def lastWr_def)
  apply(intro conjI impI allI)
             apply(unfold writes_on_def)
  apply clarsimp
             apply (smt dual_order.trans getVW_in_vw mem_Collect_eq ts_oride_same_var visible_writes_def)
            apply(simp add: visible_writes_def)
  apply (smt Collect_cong dual_order.trans getVW_in_vw mem_Collect_eq surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(2) ts_oride_same_var visible_writes_def)
           apply(simp add: ts_oride_def)
  apply(elim conjE)

  apply (smt dual_order.trans fun_upd_same getVW_in_vw mem_Collect_eq releasing_def surrey_state.select_convs(4) surrey_state.surjective surrey_state.update_convs(2) visible_writes_def)
  apply clarsimp
    apply (smt dual_order.trans getVW_in_vw mem_Collect_eq visible_writes_def)
         apply clarsimp
         apply (smt dual_order.trans getVW_in_vw mem_Collect_eq visible_writes_def)
        apply clarsimp
  defer
        apply (metis getVW_var)
       apply (metis getVW_var)
      apply (metis getVW_var)
     apply auto[2]
   apply (metis assms(1) assms(3) getVW_in_vw visible_var)
  using assms(1) assms(2)
  apply(unfold wfs_def)
  by (smt assms(1) dual_order.trans getVW_in_vw mem_Collect_eq releasing_def surrey_state.select_convs(4) surrey_state.surjective surrey_state.update_convs(2) visible_writes_def)
  


lemma c_obs_read_d_obs  :
  assumes "wfs \<sigma>"
  and "[x = u]\<lparr>y =\<^sub>t v\<rparr> \<sigma>"
  and "getVW \<sigma> t x = w"
  and "value \<sigma> w = u"
shows "[y =\<^sub>t v] (read_trans t True w \<sigma>)"
  using assms
  apply(unfold c_obs_def d_obs_def d_obs_t_def)
  apply(intro conjI)
   apply(unfold  value_def)
   apply clarsimp
   apply (simp add: getVW_in_vw lastWr_read_pres last_write_max  ts_oride_def)
  apply (metis getVW_in_vw own_ModView subsetD visible_writes_in_writes)
  apply(simp add: read_trans_def Let_def rev_app_def update_thrView_def)
   apply(intro conjI impI)
   apply(simp add: lastWr_def)
  apply(unfold writes_on_def, clarsimp)
  using getVW_in_vw apply blast
   apply(simp add: lastWr_def)
  apply(unfold writes_on_def, clarsimp)
  using getVW_in_vw apply blast
  done

lemma d_obs_diff_c_obs  :
  assumes "wfs \<sigma>"
and "[x =\<^sub>t z] \<sigma>"
  and "z \<noteq> u"
shows "[x = u]\<lparr>y =\<^sub>t v\<rparr> \<sigma>"
  using assms
  using d_obs_not_p_obs not_p_obs_implies_c_obs by blast


lemma not_d_obs_c_obs_ext  :
  assumes "wfs \<sigma>"
      and "\<not>[x \<approx>\<^sub>t' u] \<sigma>"
      and "[y =\<^sub>t v] \<sigma>"
      and "getVWNC \<sigma> t' x = w"
      and " ts' = getTS \<sigma> w"
      and "value \<sigma> w = u"
      and "y \<noteq> x"
      and "t \<noteq> t'"
    shows"[x = u]\<lparr> y =\<^sub>t' v\<rparr> (write_trans t' True w v \<sigma> ts')"
  using assms
  apply(unfold p_obs_def d_obs_def d_obs_t_def c_obs_def visible_writes_def)
  apply(unfold visible_writes_def value_def lastWr_def writes_on_def)
  apply(unfold write_trans_def rev_app_def update_wa_def update_mods_def update_thrView_def update_modView_def)
  by (metis assms(1) assms(2) assms(4) assms(6) getVWNC_in_vw p_obs_def value_def)


lemma c_obs_pres_write_diff_var_ext  :
  assumes "wfs \<sigma>"
      and "[x = u]\<lparr>y =\<^sub>t v\<rparr> \<sigma>"
      and "getVWNC \<sigma> t z = w"
      and "x \<noteq> z"
      and "y \<noteq> z"
      and " getTS \<sigma> w = ts'"
    shows "[x = u]\<lparr>y =\<^sub>t v\<rparr> (write_trans t b w v \<sigma> ts')"
  using assms(2)
  apply(simp add: p_obs_def d_obs_def d_obs_t_def c_obs_def visible_writes_def value_def)
  apply(intro conjI impI allI, elim conjE)
       apply simp
  
  using assms(1) assms(3) assms(4) getVWNC_var apply blast
  
  using assms(1) assms(3) assms(4) getVWNC_var apply blast
  
  using assms(1) assms(3) assms(4) getVWNC_var apply blast
    apply(elim conjE)
    apply(subgoal_tac "a = x")
     apply simp
  using assms(3,4,5,6)
  
  apply (metis assms(1) getVWNC_var write_to_different_var)
  
  using w_in_writes_on_var apply blast
  using assms(3,4,5,6)
    apply(elim conjE)
   apply(subgoal_tac "a = x")
    apply simp
    apply(subgoal_tac "var w = z")
  apply simp
  
     apply (simp add: assms(1))
  
  using assms(1) getVWNC_var apply blast
  
  using w_in_writes_on_var apply blast
  apply(subgoal_tac "a = x")
  apply (simp add: releasing_def)
  using w_in_writes_on_var by blast

lemma ext_c_obs_Up_intro  : 
  assumes  "wfs \<sigma>"
  and "getVWNC \<sigma> t x = w"
  and "getTS \<sigma> w = ts'"
  and  "[y =\<^sub>t v] \<sigma>"
  and  " \<not> [x \<approx>\<^sub>t' u] \<sigma>"
  and  "x \<noteq> y"  
  and "t' \<noteq> t"
shows "[x = u]\<lparr>y =\<^sub>t' v\<rparr> (update_trans t w u \<sigma> ts')"
  using assms(4,5)
  apply(simp add: c_obs_def p_obs_def d_obs_def d_obs_t_def visible_writes_def)
  apply(intro allI impI conjI, elim conjE)
  using assms(2,3,6,7)
    apply(subgoal_tac "a = x")
    apply(subgoal_tac "var w = x")
      apply simp
      apply(elim disjE)
       apply simp
       apply(case_tac "releasing \<sigma> w")
        apply simp
  apply(simp add: ts_oride_def)
        apply (metis assms(1) dual_order.antisym lastWr_def modView_lte_last same_ws wfs_def writes_new_update_diff_var)
       apply simp
        apply (simp add: lastWr_def writes_new_update_diff_var)
  apply (case_tac "b = ts'")
  using assms(1) w_not_in_writes_on apply blast
      apply simp
      apply(simp add: value_def)
      apply blast
  using assms(1) getVWNC_var apply blast
   using w_in_writes_on_var apply blast
    apply (metis assms(1) assms(2) assms(3) assms(6) d_obs_def d_obs_t_def update_diff_var_pres_dobs_ext)
  apply(elim conjE)
    apply(subgoal_tac "a = x")
   apply(subgoal_tac "var w = x")
    apply simp
    apply(elim disjE)
  apply(simp add: releasing_def)
    apply(simp add: releasing_def)
  apply(case_tac "b = ts'")
  using assms(1) assms(2) assms(3) w_not_in_writes_on apply blast
  using assms(7)
    apply simp
  apply(simp add: value_def)
    apply blast
  using assms(1) assms(2) getVWNC_var apply blast
  using w_in_writes_on_var by blast
  


lemma ext_c_obs_read_diff_var_pres  : 
  assumes  "wfs \<sigma>"
  and  "[x = u]\<lparr>y =\<^sub>t' v\<rparr> \<sigma>"
  and  "z \<noteq> x"  
  and "x \<noteq> y"
  and "w = getVW \<sigma> t z"
shows "[x = u]\<lparr>y =\<^sub>t' v\<rparr> (read_trans t b w \<sigma>)"
  using assms(2)
  apply(simp add: c_obs_def d_obs_def visible_writes_def)
  apply(subgoal_tac "var w = z")
   defer
  using assms(1) assms(5) getVW_var apply blast
  apply(intro allI impI)
  apply(subgoal_tac "a = x") defer
  using w_in_writes_on_var apply blast
  apply simp
  apply(intro conjI, elim conjE)
    apply (simp add: value_def)
    apply(subgoal_tac "var w \<noteq> x") 
     apply simp
  apply(case_tac "t \<noteq> t'")
      apply (simp add: lastWr_read_pres)
     apply(case_tac "\<not>syncing \<sigma> w b")
      apply (simp add: lastWr_read_pres)
     apply simp
     apply(simp add: ts_oride_def)
  apply(case_tac "tst (thrView \<sigma> t' x)
              \<le> tst (modView \<sigma> w x)")
      apply (simp add: lastWr_read_pres)
     apply (simp add: lastWr_read_pres)
  using assms(3) apply blast
   apply (simp add: value_def)
   apply(case_tac "t \<noteq> t'")
    apply (simp add: lastWr_read_pres)
   apply simp
   apply(case_tac "\<not>syncing \<sigma> w b")
    apply simp
  apply(case_tac "x = z")
  using assms(3) apply blast
  apply (simp add: lastWr_read_pres)
   apply simp
     apply(simp add: ts_oride_def)
  apply(case_tac "x = z")
  using assms(3) apply blast
   apply simp
  apply(case_tac "tst (thrView \<sigma> t' x)
               \<le> tst (modView \<sigma> w x)")
  apply simp
    apply (metis dual_order.trans lastWr_read_pres)
   apply simp
   apply (simp add: lastWr_read_pres)
  apply(simp add: releasing_def)
  apply(case_tac "t \<noteq> t'", simp)
   apply(simp add: value_def)
   apply(simp add: value_def)
    apply(case_tac "\<not>syncing \<sigma> w b", simp)
   
  using assms(3) apply auto[1]
  apply simp
     apply(simp add: ts_oride_def)
  apply(case_tac "x = z")
  
  using assms(3) apply blast
  apply simp
  apply(case_tac "tst (thrView \<sigma> t' x)
               \<le> tst (modView \<sigma> w x)")
   apply simp
  by simp
  

lemma ext_c_obs_rdx_pres  :
  assumes  "wfs \<sigma>"
  and  "[x = u]\<lparr>y =\<^sub>t' v\<rparr> \<sigma>"
  and  "y \<noteq> x"  
  and "w = getVW \<sigma> t z"
  and "t \<noteq> t'"
shows "[x = u]\<lparr>y =\<^sub>t' v\<rparr> (read_trans t b w \<sigma>)"
  using assms(2,5)
  apply(simp add: c_obs_def d_obs_def visible_writes_def)
  apply (intro allI impI)
  apply(subgoal_tac "a = x")
  defer 
  using w_in_writes_on_var apply blast
  apply simp
  apply(intro conjI)
    apply(case_tac "x \<noteq> z")
     apply(simp add: value_def)
  apply(subgoal_tac "var w \<noteq> x")
    apply (simp add: lastWr_read_pres)
  using assms(1) assms(4) getVW_var apply blast
    apply simp
  apply(simp add: value_def)
  
    apply (simp add: lastWr_read_pres)
   apply(simp add: value_def)
  
   apply (simp add: lastWr_read_pres)
 by(simp add: value_def releasing_def)


(******* Covered **********)

lemma covered_contradiction [simp]:
  assumes "wfs \<sigma>"
    and "cvd[x, u] \<sigma>"
    and "u \<noteq> v"
    and "[x =\<^sub>t v] \<sigma>"
  shows "False"
  using assms
  by (metis covered_v_def d_obs_def d_obs_t_def wfs_def)


lemma covered_contradiction2  :
  assumes "wfs \<sigma>"
    and "cvd[x, u] \<sigma>"
    and "cvd[x, v] \<sigma>"
    and "u \<noteq> v"
  shows "False"
  using assms
  by (metis covered_v_def last_write_write_on wfs_def)

lemma covered_wr_diif_var_pres  :
  assumes "wfs \<sigma>"
  and "cvd[x, u] \<sigma>"
  and "getVWNC \<sigma> t y = w"
  and "getTS \<sigma> w = ts'"
  and "x \<noteq> y"
shows "cvd[x, u] (write_trans t b w v \<sigma> ts')"
  using assms(2,5)
  apply(simp add: covered_v_def)
  apply(intro allI impI conjI, elim conjE)
   apply(subgoal_tac "a = x")
    apply simp
    apply(simp add: lastWr_def)
    apply(subgoal_tac "var w = y")
  apply simp
  using assms(1) assms(3) getVWNC_var apply blast
  using w_in_writes_on_var apply blast
  apply(simp add: value_def)
  apply(subgoal_tac "a = x")
    apply(subgoal_tac "var w = y")
  apply simp
  using assms(1) assms(3) getVWNC_var apply blast 
  using w_in_writes_on_var by blast



lemma ext_cvd_update_cvd  :
  assumes "wfs \<sigma>"
      and "w = getVWNC \<sigma> t x"
      and "ts' = getTS \<sigma> w"
      and "cvd[x, u] \<sigma>"
    shows "cvd[x, v] (update_trans t w v \<sigma> ts')"
  apply(case_tac "w \<noteq> lastWr \<sigma> x")
  using assms(1) assms(2) assms(4) covered_v_def getVWNC_in_writes_on getVWNC_wa apply blast
  apply simp
  apply(subgoal_tac "var w = x")
  defer
   apply simp
  apply (subgoal_tac "value \<sigma> w = u") defer
  using assms(1) assms(4) covered_v_def last_write_write_on wfs_def apply blast
  using assms(4)
  apply(simp add: covered_v_def)
  apply(intro allI impI)
   apply(subgoal_tac "a=x")
   apply simp
   defer
  using w_in_writes_on_var apply blast
  apply(elim conjE, intro conjI)
   apply(case_tac "b = ts'") 
    apply (metis assms(1) assms(2) assms(3) getTS_valid getVWNC_in_vw lastWr_def lastWr_upd)
   apply simp
   apply(case_tac "(x, b) = w")
    apply simp
   apply simp
   apply(case_tac "b < tst w")
  apply simp
  apply (metis Max.coboundedI assms(1) assms(2) finite_imageI getVWNC_in_writes_on image_eqI lastWr_def last_write_max2 not_less_iff_gr_or_eq order.not_eq_order_implies_strict wfs_def)
  apply(case_tac "b = ts'") 
   apply(simp add: value_def)
  apply simp
   apply(case_tac "(x, b) = w")
   apply simp
  apply(case_tac "b < tst w")
  apply simp 
  by (metis Max.coboundedI assms(1) assms(2) finite_imageI getVWNC_in_writes_on image_eqI lastWr_def last_write_max2 not_less_iff_gr_or_eq order.not_eq_order_implies_strict wfs_def)
  
lemma covered_update_pres_ext  :
  assumes  "wfs \<sigma>"
  and "cvd[x, u] \<sigma>"
  and "getVWNC \<sigma> t x = w"
  and "getTS \<sigma> w = ts'"
shows "cvd[x, v] (update_trans t w v \<sigma> ts')"
  using assms(1) assms(2) assms(3) assms(4) ext_cvd_update_cvd by blast

lemma ext_cvd_rd_pres  :
     assumes  "cvd[x, u] \<sigma>"
    and "wfs \<sigma>"
      and "w = getVW \<sigma> t y"
    shows "cvd[x, u]  (read_trans t b w \<sigma>)"
  using assms(1)
  apply(simp add: covered_v_def)
  apply(intro allI impI conjI)
   apply (simp add: lastWr_read_pres)
  by(simp add: value_def)
  


(************* INIT *****************)
lemma init_rd_pres  :
  assumes "wfs \<sigma>"
  and " [init x u] \<sigma>"
  and "w = getVW \<sigma> t y"
shows "[init x u]  (read_trans t b w \<sigma>)"
  using assms(2)
  apply(unfold init_val_def value_def)
  apply(unfold read_trans_def rev_app_def Let_def update_thrView_def writes_on_def)
  by simp


lemma init_wr_pres_1:
  assumes "wfs \<sigma>"
  and " [init x u] \<sigma>"
  and "getVWNC \<sigma> t y = w"
  and "getTS \<sigma> w = ts'"
  and "x = y"
shows "[init x u] (write_trans t b w v \<sigma> ts')"
  using assms(2)
  apply(simp add: init_val_def mo_def)
  apply(simp add: value_def)
  apply clarsimp
  apply(subgoal_tac "a = x")
  defer
    apply (simp add: w_in_writes_on_var)
  apply simp
  apply(subgoal_tac "var w = x")
   defer 
  using assms(5)
  using assms(1) assms(3) getVWNC_var apply blast
  apply simp
  apply(rule_tac x = x in exI)
  apply simp
  apply(subgoal_tac "ba \<noteq> ts'")
   defer  
  using assms(1) assms(3) assms(4) assms(5) w_not_in_writes_on apply blast
  apply(rule_tac x = ba in exI)
  apply(intro conjI)  
     apply simp
    defer  
    apply blast
   apply simp
  apply simp
  using assms(3,4,5)
  by (metis assms(1) getTS_greater_init_ts)

lemma init_wr_pres_2:
  assumes "wfs \<sigma>"
  and " [init x u] \<sigma>"
  and "getVWNC \<sigma> t y = w"
  and "getTS \<sigma> w = ts'"
  and "x \<noteq> y"
shows "[init x u] (write_trans t b w v \<sigma> ts')"
  using assms(2)
  apply(simp add: init_val_def mo_def)
  apply(simp add: value_def)
  apply clarsimp
  apply(subgoal_tac "a = x")
  defer
   apply (simp add: w_in_writes_on_var)
    apply simp
  apply(subgoal_tac "var w = y")
   defer 
  using assms(1) assms(3) getVWNC_var apply blast
  using assms(5)
  apply simp
  using assms(3,4)
  apply(rule_tac x = x in exI)
  apply simp
  by blast 


lemma init_wr_pres:
  assumes "wfs \<sigma>"
  and " [init x u] \<sigma>"
  and "getVWNC \<sigma> t y = w"
  and "getTS \<sigma> w = ts'"
shows "[init x u] (write_trans t b w v \<sigma> ts')"
  apply(case_tac "y = x")
  using assms(1) assms(2) assms(3) assms(4) init_wr_pres_1 apply blast
  using assms(1) assms(2) assms(3) assms(4) init_wr_pres_2 by auto


lemma init_upd_pres  :
  assumes "wfs \<sigma>"
  and " [init x u] \<sigma>"
  and "w = getVWNC \<sigma> t y"
  and " ts' = getTS \<sigma> w"
shows "[init x u]  (update_trans t w v \<sigma> ts')"
  apply(case_tac "x = y")
  using assms(2)
   apply(simp add: init_val_def mo_def)
  apply(simp add: value_def)
  apply clarsimp
   apply(subgoal_tac "a = y") defer
    apply (simp add: w_in_writes_on_var) defer
   apply simp
  apply(subgoal_tac "var w = y")
    apply simp
  apply(rule_tac x = y in exI)
  apply(rule_tac x = b in exI)
  apply(intro conjI)   
       apply blast
      apply (metis assms(1) assms(3) assms(4) getTS_greater_init_ts)
     apply simp
  apply(case_tac "b = ts'")
     apply (simp add: assms(1) assms(3) assms(4) w_not_in_writes_on)
  apply simp 
  using assms(1) assms(3) getVWNC_var apply blast
  using assms(2)
   apply(simp add: init_val_def mo_def)
  apply(simp add: value_def)
  apply clarsimp
   apply(subgoal_tac "a = x") defer
    apply (simp add: w_in_writes_on_var) defer
  apply simp
  apply(subgoal_tac "var w = y")
    apply simp
  apply(rule_tac x = x in exI)
  apply(rule_tac x = b in exI)
  apply(intro conjI)     
     apply simp
    apply simp
  apply simp
  using assms(1) assms(3) getVWNC_var by blast  




end
