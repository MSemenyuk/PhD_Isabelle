theory TS_Pop_Refinement
imports  TS_Refinement_Proof_Rules
begin


lemma stuttering_step_L1_pop_bd:
  assumes "wfs ccs"
  and "lib_wfs cls ccs"
  and "pc ps t = L1"
  and "lib_pop t l ps cls ccs ps' cls' ccs'"      
  and "rr f ps als cls"
  and "rr_cliV f cls als ps"
  and "ref_client_thrView t acs ccs"
  and "rr_f_pushed_unmatched f cls als ps"
  and "rr_cliV_thView t f ccs cls als ps"
shows "rr f ps' als cls' 
            \<and> rr_cliV f cls' als ps' 
            \<and> ref_client_thrView t acs ccs' 
            \<and> rr_f_pushed_unmatched f cls' als ps' 
            \<and> rr_cliV_thView t f ccs' cls' als ps'"
proof - 
  have a1: "lib_value cls' (lib_lastWr cls' Top) = lib_value cls (lib_lastWr cls Top)" 
    using assms(3) assms(4) lib_pop_def rd_A_preserves_last by auto
      have a4: "\<And>a. lib_value cls (lib_lastWr cls a) = lib_value cls' (lib_lastWr cls' a)"
    using assms 
    apply (simp add: lib_pop_def) 
    by (metis (no_types, lifting) lib_last_in_visible_writes lib_read_last_diff_var_pres lib_value_read_pres lib_visible_writes_def mem_Collect_eq)
  show ?thesis
  proof (intro conjI)
  from assms show "rr f ps' als cls'"
    apply (simp add: rr_def lib_pop_def pop_inv_def)
    by (metis (no_types, hide_lams) a4 lastTop_def)
  from assms show "rr_cliV f cls' als ps'"
    apply(simp add: rr_cliV_def lib_pop_def lib_read_step_def lib_read_def all_updates_l 
                    lib_value_def lib_lastWr_def lib_writes_on_def ref_client_thrView_def)
    apply safe
    by(simp_all add: all_updates_l)
  from assms show "ref_client_thrView t acs ccs'"
    apply (simp add: ref_client_thrView_def lib_pop_def lib_read_step_def lib_read_def all_updates_l)
    apply (safe; simp add: ts_oride_def)
    apply (meson less_le_trans not_less) 
    apply (meson less_le_trans not_le)
    by (meson less_le_trans not_le)
  from assms show "rr_f_pushed_unmatched f cls' als ps' "
    by (simp add: rr_f_pushed_unmatched_def lib_pop_def lib_read_step_def lib_read_def all_updates_l)
  from assms show "rr_cliV_thView t f ccs' cls' als ps'"
    apply (simp add: rr_cliV_thView_def lib_pop_def lib_read_step_def lib_read_def all_updates_l)
    apply safe
    apply(simp_all add: ts_oride_def)
    using dual_order.trans by blast+
  qed
qed 

lemma stuttering_step_L1_pop:
  assumes "wfs ccs"
  and "lib_wfs cls ccs"
  and "pc ps t = L1"
  and "rr f ps als cls"
  and "lib_pop t l ps cls ccs ps' cls' ccs'"      
  and "rr_cliV f cls als ps"
  and "ops_wfs_ext  als acs"
  and "ref_client_thrView t acs ccs"
  and "rr_f_pushed_unmatched f cls als ps"
  and "rr_cliV_thView t f ccs cls als ps"
shows "\<exists> als' acs' f'.  als' = als \<and> acs' = acs \<and> rr f' ps' als' cls' \<and> rr_cliV f' cls' als' ps' \<and> ref_client_thrView t acs' ccs' \<and> rr_f_pushed_unmatched f' cls' als' ps' \<and> rr_cliV_thView t f' ccs' cls' als' ps'"
  using assms stuttering_step_L1_pop_bd
  by fastforce


lemma stuttering_step_L2_pop:
  assumes "wfs ccs"
  and "wfs acs"
  and "lib_wfs cls ccs"
  and "ops_wfs als acs"
  and "pc ps t = L2"
  and "res ps' t"
  and "rr f ps  als cls"
  and "lib_pop t l ps cls ccs ps' cls' ccs'"      
  and "pop_inv t l (pc ps t) cls ccs ps"
  and "glb_inv ps cls"
  and "rr_cliV f cls als ps"
  and "ops_wfs_ext  als acs"
  and "ref_client_thrView t acs ccs"
  and "rr_f_pushed_unmatched f cls als ps"
  and "rr_cliV_thView t f ccs cls als ps"
shows "\<exists> als' acs' f'.  als' = als \<and> acs' = acs \<and> rr f' ps' als' cls' \<and> rr_cliV f' cls' als' ps' \<and> ref_client_thrView t acs' ccs' \<and> rr_f_pushed_unmatched f' cls' als' ps' \<and> rr_cliV_thView t f' ccs' cls' als' ps'"
  using assms
  apply(rule_tac x = als in exI)
  apply(rule_tac x = acs in exI)
  apply(rule_tac x = f in exI)
      apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = lib_value cls (lib_lastWr cls Top)", simp)
   apply(subgoal_tac "pushed_addr ps' = pushed_addr ps")
  apply(subgoal_tac "lib_writes_on cls' Top = lib_writes_on cls Top")
  apply(intro conjI)
        apply(simp_all)
      apply(simp add: rr_def lib_pop_def pop_inv_def)
         apply(intro allI impI conjI)
  
  using rd_preserves_last apply force
  apply (metis rd_preserves_last)
  
  using rd_preserves_last apply auto[1]
  
  apply (metis lastTop_def)
  apply (simp add: lastTop_def)
  apply (meson rd_preserves_last)
  
  apply (metis lastTop_def rd_preserves_last)

        apply(simp add: rr_cliV_def )
        apply(simp add: lib_pop_def)
        apply(intro allI impI conjI)
  apply(subgoal_tac "lib_value cls' (a, b) = lib_value cls (a, b) \<and> lib_modView cls' (a, b) Lib.VARS.CVARS la = lib_modView cls (a, b) Lib.VARS.CVARS la")
         apply simp
  apply(intro conjI)
  using lib_value_read_pres apply blast
        apply(simp add: lib_read_step_def lib_read_def all_updates_l lib_syncing_def, elim exE conjE)
        apply clarsimp

       apply(simp add: ref_client_thrView_def lib_pop_def, elim conjE exE)
  apply(intro allI impI)
        apply(simp add: lib_read_step_def lib_read_def all_updates_l lib_syncing_def, elim exE conjE)
        apply clarsimp
      apply(simp add: rr_f_pushed_unmatched_def lib_pop_def)
     apply(simp add: rr_cliV_thView_def lib_pop_def)
  apply(intro allI impI)
        apply(simp add: lib_read_step_def lib_read_def all_updates_l lib_syncing_def, elim exE conjE)
        apply clarsimp
    apply(simp add: lib_pop_def all_updates_l)
    using read_pres_writes_on_diff_var apply blast 
      apply(simp add: lib_pop_def all_updates_l lib_value_def lib_lastWr_def lib_writes_on_def)
    apply(simp add: lib_pop_def all_updates_l)
    using rd_preserves_last by auto 


lemma refinement_step_pop:
  assumes "wfs ccs"
  and "wfs acs"
  and "lib_wfs cls ccs"
  and "ops_wfs als acs"
  and "pc ps t = L3"
  and "res ps' t"
  and "rr f ps  als cls"
  and "lib_pop t l ps cls ccs ps' cls' ccs'"      
  and "[lib(l) =\<^sub>t v] cls'"
  and "v > 0"
  and "pop_inv t l (pc ps t) cls ccs ps"
  and "glb_inv ps cls"
  and "rr_cliV f cls als ps"
  and "ops_wfs_ext  als acs"
  and "ref_client_thrView t acs ccs"
  and "rr_f_pushed_unmatched f cls als ps"
  and "rr_cliV_thView t f ccs cls als ps"
shows "\<exists> als' acs' f'. pop_step t v True als acs als' acs' \<and> rr f' ps' als' cls' \<and> rr_cliV f' cls' als' ps' \<and> ref_client_thrView t acs' ccs' \<and> rr_f_pushed_unmatched f' cls' als' ps' \<and> rr_cliV_thView t f' ccs' cls' als' ps'"
  apply(rule_tac x = "als
       \<lparr>ops := insert (POP, Max (snd ` ops als) + 1) (ops als),
          ops_mods := (ops_mods als)
            ((POP, Max (snd ` ops als) + 1) :=
               ops_mods als (POP, Max (snd ` ops als) + 1)
               \<lparr>ops_record.val := lib_value cls
     (lib_lastWr cls (lib_value cls (lib_lastWr cls Top))), op_sync := True\<rparr>),
          ops_matched :=
            insert
             ((PUSH, Max (snd ` ops_unmatched_push als)), POP,
              Max (snd ` ops als) + 1)
             (ops_matched als),
          ops_thrView := (ops_thrView als)
            (t := (POP, Max (snd ` ops als) + 1)),
          ops_modView_cli := (ops_modView_cli als)
            ((POP, Max (snd ` ops als) + 1) := thrView acs t)\<rparr>" in exI)
  apply(rule_tac x = "if (op_syncing als (PUSH, Max (snd ` ops_unmatched_push als)) True)
then
update_thrView t
          (ts_oride (thrView acs t)
            (ops_modView_cli als
              (PUSH, Max (snd ` ops_unmatched_push als))))
          acs
else
		  acs" in exI)
  apply(rule_tac x = f in exI)
proof (intro conjI)
  show "pop_step t v True als acs
     (als\<lparr>ops := insert (POP, Max (snd ` ops als) + 1) (ops als),
            ops_mods := (ops_mods als)
              ((POP, Max (snd ` ops als) + 1) :=
                 ops_mods als (POP, Max (snd ` ops als) + 1)
                 \<lparr>ops_record.val :=
                    lib_value cls
                     (lib_lastWr cls
                       (lib_value cls (lib_lastWr cls Top))),
                    op_sync := True\<rparr>),
            ops_matched :=
              insert
               ((PUSH, Max (snd ` ops_unmatched_push als)), POP,
                Max (snd ` ops als) + 1)
               (ops_matched als),
            ops_thrView := (ops_thrView als)
              (t := (POP, Max (snd ` ops als) + 1)),
            ops_modView_cli := (ops_modView_cli als)
              ((POP, Max (snd ` ops als) + 1) := thrView acs t)\<rparr>)
     (if op_syncing als (PUSH, Max (snd ` ops_unmatched_push als))
          True
      then update_thrView t
            (ts_oride (thrView acs t)
              (ops_modView_cli als
                (PUSH, Max (snd ` ops_unmatched_push als))))
            acs
      else acs)"
  using assms
  apply(simp add: rr_def pop_step_def lib_pop_def lib_CAS_Rel_step_def pop_inv_def, elim conjE)
  apply(elim exE conjE)
  apply(case_tac "lib_value cls (a, b) = prog_state.top ps t"; simp; elim conjE)
  apply(case_tac "a = Top", simp)
   apply(subgoal_tac "lib_value cls (Top, b) = x", simp)
  apply(intro impI conjI)
  apply(rule_tac x=PUSH in exI)
  apply(subgoal_tac "lib_value cls (lib_lastWr cls Top) = prog_state.top ps t")
  apply(simp add: lastPush_def)
  apply(rule_tac x = "Max (snd ` ops_unmatched_push als)" in exI)
  apply(rule_tac x = "Max (snd ` ops als) + 1" in exI)
  apply(intro conjI)  
  apply (metis ops_vts_pop_max)
  apply(case_tac "ops_unmatched_push als \<noteq> {}")
  apply (metis lastUnmatchedPush_max)
         apply (simp add: glb_inv3_def glb_inv_def)
  
  apply (simp add: lastTop_def)
   apply simp
         apply(subgoal_tac "[lib(l) =\<^sub>t v] cls", simp)
         apply(simp add: glb_inv_def glb_inv3_def lastTop_def, elim conjE) 
         apply (metis d_obs_visible_writes insertI1 lib_dobs_visible_writes)
        apply(simp add:  globals, elim conjE) 
        apply(simp add: lib_pop_def)
  using d_obs_post_CAS_R_diff_var_pre glb_inv_def glb_inv1_def lib_cvd_exist_write lib_pop_def not_gr_zero same_except_for_pc_def
  apply (smt subsetD)
  apply(simp add: op_pop_def)
        apply(simp add: op_pop_def)
         apply(intro conjI impI)
          apply (simp add: getOp_def)
  apply (simp add: op_syncing_def)
  apply(simp add: op_pop_def update_thrView_def)
        apply (simp add: getOp_def)
        apply(simp add: glb_inv_def glb_inv3_def, elim conjE) 
  apply (metis lastTop_def)
  apply(simp add: glb_inv_def glb_inv3_def, elim conjE) 
       apply (simp add: op_syncing_def)
  using lib_cvd_exist_last_write   defer 
       apply (metis assms(1) assms(3))
      apply(simp add: glb_inv_def glb_inv3_def, elim conjE) 
  apply(simp add: rr_def)
      apply(subgoal_tac "0 < lib_value cls (lib_lastWr cls Top)")
     apply(subgoal_tac "\<exists> x y . (x,y) = f (lastTop cls)")
      apply(elim exE)
  apply(rule_tac x = xa in exI)
      apply(rule_tac x = y in exI)
       apply(rule_tac x = "Max (snd ` ops als) + 1" in exI)
        apply(intro conjI)
            apply (metis ops_vts_pop_max)
           apply (metis lastTop_def all_not_in_conv lastPush_def lastUnmatchedPush_max)
  apply(subgoal_tac "lib_value cls
        (lib_lastWr cls (lib_value cls (lib_lastWr cls Top))) = v")
           apply simp
  apply (metis lastTop_def)
         apply(subgoal_tac "[lib(top ps t) =\<^sub>t v] cls")
          apply(simp add: glb_inv1_def )
          apply (metis lib_cvd_exist_last_write lib_d_obs_def lib_d_obs_t_def)
         apply (simp add:  lib_pop_def)
  apply (metis Null_def d_obs_post_CAS_R_diff_var_pre glb_inv1_def less_not_refl2 lib_cvd_exist_write)
        apply(simp add: op_pop_def)
  apply(intro conjI impI)
         apply (metis (no_types) OP.distinct(1) fst_conv getOp_def lastPush_def lastTop_def)
  apply(simp add: lastPush_def lastTop_def)
        apply metis

  apply(simp add: op_pop_def)
       apply (intro impI)
       apply (simp add: lastPush_def lastTop_def)
  apply (simp add: lastPush_def lastTop_def)
  apply (metis lib_cvd_exist_last_write)
     apply (simp add: cvd_vw_val) 
   apply (simp add: a_is_x) defer
   apply(simp add: op_pop_def getOp_def op_syncing_def lastTop_def)
  done
next show "rr f ps'
     (als\<lparr>ops := insert (POP, Max (snd ` ops als) + 1) (ops als),
            ops_mods := (ops_mods als)
              ((POP, Max (snd ` ops als) + 1) :=
                 ops_mods als (POP, Max (snd ` ops als) + 1)
                 \<lparr>ops_record.val :=
                    lib_value cls
                     (lib_lastWr cls
                       (lib_value cls (lib_lastWr cls Top))),
                    op_sync := True\<rparr>),
            ops_matched :=
              insert
               ((PUSH, Max (snd ` ops_unmatched_push als)), POP,
                Max (snd ` ops als) + 1)
               (ops_matched als),
            ops_thrView := (ops_thrView als)
              (t := (POP, Max (snd ` ops als) + 1)),
            ops_modView_cli := (ops_modView_cli als)
              ((POP, Max (snd ` ops als) + 1) := thrView acs t)\<rparr>)
     cls'"
    using assms
  apply(simp add: rr_def)
  apply(intro allI impI conjI)
        apply(simp add: lib_pop_def lastTop_def) 
    apply (metis succ_CAS_preserves_last)
        apply(simp add: lib_pop_def)
       apply(elim conjE)
             apply(simp add: lastTop_def ops_unmatched_push_def ops_mtch_push_def ops_on_def getOp_def)
    apply(subgoal_tac "lib_value cls' (lib_lastWr cls' (Suc a)) = lib_value cls (lib_lastWr cls (Suc a))")
  apply (metis (full_types, hide_lams) OP.distinct(5))
   apply (metis succ_CAS_preserves_last)

  apply(simp add: lib_pop_def)
  apply(simp add: glb_inv_def glb_inv5_def glb_inv4_def)
      apply(elim conjE)
      apply(erule_tac x = a in allE)
      apply simp
      apply(subgoal_tac "\<forall> a . a\<in>pushed_addr ps \<longrightarrow> lastNxtVal cls a \<noteq> lastTop cls")
  apply(subgoal_tac "prog_state.top ps t = lastTop cls")
        apply simp
            apply (simp add: pop_inv_def ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def, elim exE conjE)
            apply(subgoal_tac "f (lib_value cls (lib_lastWr cls Top)) = lastPush als")
  apply(simp add: lastPush_def ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def)
   apply(simp add: glb_inv_def glb_inv1_def   glb_inv3_def)
               apply metis
    apply (metis lastTop_def)
      apply (simp add: pop_inv_def, elim conjE exE)
           apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def)
    apply (metis assms(1) assms(3) cvd_CAS_R_success_read_val lib_cvd_exist_last_write lastTop_def)
         apply (metis assms(7) rr_def)
           apply (simp add: pop_inv_def lib_pop_def, elim conjE exE)   
    apply (metis cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write succ_CAS_preserves_last)
      apply (simp add: pop_inv_def, elim conjE exE)
        apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def)
          apply(intro allI impI conjI)
           apply(subgoal_tac " a \<in> pushed_addr ps")
            apply(case_tac "lastTop cls = Null", simp_all)
            apply(simp add: glb_inv_def glb_inv3_def glb_inv5_def glb_inv4_def glb_inv1_def , elim conjE)
           apply(simp add:  lib_pop_def)
          apply(simp add: glb_inv_def glb_inv1_def   glb_inv3_def  glb_inv4_def  glb_inv5_def)
  apply(subgoal_tac "a \<in> pushed_addr ps") 
           apply blast
           apply(simp add:  lib_pop_def)
           apply(simp add:  lib_pop_def)
         apply(simp add: glb_inv_def glb_inv1_def   glb_inv3_def  glb_inv4_def  glb_inv5_def, elim conjE exE)
        apply(simp add: lastPush_def ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def)

           apply (metis (no_types, lifting) lastTop_def cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
        apply(simp add: lib_pop_def pop_inv_def lastPush_def ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def, elim conjE exE)
        apply(simp add: lib_pop_def pop_inv_def lastPush_def ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def, elim conjE exE)
            apply(simp add: glb_inv_def glb_inv1_def   glb_inv3_def  glb_inv4_def  glb_inv5_def, elim conjE exE)
       apply(intro conjI impI)
 apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = ntop ps t")
           apply (metis (no_types, hide_lams) assms(1) assms(3) lastTop_def  cvd_CAS_R_success_read_val less_nat_zero_code lib_cvd_exist_last_write) 
      apply(subgoal_tac "[lib(Top) =\<^sub>t (ntop ps t)] cls'")
  apply(simp add: lib_d_obs_t_def lib_d_obs_def)
  using cvd_CAS_R_success_d_obs_post apply metis
         apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = ntop ps t")
          apply(subgoal_tac "ntop ps t \<in> pushed_addr ps")
    apply (metis (no_types, hide_lams) lastTop_def)
           apply(subgoal_tac "[lib(Top) =\<^sub>t (ntop ps t)] cls'")
           apply(simp add: lib_d_obs_t_def lib_d_obs_def)
  apply (metis cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write not_gr0)
  using cvd_CAS_R_success_d_obs_post lastTop_def apply metis
        apply(subgoal_tac "f (lastTop cls) = lastPush als")
        apply(simp add: lastPush_def ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def)
         apply(subgoal_tac "lib_value cls (lib_lastWr cls Top) = top ps t")
          apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = ntop ps t")
  apply (metis)
           apply(subgoal_tac "[lib(Top) =\<^sub>t (ntop ps t)] cls'")
  apply(simp add: lib_d_obs_t_def lib_d_obs_def)
  using cvd_CAS_R_success_d_obs_post apply metis
  apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
        apply(simp add: lastPush_def ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def)
  apply (metis lastTop_def cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
          apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = ntop ps t")
  apply (metis Zero_not_Suc cvd_CAS_R_success_read_val gr0_conv_Suc lastTop_def lib_cvd_exist_last_write)
           apply(subgoal_tac "[lib(Top) =\<^sub>t (ntop ps t)] cls'")
         apply(simp add: lib_d_obs_t_def lib_d_obs_def lastTop_def)
        apply (meson cvd_CAS_R_success_d_obs_post) 
       apply(simp add: lastTop_def)
       apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = ntop ps t")
  using lib_cvd_exist_last_write cvd_CAS_R_success_read_val Zero_not_Suc cvd_CAS_R_success_read_val gr0_conv_Suc lib_cvd_exist_last_write
  apply smt
  using succ_CAS_last_value 
  apply (metis cvd_CAS_R_success_read_val)
            apply(subgoal_tac "[lib(Top) =\<^sub>t (ntop ps t)] cls'")
       apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = lastNxtVal cls (lastTop cls)", simp)
          apply(simp add:lastTop_def lastPush_def ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def)
  apply(subgoal_tac " f (lastNxtVal cls (lastTop cls)) = oneBeforeLastPush als", simp)
          apply(simp add: oneBeforeLastPush_def lastPush_def ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def)
  apply(subgoal_tac "{opp.  fst opp = PUSH \<and>  (opp = (POP, Max (snd ` ops als) + 1) \<or> opp \<in> ops als)}
= {opp. fst opp = PUSH \<and> opp \<in> ops als}", simp)
          apply safe
  apply(subgoal_tac "{opp.
              fst opp = PUSH \<and>
              (opp =
               (PUSH,
                Max (snd ` ({opp. fst opp = PUSH \<and> opp \<in> ops als} - {opp. fst opp = PUSH \<and> opp \<in> fst ` ops_matched als}))) \<or>
               opp \<in> fst ` ops_matched als)} = {opp.
              fst opp = PUSH \<and>
              opp \<in> fst ` ops_matched als} \<union>
             {(PUSH,
               Max (snd `
                    ({opp.
                      fst opp = PUSH \<and>
                      opp \<in> ops als} -
                     {opp.
                      fst opp = PUSH \<and>
                      opp
                      \<in> fst ` ops_matched als})))}")
  apply (metis lastTop_def Diff_insert Un_empty_right Un_insert_right)
  apply safe  
  apply blast
             apply blast
  apply blast
  apply blast
  apply (metis fst_eqD)  
  apply (metis OP.distinct(5) fst_conv)
  apply(simp add: lib_pop_def pop_inv_def, elim exE conjE)
  using assms nxt_TopLV_oneBeforeLast[where als = als and acs = acs and f=f and ps = ps and cls=cls and ccs=ccs] 
        apply simp
  apply (metis lastTop_def cvd_CAS_R_success_read_val lib_cvd_exist_last_write)
  apply(simp add: lib_pop_def pop_inv_def glb_inv_def, elim exE conjE)
          apply(subgoal_tac "[lib(Top) =\<^sub>t (ntop ps t)] cls'")
        apply(simp add: lib_d_obs_t_def lib_d_obs_def)
  apply (metis (no_types, lifting) Null_def cvd_CAS_R_success_read_val glb_inv3_def gr_implies_not0 lastTop_def lib_cvd_exist_last_write)
  apply blast
  apply(simp add: lib_pop_def pop_inv_def glb_inv_def, elim exE conjE)
  apply (simp add: cvd_CAS_R_success_d_obs_post)
          apply(subgoal_tac "[lib(Top) =\<^sub>t (ntop ps t)] cls'")
      apply(simp add: lib_d_obs_t_def lib_d_obs_def op_value_def)
  apply(intro conjI impI)
  apply(subgoal_tac "a \<in> pushed_addr ps")
             apply(subgoal_tac "f a \<in> ops_unmatched_push als")
  apply (metis (no_types, lifting) DiffE  assms(4) getTs_def image_iff  mem_Collect_eq old.prod.exhaust ops_on_def ops_unmatched_push_def ops_vts_pop_def ops_vts_pop_max snd_conv)
        apply blast
  apply(simp add: lib_pop_def, elim exE conjE)
      apply(simp add: lib_pop_def, elim exE conjE)
      apply(subgoal_tac " (lib_lastWr cls' a) = (lib_lastWr cls a)", simp)
       apply(subgoal_tac "a \<noteq> Top")
  apply(subgoal_tac "lib_lastWr cls a \<in> lib_writes_on cls a")
  using write_value_CAS_R_diff_var apply auto[1]
  apply(simp add: lib_wfs_def)
        apply (metis all_not_in_conv assms(3) lib_last_in_writes_on)
  apply(simp add: pop_inv_def glb_inv_def glb_inv5_def, elim exE conjE)
  apply blast
       apply(subgoal_tac "a \<noteq> Top")
  using assms(1) last_CAS_R_diff_var apply auto[1]
  apply(simp add: pop_inv_def glb_inv_def glb_inv5_def, elim exE conjE)
      apply blast

  apply(simp add: lib_pop_def pop_inv_def, elim exE conjE)
     apply (simp add: cvd_CAS_R_success_d_obs_post)
   apply(simp add: lib_pop_def pop_inv_def, elim exE conjE)
            apply(simp add: glb_inv_def glb_inv1_def  glb_inv3_def  glb_inv4_def  glb_inv5_def pop_inv_def, elim conjE exE)
    apply(subgoal_tac "x = top ps t", simp)
  apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = ntop ps t")
  using assms(11)
      apply(simp add: pop_inv_def glb_inv6_def, elim conjE exE)
      apply(subgoal_tac "lastNxtVal cls a \<noteq> lastNxtVal cls (top ps t)")
       apply (metis lastTop_def lib_cvd_exist_last_write succ_CAS_preserves_last)
  apply (metis lastTop_def lib_cvd_exist_last_write succ_CAS_preserves_last)
  apply(subgoal_tac "[lib(Top) =\<^sub>t (ntop ps t)] cls'")
  apply(simp add: lib_d_obs_def lib_d_obs_t_def)
  apply (simp add: cvd_CAS_R_success_d_obs_post)
    apply (metis cvd_CAS_R_success_read_val)
  apply(subgoal_tac "a2 \<in> pushed_addr ps \<and> a1 \<in> pushed_addr ps")
    apply simp
   apply(simp add: lib_pop_def)
  apply(rule_tac x = a in exI)
  apply(rule_tac x = b in exI)
  apply(simp add: ops_init_def)
  done

next show "rr_cliV f cls'
     (als\<lparr>ops := insert (POP, Max (snd ` ops als) + 1) (ops als),
            ops_mods := (ops_mods als)
              ((POP, Max (snd ` ops als) + 1) :=
                 ops_mods als (POP, Max (snd ` ops als) + 1)
                 \<lparr>ops_record.val :=
                    lib_value cls
                     (lib_lastWr cls
                       (lib_value cls (lib_lastWr cls Top))),
                    op_sync := True\<rparr>),
            ops_matched :=
              insert
               ((PUSH, Max (snd ` ops_unmatched_push als)), POP,
                Max (snd ` ops als) + 1)
               (ops_matched als),
            ops_thrView := (ops_thrView als)
              (t := (POP, Max (snd ` ops als) + 1)),
            ops_modView_cli := (ops_modView_cli als)
              ((POP, Max (snd ` ops als) + 1) := thrView acs t)\<rparr>)
     ps'"
    using assms
   


     apply(simp add: rr_cliV_def)
     apply(intro conjI impI allI)
   apply(simp add: lib_pop_def)
      apply(elim conjE)
      apply(case_tac "(a, b) \<in> lib_writes_on cls Top")
  apply(subgoal_tac "lib_value cls' (a, b) =lib_value cls (a, b)")
       apply(subgoal_tac "lib_value cls (a,b) \<in> pushed_addr ps")
        apply(simp add: rr_def)
        apply(subgoal_tac " f (lib_value cls (a,b)) \<in> ops_unmatched_push als")
  apply(simp add: ops_unmatched_push_def ops_on_def getOp_def)
         apply blast
  apply simp
        apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
        apply(case_tac "lib_value cls (aa, ba) = prog_state.top ps t", simp_all)
  apply(simp add: lib_update_r_def all_updates_l lib_writes_on_def lib_value_def)
       apply (metis fresh_ts_not_in_writes)
      apply(subgoal_tac "lib_value cls' (a, b) = ntop ps t", simp)
  apply(simp add: pop_inv_def, elim exE conjE)
       apply(case_tac "ntop ps t = Null")
        apply(simp add: rr_def)
        apply(simp add: ops_init_def getOp_def)
       apply(subgoal_tac "ntop ps t \<in> pushed_addr ps")
        apply(subgoal_tac "f (ntop ps t)\<in> ops_on PUSH als")
  apply(simp add: ops_on_def getOp_def)
        apply(simp add: rr_def ops_unmatched_push_def)
        apply metis
       apply blast
        apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
        apply(case_tac "lib_value cls (aa, ba) = prog_state.top ps t", simp_all)
      apply(simp add: lib_update_r_def all_updates_l lib_writes_on_def lib_value_def)
      apply auto[1]
  apply(case_tac "(a, b) \<in> lib_writes_on cls Top")
  apply(subgoal_tac "lib_value cls' (a, b) =lib_value cls (a, b)")
       apply(subgoal_tac "lib_value cls (a,b) \<in> pushed_addr ps")
        apply simp
  apply(subgoal_tac "lib_modView cls' (a, b) Lib.VARS.CVARS la = lib_modView cls (a, b) Lib.VARS.CVARS la")
         apply simp
        apply(simp add:lib_pop_def lib_CAS_Rel_step_def, elim exE conjE)
        apply(case_tac "lib_value cls (aa, ba) = prog_state.top ps t", simp_all)
        apply(simp add: lib_update_r_def all_updates_l lib_writes_on_def lib_value_def)
        apply (metis fresh_ts_not_in_writes)
       apply(simp add:lib_pop_def)
        apply(simp add:lib_pop_def lib_CAS_Rel_step_def, elim exE conjE)
        apply(case_tac "lib_value cls (aa, ba) = prog_state.top ps t", simp_all)
      apply(simp add: lib_update_r_def all_updates_l lib_writes_on_def lib_value_def)
     apply (metis fresh_ts_not_in_writes)
       apply(simp add: lib_pop_def  pop_inv_def , elim conjE exE)
        apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
        apply(case_tac "lib_value cls (aa, ba) = prog_state.top ps t", simp_all)
     apply(simp add: lib_update_r_def all_updates_l lib_writes_on_def lib_value_def)
     apply(intro conjI impI)
       apply simp
        apply(simp add: rr_cliV_thView_def)
  apply blast
    by auto[1]

next 
  show "ref_client_thrView t
     (if op_syncing als (PUSH, Max (snd ` ops_unmatched_push als))
          True
      then update_thrView t
            (ts_oride (thrView acs t)
              (ops_modView_cli als
                (PUSH, Max (snd ` ops_unmatched_push als))))
            acs
      else acs)
     ccs'"

    using assms
    apply(simp add: ref_client_thrView_def)
    apply(simp add: lib_pop_def lib_CAS_Rel_step_def, elim exE conjE  lib_update_r_def all_updates_l rr_cliV_def globals rr_def lib_syncing_def)
  apply(case_tac "lib_value cls (a, b) = prog_state.top ps t", simp_all)
    apply(simp add: lib_update_r_def all_updates_l rr_cliV_def globals rr_def lib_syncing_def
          lib_pop_def lib_CAS_Rel_step_def, elim exE conjE)
  apply(case_tac "lib_value cls (a, b) = prog_state.top ps t", simp_all)
     apply(simp add: update_thrView_def ts_oride_def)
  apply(intro allI impI)
  apply(simp add: pop_inv_def, elim exE conjE)
  apply(subgoal_tac "xa = top ps t", simp) defer
  apply (metis cvd_vw_val) 
  apply(case_tac "top ps t \<noteq> Null", simp) 
  apply(case_tac "top ps t \<in> pushed_addr ps") defer
  apply (metis lib_cvd_exist_last_write) 
  apply(case_tac "lastTop cls = top ps t") 
  using lib_cvd_exist_last_write apply fastforce  
  apply (metis lastTop_def assms(3) lib_cvd_exist_last_write)
    apply(case_tac "f (top ps t) = lastPush als") defer 
     apply (metis lib_cvd_exist_last_write)
  apply(case_tac "tst (lib_modView cls (a, b) Lib.VARS.CVARS x) \<ge> tst (ops_modView_cli als
             (PUSH, Max (snd ` ops_unmatched_push als)) x)") defer  
   apply (metis (no_types, lifting) lastPush_def lib_visible_writes_def mem_Collect_eq)
  apply(simp add: rr_cliV_thView_def)
  apply (metis lastPush_def) done

next show "rr_f_pushed_unmatched f cls'
     (als\<lparr>ops := insert (POP, Max (snd ` ops als) + 1) (ops als),
            ops_mods := (ops_mods als)
              ((POP, Max (snd ` ops als) + 1) :=
                 ops_mods als (POP, Max (snd ` ops als) + 1)
                 \<lparr>ops_record.val :=
                    lib_value cls
                     (lib_lastWr cls
                       (lib_value cls (lib_lastWr cls Top))),
                    op_sync := True\<rparr>),
            ops_matched :=
              insert
               ((PUSH, Max (snd ` ops_unmatched_push als)), POP,
                Max (snd ` ops als) + 1)
               (ops_matched als),
            ops_thrView := (ops_thrView als)
              (t := (POP, Max (snd ` ops als) + 1)),
            ops_modView_cli := (ops_modView_cli als)
              ((POP, Max (snd ` ops als) + 1) := thrView acs t)\<rparr>)
     ps'"

    using assms

  apply(simp add:  rr_f_pushed_unmatched_def)
  apply(subgoal_tac "ops_unmatched_push
     (als\<lparr>ops := insert (POP, Max (snd ` ops als) + 1) (ops als),
            ops_mods := (ops_mods als)
              ((POP, Max (snd ` ops als) + 1) := ops_mods als (POP, Max (snd ` ops als) + 1)
                 \<lparr>ops_record.val :=
                    lib_value cls (lib_lastWr cls (lib_value cls (lib_lastWr cls Top))),
                    op_sync := True\<rparr>),
            ops_matched :=
              insert
               ((PUSH, Max (snd ` {f a |a. a \<in> pushed_addr ps})), POP,
                Max (snd ` ops als) + 1)
               (ops_matched als),
            ops_thrView := (ops_thrView als)(t := (POP, Max (snd ` ops als) + 1)),
            ops_modView_cli := (ops_modView_cli als)
              ((POP, Max (snd ` ops als) + 1) := thrView acs t)\<rparr>) = ops_unmatched_push als - {(PUSH,  Max (snd ` {f a |a. a \<in> pushed_addr ps}))}")
   defer
   apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def)
  apply(subgoal_tac "{opp. getOp opp = PUSH \<and> (opp = (POP, Max (snd ` ops als) + 1) \<or> opp \<in> ops als)} =
{opp. getOp opp = PUSH \<and> (opp \<in> ops als)}")
  apply simp
  apply blast
  apply (metis OP.distinct(5) fst_conv getOp_def) defer 
  apply simp
  apply(simp add: lib_pop_def pop_inv_def, elim exE conjE)
  apply(subgoal_tac "top ps t = lastTop cls") defer
  apply (metis lastTop_def assms(1) assms(3) cvd_CAS_R_success_read_val lib_cvd_exist_last_write)

   
  apply (simp add: ops_mtch_push_def getOp_def getTs_def lastPush_def ops_unmatched_push_def ops_on_def)
  defer

    apply(subgoal_tac "top ps t\<in>pushed_addr ps")
   defer
    apply(simp add: globals)
  defer
  apply(simp add: rr_def)
  apply(subgoal_tac " {f a |a. a \<in> pushed_addr ps \<and> a \<noteq> lib_value cls (lib_lastWr cls Top)} =  {f a |a. a \<in> pushed_addr ps} - {( f (lib_value cls (lib_lastWr cls Top)))}")
   apply (simp add: lastPush_def)
  apply(elim exE conjE)
   apply (simp add: lastTop_def ops_mtch_push_def getOp_def getTs_def lastPush_def ops_unmatched_push_def ops_on_def)
     apply(simp add: globals)
  apply safe
  apply blast
  apply simp defer
        apply (metis)
    apply simp_all
        apply metis
        
    apply metis
        by blast
next show "rr_cliV_thView t f ccs' cls'
     (als\<lparr>ops := insert (POP, Max (snd ` ops als) + 1) (ops als),
            ops_mods := (ops_mods als)
              ((POP, Max (snd ` ops als) + 1) :=
                 ops_mods als (POP, Max (snd ` ops als) + 1)
                 \<lparr>ops_record.val :=
                    lib_value cls
                     (lib_lastWr cls
                       (lib_value cls (lib_lastWr cls Top))),
                    op_sync := True\<rparr>),
            ops_matched :=
              insert
               ((PUSH, Max (snd ` ops_unmatched_push als)), POP,
                Max (snd ` ops als) + 1)
               (ops_matched als),
            ops_thrView := (ops_thrView als)
              (t := (POP, Max (snd ` ops als) + 1)),
            ops_modView_cli := (ops_modView_cli als)
              ((POP, Max (snd ` ops als) + 1) := thrView acs t)\<rparr>)
     ps'"
    using assms
  apply(simp add: rr_cliV_thView_def)
  apply(intro allI impI conjI)
  apply(subgoal_tac "ad \<in> pushed_addr ps")
    apply(simp add: rr_def)
    apply(subgoal_tac "f ad \<in> ops_unmatched_push als", simp)
  apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def) 
    apply blast
  apply(simp add: lib_pop_def)
  apply(subgoal_tac "ad \<in> pushed_addr ps")
   apply(simp add: lib_pop_def rr_def ref_client_thrView_def lib_CAS_Rel_step_def)
   apply(elim exE conjE)
  apply(case_tac "lib_value cls (a, b) = prog_state.top ps t", simp_all)
  apply(simp add: lib_update_r_def all_updates_l)
    apply(simp add: lib_pop_def)
 done
qed



end
