theory TS_Push_Refinement
imports  TS_Refinement_Proof_Rules
begin
lemmas wfs_ext = ops_wfs_ext_def cliV_init_def cliV_pushes_gt_init_def

lemma " B\<subseteq>A \<Longrightarrow> a\<notin>A \<Longrightarrow>  insert (a) (A) - B = insert (a) (A - B)"
  by blast

lemma new_element_in_set_comp: "insert a {x . x\<in>B} = {x. x=a \<or> x\<in>B}"
  by auto


lemma ops_mtch_push_subset_ops: "ops_wfs als acs \<Longrightarrow> ops_mtch_push als \<subseteq> ops als"
  apply(simp add: ops_mtch_push_def getOp_def)
  apply(simp add: ops_wfs_def ops_init_def getOp_def)
  by (metis (no_types, lifting) mem_Collect_eq subsetD subsetI)

lemma ops_on_subset_ops: "ops_wfs als acs \<Longrightarrow> ops_on PUSH als \<subseteq> ops als"
  apply(simp add: ops_on_def getOp_def)
  apply(simp add: ops_wfs_def ops_init_def getOp_def)
  by (metis (no_types, lifting) mem_Collect_eq  subsetI)


lemma ops_unmatched_push_subset_ops: "ops_wfs als acs \<Longrightarrow> ops_unmatched_push als \<subseteq> ops als"
  apply(simp add: ops_unmatched_push_def)
  by (meson Diff_subset dual_order.trans ops_on_subset_ops)


lemma ops_unmatched_push_subset_ops_on: "ops_wfs als acs \<Longrightarrow> ops_unmatched_push als \<subseteq> ops_on PUSH als"
  by(simp add: ops_unmatched_push_def ops_on_def)



lemma lastPush_in_ops_unmatched_push: "ops_wfs als acs \<Longrightarrow> ops_unmatched_push als \<noteq> {} \<Longrightarrow>
 lastPush als \<in> ops_unmatched_push als"
  apply(subgoal_tac "Max (snd`(ops_unmatched_push als))\<in> snd`(ops_unmatched_push als)") defer
  apply(subgoal_tac "finite(snd ` ops_unmatched_push als)")
    apply simp
  apply (simp add:  ops_on_def ops_unmatched_push_def ops_mtch_push_def getOp_def)
   apply(unfold ops_wfs_def ops_on_def ops_init_def)[1]
   apply simp
  apply(simp add: lastPush_def)
  apply (simp add: ops_on_def ops_unmatched_push_def ops_mtch_push_def getOp_def)
  by (simp add: image_iff set_diff_eq)


lemma lastPush_in_ops: "ops_wfs als acs \<Longrightarrow> ops_unmatched_push als \<noteq> {} \<Longrightarrow> lastPush als \<in> ops als"
  using lastPush_in_ops_unmatched_push ops_unmatched_push_subset_ops by fastforce

lemma lastPush_less_Max: "ops_wfs als acs \<Longrightarrow>ops_unmatched_push als \<noteq> {} \<Longrightarrow> getTs (lastPush als) \<le>  Max (snd `(ops als))"
  apply(subgoal_tac "lastPush als \<in> ops als")
  defer using lastPush_in_ops
   apply (simp add: lastPush_in_ops)
  by(unfold ops_wfs_def ops_unmatched_push_def getOp_def ops_on_def lastPush_def getTs_def, simp)


lemma a_in_ops_less_eq_Max: "ops_wfs als acs \<Longrightarrow>a \<in>ops als \<Longrightarrow> getTs (a) \<le>  Max (snd `(ops als))"
  by(unfold ops_wfs_def ops_unmatched_push_def getOp_def ops_on_def lastPush_def getTs_def, simp)

lemma Max_add_element: "finite(A) \<Longrightarrow> A \<noteq> {}  \<Longrightarrow> a\<notin>B  \<Longrightarrow> a>Max A \<Longrightarrow> Max ((A \<union> {a}) - B) = a"
  apply clarsimp
  by (smt DiffD1 Max_in empty_iff finite.insertI finite_Diff insert_Diff_if insert_iff not_max)

lemma Max_add_element_snd: "finite(A) \<Longrightarrow> A \<noteq> {}  \<Longrightarrow> a\<notin>(snd `B)  \<Longrightarrow> a>Max (snd `A) \<Longrightarrow> Max (snd`((A \<union> {(x,a)}) - B)) = a"
  apply clarsimp
  by (smt DiffE Max_in finite.insertI finite_Diff finite_imageI image_iff infinite_growing insertE insertI1 insert_Diff_if member_less_max snd_eqD)


lemma A_minus_B_max_in_A: "finite A \<Longrightarrow> A - B \<noteq> {} \<Longrightarrow> Max (snd` (A - B)) \<in> snd `A"
  by (metis Diff_insert_absorb Diff_subset eq_Max_iff  finite_imageI image_is_empty image_mono rev_finite_subset subset_Diff_insert)


lemma new_element_in_set_eq: "finite A  \<Longrightarrow> P b  \<Longrightarrow> {a . P a \<and> (a=b \<or> a\<in>A)} = {a. P a \<and> a\<in>A} \<union> {b}"
  by safe
  


lemma A_minus_B_not_empty: "ops_wfs als acs \<Longrightarrow> {opp.
              fst opp = PUSH \<and>
              (opp = (PUSH, Max (snd ` ops als) + 1) \<or>
               opp \<in> ops als)} -
             {opp.
              fst opp = PUSH \<and> opp \<in> fst ` ops_matched als} \<noteq> {}"
  apply(subgoal_tac "{opp.
              fst opp = PUSH \<and>
              (opp = (PUSH, Max (snd ` ops als) + 1) \<or>
               opp \<in> ops als)} = {opp.
              fst opp = PUSH \<and>
              (opp \<in> ops als)} \<union> {(PUSH, Max (snd ` ops als) + 1)}")
   defer
  apply(unfold ops_wfs_def, simp)[1] 
   apply (smt Collect_cong insert_Collect old.prod.inject prod.collapse)
  apply simp
  apply(unfold ops_wfs_def, simp)[1] 
  apply(intro allI impI)
  apply(subgoal_tac "(PUSH, Max (snd ` ops als) + 1)\<notin>ops als")
   apply (meson subset_iff)
  apply(subgoal_tac "Max (snd ` ops als) + 1 \<notin> snd` ops als")
   apply (metis (no_types, hide_lams) add.commute insertI1 insert_image snd_eqD)
  apply(subgoal_tac "finite(snd ` ops als)")
   apply (metis Max.coboundedI less_add_one less_le_not_le)
  by simp

lemma Max_set_new_el_eq:  "finite A \<Longrightarrow> A - B \<noteq> {} \<Longrightarrow> b\<notin>A \<Longrightarrow> P b \<Longrightarrow> Max (snd ` ({e . P e \<and> (e = b \<or> e\<in>A)} - B)) = Max (snd`({e. P e \<and> e\<in> A} \<union> {(b)} - B))"
  by (simp add: new_element_in_set_eq)


lemma ops_unmatched_push' :  "ops_wfs als acs \<Longrightarrow> ops_unmatched_push
             (als\<lparr>ops :=
                    insert (PUSH, Max (snd ` ops als) + 1)
                     (ops als),
                    ops_mods := (ops_mods als)
                      ((PUSH, Max (snd ` ops als) + 1) :=
                         ops_mods als
                          (PUSH, Max (snd ` ops als) + 1)
                         \<lparr>ops_record.val := v,
                            op_sync := True\<rparr>),
                    ops_thrView := (ops_thrView als)
                      (t := (PUSH, Max (snd ` ops als) + 1)),
                    ops_modView_cli := (ops_modView_cli als)
                      ((PUSH, Max (snd ` ops als) + 1) :=
                         thrView acs t)\<rparr>) = ops_unmatched_push als \<union> {(PUSH, Max (snd ` ops als) + 1)}"
  apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def)
  apply(subgoal_tac " (PUSH, Max (snd ` ops als) + 1)\<notin>
     ({opp. getOp opp = PUSH \<and> opp \<in> ops als}) \<and> (PUSH, Max (snd ` ops als) + 1)\<notin> {opp. getOp opp = PUSH \<and> opp \<in> fst ` ops_matched als}")

  apply(subgoal_tac "getOp (PUSH, Max (snd ` ops als) + 1) = PUSH")
  apply(subgoal_tac "{opp.
     getOp opp = PUSH \<and>
     (opp = (PUSH, Max (snd ` ops als) + 1) \<or> opp \<in> ops als)} = {opp.
     getOp opp = PUSH \<and>
     (opp \<in> ops als)}  \<union> {(PUSH, Max (snd ` ops als) + 1)}")
     apply clarsimp
     apply (simp add: insert_Diff_if)
  apply(unfold ops_wfs_def, simp)[1]
  using new_element_in_set_eq
  apply blast
   apply (simp add: getOp_def)
  apply(subgoal_tac "(PUSH, Max (snd ` ops als) + 1)
    \<notin> ops als")
  apply(intro conjI)
  apply simp
   apply(unfold ops_wfs_def, simp)[1]
  apply (meson subset_iff)
  by (metis getTs_def imageI  old.prod.exhaust ops_vts_pop_def ops_vts_pop_max  snd_conv)

lemma "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow>Max (insert a A) = Max {a , Max A}"
  by simp

lemma "finite A \<Longrightarrow> A = {} \<Longrightarrow>Max (insert a A) = a"
  by simp


lemma Max_insert_Max_plus_one: "ops_wfs als acs \<Longrightarrow> Max (snd ` ops als) + 1 =
       Max (insert (Max (snd ` ops als) + 1) (snd ` ops_unmatched_push als))"
  apply(case_tac "snd ` ops_unmatched_push als = {}")
  apply auto[1]
  apply(subgoal_tac "finite(ops_unmatched_push als) \<and> finite(ops als)")
   apply(subgoal_tac "Max (insert (Max (snd ` ops als) + 1) (snd ` ops_unmatched_push als)) = Max {Max (snd ` ops als) + 1, Max(snd ` ops_unmatched_push als)}")
    apply(subgoal_tac " Max (snd ` ops_unmatched_push als) \<le> Max (snd `(ops als))")
  apply(subgoal_tac "Max (snd ` ops als) + 1 > Max (snd ` ops als)")
      apply simp
  apply safe
    apply (metis (mono_tags, lifting) getTs_def lastPush_def lastPush_less_Max less_add_one max.bounded_iff max.strict_order_iff max_def snd_conv)
  using less_add_one apply blast
  apply (metis emptyE getTs_def lastPush_def lastPush_less_Max snd_eqD)
  apply (smt Max.bounded_iff Max.subset_imp Max_in Max_insert2 empty_is_image finite.emptyI finite.insertI finite_imageI insert_Diff insert_Diff_single insert_iff singletonD subset_insertI)
   apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def)
   apply(unfold ops_wfs_def, simp)
  by blast


lemma stuttering_step_L1_push:
  assumes "wfs ccs"
  and "wfs acs"
  and "lib_wfs cls ccs"
  and "ops_wfs als acs"
  and "pc ps t = L1"
  and "res ps' t"
  and "rr f ps  als cls"
  and "lib_push t v ps cls ccs ps' cls' ccs'"     
  and "v > 0"
  and "push_inv t v (pc ps t) cls ccs ps"
  and "glb_inv ps cls"
  and "rr_cliV f cls als ps"
  and "rr_cliV_thView t f ccs cls als ps"
  and "ops_wfs_ext  als acs"
  and "ref_client_thrView t acs ccs"
  and "to ps cls"
  and "rr_f_pushed_unmatched f cls als ps"
shows "\<exists> als' acs' f'. als' = als \<and> acs' = acs \<and> rr f' ps' als' cls' \<and> rr_cliV f' cls' als' ps' \<and> rr_cliV_thView t f' ccs' cls' als' ps'  \<and> ref_client_thrView t acs' ccs' \<and> rr_f_pushed_unmatched f' cls' als' ps'"
  using assms
  apply(rule_tac x = als in exI)
  apply(rule_tac x = acs in exI)
  apply(rule_tac x = f in exI)
  apply(subgoal_tac "lastTop cls' = lastTop cls")
  apply(intro conjI; simp; elim exE conjE)
      apply(simp add: rr_def)
  apply (smt assms(8) lib_push_L1_pushed)
     apply(simp add: rr_cliV_def)
  using assms(8) lib_push_L1_pushed apply blast
    apply(simp add: rr_cliV_thView_def)
  using assms(8) lib_push_L1_pushed apply blast
   apply(simp add: rr_f_pushed_unmatched_def)
  apply (metis assms(8) lib_push_L1_pushed)
   apply (simp add: lib_push_L1_pushed)
  done

lemma stuttering_step_L2_push:
  assumes "wfs ccs"
  and "wfs acs"
  and "lib_wfs cls ccs"
  and "ops_wfs als acs"
  and "pc ps t = L2"
  and "res ps' t"
  and "rr f ps  als cls"
  and "lib_push t v ps cls ccs ps' cls' ccs'"     
  and "v > 0"
  and "push_inv t v (pc ps t) cls ccs ps"
  and "glb_inv ps cls"
  and "rr_cliV f cls als ps"
  and "rr_cliV_thView t f ccs cls als ps"
  and "ops_wfs_ext  als acs"
  and "ref_client_thrView t acs ccs"
  and "to ps cls"
  and "rr_f_pushed_unmatched f cls als ps"
shows "\<exists> als' acs' f'. als' = als \<and> acs' = acs \<and> rr f' ps' als' cls' \<and> rr_cliV f' cls' als' ps' \<and> rr_cliV_thView t f' ccs' cls' als' ps'  \<and> ref_client_thrView t acs' ccs' \<and> rr_f_pushed_unmatched f' cls' als' ps'"
  using assms
  apply(rule_tac x = als in exI)
  apply(rule_tac x = acs in exI)
  apply(rule_tac x = f in exI)
  apply(subgoal_tac "lastTop cls' = lastTop cls")
  apply(subgoal_tac "lib_writes_on cls' Top = lib_writes_on cls Top")
  apply(intro conjI; simp; elim exE conjE)
       apply(simp add: rr_def)
        apply(intro allI impI conjI)
  apply(subgoal_tac "lib_value cls'
                 (lib_lastWr cls' (Suc a)) = lib_value cls
                 (lib_lastWr cls (Suc a))")
              apply simp
  apply(simp add:no_Top_n_def globals)
             apply (metis wr_preserves_last)       
  apply(subgoal_tac "lib_value cls'
                 (lib_lastWr cls' (Suc a)) = lib_value cls
                 (lib_lastWr cls (Suc a))")
              apply simp
  apply(simp add:no_Top_n_def globals)
            apply (metis wr_preserves_last)       
  apply(subgoal_tac "lib_value cls'
                 (lib_lastWr cls' (Suc a)) = lib_value cls
                 (lib_lastWr cls (Suc a))")
              apply simp
  apply(simp add:no_Top_n_def globals)
           apply (metis wr_preserves_last)       
  apply metis
         apply (metis wr_preserves_last)
  apply(simp add:no_Top_n_def globals)
  apply (metis write_diff_var_last_val)
       apply(simp add: rr_cliV_def)
       apply(simp add: lib_write_step_def lib_write_def, elim exE conjE, simp add: all_updates_l lib_writes_on_def lib_lastWr_def lib_value_def)
  apply(intro allI impI conjI, simp_all)
       apply (simp add: fresh_ts_not_in_writes)
      apply(simp add: rr_cliV_thView_def)
      apply(simp add: lib_write_step_def lib_write_def, elim exE conjE, simp add: all_updates_l lib_writes_on_def lib_lastWr_def lib_value_def)
      apply(simp add: rr_cliV_thView_def)
       apply(simp add: lib_write_step_def lib_write_def, elim exE conjE, simp add: all_updates_l lib_writes_on_def lib_lastWr_def lib_value_def)
     apply(simp add: rr_f_pushed_unmatched_def)
      apply(simp add: rr_cliV_thView_def)
       apply(simp add: lib_write_step_def lib_write_def, elim exE conjE, simp add: all_updates_l lib_writes_on_def lib_lastWr_def lib_value_def)
  apply(simp add: tst_def var_def)
   apply (metis a_is_x fst_conv)
       apply(simp add: lib_write_step_def lib_write_def, elim exE conjE, simp add: all_updates_l lib_writes_on_def lib_lastWr_def lib_value_def)
  apply(simp add:  globals tst_def var_def lib_value_def lib_lastWr_def lib_writes_on_def)
  by (smt Collect_cong a_is_x fst_conv)

lemma stuttering_step_L3_push:
  assumes "wfs ccs"
  and "wfs acs"
  and "lib_wfs cls ccs"
  and "ops_wfs als acs"
  and "pc ps t = L3"
  and "res ps' t"
  and "rr f ps  als cls"
  and "lib_push t v ps cls ccs ps' cls' ccs'"     
  and "v > 0"
  and "push_inv t v (pc ps t) cls ccs ps"
  and "glb_inv ps cls"
  and "rr_cliV f cls als ps"
  and "rr_cliV_thView t f ccs cls als ps"
  and "ops_wfs_ext  als acs"
  and "ref_client_thrView t acs ccs"
  and "to ps cls"
  and "rr_f_pushed_unmatched f cls als ps"
shows "\<exists> als' acs' f'. als' = als \<and> acs' = acs \<and> rr f' ps' als' cls' \<and> rr_cliV f' cls' als' ps' \<and> rr_cliV_thView t f' ccs' cls' als' ps'  \<and> ref_client_thrView t acs' ccs' \<and> rr_f_pushed_unmatched f' cls' als' ps'"
  using assms
  apply(rule_tac x = als in exI)
  apply(rule_tac x = acs in exI)
  apply(rule_tac x = f in exI)
  apply(subgoal_tac "lastTop cls' = lastTop cls")
  apply(subgoal_tac "lib_writes_on cls' Top = lib_writes_on cls Top")
  apply(intro conjI; simp; elim exE conjE)
       apply(simp add: rr_def)
        apply(intro allI impI conjI)
             apply(subgoal_tac "lib_value cls' (lib_lastWr cls' (Suc a)) = lib_value cls (lib_lastWr cls (Suc a))")
              apply metis
  using rd_A_preserves_last apply metis
            apply(subgoal_tac "lib_value cls' (lib_lastWr cls' (Suc a)) = lib_value cls (lib_lastWr cls (Suc a))")
              apply metis
  using rd_A_preserves_last apply metis
apply(subgoal_tac "lib_value cls' (lib_lastWr cls' (Suc a)) = lib_value cls (lib_lastWr cls (Suc a))")
              apply metis
  using rd_A_preserves_last apply metis
apply(subgoal_tac "lib_value cls' (lib_lastWr cls' (Suc a)) = lib_value cls (lib_lastWr cls (Suc a))")
              apply metis
  using rd_A_preserves_last apply metis
  using rd_A_preserves_last apply metis
  using rd_A_preserves_last apply metis
       apply(simp add: rr_cliV_def)
       apply(simp add: lib_read_step_def lib_read_def, elim exE conjE, simp add: all_updates_l lib_writes_on_def lib_lastWr_def lib_value_def)
      apply(simp add: rr_cliV_thView_def)
       apply(simp add: lib_read_step_def lib_read_def, elim exE conjE, simp add: all_updates_l lib_writes_on_def lib_lastWr_def lib_value_def)
      apply(intro allI impI conjI)
  apply(simp add: ts_oride_def)
  using dual_order.trans apply blast
      apply(simp add: rr_cliV_thView_def)
       apply(simp add: lib_read_step_def lib_read_def, elim exE conjE, simp add: all_updates_l lib_writes_on_def lib_lastWr_def lib_value_def)
     apply(simp add: rr_f_pushed_unmatched_def)
     apply(simp add: ref_client_thrView_def)
  apply(simp add: ts_oride_def)
  apply (meson order.trans)
  apply(simp add: rr_f_pushed_unmatched_def)
       apply(simp add: lib_read_step_def lib_read_def, elim exE conjE, simp add: all_updates_l lib_writes_on_def lib_lastWr_def lib_value_def)
       apply(simp add: lib_read_step_def lib_read_def, elim exE conjE, simp add: all_updates_l lib_writes_on_def lib_lastWr_def lib_value_def)
  apply safe
   apply(simp add: lastTop_def lib_value_def lib_lastWr_def lib_writes_on_def)
   apply(simp add: lastTop_def lib_value_def lib_lastWr_def lib_writes_on_def)
  done

lemma stuttering_step_L4_push:
  assumes "wfs ccs"
  and "wfs acs"
  and "lib_wfs cls ccs"
  and "ops_wfs als acs"
  and "pc ps t = L4"
  and "res ps' t"
  and "rr f ps  als cls"
  and "lib_push t v ps cls ccs ps' cls' ccs'"     
  and "v > 0"
  and "push_inv t v (pc ps t) cls ccs ps"
  and "glb_inv ps cls"
  and "rr_cliV f cls als ps"
  and "rr_cliV_thView t f ccs cls als ps"
  and "ops_wfs_ext  als acs"
  and "ref_client_thrView t acs ccs"
  and "to ps cls"
  and "rr_f_pushed_unmatched f cls als ps"
shows "\<exists> als' acs' f'. als' = als \<and> acs' = acs \<and> rr f' ps' als' cls' \<and> rr_cliV f' cls' als' ps' \<and> rr_cliV_thView t f' ccs' cls' als' ps'  \<and> ref_client_thrView t acs' ccs' \<and> rr_f_pushed_unmatched f' cls' als' ps'"
  using assms
  apply(rule_tac x = als in exI)
  apply(rule_tac x = acs in exI)
  apply(rule_tac x = f in exI)
  apply(subgoal_tac "lastTop cls' = lastTop cls")
  apply(subgoal_tac "lib_writes_on cls' Top = lib_writes_on cls Top")
  apply(intro conjI; simp; elim exE conjE)
       apply(simp add: rr_def)
        apply(intro allI impI conjI)
             apply(subgoal_tac "lib_value cls' (lib_lastWr cls' (Suc a)) = lib_value cls (lib_lastWr cls (Suc a))")
  apply metis 
  apply (metis old.nat.inject wr_preserves_last)
             apply(subgoal_tac "lib_value cls' (lib_lastWr cls' (Suc a)) = lib_value cls (lib_lastWr cls (Suc a))")
  apply metis 
            apply (metis old.nat.inject wr_preserves_last)
             apply(subgoal_tac "lib_value cls' (lib_lastWr cls' (Suc a)) = lib_value cls (lib_lastWr cls (Suc a))")
  apply metis 
           apply (metis old.nat.inject wr_preserves_last)
             apply(subgoal_tac "lib_value cls' (lib_lastWr cls' (Suc a)) = lib_value cls (lib_lastWr cls (Suc a))")
  apply metis 
          apply (metis old.nat.inject wr_preserves_last)
  apply (metis  wr_preserves_last)
  apply (metis add_diff_cancel_left' plus_1_eq_Suc write_diff_var_last_val)
       apply(simp add: rr_cliV_def)
       apply(intro allI impI conjI)
  apply(subgoal_tac "lib_value cls' (a, b) = lib_value cls (a, b) \<and> lib_modView cls' (a, b) Lib.VARS.CVARS l = lib_modView cls (a, b) Lib.VARS.CVARS l")
        apply metis
  apply(intro conjI)
  apply (metis wr_preserves_value_diff_var)
  apply (metis wr_preserves_mView_diff_var)
      apply(simp add: rr_cliV_thView_def)
  apply (metis lib_write_step_def)
     apply(simp add: rr_cliV_thView_def ref_client_thrView_def)
  apply (metis lib_write_step_def)
    apply(simp add: rr_f_pushed_unmatched_def)
  apply(simp add: globals no_Top_n_def)
  apply (metis (full_types) wr_preserves_writes_on_diff_var)
  apply(simp add: lastTop_def)
  by (metis wr_preserves_last)


lemma refinement_step_push:
  assumes "wfs ccs"
  and "wfs acs"
  and "lib_wfs cls ccs"
  and "ops_wfs als acs"
  and "pc ps t = L5"
  and "res ps' t"
  and "rr f ps  als cls"
  and "lib_push t v ps cls ccs ps' cls' ccs'"     
  and "v > 0"
  and "push_inv t v (pc ps t) cls ccs ps"
  and "glb_inv ps cls"
  and "rr_cliV f cls als ps"
  and "rr_cliV_thView t f ccs cls als ps"
  and "ops_wfs_ext  als acs"
  and "ref_client_thrView t acs ccs"
  and "to ps cls"
  and "rr_f_pushed_unmatched f cls als ps"
shows "\<exists> als' acs' f'. push_step t v True als acs als' acs' \<and> rr f' ps' als' cls' \<and> rr_cliV f' cls' als' ps' \<and> rr_cliV_thView t f' ccs' cls' als' ps'  \<and> ref_client_thrView t acs' ccs' \<and> rr_f_pushed_unmatched f' cls' als' ps'"
  using assms
  apply(rule_tac x = "als
           \<lparr>ops := insert (PUSH, (Max (snd ` ops als) + 1)) (ops als),
              ops_mods := (ops_mods als)
                ((PUSH, (Max (snd ` ops als) + 1)) := ops_mods als (PUSH,  (Max (snd ` ops als) + 1))
                   \<lparr>ops_record.val := v, op_sync := True\<rparr>),
              ops_thrView := (ops_thrView als)(t := (PUSH,  (Max (snd ` ops als) + 1))),
              ops_modView_cli := (ops_modView_cli als)((PUSH,  (Max (snd ` ops als) + 1)) := thrView acs t)\<rparr>" in exI)
  apply(rule_tac x = acs in exI)
  apply(rule_tac x = "f ((n_val ps t) := (PUSH, (Max (snd ` ops als) + 1)))" in exI)
  apply(intro conjI)
  apply(simp add: push_step_def, elim exE conjE)
      apply(rule_tac x="(Max (snd ` ops als) + 1)" in exI)
      apply(intro conjI)
  using ops_vts_push_max apply blast
   apply(simp add: op_push_def)
     apply(unfold rr_def)[1]
     apply(intro conjI)
       apply(elim conjE exE)
       apply(intro allI impI)
       apply(intro conjI)
             apply simp
              apply(intro allI conjI impI) 
  
                     apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_write no_Top_n_def succ_CAS_preserves_last)
  apply (smt cvd_CAS_R_success_read_val lib_cvd_exist_last_write succ_CAS_preserves_last)
                   apply metis
  apply (metis lastTop_def succ_CAS_preserves_last)
    apply auto[1]
                apply (metis lastTop_def succ_CAS_preserves_last)
  apply(elim conjE exE)
              apply(subgoal_tac "top ps t = lastTop cls", simp)
                apply(case_tac "lib_value cls (lib_lastWr cls Top) = Null", simp_all)
               apply(simp add: ops_init_def getOp_def getTs_def)
                 apply(subgoal_tac "snd op \<le> Max (snd` ops als) ")
  apply (metis add.commute add_strict_increasing cvd_CAS_R_success_read_val lib_cvd_exist_last_write succ_CAS_preserves_last zero_less_one)
  apply(subgoal_tac "finite(snd` ops als)")
                apply simp
               apply(unfold ops_wfs_def getOp_def ops_init_def getTs_def)[1]
                 apply simp
  apply(simp add: no_Top_n_def globals)

  apply(simp add: getTs_def)
              apply(subgoal_tac "f (lib_value cls (lib_lastWr cls Top)) \<in>  ops_unmatched_push als")               
               apply(simp add: ops_unmatched_push_def getTs_def ops_on_def getOp_def ops_mtch_push_def)
               apply clarsimp
                 apply(subgoal_tac "snd (f (lib_value cls (lib_lastWr cls Top))) \<le> Max (snd` ops als)")  
  apply(subgoal_tac "lib_value cls'
                (lib_lastWr cls' (Suc (n_val ps t))) = lib_value cls
                (lib_lastWr cls (Suc (n_val ps t)))", simp)
                  apply (metis succ_CAS_preserves_last)
  apply(simp add:  no_Top_n_def globals lastPush_def)
                 apply(subgoal_tac "finite(snd` ops als)")
  apply (metis Max_ge image_eqI snd_conv)
                apply(unfold ops_wfs_def getOp_def ops_init_def getTs_def)[1]
               apply simp   
                apply (simp add: glb_inv3_def glb_inv_def) 
               apply (metis cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write)

              apply (metis lastTop_def succ_CAS_preserves_last)
             apply(subgoal_tac "ops_unmatched_push
                 (als\<lparr>ops :=
                        insert (PUSH, Max (snd ` ops als) + 1)
                         (ops als),
                        ops_mods := (ops_mods als)
                          ((PUSH, Max (snd ` ops als) + 1) :=
                             ops_mods als
                              (PUSH, Max (snd ` ops als) + 1)
                             \<lparr>ops_record.val := v, op_sync := True\<rparr>),
                        ops_thrView := (ops_thrView als)
                          (t := (PUSH, Max (snd ` ops als) + 1)),
                        ops_modView_cli := (ops_modView_cli als)
                          ((PUSH, Max (snd ` ops als) + 1) :=
                             thrView acs t)\<rparr>) = ops_unmatched_push als \<union> {(PUSH, Max (snd ` ops als) + 1)}")
                apply simp
          apply(case_tac "top ps t = n_val ps t"; case_tac "lastNxtVal cls a = n_val ps t"; case_tac "a = n_val ps t"; simp)
          apply(intro allI impI conjI)
            apply(subgoal_tac "lib_value cls'
            (lib_lastWr cls' (Suc (n_val ps t))) = lib_value cls
            (lib_lastWr cls (Suc (n_val ps t)))", simp)
            apply(simp add: globals )
            apply (metis)
            apply (metis succ_CAS_preserves_last)
          apply(intro allI impI conjI)
            apply metis
            apply metis
                 apply(intro allI impI conjI)
  
                  apply (metis cvd_CAS_R_success_read_val lib_cvd_exist_last_write succ_CAS_preserves_last)
  apply(subgoal_tac "lib_value cls'
               (lib_lastWr cls' (Suc a)) = lib_value cls
               (lib_lastWr cls (Suc a))", simp)
  apply(simp add: globals)
                  apply metis
  apply (metis lastTop_def succ_CAS_preserves_last)
          apply (metis)
               apply(intro allI impI conjI)
                apply (metis succ_CAS_preserves_last)
  apply(subgoal_tac "lib_value cls'
               (lib_lastWr cls' (Suc (n_val ps t))) = lib_value cls
               (lib_lastWr cls (Suc (n_val ps t)))", elim exE conjE)
  apply simp

               apply(intro disjI1)
               apply(subgoal_tac "\<exists> a . a\<in>pushed_addr ps \<and> f a = (aa, b)")
                apply(elim exE conjE)
                apply(case_tac "ab = top ps t", simp_all)
                apply(case_tac "lastTop cls = Null")
  apply (metis Null_def TopLV_Null_pushed_empty  assms(11) assms(16) glb_def insert_Diff insert_not_empty)
                apply(subgoal_tac "top ps t = lastTop cls")
                 apply(subgoal_tac "f (prog_state.top ps t) = lastPush als")
                  apply simp
                    apply(subgoal_tac "aa = PUSH")
                  apply(subgoal_tac "(PUSH, b) \<noteq> lastPush als") 
                   apply(subgoal_tac "finite(ops_unmatched_push als)")
                     apply(simp add: lastPush_def getTs_def)
  apply(subgoal_tac "b \<in> snd `(ops_unmatched_push als)")  
  apply (metis finite_imageI image_constant image_is_empty  insert_not_empty member_less_max )
  apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def getTs_def)
  apply(subgoal_tac " b \<in> snd `
            ({opp. fst opp = PUSH \<and> opp \<in> ops als}) \<and>  b\<notin>
             snd` ({opp. fst opp = PUSH \<and> opp \<in> fst ` ops_matched als})")  
                      apply blast
  apply (intro conjI)
  apply (smt image_iff mem_Collect_eq snd_conv)
                     apply (smt image_iff mem_Collect_eq prod.collapse)
                    apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def getTs_def)
                    apply(unfold  ops_wfs_def ops_init_def getOp_def getTs_def)[1]
                    apply simp
  apply blast
                    apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def getTs_def)
  apply (metis)
                  apply (metis (no_types, lifting) assms(7) rr_def)
  apply (metis cvd_CAS_R_success_read_val lastTop_def lib_cvd_exist_last_write)

                apply (smt mem_Collect_eq rr_f_pushed_unmatched_def)
  apply (metis succ_CAS_preserves_last)
              apply(intro allI impI conjI, elim conjE)
              apply(case_tac "lastTop cls = Null", simp_all)
  apply(subgoal_tac "pushed_addr ps = {}", simp)
                apply(simp add: globals no_Top_n_def)
  
                apply (metis succ_CAS_preserves_last)
               apply (metis lastTop_def succ_CAS_preserves_last)
              apply(case_tac "a = lastTop cls")
               apply(elim conjE disjE, simp)
                apply(case_tac "lastNxtVal cls a = Null")
                 apply(intro disjI2)
                 apply(case_tac "ops_unmatched_push als = {}", simp_all)
                 apply(subgoal_tac " getTs (lastPush als) \<le> Max (snd ` ops als) ")
  apply(subgoal_tac "f (lastTop cls) = lastPush als")

                  apply(simp add: getTs_def  )
  apply (metis gr0I)
                 apply (meson lastPush_less_Max)
                 apply(intro disjI2)
                 apply(case_tac "ops_unmatched_push als = {}", simp_all)
                 apply(subgoal_tac " getTs (lastPush als) \<le> Max (snd ` ops als) ")
                 apply(simp add: getTs_def)
  apply(subgoal_tac "f (lastTop cls) = lastPush als", simp)
  apply (metis Null_def TopLV_Null_pushed_empty equals0D glb_def le0 nat_less_le)
                apply (meson lastPush_less_Max)
  
               apply (smt cvd_CAS_R_success_read_val succ_CAS_last_value succ_CAS_preserves_last)

                 apply(elim conjE disjE)
  apply(intro disjI2)
               apply(simp add: getTs_def)
               apply(subgoal_tac "f a \<in> ops als")
  apply(subgoal_tac "snd (f a) \<le> Max (snd ` ops als)")
                 apply linarith
                apply(unfold ops_wfs_def, simp)[1]
               apply(simp add: ops_unmatched_push_def ops_on_def)
  apply (smt cvd_CAS_R_success_read_val succ_CAS_last_value succ_CAS_preserves_last)

  apply(simp add: ops_unmatched_push_def)

             apply(simp add: ops_unmatched_push_def ops_mtch_push_def ops_on_def getOp_def getTs_def)
             apply clarify
  apply(subgoal_tac " {opp.
        fst opp = PUSH \<and>
        (opp = (PUSH, Max (snd ` ops als) + 1) \<or> opp \<in> ops als)} =  {opp.
        fst opp = PUSH \<and>
        (opp \<in> ops als)} \<union>  {(PUSH, Max (snd ` ops als) + 1)}")        
              apply simp
             apply(subgoal_tac "{opp. fst opp = PUSH \<and> opp \<in> fst ` ops_matched als} \<subseteq> {opp. fst opp = PUSH \<and> opp \<in> ops als}")
  apply(subgoal_tac "(PUSH, Max (snd ` ops als) + 1) \<notin> {opp. fst opp = PUSH \<and> opp \<in> ops als}")
  
                apply (meson insert_Diff_if subsetD)
               apply clarsimp
  apply(subgoal_tac "Max (snd ` ops als) + 1 \<notin> snd `ops als")
                apply (metis (no_types, lifting) image_iff snd_conv)
  apply(subgoal_tac "finite (snd ` ops als)")
  apply (metis Max_ge add.commute add_le_same_cancel2 not_one_le_zero)
               apply(unfold ops_wfs_def getOp_def getTs_def ops_init_def)[1]
  apply simp
               apply(unfold ops_wfs_def getOp_def getTs_def ops_init_def)[1]
  apply simp
              apply (metis (no_types, lifting) Collect_mono subset_eq)
  using new_element_in_set_comp
  using Collect_mem_eq apply auto[1]
            apply(elim disjE, simp_all)
             apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def)
             apply(unfold ops_wfs_def, simp)[1]
  apply(subgoal_tac "(PUSH, Max (snd ` ops als) + 1) \<notin> ops als")
              apply (meson subset_iff)
  apply(subgoal_tac " Max (snd ` ops als) + 1 \<notin> snd` (ops als)")
              apply (metis Pair_inject prod.collapse rev_image_eqI)
             apply(subgoal_tac "finite(snd ` ops als)")
              apply(metis Max.coboundedI less_add_one less_le_not_le)
             apply (metis finite_imageI)
            apply(case_tac "a = n_val ps t", simp_all)
            apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def lastTop_def no_Top_n_def)
  apply(subgoal_tac "lib_value cls' (lib_lastWr cls' (Suc a)) = lib_value cls (lib_lastWr cls (Suc a))", simp add: globals)
            apply (metis cvd_CAS_R_success_read_val gr0I lib_cvd_exist_last_write)
  apply (metis lastTop_def succ_CAS_preserves_last)
          apply(elim disjE)
           apply(subgoal_tac "lib_value cls' (lib_lastWr cls' Top) = n_val ps t", simp_all)
  apply(intro impI conjI)
              apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def)
             apply(subgoal_tac " Max (snd ` ops als) + 1 \<notin> snd` (ops als)")
              apply(unfold ops_wfs_def, simp)[1]
  apply (metis (no_types, lifting) Pair_inject in_mono prod.collapse rev_image_eqI)
             apply(subgoal_tac "finite(snd ` ops als)")
              apply(metis Max.coboundedI less_add_one less_le_not_le)
              apply(unfold ops_wfs_def, simp)[1]
            defer (*easy but time consuming*)
            apply(subgoal_tac "[lib(Top) =\<^sub>t (n_val ps t)] cls'")
                apply(simp add: lib_d_obs_t_def lib_d_obs_def)
  apply (simp add: lastTop_def)
  using cvd_CAS_R_success_d_obs_post apply blast
              apply (simp add: lastTop_def)
  apply (simp add: lastTop_def)
  apply (metis cvd_CAS_R_success_read_val succ_CAS_last_value)

  apply(intro impI conjI)
  apply blast
  apply blast
            apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def)
            apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def)
  apply(unfold ops_wfs_def, simp)[1]
                  apply(subgoal_tac "(PUSH, Max (snd ` ops als) + 1) \<notin> ops als")
              apply (meson subset_iff)
  apply(subgoal_tac " Max (snd ` ops als) + 1 \<notin> snd` (ops als)")
              apply (metis Pair_inject prod.collapse rev_image_eqI)
             apply(subgoal_tac "finite(snd ` ops als)")
              apply(metis Max.coboundedI less_add_one less_le_not_le)
                  apply (metis finite_imageI)
            defer (*easy but time consuming*)
  apply blast
  apply blast
  apply blast
            apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def)
             apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def)
             apply(intro conjI impI)
  apply (metis cvd_CAS_R_success_read_val lastTop_def succ_CAS_last_value)
  apply(intro disjI1)
            apply(subgoal_tac "[lib(Top) =\<^sub>t (n_val ps t)] cls'")
               apply(simp add: lib_d_obs_t_def lib_d_obs_def)
  apply (simp add: lastTop_def)
  using cvd_CAS_R_success_d_obs_post apply blast
  apply (metis cvd_CAS_R_success_read_val lastTop_def succ_CAS_last_value)
            apply(subgoal_tac "[lib(Top) =\<^sub>t (n_val ps t)] cls'")
             apply(simp add: lib_d_obs_t_def lib_d_obs_def)
  
  apply (simp add: lastTop_def)

  using cvd_CAS_R_success_d_obs_post apply blast
  apply(intro conjI impI)
            apply(simp add: op_value_def)
            apply(subgoal_tac " [libn_val ps t =\<^sub>t v] cls'")
  apply(simp add: lib_d_obs_t_def lib_d_obs_def)  
            apply (metis d_obs_CAS_R_diff_var)
  apply(elim disjE)
            apply blast
           apply(simp add: op_value_def)
  apply(intro impI conjI)
            apply(subgoal_tac "f a \<in> ops als")
  apply(subgoal_tac "(PUSH, Max (snd ` ops als) + 1)\<notin>ops als ")
              apply auto[1]
  apply(unfold ops_wfs_def, simp)[1]
    apply(subgoal_tac " Max (snd ` ops als) + 1\<notin>snd`(ops als)")  
  apply (metis imageI snd_conv)
  apply(subgoal_tac "finite(snd ` ops als)")
apply(metis Max.coboundedI less_add_one less_le_not_le)
                  apply (metis finite_imageI)
            apply (meson in_mono ops_unmatched_push_subset_ops)
           apply(subgoal_tac "a \<noteq> Top")
            apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
            apply(case_tac "lib_value cls (aa, b) = prog_state.top ps t", simp_all)
  apply(simp add: var_def tst_def lib_update_r_def all_updates_l lib_value_def lib_lastWr_def lib_writes_on_def)
  apply (smt Collect_cong a_is_x fst_conv)
           apply(simp add: globals)
  apply auto[1]
          apply(elim disjE)
           apply(simp add: globals)
  
  apply (metis cvd_CAS_R_success_read_val succ_CAS_last_value succ_CAS_preserves_last)
  apply(simp add: globals)
  apply (smt cvd_CAS_R_success_read_val succ_CAS_last_value succ_CAS_preserves_last)
         apply(intro allI impI conjI)
  apply(subgoal_tac "f a2 \<in> ops als")
  apply(subgoal_tac "(PUSH, Max (snd ` ops als) + 1)\<notin>ops als ")
              apply auto[1]
  apply(unfold ops_wfs_def, simp)[1]
           apply(subgoal_tac " Max (snd ` ops als) + 1\<notin>snd`(ops als)")  
  apply (metis imageI old.prod.inject prod.collapse)
  apply(subgoal_tac "finite(snd ` ops als)")
apply(metis Max.coboundedI less_add_one less_le_not_le)
                  apply (metis finite_imageI)  
          apply (meson in_mono ops_unmatched_push_subset_ops)

          apply(subgoal_tac "f a1 \<in> ops als")
  apply(subgoal_tac "(PUSH, Max (snd ` ops als) + 1)\<notin>ops als ")
              apply auto[1]
  apply(unfold ops_wfs_def, simp)[1]
           apply(subgoal_tac " Max (snd ` ops als) + 1\<notin>snd`(ops als)")  
  apply (metis imageI old.prod.inject prod.collapse)
  apply(subgoal_tac "finite(snd ` ops als)")
apply(metis Max.coboundedI less_add_one less_le_not_le)
                  apply (metis finite_imageI)  
         apply (meson in_mono ops_unmatched_push_subset_ops)
  apply(intro allI impI conjI)
         apply auto[1]
        apply(elim conjE exE)
        apply(simp add: ops_init_def)
       apply(simp add: rr_cliV_def)
       apply(intro allI impI conjI)
         apply(subgoal_tac "a = Top", simp)
          apply(simp add: lib_CAS_Rel_step_def, elim conjE exE)
          apply(case_tac "lib_value cls (aa, ba) = prog_state.top ps t", simp_all)
          apply(simp add:lib_update_r_def all_updates_l)
  apply(intro impI conjI)
  using ref_client_thrView_def apply blast
         apply(subgoal_tac "aa = Top", simp)
  apply(simp add: globals lib_value_def lib_writes_on_def no_Top_n_def)
  using a_is_x apply blast
         apply(simp add: globals lib_value_def lib_writes_on_def no_Top_n_def)
  apply(elim conjE exE)
        apply(subgoal_tac "(a, b) \<in> lib_writes_on cls Top")
         apply(subgoal_tac "lib_value cls' (a,b) = lib_value cls (a,b)", simp)
          apply(simp add: rr_def, elim conjE)
          apply(subgoal_tac "getTs (f (lib_value cls (a, b))) \<le> Max (snd` ops als)")
           apply(simp add: getTs_def)
  apply(subgoal_tac "f (lib_value cls (a, b)) \<in> ops als")
    apply (simp add: a_in_ops_less_eq_Max)
          apply (metis in_mono ops_unmatched_push_subset_ops)
         apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
         apply(case_tac "lib_value cls (aa, ba) = prog_state.top ps t", simp_all)
  apply(simp add: lib_update_r_def all_updates_l lib_value_def)
         apply auto[1]
         apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
         apply(case_tac "lib_value cls (aa, ba) = prog_state.top ps t", simp_all)
  apply(simp add: lib_update_r_def all_updates_l lib_value_def lib_writes_on_def)
        apply auto[1]
        apply(subgoal_tac "(a, b) \<in> lib_writes_on cls Top")
         apply(subgoal_tac "lib_value cls' (a,b) = lib_value cls (a,b)", simp)
         apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
         apply(case_tac "lib_value cls (aa, ba) = prog_state.top ps t", simp_all)
  apply(simp add: lib_update_r_def all_updates_l lib_value_def)
  apply auto[1]
         apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
         apply(case_tac "lib_value cls (aa, ba) = prog_state.top ps t", simp_all)
  apply(simp add: lib_update_r_def all_updates_l lib_value_def)
  apply auto[1]
         apply(simp add: lib_CAS_Rel_step_def, elim exE conjE)
         apply(case_tac "lib_value cls (aa, ba) = prog_state.top ps t", simp_all)
       apply(simp add: lib_update_r_def all_updates_l lib_value_def)
         apply(simp add: globals lib_value_def lib_writes_on_def no_Top_n_def)
       apply auto[1]
      apply(simp add: rr_cliV_thView_def ref_client_thrView_def, elim exE conjE)
      apply(intro allI impI conjI)
  apply(simp add: lib_CAS_Rel_step_def, elim conjE exE)
        apply(case_tac "lib_value cls (a, b) = prog_state.top ps t", simp_all)
  apply(simp add: lib_update_r_def all_updates_l)
  apply(simp add: lib_CAS_Rel_step_def, elim conjE exE)
        apply(case_tac "lib_value cls (a, b) = prog_state.top ps t", simp_all)
       apply(simp add: lib_update_r_def all_updates_l)
  apply(simp add: lib_CAS_Rel_step_def, elim conjE exE)
        apply(case_tac "lib_value cls (a, b) = prog_state.top ps t", simp_all)
      apply(simp add: lib_update_r_def all_updates_l)
     apply(simp add: ref_client_thrView_def)
  apply(simp add: lib_CAS_Rel_step_def, elim conjE exE)
        apply(case_tac "lib_value cls (a, b) = prog_state.top ps t", simp_all)
     apply(simp add: lib_update_r_def all_updates_l)
    apply(simp add: rr_f_pushed_unmatched_def ops_unmatched_push_def ops_on_def ops_mtch_push_def getOp_def)
  apply safe  
             apply blast
  apply (smt DiffI mem_Collect_eq)  
  apply (smt DiffI mem_Collect_eq)  
  apply (smt DiffI mem_Collect_eq)  
  apply blast
  apply blast  
  apply simp
                   apply blast
  apply auto[1]
                 apply blast
  apply blast
  apply blast
  apply blast
  
             apply auto[1]
  apply blast
   apply blast
            apply(subgoal_tac "(PUSH, Max (snd ` ops als) + 1) \<in> ops als")
  apply(subgoal_tac " Max (snd ` ops als) + 1 \<notin> snd `ops als")
  using image_iff apply fastforce
  apply(subgoal_tac "finite(snd `ops als)")
  apply (metis Max.coboundedI less_add_one less_le_not_le)
  apply(unfold  ops_wfs_def, simp)[1]
  apply(unfold  ops_wfs_def, simp)[1]
  apply (metis (no_types, lifting) Pair_inject image_insert insert_iff mk_disjoint_insert prod.collapse subsetD)
         apply blast
   
  apply blast
       apply simp
       defer
  apply blast
  apply(simp add: lastPush_def)
   apply(simp add:  ops_unmatched_push' )
  using Max_insert_Max_plus_one   

   apply metis
  apply(simp add: lastPush_def)
   apply(simp add:  ops_unmatched_push' )
  using Max_insert_Max_plus_one
     apply metis
  apply(simp add: lastPush_def)
   apply(simp add:  ops_unmatched_push' )
  using Max_insert_Max_plus_one
    apply metis
    apply(simp add: lastPush_def)
   apply(simp add:  ops_unmatched_push' )
  using Max_insert_Max_plus_one
   apply metis
  apply(unfold ops_wfs_def)
  apply(subgoal_tac "(PUSH, ba)\<notin>ops als")
   defer
   apply(simp add: getOp_def ops_init_def getTs_def)
  apply(subgoal_tac "Max (snd ` ops als) + 1 \<notin> snd `(ops als)")
    apply (metis image_eqI old.prod.inject prod.collapse)
  apply (meson Max.coboundedI finite_imageI less_add_one not_less)
  apply(simp add: getOp_def ops_init_def getTs_def)
  apply(elim conjE)
  apply safe
  apply(subgoal_tac "(PUSH, Max (snd ` ops als) + 1) \<in> fst ` ops_matched als")
   apply (meson subset_iff)
    by (metis fst_conv rev_image_eqI)


lemma " finite (A::rat set) \<Longrightarrow> (Max A) + 1 \<notin> A"
    by (meson Max.coboundedI less_add_one less_le_not_le)
end
