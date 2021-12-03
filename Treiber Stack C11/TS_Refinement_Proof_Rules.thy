theory TS_Refinement_Proof_Rules
imports  TS_Proof_Rules
begin

lemma exists_ops_vts_push: "ops_wfs s c \<Longrightarrow> \<exists>ts'. ops_vts_push t ts' s"
  apply(simp add: ops_vts_push_def getTs_def)
  apply(case_tac "ops s = {}")
   apply simp
  apply(case_tac "ops_matched s = {}", simp_all)
    apply (simp add: gt_ex)
  apply(unfold ops_wfs_def)[1]
   apply simp
  apply(case_tac "ops_matched s = {}", simp_all)
   apply(rule_tac x = "Max(snd ` ops s) + 1" in exI)
   apply(unfold ops_wfs_def)[1]
  apply(intro conjI, elim conjE, simp_all)  
  apply (metis (no_types, lifting) add.commute finite_imageI image_eqI image_is_empty less_add_one member_less_max pos_add_strict zero_less_one)
   apply (metis Max_less_iff equals0D finite_imageI infinite_growing less_add_same_cancel1 zero_less_double_add_iff_zero_less_single_add zero_less_two)
  apply(subgoal_tac "snd` ops_matched s \<subseteq> ops s")
   apply(subgoal_tac "fst` ops_matched s \<subseteq> ops s")
    defer
   apply(unfold ops_wfs_def)[1]
  apply linarith
   apply(unfold ops_wfs_def)[1]
   apply linarith
  apply(rule_tac x = "Max (snd `(ops s)) +1" in exI)
  apply(intro allI impI conjI)
    apply(unfold ops_wfs_def getTs_def getOp_def ops_init_def, simp)[1]
  apply(subgoal_tac "finite(snd ` ops s)")
  apply (simp add: add.commute add_strict_increasing)
    apply simp
   apply(subgoal_tac "finite(snd ` ops s)")
  apply(subgoal_tac "Max (snd ` ops s) + 1 > Max (snd ` ops s)")
  using Max_less_iff apply blast
  using less_add_one apply blast
    apply(unfold ops_wfs_def getTs_def getOp_def ops_init_def, simp)[1]
  apply(unfold ops_wfs_def getTs_def getOp_def ops_init_def, simp)[1]
  apply(subgoal_tac "ba \<le> Max (snd ` ops s)")
   apply linarith
  apply simp
  by (metis Max.coboundedI finite_imageI image_iff image_subset_iff prod.exhaust_sel snd_eqD)


lemma exist_ops_vts_pop: "ops_wfs s c \<Longrightarrow> \<exists> ts'. ops_vts_pop t ts' s"
  apply(simp add: ops_vts_pop_def ops_init_matched_pairs_def getTs_def)
  apply(case_tac "ops s = {}")
  apply simp
  apply(case_tac "ops_matched s = {}", simp_all)
    apply (simp add: gt_ex)
  apply(unfold ops_wfs_def)[1]
   apply simp
   apply(rule_tac x = "Max(snd ` ops s) + 1" in exI)
    apply(unfold ops_wfs_def, simp_all)[1]
 apply (intro conjI)
  apply (simp add: add.commute add_strict_increasing)
   apply (metis Max_less_iff equals0D finite_imageI infinite_growing less_add_same_cancel1 zero_less_double_add_iff_zero_less_single_add zero_less_two)  
  apply(intro allI conjI impI)
  apply(elim conjE, intro disjI2)
  apply(subgoal_tac " (aa, ba) \<in> ops s") defer
   apply (metis imageI old.prod.inject prod.collapse subset_iff)
  apply(simp add: getTs_def getOp_def ops_init_def)
  by (metis Max.coboundedI add.commute add_strict_increasing finite_imageI image_iff snd_eqD zero_less_one)

(*****************************************)

definition "ref_client_thrView t ac cc \<equiv> \<forall> x . tst (thrView ac t x) \<le> tst (thrView cc t x) "

definition "ref_Top ss ls \<equiv> \<forall> w . lib_lastWr ls Top = w \<and> lib_value ls w \<noteq> Null \<longrightarrow>
           (\<exists> op . op\<notin>fst`(ops_matched ss) \<and> getOp op = PUSH \<and> op\<in>ops ss 
                  \<and> op_value op ss = lib_value ls (lib_lastWr ls (lib_value ls w)))"


definition "ref_addr_push f als cls ps \<equiv> \<forall> ad . ad\<in>addr ps \<longrightarrow>
           (\<exists> op . op\<in>ops als \<and> getOp op = PUSH \<and> f ad = op \<and> lib_value cls (lib_lastWr cls ad) = op_value op als)"


definition "refs t f ps als cls acs ccs \<equiv> ref_client_thrView t acs ccs \<and> ref_addr_push f als cls ps"

lemmas [simp] = refs_def

lemma "f a = b \<Longrightarrow> c\<notin>dom f \<Longrightarrow> f' = f(c:=d) \<Longrightarrow> f' c = d"
  by simp

(*
ps  = program state
ccs = concrete client state
acs = abstract client state
ccl = concrete stack library state
als = abstract stack library state
*)

lemma lib_last_in_writes_on: "lib_wfs cls ccs \<Longrightarrow> lib_writes_on cls x \<noteq> {} \<Longrightarrow> lib_lastWr cls x \<in> lib_writes_on cls x"
  apply(simp add: lib_wfs_def lib_writes_on_def lib_lastWr_def tst_def var_def)
  apply(subgoal_tac "finite(snd ` {w. fst w = x \<and> w \<in> lib_writes cls})")
   apply safe
  defer
   apply blast
  apply(subgoal_tac " Max (snd ` {w. fst w = x \<and> w \<in> lib_writes cls}) \<in>  (snd ` {w. fst w = x \<and> w \<in> lib_writes cls})")
  apply (simp add: image_iff)
  using Max_in by blast
  
lemma ops_vts_push_max: "ops_wfs als acs \<Longrightarrow> ops_vts_push t (Max (snd ` ops als) + 1) als"
  apply(simp add: ops_vts_push_def getTs_def getOp_def)
  apply (intro conjI)
    apply(unfold ops_wfs_def ops_init_def getOp_def getTs_def)[1]
  apply simp
    apply (simp add: add.commute add_strict_increasing)
    apply(unfold ops_wfs_def ops_init_def getOp_def getTs_def)[1]
  apply simp
    apply (simp add: add.commute add_strict_increasing)  
  apply (meson Max.coboundedI add_le_same_cancel2 finite_imageI not_one_le_zero)
    apply(unfold ops_wfs_def ops_init_def getOp_def getTs_def lastOp_def)[1]
  apply simp
  apply (simp add: add.commute add_strict_increasing )  
  apply(intro allI impI conjI, elim conjE exE)
  apply(intro disjI2)
  apply clarsimp
  by (metis Max.coboundedI add_strict_increasing finite_imageI image_eqI image_subset_iff snd_conv zero_less_one)

lemma ops_vts_pop_max: "ops_wfs als acs \<Longrightarrow> ops_vts_pop t (Max (snd ` ops als) + 1) als"
  apply(simp add: ops_vts_pop_def getTs_def getOp_def)
  apply (intro conjI)
    apply(unfold ops_wfs_def ops_init_def)[1]
  apply simp
    apply (simp add: add.commute add_strict_increasing)
    apply(unfold ops_wfs_def ops_init_def)[1]
  apply (simp add: getOp_def getTs_def)
  apply (metis (mono_tags, hide_lams) Max_ge add_le_same_cancel1 finite_imageI  not_one_le_zero)
  apply(intro conjI allI impI disjI2)
  apply(unfold ops_wfs_def ops_init_def)[1]
  apply (simp add: getOp_def getTs_def ops_init_matched_pairs_def)
  apply(elim conjE, simp)
  apply(subgoal_tac "(aa, ba)\<in> ops als") defer
  apply (metis (mono_tags, hide_lams) fst_conv imageI snd_eqD subset_iff subset_refl)
  by (metis Max_ge add.commute add_strict_increasing finite_imageI image_iff snd_eqD zero_less_one)

lemma lastUnmatchedPush_max: "ops_wfs als acs \<Longrightarrow> ops_unmatched_push als \<noteq> {} \<Longrightarrow> lastUnmatchedPush (Max (snd ` ops als) + 1)
        (PUSH, Max (snd ` ops_unmatched_push als)) als"
  apply(simp add: lastUnmatchedPush_def ops_umatched_upto_ts_def)
  apply(intro conjI)
    apply(intro disjI1)
    apply(subgoal_tac "fst` ops_unmatched_push als = {PUSH}")
  defer
     apply(simp add: ops_unmatched_push_def)
     apply(simp add: ops_on_def ops_mtch_push_def getOp_def) 
  apply blast
    defer defer
    apply(subgoal_tac "finite (ops_unmatched_push als)")
  apply (metis Domain.DomainI Domain_fst Max_in RangeE Range_snd empty_is_image finite_imageI  singletonD)
  apply(unfold ops_wfs_def ops_init_def)[1]
    apply (simp add: getOp_def getTs_def ops_init_matched_pairs_def)
  apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def)
   apply(simp_all add: getTs_def)
  apply(subgoal_tac "ops_unmatched_push als \<subseteq> ops als")
    apply(subgoal_tac "finite (ops_unmatched_push als)")
    apply(subgoal_tac "finite (ops als)")
  apply (smt Max_less_iff empty_is_image finite_imageI image_iff less_add_one subset_empty subset_iff)
   apply(unfold ops_wfs_def ops_init_def)[1]
  apply blast
  apply(unfold ops_wfs_def ops_init_def)[1]
    apply (simp add: getOp_def getTs_def ops_init_matched_pairs_def)
    apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def)
    apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def)
   apply blast
 
  apply(subgoal_tac "Max (snd `
         {opp.
          (opp \<in> ops_unmatched_push als \<or> opp \<in> ops_init als) \<and> snd opp < Max (snd ` ops als) + 1}) \<in> snd ` ops_init als \<union> snd ` ops_unmatched_push als") 
   defer
  apply(subgoal_tac " {opp.
          (opp \<in> ops_unmatched_push als \<or> opp \<in> ops_init als) \<and> snd opp < Max (snd ` ops als) + 1} \<noteq> {}")
  apply(subgoal_tac "finite({opp.
          (opp \<in> ops_unmatched_push als \<or> opp \<in> ops_init als) \<and> snd opp < Max (snd ` ops als) + 1})")
  apply (smt Max_in UnI1 UnI2 empty_is_image finite_imageI image_iff mem_Collect_eq)
    apply(unfold ops_wfs_def ops_init_def)[1]
  apply(simp add: ops_unmatched_push_def getOp_def ops_on_def)
     apply(unfold ops_wfs_def ops_init_def)[1]
  apply(simp add: ops_unmatched_push_def getOp_def ops_on_def ops_mtch_push_def)
  apply (metis (no_types, lifting)  Max.coboundedI add.commute add_strict_increasing finite_imageI  imageI image_cong snd_eqD surj_pair zero_less_one)
  apply(case_tac "Max (snd `
         {opp.
          (opp \<in> ops_unmatched_push als \<or> opp \<in> ops_init als) \<and> snd opp < Max (snd ` ops als) + 1})
    \<in> snd ` ops_init als")
   apply(subgoal_tac "\<exists> op . op\<in>ops_unmatched_push als")
    apply (elim exE)
  apply(subgoal_tac "op\<in>{opp.
                (opp \<in> ops_unmatched_push als \<or> opp \<in> ops_init als) \<and>
                snd opp < Max (snd ` ops als) + 1}")
     apply(subgoal_tac "getOp op = PUSH")
  defer
  apply(simp add: getOp_def ops_unmatched_push_def ops_on_def)
  apply(simp add: getOp_def ops_unmatched_push_def ops_on_def ops_mtch_push_def)
     apply(unfold ops_wfs_def ops_init_def)[1]
     apply(simp add: ops_unmatched_push_def getOp_def ops_on_def ops_mtch_push_def)
  apply (metis (no_types, lifting) Max_ge add.commute add_strict_increasing finite_imageI imageI old.prod.exhaust snd_conv zero_less_one)
  apply blast
   defer
   apply simp
  apply(subgoal_tac "op\<in>{opp.
                (opp \<in> ops_unmatched_push als \<or> opp \<in> ops_init als) \<and>
                snd opp < Max (snd ` ops als) + 1}")
    apply(subgoal_tac "\<forall> ts . ts \<in> snd ` ops_init als \<longrightarrow> getTs op > ts")
     defer
     apply(intro allI impI)
  apply(simp add: getTs_def)
     apply(unfold ops_wfs_def ops_init_def)[1]
     apply(simp add: getTs_def getOp_def)
  apply(elim conjE exE)
     apply(simp add: ops_unmatched_push_def getOp_def ops_on_def ops_mtch_push_def)
  apply (smt OP.distinct(1) imageE mem_Collect_eq prod.collapse)
  apply blast
   defer
   apply(subgoal_tac "\<forall> opp . opp\<in>ops_init als \<longrightarrow> getTs opp < getTs op")
  defer
  using getTs_def apply blast
  defer   
  apply(subgoal_tac "\<forall> oppp opinit. oppp\<in>{opp.
                (opp \<in> ops_unmatched_push als \<or> opp \<in> ops_init als) \<and>
                snd opp < Max (snd ` ops als) + 1} \<and> opinit\<in>ops_init als \<longrightarrow> getTs oppp \<le> getTs opinit")
    apply (simp add: leD)
   apply(intro allI impI)
   apply(simp add: ops_init_def)
  apply(subgoal_tac "finite({opp.
             (opp \<in> ops_unmatched_push als \<or> getOp opp = INIT \<and> opp \<in> ops als) \<and>
             snd opp < Max (snd ` ops als) + 1})")
  apply(subgoal_tac "{opp.
             (opp \<in> ops_unmatched_push als \<or> getOp opp = INIT \<and> opp \<in> ops als) \<and>
             snd opp < Max (snd ` ops als) + 1} \<noteq> {}")
    apply (metis (mono_tags, lifting) Max_less_iff finite_imageI getTs_def imageI image_is_empty infinite_growing mem_Collect_eq)
    apply blast
     apply(unfold ops_wfs_def ops_init_def)[1]
   apply(simp add: getTs_def getOp_def)

 apply(simp add: getTs_def ops_unmatched_push_def getOp_def ops_on_def ops_mtch_push_def)
  apply simp
  apply(subgoal_tac "ops_unmatched_push als \<subseteq> ops als") defer
 apply(simp add: getTs_def ops_unmatched_push_def getOp_def ops_on_def ops_mtch_push_def)
  apply blast
  apply(subgoal_tac "ops_init als \<subseteq> ops als") defer
 apply(simp add: ops_init_def  getTs_def ops_unmatched_push_def getOp_def ops_on_def ops_mtch_push_def)
   apply blast
  apply(subgoal_tac "{opp. (opp \<in> ops_unmatched_push als \<or> opp \<in> ops_init als) \<and> snd opp < Max (snd ` ops als) + 1} = {opp. (opp \<in> ops_unmatched_push als \<or> opp \<in> ops_init als)}")
   defer
   apply(subgoal_tac " Max (snd ` ops als) + 1 >  Max (snd ` ops als)") 
  apply(subgoal_tac "\<forall> opp . opp \<in> ops_unmatched_push als \<or> opp \<in> ops_init als \<longrightarrow> getTs opp < Max (snd ` ops als) + 1")
     apply (metis getTs_def)
    apply(intro allI impI)
    apply(simp add: getTs_def)
    apply(elim disjE)
  apply(subgoal_tac "\<forall> opp . opp \<in> ops_unmatched_push als \<longrightarrow> getTs opp \<le> Max (snd ` ops als) ")
apply (metis add.commute getTs_def le_less_trans less_add_one)
     apply(intro allI impI)
  apply(unfold ops_wfs_def)[1]
  apply simp
  apply (metis Max.coboundedI finite_imageI getTs_def imageI subset_iff)
  apply(unfold ops_wfs_def)[1]
  apply simp
  apply (metis (no_types, lifting) Max.coboundedI add.commute add_strict_increasing finite_imageI getOp_def imageI mem_Collect_eq old.prod.exhaust old.prod.inject ops_init_def prod.collapse snd_conv  zero_less_one)
  apply linarith
  apply simp
  apply(subgoal_tac "finite(snd ` {opp. opp \<in> ops_unmatched_push als \<or> opp \<in> ops_init als})")
  apply(subgoal_tac "finite(snd ` ops_unmatched_push als)")
  apply (smt Max.coboundedI Max_eq_if image_iff mem_Collect_eq)
 apply(simp add: ops_init_def  getTs_def ops_unmatched_push_def getOp_def ops_on_def ops_mtch_push_def)
   apply(unfold ops_wfs_def)[1]
  apply simp
 apply(simp add: ops_init_def  getTs_def ops_unmatched_push_def getOp_def ops_on_def ops_mtch_push_def)
   apply(unfold ops_wfs_def)[1]
  apply simp
  done

lemma lastUnmatchedPush_lastPush: "ops_wfs als acs \<Longrightarrow> op = lastPush als \<Longrightarrow> op \<in> ops als \<Longrightarrow> op \<notin> fst ` ops_matched als  \<Longrightarrow> lastUnmatchedPush (Max (snd ` ops als) + 1) op als"
  apply(simp add:lastUnmatchedPush_def)
  apply safe
   apply(simp add: ops_umatched_upto_ts_def lastPush_def ops_unmatched_push_def)
   apply safe
     apply (simp add: getOp_def ops_on_def)
  using ops_mtch_push_def apply auto[1]
   apply (simp add: getOp_def ops_on_def ops_mtch_push_def getTs_def)
  apply(subgoal_tac "{opp. fst opp = PUSH \<and> opp \<in> ops als} -
          {opp. fst opp = PUSH \<and> opp \<in> fst ` ops_matched als} \<subseteq> ops als")
  apply(subgoal_tac " Max (snd `
         ({opp. fst opp = PUSH \<and> opp \<in> ops als} -
          {opp. fst opp = PUSH \<and> opp \<in> fst ` ops_matched als}))
    \<le> Max (snd ` ops als)")
  apply linarith
    defer
    apply blast defer
   apply(unfold ops_wfs_def getOp_def, simp)[1]
  apply(subgoal_tac "{opp. fst opp = PUSH \<and> opp \<in> ops als} -
          {opp. fst opp = PUSH \<and> opp \<in> fst ` ops_matched als} \<noteq> {}")  
  apply (meson Max_mono finite_imageI image_is_empty image_mono)
  apply (metis (mono_tags, lifting) Collect_mono_iff Diff_eq_empty_iff fst_conv image_is_empty)
  apply(simp add: ops_umatched_upto_ts_def lastPush_def getTs_def)
  apply(subgoal_tac "{opp.
          (opp \<in> ops_unmatched_push als \<or> opp \<in> ops_init als) \<and>
          snd opp < Max (snd ` ops als) + 1} = ops_unmatched_push als \<union> ops_init als")
   defer
  apply(simp add: ops_unmatched_push_def ops_mtch_push_def ops_init_def ops_on_def getOp_def)
   apply safe
     apply blast
    apply clarsimp
    defer
  apply(subgoal_tac "snd (a, b) \<le> Max (snd ` ops als)")
  apply linarith
    apply(unfold ops_wfs_def getOp_def ops_init_def getTs_def, simp)[1]
  apply (simp add: rev_image_eqI)
   apply simp
   defer
  apply(subgoal_tac "b \<le> Max (snd ` ops als)")
    apply(unfold ops_wfs_def getOp_def ops_init_def getTs_def, simp)[1]
   apply(case_tac "b \<in> snd ` ops als")
  apply(subgoal_tac "finite(snd ` ops als)")
  using Max_ge apply blast
    apply(unfold ops_wfs_def getOp_def ops_init_def getTs_def, simp)[1]
   apply (simp add: rev_image_eqI)
  apply(subgoal_tac "Max (snd ` (ops_unmatched_push als \<union> ops_init als)) = Max (snd ` (ops_unmatched_push als))")
   apply linarith
  apply(subgoal_tac "Max (snd ` (ops_unmatched_push als \<union> ops_init als)) = Max (snd ` (ops_unmatched_push als)) \<or> Max (snd ` (ops_unmatched_push als \<union> ops_init als)) = Max (snd ` ( ops_init als))")
   apply(subgoal_tac "\<forall> op1 op2. op1\<in>snd `(ops_unmatched_push als) \<and> op2\<in>snd `(ops_init als) \<longrightarrow> op1 > op2")
    apply(subgoal_tac "finite(ops_init als)")
     apply(subgoal_tac "finite(ops_unmatched_push als)")
      apply(subgoal_tac "ops_init als \<noteq> {} \<and> ops_unmatched_push als \<noteq> {}")
  apply(elim conjE)
       apply (smt Max_in Un_empty Un_iff finite_UnI finite_imageI image_Un image_is_empty member_less_max not_max)
  apply(intro conjI)
    apply(unfold ops_wfs_def getOp_def ops_init_def getTs_def, simp)[1]
   apply auto[1]
       apply(unfold ops_wfs_def getOp_def ops_init_def getTs_def ops_unmatched_push_def ops_on_def ops_mtch_push_def, simp)[1]
  apply (simp add: Collect_mono_iff)
    apply(unfold ops_wfs_def getOp_def ops_init_def getTs_def ops_unmatched_push_def ops_on_def ops_mtch_push_def, simp)[1]
  apply (simp add: Collect_mono_iff)
    apply(unfold ops_wfs_def getOp_def ops_init_def getTs_def ops_init_def ops_unmatched_push_def ops_on_def ops_mtch_push_def, simp)[1]
    apply(unfold ops_wfs_def getOp_def ops_init_def getTs_def ops_init_def ops_unmatched_push_def ops_on_def ops_mtch_push_def, simp)[1]
  apply(intro allI impI conjI)
    apply(unfold ops_wfs_def getOp_def ops_init_def getTs_def ops_init_def ops_unmatched_push_def ops_on_def ops_mtch_push_def, simp)[1]
  apply (smt OP.distinct(1) image_iff mem_Collect_eq prod.collapse set_diff_eq)
   apply(intro disjI1)
    apply(subgoal_tac "finite(ops_init als)")
   apply(subgoal_tac "finite(ops_unmatched_push als)")
  apply(subgoal_tac "ops_unmatched_push als \<noteq> {}")
   apply(subgoal_tac "\<forall> op1 op2. op1\<in>snd `(ops_unmatched_push als) \<and> op2\<in>snd `(ops_init als) \<longrightarrow> op1 > op2")
  apply (smt Max_in Un_empty Un_iff finite_UnI finite_imageI image_Un image_is_empty member_less_max not_max)
     apply(intro allI impI)
    apply(unfold ops_wfs_def getOp_def ops_init_def getTs_def ops_init_def ops_unmatched_push_def ops_on_def ops_mtch_push_def, simp)[1]
  apply (smt OP.distinct(1) image_iff mem_Collect_eq prod.collapse set_diff_eq)
    apply(unfold ops_wfs_def getOp_def ops_init_def getTs_def ops_init_def ops_unmatched_push_def ops_on_def ops_mtch_push_def, simp)[1] 
  apply (metis (mono_tags, lifting) Collect_mono_iff fst_conv)
    apply(unfold ops_wfs_def getOp_def ops_init_def getTs_def ops_init_def ops_unmatched_push_def ops_on_def ops_mtch_push_def, simp)[1]
    apply(unfold ops_wfs_def getOp_def ops_init_def getTs_def ops_init_def ops_unmatched_push_def ops_on_def ops_mtch_push_def, simp)[1]
  done



definition "cli_lib_mView cls w \<equiv>   ((lib_modView cls) w) Lib.CVARS"
definition "cli_stack_mView als op \<equiv>   ((ops_modView_cli als) op)"


lemmas shorthands [simp] = TopL_def  cli_lib_mView_def cli_stack_mView_def


(* nxt ps a = lastNxtVal cls a *)
definition "rr f ps als cls \<equiv> 
  (\<forall> a .  a \<in> pushed_addr ps \<longrightarrow> 
            (getTs (f a) > getTs (f (lastNxtVal cls a))) 
          \<and> (\<forall> op . op \<in> ops_unmatched_push als \<and> op \<noteq> f a \<and> op \<noteq> f (lastNxtVal cls a) \<longrightarrow> 
                        getTs op < getTs (f (lastNxtVal cls a)) \<or> getTs op > getTs (f a)) 
          \<and> f a \<in> ops_unmatched_push als 
          \<and> lastNxtVal cls a \<in> pushed_addr ps \<union> {Null} 
          \<and> (lastTop cls \<noteq> Null \<longrightarrow> 
                (\<exists> op opl . f a = op \<and> op\<in>ops_unmatched_push als 
                          \<and> f (lastTop cls) = opl \<and> opl\<in>ops_unmatched_push als 
                          \<and> opl = lastPush als))
          \<and> op_value (f a) als = lib_value cls (lib_lastWr cls a) 
          \<and> lastNxtVal cls a \<noteq> lastTop cls) 
 \<and> (\<forall>a1 a2. a1 \<in> pushed_addr ps \<and> a2 \<in> pushed_addr ps \<and> f a1 = f a2 \<longrightarrow> a1 = a2) 
 \<and> (\<exists> op . op\<in>ops_init als \<and> f Null = op)      
                "

definition "rr_cliV f cls als ps \<equiv>   
   (\<forall> ad w l. ad\<in>pushed_addr ps \<and> w\<in>lib_writes_on cls Top \<and> lib_value cls w = ad \<longrightarrow>
              tst ((cli_lib_mView cls w) l) \<ge> tst ((cli_stack_mView als (f ad)) l))"
(*not correct
definition "rr_cliV_abst f cls als ps \<equiv> (\<forall> ad x . ad\<in>pushed_addr ps \<longrightarrow> snd (ops_modView_cli als (f (ad)) x) \<ge> snd (ops_modView_cli als (f (nxt ps ad)) x))"
*)

definition "rr_cliV_thView t f ccs cls als ps \<equiv> \<forall> ad l . ad\<in>pushed_addr ps \<longrightarrow> tst (ops_modView_cli als (f (ad)) l)
       \<le> tst (thrView ccs t l)"

definition "rr_f_pushed_unmatched f cls als ps \<equiv> ops_unmatched_push als = {f a | a .  a\<in>pushed_addr ps}"

lemma max_minus_max: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> a > b \<Longrightarrow> a = Max A
\<Longrightarrow> (\<forall> e . e\<in>A \<and> e \<noteq> Max A \<longrightarrow> e \<le> b) \<Longrightarrow> b = Max (A-{a})"
  apply(subgoal_tac "A-{a} \<noteq> {}")
  defer  
  apply blast
    apply(subgoal_tac "finite (A-{a})")
  defer 
   apply simp
  apply (subgoal_tac "\<forall> e . e\<in>A  \<longrightarrow> e \<le> Max A")
  defer
  using Max_ge apply blast
  apply (subgoal_tac "a \<noteq> b")
  defer
   apply blast
  apply(subgoal_tac "b\<in>A-{a}")
   defer
  apply blast
  by (metis DiffD1 Diff_insert_absorb Max_eqI mk_disjoint_insert)


lemma nxt_TopLV_oneBeforeLast: "ops_wfs als acs \<Longrightarrow> lib_wfs cls ccs \<Longrightarrow>
       lastTop cls \<noteq> Null \<Longrightarrow> glb_inv ps cls \<Longrightarrow>  ops_wfs als acs \<Longrightarrow> 
        lastNxtVal cls (lastTop cls) \<noteq> Null \<Longrightarrow> 
        rr f ps als cls \<Longrightarrow>
        f (lastNxtVal cls (lastTop cls)) = oneBeforeLastPush als"
  apply(simp add: rr_def oneBeforeLastPush_def glb_inv_def)
  apply(subgoal_tac "f (lastTop cls) = lastPush als")
  defer
   apply (metis Null_def  glb_inv3_def order.strict_implies_not_eq)
  apply(subgoal_tac "f (lastNxtVal cls (lib_value cls (lib_lastWr cls Top))) \<in> ops_unmatched_push als")
  apply(subgoal_tac "snd (f (lastNxtVal cls (lib_value cls (lib_lastWr cls Top)))) = Max (snd ` (ops_unmatched_push als - {lastPush als}))")
  apply(subgoal_tac "fst (f (lastNxtVal cls (lib_value cls (lib_lastWr cls Top)))) = PUSH")
   apply simp
    apply (metis lastTop_def   lastVal_def  prod.collapse)
  apply(subgoal_tac "(lastNxtVal cls (lib_value cls (lib_lastWr cls Top)))\<in>pushed_addr ps")
    apply(simp add: glb_inv1_def glb_inv2_def glb_inv3_def glb_inv4_def glb_inv5_def)
  apply(simp add: getTs_def getOp_def, elim conjE exE)
  apply(simp add: ops_unmatched_push_def ops_on_def getOp_def ops_init_def getTs_def ops_mtch_push_def)
  apply (metis Null_def Suc_eq_plus1 glb_inv3_def gr_implies_not_zero lastNxtVal_def lastTop_def lastVal_def)
    using Null_def glb_inv3_def not_less_zero
    defer  
    apply (metis Suc_eq_plus1 lastNxtVal_def lastTop_def lastVal_def)
  apply(subgoal_tac "Max (snd`(ops_unmatched_push als)) = snd (lastPush als)") defer
   apply (simp add: lastPush_def)
  apply(subgoal_tac "(snd ` (ops_unmatched_push als - {lastPush als})) = (snd ` (ops_unmatched_push als)) - {snd (lastPush als)}")
   defer
   apply (simp add: lastPush_def getTs_def getOp_def ops_unmatched_push_def)
  apply safe
     apply blast
      apply blast
  apply(simp add: ops_on_def)
  apply (simp add: getOp_def)
  apply (metis snd_conv)
  apply simp
  apply (metis DiffI Diff_insert image_eqI insert_iff snd_conv)
  apply simp
  apply(subgoal_tac "snd (f (lastTop cls)) > snd (f (lastNxtVal cls (lib_value cls (lib_lastWr cls Top))))")
     defer  
    apply (metis Nat.add_0_right Null_def One_nat_def add_Suc_right getTs_def glb_inv3_def gr_implies_not0 lastNxtVal_def lastTop_def lastVal_def)
  apply(subgoal_tac "snd (f (lastTop cls))\<in> snd ` ops_unmatched_push als")
  defer
  apply (metis Null_def  equals0I glb_inv3_def imageI  less_numeral_extra(3))
  apply(subgoal_tac "snd (f (lastNxtVal cls (lib_value cls (lib_lastWr cls Top)))) \<in> snd ` ops_unmatched_push als")
   apply(subgoal_tac "lastNxtVal cls (lib_value cls (lib_lastWr cls Top)) \<in> pushed_addr ps")
  apply simp
      defer  
    apply (metis Nat.add_0_right Null_def One_nat_def add_Suc_right glb_inv3_def gr_implies_not0 lastNxtVal_def lastTop_def lastVal_def)
  apply simp
     apply(subgoal_tac "(\<forall> e . e\<in>(snd ` ops_unmatched_push als) \<and> e \<noteq> Max (snd ` ops_unmatched_push als) \<longrightarrow> e \<le> snd (f (lastNxtVal cls (lib_value cls (lib_lastWr cls Top)))))")
   defer
   apply(intro allI impI)
  apply(case_tac " e = snd (f (lastNxtVal cls (lib_value cls (lib_lastWr cls Top))))")
    apply linarith
   apply simp
  apply(subgoal_tac "\<forall> a b. a\<in>pushed_addr ps \<and>
                b \<in> snd`(ops_unmatched_push als) \<and>  b \<noteq> snd (f a) \<and>  b \<noteq> snd(f (lastNxtVal cls a)) \<longrightarrow>
                b < snd (f (lastNxtVal cls a)) \<or> snd (f a) < b") defer
    apply(simp add: getTs_def)
    apply(intro allI impI conjI)
    apply(erule_tac x = aa in allE, simp, elim conjE)
    apply(erule_tac x = PUSH in allE)
    apply(erule_tac x = ba in allE)
  apply(subgoal_tac "(PUSH, ba) \<in> ops_unmatched_push als \<and>
       (PUSH, ba) \<noteq> f aa \<and> (PUSH, ba) \<noteq> f (lastNxtVal cls aa)")
    apply simp
    apply(intro conjI)
  apply(simp add: ops_on_def getOp_def ops_unmatched_push_def)
  apply force 
       apply (metis sndI)
    apply simp
    apply (metis sndI) defer
  apply(elim conjE)
  apply(erule_tac x = "lastTop cls" in allE)
   apply(erule_tac x = "lastTop cls" in allE)
  apply(erule_tac x = "lastTop cls" in allE)
  apply(erule_tac x = "e" in allE)
   apply simp
  apply(subgoal_tac "lib_value cls (lib_lastWr cls Top) \<in> pushed_addr ps \<and>
       e \<in> snd ` ops_on PUSH als", simp)
    apply(subgoal_tac "snd (lastPush als) > e", simp)
    apply(subgoal_tac "Max ( snd ` (ops_unmatched_push als)) = snd (lastPush als)", simp)
        apply(subgoal_tac "finite(snd ` ops_unmatched_push als)")
    apply simp
    apply (simp add: lastTop_def)
  apply(unfold ops_wfs_def ops_mtch_push_def getOp_def getTs_def ops_on_def ops_unmatched_push_def lastPush_def ops_init_def)[1]
  apply (metis (no_types, lifting) Collect_mem_eq Collect_mono_iff Diff_eq_empty_iff finite.emptyI finite_Diff finite_Diff2 finite_imageI  set_diff_eq)
       apply blast
  apply(subgoal_tac "finite(snd ` ops_unmatched_push als)")
       apply(subgoal_tac "(snd ` ops_unmatched_push als) \<noteq> {}")
        apply (metis member_less_max)
       apply blast
  apply(unfold ops_wfs_def ops_mtch_push_def getOp_def getTs_def ops_on_def ops_unmatched_push_def lastPush_def ops_init_def)[1]
  apply (metis (no_types, lifting) Collect_mem_eq Collect_mono_iff Diff_eq_empty_iff finite.emptyI finite_Diff finite_Diff2 finite_imageI set_diff_eq)
     apply simp
    apply(intro conjI)
    apply (simp add: bot_nat_def glb_inv3_def lastTop_def)
    apply (metis (no_types, lifting) DiffD1 image_iff ops_unmatched_push_def)
    apply clarsimp
  apply(subgoal_tac "finite(snd ` ops_unmatched_push als)")
  apply(subgoal_tac "(snd ` ops_unmatched_push als) \<noteq> {}")
    apply (simp add: max_minus_max)    
    apply blast
  apply(unfold ops_wfs_def ops_mtch_push_def getOp_def getTs_def ops_on_def ops_unmatched_push_def lastPush_def ops_init_def)[1]
  apply (metis (no_types, lifting) Collect_mem_eq Collect_mono_iff Diff_eq_empty_iff finite.emptyI finite_Diff finite_Diff2 finite_imageI set_diff_eq)
 done

end
