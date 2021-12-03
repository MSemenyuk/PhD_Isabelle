theory TicketLock_Lib
  imports Main Lib_ProofRules AbstractLock_Lib ordered_set_sd
begin
datatype PC =
  L1
| L2
| L3
| L4
| L5
| CS


consts nt :: L (*next ticket*)
consts sn :: L (*serving now*)
consts l :: L


definition "thrdsvars \<equiv> nt \<noteq> sn"


record prog_state =
  pc :: "T \<Rightarrow> PC"
  my_ticket :: "T \<Rightarrow> nat"
  serving_now :: "T \<Rightarrow> nat"
  r :: "T \<Rightarrow> nat"
  first :: bool


definition 
  "update_pc t nv pcf \<equiv> pcf (t := nv)"


definition lock_acq :: "T \<Rightarrow> prog_state \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> prog_state \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool " where
"lock_acq t s ls cs s' ls' cs' \<equiv> 
(
if (pc s) t = L1
then
    ((ls) (cs) fetch-and-inc[my_ticket s' t  \<leftarrow> lib(nt)]\<^sub>t (ls') (cs')) \<and>
     (pc s' = update_pc t L2 (pc s)) \<and>
    (serving_now s' = serving_now s) 
     \<and>  (\<forall>t' . t'\<noteq>t \<longrightarrow> my_ticket s' t' = my_ticket s t') \<and> (first s' = False)
else
if (pc s) t = L2
then 
    ((ls) (cs) [serving_now s' t \<leftarrow>\<^sup>A lib(sn)]\<^sub>t (ls') (cs')) \<and>
    (my_ticket s' t = serving_now s' t \<longrightarrow> pc s' = update_pc t CS (pc s)) \<and>
    (my_ticket s' t \<noteq> serving_now s' t \<longrightarrow> pc s' = update_pc t L2 (pc s)) \<and> 
    (my_ticket s = my_ticket s') \<and> (\<forall>t' . t'\<noteq>t \<longrightarrow> serving_now s' t' = serving_now s t')
    \<and> (first s' = first s)
else
True
)"

     (*((ls) (cs) [r s' t \<leftarrow> lib(sn)]\<^sub>t (ls') (cs'))*)
definition lock_rel :: "T \<Rightarrow> prog_state \<Rightarrow> lib_state \<Rightarrow> surrey_state  \<Rightarrow>  prog_state \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool " where
"lock_rel t s ls cs  s' ls' cs' \<equiv> 
(
if (pc s) t = L3
then
     ls = ls' \<and> cs = cs'\<and>
    pc s' = update_pc t L4 (pc s) \<and> 
    (my_ticket s = my_ticket s') \<and>  (serving_now s = serving_now s') \<and> (first s' = first s)
else
  if  (pc s) t = L4
    then
     ((ls) (cs) [lib(sn) :=\<^sup>R ((serving_now s t) + 1)]\<^sub>t (ls') (cs')) \<and>
     pc s' = update_pc t L5 (pc s)  \<and>
     (my_ticket s = my_ticket s') \<and>  (serving_now s = serving_now s') \<and> (first s' = first s)

else
  if (pc s) t = L5
  then
    False
  else
True
)"


definition c_ops :: "T \<Rightarrow> prog_state \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow>  prog_state \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool " where
"c_ops t s ls cs s' ls' cs' \<equiv> 
(if (pc s) t = CS 
then
  ls' = ls \<and>  (pc s' = update_pc t L3 (pc s)) \<and>
  (my_ticket s = my_ticket s') \<and>  (serving_now s = serving_now s') \<and> (first s' = first s)

else 
  True
)
"

(*****************TicketLock Properties************)
definition "previous_versions ls \<equiv> \<forall> w v . w \<in> lib_writes_on ls nt \<and> v = lib_value ls w \<and> v \<noteq> 0
                                      \<longrightarrow> (\<exists> w'. w'\<in> lib_writes_on ls nt \<and> lib_value ls w'= v-1)"

definition "nt_ns_gt_zero ls \<equiv> \<forall> w w' . w \<in> lib_writes_on ls nt \<and> w' \<in> lib_writes_on ls sn
            \<longrightarrow> lib_value ls w \<ge> 0 \<and>  lib_value ls w' \<ge> 0"

definition "nt_all_cvd_but_last cl \<equiv> \<forall> wnt . wnt \<noteq> lib_lastWr cl nt  \<longrightarrow>  wnt \<in> lib_covered cl "

definition "nt_order ls \<equiv> \<forall> w w' . w\<in>lib_writes_on ls nt \<and>  w'\<in>lib_writes_on ls nt \<and> tst w' > tst w
      \<longrightarrow> lib_value ls w' > lib_value ls w "


definition "nt_order_ts ls \<equiv> \<forall> w w' . w\<in>lib_writes_on ls nt \<and>  w'\<in>lib_writes_on ls nt \<and>  lib_value ls w' > lib_value ls w
      \<longrightarrow>  tst w' > tst w "

definition "glb_inv_1 ls \<equiv> previous_versions ls \<and> nt_ns_gt_zero ls \<and> nt_all_cvd_but_last ls \<and> nt_order ls"


lemmas glb_inv_1 = glb_inv_1_def previous_versions_def nt_ns_gt_zero_def nt_all_cvd_but_last_def nt_order_def
 
lemma ticketlock_previous_versions_inv:
  assumes "lib_wfs ls cs" 
      and "thrdsvars"
      and "wfs cs "
      and "previous_versions ls"
      and "lock_acq t s ls cs s' ls' cs'"
      and "c_ops t s ls cs s' ls' cs'"
      and "lock_rel t s ls cs s' ls' cs'"
    shows "previous_versions ls'"
  using assms
  apply(simp add: thrdsvars_def previous_versions_def lock_acq_def)
  apply(case_tac "pc s t = L1", simp)
   apply(simp add: lib_fetch_and_inc_step_def)
   apply(elim conjE exE, intro allI impI, elim conjE)
    apply(subgoal_tac "a = nt \<and> aa = nt", simp_all)
  apply(simp add: lib_writes_on_def lib_value_def)
   apply(simp add: lib_update_def all_updates_l lib_value_def lib_writes_on_def)
    apply(intro conjI impI, simp)
  apply(simp add: lib_visible_writes_def lib_writes_on_def lib_valid_fresh_ts_def)
  using not_less_iff_gr_or_eq apply blast
  apply(simp add: lib_visible_writes_def lib_writes_on_def lib_valid_fresh_ts_def)
    apply (metis dual_order.strict_implies_not_eq)
  apply(simp add: lib_visible_writes_def lib_writes_on_def lib_valid_fresh_ts_def)
    apply(intro allI impI)
  apply(case_tac "pc s t = L2", simp)
   apply(simp add: lib_read_step_def lib_read_def)
   apply(elim conjE exE)
    apply(subgoal_tac "a = nt \<and> aa = sn", simp_all)
  apply(simp add: lib_writes_on_def lib_value_def)
   apply(simp add:  all_updates_l lib_value_def lib_writes_on_def)
   apply(simp add: lib_visible_writes_def lib_writes_on_def lib_valid_fresh_ts_def)
  apply(simp add: c_ops_def lock_rel_def)
  apply(cases "pc s t", simp_all) 
   apply (metis write_pres_value write_writes_on_diff_var)
  done

lemma nt_ns_gt_zero_inv:
  assumes "lib_wfs ls cs" 
      and "thrdsvars"
      and "wfs cs "
      and "nt_ns_gt_zero ls"
      and "lock_acq t s ls cs s' ls' cs'"
      and "c_ops t s ls cs s' ls' cs'"
      and "lock_rel t s ls cs s' ls' cs'"
    shows "nt_ns_gt_zero ls'"
  using assms
  by(simp add: thrdsvars_def nt_ns_gt_zero_def lock_acq_def)


lemma nt_all_cvd_but_last_inv:
  assumes "lib_wfs ls cs" 
      and "thrdsvars"
      and "wfs cs "
      and "nt_all_cvd_but_last ls"
      and "lock_acq t s ls cs s' ls' cs'"
      and "c_ops t s ls cs s' ls' cs'"
      and "lock_rel t s ls cs s' ls' cs'"
    shows "nt_all_cvd_but_last ls'"
  using assms
  using assms
  apply(simp add: thrdsvars_def nt_all_cvd_but_last_def lock_acq_def)
  apply(cases "pc s t", simp_all)
  apply(intro allI impI)
    apply(simp add: lib_fetch_and_inc_step_def  lib_update_def all_updates_l lib_writes_on_def lib_value_def)
  apply(elim conjE exE)
   apply(case_tac "lib_releasing ls (a, b)", simp_all)
  apply (metis Pair_inject)
  apply (metis old.prod.inject)
  apply(intro allI impI)
      apply (metis (mono_tags, lifting)  lib_lastWr_def lib_wfs_def  prod.inject)
  apply (metis (full_types) a_is_x lib_lastWr_def lib_last_in_visible_writes lib_wfs_def)
    apply (simp add: lock_rel_def)
    defer
    apply (simp add: lock_rel_def)
  using c_ops_def apply auto[1]
  apply(simp add: update_pc_def)
  apply(elim conjE)
  apply(simp add: lib_write_step_def lib_write_def)
  by (metis a_is_x assms(1) assms(3) assms(4) lib_last_in_visible_writes nt_all_cvd_but_last_def)

lemma nt_all_cvd_but_last_cvd: "nt_all_cvd_but_last ls \<Longrightarrow> 
                  cvd[lib(nt), (lib_value ls (lib_lastWr ls nt))] ls"
  using lib_covered_v_def nt_all_cvd_but_last_def by force



lemma nt_order_inv:
  assumes "lib_wfs ls cs" 
      and "thrdsvars"
      and "wfs cs "
      and "nt_order ls"
      and "nt_all_cvd_but_last ls"
      and "lock_acq t s ls cs s' ls' cs'"
      and "c_ops t s ls cs s' ls' cs'"
      and "lock_rel t s ls cs s' ls' cs'"
        shows "nt_order ls'"
  using assms
  apply(simp add: thrdsvars_def nt_order_def lock_acq_def nt_all_cvd_but_last_def c_ops_def lock_rel_def)
  apply(cases "pc s t", simp_all)
    apply(simp_all add: update_pc_def)
      apply clarsimp
  apply(case_tac "(a, b) \<in> lib_writes_on ls nt \<and>
               (aa, ba) \<in> lib_writes_on ls nt")
       apply (metis f_a_i_pres_value)
      apply simp
      apply(case_tac "(a, b) \<in> lib_writes_on ls nt", simp_all)
    apply(subgoal_tac " lib_value ls' (a, b) =  lib_value ls (a, b)", simp)
     apply(simp add: lib_fetch_and_inc_step_def) 
      apply(elim exE conjE)
      apply(subgoal_tac "cvd[lib(nt), (lib_value ls (lib_lastWr ls nt))] ls")
       apply(subgoal_tac "\<exists> v . v = (lib_value ls (lib_lastWr ls nt))")
  apply(elim exE)
     apply(subgoal_tac "lib_value ls (ab, bb) = v \<and> (ab, bb)\<in>lib_writes_on ls nt 
          \<and> lib_value ls (a,b) \<le> v", simp)
  apply(simp add: lib_update_def all_updates_l lib_writes_on_def lib_value_def)
      apply blast
        apply(intro conjI)
  using cvd_vw_val apply blast
         apply(simp add: lib_visible_writes_def)
        apply(subgoal_tac "(ab, bb) =  lib_lastWr ls nt")
         apply(case_tac "(a, b) = (ab, bb)", simp_all)
  apply(subgoal_tac "b < bb")
       apply (smt less_imp_le_nat lib_covered_v_def lib_cvd_exist_last_write)
  apply(simp add: lib_visible_writes_def lib_wfs_def lib_writes_on_def)
      apply (metis assms(1) leI snd_conv ts_ge_last_is_last tst_def)
  apply(simp add: lib_visible_writes_def)
  using lib_covered_v_def apply blast
  using assms (5) nt_all_cvd_but_last_cvd
  apply blast
  using f_a_i_pres_value apply auto[1]
   apply(simp add: lib_fetch_and_inc_step_def) 
   apply(elim exE conjE)
   apply(subgoal_tac "b = ts'")
    apply(case_tac "(aa, ba) \<in> lib_writes_on ls nt")
  apply(case_tac "(aa, ba) = (ab, bb)", simp_all)
      apply(simp add: lib_valid_fresh_ts_def)
  apply (subgoal_tac "aa = ab", simp)
     apply(subgoal_tac "(ab, bb) =  lib_lastWr ls nt")
      apply(simp add: lib_valid_fresh_ts_def)  
        apply (metis a_is_x dual_order.strict_implies_order leD less_trans ts_eq_lastWr)
  apply(subgoal_tac "(ab, bb)\<in>lib_writes_on ls nt")
  using lib_covered_v_def apply blast
  apply(simp add: lib_visible_writes_def)
     apply(simp add: lib_visible_writes_def lib_writes_on_def)
  apply(simp add: lib_update_def all_updates_l lib_writes_on_def lib_value_def)
    apply blast
  apply(simp add: lib_update_def all_updates_l lib_writes_on_def lib_value_def)
   apply auto[1]  
    apply (metis lib_read_writes_on_diff_var_pres_backwards read_pres_value)
  apply (metis (full_types) write_pres_value write_writes_on_diff_var)
  done


lemma nt_order_ts_inv:
  assumes "lib_wfs ls cs" 
      and "thrdsvars"
      and "wfs cs "
      and "nt_order_ts ls"
      and "nt_all_cvd_but_last ls"
      and "lock_acq t s ls cs s' ls' cs'"
      and "c_ops t s ls cs s' ls' cs'"
      and "lock_rel t s ls cs s' ls' cs'"
        shows "nt_order_ts ls'"
  using assms
  apply(simp add: thrdsvars_def nt_order_ts_def lock_acq_def nt_all_cvd_but_last_def c_ops_def lock_rel_def)
  apply(cases "pc s t", simp_all)
    apply(simp_all add: update_pc_def)
    defer
  
    apply (metis lib_read_writes_on_diff_var_pres_backwards read_pres_value)
  apply (metis assms(1) assms(3)  write_pres_value write_writes_on_diff_var)
      apply clarsimp
  apply(case_tac "(a, b) \<in> lib_writes_on ls nt \<and>
               (aa, ba) \<in> lib_writes_on ls nt")
       apply (metis f_a_i_pres_value)
  apply simp
     apply(simp add: lib_fetch_and_inc_step_def lib_update_def  all_updates_l lib_value_def) 
  apply(elim exE conjE)
  apply(case_tac "lib_releasing ls (ab, bb)"; case_tac "(a, b) \<in> lib_writes_on ls nt", simp_all add: lib_writes_on_def)
     apply(simp add: lib_valid_fresh_ts_def lib_visible_writes_def lib_writes_on_def var_def tst_def)
  apply(case_tac "nt = ab \<and> b = ts'", simp_all)
      apply blast
     apply safe
  apply (simp add: lib_wfs_def) 
  apply (metis subsetD)
     apply(simp add: lib_valid_fresh_ts_def lib_visible_writes_def lib_writes_on_def var_def tst_def)
  using Suc_lessD apply presburger
     apply(simp add: lib_valid_fresh_ts_def lib_visible_writes_def lib_writes_on_def var_def tst_def)
  apply clarsimp
  apply (metis dual_order.strict_implies_order dual_order.trans not_le_imp_less snd_conv ts_ge_last_is_last tst_def)
     apply(simp add: lib_valid_fresh_ts_def lib_visible_writes_def lib_writes_on_def var_def tst_def)
  using Suc_lessD by presburger


definition "sn_ordered_val ls \<equiv> \<forall> w . w\<in>lib_writes_on ls sn \<and> lib_value ls w > 0 \<longrightarrow>
                                  (\<exists> w' .  w'\<in>lib_writes_on ls sn \<and>  lib_value ls w' = lib_value ls w - 1)"


lemma no_val_next: " u > i   \<Longrightarrow> [\<zero>lib(sn), u]\<^sub>i ls  \<Longrightarrow> sn_ordered_val ls \<Longrightarrow> [\<zero>lib(sn), (u+1)]\<^sub>i ls"
  apply(simp add:  sn_ordered_val_def)
  apply(subgoal_tac "\<forall> w . w\<in>lib_writes_on ls sn \<longrightarrow> lib_value ls w \<noteq> u") defer
  apply (simp add: no_val_no_value)
  apply(simp add: lib_no_val_def, elim conjE)
  apply(simp add: lib_p_vorder_def lib_init_val_def, intro allI impI, elim exE conjE)
  apply(subgoal_tac "Suc u > 0") defer
   apply blast defer
  apply(erule_tac x = aa in allE)
  apply(erule_tac x = aa in allE)
  apply(erule_tac x = ba in allE)
  apply simp
   apply(simp add: lib_writes_on_def)
   apply blast
  apply(subgoal_tac "\<forall> w . w\<in>lib_writes_on ls sn \<longrightarrow> lib_value ls w \<noteq> u") defer
  apply (simp add: no_val_no_value)
  apply(simp add: lib_no_val_def, elim conjE)
  apply(simp add: lib_p_vorder_def lib_init_val_def, intro allI impI, elim exE conjE)
  apply(subgoal_tac "Suc u > 0") defer
   apply blast defer
  apply(erule_tac x = aa in allE)
  apply(erule_tac x = aa in allE)
  apply(erule_tac x = ba in allE)
  apply simp
   apply(simp add: lib_writes_on_def)
  apply blast
done

lemma no_val_next_future: " u > i   \<Longrightarrow> [\<zero>lib(sn), u]\<^sub>i ls  \<Longrightarrow> sn_ordered_val ls \<Longrightarrow> u < u' \<Longrightarrow> [\<zero>lib(sn), (u')]\<^sub>i ls"
  apply(induction u')
   apply simp
  by (metis Suc_eq_plus1 dual_order.strict_trans no_val_next not_less_less_Suc_eq)


definition "sn_ordered_ts ls \<equiv> \<forall> w w' . w\<in>lib_writes_on ls sn \<and>  w'\<in>lib_writes_on ls sn \<and> tst w < tst w' \<longrightarrow>
                                       lib_value ls w < lib_value ls w'"


lemma vals_smaller_d_obs_sn_order: "lib_wfs ls cs \<Longrightarrow> sn_ordered_val ls \<Longrightarrow> sn_ordered_ts ls \<Longrightarrow> [lib(sn) =\<^sub>t u] ls \<Longrightarrow> w\<in>lib_writes_on ls sn \<Longrightarrow> lib_value ls w \<le> u"
  apply(simp add:  sn_ordered_ts_def lib_d_obs_t_def lib_d_obs_def)
  apply(elim conjE)
  apply(case_tac "w = lib_lastWr ls sn")
   apply blast
  apply(subgoal_tac "tst w < tst (lib_lastWr ls sn) \<and> lib_lastWr ls sn\<in>lib_writes_on ls sn")
   apply(simp add:  sn_ordered_val_def)
   apply(elim conjE)
   apply(subgoal_tac "\<exists> a aa b bb. w = (a,b) \<and> (lib_lastWr ls sn = (aa, bb))")
  apply(elim exE conjE, simp)
  using less_or_eq_imp_le apply blast
  apply simp
  apply(intro conjI)
  apply(simp add: lib_lastWr_def lib_value_def tst_def lib_writes_on_def lib_wfs_def var_def)
  apply (metis (mono_tags) Max_ge finite_imageI imageI less_eq_rat_def mem_Collect_eq prod.collapse)
  apply(simp add: lib_lastWr_def lib_value_def tst_def lib_writes_on_def lib_wfs_def var_def)
  by metis

lemma sn_ordered_val_pres: "sn_ordered_val ls \<Longrightarrow> lib_fetch_and_inc_step t y ls cs ls' cs' v \<Longrightarrow> y \<noteq> sn \<Longrightarrow> sn_ordered_val ls'"
  apply(simp add: lib_fetch_and_inc_step_def sn_ordered_val_def lib_update_def all_updates_l )
  apply(elim exE conjE, intro allI impI conjI)
  apply(simp add: lib_visible_writes_def lib_writes_on_def lib_valid_fresh_ts_def lib_value_def)
  apply(case_tac "lib_releasing ls (y, b)", simp_all)
  by auto

lemma sn_ordered_ts_pres: "sn_ordered_ts ls \<Longrightarrow> lib_fetch_and_inc_step t y ls cs ls' cs' v \<Longrightarrow> y \<noteq> sn \<Longrightarrow> sn_ordered_ts ls'"
  apply(simp add: lib_fetch_and_inc_step_def sn_ordered_ts_def lib_update_def all_updates_l )
  apply(elim exE conjE, intro allI impI conjI)
  apply(simp add: lib_visible_writes_def lib_writes_on_def lib_valid_fresh_ts_def lib_value_def)
  apply(case_tac "lib_releasing ls (y, b)", simp_all)
  by auto


lemma sn_ordered_val_read_pres: "sn_ordered_val ls \<Longrightarrow> lib_read_step t y b ls cs ls' cs' v \<Longrightarrow> sn_ordered_val ls'"
  apply(simp add: lib_read_step_def sn_ordered_val_def lib_read_def all_updates_l )
  apply(elim exE conjE, intro allI impI conjI)
  apply(simp add: lib_visible_writes_def lib_writes_on_def lib_valid_fresh_ts_def lib_value_def)
  by auto

lemma sn_ordered_ts_read_pres: "sn_ordered_ts ls \<Longrightarrow> lib_read_step t y b ls cs ls' cs' v \<Longrightarrow> sn_ordered_ts ls'"
  apply(simp add: lib_read_step_def sn_ordered_ts_def lib_read_def all_updates_l )
  apply(elim exE conjE, intro allI impI conjI)
  apply(simp add: lib_visible_writes_def lib_writes_on_def lib_valid_fresh_ts_def lib_value_def)
  by auto


lemma sn_ordered_val_write_pres: "lib_wfs ls cs \<Longrightarrow> sn_ordered_val ls \<Longrightarrow>[lib(sn) =\<^sub>t v] ls \<Longrightarrow> lib_write_step t sn b ls cs ls' cs' (Suc v) \<Longrightarrow> sn_ordered_val ls'"
  apply(simp add: sn_ordered_val_def)
  apply(intro allI impI)
  apply(case_tac "(a, ba) \<in> lib_writes_on ls sn")
   apply(subgoal_tac "lib_value ls' (a, ba) = lib_value ls (a, ba)", simp)
  apply(erule_tac x = a in allE)
    apply(erule_tac x = ba in allE)
    apply(elim conjE exE, simp)
    apply(elim exE conjE)
  apply(rule_tac x = "aa" in exI)
    apply(rule_tac x = "baa" in exI)
    apply(intro conjI)
  apply(simp add: lib_write_step_def lib_write_def all_updates_l lib_writes_on_def)
     apply(elim exE conjE, simp)
  apply(subgoal_tac "lib_value ls (aa, baa) = lib_value ls' (aa, baa)")
     apply simp
  apply(simp add: lib_write_step_def lib_write_def all_updates_l lib_writes_on_def lib_value_def)
     apply(elim exE conjE, simp)
    using fresh_ts_not_in_writes apply auto[1]
  apply(simp add: lib_write_step_def lib_write_def all_updates_l lib_writes_on_def lib_value_def)
     apply(elim exE conjE, simp)
    using fresh_ts_not_in_writes apply blast
    apply(subgoal_tac "lib_value ls' (a, ba) = Suc v") defer
   apply(simp add: lib_write_step_def lib_write_def all_updates_l lib_writes_on_def lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def tst_def var_def)
     apply(elim exE conjE)
     apply(subgoal_tac "ba = ts'", simp)
     apply(case_tac "a = sn", simp_all)
    apply(subgoal_tac "\<exists> a b . (a, b)\<in>lib_writes_on ls sn \<and> lib_value ls (a,b) = v")
     apply(elim conjE exE)
    apply(subgoal_tac "(aa, baa) \<in> lib_writes_on ls' sn \<and>
       lib_value ls (aa, baa) = lib_value ls' (aa, baa)")
      apply auto[1]
    apply(intro conjI)
    apply(simp add: lib_write_step_def lib_write_def all_updates_l lib_writes_on_def lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def tst_def var_def)
     apply(elim conjE exE, simp)
    apply(simp add: lib_write_step_def lib_write_def all_updates_l lib_writes_on_def lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def tst_def var_def)
     apply(elim conjE exE, simp)   
     apply blast
    apply(simp add: lib_d_obs_def lib_d_obs_t_def)
         apply(elim conjE)
    apply(subgoal_tac "\<exists> a b . lib_lastWr ls sn = (a, b)")
     apply(elim exE conjE, simp)
    apply(rule_tac x = aa in exI)
     apply(rule_tac x = baa in exI)
     apply(intro conjI)
    apply(subgoal_tac "lib_lastWr ls sn\<in>lib_writes_on ls sn")
       apply simp
    apply(simp add: lib_writes_on_def lib_lastWr_def var_def tst_def lib_wfs_def)
  apply metis
  apply auto[1]
    using surj_pair by blast

lemma sn_ordered_ts_write_pres: "lib_wfs ls cs \<Longrightarrow>  sn_ordered_val ls \<Longrightarrow> sn_ordered_ts ls
       \<Longrightarrow> [lib(sn) =\<^sub>t v] ls \<Longrightarrow> lib_write_step t sn b ls cs ls' cs' (Suc v)
       \<Longrightarrow> sn_ordered_ts ls'"
  apply(simp add: sn_ordered_ts_def)
  apply(intro allI impI, elim conjE)
  apply(case_tac "(a, ba) \<in> lib_writes_on ls sn \<and>  (aa, baa) \<in> lib_writes_on ls sn")
   apply(subgoal_tac " lib_value ls' (a, ba) =  lib_value ls (a, ba) \<and> lib_value ls' (aa, baa) = lib_value ls (aa, baa)")
    apply simp
   apply(intro conjI)
    apply(simp add: lib_write_step_def lib_write_def all_updates_l lib_writes_on_def lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def tst_def var_def)
     apply(elim conjE exE, simp)
  apply blast
    apply(simp add: lib_write_step_def lib_write_def all_updates_l lib_writes_on_def lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def tst_def var_def)
   apply(elim conjE exE, simp)
  apply blast
  apply simp
  apply(case_tac "(a, ba) \<in> lib_writes_on ls sn", simp_all)
   apply(subgoal_tac "lib_value ls (a, ba) \<le> v") defer
  apply(subgoal_tac "sn_ordered_ts ls")
  using vals_smaller_d_obs_sn_order
     apply blast
    apply(simp add: sn_ordered_ts_def) defer  
  apply(subgoal_tac "lib_value ls' (aa, baa) = Suc v \<and> lib_value ls (a, ba) = lib_value ls' (a, ba)")
    apply linarith
   apply(intro conjI)
    apply(simp add: lib_write_step_def lib_write_def all_updates_l lib_writes_on_def lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def tst_def var_def)
   apply(elim conjE exE, simp)
    apply(simp add: lib_write_step_def lib_write_def all_updates_l lib_writes_on_def lib_value_def lib_valid_fresh_ts_def lib_visible_writes_def tst_def var_def)
   apply(elim conjE exE, simp)
  apply(case_tac "(aa, baa) \<in> lib_writes_on ls sn")
   apply(simp add: lib_write_step_def)
   apply(elim exE conjE)
  apply(subgoal_tac "ba = ts'", simp)
    defer
      apply(simp add: lib_write_step_def lib_write_def all_updates_l lib_writes_on_def   lib_visible_writes_def )
    apply blast defer
   apply(case_tac "(aa, baa) = lib_lastWr ls sn")
      apply(simp add: lib_write_step_def lib_write_def all_updates_l lib_writes_on_def tst_def var_def  lib_lastWr_def  lib_visible_writes_def lib_value_def)
    apply(elim conjE)
  apply(simp add: lib_d_obs_t_def lib_d_obs_def lib_value_def lib_lastWr_def lib_writes_on_def)
  apply (metis  dual_order.irrefl dual_order.strict_trans2 lib_valid_fresh_ts_def  order.strict_trans  snd_conv tst_def var_def)
  apply(subgoal_tac "baa <  tst (lib_lastWr ls sn)")
    defer
    apply(simp add: lib_lastWr_def lib_writes_on_def tst_def var_def)
    apply(subgoal_tac "baa \<in> snd ` {w. fst w = sn \<and> w \<in> lib_writes ls} ")
  apply(simp add: lib_wfs_def lib_writes_on_def var_def tst_def lib_visible_writes_def )
  apply (metis (mono_tags)  Max_ge  finite_imageI   less_eq_rat_def  )
    apply (simp add: image_iff)
  defer
    apply(simp add:tst_def var_def lib_d_obs_t_def lib_d_obs_def lib_visible_writes_def lib_value_def lib_valid_fresh_ts_def lib_lastWr_def lib_writes_on_def)
        apply(simp add: lib_write_step_def  lib_write_def all_updates_l lib_writes_on_def tst_def var_def  lib_lastWr_def  lib_visible_writes_def lib_value_def)
    apply(elim conjE exE, simp)
  done


lemma sn_d_obs_next_no_val: "lib_wfs ls cs \<Longrightarrow> lib_init_val ls sn 0 \<Longrightarrow> sn_ordered_val ls \<Longrightarrow> sn_ordered_ts ls \<Longrightarrow> [lib(sn) =\<^sub>t u] ls \<Longrightarrow> [\<zero>lib(sn), (u+1)]\<^sub>0 ls"
  apply(simp add: lib_d_obs_def lib_d_obs_t_def)
  apply(elim conjE)
  apply(subgoal_tac "\<exists> a b . lib_lastWr ls sn = (a,b)") defer
   apply simp
  apply(elim exE)
  apply(subgoal_tac "\<forall> a ts . (a,ts)\<in>lib_writes_on ls sn \<and> b\<noteq>ts \<longrightarrow> ts < b") defer
   apply(simp add: lib_lastWr_def lib_writes_on_def lib_value_def tst_def var_def lib_wfs_def)
   apply(intro allI impI)
  apply(subgoal_tac "(a,b)\<in>lib_writes_on ls sn") defer
    apply (metis (mono_tags, lifting) lib_writes_on_def mem_Collect_eq var_def) defer
   apply(simp add: lib_writes_on_def var_def tst_def)
  apply(subgoal_tac "finite (snd ` {w. fst w = sn \<and> w \<in> lib_writes ls})")
  apply (metis (mono_tags, lifting) Max_ge image_iff mem_Collect_eq order.not_eq_order_implies_strict snd_conv)
  apply blast
  apply(simp add: lib_no_val_def lib_p_vorder_def)
  apply(intro conjI allI impI)
  apply safe
  using lib_d_obs_def lib_d_obs_t_def vals_smaller_d_obs_sn_order by fastforce



lemma sn_ordered_d_obs_no_val: "lib_wfs ls cs \<Longrightarrow> lib_init_val ls sn 0 \<Longrightarrow> sn_ordered_val ls \<Longrightarrow> sn_ordered_ts ls \<Longrightarrow> [lib(sn) =\<^sub>t u] ls \<Longrightarrow> v > u \<Longrightarrow> [\<zero>lib(sn), v]\<^sub>0 ls"
  apply(induction v)
   apply simp
  by (metis Suc_eq_plus1_left Zero_not_Suc add.commute gr0I lessI less_imp_Suc_add no_val_next_future not_less_less_Suc_eq sn_d_obs_next_no_val)


lemma sn_ordered_exist_w_and_one_less:
"lib_wfs ls cs \<Longrightarrow> lib_init_val ls sn 0 \<Longrightarrow> sn_ordered_val ls \<Longrightarrow> sn_ordered_ts ls \<Longrightarrow> (a,b)\<in>lib_writes_on ls sn
\<Longrightarrow> lib_value ls (a,b) = u \<Longrightarrow> u > 0 \<Longrightarrow> v = u - 1 \<Longrightarrow> (\<exists> w'. w'\<in>lib_writes_on ls sn \<and> lib_value ls w' = v)"
  apply(simp add: sn_ordered_val_def)
  apply(erule_tac x = "a" in allE)
  apply(erule_tac x = "b" in allE)
  apply simp
  done


lemma sn_ordered_u_plus_one:
"lib_wfs ls cs \<Longrightarrow> lib_init_val ls sn 0 \<Longrightarrow> sn_ordered_val ls \<Longrightarrow> sn_ordered_ts ls \<Longrightarrow> (a,b)\<in>lib_writes_on ls sn
\<Longrightarrow> lib_value ls (a,b) = 1 \<Longrightarrow>  (\<exists> w'. w'\<in>lib_writes_on ls sn \<and> lib_value ls w' = 0)"
  using sn_ordered_exist_w_and_one_less by fastforce


lemma sn_ordered_exist_w_and_all_less:
"lib_wfs ls cs \<Longrightarrow> lib_init_val ls sn 0 \<Longrightarrow> sn_ordered_val ls \<Longrightarrow> sn_ordered_ts ls
 \<Longrightarrow> w\<in>lib_writes_on ls sn
\<Longrightarrow> lib_value ls w = u \<Longrightarrow> u > v \<Longrightarrow> v \<ge> 0 \<Longrightarrow>
 (\<exists> w'. w'\<in>lib_writes_on ls sn \<and> lib_value ls w' = v)"
  using earlier_elements  [where A = "lib_writes_on ls sn" and f = "lib_value ls" and u = u and e = w]
  using sd_ordereded_def sd_earlier_def
  by (smt dual_order.strict_trans2 earlier_elements sn_ordered_val_def)


lemma sn_d_obs_noval: "lib_wfs ls cs \<Longrightarrow> sn_ordered_val ls \<Longrightarrow> sn_ordered_ts ls \<Longrightarrow> [lib(sn) =\<^sub>t u] ls \<Longrightarrow> [\<zero>lib(sn), Suc v]\<^sub>0 ls \<Longrightarrow> v \<ge> u"
  apply(case_tac " u = 0")
  apply simp
  apply(subgoal_tac "u > 0", simp)
   defer
   apply simp
  apply(subgoal_tac "\<forall>z. z < u \<and> z > 0 \<longrightarrow>  \<not>[\<zero>libsn, z]\<^sub>0 ls")
   defer
   apply(intro allI impI)
   apply(simp add: lib_no_val_def lib_p_vorder_def)
   apply(elim conjE)
   apply(simp add: lib_init_val_def)
   apply(elim conjE exE)
  apply(rule_tac x = a in exI)
   apply(rule_tac x = b in exI)
   apply(intro conjI)
    apply blast
   apply(subgoal_tac "\<exists> aaa  bbb . (aaa,bbb)\<in>lib_writes_on ls sn \<and> lib_value ls (aaa,bbb) = z")
    defer
    apply(simp add: sn_ordered_val_def)
   apply(subgoal_tac "\<exists> aaaa  bbbb . (aaaa,bbbb)\<in>lib_writes_on ls sn \<and> lib_value ls (aaaa,bbbb) = u")
     defer
     apply(simp add: lib_d_obs_t_def lib_d_obs_def)
  apply(subgoal_tac "lib_lastWr ls sn \<in> lib_writes_on ls sn")
      apply (metis surj_pair)
  apply(simp add: lib_lastWr_def lib_writes_on_def var_def tst_def lib_wfs_def)
  apply metis
    defer
    apply(elim exE conjE) 
  apply(rule_tac x = aaa in exI)
    apply(rule_tac x = bbb in exI)
  apply(intro conjI)
       apply blast+
    apply(simp add: sn_ordered_ts_def sn_ordered_val_def)
  apply(simp add: lib_value_def lib_writes_on_def var_def tst_def)
    apply (metis (full_types)  Suc_pred Zero_not_Suc)
  defer
  apply(subgoal_tac " \<not>[\<zero>libsn, u]\<^sub>0 ls")
  apply (metis Suc_lessI gr0_conv_Suc leI)  
  using d_obs_p_obs_contradiction no_val_not_p_obs apply blast
  apply(elim exE conjE) 
  apply(subgoal_tac "[\<zero>lib(sn), Suc v]\<^sub>0 ls \<and> lib_wfs ls cs \<and> sn_ordered_val ls")
   apply(simp add: lib_no_val_def, elim conjE)
   apply (metis less_eq_nat.simps(1) sn_ordered_exist_w_and_all_less surj_pair)
   apply(simp add: lib_no_val_def lib_init_val_def sn_ordered_val_def lib_p_vorder_def)
  by blast


(****************************************)

definition "lib_mt t p ls cs  s \<equiv> 
     (case p of
          L1 \<Rightarrow>  (\<exists> v. cvd[lib(nt), v] ls \<and> (\<forall>t' . t'\<noteq>t \<and> pc s t' \<noteq>  L1 \<longrightarrow> v > my_ticket s t' )) 
        | L2 \<Rightarrow>  (\<forall>t' . t'\<noteq>t \<and> pc s t' \<noteq>L1 \<longrightarrow> my_ticket s t \<noteq> my_ticket s t' ) \<and> en[lib(nt), (Suc (my_ticket s t))]\<^sub>t ls
        | CS \<Rightarrow>  (\<forall>t' . t'\<noteq>t \<and> pc s t' \<noteq>L1 \<longrightarrow> my_ticket s t \<noteq> my_ticket s t' ) \<and> en[lib(nt), (Suc (my_ticket s t))]\<^sub>t ls
        | L3 \<Rightarrow>  (\<forall>t' . t'\<noteq>t \<and> pc s t' \<noteq>L1 \<longrightarrow> my_ticket s t \<noteq> my_ticket s t' ) \<and> en[lib(nt), (Suc (my_ticket s t))]\<^sub>t ls
        | L4 \<Rightarrow>  (\<forall>t' . t'\<noteq>t \<and> pc s t' \<noteq>L1 \<longrightarrow> my_ticket s t \<noteq> my_ticket s t' ) \<and> en[lib(nt), (Suc (my_ticket s t))]\<^sub>t ls
        | L5 \<Rightarrow>  (\<forall>t' . t'\<noteq>t \<and> pc s t' \<noteq>L1 \<longrightarrow> my_ticket s t \<noteq> my_ticket s t' ) \<and> en[lib(nt), (Suc (my_ticket s t))]\<^sub>t ls
    )
"

lemma lib_inv_m_t_local:
  assumes "lib_wfs ls cs" 
      and "thrdsvars"
      and "wfs cs "
      and "lib_mt t (pc s t) ls cs  s"
      and "lock_acq t s ls cs s' ls' cs'"
      and "c_ops t s ls cs s' ls' cs'"
      and "lock_rel t s ls cs s' ls' cs'"
    shows "lib_mt t (pc s' t) ls' cs'  s'"
  using assms
  apply(simp add: lib_mt_def lock_acq_def c_ops_def lock_rel_def sn_ordered_val_def)
  apply(cases "pc s t", simp_all add: update_pc_def)
   apply(elim exE conjE)
    apply(subgoal_tac "my_ticket s' t = v", simp)
  apply(intro conjI)
      apply blast
  apply(simp add: lib_fetch_and_inc_step_def)
  using lib_update_enc_intro lib_update_step_def apply blast
  apply(simp add: lib_fetch_and_inc_step_def)
  using cvd_vw_val apply blast
  apply(cases "pc s' t", simp_all)
        apply auto[1]  
  apply (metis fun_upd_other lib_enc_read_pres)
      apply fastforce
  apply auto[1]  
  apply auto[1]  
  apply (metis fun_upd_apply lib_enc_read_pres)  
  using lib_enc_write_pres by blast

lemma lib_inv_m_t_global:
  assumes "lib_wfs ls cs" 
      and "thrdsvars"
      and "t \<noteq> t'"
      and "wfs cs "
      and "lib_mt t (pc s t) ls cs  s"
      and "lib_mt t' (pc s t') ls cs  s"
      and "lock_acq t' s ls cs s' ls' cs'"
      and "c_ops t' s ls cs s' ls' cs'"
      and "lock_rel t' s ls cs s' ls' cs'"
    shows "lib_mt t (pc s' t) ls' cs'  s'"
  using assms
  apply(simp add: lib_mt_def lock_acq_def c_ops_def lock_rel_def)
  apply(cases "pc s t"; cases "pc s t'";cases "pc s' t"; simp add: update_pc_def; elim exE conjE)
           apply(subgoal_tac "v = va", simp)
            apply(subgoal_tac "my_ticket s' t' = v", simp) 
  apply (meson f_a_i_cvd_pres less_add_one trans_less_add1)
  apply(simp add: lib_fetch_and_inc_step_def)  
  using cvd_vw_val apply blast
  using lib_cvd_exist_last_write apply blast
  apply (metis PC.distinct(1) assms(1) assms(4) fun_upd_apply fun_upd_idem lib_read_cvd_pres) 
                apply force 
  
                      apply force
  apply auto[3]
                      apply force
   apply (metis PC.distinct(5) assms(1) assms(2) assms(3) assms(4) lib_covered_write_diff_var_pres thrdsvars_def)
   apply force
                      apply(subgoal_tac "my_ticket s' t' = v")
  apply(intro conjI)
                      apply fastforce
  using lib_enc_f_a_i_pres apply blast
  apply(subgoal_tac "my_ticket s' t' = v")
  apply blast
  apply(subgoal_tac "my_ticket s' t' = v")
                      apply blast
  apply(simp add: lib_fetch_and_inc_step_def)
  using cvd_vw_val apply blast
                      apply auto[1]
  
  apply (metis PC.distinct(1) fun_upd_apply lib_enc_read_pres)
  apply auto[1]
   using update_pc_def apply auto[1] 
                       apply auto[2]  
   using lib_enc_write_pres apply blast

                       apply(subgoal_tac "my_ticket s' t' = v")
   
   using lib_enc_f_a_i_pres apply auto[1]
  apply(simp add: lib_fetch_and_inc_step_def)
  using cvd_vw_val apply blast
                      apply auto[2]  
  apply (metis PC.distinct(1) fun_upd_other lib_enc_read_pres)
                      apply auto[3]  
  using lib_enc_write_pres apply blast
                      apply(subgoal_tac "my_ticket s' t' = v")    
  using lib_enc_f_a_i_pres apply auto[1]
  apply(simp add: lib_fetch_and_inc_step_def) 
  using cvd_vw_val apply blast
                      apply auto[3]
  apply (metis PC.distinct(1) fun_upd_apply lib_enc_read_pres)
  apply auto[2]
  
  using lib_enc_write_pres apply blast
    apply(subgoal_tac "my_ticket s' t' = v")
  
  using lib_enc_f_a_i_pres apply auto[1]
                 apply(simp add: lib_fetch_and_inc_step_def)
  using cvd_vw_val apply blast
  apply auto[1]
  using update_pc_def apply auto[1]
              apply auto[2]  
  
  apply (metis PC.distinct(1) fun_upd_apply lib_enc_read_pres)
           apply auto[1]
  using lib_enc_write_pres apply blast
         apply(subgoal_tac "my_ticket s' t' = v") 
  
  using lib_enc_f_a_i_pres apply auto[1]

  apply(simp add: lib_fetch_and_inc_step_def)
  using cvd_vw_val apply blast  
  apply auto[1]  
  using update_pc_def apply auto[1]  
  apply auto[2]  
    apply auto[1]  
   apply (metis fun_upd_apply lib_enc_read_pres)
  using lib_enc_write_pres by blast
  
(****************************************)
definition "lib_main_inv t p ls cs  s \<equiv> 
     (case p of
          L1 \<Rightarrow>  [init lib(sn) 0] ls \<and> (my_ticket s t = 0)  \<and> (serving_now s t = 0) \<and> (sn_ordered_val ls)  \<and> (sn_ordered_ts ls) \<and> (\<exists> v . cvd[lib(nt), v] ls \<and> [lib(sn) = v]\<lparr>lib(sn) =\<^sub>t v\<rparr> ls \<and> [\<zero>lib(sn), (v+1)]\<^sub>0 ls) 
        | L2 \<Rightarrow>  [init lib(sn) 0] ls \<and> (my_ticket s t \<ge> 0)  \<and> (serving_now s t \<ge> 0) \<and> (sn_ordered_val ls) \<and> (sn_ordered_ts ls) \<and> ([lib(sn) = (my_ticket s t)]\<lparr>lib(sn) =\<^sub>t (my_ticket s t)\<rparr> ls) \<and> (\<exists> v . cvd[lib(nt), v] ls \<and> v > my_ticket s t) \<and>  [\<zero>lib(sn), Suc (my_ticket s t)]\<^sub>0 ls
        | CS \<Rightarrow>  [init lib(sn) 0] ls \<and> my_ticket s t \<ge> 0  \<and> (serving_now s t \<ge> 0) \<and> (my_ticket s t = serving_now s t) \<and> (sn_ordered_val ls)  \<and> (sn_ordered_ts ls)  \<and> ([lib(sn) =\<^sub>t (my_ticket s t)] ls) \<and> (en[lib(sn), (serving_now s t)]\<^sub>t ls)  \<and> (\<exists> v . cvd[lib(nt), v] ls \<and> v > my_ticket s t) \<and> [\<zero>lib(sn), Suc (serving_now s t)]\<^sub>0 ls
        | L3 \<Rightarrow>  [init lib(sn) 0] ls \<and> ([lib(sn) =\<^sub>t (my_ticket s t)] ls) \<and> (my_ticket s t = serving_now s t) \<and> (sn_ordered_val ls) \<and> (sn_ordered_ts ls) \<and> (en[lib(sn), (serving_now s t)]\<^sub>t ls)  \<and> (\<exists> v . cvd[lib(nt), v] ls \<and> v > my_ticket s t) \<and> [\<zero>lib(sn), Suc (serving_now s t)]\<^sub>0 ls
        | L4 \<Rightarrow>  [init lib(sn) 0] ls \<and> ([lib(sn) =\<^sub>t (my_ticket s t)] ls) \<and> (my_ticket s t = serving_now s t) \<and> (sn_ordered_val ls) \<and> (sn_ordered_ts ls) \<and> (en[lib(sn), (serving_now s t)]\<^sub>t ls)  \<and> (\<exists> v . cvd[lib(nt), v] ls \<and> v > my_ticket s t) \<and> [\<zero>lib(sn), Suc (serving_now s t)]\<^sub>0 ls
        | L5 \<Rightarrow>  [init lib(sn) 0] ls \<and> (sn_ordered_val ls) \<and> (sn_ordered_ts ls)
    )
"

lemma lib_inv_main_local:
  assumes "lib_wfs ls cs" 
      and "thrdsvars"
      and "wfs cs "
      and "lib_main_inv t (pc s t) ls cs  s"
      and "lock_acq t s ls cs s' ls' cs'"
      and "c_ops t s ls cs s' ls' cs'"
      and "lock_rel t s ls cs s' ls' cs'"
    shows "lib_main_inv t (pc s' t) ls' cs'  s'"
  using assms
  apply(simp add: lib_main_inv_def lock_acq_def c_ops_def lock_rel_def sn_ordered_val_def)
  apply(cases "pc s t", simp_all)
      apply(simp_all add: update_pc_def)
   apply(elim conjE exE)
   apply(subgoal_tac "v = my_ticket s' t") defer
  apply(simp add: lib_fetch_and_inc_step_def)
  using cvd_vw_val apply fastforce defer
  apply(intro conjI)
        apply auto[1]
       apply auto[1]
     apply(intro conjI)
  using lib_init_val_write_pres apply blast
       apply(simp add: sn_ordered_val_def)
    apply(intro allI impI)
    apply(case_tac "(a, b) \<in> lib_writes_on ls sn")
     apply(subgoal_tac "lib_value ls' (a, b) = lib_value ls (a, b)", simp)
      apply(elim conjE)
  apply(erule_tac x = a in allE)
      apply(erule_tac x = b in allE, simp)
      apply(elim exE)
  apply(rule_tac x=aa in exI)
      apply(rule_tac x=ba in exI)
  apply(case_tac "(aa, ba) \<in> lib_writes_on ls' sn", simp)
  using write_pres_value apply auto[1]
      apply(simp add: lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
  apply(simp add: lib_writes_on_def lib_value_def)
      apply auto[1]
  using write_pres_value apply auto[1]
    apply(simp add: lib_enc_t_def lib_enc_def, elim conjE exE)
    apply(subgoal_tac "lib_value ls' (a, b) = Suc (serving_now s t)", simp)
  apply(rule_tac x = aa in exI)
     apply(rule_tac x = ba in exI)
     apply(intro conjI)
      apply(simp add: lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
  apply(simp add: lib_writes_on_def lib_value_def)
      apply auto[1]
  using write_pres_value apply auto[1]
      apply(simp add: lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
  apply(simp add: lib_writes_on_def lib_value_def)
     apply blast
     apply(simp add: sn_ordered_ts_def)
     apply(intro conjI allI impI, elim conjE exE)
     apply(case_tac "(a, b)\<in>lib_writes_on ls sn \<and> (aa, ba)\<in>lib_writes_on ls sn")
  apply(subgoal_tac "lib_value ls' (a, b) = lib_value ls (a, b) \<and>
                 lib_value ls' (aa, ba) =  lib_value ls (aa, ba)")
      apply(elim conjE)
       apply simp
  using write_pres_value apply auto[1]
     apply simp
     apply(case_tac "(a, b) \<in> lib_writes_on ls sn", simp_all)
      apply(subgoal_tac " lib_value ls' (a, b) =  lib_value ls (a, b)", simp)
       apply(subgoal_tac "ba > b") 
        apply(subgoal_tac "lib_value ls' (aa, ba) = Suc (serving_now s' t)")
  apply(subgoal_tac "lib_value ls (a,b) \<le> serving_now s' t")
          apply linarith
  apply(subgoal_tac "sn_ordered_ts ls")
  using vals_smaller_d_obs_sn_order apply blast
  apply(simp add: sn_ordered_ts_def)
      apply(simp add: lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
        apply(simp add: lib_writes_on_def lib_value_def)
  apply auto[1]
       apply auto[1]
  using write_pres_value apply auto[1]
     apply(case_tac "(aa, ba) \<in> lib_writes_on ls sn")
      apply(simp add: lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
        apply(simp add: lib_writes_on_def )
  apply (smt dual_order.strict_implies_order dual_order.strict_trans less_imp_neq lib_dobs_visible_writes_last lib_valid_fresh_ts_def lib_visible_writes_def mem_Collect_eq ts_eq_lastWr ts_ge_last_is_last)
      apply(simp add: lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
     apply(simp add: lib_writes_on_def )
     apply blast
    apply auto[1]
    apply(intro conjI)
  using lib_init_val_fai_pres apply blast
    using sn_ordered_val_pres thrdsvars_def apply blast
  using sn_ordered_ts_pres thrdsvars_def apply blast
  using lib_c_obs_diff_var_fai_pres thrdsvars_def apply blast
  using f_a_i_cvd_pres apply fastforce
  apply(simp add: lib_fetch_and_inc_step_def)
  apply (metis lib_no_val_update_pres_diff_var_diff_val lib_update_step_def thrdsvars_def)
  apply(cases "pc s' t", simp_all)
      apply auto[1]
      apply(intro conjI)  
  using lib_init_val_read_pres apply blast
  using sn_ordered_val_read_pres apply blast
  using sn_ordered_ts_read_pres apply blast
   apply(elim conjE exE)
  apply(case_tac "my_ticket s' t = serving_now s' t", simp_all)
  using lib_c_obs_diff_var_read_pres apply blast    
  using lib_read_cvd_pres apply blast
  using lib_no_val_read_pres_diff_var apply blast
      apply auto[1]
  apply auto[1]
    apply auto[1]  
  apply(simp add: sn_ordered_val_def)
  apply(intro conjI)
  using lib_init_val_read_pres apply blast  
  apply auto[1]
      apply (metis lib_value_read_pres read_pres_writes_on_diff_var)
  using sn_ordered_ts_read_pres apply blast
   apply (metis PC.distinct(17) fun_upd_triv lib_c_obs_transfer)
  using lib_enc_read_intro apply blast
  using lib_read_cvd_pres apply blast  
  by (metis PC.distinct(17) fun_upd_same lib_no_val_read_pres_diff_var)

lemma lib_inv_main_global:
  assumes "lib_wfs ls cs" 
      and "thrdsvars"
      and "t \<noteq> t'"
      and "wfs cs "
      and "lib_mt t (pc s t) ls cs  s"
      and "lib_mt t' (pc s t') ls cs  s"
      and "lib_main_inv t (pc s t) ls cs  s"
      and "lib_main_inv t' (pc s t') ls cs  s"
      and "lock_acq t' s ls cs s' ls' cs'"
      and "c_ops t' s ls cs s' ls' cs'"
      and "lock_rel t' s ls cs s' ls' cs'"
    shows "lib_main_inv t (pc s' t) ls' cs'  s'"
  using assms
  apply(simp add:  lib_main_inv_def lock_acq_def c_ops_def lock_rel_def)
  apply(cases "pc s t"; cases "pc s t'"; cases "pc s' t", simp_all)
                      apply(simp_all add: update_pc_def; intro conjI impI; elim conjE exE)
  using lib_init_val_fai_pres apply blast
  using sn_ordered_val_pres thrdsvars_def apply blast
  using sn_ordered_ts_pres thrdsvars_def apply blast
  apply(subgoal_tac "my_ticket s'
     t' = va") 
                      apply(rule_tac x="Suc (my_ticket s'
     t')" in exI, intro conjI)
  using f_a_i_cvd_pres apply auto[1]
  apply (simp add: lib_c_obs_pres_fai_diff_var lib_not_pobs_cobs no_val_not_p_obs thrdsvars_def)
                      apply simp
                      apply(subgoal_tac "[\<zero>libsn, Suc (Suc va)]\<^sub>0 ls") 
                      apply(simp add: lib_fetch_and_inc_step_def)
                      apply (metis lib_no_val_update_pres_diff_var_diff_val lib_update_step_def n_not_Suc_n)
  using no_val_next_future apply blast
  apply(case_tac "v \<noteq> va", simp_all)
  using lib_cvd_exist_last_write apply blast
                      apply(simp add: lib_fetch_and_inc_step_def)
  using cvd_vw_val apply blast
                        apply(simp_all add: update_pc_def; intro conjI impI; elim conjE exE)
                      apply(simp_all add: update_pc_def; intro conjI impI; elim conjE exE)
                      apply(simp_all add: update_pc_def; intro conjI impI; elim conjE exE)
                      apply(simp_all add: update_pc_def; intro conjI impI; elim conjE exE)
                      apply(simp_all add: update_pc_def; intro conjI impI; elim conjE exE)
                      apply(simp_all add: update_pc_def; intro conjI impI; elim conjE exE)
     using lib_init_val_read_pres apply blast   
     using sn_ordered_val_read_pres apply blast   
     using sn_ordered_ts_read_pres apply blast   
     apply (meson lib_c_obs_diff_var_read_pres lib_no_val_read_pres_diff_var lib_read_cvd_pres)
                       apply(simp_all add: update_pc_def; intro conjI impI; elim conjE exE)
    using lib_init_val_read_pres apply blast   
    using sn_ordered_val_read_pres apply blast  
    using sn_ordered_ts_read_pres apply blast   
    using update_pc_def
                        apply auto[3]   
                        apply(simp_all add: update_pc_def; intro conjI impI; elim conjE exE)
   using lib_init_val_read_pres apply blast   
   using update_pc_def apply auto[1]    
   using sn_ordered_val_read_pres apply blast    
   using sn_ordered_ts_read_pres apply blast    
                       apply auto[3]
                    apply(simp_all add: update_pc_def; intro conjI impI; elim conjE exE)   
   using update_pc_def apply auto[1]   
   apply auto[1]
   using sn_ordered_val_read_pres apply blast  
   using sn_ordered_ts_read_pres apply blast
   apply auto[1]   
   apply (meson lib_init_val_read_pres sn_ordered_ts_read_pres sn_ordered_val_read_pres)
                    apply(simp_all add: update_pc_def; intro conjI impI; elim conjE exE)   
   apply simp+
  apply auto[1]
   apply(intro conjI)
   using lib_init_val_read_pres apply blast
   using sn_ordered_val_read_pres apply blast   
   using sn_ordered_ts_read_pres apply blast   
   apply(intro conjI)   
   using lib_init_val_read_pres apply blast
   using sn_ordered_val_read_pres apply blast
   using sn_ordered_ts_read_pres apply blast
                       apply(elim conjE exE)
                       apply(subgoal_tac "v = va", simp)
   apply(simp add: update_pc_def)
                       apply auto[1]
   using lib_cvd_exist_last_write apply blast
                       apply(elim conjE exE)
                       apply(subgoal_tac "v = va", simp)
    apply(simp add: update_pc_def)
  apply auto[1]
  using lib_cvd_exist_last_write apply blast
  apply (metis gr_implies_not_zero lib_read_cvd_pres neq0_conv)
    apply(simp_all add: update_pc_def)
                      apply auto[1]
   apply(intro conjI)   
  using lib_init_val_write_pres apply blast
  
  using sn_ordered_val_write_pres apply fastforce
  
                      apply (metis assms(1) sn_ordered_ts_write_pres)
                      apply(elim exE conjE)
  apply(subgoal_tac "v = va", simp)
                      defer  
  using lib_cvd_exist_last_write apply blast
   apply(intro conjI)   
  using lib_init_val_fai_pres apply blast  
  using sn_ordered_val_pres thrdsvars_def apply blast  
  using sn_ordered_ts_pres thrdsvars_def apply blast  
  using lib_c_obs_pres_fai_diff_var thrdsvars_def apply fastforce  
  apply (metis Suc_eq_plus1 assms(1) f_a_i_cvd_pres less_add_Suc1 less_imp_add_positive)
  apply(elim conjE exE)
                      apply(subgoal_tac "v = va", simp)
  apply(simp add: lib_fetch_and_inc_step_def)
  apply (metis (no_types, hide_lams) cvd_vw_val less_Suc_eq_0_disj less_irrefl_nat lib_no_val_update_pres_diff_var_diff_val lib_update_step_def)  
  using lib_cvd_exist_last_write apply blast  
  apply force
  apply (meson lib_c_obs_diff_var_read_pres lib_no_val_def lib_no_val_read_pres_diff_var lib_read_cvd_pres sn_ordered_ts_read_pres sn_ordered_val_read_pres)  
  apply auto[1]
  apply (metis PC.distinct(13) assms(3) fun_upd_apply fun_upd_idem_iff update_pc_def)  
  apply auto[1]
  apply (metis PC.distinct(17) assms(3) fun_upd_apply fun_upd_idem_iff update_pc_def)
  apply(elim conjE exE)
                      apply(subgoal_tac "v = va", simp)
  apply(intro conjI) 
  using lib_init_val_write_pres apply blast  
  using sn_ordered_val_write_pres apply blast  
  using sn_ordered_ts_write_pres apply blast
                      apply(subgoal_tac "my_ticket s' t \<ge> my_ticket s' t'") 
                      apply(simp add: lib_mt_def)
                      apply(subgoal_tac "serving_now s' t' <  my_ticket s' t") 
                      apply(subgoal_tac " [\<zero>libsn, my_ticket s' t]\<^sub>0 ls") 
  apply(case_tac "Suc (serving_now s' t') = my_ticket s' t", simp)
  apply (simp add: lib_c_obs_intro no_val_not_p_obs)
  apply (metis gr_implies_not0 lib_no_val_write_pres_diff_var_diff_val lib_not_pobs_cobs no_val_not_p_obs)
  using sn_ordered_d_obs_no_val apply blast
  using leI apply auto[1]
  apply (simp add: sn_d_obs_noval)  
  apply (metis assms(1) assms(2) assms(4) lib_covered_write_diff_var_pres thrdsvars_def)
                      apply(subgoal_tac "my_ticket s' t \<ge> my_ticket s' t'") 
                      apply(simp add: lib_mt_def)
                      apply(subgoal_tac "serving_now s' t' <  my_ticket s' t")   
  apply (simp add: lib_no_val_write_pres_diff_var_diff_val)  
  apply (simp add: le_neq_implies_less)  
  apply (simp add: sn_d_obs_noval)
                      apply(simp add: lib_write_step_def)
  using lib_cvd_exist_last_write apply blast
  apply(elim exE conjE, intro conjI)  
  using lib_init_val_fai_pres apply blast 
  apply (simp add: lib_d_obs_pres_fai_diff_var thrdsvars_def)  
  using sn_ordered_val_pres thrdsvars_def apply blast  
  using sn_ordered_ts_pres thrdsvars_def apply blast  
  using lib_enc_f_a_i_pres apply blast
                      apply(subgoal_tac "v = va")
                      apply(rule_tac x="Suc (my_ticket s' t')" in exI)
                      apply(intro conjI)
                      apply(subgoal_tac "v = my_ticket s' t'", clarsimp)
  using f_a_i_cvd_pres
                      apply auto[1]
  apply(simp add: lib_fetch_and_inc_step_def)
  
  using cvd_vw_val apply fastforce
                      apply(subgoal_tac "v = va", simp)
                      apply(subgoal_tac "serving_now s t \<le>  my_ticket s' t'")
  using less_Suc_eq_le apply blast
  apply(subgoal_tac "va = my_ticket s' t'", simp)
  apply(simp add: lib_fetch_and_inc_step_def)  
  using cvd_vw_val apply fastforce
  apply blast
  using lib_cvd_exist_last_write apply blast
  apply(simp add: lib_fetch_and_inc_step_def)  
  apply (metis (no_types, hide_lams) cvd_vw_val less_Suc_eq_0_disj less_irrefl_nat lib_no_val_update_pres_diff_var_diff_val lib_update_step_def)  
                      apply auto[1]
                      apply auto[1]
  apply(intro conjI)
  
  using lib_init_val_read_pres apply blast
  apply(elim conjE exE)
                      apply(subgoal_tac "v = va", simp)
                      defer
  using lib_cvd_exist_last_write apply blast   
  using sn_ordered_val_read_pres apply blast  
  using sn_ordered_ts_read_pres apply blast 
  using lib_enc_read_pres apply blast  
  apply (metis lib_read_cvd_pres)  
  using lib_no_val_read_pres_diff_var apply blast  
  apply auto[4]  
  apply(elim exE conjE, intro conjI)  
  using lib_init_val_write_pres apply blast
                      apply(subgoal_tac "my_ticket s' t' \<noteq> my_ticket s' t")
  using lib_d_obs_cont apply blast
  apply(simp add: lib_mt_def)
  apply auto[1]  
  apply (simp add: sn_ordered_val_write_pres)  
  apply (simp add: sn_ordered_ts_write_pres)  
  using lib_enc_write_pres apply blast  
                      apply (metis lib_covered_write_diff_var_pres thrdsvars_def)
  apply(simp add: lib_mt_def)
  using lib_d_obs_cont apply fastforce
  apply(elim exE conjE, intro conjI)
                      apply simp
  apply auto[1]
  apply(elim exE conjE)
  apply( intro conjI)
  using lib_init_val_fai_pres apply blast  
  apply (simp add: lib_d_obs_pres_fai_diff_var thrdsvars_def)  
  using sn_ordered_val_pres thrdsvars_def apply blast  
  using sn_ordered_ts_pres thrdsvars_def apply blast
  using lib_enc_f_a_i_pres apply blast  
  apply (metis Suc_eq_plus1 assms(1) assms(4) f_a_i_cvd_pres less_iff_Suc_add less_imp_add_positive)
  apply(simp add: lib_fetch_and_inc_step_def)
  apply (metis (no_types, hide_lams) cvd_vw_val less_Suc_eq_0_disj less_irrefl_nat lib_no_val_update_pres_diff_var_diff_val lib_update_step_def)
   apply force   
  apply auto[1]
  apply(elim exE conjE)
   apply (metis PC.distinct(19) assms(3) fun_upd_apply fun_upd_idem_iff update_pc_def)
  apply(elim exE conjE)
   apply( intro conjI)
  using lib_init_val_read_pres apply blast
  apply simp
   using lib_d_obs_pres_read apply blast
   using sn_ordered_val_read_pres apply blast
   using sn_ordered_ts_read_pres apply blast
   using lib_enc_read_pres apply blast
   apply (metis lib_read_cvd_pres)
   using lib_no_val_read_pres_diff_var apply blast
   apply auto[1]
   apply force
   apply auto[1]
   apply(simp add: lib_mt_def)
   apply (metis PC.distinct(5) lib_d_obs_cont)
   apply auto[1]
   apply (meson lib_init_val_fai_pres sn_ordered_ts_pres sn_ordered_val_pres thrdsvars_def)
   apply force
   apply auto[1]
   apply auto[1]
   apply auto[1]
   apply (meson lib_init_val_read_pres sn_ordered_ts_read_pres sn_ordered_val_read_pres)
   apply auto[1]
   apply (metis (full_types) assms(1) assms(4) lib_init_val_write_pres sn_ordered_ts_write_pres sn_ordered_val_write_pres)
   apply(elim exE conjE)
              apply( intro conjI)
   using lib_init_val_fai_pres apply blast
   using sn_ordered_val_pres thrdsvars_def apply blast
   using sn_ordered_ts_pres thrdsvars_def apply blast
   apply (simp add: lib_d_obs_pres_fai_diff_var thrdsvars_def)
   using lib_enc_f_a_i_pres apply blast
               apply(subgoal_tac "va = v", simp)
   apply(simp add: lib_mt_def)
                apply(simp add: lib_fetch_and_inc_step_def)
   apply (metis cvd_vw_val less_Suc_eq lib_cvd_update_pres lib_update_step_def)
   using lib_cvd_exist_last_write apply blast
                apply(simp add: lib_fetch_and_inc_step_def)
    apply (metis (no_types, hide_lams) cvd_vw_val less_Suc_eq_0_disj less_irrefl_nat lib_no_val_update_pres_diff_var_diff_val lib_update_step_def)
   using fun_upd_other apply auto[1]
            apply auto[1]
    apply force
   apply force
   apply force
   apply (metis assms(1) assms(4) lib_d_obs_pres_read lib_enc_read_pres lib_no_val_def lib_no_val_read_pres_diff_var lib_read_cvd_pres sn_ordered_ts_read_pres sn_ordered_val_read_pres)
    apply auto[1]
   apply(elim exE conjE)
      apply( intro conjI)
   using lib_init_val_write_pres apply blast
   apply (simp add: sn_ordered_val_write_pres)
          apply (simp add: sn_ordered_ts_write_pres)
   apply(simp add: lib_mt_def)
   using lib_d_obs_cont apply fastforce
   using lib_enc_write_pres apply blast
  apply (metis lib_covered_write_diff_var_pres thrdsvars_def)
   apply(simp add: lib_mt_def)
  using lib_d_obs_cont apply fastforce
    apply auto[1]
   apply(simp add: lib_mt_def)
   apply(case_tac "Suc (serving_now s' t') = v", simp)
  apply (metis  assms(1) assms(2) assms(3) assms(4)  lib_c_obs_intro lib_covered_write_diff_var_pres lib_no_val_write_pres_diff_var_diff_val n_not_Suc_n nat.discI  no_val_not_p_obs not0_implies_Suc old.nat.inject thrdsvars_def)
  apply (metis  assms(1) assms(2) assms(4) lessE less_irrefl_nat lib_covered_write_diff_var_pres lib_no_val_write_pres_diff_var_diff_val lib_not_pobs_cobs nat.discI no_val_not_p_obs not0_implies_Suc old.nat.inject sn_ordered_d_obs_no_val thrdsvars_def)
  using lib_d_obs_pres_read by blast


definition "invs t p ls cs s \<equiv> lib_mt t p ls cs  s \<and> lib_main_inv t p ls cs  s "

(*********** Pending ************)


definition "sn_distinct_vals ls \<equiv>  \<forall> w w' . w \<in> lib_writes_on ls sn \<and> w'\<in>lib_writes_on ls sn \<and>
                      lib_value ls w = lib_value ls w' \<longrightarrow> w = w'"

lemma lib_writes_on_write_simp: "lib_valid_fresh_ts ls w ts' \<Longrightarrow> w\<in>lib_writes_on ls x \<Longrightarrow> lib_writes_on (lib_write t b w v ls cs ts') x = lib_writes_on ls x  \<union> {(x, ts')} "
  apply(simp add: lib_write_def lib_writes_on_def lib_valid_fresh_ts_def all_updates_l var_def tst_def)
  using Collect_cong by auto


lemma lib_write_value_new_simp: "lib_valid_fresh_ts ls w ts' \<Longrightarrow> w\<in>lib_writes_on ls x \<Longrightarrow> lib_value (lib_write t b w v ls cs ts') (x,ts') = v "
  apply(simp add: lib_write_def lib_writes_on_def lib_valid_fresh_ts_def all_updates_l var_def tst_def lib_value_def)
  done

lemma lib_write_value_simp: "lib_valid_fresh_ts ls w ts' \<Longrightarrow> w\<in>lib_writes_on ls x \<Longrightarrow>\<forall> w'. w'\<in>lib_writes_on ls x \<longrightarrow> lib_value (lib_write t b w v ls cs ts') w' = lib_value ls w' "
  apply(simp add: lib_write_def lib_writes_on_def lib_valid_fresh_ts_def all_updates_l var_def tst_def lib_value_def)
  apply safe
  by auto

lemma lib_write_new_ts_simp: "lib_valid_fresh_ts ls w ts' \<Longrightarrow> w\<in>lib_writes_on ls x \<Longrightarrow> (x,z)\<notin>lib_writes_on ls x \<Longrightarrow> (x,z)\<in>lib_writes_on (lib_write t b w v ls cs ts') x \<Longrightarrow> z = ts'"
  apply(simp add: lib_write_def lib_writes_on_def lib_valid_fresh_ts_def all_updates_l var_def tst_def lib_value_def)
  done

lemma sn_distinct_vals_acq_inv:
  assumes "lib_wfs ls cs" 
      and "thrdsvars"
      and "wfs cs "
      and "sn_distinct_vals ls"
      and "invs t (pc s t) ls cs s"
      and "lock_acq t s ls cs s' ls' cs'"
      and "c_ops t s ls cs s' ls' cs'"
      and "lock_rel t s ls cs s' ls' cs'"
    shows "sn_distinct_vals ls'"
  using assms 
  apply(simp add: sn_distinct_vals_def)
  apply(intro allI conjI impI)
  apply(simp add: lib_writes_on_def)
  apply(cases "(pc s t)")
  apply(simp add: thrdsvars_def lock_acq_def invs_def lib_mt_def lib_main_inv_def, elim conjE exE)
  apply (metis f_a_i_pres_value lib_f_a_i_writes_on_diff_var_pres_backwards)
  apply(simp add: thrdsvars_def lock_acq_def invs_def lib_mt_def lib_main_inv_def, elim conjE exE)
  apply (metis lib_read_writes_on_diff_var_pres_backwards read_pres_value)
     apply(simp add: thrdsvars_def lock_rel_def invs_def lib_mt_def lib_main_inv_def, elim conjE exE)
    apply(simp add: thrdsvars_def lock_rel_def invs_def lib_mt_def lib_main_inv_def, elim conjE exE)
  defer
    apply(simp add: thrdsvars_def lock_rel_def invs_def lib_mt_def lib_main_inv_def, elim conjE exE)
    apply(simp add: thrdsvars_def  invs_def lib_mt_def lib_main_inv_def, elim conjE exE)
   apply(simp add: c_ops_def)
  apply(case_tac "(a, b) \<in> lib_writes_on ls sn \<and>
       (aa, ba) \<in> lib_writes_on ls sn")
   apply (metis write_pres_value)
  apply simp
  apply(case_tac "(a, b) \<in> lib_writes_on ls sn", simp_all)
   apply(simp add: lib_write_step_def)
   apply(elim exE conjE)
   apply(subgoal_tac "lib_value ls (ab, bb) = serving_now s' t")
    apply(simp add: lib_visible_writes_def)
    apply(simp add: lib_writes_on_write_simp)
    apply(elim conjE)
  apply(subgoal_tac "lib_value (lib_write t True (ab, bb) (Suc (serving_now s' t)) ls cs ts')
        (a, b) = lib_value ls (a,b)")
     apply (metis lib_write_value_new_simp no_val_no_value zero_less_Suc)
  using lib_write_value_simp
  apply blast
  using lib_dobs_visible_writes apply blast
    apply(simp add: lib_write_step_def)
   apply(elim exE conjE)
     apply(subgoal_tac "lib_value ls (ab, bb) = serving_now s' t")
  defer
  using lib_dobs_visible_writes apply blast
  apply(subgoal_tac "a = sn \<and> ab = sn \<and> aa = sn", simp)
   defer
  apply(unfold lib_writes_on_def var_def, clarify)[1]
   apply (metis a_is_x fst_eqD)
  apply(elim conjE)
  apply(subgoal_tac "b = ts'")
   defer
  apply(simp add: lib_visible_writes_def)
  using lib_write_new_ts_simp
  apply blast
  apply simp
  apply(subgoal_tac " lib_value
        (lib_write t True (sn, bb) (Suc (serving_now s' t)) ls cs ts')
        (sn, ts') = (Suc (serving_now s' t))")
   defer
  apply(simp add: lib_visible_writes_def)
   apply (metis lib_write_value_new_simp)
  apply(case_tac "(sn, ba)
       \<in> lib_writes_on ls sn")
  apply(subgoal_tac "lib_value
        (lib_write t True (sn, bb) (Suc (serving_now s' t)) ls cs ts')
        (sn, ba) = lib_value ls (sn, ba)")
   defer
    apply(simp add: lib_visible_writes_def)
  apply (metis lib_write_value_simp)
   defer
   apply (metis Suc_n_not_le_n vals_smaller_d_obs_sn_order)
  apply(subgoal_tac "ba = ts'") defer
    apply(simp add: lib_visible_writes_def)  
  using lib_write_new_ts_simp apply blast  
  by linarith


definition "exist_nt_for_sn cl  \<equiv> \<forall> wsn .  wsn\<in>lib_writes_on cl sn \<longrightarrow> (\<exists> wnt . wnt\<in>lib_writes_on cl nt  \<and> lib_value cl wnt = lib_value cl wsn)"

lemma exist_nt_for_sn_inv:
  assumes "lib_wfs ls cs" 
      and "thrdsvars"
      and "wfs cs "
      and "nt_all_cvd_but_last ls"
      and "exist_nt_for_sn ls"
       and "invs t (pc s t) ls cs s"
     and "lock_acq t s ls cs s' ls' cs'"
      and "c_ops t s ls cs s' ls' cs'"
      and "lock_rel t s ls cs s' ls' cs'"
    shows "exist_nt_for_sn ls'"
  using assms
  apply(simp add: thrdsvars_def exist_nt_for_sn_def  invs_def lib_mt_def lib_main_inv_def)
  apply(cases "pc s t"; simp; elim exE conjE)
  apply(simp add: lock_acq_def)
       apply (metis f_a_i_pres_value lib_f_a_i_writes_on_diff_var_pres_backwards lib_w_in_writes_f_a_i_pres)
  apply(simp add: lock_acq_def)
      apply (metis lib_read_writes_on_diff_var_pres_backwards read_pres_value)
     apply(simp add: lock_rel_def)
  defer
  apply(simp add: lock_rel_def)
   apply(simp add: c_ops_def)
  apply(intro allI impI)
  apply(simp add: lock_rel_def)
  apply(case_tac " (a, b) \<in> lib_writes_on ls sn")
   apply(subgoal_tac "lib_value ls' (a, b) = lib_value ls (a, b)", simp)
    defer
  using write_pres_value apply auto[1]
  defer
      apply(erule_tac x = a in allE)
    apply(erule_tac x = b in allE)
  apply simp
  apply (metis write_pres_value write_writes_on_diff_var)
  apply(simp add: lib_enc_t_def lib_enc_def)
  apply(elim exE conjE)
  apply(rule_tac x = aa in exI)
  apply(rule_tac x = ba in exI)
  apply(intro conjI)
  using write_writes_on_diff_var apply auto[1]
  apply(subgoal_tac "lib_value ls' (aa, ba) = lib_value ls (aa, ba)")
  apply(subgoal_tac "lib_value ls' (a, b) = Suc (serving_now s' t)")
    apply linarith
  apply(simp add: lib_write_step_def lib_write_def all_updates_l, elim exE conjE)
  apply (metis less_not_refl3 lib_cvd_exist_last_write lib_dobs_visible_writes nt_all_cvd_but_last_def)
  using write_pres_value by auto


definition "global ls  \<equiv>  previous_versions ls \<and>
                          nt_ns_gt_zero ls \<and>
                          nt_all_cvd_but_last ls \<and>
                          nt_order ls \<and>
                          nt_order_ts ls \<and>
                          sn_ordered_val ls \<and>
                          sn_ordered_ts ls \<and>
                          sn_distinct_vals ls \<and>
                          thrdsvars \<and>
                          exist_nt_for_sn ls"


lemmas globals = global_def previous_versions_def
nt_ns_gt_zero_def  thrdsvars_def

(*******************mutex**************************)

definition "mutex1 s t t' \<equiv>  pc s t \<in> {CS,L3,L4} \<and> pc s t' = CS \<longrightarrow> t = t'"
definition "mutex2 s t t' \<equiv>  pc s t \<in> {CS,L3,L4} \<and> t \<noteq> t' \<longrightarrow> pc s t'\<in> {L1, L2, L5}"

lemma "mutex2 s t t' \<Longrightarrow> mutex1 s t t'"
  using mutex2_def mutex1_def 
  by (smt PC.distinct(17) PC.distinct(29) PC.distinct(9) emptyE insert_iff)


lemma mutex: "lib_wfs ls cs \<Longrightarrow> t\<noteq>t' \<Longrightarrow>
              invs t (pc s t) ls cs s \<Longrightarrow> 
              invs t' (pc s t') ls cs s \<Longrightarrow>
              mutex2 s t t'"
  apply(simp add: invs_def mutex2_def lib_main_inv_def lib_mt_def)
  apply(intro conjI allI impI, elim disjE conjE, simp_all)
    apply(cases "pc s t'", simp_all)
      apply(elim conjE exE)
  apply(subgoal_tac "my_ticket s t' \<noteq> my_ticket s t")
  using lib_d_obs_cont apply blast
  apply auto[1]
  using lib_d_obs_cont apply fastforce
  using lib_d_obs_cont apply fastforce
    apply(cases "pc s t'", simp_all)
  using lib_d_obs_cont apply fastforce
  using lib_d_obs_cont apply fastforce
  using lib_d_obs_cont apply fastforce
    apply(cases "pc s t'", simp_all)
  using lib_d_obs_cont apply fastforce
  using lib_d_obs_cont apply fastforce
  using lib_d_obs_cont by fastforce

(**************************************************)


(*Proof of refinement*)

(*
cc = concrete client state
ac = abstract client state
al = abstract lock state
cl = concrete lock state
*)

definition "writes_rel al cl s t \<equiv> \<forall> wnt wsn .  (wnt\<in>lib_writes_on cl nt \<and>
                                            wsn\<in>lib_visible_writes cl t sn
                                           \<and> ((lib_value cl wnt) = ((lib_value cl wsn))) \<and>
                                            pc s t \<in> {L1, L2, L5}) \<longrightarrow> 
                                            (\<exists> wl . wl\<in>lib_visible_writes al t l \<and> even (lib_value al wl) \<and> wl \<notin> lib_covered al
                                            \<and> lib_modView cl wsn CVARS = lib_modView al wl CVARS \<and> lib_releasing cl wsn = lib_releasing al wl )"

definition "writes_rel_odd al cl s t \<equiv> \<forall> wnt wsn .  (wnt\<in>lib_writes_on cl nt \<and>
                                            wsn\<in>lib_visible_writes cl t sn
                                           \<and> ((lib_value cl wnt) \<noteq> ((lib_value cl wsn))) \<and>
                                              pc s t \<in> {CS, L3, L4}) \<longrightarrow> 
                                            (\<exists> wl . wl\<in>lib_visible_writes al t l \<and> odd (lib_value al wl) \<and> wl \<notin> lib_covered al
                                            \<and> lib_modView cl wsn CVARS = lib_modView al wl CVARS )"


definition "client_ref_rel t ac cc \<equiv> \<forall> x . tst (thrView cc t x) \<ge>  tst (thrView ac t x) \<and>
                                writes ac = writes cc \<and> modView ac = modView cc \<and>
                                covered ac = covered cc \<and> mods ac = mods cc "

lemma "ac = cc \<Longrightarrow> client_ref_rel t ac cc"
  by (simp add: client_ref_rel_def)



definition lib_ref_rel :: "lib_state \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> surrey_state \<Rightarrow> T \<Rightarrow> prog_state \<Rightarrow> bool"
  where "lib_ref_rel al cl ac cc t s  \<equiv> writes_rel al cl s t \<and> writes_rel_odd al cl s t \<and> client_ref_rel t ac cc"
definition "w_f_s ac cc al cl \<equiv> wfs cc \<and> wfs ac \<and> lib_wfs al ac \<and> lib_wfs cl cc"
definition "invariants al cl ac cc t s \<equiv> abslock_invs al l \<and> global cl \<and> invs t (pc s t) cl cc s"


lemmas [simp] = w_f_s_def invariants_def lib_ref_rel_def global_def

lemma refinement_step_lock_acquire_successful:
  assumes "w_f_s ac cc al cl"  
      and "invariants al cl ac cc t s"
      and "lib_ref_rel al cl ac cc t s"
      and "pc s t = L2"
      and "my_ticket s' t = serving_now s' t"
      and "lock_acq t s cl cc s' cl' cc'"      
    shows "\<exists> al' ac' ver  . [ac al t LOCKACQ(l) ac' al' True  ver] \<and> lib_ref_rel al' cl' ac' cc' t  s'"
  using assms
  apply(simp add:  lock_acquire_step_def   lock_acq_def invs_def lib_mt_def lib_main_inv_def)
  apply(elim conjE exE)
  apply(subgoal_tac "[lib(sn) \<approx>\<^sub>t (serving_now s' t)] cl'")
   defer
  using lib_p_obs_read apply blast
  apply(subgoal_tac " en[libnt,  (serving_now s' t)]\<^sub>t cl")
   defer
   apply(simp add: previous_versions_def lib_enc_t_def lib_enc_def, elim exE conjE)
  apply(erule_tac x = a in allE)
   apply(erule_tac x = b in allE)
   apply simp
   apply(elim conjE exE)
   apply(simp add: nt_order_ts_def)
   apply(subgoal_tac "ba < b") 
  apply(rule_tac x = "aa" in exI)
    apply(rule_tac x = "ba" in exI)
    apply(simp add: tst_def)
   apply (metis lessI)

     apply(simp add: writes_rel_def)
   apply(simp add: lib_p_obs_def lib_enc_t_def lib_enc_def, elim exE conjE)
  apply(erule_tac x = "ab" in allE)
  apply(erule_tac x = "bb" in allE)
  apply(erule_tac x = "aa" in allE)
  apply(erule_tac x = "aa" in allE)
  apply(erule_tac x = "aa" in allE)
     apply(erule_tac x = "ba" in allE)
     apply simp
     apply(subgoal_tac "(aa, ba) \<in> lib_visible_writes cl t sn", simp) 
      apply(subgoal_tac "lib_value cl' (aa, ba) =  lib_value cl (aa, ba)", simp)
       apply(elim exE conjE)
    defer
  apply(simp add: lib_visible_writes_def)  
  using lib_value_read_pres apply blast
  using lib_read_visible_writes_pres_backwards apply blast
    apply(subgoal_tac "\<exists> ts' . lib_valid_fresh_ts al (aca, bc) ts'")
        apply(elim exE conjE)
   defer
  apply(simp add: lib_visible_writes_def)  
  using exist_lib_valid_fresh_ts apply blast

  apply(rule_tac x = "if  (lib_releasing al (aca, bc)) then
         al
        \<lparr>lib_thrView := (lib_thrView al)
           (t := ts_oride
                  ((lib_thrView al t)(aca := (aca, ts')))
                  (lib_modView al (aca, bc) LVARS)),
           lib_modView := (lib_modView al)
             ((aca, ts') := (lib_modView al (aca, ts'))
                (CVARS :=
                   ts_oride (thrView ac t)
                    (lib_modView al (aca, bc) CVARS),
                 LVARS :=
                   ts_oride
                    ((lib_thrView al t)
                     (aca := (aca, ts')))
                    (lib_modView al (aca, bc) LVARS))),
           lib_mods := (lib_mods al)
             ((aca, ts') :=
                \<lparr>lib_val = Suc (lib_value al (aca, bc)),
                   lib_rel = True\<rparr>),
           lib_writes :=
             insert (aca, ts') (lib_writes al),
           lib_covered :=
             insert (aca, bc) (lib_covered al)\<rparr> else
         al
        \<lparr>lib_thrView := (lib_thrView al)
           (t := (lib_thrView al t)(aca := (aca, ts'))),
           lib_modView := (lib_modView al)
             ((aca, ts') := (lib_modView al (aca, ts'))
                (CVARS := thrView ac t,
                 LVARS := (lib_thrView al t)
                   (aca := (aca, ts')))),
           lib_mods := (lib_mods al)
             ((aca, ts') :=
                \<lparr>lib_val = Suc (lib_value al (aca, bc)),
                   lib_rel = True\<rparr>),
           lib_writes :=
             insert (aca, ts') (lib_writes al),
           lib_covered :=
             insert (aca, bc) (lib_covered al)\<rparr>" in exI)
  apply(rule_tac x = "if lib_releasing al (aca, bc) then ac
        \<lparr>thrView := (thrView ac)
           (t := ts_oride (thrView ac t)
                  (lib_modView al (aca, bc) CVARS))\<rparr> else  ac" in exI)
  apply(intro conjI)
  apply(rule_tac x = "lib_value al (aca, bc)" in exI)
  apply(rule_tac x = "aca" in exI)
       apply(rule_tac x = "bc" in exI)
  apply(intro conjI)
  apply blast  
        apply blast
      apply(rule_tac x = "ts'" in exI)
  apply(intro conjI)
            apply blast
  apply(simp add: lock_acquire_def lib_update_def all_updates_l)
  apply(simp add: lock_acquire_def lib_update_def all_updates_l)
      apply(simp add: lock_acquire_def lib_update_def all_updates_l)
     apply(simp add: lock_acquire_def lib_update_def all_updates_l lib_value_def)
    apply(simp add: update_pc_def)
   apply(simp add: writes_rel_odd_def)
   apply(intro conjI)
  apply(case_tac "lib_releasing al (aca, bc)", simp_all)
    apply(simp add: update_pc_def)
  apply(subgoal_tac "lib_writes_on cl' nt = lib_writes_on cl nt \<and>
                     (aa, ba) \<in> lib_visible_writes cl t sn  \<and> (\<forall> w' x . w'\<in>lib_writes_on cl' x \<longrightarrow> lib_value cl' w' = lib_value cl w')", simp)
     apply(intro allI impI, elim conjE)

  apply(rule_tac x = aca in exI) 
     apply(rule_tac x = ts' in exI) 
     apply simp
     apply(intro conjI)
  apply(simp add: lib_visible_writes_def)
     apply(intro conjI)
           apply(simp add: lib_writes_on_def)
          apply(simp add: tst_def ts_oride_def)
          apply (subgoal_tac "aca = l", simp)
           apply(subgoal_tac "snd (lib_modView al (l, bc) LVARS l) = bc", simp)
  apply(simp add: lib_valid_fresh_ts_def)
  apply(subgoal_tac "lib_modView al (l, bc) LVARS l = (l,bc)",simp)
           apply(simp add: lib_wfs_def)
           apply (simp add: lib_writes_on_def)   
  apply (simp add: lib_writes_on_def)
         apply(simp add: lib_value_def)
        apply(simp add: lib_valid_fresh_ts_def)
       apply(subgoal_tac "(aca, ts')\<notin>lib_writes al")
  apply(simp add: lib_wfs_def lib_writes_on_def lib_visible_writes_def)
        apply (metis order.strict_iff_order psubsetD)
  using fresh_ts_not_in_writes apply blast
  apply(simp add: lib_read_step_def lib_read_def all_updates_l, elim exE conjE)
      apply(case_tac "lib_syncing cl (af, bf) True", simp_all)
  apply(subgoal_tac "a = nt \<and> ab = nt \<and> aa = sn \<and> aca = l \<and> ad = nt \<and> ae = sn \<and> af = sn", simp)
        apply(simp add: client_ref_rel_def)
        apply(elim conjE)
       apply(simp add:lib_wfs_def)
  apply(simp add: lib_d_obs_def lib_c_obs_lib_only_def )
  apply (metis assms(1) less_not_refl3 lib_cvd_exist_last_write lib_wfs_def nt_all_cvd_but_last_def w_f_s_def)
       apply(simp add: lib_visible_writes_def lib_writes_on_def)
  apply(simp add:lib_wfs_def)
     apply (simp add: lib_c_obs_lib_only_def lib_syncing_def)
  apply(intro conjI)
  using read_pres_writes_on_diff_var apply blast
  apply(simp add: lib_read_step_def lib_read_def all_updates_l, elim exE conjE)
    apply (intro allI impI, elim exE)
    apply(case_tac " lib_syncing cl (ad, bd) True", simp_all)
  apply(simp add: lib_value_def)
  apply(simp add: lib_value_def)
   apply (simp add: lib_c_obs_lib_only_def)
  apply(simp add: client_ref_rel_def)
  apply(case_tac "lib_releasing al (aca, bc)", simp_all)
  apply(intro conjI allI impI)
  defer
  apply(simp add: lib_read_step_def lib_read_def all_updates_l, elim exE conjE)
  apply(case_tac "lib_syncing cl (ad, bd) True", simp_all)
  apply(simp add: lib_read_step_def lib_read_def all_updates_l, elim exE conjE)
      apply(case_tac "lib_syncing cl (ad, bd) True", simp_all)
  apply(simp add: lib_read_step_def lib_read_def all_updates_l, elim exE conjE)
     apply(case_tac "lib_syncing cl (ad, bd) True", simp_all)
  apply(simp add: lib_read_step_def lib_read_def all_updates_l, elim exE conjE)
    apply(case_tac "lib_syncing cl (ad, bd) True", simp_all)
  apply(intro conjI allI impI)
  defer
  apply(simp add: lib_read_step_def lib_read_def all_updates_l, elim exE conjE)
  apply(case_tac "lib_syncing cl (ad, bd) True", simp_all)
  apply(simp add: lib_read_step_def lib_read_def all_updates_l, elim exE conjE)
      apply(case_tac "lib_syncing cl (ad, bd) True", simp_all)
  apply(simp add: lib_read_step_def lib_read_def all_updates_l, elim exE conjE)
     apply(case_tac "lib_syncing cl (ad, bd) True", simp_all)
    apply(simp add: lib_read_step_def lib_read_def all_updates_l, elim exE conjE)
  using lib_c_obs_lib_only_def apply blast
  defer
  apply(simp add: lib_read_step_def lib_read_def all_updates_l, elim exE conjE)
  apply (simp add: lib_c_obs_lib_only_def)
  apply(simp add: lib_read_step_def lib_read_def all_updates_l lib_wfs_def, elim exE conjE)
  apply(simp add: lib_c_obs_lib_only_def lib_cvd_exist_last_write lib_d_obs_def)
  apply (metis assms(1) less_not_refl3 lib_cvd_exist_last_write lib_wfs_def nt_all_cvd_but_last_def w_f_s_def)
  done


lemma stuttering_step_lock_acquire_not_successful:
  assumes "w_f_s ac cc al cl"  
      and "invariants al cl ac cc t s"
      and "lib_ref_rel al cl ac cc t s"
      and "pc s t = L2"
      and "my_ticket s' t \<noteq> serving_now s' t"
      and "lock_acq t s cl cc s' cl' cc'"      
    shows "lib_ref_rel al cl' ac cc' t  s' \<and> client_ref_rel t ac cc'"
  using assms
  apply(simp add:  lock_acquire_step_def  lock_acq_def invs_def lib_mt_def lib_main_inv_def)
  apply(elim conjE exE, intro conjI)
    apply(simp add: writes_rel_def update_pc_def)
    apply(intro conjI impI allI)
    apply(subgoal_tac "lib_writes_on cl' nt = lib_writes_on cl nt \<and>
                       (aa, ba) \<in> lib_visible_writes cl t sn \<and>
      lib_value cl' (a, b) = lib_value cl' (a, b) \<and> lib_value cl' (aa, ba) = lib_value cl (aa, ba) \<and> lib_modView cl' = lib_modView cl
\<and> lib_releasing cl' (aa, ba) = lib_releasing cl (aa, ba)")
     apply simp
     apply (metis a_is_x numeral_2_eq_2 read_pres_value)
    apply(intro conjI)
  apply (simp add: read_pres_writes_on_diff_var)
        apply (meson lib_read_visible_writes_pres_backwards) 
       apply linarith
  apply(simp add:  lib_visible_writes_def)    
  apply (metis read_pres_value read_pres_writes_on_diff_var)
     apply(simp add: lib_read_step_def lib_read_def all_updates_l)
     apply(elim exE conjE)
  apply(case_tac "lib_syncing cl (ab, bb) True", simp_all)
   apply(simp add:  lib_visible_writes_def)    
     apply(simp add: lib_read_step_def lib_read_def all_updates_l lib_releasing_def)
     apply(elim exE conjE)
    apply(case_tac "lib_syncing cl (ab, bb) True", simp_all)
   apply(simp add: writes_rel_odd_def update_pc_def)
  apply(simp add: client_ref_rel_def lib_wfs_def)
     apply(simp add: lib_read_step_def lib_read_def all_updates_l lib_releasing_def)
  apply(elim exE conjE, intro conjI)
  apply(case_tac "lib_syncing cl (a, b) True",simp_all)
  apply(intro conjI allI impI)
  apply(simp add: lib_visible_writes_def)
   apply(simp add: lib_c_obs_lib_only_def lib_cvd_exist_last_write lib_d_obs_def ts_oride_def)
  by (metis diff_mono diff_self le_iff_diff_le_0)


lemma stuttering_step_fetch_and_inc:
  assumes "w_f_s ac cc al cl"  
      and "invariants al cl ac cc t s"
      and "lib_ref_rel al cl ac cc t s"
      and "pc s t = L1"
      and "lock_acq t s cl cc s' cl' cc'"      
    shows "lib_ref_rel al cl' ac cc' t  s' \<and> client_ref_rel t ac cc'"
  using assms
  apply(simp add:  lock_acquire_step_def  lock_acq_def invs_def lib_mt_def lib_main_inv_def)
  apply(elim conjE exE, intro conjI)
     apply(simp add: writes_rel_def)
  apply(intro allI impI)
   apply(elim conjE exE)
    apply(simp add: update_pc_def)
     apply(subgoal_tac "(aa, ba) \<in> lib_visible_writes cl t sn  \<and>
              lib_value cl' (aa, ba)=lib_value cl (aa, ba)
\<and>  lib_modView cl' (aa, ba) CVARS  =  lib_modView cl (aa, ba) CVARS \<and> lib_releasing cl' (aa, ba) = lib_releasing cl (aa, ba)")
     apply(case_tac "(a, b) \<in> lib_writes_on cl nt")
  apply(subgoal_tac " lib_value cl' (a, b) = lib_value cl (a, b)")
       apply force
  using f_a_i_pres_value apply auto[1]
  apply(elim conjE)
      apply(subgoal_tac "v = va", simp)
       apply(subgoal_tac "va = my_ticket s' t", simp)
       apply(subgoal_tac "lib_value cl (aa, ba) \<noteq>  Suc (my_ticket s' t)")
  apply(subgoal_tac "lib_value cl' (a, b) = Suc (my_ticket s' t) ")
         apply linarith
        apply(simp add: lib_fetch_and_inc_step_def lib_visible_writes_def)
        apply(elim conjE exE)
  apply(simp add:lib_update_def all_updates_l lib_writes_on_def lib_value_def)
        apply auto[1]
  apply(simp add: lib_visible_writes_def)
  using no_val_no_value apply blast
        apply(simp add: lib_fetch_and_inc_step_def)
  apply (metis cvd_vw_val)
     apply (metis lib_cvd_exist_last_write)
  apply(intro conjI)
  apply (metis a_is_x lib_f_a_i_writes_on_diff_var_pres thrdsvars_def)
  apply(simp add: lib_visible_writes_def)
  apply (metis f_a_i_pres_value f_a_i_pres_writes_on_diff_var thrdsvars_def)
  apply(simp add: lib_visible_writes_def)
        apply(simp add: lib_fetch_and_inc_step_def)
  apply(simp add:lib_update_def all_updates_l lib_writes_on_def lib_value_def)
     apply(elim conjE exE)
  apply(case_tac "lib_releasing cl (ab, bb)", simp_all)
  apply (metis a_is_x thrdsvars_def)
     apply (metis a_is_x thrdsvars_def)
  apply(simp add: lib_visible_writes_def)
        apply(simp add: lib_fetch_and_inc_step_def)
  apply(simp add:lib_update_def all_updates_l lib_writes_on_def lib_value_def lib_releasing_def)
     apply(elim conjE exE)
  apply(case_tac "lib_releasing cl (ab, bb)", simp_all)
  apply (metis a_is_x thrdsvars_def)
  apply (metis a_is_x thrdsvars_def)
   apply(simp add: writes_rel_odd_def update_pc_def)
  apply(simp add: client_ref_rel_def)
        apply(simp add: lib_fetch_and_inc_step_def)
  apply(simp add:lib_update_def all_updates_l lib_writes_on_def lib_value_def lib_releasing_def)
  apply(elim conjE exE)
  apply(intro conjI allI impI)
  apply(case_tac "lib_rel (lib_mods cl (a, b))", simp_all)
  apply(simp add: ts_oride_def)
  apply (smt order.trans )
  done
(*************Release Operation Refinement**************)


lemma refinement_step_release:
  assumes "w_f_s ac cc al cl"  
      and "invariants al cl ac cc t s"
      and "lib_ref_rel al cl ac cc t s"
      and "pc s t = L4"
      and "lock_rel t s cl cc s' cl' cc'"      
    shows "\<exists> al' ac'  . [ac al t LOCKREL(l) al' ac'] \<and>  lib_ref_rel al' cl' ac' cc' t s'"
  using assms
  apply(simp add: lock_rel_def update_pc_def lock_release_step_def)
  apply(elim exE conjE)
  apply(simp add: invs_def lib_mt_def lib_main_inv_def, elim conjE exE)
  apply(subgoal_tac "\<exists> a b . (a,b)\<in>lib_visible_writes cl t sn \<and> lib_value cl (a,b) = serving_now s' t")
   apply(simp add: lib_enc_t_def lib_enc_def writes_rel_odd_def, elim conjE exE)
  apply(erule_tac x = a in allE)
  apply(erule_tac x = b in allE)
  apply(erule_tac x = ab in allE)
  apply(erule_tac x = ab in allE)
   apply(erule_tac x = bb in allE)
   apply simp
  apply(elim exE conjE)
   defer
  apply(simp add: lib_write_step_def)
   apply (metis lib_dobs_visible_writes)
  apply(subgoal_tac " \<exists>ts'. lib_valid_fresh_ts al (aca, bc) ts'")
   defer
  apply(simp add: lib_visible_writes_def)
  using exist_lib_valid_fresh_ts apply blast
  apply(elim exE conjE)
  apply(rule_tac x ="al
       \<lparr>lib_thrView := (lib_thrView al)
          (t := (lib_thrView al t)(aca := (aca, ts'))),
          lib_modView := (lib_modView al)
            ((aca, ts') := (lib_modView al (aca, ts'))
               (CVARS := thrView ac t,
                LVARS := (lib_thrView al t)(aca := (aca, ts')))),
          lib_mods := (lib_mods al)
            ((aca, ts') :=
               \<lparr>lib_val = Suc (lib_value al (aca, bc)),
                  lib_rel = True\<rparr>),
          lib_writes := insert (aca, ts') (lib_writes al)\<rparr>" in exI)
  apply(rule_tac x = ac in exI)
  apply(intro conjI)
  apply(rule_tac x = aca in exI)
    apply(rule_tac x = bc in exI)
    apply(intro conjI)
      apply blast
     apply blast
  apply(rule_tac x = ts' in exI)
    apply(intro conjI)
      apply blast
     apply(simp add: lock_release_def lib_write_def all_updates_l)
    apply simp
   apply(simp add: writes_rel_def)
   apply(intro allI impI, elim conjE)
  apply(rule_tac x = aca in exI)
  apply(rule_tac x = ts' in exI)
   apply simp
   apply(intro conjI)
       apply(simp add: lib_visible_writes_def lib_writes_on_def) 
  apply(simp add: lib_value_def)
  apply (metis less_not_refl3 lib_cvd_exist_last_write lib_dobs_visible_writes_last lib_write_step_def nt_all_cvd_but_last_def)
   apply (metis lib_cvd_exist_last_write lib_dobs_visible_writes_last lib_write_step_def nat_neq_iff nt_all_cvd_but_last_def)
    apply(simp add: lib_releasing_def) 
  apply (metis lib_cvd_exist_last_write lib_dobs_visible_writes_last lib_write_step_def nat_neq_iff nt_all_cvd_but_last_def)
  apply(simp add: client_ref_rel_def)
  apply(intro conjI allI impI)
  apply (metis lib_write_step_def)    
  apply (metis lib_write_step_def)
  apply (metis lib_write_step_def)
  apply (metis lib_write_step_def)
  by (metis lib_write_step_def)

end
