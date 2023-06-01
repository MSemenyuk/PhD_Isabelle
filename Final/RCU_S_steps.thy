theory RCU_S_steps
  imports RCU_model
begin


(*datatype PC = I1 | I2 | I3 | I4 | I5 | I6 | I7 | I8 | I9 | I10 | I11 | I12 | I13 | I14 |  cas_res | finished
            | R1 | R2 | R3 | R4 | R5 
            | S1 | S2 | S3 | S4 | S5 | S6 | S7 *)



(*
(\<forall> x. lastWr \<sigma> x \<notin> covered \<sigma>)"
*)

(*the following must be included in the proof:

con_assms ps                            assumed         --- concerns allocation/bounds of C and rcu_0+i for all i

main_inv ms                             *done*          --- main invariant has 3 parts
psem_rules ps                           *done*          --- how allocation works on the inside
allocated_addresses ms ps               *done*          --- allocation for above are defined here
simple - observation_inv_ms ms          *done*          --- how own\<^sub>W affects loc status (own\<^sub>W loc = t \<longrightarrow> loc\<in>{s,n,det} t)
hard   - observation_inv_sig ms ps \<sigma>    *done*          --- limits which values can be WM_read from C
simple - own\<^sub>W_n_by_t_imp ms             *done*          --- related own\<^sub>W of n to n_dec and n (value)
tedious - general_structure ms          *done*          --- says how n \<noteq> s \<noteq> detaddrs
local - preCond ms ps (pc ms t) t     *done*          --- defines preconditions for t to proceed with stepping      
global - preCond ms ps (pc ms ta) ta  *done*          --- defines preconditions for t to proceed with stepping      

block_cond weak memory                  *done (wm_proofs)*
det_block weak memory (t)               *done*
det_block weak memory (ta)              *done (wm_proofs)*



*)






(***************done***************)






lemma showing_main_inv_1_for_S:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> S_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  main_inv_1 ms'"
  apply (simp, safe; clarsimp)
  apply(simp_all add:main_inv_1_def step_def setup_r_def)
  apply (metis main_inv_1_def main_inv_def option.distinct(1))
  apply(simp add:preCond_def)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all add:abbr)
  apply (simp add: main_inv_1_def main_inv_def)
  apply (simp add: main_inv_1_def main_inv_def)
  apply (simp add: main_inv_1_def main_inv_def)
  apply (simp add: main_inv_1_def main_inv_def)
  apply(simp add:preCond_def OpSem.step_def general_structure_def)
  apply clarify apply auto
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)
  apply (metis main_inv_1_def main_inv_def option.discI option.sel singletonD)
  apply (metis main_inv_1_def main_inv_def option.distinct(1) option.sel singleton_iff)
  apply (metis Set.set_insert main_inv_1_def main_inv_def option.discI option.sel singleton_insert_inj_eq)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)
  apply (metis main_inv_1_def main_inv_def option.discI option.sel singletonI)
  apply (metis main_inv_1_def main_inv_def option.discI option.sel singletonI)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply (metis main_inv_1_def main_inv_def option.distinct(1) option.sel singleton_iff)
  apply (metis main_inv_1_def main_inv_def option.discI option.sel singletonI)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply (metis main_inv_1_def main_inv_def option.distinct(1) option.sel singleton_iff) 
  apply (metis main_inv_1_def main_inv_def option.discI option.sel singleton_iff)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply (metis main_inv_1_def main_inv_def option.discI option.sel singletonI)
  apply (metis main_inv_1_def main_inv_def option.discI option.sel singletonI)
  apply (metis main_inv_1_def main_inv_def option.distinct(1) option.sel singleton_iff) 
  apply (metis main_inv_1_def main_inv_def option.discI option.sel singletonI)
  apply(case_tac "reg ms t = Suc 0", simp_all add:abbr) 
  apply (metis main_inv_1_def main_inv_def option.discI option.sel singleton_iff)
  apply (meson main_inv_3_def main_inv_def own\<^sub>W_n_by_t_imp_def)
  apply (metis main_inv_1_def main_inv_def option.discI option.sel singleton_iff)
  apply(case_tac "reg ms t = Suc 0", simp_all add:abbr) 
  apply (metis main_inv_1_def main_inv_def option.discI option.sel singletonI)
  by (metis main_inv_1_def main_inv_def option.discI option.sel singletonI)






lemma showing_main_inv_2_for_S:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> S_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  main_inv_2 ms' ps'"
  apply(simp, safe; simp_all)
  apply(simp_all add:step_def)
  apply(simp_all add:main_inv_2_def abbr main_inv_def)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all add:abbr) defer
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr) defer
  apply(case_tac "CTRsync\<^sub>2 ms t = t ", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr) apply(simp add:main_inv_3_def) apply auto[1]
  apply(case_tac "reg ms t = Suc 0", simp_all add:abbr) apply auto[1]
  by(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)



lemma showing_main_inv_3_for_S:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> S_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  main_inv_3 ms' ps'"
  apply(simp, safe; simp_all)
  apply(simp_all add:step_def)
  apply(simp_all add:main_inv_3_def abbr main_inv_def)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all add:abbr) defer
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr) defer
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr) defer
  apply(case_tac "reg ms t = Suc 0", simp_all add:abbr) defer
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)
  by auto



lemma showing_main_inv_for_S:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> S_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  main_inv ms' ps'"
  apply(subgoal_tac "main_inv_1 ms' \<and> main_inv_2 ms' ps' \<and> main_inv_3 ms' ps'")
  apply(simp add:main_inv_def)
  apply(intro conjI impI)
  using showing_main_inv_1_for_S apply blast
  using showing_main_inv_2_for_S apply blast
  using showing_main_inv_3_for_S by blast


















lemma showing_psem_rules_for_S:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> S_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  psem_rules ps'" 
  apply(simp, safe; simp_all)
  apply(simp_all add: step_def abbr)
  apply (metis domI fst_conv option.sel)
  apply blast+
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all add:abbr)
  apply (metis domI fst_eqD option.sel)
  apply (metis domI fst_conv option.sel)
  apply (metis domI fst_conv option.sel)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all add:abbr)
  apply blast
  apply blast
  apply blast apply auto[1]
  apply (metis domI fst_conv option.sel)
  apply blast
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr) apply auto[1]
  apply (metis domI fst_conv option.sel)
  apply (metis domI fst_conv option.sel)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr) 
  apply blast
  apply blast
  apply blast
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr) 
  apply (metis domI fst_eqD option.sel)
  apply (metis domI fst_eqD option.sel)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply blast
  apply blast
  apply auto[1] 
  apply (metis domI eq_fst_iff option.sel)
  apply blast
  apply(case_tac "reg ms t = Suc 0", simp_all add:abbr)
  apply (metis domI fst_eqD option.sel)
  apply (metis domI fst_eqD option.sel)
  apply(case_tac "reg ms t = Suc 0", simp_all add:abbr)
  apply(case_tac "reg ms t = Suc 0", simp_all add:abbr)
  apply blast
  by blast





















lemma showing_allocated_addresses_for_S:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> S_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  allocated_addresses ms' ps'" 
  apply(simp, safe; simp_all)
  apply(simp add:allocated_addresses_lemmas step_def abbr)
  apply(simp add:allocated_addresses_lemmas step_def abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all add:abbr)
  apply(simp add:allocated_addresses_lemmas step_def abbr)
  apply auto[1] apply blast 
  apply(simp add:allocated_addresses_lemmas step_def abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)
  apply(simp add:allocated_addresses_lemmas step_def abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply(simp add:allocated_addresses_lemmas step_def abbr)
  apply auto[1] apply blast 
  apply(simp add:allocated_addresses_lemmas step_def abbr)
  by(case_tac "reg ms t = Suc 0", simp_all add:abbr)



















lemma showing_observation_inv_ms_for_S:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> S_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  observation_inv_ms ms'" 
  apply(simp, safe; simp_all)
  apply(simp add:observation_inv_ms_def step_def abbr)
  apply(simp add:observation_inv_ms_def step_def abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all add:abbr)
  apply(simp add:observation_inv_ms_def step_def abbr)
  apply auto[1]
  apply blast
  apply blast
  apply(simp add:observation_inv_ms_def step_def abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)
  apply(simp add:observation_inv_ms_def step_def abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply(simp add:observation_inv_ms_def step_def abbr)
  apply auto[1]
  apply blast
  apply blast
  apply(simp add:observation_inv_ms_def step_def abbr)
  by(case_tac "reg ms t = Suc 0", simp_all add:abbr)
















lemma showing_observation_inv_sig_for_S:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> S_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  observation_inv_sig ms' ps' \<sigma>'" 
  apply (simp, safe; clarsimp)
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply clarify
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max") prefer 2 apply simp
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply blast
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all add:abbr)
  apply blast
  apply blast
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply auto[1] 
  apply(subgoal_tac "loc \<noteq> l") prefer 2
  apply blast
  apply(simp add:OpSem.step_def wfs_2_def) apply auto[1]
  using OpSem.step_def not_cvd_RdX_pres apply blast
  apply(simp add:OpSem.step_def wfs_2_def) apply auto[1]
  using OpSem.step_def not_cvd_RdX_pres apply blast
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max") prefer 2 apply simp
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp add:abbr)
  apply(simp add:step_def) apply(simp add:abbr)
  apply(simp add:step_def)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0") prefer 2 apply simp
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply(simp add:abbr)
  unfolding observation_inv_sig_def apply simp
  prefer 2
  unfolding step_def
  apply(case_tac "reg ms t = 1", simp_all add:abbr con_assms_def) (*last 1, S6, load(rcu)*)
  apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2 
  apply clarify
  apply(subgoal_tac "CTRsync\<^sub>2 ms t < T_max") prefer 2 
  using preCond_def pre_S6_def apply (metis PC.simps(783))
  apply(simp add:wfs_2_def)
  apply (meson cvd_Rdx_pres)
  apply(intro allI) apply(intro conjI impI) apply clarify
  apply(simp add:wfs_2_def) 
  by (metis not_cvd_RdX_pres)






lemma showing_own\<^sub>W_n_by_t_imp_for_S:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> S_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms'" 
  apply (simp, safe; clarsimp)
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max")
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all add:abbr)
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply auto
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max")
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)
  apply(simp add:step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply(simp add:step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply auto
  apply(simp add:step_def abbr own\<^sub>W_n_by_t_imp_def)
  by(case_tac "reg ms t = Suc 0", simp_all add:abbr)











lemma showing_general_structure_for_S:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> S_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  general_structure ms'" 
  apply (simp, safe; clarsimp)
  apply(simp_all add:step_def abbr)
  apply(simp_all add:general_structure_def)
  apply(intro conjI)   
  apply(simp add:n_differ_def)  apply auto[1]
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1]
  apply(simp add:n_differ_from_s_inside_def)  apply auto[1]
  apply(simp add:s_differ_from_det_inside_def)  apply auto[1]  
  apply(simp add:n_differ_from_det_def)  apply auto[1]  
  apply(simp add:det_differ_from_det_def)  apply auto[1]
  apply(simp add:det_differ_inside_def)  apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def) 
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max")
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all)
  apply(simp add: abbr)
  apply(intro conjI)
  apply(simp add:n_differ_def)  apply auto[1]
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1]
  apply(simp add:n_differ_from_s_inside_def)  apply auto[1]
  apply(simp add:s_differ_from_det_inside_def)  apply auto[1]  
  apply(simp add:n_differ_from_det_def)  apply auto[1]  
  apply(simp add:det_differ_from_det_def)  apply auto[1]
  apply(simp add:det_differ_inside_def)  apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def) 
  apply(simp add:abbr)
  apply(intro conjI)
  apply(simp add:n_differ_def)  apply auto[1]
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1]
  apply(simp add:n_differ_from_s_inside_def)  apply auto[1]
  apply(simp add:s_differ_from_det_inside_def)  apply auto[1]  
  apply(simp add:n_differ_from_det_def)  apply auto[1]  
  apply(simp add:det_differ_from_det_def)  apply auto[1]
  apply(simp add:det_differ_inside_def)  apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def) 
  apply(simp add:abbr)
  apply(intro conjI)
  apply(simp add:n_differ_def)  apply auto[1]
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1]
  apply(simp add:n_differ_from_s_inside_def)  apply auto[1]
  apply(simp add:s_differ_from_det_inside_def)  apply auto[1]  
  apply(simp add:n_differ_from_det_def)  apply auto[1]  
  apply(simp add:det_differ_from_det_def)  apply auto[1]
  apply(simp add:det_differ_inside_def)  apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def) 
  defer (*rcu_read (CTR_sync\<^sub>1)*)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)
  apply(intro conjI)
  apply(simp add:n_differ_def)  apply auto[1]
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1]
  apply(simp add:n_differ_from_s_inside_def)  apply auto[1] 
  apply(simp add:s_differ_from_det_inside_def)  apply auto[1]  
  apply(simp add:n_differ_from_det_def)  apply auto[1]  
  apply(simp add:det_differ_from_det_def)  apply auto[1]
  apply(simp add:det_differ_inside_def)  apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def)  
  apply(intro conjI)
  apply(simp add:n_differ_def)  apply auto[1]
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1]
  apply(simp add:n_differ_from_s_inside_def)  apply auto[1]
  apply(simp add:s_differ_from_det_inside_def)  apply auto[1]  
  apply(simp add:n_differ_from_det_def)  apply auto[1]  
  apply(simp add:det_differ_from_det_def)  apply auto[1]
  apply(simp add:det_differ_inside_def)  apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def)  
  apply(intro conjI)
  apply(simp add:n_differ_def)  apply auto[1]
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1]
  apply(simp add:n_differ_from_s_inside_def)  apply auto[1]
  apply(simp add:s_differ_from_det_inside_def)  apply auto[1]  
  apply(simp add:n_differ_from_det_def)  apply auto[1]  
  apply(simp add:det_differ_from_det_def)  apply auto[1]
  apply(simp add:det_differ_inside_def)  apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def)  
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all)
  apply(simp add:abbr)
  apply(intro conjI)
  apply(simp add:n_differ_def)  apply auto[1]
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1]
  apply(simp add:n_differ_from_s_inside_def)  apply auto[1]
  apply(simp add:s_differ_from_det_inside_def)  apply auto[1]  
  apply(simp add:n_differ_from_det_def)  apply auto[1]  
  apply(simp add:det_differ_from_det_def)  apply auto[1]
  apply(simp add:det_differ_inside_def)  apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def) 
  apply(simp add:abbr)
  apply(intro conjI)
  apply(simp add:n_differ_def)  apply auto[1]
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1]
  apply(simp add:n_differ_from_s_inside_def)  apply auto[1]
  apply(simp add:s_differ_from_det_inside_def)  apply auto[1]  
  apply(simp add:n_differ_from_det_def)  apply auto[1]  
  apply(simp add:det_differ_from_det_def)  apply auto[1]
  apply(simp add:det_differ_inside_def)  apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def) 
  defer (*rcu_read (CTR_sync\<^sub>2)*)
  apply(case_tac "reg ms t = Suc 0", simp_all)
  apply(simp add:abbr)
  apply(intro conjI)
  apply(simp add:n_differ_def)  apply auto[1]
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1]
  apply(simp add:n_differ_from_s_inside_def)  apply auto[1]
  apply(simp add:s_differ_from_det_inside_def)  apply auto[1]  
  apply(simp add:n_differ_from_det_def)  apply auto[1]  
  apply(simp add:det_differ_from_det_def)  apply auto[1]
  apply(simp add:det_differ_inside_def)  apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def) 
  apply(simp add:abbr)
  apply(intro conjI)
  apply(simp add:n_differ_def)  apply auto[1]
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1]
  apply(simp add:n_differ_from_s_inside_def)  apply auto[1]
  apply(simp add:s_differ_from_det_inside_def)  apply auto[1]  
  apply(simp add:n_differ_from_det_def)  apply auto[1]  
  apply(simp add:det_differ_from_det_def)  apply auto[1]
  apply(simp add:det_differ_inside_def)  apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def) 
  apply(intro conjI)                      
  apply(simp add:n_differ_def)  apply auto[1]
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1]
  apply(simp add:n_differ_from_s_inside_def)  apply auto[1]
  apply(simp add:s_differ_from_det_inside_def)  apply auto[1]  apply blast
  apply(simp add:n_differ_from_det_def)  apply auto[1]  apply blast
  apply(simp add:det_differ_from_det_def)  apply auto[1]
  apply(simp add:det_differ_inside_def)  apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def)  apply auto[1]
  apply(intro conjI)                   
  apply(simp add:n_differ_def)  apply auto[1]
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1]
  apply(simp add:n_differ_from_s_inside_def)  apply auto[1]
  apply(simp add:s_differ_from_det_inside_def)  apply auto[1]  apply blast
  apply(simp add:n_differ_from_det_def)  apply auto[1]  apply blast
  apply(simp add:det_differ_from_det_def)  apply auto[1]
  apply(simp add:det_differ_inside_def)  apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def)  by auto[1]  







lemma showing_local_preCond_for_S4:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow> 
  pc ms t = S4 \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  det_block t ms \<sigma>  \<Longrightarrow>
  preCond ms' ps' (pc ms' t) t" 
  apply(simp add:step_def preCond_def)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)
  apply auto[1]
  apply(subgoal_tac "\<forall>i. i\<ge>0 \<longrightarrow> own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def bot_nat_0.extremum) apply auto[1]
  apply(subgoal_tac "\<forall>i. i\<ge>0 \<longrightarrow> own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit) Wcap_def bot_nat_0.extremum)   apply auto[1]
  apply (smt (verit) Rcap_def Wcap_def mstate.select_convs(16) mstate.select_convs(17) mstate.surjective mstate.update_convs(1))
  apply auto[1]
  apply(subgoal_tac "\<forall>i. i\<ge>0 \<longrightarrow> own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def bot_nat_0.extremum)  apply auto[1]
  apply(subgoal_tac "\<forall>i. i\<ge>0 \<longrightarrow> own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (smt (verit) Wcap_def bot_nat_0.extremum)   apply auto[1] 
  apply(simp add:con_assms_def)
  apply (metis linorder_not_less)
  apply(simp add:con_assms_def)
  by (smt (verit) Rcap_def mem_Collect_eq)


lemma showing_local_preCond_for_S5:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow> 
  pc ms t = S5 \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  det_block t ms \<sigma>  \<Longrightarrow>
  preCond ms' ps' (pc ms' t) t" 
  apply(simp add:step_def preCond_def)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp add:abbr)
  apply auto 
  apply(simp add:det_block_def)
  apply(simp add:con_assms_def)
  apply clarify apply(subgoal_tac "\<forall>i. i\<ge>0 \<longrightarrow> own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def bot_nat_0.extremum)  apply auto[1]
  apply(subgoal_tac "\<forall>i. i\<ge>0 \<longrightarrow> own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit) Wcap_def bot_nat_0.extremum)   apply auto[1]
  apply (metis less_SucE)
  apply(simp add:abbr)
  apply auto[1]
  apply(subgoal_tac "\<forall>i. i\<ge>0 \<longrightarrow> own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def bot_nat_0.extremum)  apply auto[1]
  apply(subgoal_tac "\<forall>i. i\<ge>0 \<longrightarrow> own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (smt (verit) Wcap_def bot_nat_0.extremum)   apply auto[1] 
  by (metis One_nat_def con_assms_def less_nat_zero_code linorder_not_less r_takes_one_or_two_def)

  

lemma showing_local_preCond_for_S6:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow> 
  pc ms t = S6 \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  det_block t ms \<sigma>  \<Longrightarrow>
  preCond ms' ps' (pc ms' t) t" 
  apply(simp add:step_def preCond_def)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp add:abbr)
  apply auto 
  apply(simp add:det_block_def)
  apply(simp add:rcu_temp_copy_def)
  apply(simp add:con_assms_def)
  apply(subgoal_tac "pc ms' t = S7") prefer 2 apply auto[1]
  apply clarsimp apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. i\<ge>0 \<longrightarrow> own\<^sub>R ms i = own\<^sub>R ms' i") prefer 2 apply auto[1]
  apply (metis (no_types, lifting) Rcap_def bot_nat_0.extremum)
  apply(subgoal_tac "\<forall>i. i\<ge>0 \<longrightarrow> own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (smt (verit) Wcap_def bot_nat_0.extremum)   apply auto[1] 
  by (metis (no_types, lifting) d_obs_read_value wfs_2_def)



lemma showing_local_preCond_for_S7:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow> 
  pc ms t = S7 \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  det_block t ms \<sigma>  \<Longrightarrow>
  preCond ms' ps' (pc ms' t) t" 
  apply(simp add:step_def preCond_def)
  apply(simp add:det_block_def)
  apply(case_tac "reg ms t = Suc 0", simp_all add:abbr con_assms_def)
  apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. i\<ge>0 \<longrightarrow> own\<^sub>R ms i = own\<^sub>R ms' i") prefer 2 apply auto[1]
  apply (metis (no_types, lifting) Rcap_def bot_nat_0.extremum)
  apply(subgoal_tac "\<forall>i. i\<ge>0 \<longrightarrow> own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (smt (verit) Wcap_def bot_nat_0.extremum)   apply auto[1] 
  apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. i\<ge>0 \<longrightarrow> own\<^sub>R ms i = own\<^sub>R ms' i") prefer 2 apply auto[1]
  apply (metis (no_types, lifting) Rcap_def bot_nat_0.extremum)
  apply(subgoal_tac "\<forall>i. i\<ge>0 \<longrightarrow> own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (smt (verit) Wcap_def bot_nat_0.extremum)   apply auto[1] 
  by (metis less_SucE)


lemma showing_local_preCond_for_S:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  T_limitation ms \<Longrightarrow>
  pc ms t \<in> S_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  det_block t ms \<sigma>  \<Longrightarrow>
  preCond ms' ps' (pc ms' t) t" 
  apply(case_tac "pc ms t = S4") using showing_local_preCond_for_S4 apply blast
  apply(case_tac "pc ms t = S5") using showing_local_preCond_for_S5 apply blast
  apply(case_tac "pc ms t = S6") using showing_local_preCond_for_S6 apply blast
  apply(case_tac "pc ms t = S7") using showing_local_preCond_for_S7 apply blast
  apply (simp, safe; clarsimp)
  apply(simp_all add:preCond_def step_def abbr)
  apply(simp add:Rcap_def Wcap_def) apply auto[1]
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all add:abbr)
  apply(simp add:Rcap_def Wcap_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply auto[1]
  apply(intro conjI impI)
  apply(simp add:Rcap_def Wcap_def) 
  apply (simp add: Wcap_def) 
  apply (simp add:con_assms_def)
  apply(clarsimp)
  apply(intro conjI impI)
  apply(simp add:Rcap_def Wcap_def) 
  apply (simp add: Wcap_def) 
  apply(simp add:post_block_def det_block_def)
  apply(subgoal_tac "x = 0 \<longrightarrow> (\<not>([(rcu_0 + (CTRsync\<^sub>1 ms t)) =\<^sub>t (Suc 0)] \<sigma>))") prefer 2
  apply (metis One_nat_def d_obs_read_value wfs_2_def zero_neq_one)
  by blast
  
 

lemma WM_read_and_dobs_other_pres:
  "wfs \<sigma> \<Longrightarrow> [y =\<^sub>t z] \<sigma> \<Longrightarrow> x\<noteq>y \<Longrightarrow> \<sigma> [wu \<leftarrow> w]\<^sub>t \<sigma>' \<Longrightarrow> [y =\<^sub>t z] \<sigma>'"
  using d_obs_RdX_pres
  by (metis d_obs_RdX_other)



lemma showing_det_pres_local_for_S:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  t' < T_max \<Longrightarrow>
  t'\<noteq> t \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  pc ms t \<in> S_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  \<forall>t'. t'<T_max \<and> t\<noteq>t'\<longrightarrow> block_cond t t' ms \<sigma>  \<Longrightarrow>
  det_block t ms \<sigma>  \<Longrightarrow>
  det_block t ms' \<sigma>'" 
  apply(simp add:det_block_def)
  apply(simp add:step_def)
  apply clarsimp
  apply(case_tac "pc ms t", simp_all add:abbr)
  apply blast
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all add:abbr)
  apply blast
  apply blast
  apply blast
  apply(clarify) 
  apply(case_tac "x = 0", simp_all)
  apply (metis d_obs_RdX_other d_obs_RdX_pres wfs_2_def)
  apply (metis d_obs_RdX_other d_obs_RdX_pres wfs_2_def)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)
  apply blast
  apply blast
  apply blast
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply blast
  apply blast
  apply clarify
  apply(case_tac "v = 0", simp_all)
  apply (metis d_obs_RdX_other d_obs_RdX_pres wfs_2_def)
  apply (metis RdX_def d_obs_Rd_pres isRd.simps(1) wfs_2_def)
  apply(case_tac "reg ms t = Suc 0", simp_all add:abbr)
  apply blast
  by blast



lemma changing_diff_pc_shows_global_preCond:
 "ta \<noteq> t \<Longrightarrow>
  ms' = (pc[t]:=i)  ms \<and> ps = ps' \<and> \<sigma>=\<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms ta) ta \<Longrightarrow>
  preCond ms' ps' (pc ms' ta) ta"  
  apply(subgoal_tac "pc ms ta = pc ms' ta") prefer 2 apply(simp add:abbr) 
  apply(simp add:preCond_def)
  apply(case_tac "pc ms ta", simp_all) 
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) 
  apply(simp add:Rcap_def Wcap_def abbr) 
  apply(simp add:Rcap_def Wcap_def abbr) 
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis 
  apply(simp add:abbr) apply(intro conjI impI)  
  apply(unfold Rcap_def)[1] apply clarify
  apply (metis (no_types, lifting) mstate.select_convs(16) mstate.surjective mstate.update_convs(1))
  apply(unfold Wcap_def)[1] apply clarify
  apply (metis (no_types, lifting) mstate.select_convs(17) mstate.surjective mstate.update_convs(1))
  apply(simp add:abbr) apply(intro conjI impI)  
  apply(unfold Rcap_def)[1] apply clarify
  apply (metis (no_types, lifting) mstate.select_convs(16) mstate.surjective mstate.update_convs(1))
  apply(unfold Wcap_def)[1] apply clarify
  apply (metis (no_types, lifting) mstate.select_convs(17) mstate.surjective mstate.update_convs(1))
  apply(simp add:abbr) apply(intro conjI impI)  
  apply(unfold Rcap_def)[1] apply clarify
  apply (metis (no_types, lifting) mstate.select_convs(16) mstate.surjective mstate.update_convs(1))
  apply(unfold Wcap_def)[1] apply clarify
  apply (metis (no_types, lifting) mstate.select_convs(17) mstate.surjective mstate.update_convs(1))
  apply(simp add:abbr) apply(intro conjI impI)  
  apply(unfold Rcap_def)[1] apply clarify
  apply (metis (no_types, lifting) mstate.select_convs(16) mstate.surjective mstate.update_convs(1))
  apply(unfold Wcap_def)[1] apply clarify
  by (metis (no_types, lifting) mstate.select_convs(17) mstate.surjective mstate.update_convs(1))
  
lemma changing_diff_pc_and_CTR_1_shows_global_preCond:
 "ta \<noteq> t \<Longrightarrow>
  ms' = (pc[t]:=i \<circ> CTRsync\<^sub>1[t]++)  ms \<and> ps = ps' \<and> \<sigma>=\<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms ta) ta \<Longrightarrow>
  preCond ms' ps' (pc ms' ta) ta"  
  apply(subgoal_tac "pc ms ta = pc ms' ta") prefer 2 apply(simp add:abbr) 
  apply(simp add:preCond_def)
  apply(case_tac "pc ms ta", simp_all) 
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) 
  apply(simp add:Rcap_def Wcap_def abbr) 
  apply(simp add:Rcap_def Wcap_def abbr) 
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis 
  apply(simp add:abbr)  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) apply auto[1] 
  apply(simp add:abbr)  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) apply auto[1] 
  apply(simp add:abbr)  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) apply auto[1] 
  apply(simp add:abbr)  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) by auto 

lemma changing_diff_pc_and_CTR_2_shows_global_preCond:
 "ta \<noteq> t \<Longrightarrow>
  ms' = (pc[t]:=i \<circ> CTRsync\<^sub>2[t]++)  ms \<and> ps = ps' \<and> \<sigma>=\<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms ta) ta \<Longrightarrow>
  preCond ms' ps' (pc ms' ta) ta"  
  apply(subgoal_tac "pc ms ta = pc ms' ta") prefer 2 apply(simp add:abbr) 
  apply(simp add:preCond_def)
  apply(case_tac "pc ms ta", simp_all) 
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) 
  apply(simp add:Rcap_def Wcap_def abbr) 
  apply(simp add:Rcap_def Wcap_def abbr) 
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis 
  apply(simp add:abbr)  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) apply auto[1] 
  apply(simp add:abbr)  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) apply auto[1] 
  apply(simp add:abbr)  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) apply auto[1] 
  apply(simp add:abbr)  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) by auto 


lemma changing_regreset_shows_global_preCond:
 "ta \<noteq> t \<Longrightarrow>
  ms' = regreset[t]  ms \<and> ps = ps' \<and> \<sigma>=\<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms ta) ta \<Longrightarrow>
  preCond ms' ps' (pc ms' ta) ta" 
  apply(subgoal_tac "pc ms ta = pc ms' ta") prefer 2 apply(simp add:abbr) 
  apply(simp add:preCond_def)
  apply(case_tac "pc ms ta", simp_all) 
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) 
  apply(simp add:Rcap_def Wcap_def abbr) 
  apply(simp add:Rcap_def Wcap_def abbr) 
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis 
  apply(simp add:abbr)  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) apply auto[1] 
  apply(simp add:abbr)  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) apply auto[1] 
  apply(simp add:abbr)  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) apply auto[1] 
  apply(simp add:abbr)  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) by auto  



lemma changing_diff_rN_0_shows_global_preCond:
 "ta \<noteq> t \<Longrightarrow>
  (ms r[N]:={0} t ms') \<and> ps = ps' \<and> \<sigma>=\<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms ta) ta \<Longrightarrow>
  preCond ms' ps' (pc ms' ta) ta"  
  apply(subgoal_tac "pc ms ta = pc ms' ta") prefer 2 apply(simp add:abbr) 
  apply(simp add:preCond_def)
  apply(case_tac "pc ms ta", simp_all) 
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) 
  apply(simp add:Rcap_def Wcap_def abbr) 
  apply(simp add:Rcap_def Wcap_def abbr) 
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis
  apply(simp add:Rcap_def Wcap_def abbr) apply metis 
  apply(simp add:abbr)  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) apply auto[1] 
  apply(simp add:abbr)  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) apply auto[1] 
  apply(simp add:abbr)  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) apply auto[1] 
  apply(simp add:abbr)  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) by auto 



lemma changing_loadCTR2_shows_global_preCond:
 "ta \<noteq> t \<Longrightarrow>
  (ms \<sigma> load((CTRsync\<^sub>2 ms t))\<^sub>t ms' \<sigma>') \<and> ps = ps' \<Longrightarrow> 
  preCond ms ps (pc ms ta) ta \<Longrightarrow>
  preCond ms' ps' (pc ms' ta) ta" 
  apply(subgoal_tac "pc ms ta = pc ms' ta") prefer 2 apply(simp add:abbr) apply auto[1]
  apply(simp add:preCond_def abbr)
  apply(case_tac "pc ms ta", simp_all)  
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1]  
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1]  
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1]  
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1]  
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply(simp add:Rcap_def Wcap_def abbr) apply clarify apply auto[1] 
  apply clarify apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) apply auto[1] 
  apply clarify apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) apply auto[1] 
  apply clarify apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) apply auto[1]
  apply clarify apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i") 
  apply (smt (verit, best) Wcap_def) by auto[1]
  


lemma showing_global_preCond_for_S:
 "ta \<noteq> t \<Longrightarrow>
  pc ms t \<in> S_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow>  
  preCond ms ps (pc ms ta) ta \<Longrightarrow>
  preCond ms' ps' (pc ms' ta) ta"    
  apply (simp add:step_def abbr, safe; clarsimp)
  using changing_diff_rN_0_shows_global_preCond apply presburger
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all) 
  (*8*)
  using changing_diff_pc_and_CTR_1_shows_global_preCond apply auto[1]
  (*7*)
  using changing_diff_pc_shows_global_preCond apply presburger     
  (*6*)
  using changing_diff_pc_shows_global_preCond apply presburger
  (*5*)
  apply(simp add:abbr preCond_def)
  apply auto[1]
  apply(cases "pc ms ta")
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) apply metis 
  apply(simp add:Rcap_def Wcap_def) apply metis 
  apply(simp add:Rcap_def Wcap_def) apply metis 
  apply(simp add:Rcap_def Wcap_def) apply metis 
  apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) apply metis 
  apply(simp add:Rcap_def Wcap_def) apply metis 
  apply(simp add:Rcap_def Wcap_def) apply metis  
  apply simp apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i") 
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply simp apply (intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply simp apply (intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply simp apply (intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply simp apply (intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply simp apply (intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply simp apply (intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply simp apply (intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply simp apply (intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  (*4*)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all)  
  apply (simp add: changing_diff_pc_and_CTR_2_shows_global_preCond)
  using changing_diff_pc_shows_global_preCond apply presburger
  using changing_diff_pc_shows_global_preCond apply presburger
  using changing_diff_pc_and_CTR_2_shows_global_preCond changing_diff_pc_shows_global_preCond apply presburger                   
  (*2*)
  using changing_loadCTR2_shows_global_preCond apply blast
  (*1*)
  apply(case_tac "reg ms t = Suc 0", simp_all)
  apply (meson changing_diff_pc_shows_global_preCond changing_regreset_shows_global_preCond)
  by (simp add: changing_diff_pc_and_CTR_2_shows_global_preCond changing_regreset_shows_global_preCond)  

  

end
 
