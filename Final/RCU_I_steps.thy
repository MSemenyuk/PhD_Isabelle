theory RCU_I_steps
imports RCU_model RCU_wm_proofs
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




(** I1 | I2 | I3 | I4 | I5 | I6 | I7 | I8 | I9 | I10 | I11 | I12 | I13 | I14 |  cas_res | finished*)




(*-----------------------------General Struct Supp-------------------------------------------*)

lemma testing_weak_mem:
  "wfs \<sigma> \<Longrightarrow>
   [z \<approx>\<^sub>t 0] \<sigma> \<Longrightarrow>
  \<not>[z =\<^sub>t 1] \<sigma> "
  by (metis d_obs_p_obs_agree zero_neq_one)



lemma support_psem:
  "Unique_allocs ps \<Longrightarrow>
  \<forall>prov prov'. prov\<in>dom(A ps) \<and> prov'\<in>dom(A ps) \<and> prov\<noteq>prov' \<longrightarrow>
  fst(the(A ps prov))\<noteq>fst(the(A ps prov'))"
  using Unique_allocs_def by blast

lemma support_psem2:
  "\<forall>prov prov'. prov\<in>dom(A ps) \<and> prov'\<in>dom(A ps) \<and> prov\<noteq>prov' \<longrightarrow>
  fst(the(A ps prov))\<noteq>fst(the(A ps prov')) \<Longrightarrow>Unique_allocs ps"
  by auto







(**************************Done******************************)
 






lemma showing_main_inv_1_for_I:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> I_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  main_inv_1 ms'"
  apply (simp, safe; clarsimp)
  apply(simp_all add:main_inv_1_def step_def)
  apply(simp_all add:abbr)
  apply(simp add:preCond_def)
  apply (metis main_inv_1_def main_inv_def option.discI)
  apply(simp_all add:preCond_def)
  apply (metis main_inv_1_def main_inv_def option.discI option.sel)
  apply (metis main_inv_1_def main_inv_def option.discI option.sel)
  apply(simp add:Rcap_def Wcap_def main_inv_lemmas allocated_addresses_lemmas) 
  apply(clarify)
  apply auto[1]
  apply metis
  apply (metis option.sel singleton_iff)
  apply (metis option.inject own\<^sub>W_n_by_t_imp_def)
  apply (metis main_inv_1_def main_inv_def option.discI option.sel)
  apply(case_tac "repeat ms t", simp_all)
  apply clarify
  apply (metis (no_types, lifting) Diff_empty Diff_insert0 general_structure_def main_inv_1_def main_inv_def n_differ_from_s_inside_def n_differ_from_s_outside_def option.distinct(1) option.sel)
  apply (simp add: main_inv_1_def main_inv_def)
  apply (metis main_inv_1_def main_inv_def option.discI option.sel)
  apply(simp add:get_C_val_def FAAZ_def)
  apply(simp add:Rcap_def Wcap_def main_inv_lemmas allocated_addresses_lemmas) 
  apply(case_tac "\<not>repeat ms t", simp_all)
  apply clarify
  apply(simp add:observation_inv_sig_def observation_inv_ms_def)
  apply (smt (verit) CollectD covered_v_def option.sel own\<^sub>W_n_by_t_imp_def visible_writes_def)
  apply(simp add:observation_inv_sig_def observation_inv_ms_def own\<^sub>W_n_by_t_imp_def)
  apply clarify
  apply(simp add:observation_inv_sig_def observation_inv_ms_def general_structure_def)
  apply (metis Up_reads_cvd_v option.sel relating_step_to_update_trans_1)
  apply(simp add:Rcap_def Wcap_def main_inv_lemmas allocated_addresses_lemmas)
  apply clarify
  apply(simp add:abbr main_inv_lemmas)
  apply (metis option.sel)
  apply clarify
  apply(simp add:abbr main_inv_lemmas)
  apply (metis option.sel)
  apply(simp add:cas_step_rcu_def) apply clarify
  apply(case_tac "ya", simp_all)
  apply(simp add:main_inv_lemmas)
  apply (metis option.sel)
  apply (metis main_inv_1_def main_inv_def option.discI option.sel)
  apply clarify
  apply(simp add:abbr main_inv_lemmas)
  apply blast
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  by(case_tac "CAS_succ ms t", simp_all add:abbr main_inv_lemmas)
  






lemma showing_main_inv_2_for_I:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> I_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  main_inv_2 ms' ps'"
  apply(simp, safe; simp_all)
  apply(simp_all add:step_def)
  apply(simp_all add:main_inv_2_def abbr main_inv_def)
  apply(clarify)
  apply(simp_all add:abbr) prefer 5
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply(simp add:abbr main_inv_lemmas)
  apply(case_tac "\<not>repeat ms t", simp_all)
  apply clarify
  apply(simp add:observation_inv_sig_def observation_inv_ms_def)
  apply(simp add:FAAZ_def get_C_val_def)
  apply(case_tac "\<not>repeat ms t", simp_all)
  apply clarify
  apply(simp add:observation_inv_sig_def observation_inv_ms_def)
  apply (metis Up_reads_cvd_v relating_step_to_update_trans_1)
  apply clarify
  apply(simp add:observation_inv_sig_def observation_inv_ms_def general_structure_def)
  apply (metis Up_reads_cvd_v relating_step_to_update_trans_1)
  prefer 2
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:cas_step_rcu_def)
  apply clarify
  apply(case_tac "y", simp_all)
  apply(simp add:abbr main_inv_lemmas preCond_def)
  apply clarify by auto[1]







lemma showing_main_inv_3_for_I:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> I_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  main_inv_3 ms' ps'"
  apply(simp, safe; simp_all)
  apply(simp_all add:step_def)
  apply(simp_all add:main_inv_3_def abbr main_inv_def)
  apply clarify
  apply(simp add:preCond_def)
  apply (metis insert_iff option.inject)
  apply(case_tac "\<not>repeat ms t", simp_all)
  apply clarify
  apply(simp add:observation_inv_sig_def observation_inv_ms_def) 
  apply(simp add:preCond_def Wcap_def Rcap_def)
  apply (metis general_structure_def less_nat_zero_code list.size(3) n_differ_from_s_inside_def option.sel s_differ_from_det_inside_def)
  defer
  apply(simp add:abbr main_inv_lemmas)
  apply force
  apply(simp add:abbr main_inv_lemmas)
  defer
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:preCond_def) apply clarify 
  apply (metis option.sel own\<^sub>W_n_by_t_imp_def)
  apply(simp add:abbr main_inv_lemmas)
  apply(case_tac "CAS_succ ms t ", simp_all)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:FAAZ_def get_C_val_def)
  apply(case_tac "\<not>repeat ms t", simp_all)
  apply clarify
  apply(simp add:observation_inv_sig_def observation_inv_ms_def) 
  apply (metis insertCI)
  apply clarify
  apply(simp add:observation_inv_sig_def observation_inv_ms_def general_structure_def) 
  apply (metis insertI2)
  apply(simp add:cas_step_rcu_def CAS_def)
  apply clarify
  apply(case_tac "y", simp_all) 
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(case_tac "loc = the (s ms t)", simp_all add:preCond_def)
  apply (meson Rcap_def insertCI)
  by (meson option.distinct(1))
   





lemma showing_main_inv_for_I:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> I_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  main_inv ms' ps'"
  apply(subgoal_tac "main_inv_1 ms' \<and> main_inv_2 ms' ps' \<and> main_inv_3 ms' ps'")
  apply(simp add:main_inv_def)
  apply(intro conjI impI)
  using showing_main_inv_1_for_I apply blast
  using showing_main_inv_2_for_I apply blast
  using showing_main_inv_3_for_I by blast













lemma showing_psem_rules_for_I4_supp:
 "pc ms t = I4 \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  psem_rules ps \<Longrightarrow>
  psem_rules ps'" 
  apply(simp add:step_def add:abbr)
  apply auto[1]  
  apply (metis domI fst_eqD option.sel ranI)
  apply (metis insert_iff option.exhaust_sel ran_map_upd surj_pair) prefer 2
  apply (metis domIff in_dom_notNone insert_iff prod.inject ran_map_upd)
  by (metis domIff in_dom_notNone insert_iff ran_map_upd)
  

lemma showing_psem_rules_for_I:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> I_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  psem_rules ps'" 
  apply(case_tac "pc ms t = I4") using showing_psem_rules_for_I4_supp apply blast 
  apply (simp add:step_def add:abbr)
  apply(subgoal_tac "ps = ps'") 
  apply meson apply(case_tac "pc ms t", simp_all add:abbr)
  by(case_tac "CAS_succ ms t", simp_all add:abbr)




















lemma allocated_addresses_preservation_for_I:
  "main_inv ms ps \<Longrightarrow> 
  t<T_max \<Longrightarrow>
  pc ms t \<in> I_steps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,vala] \<sigma> \<Longrightarrow>
  \<not>isfree_addr vala ps \<Longrightarrow>          \<comment> \<open>this is easily shown through alloc_addr\<close>
  general_structure ms \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  con_assms ms ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  allocated_addresses ms' ps'"
  apply (simp add:step_def preCond_def)
  apply(case_tac " pc ms t", simp_all add:own\<^sub>W_n_by_t_imp_def)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas) 
  apply meson
  apply(subgoal_tac "n ms t = None") prefer 2
  apply meson 
  apply clarsimp 
  apply(simp add:abbr allocated_addresses_lemmas general_structure_def)
  apply(intro conjI impI) 
  apply clarsimp
  apply(simp add:Rcap_def)
  apply metis
  apply clarsimp
  apply(simp add:Rcap_def)
  apply (metis option.sel)
  apply clarsimp
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas) 
  apply(case_tac "repeat ms t", simp_all)
  apply(simp add:Rcap_def Wcap_def general_structure_def con_assms_def)
  apply (metis option.sel)
  apply(simp add:abbr allocated_addresses_lemmas)
  defer                                               (*FAAZ*)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:OpSem.step_def RdX_def) 
  apply(simp add:Rcap_def Wcap_def general_structure_def con_assms_def)
  apply clarsimp 
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas cas_step_rcu_def) apply clarify
  apply(case_tac "ya", simp_all)
  apply(simp add:abbr allocated_addresses_lemmas) 
  apply (metis option.sel)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(case_tac "CAS_succ ms t", simp_all)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas)
  (*FAAZ*)
  apply(intro conjI impI) prefer 2
  apply(simp add:get_C_val_def allocated_n_addr_def)
  apply(simp add:abbr allocated_addresses_lemmas FAAZ_def)
  apply(simp add:Rcap_def Wcap_def general_structure_def con_assms_def)
  apply clarsimp
  apply metis  prefer 2
  apply(simp add:get_C_val_def allocated_n_addr_def)
  apply(simp add:abbr allocated_addresses_lemmas FAAZ_def)
  apply(simp add:Rcap_def Wcap_def general_structure_def con_assms_def)
  apply clarsimp
  apply(simp add:get_C_val_def allocated_n_addr_def)
  apply(simp add:abbr allocated_addresses_lemmas FAAZ_def)
  apply(simp add:Rcap_def Wcap_def general_structure_def con_assms_def)
  apply clarsimp
  by (metis Up_reads_cvd_v map_upd_eqD1 relating_step_to_update_trans_1)


















lemma Local_correctness_observation_inv_ms_for_I:
  "main_inv ms ps \<Longrightarrow> 
  t<T_max \<Longrightarrow>
  pc ms t \<in> I_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  observation_inv_ms ms \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms  \<Longrightarrow> 
observation_inv_ms ms'"
  apply(simp add:observation_inv_ms_def)
  apply(simp add:step_def preCond_def)
  apply(case_tac "pc ms t", simp_all add:abbr own\<^sub>W_n_by_t_imp_def Wcap_def Rcap_def)
  apply(simp add:general_structure_lemmas con_assms_def observation_inv_sig_def main_inv_lemmas)
  apply meson
  apply metis apply clarsimp 
  apply (metis option.inject)
  apply(case_tac "repeat ms t", simp_all)
  apply(case_tac "repeat ms t", simp_all)
  (*FAAZ*) defer defer
  apply(simp add:general_structure_lemmas con_assms_def observation_inv_sig_def main_inv_lemmas)
  apply clarify
  apply(simp add: step_def RdX_def)
  apply metis
  (*CAS*) defer 
  apply(case_tac "CAS_succ ms t", simp_all)
  apply(simp add:abbr)
  apply(simp add:abbr)
  apply(simp add:get_C_val_def FAAZ_def)
  apply(case_tac "repeat ms t", simp_all)
  apply clarsimp 
  apply metis
  apply(simp add:get_C_val_def FAAZ_def)
  apply(case_tac "repeat ms t", simp_all)
  apply clarsimp 
  apply metis
  apply(clarify) apply(simp add:cas_step_rcu_def) apply clarify
  apply(case_tac "snd (CAS t (a, b) (the (s ms t)) (the (n ms t)) \<sigma> ts')", simp_all)
  apply(case_tac "loc = y", simp_all) 
  apply(case_tac "y = ya", simp_all) 
  apply(case_tac "loc = ya", simp_all)
  apply metis
  by blast

















lemma showing_observation_inv_sig_for_I11:
"main_inv ms ps \<Longrightarrow>
    con_assms ms ps \<Longrightarrow>
    wfs_2 \<sigma> \<Longrightarrow>
    cvd[C, vala] \<sigma> \<Longrightarrow>
    t < T_max \<Longrightarrow>
    general_structure ms \<Longrightarrow>
    RCU_model.step ms ps \<sigma> I11 t ms' ps' \<sigma>' \<Longrightarrow>
    preCond ms ps I11 t \<Longrightarrow>
    allocated_addresses ms ps \<Longrightarrow>
    psem_rules ps \<Longrightarrow>
    own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
    observation_inv_ms ms \<Longrightarrow>
    observation_inv_sig ms ps \<sigma> \<Longrightarrow>
 observation_inv_sig ms' ps' \<sigma>'"
  apply(simp add:step_def preCond_def)
  apply (simp add:cas_step_rcu_def)
  apply (simp add:observation_inv_sig_def covered_v_def wfs_2_def)
  apply (simp add:CAS_def)
  apply(clarify)
  apply(case_tac "ya", simp_all)  prefer 2
  apply(case_tac "value \<sigma> (a, b) = yb", simp_all) 
  apply(subgoal_tac "cvd[C,vala] \<sigma>'") prefer 2 apply(simp add:covered_v_def) apply clarify 
  apply auto[1] apply(simp add:covered_v_def) apply auto[1] 
  apply metis 
  apply blast 
  apply blast 
  apply blast
  apply(case_tac "value \<sigma> (a, b) = yb", simp_all)
  apply(case_tac "loc = yb", simp_all add:general_structure_lemmas) 
  apply (metis RMW_exist_w_in_post relating_step_to_update_trans_1 surj_pair)
  apply(case_tac "loc = y", simp_all add:Wcap_def)
  apply (meson allocated_addresses_def allocated_n_addr_def isfree_addr_def)
  by (metis (no_types, opaque_lifting) RMW_exist_w_in_post relating_step_to_update_trans_1 surj_pair)

  
 
lemma showing_observation_inv_sig_for_I:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> I_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  observation_inv_sig ms' ps' \<sigma>'" 
  apply(case_tac "pc ms t = I11") using showing_observation_inv_sig_for_I11 
  apply auto[1]
  apply (simp, safe; clarsimp)
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply(simp add:observation_inv_sig_def step_def abbr) 
  apply(simp add:preCond_def allocated_addresses_lemmas)
  apply(simp add:Wcap_def Rcap_def) apply auto[1]
  apply blast
  apply blast
  apply(simp add:observation_inv_sig_def step_def abbr) 
  apply(simp add:preCond_def allocated_addresses_lemmas)
  apply(simp add:Wcap_def Rcap_def) apply auto[1]
  apply (metis not_cvd_WrX_pres wfs_2_def)
  apply (metis not_cvd_WrX_pres wfs_2_def)
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply(simp add:preCond_def allocated_addresses_lemmas) 
  apply(simp add:Wcap_def Rcap_def)
  apply(case_tac "repeat ms t", simp_all) apply clarify 
  apply (metis not_cvd_WrX_pres wfs_2_def)  apply clarify 
  apply (metis not_cvd_WrX_pres wfs_2_def) 
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply(simp add:preCond_def allocated_addresses_lemmas) 
  apply(simp add:Wcap_def Rcap_def) apply clarify 
  apply (metis not_cvd_WrX_pres wfs_2_def)
  (*get_C_val*) defer
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply(simp add:preCond_def allocated_addresses_lemmas)
  apply(simp add:Wcap_def Rcap_def) apply auto[1]
  apply (meson cvd_Rdx_pres testtttttt wfs_2_def wfs_2_preserved)
  apply (metis not_cvd_RdX_pres wfs_2_def)
  apply(simp add:observation_inv_sig_def step_def abbr)
  using not_cvd_WrX_pres wfs_2_def apply blast
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply (metis not_cvd_WrX_pres wfs_2_def)
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply(simp add:observation_inv_sig_def step_def abbr)
  (*get_C_val*)
  apply(simp add:observation_inv_sig_def step_def abbr get_C_val_def FAAZ_def)
  apply clarify
  apply(simp add:wfs_2_def)
  by (metis Up_reads_cvd_v cvd_RMW_new_cvd relating_step_to_update_trans_1 testtttttt wfs_2_def wfs_2_preserved)
 










lemma showing_own\<^sub>W_n_by_t_imp_for_I:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> I_steps \<Longrightarrow>
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
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:preCond_def Rcap_def Wcap_def) apply auto[1]
  apply (metis allocated_addresses_def allocated_n_addr_def isfree_addr_def)
  apply (metis option.inject)
  apply (metis option.sel)     
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply(case_tac "repeat ms t", simp_all)
  apply(simp add:preCond_def Rcap_def Wcap_def) apply auto[1] 
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply(case_tac "repeat ms t", simp_all) 
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  (*FAAZ*) defer
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:preCond_def Rcap_def Wcap_def) apply auto[1]
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  (*cas_step_rcu*) defer
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  (*FAAZ*)
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def get_C_val_def FAAZ_def)
  apply(simp add:preCond_def Rcap_def Wcap_def) apply auto[1]
  (*cas_step_rcu*)
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def cas_step_rcu_def)
  apply clarsimp
  apply(case_tac "y", simp_all)
  apply(simp add:preCond_def) apply auto[1]
  apply (meson general_structure_def n_differ_from_s_inside_def)
  by (meson Rcap_def general_structure_def insertCI n_differ_from_s_outside_def)
  






lemma showing_general_structure_for_I:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> I_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  general_structure ms'" 
  (*FAAZ*)
  apply(case_tac "pc ms t = I8")
  apply(simp add:step_def abbr)
  apply(simp add:general_structure_def get_C_val_def FAAZ_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def)  apply auto[1] 
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1]
  apply(case_tac "i = value \<sigma> (a, b)", simp_all) 
  apply (metis Up_reads_cvd_v observation_inv_sig_def own\<^sub>W_n_by_t_imp_def relating_step_to_update_trans_1)
  apply(simp add:n_differ_from_s_inside_def)  apply auto[1] apply(case_tac "ta = t", simp_all)
  apply (metis Up_reads_cvd_v observation_inv_sig_def own\<^sub>W_n_by_t_imp_def relating_step_to_update_trans_1)
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(case_tac "det ms ta ! j = value \<sigma> (a,b)", simp_all) 
  apply(case_tac "ta = t", simp_all) apply auto[1]
  apply (smt (verit) CollectD covered_v_def observation_inv_sig_def own\<^sub>W_and_det_things_def visible_writes_def)
  apply(case_tac "ta = t", simp_all)
  apply blast
  apply(simp add:n_differ_from_det_def) apply auto[1]
  apply blast
  apply(simp add:det_differ_from_det_def) apply auto[1]
  apply(simp add:det_differ_inside_def) apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def) apply auto[1]
  (*cas_step_rcu*)
  apply(case_tac "pc ms t = I11")
  apply(simp add:step_def abbr)
  apply(simp add:general_structure_def cas_step_rcu_def)
  apply clarify
  apply(case_tac "y", simp_all) apply(intro impI conjI)
  apply(simp add:n_differ_def) apply auto[1] 
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1] 
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def)  
  apply(simp add:n_differ_from_det_def)   apply auto[1] 
  apply blast
  apply(simp add:det_differ_from_det_def) 
  apply(simp add:det_differ_inside_def) 
  apply(simp add:own\<^sub>W_and_det_things_def) apply auto[1] 
  apply (metis CAS_def Pair_inject Up_reads_cvd_v observation_inv_sig_def relating_step_to_update_trans_1)
  apply(simp add:preCond_def)
  apply (metis (no_types, lifting) n_differ_from_det_def option.sel)
  apply(simp add:preCond_def) apply(simp add:Rcap_def Wcap_def CAS_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def observation_inv_sig_def visible_writes_def)
  apply(intro impI conjI)
  apply(simp add:n_differ_def)
  apply(simp add:n_differ_from_s_outside_def)
  apply(simp add:n_differ_from_s_inside_def)
  apply(simp add:s_differ_from_det_inside_def)
  apply(simp add:n_differ_from_det_def)
  apply(simp add:det_differ_from_det_def) 
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def) 
  apply(safe; clarsimp)
  apply(simp_all add:step_def abbr)
  apply(simp_all add:general_structure_def)
  apply(intro conjI)
  apply(simp add:n_differ_def)  apply auto[1]
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1]
  apply(simp add:n_differ_from_s_inside_def)  
  apply(simp add:s_differ_from_det_inside_def) 
  apply(simp add:n_differ_from_det_def) apply auto[1]  apply(simp add:preCond_def) 
  apply blast
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply (simp add:general_structure_lemmas)
  apply(intro conjI impI)
  apply metis apply metis apply metis
  apply (simp add:general_structure_lemmas)
  apply(intro conjI impI)
  apply metis apply metis apply metis
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply clarsimp 
  apply (metis allocated_addresses_def isfree_addr_def option.distinct(1) pecpec1)
  apply(simp add:n_differ_from_s_outside_def) apply clarsimp
  apply (metis allocated_addresses_def empty_iff insertE isfree_addr_def main_inv_2_def main_inv_def map_upd_eqD1 option.distinct(1) pecpec1)
  apply(simp add:n_differ_from_s_inside_def) apply clarsimp
  apply(case_tac "ta = t", simp_all)
  apply auto[1] apply(simp add:preCond_def)
  apply(simp add:s_differ_from_det_inside_def) 
  apply auto[1] apply(simp add:preCond_def)
  apply (metis (no_types, lifting) insertE n_differ_from_det_def)
  apply(simp add:n_differ_from_det_def)   apply clarsimp
  apply (metis allocated_addresses_def allocated_det_addr_def isfree_addr_def option.sel)
  apply(simp add:det_differ_from_det_def) apply clarsimp
  apply(simp add:det_differ_inside_def) apply clarsimp
  apply(simp add:own\<^sub>W_and_det_things_def) apply clarsimp
  apply (meson allocated_addresses_def allocated_det_addr_def isfree_addr_def) 
  apply(simp add:general_structure_lemmas)
  apply auto[1]
  apply(case_tac "repeat ms t", simp_all)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply clarsimp 
  apply(simp add:n_differ_from_s_outside_def)
  apply blast apply clarsimp
  apply(simp add:n_differ_from_s_inside_def)
  apply(simp add:s_differ_from_det_inside_def)  apply clarsimp apply(simp add:preCond_def) 
  apply(simp add:n_differ_from_det_def)   apply clarsimp
  apply(simp add:det_differ_from_det_def) apply clarsimp
  apply(simp add:det_differ_inside_def) apply clarsimp
  apply(simp add:own\<^sub>W_and_det_things_def) apply clarsimp
  apply(intro conjI impI)
  apply(simp add:n_differ_def) 
  apply(simp add:n_differ_from_s_outside_def)
  apply(simp add:n_differ_from_s_inside_def)
  apply(simp add:s_differ_from_det_inside_def)  
  apply(simp add:n_differ_from_det_def)
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(simp add:general_structure_lemmas)
  apply auto[1]
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply clarsimp 
  apply(simp add:n_differ_from_s_outside_def) apply clarsimp
  apply(simp add:n_differ_from_s_inside_def) apply clarsimp
  apply(simp add:s_differ_from_det_inside_def)  apply clarsimp apply(simp add:preCond_def)
  apply (metis (no_types, lifting))
  apply(simp add:n_differ_from_det_def)   apply clarsimp
  apply metis
  apply(simp add:det_differ_from_det_def) apply clarsimp
  apply(simp add:det_differ_inside_def) apply clarsimp
  apply(simp add:own\<^sub>W_and_det_things_def) apply clarsimp
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply clarsimp 
  apply(simp add:n_differ_from_s_outside_def) apply clarsimp
  apply(simp add:n_differ_from_s_inside_def) apply clarsimp
  apply(simp add:s_differ_from_det_inside_def)  apply clarsimp apply(simp add:preCond_def)
  apply(simp add:n_differ_from_det_def)   apply clarsimp
  apply(simp add:det_differ_from_det_def) apply clarsimp
  apply(simp add:det_differ_inside_def) apply clarsimp
  apply(simp add:own\<^sub>W_and_det_things_def) apply clarsimp
  apply(intro conjI impI)
  apply(simp add:n_differ_def) 
  apply(simp add:n_differ_from_s_outside_def) apply clarsimp
  apply blast
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def)  
  apply(simp add:n_differ_from_det_def)   
  apply(simp add:det_differ_from_det_def) 
  apply(simp add:det_differ_inside_def) 
  apply(simp add:own\<^sub>W_and_det_things_def) apply clarsimp
  apply(simp add:general_structure_lemmas)
  apply(simp add:general_structure_lemmas)
  apply auto[1]
  apply(case_tac "CAS_succ ms t", simp_all add:general_structure_lemmas abbr)
  apply auto[1]
  by auto[1]












lemma showing_local_preCond_for_I:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  T_limitation ms \<Longrightarrow>
  pc ms t \<in> I_steps \<Longrightarrow>
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
  apply (simp, safe; clarsimp)
  apply(simp_all add:preCond_def step_def abbr)
  apply(simp add:Rcap_def Wcap_def) apply auto[1]
  apply(intro conjI impI) apply(simp add:Rcap_def) apply(simp add:Wcap_def)
  apply(intro conjI impI) apply(simp add:Rcap_def) apply(simp add:Wcap_def)
  apply(subgoal_tac "pc ms' t = I5", simp_all) prefer 2 apply auto[1]
  apply auto[1] apply(simp add:Rcap_def) apply(simp add:Wcap_def)
  apply(intro conjI impI) apply(simp add: Rcap_def Wcap_def) apply metis apply(simp add: Rcap_def Wcap_def)
  apply(subgoal_tac "pc ms' t = I7", simp_all) prefer 2 apply auto[1]
  apply(case_tac "repeat ms t", simp_all)
  apply auto[1] apply(simp add:Rcap_def) apply(simp add:Wcap_def) apply auto[1] 
  using general_structure_def n_differ_from_s_inside_def apply blast 
  apply (metis general_structure_def less_nat_zero_code list.size(3) option.sel s_differ_from_det_inside_def) 
  apply(simp add: Rcap_def Wcap_def)
  apply(intro conjI impI) apply(simp add: Rcap_def Wcap_def) apply metis apply(simp add: Rcap_def Wcap_def)
  apply(intro conjI impI) apply(simp add:Rcap_def) apply(simp add:Wcap_def)
  apply(simp add:get_C_val_def) apply(subgoal_tac "pc ms' t = I9", simp_all) prefer 2
  apply auto[1]
  apply(simp add:Rcap_def Wcap_def FAAZ_def) apply(intro conjI impI)
  apply(subgoal_tac "(\<forall>i. (i = the (n ms' t) \<or>
         i = the (s ms' t) \<or> (\<exists>j<length (det ms' t). det ms' t ! j = i)) \<longrightarrow>
        (t \<in> own\<^sub>R ms' i)) \<and>
        (\<forall>i.  (t \<in> own\<^sub>R ms' i)\<longrightarrow>
        (i = the (n ms' t) \<or>
         i = the (s ms' t) \<or> (\<exists>j<length (det ms' t). det ms' t ! j = i)))")
  apply metis
  apply(intro conjI impI) apply clarsimp
  apply metis apply clarsimp
  apply metis 
  apply(subgoal_tac "(\<forall>i. (i = the (n ms' t) \<or> (\<exists>j<length (det ms' t). det ms' t ! j = i)) \<longrightarrow>
        (own\<^sub>W ms' i = Some t)) \<and>
                 (\<forall>i. (own\<^sub>W ms' i = Some t) \<longrightarrow> (i = the (n ms' t) \<or> (\<exists>j<length (det ms' t). det ms' t ! j = i))
        ) ")
  apply metis
  apply(intro conjI impI) apply clarsimp
  apply metis
  apply clarsimp
  apply metis apply auto[1] apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply(subgoal_tac "pc ms' t = I10", simp_all) prefer 2 apply auto[1]
  apply auto[1]
  apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:cas_step_rcu_def) apply clarify
  apply(case_tac "ya", simp_all)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis general_structure_def less_nat_zero_code list.size(3) n_differ_from_det_def)
  apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis option.sel own\<^sub>W_n_by_t_imp_def)
  apply(simp add:Rcap_def Wcap_def) 
  apply metis
  apply(simp add:Rcap_def Wcap_def) 
  apply metis
  apply(case_tac "CAS_succ ms t", simp_all add:abbr Rcap_def Wcap_def)
  by metis
















lemma showing_global_preCond_for_I4:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  ta<T_max \<Longrightarrow>
  ta \<noteq> t \<Longrightarrow>
  pc ms t \<in> {I4} \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  preCond ms ps (pc ms ta) ta \<Longrightarrow>
  general_structure ms \<Longrightarrow>
  preCond ms' ps' (pc ms' ta) ta" 
  apply(simp add:step_def abbr)
  apply(simp add:preCond_def)
  apply(subgoal_tac "pc ms' ta = pc ms ta", simp_all) prefer 2 apply auto[1]
  apply(case_tac "pc ms t", simp_all)
  apply(case_tac[!] "pc ms ta", simp_all)
  apply(simp add:Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply(simp add: con_assms_def)
  apply clarsimp
  apply (metis insert_iff)
  apply clarsimp apply(case_tac "i = loc", simp_all)
  apply (metis empty_iff isfree_addr_def main_inv_2_def main_inv_def)
  apply auto[1]  apply auto[1] apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply(simp add:allocated_addresses_lemmas)
  apply(simp add: con_assms_def)
  apply(simp add:Rcap_def Wcap_def) 
  apply(intro conjI impI) apply clarsimp
  apply (metis insert_iff) apply clarsimp 
  apply (metis less_nat_zero_code list.size(3) option.inject)
  apply auto[1]  apply auto[1] apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply auto[1]  apply auto[1] apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply auto[1]  apply auto[1] apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply auto[1]  apply auto[1] apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  (*22*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject) 
  apply clarsimp apply(intro allI)
  apply(case_tac "i = the (n ms' ta)", simp_all) apply clarify
  apply(simp add:general_structure_def n_differ_def)
  apply metis
  apply(case_tac "i = the (s ms' ta)", simp_all) apply clarify
  apply(simp add:general_structure_def n_differ_from_s_outside_def)
  apply (metis option.sel)
  apply(simp add:general_structure_def n_differ_from_det_def)
  apply clarsimp
  apply (metis insert_iff)
  apply auto[1] apply(intro allI)
  apply(case_tac "i = the (n ms' ta)", simp_all) apply clarify
  apply(simp add:general_structure_def n_differ_def)
  apply metis
  apply(simp add:general_structure_def n_differ_from_det_def)
  apply clarsimp
  apply (metis insert_iff)    
  apply auto[1] apply auto[1] apply auto[1] apply auto[1] 
  (*21*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply clarsimp apply auto[1] apply clarsimp apply auto[1] apply clarsimp apply auto[1]
  (*20*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply clarsimp apply auto[1] apply clarsimp apply auto[1] apply clarsimp apply auto[1]
  (*19*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply clarsimp apply auto[1] apply clarsimp apply auto[1] apply clarsimp 
  (*18*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply clarsimp apply auto[1] apply clarsimp apply auto[1] apply clarsimp 
  (*17*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply clarsimp apply auto[1] apply clarsimp apply auto[1] apply clarsimp 
  (*16*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply clarsimp apply auto[1] apply clarsimp apply auto[1] apply clarsimp 
  (*15*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply clarsimp apply auto[1] apply clarsimp apply auto[1] apply clarsimp 
  (*14*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply clarsimp apply auto[1] apply clarsimp apply auto[1] apply clarsimp 
  (*13*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply clarsimp apply clarsimp apply (metis insert_iff) apply clarsimp 
  apply (metis less_nat_zero_code list.size(3) option.inject)
  apply auto[1] apply clarsimp apply auto[1] apply clarsimp apply clarsimp 
  (*12*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply clarsimp apply auto[1] apply clarsimp apply auto[1] apply clarsimp 
  (*11*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply clarsimp apply auto[1] apply clarsimp apply auto[1] apply clarsimp 
  (*10*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply clarsimp apply auto[1] apply clarsimp apply auto[1] apply clarsimp 
  (*9*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI) 
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply clarsimp apply auto[1] apply clarsimp
  apply clarsimp 
  apply (metis less_nat_zero_code list.size(3)) apply clarsimp apply clarsimp
  (*8*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis option.inject)
  apply clarsimp apply auto[1] apply clarsimp apply clarsimp apply clarsimp 
  apply (metis) apply clarsimp apply clarsimp
  (*7*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI) 
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply clarsimp apply auto[1] apply clarsimp apply clarsimp  apply clarsimp 
  (*6*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI) 
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply clarsimp apply auto[1] apply clarsimp apply clarsimp  apply clarsimp 
  apply clarsimp
  apply (metis less_nat_zero_code list.size(3))
  (*5*)
  apply(simp add:allocated_addresses_lemmas con_assms_def Rcap_def Wcap_def)
  apply(intro conjI impI) 
  apply clarsimp apply (metis insert_iff)
  apply clarsimp apply (metis less_nat_zero_code list.size(3) option.inject)
  apply clarsimp apply auto[1] apply clarsimp apply clarsimp  apply clarsimp 
  apply clarsimp apply (metis less_nat_zero_code list.size(3))
  (*4*)
  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms' ta). det ms' ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)") 
  apply (meson Rcap_def)  
  apply clarsimp 
  apply (smt (verit) Rcap_def insert_iff mem_Collect_eq)
  apply(simp add:Wcap_def) 
  apply clarsimp 
  apply (metis (mono_tags, lifting) Rcap_def empty_iff isfree_addr_def main_inv_2_def main_inv_def mem_Collect_eq option.inject) 
  apply clarsimp apply auto[1] apply clarsimp apply clarsimp  apply clarsimp 
  apply clarsimp 
  apply (metis (no_types, opaque_lifting) allocated_addresses_def allocated_det_addr_def isfree_addr_def less_nat_zero_code list.size(3))
  apply clarsimp 
  apply (metis (no_types, opaque_lifting) allocated_addresses_def allocated_det_addr_def isfree_addr_def less_nat_zero_code list.size(3))
  (*3*)
  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms' ta). det ms' ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)") 
  apply (meson Rcap_def)  
  apply clarsimp 
  apply (smt (verit) Rcap_def insert_iff mem_Collect_eq)
  apply(simp add:Wcap_def) 
  apply clarsimp 
  apply (metis (mono_tags, lifting) Rcap_def empty_iff isfree_addr_def main_inv_2_def main_inv_def mem_Collect_eq option.inject) 
  apply clarsimp apply auto[1] apply clarsimp apply clarsimp  apply clarsimp  apply clarsimp 
  apply clarsimp 
  apply (metis (no_types, opaque_lifting) allocated_addresses_def allocated_det_addr_def isfree_addr_def less_nat_zero_code list.size(3))
  apply clarsimp 
  apply (metis (no_types, opaque_lifting) allocated_addresses_def allocated_det_addr_def isfree_addr_def less_nat_zero_code list.size(3))
  (*2*)
  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms' ta). det ms' ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)") 
  apply (meson Rcap_def)  
  apply clarsimp 
  apply (smt (verit) Rcap_def insert_iff mem_Collect_eq)
  apply(simp add:Wcap_def) 
  apply clarsimp 
  apply (metis (mono_tags, lifting) Rcap_def empty_iff isfree_addr_def main_inv_2_def main_inv_def mem_Collect_eq option.inject) 
  apply clarsimp apply auto[1] apply clarsimp apply clarsimp  apply clarsimp  apply clarsimp  apply clarsimp 
  apply clarsimp 
  apply (metis (no_types, opaque_lifting) allocated_addresses_def allocated_det_addr_def isfree_addr_def less_nat_zero_code list.size(3))
  apply clarsimp 
  apply (metis (no_types, opaque_lifting) allocated_addresses_def allocated_det_addr_def isfree_addr_def less_nat_zero_code list.size(3))
  (*1*)
  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms' ta). det ms' ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)") 
  apply (meson Rcap_def)  
  apply clarsimp 
  apply (smt (verit) Rcap_def insert_iff mem_Collect_eq)
  apply(simp add:Wcap_def) 
  apply clarsimp 
  apply (metis (mono_tags, lifting) Rcap_def empty_iff isfree_addr_def main_inv_2_def main_inv_def mem_Collect_eq option.inject) 
  apply clarsimp apply auto[1] apply clarsimp apply clarsimp  apply clarsimp  apply clarsimp  apply clarsimp 
  apply clarsimp 
  apply (metis (no_types, opaque_lifting) allocated_addresses_def allocated_det_addr_def isfree_addr_def less_nat_zero_code list.size(3))
  apply clarsimp 
  apply (metis (no_types, opaque_lifting) allocated_addresses_def allocated_det_addr_def isfree_addr_def less_nat_zero_code list.size(3))
  apply clarsimp
  by (smt (verit) Rcap_def empty_iff isfree_addr_def main_inv_2_def main_inv_def mem_Collect_eq)



lemma showing_global_preCond_for_FAAZ:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  ta<T_max \<Longrightarrow>
  ta \<noteq> t \<Longrightarrow>
  pc ms t \<in> {I8} \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  preCond ms ps (pc ms ta) ta \<Longrightarrow>
  general_structure ms \<Longrightarrow>
 observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  preCond ms' ps' (pc ms' ta) ta" 
  apply(simp add:step_def FAAZ_def get_C_val_def)
  apply clarify
  apply(simp add:preCond_def)
  apply(case_tac "pc ms ta", simp_all)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:general_structure_def) apply(intro conjI impI)
  apply metis
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def) 
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply(intro conjI impI)
  apply metis
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply(simp add:Rcap_def Wcap_def) apply(intro conjI impI)
  apply metis
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) CollectD covered_v_def visible_writes_def) apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply(simp add:Wcap_def)
  apply (smt (verit) Wcap_def covered_v_def mem_Collect_eq observation_inv_sig_def visible_writes_def)
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) Wcap_def covered_v_def mem_Collect_eq visible_writes_def)
  (*3*)
  apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply(simp add:Wcap_def)
  apply (smt (verit) Wcap_def covered_v_def mem_Collect_eq observation_inv_sig_def visible_writes_def)
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) Wcap_def covered_v_def mem_Collect_eq visible_writes_def)
  (*2*)
  apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply(simp add:Wcap_def)
  apply (smt (verit) Wcap_def covered_v_def mem_Collect_eq observation_inv_sig_def visible_writes_def)
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) Wcap_def covered_v_def mem_Collect_eq visible_writes_def)
  (*1*)
  apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply(simp add:Wcap_def)
  apply (smt (verit) Wcap_def covered_v_def mem_Collect_eq observation_inv_sig_def visible_writes_def)
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) Wcap_def covered_v_def mem_Collect_eq visible_writes_def)
  apply(simp add:observation_inv_sig_def)
  by (smt (verit) CollectD covered_v_def general_structure_def length_0_conv less_Suc_eq_0_disj not_less_eq own\<^sub>W_and_det_things_def visible_writes_def)



lemma showing_global_preCond_for_cas_step:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  ta<T_max \<Longrightarrow>
  ta \<noteq> t \<Longrightarrow>
  pc ms t \<in> {I11} \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  preCond ms ps (pc ms ta) ta \<Longrightarrow>
  general_structure ms \<Longrightarrow>
 observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  preCond ms' ps' (pc ms' ta) ta" 
  apply(simp add:step_def FAAZ_def cas_step_rcu_def CAS_def)
  apply clarify
  apply(simp add:preCond_def)
  apply(case_tac "y", simp_all)
  apply(case_tac "pc ms ta", simp_all)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro conjI impI)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def option.sel visible_writes_def)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def option.sel visible_writes_def)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def) 
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro conjI impI)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def option.sel visible_writes_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def option.sel visible_writes_def)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply metis
  (*14*)
  apply(case_tac "CAS_succ ms ta", simp_all)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro conjI impI) 
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel) 
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  (*13*)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply metis
  (*12*)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply metis
  (*11*)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply metis
  (*10*)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply metis
  (*9*)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply metis
  (*8*)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply metis
  (*7*)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply metis
  (*6*)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (smt (verit) CollectD covered_v_def visible_writes_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply metis
  (*5*)
  apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply(simp add:Wcap_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply (smt (verit) CollectD covered_v_def observation_inv_sig_def visible_writes_def) 
  (*4*)
  apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply(simp add:Wcap_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply (smt (verit) CollectD covered_v_def observation_inv_sig_def visible_writes_def) 
  (*3*)
  apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply(simp add:Wcap_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply (smt (verit) CollectD covered_v_def observation_inv_sig_def visible_writes_def) 
  (*2*)
  apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply(simp add:Wcap_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI) apply(intro conjI impI) 
  apply (metis option.sel)
  apply (metis option.sel)
  apply (smt (verit) CollectD covered_v_def observation_inv_sig_def visible_writes_def) 
  (*1 the other split*)
  apply(case_tac "pc ms ta", simp_all)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  apply(simp add:Rcap_def Wcap_def observation_inv_sig_def)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro allI)
  apply metis
  (*4*)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply(simp add:Wcap_def)
  (*3*)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply(simp add:Wcap_def)
  (*2*)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply(simp add:Wcap_def)
  (*1*)
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  by(simp add:Wcap_def)
 




lemma showing_global_preCond_for_I:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  ta<T_max \<Longrightarrow>
  ta \<noteq> t \<Longrightarrow>
  pc ms t \<in> I_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  preCond ms ps (pc ms ta) ta \<Longrightarrow>
  general_structure ms \<Longrightarrow>
 observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  preCond ms' ps' (pc ms' ta) ta" 
  apply(case_tac "pc ms t = I4")
  using showing_global_preCond_for_I4 apply blast
  apply(case_tac "pc ms t = I8")
  using showing_global_preCond_for_FAAZ apply blast
  apply(case_tac "pc ms t = I11")
  using showing_global_preCond_for_cas_step apply blast
  apply(cases "pc ms t", simp_all add:step_def)
  (*11*)
  apply(case_tac "pc ms ta", simp_all add:preCond_def abbr)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  (*10*)
  apply(case_tac "pc ms ta", simp_all add:preCond_def abbr)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  (*9*)
  apply(case_tac "pc ms ta", simp_all add:preCond_def abbr)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  (*8*)
  apply(case_tac "pc ms ta", simp_all add:preCond_def abbr)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  (*8*)
  apply(case_tac "repeat ms t", simp_all)
  apply(case_tac "pc ms ta", simp_all add:preCond_def abbr)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)") 
  apply (meson Rcap_def)
  apply clarsimp apply(intro conjI impI)
  apply(subgoal_tac "((\<exists>j<length (det ms ta). det ms ta ! j = y) \<longrightarrow> (ta \<in> own\<^sub>R ms y))
                    \<and> ( (ta \<in> own\<^sub>R ms y) \<longrightarrow> (\<exists>j<length (det ms ta). det ms ta ! j = y))")
  prefer 2 apply clarsimp apply(intro conjI impI) 
  apply (metis (no_types, opaque_lifting) general_structure_def less_nat_zero_code list.size(3) main_inv_3_def main_inv_def own\<^sub>W_and_det_things_def)
  apply (smt (verit) CollectD Rcap_def)
  apply blast
  apply (smt (verit) CollectD Rcap_def general_structure_def less_nat_zero_code list.size(3) main_inv_3_def main_inv_def own\<^sub>W_and_det_things_def) 
  apply(simp add:Wcap_def)
  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp apply(intro conjI impI)
  apply(subgoal_tac "((\<exists>j<length (det ms ta). det ms ta ! j = y) \<longrightarrow> (ta \<in> own\<^sub>R ms y))
                    \<and> ( (ta \<in> own\<^sub>R ms y) \<longrightarrow> (\<exists>j<length (det ms ta). det ms ta ! j = y))")
  prefer 2 apply clarsimp apply(intro conjI impI) 
  apply (metis (no_types, opaque_lifting) general_structure_def less_nat_zero_code list.size(3) main_inv_3_def main_inv_def own\<^sub>W_and_det_things_def)
  apply (smt (verit) CollectD Rcap_def)
  apply blast
  apply (smt (verit) CollectD Rcap_def general_structure_def less_nat_zero_code list.size(3) main_inv_3_def main_inv_def own\<^sub>W_and_det_things_def) 
  apply(simp add:Wcap_def)
  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp apply(intro conjI impI)
  apply(subgoal_tac "((\<exists>j<length (det ms ta). det ms ta ! j = y) \<longrightarrow> (ta \<in> own\<^sub>R ms y))
                    \<and> ( (ta \<in> own\<^sub>R ms y) \<longrightarrow> (\<exists>j<length (det ms ta). det ms ta ! j = y))")
  prefer 2 apply clarsimp apply(intro conjI impI) 
  apply (metis (no_types, opaque_lifting) general_structure_def less_nat_zero_code list.size(3) main_inv_3_def main_inv_def own\<^sub>W_and_det_things_def)
  apply (smt (verit) CollectD Rcap_def)
  apply blast
  apply (smt (verit) CollectD Rcap_def general_structure_def less_nat_zero_code list.size(3) main_inv_3_def main_inv_def own\<^sub>W_and_det_things_def) 
  apply(simp add:Wcap_def)
  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp apply(intro conjI impI)
  apply(subgoal_tac "((\<exists>j<length (det ms ta). det ms ta ! j = y) \<longrightarrow> (ta \<in> own\<^sub>R ms y))
                    \<and> ( (ta \<in> own\<^sub>R ms y) \<longrightarrow> (\<exists>j<length (det ms ta). det ms ta ! j = y))")
  prefer 2 apply clarsimp apply(intro conjI impI) 
  apply (metis (no_types, opaque_lifting) general_structure_def less_nat_zero_code list.size(3) main_inv_3_def main_inv_def own\<^sub>W_and_det_things_def)
  apply (smt (verit) CollectD Rcap_def)
  apply blast
  apply (smt (verit) CollectD Rcap_def general_structure_def less_nat_zero_code list.size(3) main_inv_3_def main_inv_def own\<^sub>W_and_det_things_def) 
  apply(simp add:Wcap_def)
  apply(case_tac "pc ms ta", simp_all add:preCond_def abbr)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)") 
  apply (meson Rcap_def)
  apply clarsimp 
  apply(subgoal_tac "((\<exists>j<length (det ms ta). det ms ta ! j = i) \<longrightarrow> (ta \<in> own\<^sub>R ms i))
                    \<and> ((ta \<in> own\<^sub>R ms i) \<longrightarrow> (\<exists>j<length (det ms ta). det ms ta ! j = i))")
  prefer 2 apply(intro conjI impI) 
  apply (metis (no_types, opaque_lifting) general_structure_def less_nat_zero_code list.size(3) main_inv_3_def main_inv_def own\<^sub>W_and_det_things_def)
  apply (smt (verit) CollectD Rcap_def)
  apply blast
  apply(simp add:Wcap_def)
  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp
  apply(subgoal_tac "((\<exists>j<length (det ms ta). det ms ta ! j = i) \<longrightarrow> (ta \<in> own\<^sub>R ms i))
                    \<and> ( (ta \<in> own\<^sub>R ms i) \<longrightarrow> (\<exists>j<length (det ms ta). det ms ta ! j = i))")
  prefer 2 apply(intro conjI impI) 
  apply (metis (no_types, opaque_lifting) general_structure_def less_nat_zero_code list.size(3) main_inv_3_def main_inv_def own\<^sub>W_and_det_things_def)
  apply (smt (verit) CollectD Rcap_def)
  apply blast
  apply(simp add:Wcap_def)
  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp 
  apply(subgoal_tac "((\<exists>j<length (det ms ta). det ms ta ! j = i) \<longrightarrow> (ta \<in> own\<^sub>R ms i))
                    \<and> ( (ta \<in> own\<^sub>R ms i) \<longrightarrow> (\<exists>j<length (det ms ta). det ms ta ! j = i))")
  prefer 2 apply(intro conjI impI) 
  apply (metis (no_types, opaque_lifting) general_structure_def less_nat_zero_code list.size(3) main_inv_3_def main_inv_def own\<^sub>W_and_det_things_def)
  apply (smt (verit) CollectD Rcap_def)
  apply blast
  apply(simp add:Wcap_def)
  apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)")
  apply (meson Rcap_def) 
  apply clarsimp 
  apply(subgoal_tac "((\<exists>j<length (det ms ta). det ms ta ! j = i) \<longrightarrow> (ta \<in> own\<^sub>R ms i))
                    \<and> ( (ta \<in> own\<^sub>R ms i) \<longrightarrow> (\<exists>j<length (det ms ta). det ms ta ! j = i))")
  prefer 2 apply(intro conjI impI) 
  apply (metis (no_types, opaque_lifting) general_structure_def less_nat_zero_code list.size(3) main_inv_3_def main_inv_def own\<^sub>W_and_det_things_def)
  apply (smt (verit) CollectD Rcap_def)
  apply blast
  apply(simp add:Wcap_def)
  (*7*)
  apply(case_tac "pc ms ta", simp_all add:preCond_def abbr)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  (*6*)
  apply(subgoal_tac "pc ms' ta = pc ms ta") prefer 2 apply auto[1]  apply clarify
  apply(case_tac "pc ms ta", simp_all add:preCond_def abbr)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  (*5*) 
  apply(subgoal_tac "pc ms' ta = pc ms ta") prefer 2 apply auto[1]  apply clarify
  apply(case_tac "pc ms ta", simp_all add:preCond_def abbr)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  (*4*)
  apply(case_tac "pc ms ta", simp_all add:preCond_def abbr)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply auto[1]
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)") 
  apply (meson Rcap_def)
  apply clarsimp apply(intro conjI impI)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply(simp add:Wcap_def)  apply auto[1]
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)") 
  apply (meson Rcap_def)
  apply clarsimp apply(intro conjI impI)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply(simp add:Wcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)") 
  apply (meson Rcap_def)
  apply clarsimp apply(intro conjI impI)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply(simp add:Wcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)") 
  apply (meson Rcap_def)
  apply clarsimp apply(intro conjI impI)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply(simp add:Wcap_def)
  apply(subgoal_tac "\<forall>i. (i\<in>{i. \<exists>j<length (det ms ta). det ms ta ! j = i}) \<longleftrightarrow> (ta\<in>own\<^sub>R ms' i)") 
  apply (meson Rcap_def)
  apply clarsimp apply(intro conjI impI)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply (smt (verit) Rcap_def mem_Collect_eq)
  apply(simp add:Wcap_def)
  (*3*)
  apply(subgoal_tac "pc ms' ta = pc ms ta") prefer 2 apply auto[1]  apply clarify
  apply(case_tac "pc ms ta", simp_all add:preCond_def abbr)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  (*2*)
  apply(subgoal_tac "pc ms' ta = pc ms ta") prefer 2 apply auto[1]  apply clarify
  apply(case_tac "pc ms ta", simp_all add:preCond_def abbr)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  (*1*)
  apply(case_tac "CAS_succ ms t", simp_all)
  apply(simp add:abbr)
  apply(subgoal_tac "pc ms' ta = pc ms ta") prefer 2 apply auto[1]  apply clarify
  apply(case_tac "pc ms ta", simp_all add:preCond_def abbr)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply(subgoal_tac "pc ms' ta = pc ms ta") prefer 2 apply auto[1]  apply clarify
  apply(case_tac "pc ms ta", simp_all add:preCond_def abbr)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) by auto[1] 
  











lemma showing_det_pres_local_for_I8:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  pc ms t = I8 \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  \<forall>t'. t'<T_max \<and> t\<noteq>t' \<longrightarrow> block_cond t t' ms \<sigma> \<Longrightarrow>
  det_block t ms \<sigma>  \<Longrightarrow>
  det_block t ms' \<sigma>'"
  apply(simp add:det_block_def block_cond_def step_def)
  apply(clarsimp)
  apply(simp add:get_C_val_def FAAZ_def) 
  apply clarify
  apply(case_tac "det ms t ! j \<noteq> value \<sigma> (a, b)", simp_all) prefer 2
  apply(simp add:observation_inv_sig_def)
  apply (smt (verit) covered_v_def general_structure_def less_nat_zero_code list.size(3) mem_Collect_eq own\<^sub>W_and_det_things_def visible_writes_def)
  apply(subgoal_tac "[(rcu_0 + t') =\<^sub>t (Suc 0)] \<sigma>'")
  apply fastforce
  apply(subgoal_tac "[(rcu_0 + t') =\<^sub>t (Suc 0)] \<sigma>", simp add:wfs_2_def) prefer 2
  apply blast
  using d_obs_other_representation_2 [where \<sigma>=\<sigma> and t=t and w = "(a, b)" 
                                and \<sigma>' = \<sigma>' and x ="(rcu_0 + t'a)" and u ="Suc 0"
                                and ts' = ts' and l=C and nv' = "(value \<sigma> (a, b))"]
  apply(subgoal_tac "wfs \<sigma>", simp_all add:con_assms_def)
  using d_obs_other_representation_2 
  by presburger




lemma showing_det_pres_local_for_I10:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  pc ms t = I10 \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  \<forall>t'. t'<T_max \<and> t'\<noteq>t \<longrightarrow> block_cond t t' ms \<sigma> \<Longrightarrow>
  det_block t ms \<sigma>  \<Longrightarrow>
  det_block t ms' \<sigma>'" 
  apply(simp add:det_block_def block_cond_def)
  apply(clarsimp)
  apply(simp add: step_def con_assms_def rcu_locs_differ_def)
  apply(simp add:abbr)
  apply(subgoal_tac "the(n ms t) \<noteq> (rcu_0+t')") 
  apply (metis d_obs_WrX_other wfs_2_def) apply clarify 
  apply(simp add:con_assms_def) 
  by metis

lemma showing_det_pres_local_for_I11:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  pc ms t = I11 \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  \<forall>t'. t'<T_max \<and> t\<noteq>t'\<longrightarrow> block_cond t t' ms \<sigma> \<Longrightarrow>
  det_block t ms \<sigma>  \<Longrightarrow>
  det_block t ms' \<sigma>'" 
  apply(simp add:det_block_def block_cond_def step_def)
  apply(clarsimp)
  apply(simp add:cas_step_rcu_def con_assms_def)
  apply(clarsimp)
  apply(case_tac "y", simp_all) 
  apply (metis CAS_def d_obs_other_representation_2 prod.inject wfs_2_def)
  by (metis CAS_def Failed_CAS_preserves_d_obs_3 prod.inject)



lemma showing_det_pres_local_for_I:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  pc ms t \<in> I_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  \<forall>t'. t'<T_max \<and> t\<noteq>t' \<longrightarrow> block_cond t t' ms \<sigma> \<Longrightarrow>
  det_block t ms \<sigma>  \<Longrightarrow>
  det_block t ms' \<sigma>'" 
  apply(case_tac "pc ms t = I8")  using showing_det_pres_local_for_I8  apply blast
  apply(case_tac "pc ms t = I10") using showing_det_pres_local_for_I10 apply blast
  apply(case_tac "pc ms t = I11") using showing_det_pres_local_for_I11 apply blast
  apply(simp add:det_block_def block_cond_def step_def)
  apply(case_tac "pc ms t", simp_all add:abbr)
  apply(simp add:preCond_def Rcap_def Wcap_def)
  apply(simp add:con_assms_def pre_block_def)
  apply clarsimp
  apply(case_tac "det ms t ! j = loc", simp_all)
  apply metis
  apply metis
  apply(simp add:preCond_def Rcap_def Wcap_def)
  apply(simp add:con_assms_def pre_block_def)
  apply clarsimp
  apply (metis add_left_imp_eq d_obs_WrX_other wfs_2_def)
  apply(case_tac "repeat ms t", simp_all)
  apply (metis add_left_imp_eq d_obs_WrX_other wfs_2_def)
  apply (metis add_left_imp_eq d_obs_WrX_other wfs_2_def)
  apply(simp add:preCond_def Rcap_def Wcap_def)
  apply(simp add:con_assms_def pre_block_def)
  apply clarsimp 
  apply (metis add_left_imp_eq d_obs_WrX_other wfs_2_def)
  apply(simp add:preCond_def Rcap_def Wcap_def)
  apply(simp add:con_assms_def pre_block_def)
  apply clarsimp 
  apply (metis RdX_def d_obs_Rd_pres isRd.simps(1) wfs_2_def)
  apply (metis add_left_imp_eq d_obs_WrX_other wfs_2_def)
  by(case_tac "CAS_succ ms t", simp_all add:abbr)













end




