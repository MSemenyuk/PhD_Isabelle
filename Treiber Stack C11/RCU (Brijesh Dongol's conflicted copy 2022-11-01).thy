theory RCU
imports RCU_model
begin 

(*the following must be included in the proof:

con_assms ps        --- concerns allocation/bounds of C and rcu_0+i for all i
main_inv ms             --- main invariant has 3 parts

nts::
psem_rules ps               --- how allocation works on the inside

tedious - general_structure ms                      --- says how n \<noteq> s \<noteq> detaddrs
allocated_addresses ms ps *********        --- allocation for above are defined here
simple - observation_inv_ms ms         --- how own\<^sub>W affects loc status (own\<^sub>W loc = t \<longrightarrow> loc\<in>{s,n,det} t)
hard - observation_inv_sig ms ps \<sigma>       --- limits which values can be WM_read from C
simple - own\<^sub>W_n_by_t_imp ms


t \<le> T_max
step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'     --- defines a program step by t
last - preCond ms ps \<sigma> (pc ms t) t             --- defines preconditions for t to proceed with stepping      




*)



(*the following describes originally reserved addresses*)
definition "default_locs \<equiv> {i | i a. i=C \<or> i = rcu_0+a \<and> a\<le>T_max }"

definition "reserved_bydef ps \<equiv> \<forall>i. i\<in>default_locs \<longrightarrow> \<not>isfree_addr i ps"

definition "reservations_differ \<equiv> \<forall>i. i\<le>T_max \<longrightarrow> C\<noteq>rcu_0+i"

definition "con_assms ps \<equiv> reserved_bydef ps \<and> reservations_differ  "

lemmas con_lemmas [simp] = reserved_bydef_def reservations_differ_def default_locs_def



(*----------------Main Invariant Shown--------------------*)

lemma main_invariant_1_preservation:
  "main_inv ms ps \<Longrightarrow> 
  t\<le>T_max \<Longrightarrow>
  general_structure ms \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
  cvd[C,vala] \<sigma> \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
    main_inv_1 ms'"
  apply simp 
  apply(simp add: step_def preCond_def general_structure_lemmas main_inv_lemmas)
  apply(case_tac "pc ms t", simp_all add:abbr) apply clarsimp
  apply (metis insert_not_empty option.sel) apply clarsimp
  apply(case_tac "repeat ms t", simp_all) 
  apply (metis option.sel)
  apply (metis option.sel)
  (*FAAZ*) defer
  apply clarsimp
  apply (metis option.sel)
  apply clarsimp
  apply(case_tac "snd (CAS t (a, b) ya y \<sigma> ts')", simp_all)
  apply (metis option.sel)
  apply (metis option.sel)
  apply (metis Diff_empty Diff_insert0 insert_Diff singleton_insert_inj_eq)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply clarsimp
  apply (metis option.sel)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply (metis Diff_empty Diff_insert0 insert_absorb insert_iff)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply clarsimp
  apply (metis option.sel)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply clarsimp
  apply (metis option.sel)
  apply(case_tac "reg ms t = 1", simp_all add:abbr)
  apply(simp add: FAAZ_def get_C_val_def)
  apply(clarsimp)  (*y \<noteq> value \<sigma> (a, b), where value \<sigma> (a, b) is retrieved from reading C*)
  apply(simp_all add: covered_v_def lastWr_def observation_inv_sig_def visible_writes_def)
  by (metis option.sel own\<^sub>W_n_by_t_imp_def)


lemma main_invariant_2_preservation:
  "main_inv ms ps \<Longrightarrow> 
  t\<le>T_max \<Longrightarrow>
  general_structure ms \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  cvd[C,vala] \<sigma> \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
    main_inv_2 ms' ps'"
  apply simp 
  apply(simp add: step_def preCond_def general_structure_lemmas main_inv_lemmas)
  apply(case_tac "pc ms t", simp_all add:abbr)
  apply clarsimp
  apply clarsimp
  apply(case_tac "repeat ms t", simp_all)  
  apply (metis subset_singleton_iff) 
  (*FAAZ*) defer
  apply clarsimp
  apply clarsimp apply(case_tac " snd (CAS t (a, b) ya y \<sigma> ts')", simp_all)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply clarsimp
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr) 
  (*detached rules*) defer
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply clarsimp
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply clarsimp
  apply(case_tac "reg ms t = 1", simp_all add:abbr)
  apply(simp add: FAAZ_def get_C_val_def)
  apply(clarsimp)  (*y \<noteq> value \<sigma> (a, b), where value \<sigma> (a, b) is retrieved from reading C*)
  apply(simp add: covered_v_def observation_inv_sig_def visible_writes_def)
  apply blast
  (*the detached list property*)
  apply clarify apply(intro conjI impI)
  apply(subgoal_tac "hd(det ms t) \<in> detaddrs ms t", simp_all) 
  apply(subgoal_tac "det ms t \<noteq> []") prefer 2
  apply blast
  apply(subgoal_tac "det ms t!0 = hd(det ms t)") prefer 2
  apply (metis hd_conv_nth)
  by blast



lemma main_invariant_3_preservation:
  "main_inv ms ps \<Longrightarrow> 
  t\<le>T_max \<Longrightarrow>
  general_structure ms \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  cvd[C,vala] \<sigma> \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
    main_inv_3 ms' ps'"
  apply simp 
  apply(simp add: step_def preCond_def general_structure_lemmas main_inv_lemmas)
  apply(case_tac "pc ms t", simp_all add:abbr Wcap_def Rcap_def)
  apply clarsimp 
  apply (meson own\<^sub>W_n_by_t_imp_def)
  apply clarsimp
  apply(case_tac "repeat ms t", simp_all add:own\<^sub>W_n_by_t_imp_def) 
  apply clarsimp 
  apply(case_tac "loc = ya", simp_all) 
  apply (metis less_nat_zero_code list.size(3) option.sel) 
  (*FAAZ*) defer
  apply clarsimp apply clarsimp
  apply(case_tac "snd (CAS t (a, b) ya y \<sigma> ts')", simp_all) 
  apply (meson option.distinct(1)) 
  apply (metis option.discI)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply clarsimp
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply clarsimp
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply clarsimp
  apply(case_tac "reg ms t = 1", simp_all add:abbr)
  apply(simp add: FAAZ_def get_C_val_def)
  apply(clarsimp) (*y \<noteq> value \<sigma> (a, b), where value \<sigma> (a, b) is retrieved from reading C*)
  by(case_tac "loc = value \<sigma> (a, b)", simp_all) 




lemma main_invariant_preservation:
  "main_inv ms ps \<Longrightarrow> 
  t\<le>T_max \<Longrightarrow>
  general_structure ms \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  cvd[C,vala] \<sigma> \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms  \<Longrightarrow> 
main_inv ms' ps'"
  unfolding main_inv_def
  apply(intro conjI impI)
  using main_invariant_1_preservation main_inv_def apply blast
  using main_invariant_2_preservation main_inv_def apply blast
  using main_invariant_3_preservation main_inv_def apply blast
  done

(*--------------------------------------------------------------------*)

(*------------------------observation_inv_sig Correctness---------------------------*)

lemma supp1:
  "cvd[C,vala] \<sigma> \<Longrightarrow>
  \<sigma> [z \<leftarrow> ya]\<^sub>t \<sigma>' \<Longrightarrow>
  cvd[C,vala] \<sigma>'"
  apply(simp add:covered_v_def lastWr_def OpSem.step_def RdX_def visible_writes_def) unfolding writes_on_def
  read_trans_def
  by (smt (z3) Collect_cong rev_app_def surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(2) update_thrView_def value_def)

lemma supp2:
  "cvd[C,vala] \<sigma> \<Longrightarrow>
  \<sigma> [z := ya]\<^sub>t \<sigma>' \<Longrightarrow>
  z\<noteq>C \<Longrightarrow>
  cvd[C,vala] \<sigma>'"
  apply(simp add:covered_v_def lastWr_def OpSem.step_def WrX_def visible_writes_def value_def) unfolding writes_on_def
  write_trans_def update_thrView_def update_mods_def 
  update_modView_def valid_fresh_ts_def 
  rev_app_def tst_def 
  apply auto
  sledgehammer


lemma Local_correctness:
  "main_inv ms ps \<Longrightarrow> 
  t\<le>T_max \<Longrightarrow>
  general_structure ms \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  cvd[C,vala] \<sigma> \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms  \<Longrightarrow> 
observation_inv_sig ms' ps' \<sigma>'"
  apply(simp add:step_def preCond_def)
  apply(case_tac "pc ms t")
  apply simp_all 
  apply (simp add:abbr)
  apply(simp add:observation_inv_sig_def)
  apply (simp add:abbr)
  apply(simp add:observation_inv_sig_def)
  apply (simp add:abbr)
  apply(simp add:observation_inv_sig_def)
  apply (simp add:abbr)
  apply(simp add:observation_inv_sig_def)
  apply clarsimp apply(simp add:covered_v_def)
  apply metis
  apply(simp add:abbr)  
(*RCU_enter()*)defer
  (*RCU_exit()*) defer
  (*RCU_enter()*)defer
  apply(simp add:abbr FAAZ_def get_C_val_def)
  apply(simp add:covered_v_def visible_writes_def observation_inv_sig_def)
  apply(simp add:lastWr_def) apply clarify
                      defer
  apply (simp add: observation_inv_sig_def) apply clarify
  apply(simp add:abbr) apply clarsimp
  apply(simp add:general_structure_lemmas main_inv_lemmas own\<^sub>W_n_by_t_imp_def Wcap_def Rcap_def)
  unfolding covered_v_def writes_on_def
  apply clarify
  sledgehammer


















(*--------------------------------------------------------------------*)


lemma preservation_of_variables_1_by_others:
  assumes "preCond ms ps \<sigma> (pc ms t) t"
  and "t \<le> T_max"
  and "ta \<le> T_max"
  and "step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "ta \<noteq> t"
shows "n ms ta = n ms' ta"
  using assms
  apply(simp add:step_def)
  apply(simp add:preCond_def)
  apply(case_tac "pc ms t", simp_all)
  apply(simp_all add:abbr)
  apply clarify
  apply(simp_all add:general_structure_lemmas) apply clarsimp  apply(simp add:get_C_val_def)
  apply(simp add:FAAZ_def)
  apply(simp add: visible_writes_def)
  apply clarsimp
  apply clarsimp 
  apply clarsimp
  apply(case_tac "snd (CAS t (a, b) (the (s ms t)) (the (n ms t)) \<sigma> ts')", simp_all)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply(clarsimp)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply(clarsimp)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply(clarsimp)
  by(case_tac "reg ms t = Suc 0", simp_all add:abbr)

lemma preservation_of_variables_2_by_others:
  assumes "preCond ms ps \<sigma> (pc ms t) t"
  and "t \<le> T_max"
  and "ta \<le> T_max"
  and "step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "ta \<noteq> t"
shows "s ms ta = s ms' ta"
  using assms 
  apply(simp add:step_def)
  apply(simp add:preCond_def)
  apply(case_tac "pc ms t", simp_all)
  apply(simp_all add:abbr)
  apply clarify
  apply(simp_all add:general_structure_lemmas)apply(simp add:get_C_val_def)
  apply(simp add:FAAZ_def)
  apply(simp add: visible_writes_def) 
  apply clarsimp
  apply clarsimp
  apply clarsimp
  apply(case_tac "snd (CAS t (a, b) (the (s ms t)) (the (n ms t)) \<sigma> ts')", simp_all)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply(clarsimp)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply(clarsimp)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply(clarsimp)
  by(case_tac "reg ms t = Suc 0", simp_all add:abbr)

lemma preservation_of_variables_3_by_others:
  assumes "preCond ms ps \<sigma> (pc ms t) t"
  and "t \<le> T_max"
  and "ta \<le> T_max"
  and "step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "ta \<noteq> t"
shows "det ms ta = det ms' ta"
  using assms
  apply(simp add:step_def)
  apply(simp add:preCond_def)
  apply(case_tac "pc ms t", simp_all)
  apply(simp_all add:abbr)
  apply clarify
  apply(simp_all add:general_structure_lemmas)apply(simp add:get_C_val_def)
  apply(simp add:FAAZ_def)
  apply(simp add: visible_writes_def) 
  apply clarsimp
  apply clarsimp
  apply clarsimp
  apply(case_tac "snd (CAS t (a, b) (the (s ms t)) (the (n ms t)) \<sigma> ts')", simp_all)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply(clarsimp)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply(clarsimp)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply(clarsimp)
  by(case_tac "reg ms t = Suc 0", simp_all add:abbr)
lemma preservation_of_variables_inset_by_others:
  assumes "preCond ms ps \<sigma> (pc ms t) t"
  and "t \<le> T_max"
  and "ta \<noteq> t"
  and "ta \<le> T_max"
  and "step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "own\<^sub>W ms loc = Some ta"
  and "observation_inv_ms ms"
shows "(loc \<in> (detaddrs ms' ta) \<or> Some loc = s ms' ta \<or> Some loc = n ms' ta)"
  using assms 
  apply(subgoal_tac "(det ms' ta) = (det ms ta)") prefer 2 
  using preservation_of_variables_3_by_others
  apply force
  apply(subgoal_tac "the (s ms' ta) = the (s ms ta)") prefer 2 
  using preservation_of_variables_2_by_others
  apply force
  apply(subgoal_tac "the (n ms' ta) = the (n ms ta)") prefer 2 
  using preservation_of_variables_1_by_others
  apply force 
  apply(simp add:observation_inv_ms_def) 
  by (metis assms(5) preservation_of_variables_1_by_others preservation_of_variables_2_by_others)+
  




lemma preservation_of_variables_ninset_by_others:
  assumes "preCond ms ps \<sigma> (pc ms t) t"
  and "t \<le> T_max"
  and "ta \<noteq> t"
  and "ta \<le> T_max"
  and "step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "(loc \<notin> (detaddrs ms ta) \<and> Some loc \<noteq> s ms ta \<and> Some loc \<noteq> n ms ta)"
  and "observation_inv_ms ms"
shows "(loc \<notin> (detaddrs ms' ta) \<and> Some loc \<noteq> s ms' ta \<and> Some loc \<noteq> n ms' ta)"
  using assms apply simp
  by (simp add: preservation_of_variables_1_by_others 
                preservation_of_variables_2_by_others 
                preservation_of_variables_3_by_others)
lemma preservation_of_ownership_by_others:
  "preCond ms ps \<sigma> (pc ms t) t
\<Longrightarrow> own\<^sub>W ms loc = Some ta 
\<Longrightarrow> ta\<noteq>t 
\<Longrightarrow> ta\<le>T_max
\<Longrightarrow> t\<le>T_max
\<Longrightarrow> main_inv_2 ms ps
\<Longrightarrow> main_inv_3 ms ps
\<Longrightarrow> observation_inv_ms ms
\<Longrightarrow> own\<^sub>W_n_by_t_imp ms
\<Longrightarrow> general_structure ms
\<Longrightarrow> step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' 
     \<Longrightarrow> own\<^sub>W ms' loc = Some ta"
  apply(simp add:step_def)
  apply(case_tac "pc ms t", simp_all add:abbr)
  (*n:=newint*) defer
  (*FAAZ*) defer
  apply force
  (*cas_step_rcu*) defer
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply force
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t", simp_all add:abbr)
  (*kill*) defer
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply force
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply force
  apply(case_tac "reg ms t = Suc 0", simp_all add:abbr)
  apply clarsimp
  apply(case_tac "loc = loca", simp_all)
  using get_C_val_def mstate.simps(17) apply force apply clarify
  apply(case_tac "snd (CAS t (a, b) (the (s ms t)) (the (n ms t)) \<sigma> ts')", simp_all)
  apply(simp add:observation_inv_ms_def)
  apply(subgoal_tac "loc \<in> (detaddrs ms ta \<union> s_and_n ms ta)") prefer 2
  apply(simp add:detaddrs_def s_and_n_def)
  apply(simp add:general_structure_lemmas)
  apply(simp add:preCond_def)
  apply meson
  apply(simp add:general_structure_lemmas)
  apply(simp add:preCond_def observation_inv_ms_def own\<^sub>W_n_by_t_imp_def)
  apply(case_tac "Some loc = (n ms ta)") 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv option.distinct(1) option.sel)
  apply (metis (no_types, lifting) option.sel)
  apply(simp add:preCond_def Wcap_def) 
  apply (metis option.sel)
  apply(simp add:preCond_def Wcap_def) 
  apply(simp add:general_structure_lemmas)
  (*ta cannot own\<^sub>W ms LOC where LOC \<in> det_addrs ms t*) 
  sorry
  
  

lemma preservation_of_nownership_by_others:
  "preCond ms ps \<sigma> (pc ms t) t
\<Longrightarrow> own\<^sub>W ms loc \<noteq> Some ta 
\<Longrightarrow> ta\<noteq>t 
\<Longrightarrow> t\<le>T_max 
\<Longrightarrow> ta\<le>T_max
\<Longrightarrow> step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' 
     \<Longrightarrow> own\<^sub>W ms' loc \<noteq> Some ta"
  apply (simp add:step_def)
  apply(case_tac "pc ms t", simp_all add:abbr)
  apply safe
  apply (smt (z3) fun_upd_apply mstate.simps(17) mstate.surjective mstate.update_convs(1) mstate.update_convs(16) mstate.update_convs(17) option.sel)
  apply(simp add:get_C_val_def FAAZ_def)
  apply safe 
  apply simp+
  apply(case_tac "loc = the (n ms t)", simp_all)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  by(case_tac "reg ms t = Suc 0", simp_all add:abbr)


lemma preservation_of_observation_inv_ms:
  assumes "preCond ms ps \<sigma> (pc ms t) t"
  and "t \<le> T_max"
  and "step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "observation_inv_ms ms"
  and "main_inv_2 ms ps"
  and "main_inv_3 ms ps"
  and "observation_inv_sig ms ps \<sigma>"
  and "own\<^sub>W_n_by_t_imp ms"
  and "general_structure ms"
  and "psem_rules ps"
shows "observation_inv_ms ms'"
  using assms unfolding observation_inv_ms_def apply simp apply clarify
  apply(case_tac "ta \<noteq> t")
  (*ta\<noteq>t*)
  apply(simp add:step_def preCond_def)
  apply(case_tac "pc ms t", simp_all add:abbr)
  apply clarsimp 
  apply blast
  apply blast
  apply blast 
  apply clarsimp 
  apply (meson own\<^sub>W_n_by_t_imp_def)
  apply (meson own\<^sub>W_n_by_t_imp_def)
  apply (meson own\<^sub>W_n_by_t_imp_def)
  apply (meson own\<^sub>W_n_by_t_imp_def)
  (*FAAZ, ta\<noteq>t*) defer
  apply(simp add:Wcap_def own\<^sub>W_n_by_t_imp_def general_structure_lemmas Rcap_def)
  sledgehammer







  sorry




























lemma own\<^sub>W_imp_not_free:
  assumes "main_inv ms ps"
  and "own\<^sub>W ms loc \<noteq> None"
shows "\<not>isfree_addr loc ps"
  using assms apply (simp_all add:main_inv_def)
  by blast




lemma global_sig_invariant_preserved:
  "con_assms ps \<Longrightarrow>
main_inv ms ps\<Longrightarrow>
observation_inv_ms ms\<Longrightarrow>
main_inv_2 ms ps\<Longrightarrow> 
main_inv_3 ms ps\<Longrightarrow> 
observation_inv_sig ms ps \<sigma>\<Longrightarrow> 
own\<^sub>W_n_by_t_imp ms\<Longrightarrow> 
general_structure ms\<Longrightarrow> 
psem_rules ps\<Longrightarrow> 
t \<le> T_max\<Longrightarrow>
step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'\<Longrightarrow>
preCond ms ps \<sigma> (pc ms t) t\<Longrightarrow>
observation_inv_sig ms' ps' \<sigma>'
"
  unfolding observation_inv_sig_def step_def preCond_def
  apply(case_tac "pc ms t", simp_all add:abbr covered_v_def con_assms_def main_inv_def observation_inv_ms_def)
  apply(simp_all add:own\<^sub>W_n_by_t_imp_def general_structure_lemmas)
  apply meson
  apply meson
  apply meson
  apply (metis domI domIff)  apply clarsimp sledgehammer
  apply (metis domI domIff)
  apply (metis domI domIff)
  apply meson
  apply meson
  apply meson












lemma ms_observation_lemma_Correctness_supp_4:
  assumes "preCond ms ps \<sigma> (pc ms t) t"
  and "t \<le> T_max"
  and "ta \<le> T_max"
  and "step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "ta \<noteq> t" 
  and "own\<^sub>W ms loc = Some ta"
  and "main_inv ms"
  and "main_inv_2 ms ps"
  and "main_inv_3 ms ps"
  and "observation_inv_ms ms"
shows "own\<^sub>W ms' loc = Some ta"
  using assms 
  apply(subgoal_tac "\<not>isfree_addr loc ps") prefer 2
  apply (metis option.distinct(1) own_imp_1) apply (simp_all)
  apply(simp add:step_def)
  apply(simp add:preCond_def)
  apply(case_tac "pc ms t", simp_all)
  apply(simp_all add:abbr)
  apply clarify
  apply(simp_all add:general_structure_lemmas)
  apply(subgoal_tac "loc\<noteq>loca", simp_all add:Rcap_def Wcap_def) 
  apply clarsimp apply(simp add:get_C_val_def)
  apply(simp add:FAAZ_def)
  apply(simp add: visible_writes_def)  apply clarsimp 
  apply clarsimp 
  apply(simp add: visible_writes_def)   apply clarsimp
  apply(case_tac "(snd (CAS t (a, b) (the (s ms t)) (the (n ms t)) \<sigma> ts'))", simp_all)
  apply (metis option.sel)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr) apply clarsimp
  apply(case_tac "nondet_val ms t", simp_all add:abbr) apply clarsimp
  apply(case_tac "det ms t", simp_all add:abbr observation_inv_ms_def) apply clarify
  apply clarsimp
  sorry





lemma FAAZ_wm_prelim1:
  assumes "ms \<sigma> s:=\<^sup>FC t ms' \<sigma>'"
  and "wfs \<sigma>"
  and "cvd[C,valaa] \<sigma>"
shows "cvd[C,valaa] \<sigma>'"
  using assms apply (simp add:get_C_val_def FAAZ_def) apply(clarify) 
  apply(simp add:update_trans_def covered_v_def Let_def rev_app_def add_cv_def update_mods_def update_modView_def
      update_thrView_def)
  apply(unfold writes_on_def value_def lastWr_def) apply safe
  apply (metis fst_conv var_def)
  apply (metis fst_conv var_def visible_var)
  apply (metis fst_conv var_def visible_var)
  apply (metis fst_conv var_def)
  apply(simp add:visible_writes_def tst_def var_def valid_fresh_ts_def)
  apply(unfold writes_on_def value_def lastWr_def wfs_def var_def) apply safe
  (*ts; is max, nempty \<and> finite*) defer
  apply auto[1]    
  apply(simp) apply(intro conjI)
  apply (meson subset_iff visible_writes_in_writes)
  apply presburger
  apply (metis fst_conv)
  apply (metis fst_conv var_def visible_var)
  apply (metis fst_conv var_def visible_var)
  apply (metis fst_conv)
  (*ts; is max*) defer    
  apply(simp) apply(intro conjI)
  apply (meson subset_iff visible_writes_in_writes)
  apply presburger
  sorry

lemma FAAZ_wm_prelim2:
  assumes "ms \<sigma> s:=\<^sup>FC t ms' \<sigma>'"
  and "wfs \<sigma>"
  and "\<exists>val. cvd[C,val] \<sigma> \<and> val\<noteq> loca"
shows "\<exists>val. cvd[C,val] \<sigma>' \<and> val\<noteq> loca"
  using assms
  using FAAZ_wm_prelim1 by blast

lemma FAAZ_wm_prelim3:
  assumes "ms \<sigma> s:=\<^sup>FC t ms' \<sigma>'"
  and "wfs \<sigma>"
  and "cvd[C,valaa] \<sigma>"
  and "valaa \<noteq> loca"
shows "\<exists>val. cvd[C,val] \<sigma>' \<and> val\<noteq> loca"
  using assms 
  using FAAZ_wm_prelim1 by blast

lemma FAAZ_wm_prelim4:
  assumes "ms \<sigma> s:=\<^sup>FC t ms' \<sigma>'"
  and "wfs \<sigma>"
  and "observation_inv_sig ms ps \<sigma>"
  and "psem_rules ps "
  and "general_structure ms"
shows "observation_inv_sig ms' ps' \<sigma>'"
  using assms 
  apply(simp add:observation_inv_sig_def general_structure_lemmas)
  apply clarify
  apply(intro conjI impI)
  apply(case_tac "ta = t")
  apply(subgoal_tac "own\<^sub>W ms loc = Some ta \<longrightarrow> own\<^sub>W ms' loc = Some ta", simp_all)
  apply(simp add:get_C_val_def)
  sledgehammer




lemma sigma_observation_lemma_Correctness:
  assumes "preCond ms ps \<sigma> (pc ms t) t"
  and "wfs \<sigma>"
  and "psem_rules ps"
  and "t \<le> T_max"
  and "step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "observation_inv_ms ms"
  and "observation_inv_sig ms ps \<sigma>"
  and "main_inv ms"
  and "main_inv_2 ms ps"
  and "main_inv_3 ms ps"
shows "observation_inv_sig ms' ps' \<sigma>'"
  using assms apply (simp_all)
  apply(simp add:preCond_def RCU.step_def)
  apply(case_tac "pc ms t", simp_all add:abbr)
  apply(simp add:covered_v_def general_structure_lemmas )
  apply clarify
  apply(unfold observation_inv_sig_def observation_inv_ms_def)
  apply clarify apply(simp_all)
  apply(case_tac "isfree_addr loc ps", simp_all)
  apply blast apply clarify
  apply(case_tac "isfree_addr loc ps", simp_all)
  apply clarify
  apply(case_tac "isfree_addr loc ps", simp_all)
  apply clarify apply(simp add:general_structure_lemmas)
  apply(case_tac "loc = loca", simp_all) 
  apply metis 
  apply meson 
  defer (*rcu_enter*)
  defer (*rcu_exit*)
  defer (*rcu_enter*)
  apply clarify
  apply(intro conjI impI)
  using FAAZ_wm_prelim2 [where ms = ms and ms' = ms' and \<sigma> = \<sigma> and \<sigma>' = \<sigma>' and t=t and loca=loc]
  apply simp
  apply(clarsimp)
  apply(case_tac "t \<le> T_max \<and> own\<^sub>W ms loca = Some t", simp_all)
  apply (meson FAAZ_wm_prelim1)
  apply(case_tac "((\<forall>x. (\<forall>a. x = {a} \<longrightarrow> (\<forall>b. (a, b) \<notin> ran (A ps))) \<or> loca \<notin> x))")
  apply (metis FAAZ_wm_prelim1)
  apply clarify
  sledgehammer


  apply metis
  apply(simp add:general_structure_lemmas)
  sledgehammer


  by (metis (full_types))+



lemma ms_observation_lemma_Correctnesssss:
  assumes "preCond ms ps \<sigma> (pc ms t) t"
  and "wfs \<sigma>"
  and "psem_rules ps"
  and "t \<le> T_max"
  and "step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "observation_inv_ms ms ps"
  and "observation_inv_sig ms ps \<sigma>"
  and "main_inv ms"
  and "main_inv_2 ms ps"
  and "main_inv_3 ms ps"
  and "cvd[C,vala] \<sigma>"
shows "observation_inv_ms ms' ps'"
  using assms apply (simp_all) 
  apply(simp add:preCond_def)
  apply(case_tac "pc ms t", simp_all)
  apply(simp add:covered_v_def general_structure_lemmas)
  apply clarify
  apply(unfold observation_inv_sig_def observation_inv_ms_def)
  apply(subgoal_tac "\<forall>loc t. t\<le>T_max \<and> own\<^sub>W ms' loc  = Some t
  \<longrightarrow> loc\<in>(detaddrs ms' t \<union> s_and_n ms' t) ") 
  apply clarify
  apply(subgoal_tac "loc \<in> detaddrs ms ta", simp add:detaddrs_def)
  apply blast

  sorry











lemma main_invariant_Correctness:
  assumes "preCond ms ps \<sigma> pcr t"
  and "t \<le> T_max"
  and "main_inv ms"
  and "main_inv_2 ms ps"
  and "pcr = pc ms t"
  and "step ms ps \<sigma> pcr t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "pcr' = pc ms' t"
  and "observation_inv_ms ms ps"
  and "observation_inv_sig ms ps \<sigma>"
shows "main_inv ms'"
  using assms apply (simp add:preCond_def step_def)
  apply(case_tac[!] "pc ms t", simp_all add:abbr) 
  apply(intro allI)
  apply(intro impI) apply(elim conjE exE) apply(simp add:isfree_addr_def) 
  apply (metis insert_not_empty option.sel) 
  apply(intro allI)
  apply(simp add:general_structure_lemmas)
  apply metis
  defer (*I8*)
  defer (*I9*)
  defer (*I11*)
  apply(simp add:general_structure_lemmas)
  apply metis 
  apply(case_tac "CAS_succ ms t", simp_all)
  apply(simp_all add:abbr)
  defer (*R2*)
  apply(simp add:general_structure_lemmas) apply(case_tac "nondet_val ms t = True", simp_all)
  apply(simp_all add:abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all) 
  apply(simp_all add:abbr)
  apply(simp add:general_structure_lemmas)
  apply (metis Diff_empty Diff_insert0 insert_absorb insert_iff)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(simp_all add:abbr)
  defer (*S3*)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all)
  apply(simp_all add:abbr)
  defer (*S6*)
  apply(case_tac "reg ms t = Suc 0", simp_all)
  apply(simp add:abbr)
  apply(simp add:abbr)
  apply(clarify) 
  apply(simp add:get_C_val_def) 
  apply(subgoal_tac "(snd (FAAZ t (a, b) \<sigma> ts')) \<noteq> the(n ms ta)", simp add:FAAZ_def) (*need this as pre_cond*)
  
        apply (metis option.sel)
  defer
  apply clarify
  apply(subgoal_tac "own\<^sub>R ms (the(n ms ta)) = {ta}") prefer 2
  apply(simp add:general_structure_lemmas) 
  apply (metis option.sel)
  apply(simp add:general_structure_lemmas)  
  apply clarify
  apply(case_tac "snd (CAS t (a, b) (the (s ms t)) (the (n ms t)) \<sigma> ts') ")
  apply(subgoal_tac "n_dec ms' t = False") prefer 2
  apply(simp add:general_structure_lemmas)
  apply(simp add:general_structure_lemmas)  
  apply (metis option.sel)
  apply(simp add:general_structure_lemmas)  
  apply (metis option.sel)                      
  apply(simp add:general_structure_lemmas)  
  apply clarify
  apply(case_tac "b", simp_all) prefer 2 
  apply (metis option.sel) 
  apply (metis option.sel)                     
  apply(simp add:general_structure_lemmas)
  apply clarify apply(simp add:names_2)
  apply (metis option.sel)                  
  apply(simp add:general_structure_lemmas)
  apply clarify
  apply(case_tac "v", simp_all) prefer 2
  apply (metis option.sel)
  apply (metis option.sel)
  apply(simp add: visible_writes_def) 
  apply(simp add:observation_lemma_def general_structure_lemmas covered_v_def FAAZ_def)  
  apply(simp add:Wcap_def)
  by (metis option.sel)
  




lemma main_invariant_2_Correctness:
  assumes "preCond ms ps \<sigma> pcr t"
  and "t \<le> T_max"
  and "main_inv ms"
  and "main_inv_2 ms ps"
  and "pcr = pc ms t"
  and "step ms ps \<sigma> pcr t ms' ps' \<sigma>'"       (*and "allocated_n_addr ms ps "     seems redundant*)
  and "general_structure ms"
  and "pcr' = pc ms' t"
  and "observation_lemma \<sigma> ms"
shows "main_inv_2 ms' ps'"
  using assms apply simp
  apply(simp add:step_def) apply(case_tac "pc ms t", simp_all add:abbr)     
  apply(simp add:general_structure_lemmas preCond_def)
  apply(elim conjE exE, intro allI impI)
  apply(simp add:names_2)    
  (*FAAZ*)
  defer     
  apply(simp add:general_structure_lemmas preCond_def)
  apply(elim conjE exE, intro allI impI)
  apply(simp add:names_2)       
  apply(simp add:general_structure_lemmas preCond_def)
  apply(elim conjE exE, intro allI impI)
  apply(simp add:names_2)  
  apply(case_tac "snd (CAS t (a, b) (the (s ms t)) y \<sigma> ts') ") prefer 2
  apply simp
  apply simp
  apply(case_tac "CAS_succ ms t", simp_all)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(elim conjE exE, intro allI impI)
  apply(simp add:names_2)       
  apply(case_tac "nondet_val ms t", simp_all)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(elim conjE exE, intro allI impI)
  apply(simp add:names_2)       
  (*show that own\<^sub>R ms i \<in> det ms t \<longrightarrow> at some point is only held by {t}*)
  defer
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(elim conjE exE, intro allI impI)
  apply(simp add:names_2)     
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(elim conjE exE, intro allI impI)
  apply(simp add:names_2)         
  apply(case_tac "reg ms t = Suc 0", simp_all)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  (*FAAZ*)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(elim conjE exE, intro allI impI)
  apply(simp add:names_2)   
   defer
  
  sledgehammer
  oops



lemma General_Structure_Correctness:
  assumes "preCond ms ps \<sigma> pcr t"
  and "t \<le> T_max"
  and "main_inv ms"
  and "main_inv_2 ms ps"
  and "pcr = pc ms t"
  and "step ms ps \<sigma> pcr t ms' ps' \<sigma>'"       
  and "general_structure ms"
  and "pcr' = pc ms' t"
  and "observation_lemma \<sigma> ms"
  and "\<exists>prov loc. prov \<notin> dom(A ps) \<and> isfree_addr loc ps"
shows "general_structure ms'"
  using assms apply simp
  apply(simp add:step_def) apply(case_tac "pc ms t", simp_all add:abbr)     
  apply(simp_all add:general_structure_lemmas preCond_def names_2)
  apply metis
  apply metis 
  defer
  apply metis 
  defer
  defer
  defer
  apply metis
  defer
  defer
  apply(elim conjE exE)
  apply(case_tac "b", simp_all)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t = []", simp_all add:abbr)
  defer
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  defer
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  defer
  apply(case_tac "reg ms t = Suc 0", simp_all add:abbr)
  prefer 2
  apply(simp add:FAAZ_def)
  apply(simp add:allocated_addresses_def observation_lemma_def)
  apply (metis option.sel)
  apply(intro conjI impI) prefer 2
  apply clarify
  apply(case_tac "ta = t", simp_all) prefer 2
  apply (metis option.sel) apply clarify
  apply(intro conjI impI)
  apply(subgoal_tac "y \<notin> alloc_addrs ps") prefer 2
  apply blast
  apply(subgoal_tac "the (s ms t) \<in> alloc_addrs ps") 
  apply blast
  apply(subgoal_tac "allocated_addresses ms ps", simp_all add:allocation_lemmas)
  oops




lemma Global_Correctness:
  assumes "preCond ms ps \<sigma> pcr\<^sub>t t"
  and "preCond ms ps \<sigma> pcr\<^sub>t\<^sub>' t'"  
  and "pcr\<^sub>t = pc ms t"
  and "pcr\<^sub>t\<^sub>' = pc ms t'"
  and "t \<noteq> t'"
  and "main_inv ms"
  and "main_inv_2 ms ps"
  and "step ms ps \<sigma> pcr\<^sub>t t ms' ps' \<sigma>'"       (*and "allocated_n_addr ms ps "     seems redundant*)
  and "general_structure ms"
  and "pcr' = pc ms' t"
shows "preCond ms' ps' \<sigma>' pcr\<^sub>t\<^sub>' t'"
  using assms apply simp
  apply(simp add:step_def) apply(case_tac "pc ms t", simp_all add:abbr)     
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2) 
  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis        
 
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)  
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis        
  
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis  

  (*existential complication*) defer
  apply(simp add:general_structure_lemmas preCond_def) 
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)  
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis        
  
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis  
  
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis  
  
  (*existential complication, FAAZ*) defer
  (*weak memory read s*)defer
  
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  
  (*existential complication, CAS*)defer
   
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)  
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
   
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)  
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
   
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)  
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis

  apply(case_tac "CAS_succ ms t", simp_all)
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)  
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis

  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis 
  
  apply(simp add:general_structure_lemmas preCond_def)
  apply(elim conjE impE exE)
  apply(case_tac "b", simp_all)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2) 
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis 
  apply(case_tac "pc ms t'", simp_all add:abbr names_2) 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis

  apply(case_tac "nondet_val ms t", simp_all)
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  
  apply(case_tac "det ms t \<noteq> []", simp_all)
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  
  (*existential complication, kill(x)*)defer
  
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  
  (*existential complication, (rcu_0 + CTRsync\<^sub>1) weak memory read*)defer
  
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all)
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  
  defer

  apply(case_tac "reg ms t = Suc 0", simp_all) 
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis

(*weak memory guarantees needed, I think (maybe I'm wrong)*)
  oops







(*lemma test2:
  assumes "wfs \<sigma>"
  and "get_C_val ms \<sigma> t ms' \<sigma>'"
  and "cvd[C,u] \<sigma>"
shows "cvd[C,u] \<sigma>'"
  using assms apply (simp add:get_C_val_def FAAZ_def) apply(clarify) 
  apply(simp add:update_trans_def covered_v_def Let_def rev_app_def add_cv_def update_mods_def update_modView_def
      update_thrView_def)
  apply(unfold writes_on_def value_def lastWr_def) apply safe
  apply (metis fst_conv var_def)
  apply (metis fst_conv var_def visible_var)
  apply (metis fst_conv var_def visible_var)
  apply (metis fst_conv var_def)
  apply(simp add:visible_writes_def tst_def var_def valid_fresh_ts_def)
  apply(unfold writes_on_def value_def lastWr_def wfs_def var_def) apply safe
  (*ts; is max, nempty \<and> finite*) defer
  apply auto[1]    
  apply(simp) apply(intro conjI)
  apply (meson subset_iff visible_writes_in_writes)
  apply presburger
  apply (metis fst_conv)
  apply (metis fst_conv var_def visible_var)
  apply (metis fst_conv var_def visible_var)
  apply (metis fst_conv)
  (*ts; is max*) defer    
  apply(simp) apply(intro conjI)
  apply (meson subset_iff visible_writes_in_writes)
  apply presburger
  sorry*)




          
(*
OWNERSHIP IDEAS:


\<forall>i. (i\<in>addrs) \<longleftrightarrow> (the(own\<^sub>W ms i)=t)


We have to get to this stage after sync():
\<forall>s i j. (s\<in>det\<^sub>i \<and> i\<noteq>j) \<longrightarrow> T\<^sub>j \<notin> own\<^sub>R(s)

because:
 T\<^sub>j \<notin> own\<^sub>R(s) \<longrightarrow> T\<^sub>j \<noteq> own\<^sub>W(s)

This allows for pop() operation to guarantee that no thread could allocate n:=newint as n:=s
unless:

own\<^sub>W(s) = T\<^sub>i \<and> own\<^sub>R(s) = { T\<^sub>i }
pop()
own\<^sub>W(s) = None \<and> own\<^sub>R(s) = {}


(Call threads t, t...)

This is absolutely guaranteed if sync() occurs deterministically:
\<forall>j. j<N \<longrightarrow> |det\<^sub>j| \<le> 1
\<forall>s j i. (s\<in>det\<^sub>j \<and> i\<noteq>j \<and> i<CTRsync\<^sub>1(j) \<and> r[i] = 0) \<longrightarrow> T\<^sub>i \<notin> own\<^sub>R(s)     (backward sync)
\<forall>s j i. (s\<in>det\<^sub>j \<and> i\<noteq>j \<and> i<CTRsync\<^sub>2(j)) \<longrightarrow> T\<^sub>i \<notin> own\<^sub>R(s)                (backward sync)
\<forall>s j i. (s\<in>det\<^sub>j \<and> i\<noteq>j \<and> CTRsync\<^sub>2(j) < N \<and> i = CTRsync\<^sub>2(j) \<and> [rcu[i] \<approx> 0]\<^sub>j) \<longrightarrow> T\<^sub>i \<notin> own\<^sub>R(s)                (backward sync)
No thread i. (j\<noteq>i) can allocate n:=newint to have address s, since own\<^sub>W(s) = T\<^sub>j
If a thread i attemps to read s=C while in rcu[i] (weak memory), this can only happen if:
CTRsync\<^sub>1 = N \<and> r[i] = 1 \<and> i\<ge>CTRsync\<^sub>2
In that case, it should be impossible for CAS\<^sub>j to succeed, resulting in eventual rcu_exit() by j with no swap,
(no matter how many times j performs rcu_enter()/rcu_exit()       ***careful in WM setting - fence*** )
which should cause {while rcu[j]} to terminate and perform CTRsync\<^sub>2++

Nondeterministically:
\<forall>j. j<N \<longrightarrow> |det\<^sub>j| \<ge> 0
\<forall>s j i. (s\<in>det\<^sub>j \<and> i\<noteq>j \<and> i<CTRsync\<^sub>2) \<longrightarrow> T\<^sub>i \<notin> own\<^sub>R(s)                (backward sync)
\<forall>s j i. (s\<in>det\<^sub>j \<and> i\<noteq>j \<and> i<CTRsync\<^sub>1 \<and> r[i] = 0) \<longrightarrow> T\<^sub>i \<notin> own\<^sub>R(s)     (backward sync)

only requirement is that own\<^sub>W(s) = T\<^sub>j to limit allocation of n:=newint to s by T\<^sub>i
T\<^sub>j faces the same problem, since n:=newint, where newint=s, requires own\<^sub>W(s) = Null.



REASONS FOR OWNERSHIP OVER NO-OWNERSHIP:
limited in Deterministic setting.
no requirement of insert(det\<^sub>j) to track order of insertion.
ease of visualisation when n:=newint happens


pop of A\<^sub>2 doesnt occur.
*)

(*definition "FAAZ t w \<sigma> ts' \<equiv> 
        (update_trans t w (value \<sigma> w) \<sigma> ts', value \<sigma> w)"*)



