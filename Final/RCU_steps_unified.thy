theory RCU_steps_unified
imports RCU_I_steps RCU_R_steps RCU_S_steps RCU_wm_proofs
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

block_cond t t' u ms \<sigma>                  *done (wm_proofs)*
det_block t ms \<sigma>                        *done*
det_block t' ms \<sigma>                       *done (wm_proofs)*

*)









lemma steps_breakdown:
  "pc ms t \<in> I_steps \<or> pc ms t \<in> R_steps \<or> pc ms t \<in> S_steps"
  apply(simp)
  using PC.exhaust by blast

lemma showing_main_inv:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  main_inv ms' ps'"
  apply(subgoal_tac "pc ms t \<in> I_steps \<or> pc ms t \<in> R_steps \<or> pc ms t \<in> S_steps") prefer 2 apply auto[1]
  using PC.exhaust 
  apply blast
  apply(elim disjE)
  using showing_main_inv_for_I apply blast
  using showing_main_inv_for_R apply blast
  using showing_main_inv_for_S by blast


lemma showing_psem_rules:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  psem_rules ps'" 
  apply(subgoal_tac "pc ms t \<in> I_steps \<or> pc ms t \<in> R_steps \<or> pc ms t \<in> S_steps") prefer 2 apply auto[1]
  using PC.exhaust 
  apply blast
  apply(elim disjE)
  using showing_psem_rules_for_I apply blast
  using showing_psem_rules_for_R apply blast
  using showing_psem_rules_for_S by blast


lemma allocated_addresses_preservation_for_I:
  "main_inv ms ps \<Longrightarrow> 
  t<T_max \<Longrightarrow>
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
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  allocated_addresses ms' ps'"
  apply(subgoal_tac "pc ms t \<in> I_steps \<or> pc ms t \<in> R_steps \<or> pc ms t \<in> S_steps") prefer 2 apply auto[1]
  using PC.exhaust 
  apply blast
  apply(elim disjE)
  using allocated_addresses_preservation_for_I apply blast
  using showing_allocated_addresses_for_R apply blast
  using showing_allocated_addresses_for_S by blast


lemma Local_correctness_observation_inv_ms:
  "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms  \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> 
  observation_inv_ms ms'"
  apply(subgoal_tac "pc ms t \<in> I_steps \<or> pc ms t \<in> R_steps \<or> pc ms t \<in> S_steps") prefer 2 apply auto[1]
  using PC.exhaust 
  apply blast
  apply(elim disjE)
  using Local_correctness_observation_inv_ms_for_I apply blast
  using showing_observation_inv_ms_for_R apply blast
  using showing_observation_inv_ms_for_S by blast

 
lemma showing_observation_inv_sig:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  observation_inv_sig ms' ps' \<sigma>'" 
  apply(subgoal_tac "pc ms t \<in> I_steps \<or> pc ms t \<in> R_steps \<or> pc ms t \<in> S_steps") prefer 2 apply auto[1]
  using PC.exhaust 
  apply blast
  apply(elim disjE)
  using showing_observation_inv_sig_for_I apply blast
  using showing_observation_inv_sig_for_R apply blast
  using showing_observation_inv_sig_for_S by blast


lemma showing_own\<^sub>W_n_by_t_imp:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms'" 
  apply(subgoal_tac "pc ms t \<in> I_steps \<or> pc ms t \<in> R_steps \<or> pc ms t \<in> S_steps") prefer 2 apply auto[1]
  using PC.exhaust 
  apply blast
  apply(elim disjE)
  using showing_own\<^sub>W_n_by_t_imp_for_I apply blast
  using showing_own\<^sub>W_n_by_t_imp_for_R apply blast
  using showing_own\<^sub>W_n_by_t_imp_for_S by blast


lemma showing_general_structure:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  general_structure ms'" 
  apply(subgoal_tac "pc ms t \<in> I_steps \<or> pc ms t \<in> R_steps \<or> pc ms t \<in> S_steps") prefer 2 apply auto[1]
  using PC.exhaust 
  apply blast
  apply(elim disjE)
  using showing_general_structure_for_I apply blast
  using showing_general_structure_for_R apply blast
  using showing_general_structure_for_S by blast


lemma showing_local_preCond:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  T_limitation ms \<Longrightarrow>
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
  apply(subgoal_tac "pc ms t \<in> I_steps \<or> pc ms t \<in> R_steps \<or> pc ms t \<in> S_steps") prefer 2 apply auto[1]
  using PC.exhaust 
  apply blast
  apply(elim disjE)
  using showing_local_preCond_for_I apply blast
  using showing_local_preCond_for_R apply blast
  using showing_local_preCond_for_S by blast


lemma showing_global_preCond:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  ta<T_max \<Longrightarrow>
  ta \<noteq> t \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  preCond ms ps (pc ms ta) ta \<Longrightarrow>
  general_structure ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  preCond ms' ps' (pc ms' ta) ta" 
  apply(subgoal_tac "pc ms t \<in> I_steps \<or> pc ms t \<in> R_steps \<or> pc ms t \<in> S_steps") prefer 2 apply auto[1]
  using PC.exhaust 
  apply blast
  apply(elim disjE)
  using showing_global_preCond_for_I apply blast
  using showing_global_preCond_for_R apply blast
  using showing_global_preCond_for_S by blast


lemma showing_det_pres_local:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  book_keeping \<sigma> l t t' \<Longrightarrow> 
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  \<forall>t'. t'<T_max \<longrightarrow> block_cond t t' ms \<sigma>  \<Longrightarrow>
  det_block t ms \<sigma>  \<Longrightarrow>                    
  det_block t ms' \<sigma>'" 
  apply(subgoal_tac "pc ms t \<in> I_steps \<or> pc ms t \<in> R_steps \<or> pc ms t \<in> S_steps") prefer 2 apply auto[1]
  using PC.exhaust book_keeping_def
  apply blast 
  apply(elim disjE)
  using showing_det_pres_local_for_I book_keeping_def apply blast
  using showing_det_pres_local_for_R book_keeping_def apply blast
  using showing_det_pres_local_for_S book_keeping_def by blast






lemma full_inv_proof_init:
  "con_assms ms ps \<Longrightarrow>
  init ms ps \<sigma> \<Longrightarrow>
  full_inv ms ps \<sigma> "
  apply(simp add:init_def full_inv_def con_assms_def wfs_2_def)
  apply(intro conjI impI)
  apply(simp add:main_inv_lemmas)
  defer defer
  apply(simp add:allocated_addresses_lemmas) apply auto[1]
  apply (simp add: observation_inv_ms_def)
  apply (simp add: observation_inv_sig_def)
  apply(simp add:initial_alloc_map_def)
  apply (metis fst_conv testingthisone)
  apply (simp add: own\<^sub>W_n_by_t_imp_def)
  apply(simp add:general_structure_lemmas) apply auto[1]
  apply(simp add:initial_alloc_map_def)
  apply (metis fst_conv testingthisone)
  by (metis (no_types, lifting) fst_conv initial_alloc_map_def testingthisone)


lemma full_inv_proof_main:
  "wfs_2 \<sigma> \<Longrightarrow>
  con_assms ms ps \<Longrightarrow>
  book_keeping \<sigma> l t t' \<Longrightarrow>
  full_inv ms ps \<sigma> \<Longrightarrow>
  full_pre ms ps \<sigma> t \<Longrightarrow> 
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  full_inv ms' ps' \<sigma>' "
  apply(unfold full_inv_def full_pre_def)
  apply(intro conjI impI) 
  using showing_main_inv book_keeping_def apply blast 
  using showing_psem_rules book_keeping_def apply blast
  using RCU_steps_unified.allocated_addresses_preservation_for_I observation_inv_sig_def book_keeping_def apply blast
  using Local_correctness_observation_inv_ms book_keeping_def apply blast
  using showing_observation_inv_sig book_keeping_def apply blast
  using showing_own\<^sub>W_n_by_t_imp book_keeping_def apply blast
  using showing_general_structure book_keeping_def by blast
  

(*this one's second line IS part of init now,
didn't add in this screenshot otherwise the whole
thing would take another 15-20 minutes to load*)
lemma full_pre_init:
  "init ms ps \<sigma> \<Longrightarrow>
  \<forall>t. t<T_max \<longrightarrow> [(rcu_0 + t) =\<^sub>t 0] \<sigma> \<Longrightarrow> 
  \<forall>t. t<T_max \<longrightarrow> full_pre ms ps \<sigma> t "
  apply(simp add:init_def full_pre_def con_assms_def wfs_2_def)
  apply(simp add:preCond_def) apply clarify
  apply(intro conjI impI)
  apply(simp add:Rcap_def)
  apply(simp add:Wcap_def)
  apply(simp add:det_block_def) 
  apply(simp add:sigma_obs_def) 
  unfolding block_cond_def 
  apply clarify
  by(case_tac "pc ms t", simp_all)
  
(*T_limitation can be part of con_assms, to be honest 
 just mentions t | t>T_max (threads not part of program)*)
lemma full_pre_proof_local:
  "con_assms ms ps \<Longrightarrow>
  book_keeping \<sigma> l t t' \<Longrightarrow>
  T_limitation ms \<Longrightarrow>
  full_inv ms ps \<sigma> \<Longrightarrow>
  full_pre ms ps \<sigma> t \<Longrightarrow> 
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  full_pre ms' ps' \<sigma>' t "
  apply(unfold full_pre_def full_inv_def)  apply clarify
  apply(intro conjI impI) 
  apply (metis book_keeping_def showing_local_preCond) 
  apply(case_tac "pc ms t \<in> I_steps", simp_all)
  apply (metis Unique_allocs_def constant_alloc_ass_def newran_def psem_rules_def showing_det_pres_local_for_I showing_det_pres_local_for_R showing_det_pres_local_for_S steps_breakdown)
  apply (metis (mono_tags, lifting) CollectD I_step_breakdown showing_det_pres_local_for_R showing_det_pres_local_for_S steps_breakdown)
  using sigma_obs_preserved_forall apply blast
  by (metis Unique_allocs_def book_keeping_def constant_alloc_ass_def newran_def psem_rules_def showing_block_cond_pres_local_2)



lemma full_pre_proof_global:
  "con_assms ms ps \<Longrightarrow> 
  book_keeping \<sigma> l t t' \<Longrightarrow>
  full_inv ms ps \<sigma> \<Longrightarrow>
  \<forall>ta. ta>T_max \<and> ta\<noteq>t' \<longrightarrow> book_keeping \<sigma> l t' ta \<Longrightarrow>
  \<forall>t. t<T_max \<longrightarrow> full_pre ms ps \<sigma> t \<Longrightarrow> 
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  full_pre ms' ps' \<sigma>' t' "
  apply(unfold full_pre_def full_inv_def)  apply clarify
  apply(intro conjI impI) 
  apply (metis book_keeping_def showing_global_preCond) 
  apply (metis book_keeping_def full_inv_def showing_det_block_pres_global)
  apply (meson book_keeping_def sigma_obs_preserved_forall)
  apply clarify
  apply(subgoal_tac "con_assms ms ps") prefer 2 apply blast
  apply(subgoal_tac "book_keeping \<sigma> l t t'") prefer 2 apply blast
  apply(subgoal_tac "book_keeping \<sigma> l t t'") prefer 2 apply blast
  apply(subgoal_tac "book_keeping \<sigma> l t' t'a") prefer 2 
  apply (meson book_keeping_def con_assms_def reservations_differ_def)
  apply(subgoal_tac "full_inv ms ps \<sigma>") prefer 2 using full_inv_def apply blast
  apply(subgoal_tac "wfs_2 \<sigma> \<and> t<T_max \<and> t' < T_max \<and> cvd[C,l] \<sigma>") prefer 2 using book_keeping_def apply blast
  using showing_block_cond_pres_global by blast








end