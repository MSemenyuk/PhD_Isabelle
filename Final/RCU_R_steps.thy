theory RCU_R_steps
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





lemma R5_breakdown_wrt_R4_Rcap_1:
 "main_inv ms ps \<Longrightarrow>               
  con_assms ms ps \<Longrightarrow>
  t<T_max \<Longrightarrow>
  ta<T_max \<Longrightarrow>
  ta \<noteq> t \<Longrightarrow>
  pc ms t = R5 \<Longrightarrow>
  pc ms ta \<in> { R2, R3, R4 , R5 , S1, S2, S3, S4, S5, S6, S7, I13, I14} \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  Rcap ms ta (detaddrs ms ta) \<Longrightarrow>
  det_differ_from_det ms \<Longrightarrow>
Rcap ms' ta (detaddrs ms' ta)" 
  apply(case_tac "pc ms ta = R2")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Rcap_def)
  apply(case_tac "pc ms ta = R3")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Rcap_def)
  apply(case_tac "pc ms ta = R4")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Rcap_def)
  apply(case_tac "pc ms ta = R5")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Rcap_def)
  apply(case_tac "pc ms ta = S1")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Rcap_def)
  apply(case_tac "pc ms ta = S2")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Rcap_def)
  apply(case_tac "pc ms ta = S3")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Rcap_def)
  apply(case_tac "pc ms ta = S4")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Rcap_def)
  apply(case_tac "pc ms ta = S5")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Rcap_def)
  apply(case_tac "pc ms ta = S6")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Rcap_def)
  apply(case_tac "pc ms ta = S7")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Rcap_def)
  apply(case_tac "pc ms ta = I13")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Rcap_def)
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  by(simp add:Rcap_def)





lemma R5_breakdown_wrt_R4_Rcap_2:
 "main_inv ms ps \<Longrightarrow>               
  con_assms ms ps \<Longrightarrow>
  t<T_max \<Longrightarrow>
  ta<T_max \<Longrightarrow>
  ta \<noteq> t \<Longrightarrow>
  pc ms t = R5 \<Longrightarrow>
  pc ms ta \<in> { R2, R3, R4 , R5 , S1, S2, S3, S4, S5, S6, S7, I13, I14} \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  preCond ms ps (pc ms ta) ta \<Longrightarrow> 
  det_differ_from_det ms \<Longrightarrow>
Rcap ms' ta (detaddrs ms' ta)" 
  apply(subgoal_tac "Rcap ms ta (detaddrs ms ta)") prefer 2 apply(simp add:preCond_def) apply auto[1] 
  using R5_breakdown_wrt_R4_Rcap_1 
  by simp

lemma R5_breakdown_wrt_R4_Wcap_1:
 "main_inv ms ps \<Longrightarrow>               
  con_assms ms ps \<Longrightarrow>
  t<T_max \<Longrightarrow>
  ta<T_max \<Longrightarrow>
  ta \<noteq> t \<Longrightarrow>
  pc ms t = R5 \<Longrightarrow>
  pc ms ta \<in> { R2, R3, R4 , R5 , S1, S2, S3, S4, S5, S6, S7, I13, I14} \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  Wcap ms ta (detaddrs ms ta) \<Longrightarrow>
  det_differ_from_det ms \<Longrightarrow>
Wcap ms' ta (detaddrs ms' ta)" 
  apply(case_tac "pc ms ta = R2")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Wcap_def) 
  apply metis
  apply(case_tac "pc ms ta = R3")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Wcap_def) 
  apply metis
  apply(case_tac "pc ms ta = R4")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Wcap_def) 
  apply metis
  apply(case_tac "pc ms ta = R5")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Wcap_def) 
  apply metis
  apply(case_tac "pc ms ta = S1")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Wcap_def) 
  apply metis
  apply(case_tac "pc ms ta = S2")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Wcap_def) 
  apply metis
  apply(case_tac "pc ms ta = S3")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Wcap_def) 
  apply metis
  apply(case_tac "pc ms ta = S4")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Wcap_def) 
  apply metis
  apply(case_tac "pc ms ta = S5")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Wcap_def) 
  apply metis
  apply(case_tac "pc ms ta = S6")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Wcap_def) 
  apply metis
  apply(case_tac "pc ms ta = S7")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Wcap_def) 
  apply metis
  apply(case_tac "pc ms ta = I13")
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Wcap_def) 
  apply metis
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "\<forall>i. i<length(det ms ta) \<longrightarrow> hd(det ms t)\<noteq>det ms ta!i") prefer 2
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_nat_zero_code list.size(3))
  apply(simp add:Wcap_def) 
  by metis


lemma R5_breakdown_wrt_R4_Wcap_2:
 "main_inv ms ps \<Longrightarrow>               
  con_assms ms ps \<Longrightarrow>
  t<T_max \<Longrightarrow>
  ta<T_max \<Longrightarrow>
  ta \<noteq> t \<Longrightarrow>
  pc ms t = R5 \<Longrightarrow>
  pc ms ta \<in> { R2, R3, R4 , R5 , S1, S2, S3, S4, S5, S6, S7, I13, I14} \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  preCond ms ps (pc ms ta) ta \<Longrightarrow> 
  det_differ_from_det ms \<Longrightarrow>
Wcap ms' ta (detaddrs ms' ta)" 
  apply(subgoal_tac "Wcap ms ta (detaddrs ms ta)") prefer 2 apply(simp add:preCond_def) apply auto[1] 
  using R5_breakdown_wrt_R4_Wcap_1 
  by simp


lemma R5_breakdown_wrt_R4_final:
 "main_inv ms ps \<Longrightarrow>               
  con_assms ms ps \<Longrightarrow>
  t<T_max \<Longrightarrow>
  ta<T_max \<Longrightarrow>
  ta \<noteq> t \<Longrightarrow>
  pc ms t = R5 \<Longrightarrow>
  pc ms ta \<in> { R2, R3, R4 , R5 , S1, S2, S3, S4, S5, S6, S7, I13, I14} \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  preCond ms ps (pc ms ta) ta \<Longrightarrow> 
  det_differ_from_det ms \<Longrightarrow>
  preCond ms' ps' (pc ms' ta) ta " 
  apply(case_tac "pc ms ta = R2")
  apply(subgoal_tac "Rcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Rcap_2 apply simp
  apply(subgoal_tac "Wcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Wcap_2 apply simp
  apply(simp add:preCond_def step_def abbr)
  apply(case_tac "pc ms ta = R3")
  apply(subgoal_tac "Rcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Rcap_2 apply simp
  apply(subgoal_tac "Wcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Wcap_2 apply simp
  apply(simp add:preCond_def step_def abbr)
  apply(case_tac "pc ms ta = R4")
  apply(subgoal_tac "Rcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Rcap_2 apply simp
  apply(subgoal_tac "Wcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Wcap_2 apply simp
  apply(simp add:preCond_def step_def abbr)
  apply(case_tac "pc ms ta = R5")
  apply(subgoal_tac "Rcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Rcap_2 apply simp
  apply(subgoal_tac "Wcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Wcap_2 apply simp
  apply(simp add:preCond_def step_def abbr)
  apply(case_tac "pc ms ta = S1")
  apply(subgoal_tac "Rcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Rcap_2 apply simp
  apply(subgoal_tac "Wcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Wcap_2 apply simp
  apply(simp add:preCond_def step_def abbr)
  apply(case_tac "pc ms ta = S2")
  apply(subgoal_tac "Rcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Rcap_2 apply simp
  apply(subgoal_tac "Wcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Wcap_2 apply simp
  apply(simp add:preCond_def step_def abbr)
  apply(case_tac "pc ms ta = S3")
  apply(subgoal_tac "Rcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Rcap_2 apply simp
  apply(subgoal_tac "Wcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Wcap_2 apply simp
  apply(simp add:preCond_def step_def abbr)
  apply(case_tac "pc ms ta = S4")
  apply(subgoal_tac "Rcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Rcap_2 apply simp
  apply(subgoal_tac "Wcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Wcap_2 apply simp
  apply(simp add:preCond_def step_def abbr)
  apply(case_tac "pc ms ta = S5")
  apply(subgoal_tac "Rcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Rcap_2 apply simp
  apply(subgoal_tac "Wcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Wcap_2 apply simp
  apply(simp add:preCond_def step_def abbr)
  apply(case_tac "pc ms ta = S6")
  apply(subgoal_tac "Rcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Rcap_2 apply simp
  apply(subgoal_tac "Wcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Wcap_2 apply simp
  apply(simp add:preCond_def step_def abbr)
  apply(case_tac "pc ms ta = S7")
  apply(subgoal_tac "Rcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Rcap_2 apply simp
  apply(subgoal_tac "Wcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Wcap_2 apply simp
  apply(simp add:preCond_def step_def abbr)
  apply(case_tac "pc ms ta = I13")
  apply(subgoal_tac "Rcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Rcap_2 apply simp
  apply(subgoal_tac "Wcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Wcap_2 apply simp
  apply(simp add:preCond_def step_def abbr)
  apply(subgoal_tac "Rcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Rcap_2 apply simp
  apply(subgoal_tac "Wcap ms' ta (detaddrs ms' ta)") prefer 2 
  using R5_breakdown_wrt_R4_Wcap_2 apply simp
  by(simp add:preCond_def step_def abbr)



(*
  apply(subgoal_tac "det_differ_from_det ms") prefer 2 using general_structure_def 
  apply blast
  apply(case_tac " pc ms ta \<in> {R4, R5} \<and> pc ms t = R5") using R5_breakdown_wrt_R4_final
  apply blast
  apply(thin_tac "det_differ_from_det ms ")
*)




lemma showing_global_preCond_for_R:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  ta<T_max \<Longrightarrow>
  ta \<noteq> t \<Longrightarrow>
  pc ms t \<in> R_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  preCond ms ps (pc ms ta) ta \<Longrightarrow>
  general_structure ms \<Longrightarrow>
  preCond ms' ps' (pc ms' ta) ta" 
  apply(cases "pc ms t") 
  apply(simp) apply(simp) apply(simp) apply(simp) apply(simp) 
  apply(simp) apply(simp) apply(simp) apply(simp) apply(simp) 
  apply(simp) apply(simp) apply(simp) apply(simp) apply(simp) 
  apply(simp) defer defer defer defer defer
  apply(simp) apply(simp) apply(simp) apply(simp) apply(simp) 
  apply(simp) apply(simp)         
  prefer 5 (*selects pc ms t = R5 *)
  apply(case_tac "pc ms ta \<in> { R2, R3, R4 , R5 , S1, S2, S3, S4, S5, S6, S7, I13, I14}")
  apply(subgoal_tac "det_differ_from_det ms") prefer 2 using general_structure_def 
  apply blast using R5_breakdown_wrt_R4_final
  apply blast
  apply(case_tac "pc ms ta")
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply(simp add:Rcap_def Wcap_def) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply simp apply simp apply simp 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply (simp add:step_def abbr preCond_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (metis hd_conv_nth length_greater_0_conv option.sel) 
  apply simp apply simp apply simp 
  apply simp apply simp apply simp 
  apply simp apply simp apply simp 
  apply simp apply simp 
  (*4*)
  apply(case_tac "pc ms ta")
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  (*3*)
  apply(case_tac "pc ms ta")
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]  
  (*2*) 
  apply (simp add:step_def abbr preCond_def)   
  apply(case_tac "nondet_val ms t", simp_all add:abbr)                      
  apply(case_tac "pc ms ta") apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) 
  apply metis
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply metis 
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]  
  apply(case_tac "pc ms ta") apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) 
  apply metis
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply metis 
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]  
  (*1*) 
  apply (simp add:step_def abbr preCond_def)   
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)                      
  apply(case_tac "pc ms ta") apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) 
  apply metis
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply metis 
  apply(simp add:Rcap_def Wcap_def) apply metis apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply(case_tac "pc ms ta") apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) 
  apply metis
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply metis 
  apply(simp add:Rcap_def Wcap_def) apply metis apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] 
  apply (simp add:step_def abbr preCond_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1] apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) apply auto[1]
  apply(subgoal_tac "\<forall>i. own\<^sub>R ms i = own\<^sub>R ms' i")
  apply (metis (no_types, lifting) Rcap_def) apply auto[1] 
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = own\<^sub>W ms' i")
  apply (metis (no_types, lifting) Wcap_def) by auto[1]












(*******************done*********************)





lemma showing_main_inv_1_for_R:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> R_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  main_inv_1 ms'"
  apply (simp, safe; clarsimp)
  apply(simp_all add:main_inv_1_def step_def setup_r_def)
  apply(simp_all add:abbr)
  apply(simp add:preCond_def)
  apply (metis main_inv_1_def main_inv_def option.discI)
  apply(simp add:preCond_def)
  apply auto[1]
  apply (metis main_inv_1_def main_inv_def option.discI option.sel singleton_iff)
  apply (metis main_inv_1_def main_inv_def option.discI option.sel singleton_iff)
  apply(case_tac "nondet_val ms t", simp_all add:abbr) 
  apply (metis main_inv_1_def main_inv_def option.discI)
  apply (metis main_inv_1_def main_inv_def option.simps(3))
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply (metis main_inv_1_def main_inv_def option.discI)
  apply (metis main_inv_1_def main_inv_def option.discI)
  apply(simp add:preCond_def)
  apply auto[1]
  apply (metis emptyE hd_conv_nth insertE length_greater_0_conv)
  apply (metis main_inv_1_def main_inv_def option.discI option.sel singleton_iff)
  apply (metis main_inv_1_def main_inv_def option.discI option.sel singleton_iff)
  by (meson main_inv_3_def main_inv_def own\<^sub>W_n_by_t_imp_def)



lemma showing_main_inv_2_for_R:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> R_steps \<Longrightarrow>
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
  apply(clarify)
  apply(case_tac "b", simp_all add:abbr)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply(simp add:preCond_def)
  apply auto[1]
  by (metis hd_conv_nth length_greater_0_conv singleton_iff)




lemma showing_main_inv_3_for_R:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> R_steps \<Longrightarrow>
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
  apply clarify
  apply(case_tac "b", simp_all)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  by(case_tac "det ms t \<noteq> []", simp_all add:abbr)





lemma showing_main_inv_for_R:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> R_steps \<Longrightarrow>
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
  using showing_main_inv_1_for_R apply blast
  using showing_main_inv_2_for_R apply blast
  using showing_main_inv_3_for_R by blast








lemma showing_psem_rules_for_R:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> R_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  psem_rules ps'" 
  apply(case_tac "pc ms t = R5") apply(simp add:step_def add:abbr) apply clarify
  apply(subgoal_tac "kill ps i ps'") prefer 2 
  using kill_def apply blast apply(subgoal_tac "psem_rules ps'") prefer 2 
  apply (meson Unique_allocs_def constant_alloc_ass_def newran_def psem_rules_def psem_rules_preserved_kill)
  apply (metis Unique_allocs_def constant_alloc_ass_def newran_def psem_rules_def)
  apply(simp, safe; simp_all)
  apply(simp_all add: step_def abbr preCond_def)
  apply (metis domI fst_conv option.sel)
  apply blast apply(clarify) apply(case_tac "b", simp_all add:abbr)
  apply (metis (no_types, lifting) domI fst_conv option.sel)
  apply (metis (no_types, lifting) domI fst_conv option.sel)
  apply blast+ 
  apply(case_tac "nondet_val ms t", simp add:abbr) 
  apply (metis (no_types, lifting) domI fst_conv option.sel)
  apply (metis (no_types, lifting) domI fst_conv option.sel)
  apply(case_tac "nondet_val ms t", simp add:abbr) 
  apply (metis (no_types, lifting))
  apply (metis (no_types, lifting))
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr) 
  apply (metis (no_types, lifting) domI fst_conv option.sel)
  apply (metis (no_types, lifting) domI fst_conv option.sel)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr) 
  by (metis (no_types, lifting)) 
  







lemma showing_allocated_addresses_for_R:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> R_steps \<Longrightarrow>
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
  apply(simp add:allocated_addresses_lemmas step_def abbr preCond_def)
  apply auto[1]
  apply (metis Rcap_def insertI1 less_Suc_eq less_nat_zero_code list.size(3) nth_append nth_append_length)
  apply(simp add:allocated_addresses_lemmas step_def abbr preCond_def)
  apply clarify
  apply(case_tac "b", simp_all add:abbr)
  apply(simp_all add:allocated_addresses_lemmas step_def abbr preCond_def)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply (intro conjI impI)
  apply auto[1]
  apply (metis hd_conv_nth length_greater_0_conv singleton_iff)
  apply blast
  apply auto[1] 
  apply (metis doubleton_eq_iff hd_conv_nth length_greater_0_conv main_inv_1_def main_inv_def option.discI testttt2)
  apply auto[1]
  apply (metis (no_types, opaque_lifting) Nitpick.size_list_simp(2) One_nat_def length_tl lessI less_trans_Suc nth_tl)
  apply (simp add: det_differ_inside_def general_structure_def hd_conv_nth nth_tl)
  by (metis (no_types, lifting) general_structure_def hd_conv_nth length_greater_0_conv option.inject own\<^sub>W_and_det_things_def)
      
     








lemma showing_observation_inv_ms_for_R:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> R_steps \<Longrightarrow>
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
  apply auto[1]
  apply (metis less_Suc_eq nth_append nth_append_length option.sel)
  apply (metis less_Suc_eq nth_append nth_append_length option.sel)
  apply(simp add:observation_inv_ms_def step_def abbr)
  apply auto[1]
  apply (metis)
  apply (metis)
  apply(simp add:observation_inv_ms_def step_def abbr)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(simp add:observation_inv_ms_def step_def abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply(simp add:observation_inv_ms_def step_def abbr)
  apply auto[1]
  apply (smt (verit) One_nat_def Suc_less_eq Suc_pred hd_conv_nth length_tl less_nat_zero_code list.size(3) not_less_iff_gr_or_eq nth_tl)
  by (smt (verit, ccfv_threshold) One_nat_def Suc_less_eq Suc_pred hd_conv_nth length_tl less_nat_zero_code list.size(3) not_less_iff_gr_or_eq nth_tl)





lemma showing_observation_inv_sig_for_R:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> R_steps \<Longrightarrow>
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
  apply clarify apply(case_tac "b", simp_all add:abbr) apply auto[1] apply auto[1]
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(simp add:observation_inv_sig_def step_def abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply(simp add:observation_inv_sig_def step_def abbr) apply auto[1]
  apply(simp add:preCond_def Wcap_def)
  apply (metis hd_conv_nth length_greater_0_conv)
  apply(simp add:preCond_def Wcap_def)
  by blast
    




lemma showing_own\<^sub>W_n_by_t_imp_for_R:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> R_steps \<Longrightarrow>
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
  apply clarify
  apply(case_tac "b", simp_all add:abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply(simp add:observation_inv_sig_def step_def abbr own\<^sub>W_n_by_t_imp_def preCond_def)
  by (metis (no_types, lifting) general_structure_def hd_conv_nth length_greater_0_conv option.sel own\<^sub>W_and_det_things_def)






lemma showing_general_structure_for_R:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  pc ms t \<in> R_steps \<Longrightarrow>
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
  (*5*)
  apply(intro conjI)
  apply(simp add:n_differ_def)  apply auto[1]
  apply(simp add:n_differ_from_s_outside_def)  apply auto[1]
  apply(simp add:n_differ_from_s_inside_def)  
  apply(simp add:s_differ_from_det_inside_def) 
  apply(simp add:n_differ_from_det_def) apply auto[1]  apply(simp add:preCond_def) 
  apply (metis (no_types, lifting) Rcap_def insertI1 less_Suc_eq less_nat_zero_code list.size(3) n_differ_from_s_outside_def nth_append nth_append_length) 
  apply(simp add:det_differ_from_det_def) 
  apply blast apply(simp add:det_differ_from_det_def) apply(simp add:preCond_def) apply auto[1] 
  apply (smt (verit) Wcap_def diff_is_0_eq' diff_zero insertI1 less_Suc_eq less_Suc_eq_le list.size(3) nth_append nth_append_length option.inject own\<^sub>W_and_det_things_def)
  apply (smt (verit) Wcap_def insertI1 less_Suc_eq less_nat_zero_code list.size(3) nth_append nth_append_length option.inject own\<^sub>W_and_det_things_def)
  apply(simp add:det_differ_inside_def)  apply auto[1] apply(simp add:preCond_def)
  apply(simp add:s_differ_from_det_inside_def)
  apply (smt (verit) Rcap_def insertI1 less_Suc_eq less_nat_zero_code list.size(3) nth_append nth_append_length option.sel)
  apply(simp add:own\<^sub>W_and_det_things_def) apply(simp add:preCond_def Wcap_def)
  apply (metis less_SucE nth_append nth_append_length)
  (*4*)
  apply clarify apply(case_tac "b", simp_all add:abbr)
  apply(intro conjI)
  apply(simp add:n_differ_def) 
  apply(simp add:n_differ_from_s_outside_def) 
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) 
  apply(simp add:n_differ_from_det_def)  
  apply(simp add:det_differ_from_det_def) 
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(intro conjI)
  apply(simp add:n_differ_def) 
  apply(simp add:n_differ_from_s_outside_def) 
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) 
  apply(simp add:n_differ_from_det_def)  
  apply(simp add:det_differ_from_det_def) 
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def) 
  (*3*)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(intro conjI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def)  
  apply(simp add:det_differ_from_det_def) 
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(intro conjI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def)  
  apply(simp add:det_differ_from_det_def) 
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def) 
  (*2*)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply(intro conjI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def)  
  apply(simp add:det_differ_from_det_def) 
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(intro conjI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def)  
  apply(simp add:det_differ_from_det_def) 
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def) 
  apply(intro conjI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1] 
  apply (metis (no_types, lifting) One_nat_def Suc_less_eq Suc_pred diff_0_eq_0 length_greater_0_conv length_tl list.size(3) nth_tl)
  apply(simp add:n_differ_from_det_def)  apply auto[1] 
  apply (metis Nitpick.size_list_simp(2) One_nat_def Suc_less_eq length_tl list.sel(2) nth_tl) 
  apply blast
  apply(simp add:det_differ_from_det_def) apply auto[1] 
  apply (metis Nitpick.size_list_simp(2) One_nat_def Suc_less_eq length_tl list.sel(2) nth_tl) 
  apply (metis Nitpick.size_list_simp(2) One_nat_def Suc_less_eq length_tl list.sel(2) nth_tl)
  apply(simp add:det_differ_inside_def) apply auto[1] 
  apply (metis (no_types, lifting) Nitpick.size_list_simp(2) One_nat_def Suc_less_eq length_tl list.sel(2) nat.inject nth_tl)
  apply(simp add:own\<^sub>W_and_det_things_def) apply auto[1]
  apply(simp add:preCond_def Wcap_def) 
  apply (simp add: det_differ_inside_def hd_conv_nth nth_tl)
  apply(simp add:preCond_def Wcap_def) 
  apply (simp add: nth_tl)
  apply(simp add:preCond_def Wcap_def) 
  by (metis (no_types, opaque_lifting) hd_conv_nth length_greater_0_conv option.sel)
  
  
  

lemma showing_local_preCond_for_R:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  T_limitation ms \<Longrightarrow>
  pc ms t \<in> R_steps \<Longrightarrow>
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
  apply (metis less_Suc_eq nth_append nth_append_length)
  apply (metis less_Suc_eq nth_append nth_append_length)
  apply (metis less_Suc_eq nth_append nth_append_length)
  apply (metis less_Suc_eq nth_append nth_append_length)
  apply clarify
  apply(case_tac "b", simp_all add:abbr) apply(intro conjI impI)
  apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) 
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(intro conjI impI)
  apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) 
  apply metis
  apply(intro conjI impI)
  apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) 
  apply metis
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply(intro conjI impI)
  apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) 
  apply metis
  apply(intro conjI impI)
  apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) 
  apply(intro conjI impI)
  apply(simp add:Rcap_def Wcap_def) apply auto[1]
  apply (simp add: det_differ_inside_def general_structure_def hd_conv_nth nth_tl)
  apply (metis Nitpick.size_list_simp(2) One_nat_def Suc_less_eq length_tl nth_tl)
  apply(subgoal_tac "\<forall>j. j<length(det ms t) \<longrightarrow> own\<^sub>R ms (det ms t!j) = {t}") prefer 2
  apply blast
  apply(subgoal_tac "length(det ms t) -1 = length(tl(det ms t))") prefer 2
  apply (metis length_tl)
  apply(subgoal_tac "\<exists>j<length (tl(det ms t)) . tl (det ms t) ! j = i")
  using One_nat_def apply presburger
  apply (smt (z3) Suc_less_eq Suc_pred' hd_conv_nth nat_neq_iff not_less_eq nth_tl zero_less_Suc)
  apply(simp add:Rcap_def Wcap_def) apply auto[1]
  apply (simp add: det_differ_inside_def general_structure_def hd_conv_nth nth_tl)
  apply (metis Nitpick.size_list_simp(2) One_nat_def Suc_less_eq length_tl nth_tl)
  apply(subgoal_tac "\<forall>j. j<length(det ms t) \<longrightarrow> own\<^sub>R ms (det ms t!j) = {t}") prefer 2
  apply blast
  apply(subgoal_tac "length(det ms t) -1 = length(tl(det ms t))") prefer 2
  apply (metis length_tl)
  apply(subgoal_tac "\<exists>j<length (tl(det ms t)) . tl (det ms t) ! j = i")
  using One_nat_def apply presburger
  apply (smt (z3) Suc_less_eq Suc_pred' hd_conv_nth nat_neq_iff not_less_eq nth_tl zero_less_Suc)
  apply(simp add:Rcap_def Wcap_def) apply auto[1]
  apply (simp add: det_differ_inside_def general_structure_def hd_conv_nth nth_tl)
  apply (metis Nitpick.size_list_simp(2) One_nat_def Suc_less_eq length_tl nth_tl)
  apply(subgoal_tac "\<forall>j. j<length(det ms t) \<longrightarrow> own\<^sub>R ms (det ms t!j) = {t}") prefer 2
  apply blast 
  apply (simp add: det_differ_inside_def general_structure_def hd_conv_nth nth_tl)
  apply(subgoal_tac "length(det ms t) -1 = length(tl(det ms t))") prefer 2
  apply (metis length_tl) 
  apply (metis Nitpick.size_list_simp(2) One_nat_def Suc_less_eq nth_tl singleton_iff) 
  by (metis Nitpick.size_list_simp(2) One_nat_def Suc_less_eq length_tl nth_tl)
  





lemma WM_read_and_dobs_other_pres:
  "wfs \<sigma> \<Longrightarrow> [y =\<^sub>t z] \<sigma> \<Longrightarrow> x\<noteq>y \<Longrightarrow> \<sigma> [wu \<leftarrow> w]\<^sub>t \<sigma>' \<Longrightarrow> [y =\<^sub>t z] \<sigma>'"
  using d_obs_RdX_pres
  by (metis d_obs_RdX_other)



lemma showing_det_pres_local_for_R:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  t' < T_max \<Longrightarrow>
  t'\<noteq> t \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  pc ms t \<in> R_steps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  \<forall>t'. t'<T_max \<and> t\<noteq>t' \<longrightarrow> block_cond t t' ms \<sigma>  \<Longrightarrow>
  det_block t ms \<sigma>  \<Longrightarrow>
  det_block t ms' \<sigma>'" 
  apply(simp add:det_block_def block_cond_def)
  apply(simp add:step_def)
  apply clarsimp
  apply(case_tac "pc ms t", simp_all add:abbr)  apply(simp add:preCond_def) 
  apply(simp add:post_block_def Rcap_def Wcap_def con_assms_def)
  apply (metis less_Suc_eq nth_append nth_append_length)
  apply clarify
  apply(case_tac "b", simp_all add:abbr)
  apply blast
  apply blast
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply blast
  apply blast
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply blast
  apply(simp add:preCond_def Wcap_def Rcap_def) 
  by (metis DiffD1 Nitpick.size_list_simp(2) One_nat_def Suc_less_eq length_tl nth_tl)
  


end