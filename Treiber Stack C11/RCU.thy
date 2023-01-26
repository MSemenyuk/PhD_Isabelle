theory RCU
imports RCU_model
begin 


lemmas genericwfs_lemma [simp] = wfs_2_def


lemma initial_wfs_2: assumes "initial_state \<sigma> I"  shows "wfs_2 \<sigma>"
  apply(simp)
  apply(rule conjI)
  using assms initial_wfs apply blast
  using assms apply (simp add: initial_state_def)
  by blast

lemma wfs_2_preserved:
  assumes "wfs_2 \<sigma>"
      and "OpSem.step t a \<sigma> \<sigma>'"
    shows "wfs_2 \<sigma>'"
  using assms apply(unfold wfs_2_def)
  apply (intro conjI)
  using wfs_preserved assms apply blast
  apply (rule step_cases[OF assms(2)]) apply simp_all
  using assms(1) wfs_2_def wfs_def apply auto[1]
  apply (simp add: read_trans_def lastWr_def covered_v_def Let_def rev_app_def OpSem.step_def update_thrView_def split:if_splits)
  using assms(1)  apply auto[1]
     apply (unfold writes_on_def wfs_2_def wfs_def)
  apply (simp add: var_def update_mods_def update_modView_def  )
  apply (simp add: write_trans_def valid_fresh_ts_def lastWr_def covered_v_def Let_def rev_app_def step_def update_thrView_def split:if_splits)
  apply (simp add: visible_writes_def update_mods_def update_modView_def )
  
   apply safe
  apply (simp add: fst_def tst_def snd_def)
  apply(case_tac "thrView \<sigma> t x", simp_all add:update_trans_def Let_def rev_app_def) 
  apply(case_tac "releasing \<sigma> (aaa, ba)", simp_all)
  apply (metis assms(1) case_prod_conv less_irrefl subset_iff wfs_2_def wfs_def)
  by (metis assms(1) case_prod_conv less_irrefl subset_iff wfs_2_def wfs_def)


lemma lastNotCovered:
"wfs \<sigma> \<Longrightarrow> lastWr \<sigma> x \<notin> covered \<sigma>  
 \<Longrightarrow> (\<exists> b. (x, b) \<notin> covered \<sigma> \<and> lastWr \<sigma> x \<in> writes_on \<sigma> x) "
  apply (simp add: lastWr_def)
  apply (unfold writes_on_def)
  by (metis lastWr_def last_write_write_on writes_on_def)


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
local - preCond ms ps \<sigma> (pc ms t) t     *done*          --- defines preconditions for t to proceed with stepping      
global - preCond ms ps \<sigma> (pc ms ta) ta  *done*          --- defines preconditions for t to proceed with stepping      

local  - weak_mem (pre/in/post block) (t ta)
global - weak_mem (pre/in/post block) (ta t)
*)



(*the following describes originally reserved addresses*)
definition "default_locs \<equiv> {i | i a. i=C \<or> i = rcu_0+a \<and> a<T_max }"

definition "reserved_bydef ps \<equiv> \<forall>i. i\<in>default_locs \<longrightarrow> \<not>isfree_addr i ps"

definition "reservations_differ \<equiv> \<forall>i. i<T_max \<longrightarrow> C\<noteq>rcu_0+i"

definition "counters_limit ms \<equiv> \<forall>t. t<T_max \<longrightarrow> CTRsync\<^sub>1 ms t \<le>T_max \<and> CTRsync\<^sub>2 ms t \<le>T_max"

definition "con_assms ms ps \<equiv> reserved_bydef ps \<and> reservations_differ \<and> counters_limit ms "
                                    
lemmas con_assms_lemmas [simp] = reserved_bydef_def reservations_differ_def
                                 default_locs_def counters_limit_def








(*----------------supporting lemmas--------------------*)
lemma blind_isabelle_hdlist [simp]:
  "det ms t\<noteq>[] \<Longrightarrow> hd(det ms t) = det ms t!0"
  by (simp add: hd_conv_nth)

lemma aap_supplem_1:
  "i<length(det ms t) \<Longrightarrow> det ms t\<noteq>[] \<Longrightarrow>((det ms t @ [ya]) ! i) = (det ms t)!i"
  by (simp add: nth_append)

lemma supportingrandomwhat1:
  "ms' = ms\<lparr>v := v ms(t \<mapsto> z), pc := (pc ms)(t := I10)\<rparr> \<Longrightarrow> 
s ms t = s ms' t \<and> n ms t = n ms' t \<and> n_dec ms t = n_dec ms' t \<and> det ms t = det ms' t \<and> (\<forall>loc. (own\<^sub>W ms loc = own\<^sub>W ms' loc \<and> own\<^sub>R ms loc = own\<^sub>R ms' loc))"
  by simp

lemma suppotingrandom1:
  "ms' = ms \<lparr>det := (det ms)(t := det ms t @ [ya]), pc := (pc ms)(t := R2),
          s_dec := (s_dec ms)(t := False), s := (s ms)(t := None)\<rparr> 
\<Longrightarrow> \<forall> loc. loc\<in>detaddrs ms t \<longrightarrow> loc\<in>detaddrs ms' t"
  apply(clarsimp)
  by (metis butlast_snoc less_SucI nth_butlast)


lemma suppotingrandom2:
  "ms' = ms \<lparr>det := (det ms)(t := tl (det ms t)),
          own\<^sub>R := (own\<^sub>R ms)(hd (det ms t) := own\<^sub>R ms (hd (det ms t)) - {t}),
          own\<^sub>W := (own\<^sub>W ms)(hd (det ms t) := None), pc := (pc ms)(t := R4)\<rparr>
\<Longrightarrow> det ms' t = tl(det ms t)"
  by(clarsimp) 

lemma suppotingrandom3:
  "ms' = ms \<lparr>det := (det ms)(t := tl (det ms t)),
          own\<^sub>R := (own\<^sub>R ms)(hd (det ms t) := own\<^sub>R ms (hd (det ms t)) - {t}),
          own\<^sub>W := (own\<^sub>W ms)(hd (det ms t) := None), pc := (pc ms)(t := R4)\<rparr>
\<Longrightarrow> det ms t \<noteq>[]
\<Longrightarrow> loc \<in> detaddrs ms' t\<Longrightarrow> loc\<in>detaddrs ms t"
  apply(clarsimp)  
  by (metis Nitpick.size_list_simp(2) Suc_less_eq Suc_pred length_greater_0_conv nth_tl)
  

lemma suppotingrandom4:
  "ms' = ms \<lparr>det := (det ms)(t := tl (det ms t)),
          own\<^sub>R := (own\<^sub>R ms)(hd (det ms t) := own\<^sub>R ms (hd (det ms t)) - {t}),
          own\<^sub>W := (own\<^sub>W ms)(hd (det ms t) := None), pc := (pc ms)(t := R4)\<rparr>
\<Longrightarrow> det ms t \<noteq>[]
\<Longrightarrow> loc\<in>detaddrs ms t \<Longrightarrow> loc\<in> detaddrs ms' t \<or> loc = hd(det ms t)"
  apply(clarsimp) 
  by (metis Nitpick.size_list_simp(2) Suc_less_eq Suc_pred less_Suc_eq_0_disj nth_tl)
  

lemma supp1:
  "cvd[C,vala] \<sigma> \<Longrightarrow>
  \<sigma> [z \<leftarrow> ya]\<^sub>t \<sigma>' \<Longrightarrow>
  cvd[C,vala] \<sigma>'"
  apply(simp add:covered_v_def lastWr_def OpSem.step_def RdX_def visible_writes_def) unfolding writes_on_def
  read_trans_def
  by (smt (z3) Collect_cong rev_app_def surrey_state.ext_inject surrey_state.surjective surrey_state.update_convs(2) update_thrView_def value_def)

lemma supp2:
  "cvd[C,vala] \<sigma> \<Longrightarrow>
wfs \<sigma> \<Longrightarrow>
  \<sigma> [z := ya]\<^sub>t \<sigma>' \<Longrightarrow>
  z\<noteq>C \<Longrightarrow>
  cvd[C,vala] \<sigma>'"
  by (metis cvd_WrX_other_var_pres)






(*******************************************************************)






(*----------------Main Invariant Shown--------------------*)

lemma main_invariant_1_preservation:
 "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  main_inv_1 ms'"
  apply simp 
  apply(simp add: step_def preCond_def)
  apply(case_tac "pc ms t", simp_all)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:new_int_def)
  apply clarify
  apply(subgoal_tac "n ms t = None") prefer 2
  apply fastforce apply(simp add:main_inv_lemmas) 
  apply clarify 
  apply(case_tac "ta = t", simp_all) 
  apply(case_tac "y = loc", simp_all)
  apply (metis insert_not_empty option.sel)
  apply (metis option.sel)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(case_tac "repeat ms t", simp add:general_structure_lemmas)
  apply (metis Diff_empty Diff_insert0 option.sel)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
(*FAAZ*) defer
  apply(simp add:abbr main_inv_lemmas  Rcap_def) apply clarify 
  apply(simp add:general_structure_def)
  apply (metis option.sel)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
(*CAS*) defer
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply (metis singleton_iff)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply(case_tac "CAS_succ ms t", simp_all)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply(simp add:abbr main_inv_lemmas  Rcap_def) apply auto[1]
  apply(case_tac "nondet_val ms t ", simp_all)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply(case_tac "det ms t \<noteq> []", simp_all)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply (metis Diff_empty Diff_insert0 singleton_inject)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
(*r[i] = rcu[counter]*) defer
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(simp add:abbr main_inv_lemmas  Rcap_def) 
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
(*load(rcu[i])*) defer
  apply(case_tac "reg ms t = Suc 0", simp_all)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
  apply(simp add:abbr main_inv_lemmas  Rcap_def)
(*dealing with FAAZ*)
  apply(simp add:FAAZ_def get_C_val_def)
  apply(case_tac "\<not>repeat ms t", simp_all)
  apply clarify
  apply(case_tac "ta = t")
  apply(simp add:general_structure_def own\<^sub>W_n_by_t_imp_def observation_inv_sig_def)
  apply (metis option.sel set_eq_subset)
  apply(simp add:general_structure_def own\<^sub>W_n_by_t_imp_def observation_inv_sig_def)
  apply clarify apply(intro conjI impI) prefer 2
  apply (metis option.sel)
  apply(subgoal_tac "ta < T_max \<and> own\<^sub>W ms (the(n ms ta)) = Some ta") prefer 2
  apply (metis option.sel)
  apply(subgoal_tac "l \<noteq> (the(n ms ta))") prefer 2
  apply blast
  apply(subgoal_tac "l = value \<sigma> (a,b)")
  apply blast 
  prefer 2
  apply clarify
  apply(case_tac "ta = t")
  apply(simp add:general_structure_def own\<^sub>W_n_by_t_imp_def observation_inv_sig_def)
  apply (metis option.sel set_eq_subset)
  apply(simp add:general_structure_def own\<^sub>W_n_by_t_imp_def observation_inv_sig_def)
  apply clarify apply(intro conjI impI) prefer 2
  apply (metis option.sel)
  apply(subgoal_tac "ta < T_max \<and> own\<^sub>W ms (the(n ms ta)) = Some ta") prefer 2
  apply (metis option.sel)
  apply(subgoal_tac "l \<noteq> (the(n ms ta))") prefer 2 
  apply blast
  apply(subgoal_tac "l = value \<sigma> (a,b)")
  apply blast 
  unfolding covered_v_def lastWr_def writes_on_def
  apply (metis (mono_tags, lifting) mem_Collect_eq subsetD visible_var visible_writes_in_writes )
  apply (metis (mono_tags, lifting) mem_Collect_eq subsetD visible_var visible_writes_in_writes )
(*resolving CAS*)
  apply(simp add:cas_step_rcu_def) apply clarify
  apply(case_tac "ya", simp_all)
  apply(simp add:main_inv_lemmas)
  apply(simp add:main_inv_lemmas)
(*resolving load_rcu_to_r*)
  apply(simp add:load_rcu_to_r_def)
  apply(simp add:main_inv_lemmas)
  apply clarify
  apply(simp add:general_structure_def own\<^sub>W_n_by_t_imp_def observation_inv_sig_def)
  apply (metis option.sel)
(*resolving load(counter)*)
  apply(simp add:rcu_temp_copy_def)
  apply(simp add:main_inv_lemmas)
  apply clarify
  apply(simp add:general_structure_def own\<^sub>W_n_by_t_imp_def observation_inv_sig_def)
  by (metis option.sel)


lemma main_invariant_2_preservation:
  "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
    main_inv_2 ms' ps'"
  apply simp 
  apply(simp add: step_def preCond_def)
  apply(case_tac "pc ms t", simp_all)
  apply(simp add:abbr main_inv_lemmas) 
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:new_int_def)
  apply clarify
  apply(subgoal_tac "n ms t = None") prefer 2
  apply fastforce apply(simp add:main_inv_lemmas) 
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(case_tac "repeat ms t", simp_all)
  apply(simp add:abbr main_inv_lemmas)
(*FAAZ*) defer
  apply(simp add:abbr main_inv_lemmas)
  apply force
  apply(simp add:abbr main_inv_lemmas)
(*CAS*) defer
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(case_tac "CAS_succ ms t ", simp_all)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply clarify
  apply(simp add:abbr main_inv_lemmas)
  apply(case_tac "nondet_val ms t", simp_all)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(case_tac "det ms t = []")
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply clarify
  apply(case_tac "loc = det ms t ! 0", simp_all)
  apply blast
  apply(simp add:abbr main_inv_lemmas)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
(*r[i] = rcu[counter]*) defer
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
(*load(rcu[i])*) defer
  apply(case_tac "reg ms t = Suc 0", simp_all)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
(*dealing with FAAZ*)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:FAAZ_def get_C_val_def)
  apply(case_tac "\<not>repeat ms t", simp_all)
  apply clarify
  apply(simp add:observation_inv_sig_def observation_inv_ms_def)
  apply (metis Up_reads_cvd_v relating_step_to_update_trans_1)
  apply clarify
  apply(simp add:observation_inv_sig_def observation_inv_ms_def general_structure_def)
  apply (metis Up_reads_cvd_v relating_step_to_update_trans_1)
(*dealing with CAS*)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:cas_step_rcu_def)
  apply clarify
  apply(case_tac "ya", simp_all)
(*dealing with load_rcu_to_r*)
  apply(simp add:load_rcu_to_r_def main_inv_lemmas)
  apply clarify
  apply(simp add:observation_inv_sig_def observation_inv_ms_def)
(*dealing with rcu_temp_copy*)
  apply(simp add:rcu_temp_copy_def main_inv_lemmas)
  apply clarify
  by(simp add:observation_inv_sig_def observation_inv_ms_def)



lemma main_invariant_3_preservation:
  "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
    main_inv_3 ms' ps'"
  apply simp 
  apply(simp add: step_def preCond_def)
  apply(case_tac "pc ms t", simp_all)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:new_int_def)
  apply clarify  apply(simp add:main_inv_lemmas) 
  apply (metis insert_iff option.inject)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(case_tac "repeat ms t", simp_all) 
  apply clarify
  apply(case_tac "ta = t", simp_all)
  apply(subgoal_tac "the(n ms t) \<noteq> the(s ms t)") prefer 2
  apply (metis general_structure_def n_differ_from_s_inside_def option.sel)
  apply(subgoal_tac "\<forall>i. i<length (det ms t) \<longrightarrow> det ms t ! i \<noteq> the(s ms t)")
  apply (smt (verit) insert_iff mem_Collect_eq names_2(2) option.sel)
  apply (metis (no_types, lifting) general_structure_def less_zeroE list.size(3) s_differ_from_det_inside_def)
  apply(simp add:abbr main_inv_lemmas)
(*FAAZ*) defer
  apply(simp add:abbr main_inv_lemmas)
  apply force
  apply(simp add:abbr main_inv_lemmas)
(*CAS*) defer
  apply(simp add:abbr main_inv_lemmas) 
  apply (metis option.sel own\<^sub>W_n_by_t_imp_def)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(case_tac "CAS_succ ms t ", simp_all)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply clarify
  apply(simp add:abbr main_inv_lemmas)
  apply(case_tac "nondet_val ms t", simp_all)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(case_tac "det ms t = []")
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
(*r[i] = rcu[counter]*) defer
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
(*load(rcu[i])*) defer
  apply(case_tac "reg ms t = Suc 0", simp_all)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:abbr main_inv_lemmas)
(*dealing with FAAZ*)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:FAAZ_def get_C_val_def)
  apply(case_tac "\<not>repeat ms t", simp_all)
  apply clarify
  apply(simp add:observation_inv_sig_def observation_inv_ms_def) 
  apply (metis insertCI)
  apply clarify
  apply(simp add:observation_inv_sig_def observation_inv_ms_def general_structure_def) 
  apply (metis insertI2)
(*dealing with CAS*)
  apply(simp add:abbr main_inv_lemmas)
  apply(simp add:cas_step_rcu_def)
  apply clarify
  apply(case_tac "ya", simp_all) 
  apply (metis (no_types, lifting) Rcap_def fun_upd_apply insertCI option.discI option.inject)
(*dealing with load_rcu_to_r*)
  apply(simp add:load_rcu_to_r_def main_inv_lemmas)
  apply clarify
  apply(simp add:observation_inv_sig_def observation_inv_ms_def)
(*dealing with rcu_temp_copy*)
  apply(simp add:rcu_temp_copy_def main_inv_lemmas)
  apply clarify
  by(simp add:observation_inv_sig_def observation_inv_ms_def)




lemma main_invariant_preservation:
  "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow> \<comment> \<open>new\<close> 
  t<T_max \<Longrightarrow>
  general_structure ms \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow> \<comment> \<open>new\<close> 
  cvd[C,vala] \<sigma> \<Longrightarrow>  
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms  \<Longrightarrow> 
main_inv ms' ps'"
  unfolding main_inv_def
  apply(intro conjI impI)
  using main_invariant_1_preservation main_inv_def apply blast
  using main_invariant_2_preservation main_inv_def apply blast
  using main_invariant_3_preservation main_inv_def by blast

(*--------------------------------------------------------------------*)







(*----------------allocated_addresses ms ps--------------------*)

lemma allocated_addresses_preservation:
  "main_inv ms ps \<Longrightarrow> 
  t<T_max \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,vala] \<sigma> \<Longrightarrow>
  \<not>isfree_addr vala ps \<Longrightarrow>          \<comment> \<open>this is easily shown through alloc_addr\<close>
  general_structure ms \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
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
  apply (metis option.sel)
  apply(simp add:abbr allocated_addresses_lemmas)  
  defer                                                 (*FAAZ*)
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
  apply(intro conjI impI) 
  apply meson 
  apply(case_tac "det ms t = []", simp_all)
  apply(simp add:general_structure_def)
  apply (metis Rcap_def insertCI option.sel)  apply clarify
  apply(simp add:Rcap_def)
  apply(simp add:general_structure_def) 
  apply (metis (no_types, opaque_lifting) aap_supplem_1 less_Suc_eq nth_append_length)
  apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(case_tac "nondet_val ms t", simp_all)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(case_tac " det ms t \<noteq> [] ", simp_all)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas) 
  apply(simp add:abbr allocated_addresses_lemmas general_structure_def) 
  apply clarsimp 
  apply(intro conjI impI)
  apply(case_tac "det ms t = []", simp add:Rcap_def)
  apply clarsimp
  apply(subgoal_tac "hd (det ms t) = det ms t !0") prefer 2 
  apply (metis hd_conv_nth)
  apply (metis empty_iff insert_iff length_0_conv not_gr_zero) 
  apply (meson length_greater_0_conv n_differ_from_det_def)
  apply(case_tac "det ms t = []", simp add:Rcap_def)
  apply clarsimp
  apply(subgoal_tac "hd (det ms t) = det ms t !0") prefer 2 
  apply (metis hd_conv_nth) 
  apply(case_tac "t \<noteq> ta") 
  apply (meson det_differ_from_det_def length_greater_0_conv)
  apply clarify 
  apply clarsimp
  apply(case_tac "length(det ms t) = 1") 
  apply linarith
  apply(subgoal_tac "hd (det ms t) = det ms t !0") prefer 2 
  apply (metis hd_conv_nth)
  apply(subgoal_tac "tl (det ms t) ! ia = (det ms t) ! (ia+1)") prefer 2
  apply (metis One_nat_def Suc_eq_plus1 length_tl nth_tl) 
  apply(simp add:det_differ_from_det_def det_differ_inside_def) 
  apply (metis (no_types, lifting) Suc_less_eq Suc_pred length_greater_0_conv)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(case_tac " CTRsync\<^sub>1 ms t = t", simp_all)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:OpSem.step_def RdX_def) 
  apply(simp add:Rcap_def Wcap_def general_structure_def con_assms_def)
  apply clarsimp
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:OpSem.step_def RdX_def) 
  apply(simp add:Rcap_def Wcap_def general_structure_def con_assms_def)
  apply clarsimp
  apply(case_tac "reg ms t = Suc 0", simp_all)
  apply(simp add:abbr allocated_addresses_lemmas)
  apply(simp add:abbr allocated_addresses_lemmas)
  (*FAAZ*)
  apply(simp add:allocated_addresses_def)
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


(*--------------------------------------------------------------------*)







(*---------------------observation_inv_ms ms----------------------------*)





lemma Local_correctness_observation_inv_ms:
  "main_inv ms ps \<Longrightarrow> 
  t<T_max \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
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
  (*FAAZ*) defer
  apply(simp add:general_structure_lemmas con_assms_def observation_inv_sig_def main_inv_lemmas)
  apply clarify
  apply(simp add: step_def RdX_def)
  apply metis
  (*CAS*) defer
  apply(case_tac "CAS_succ ms t", simp_all)
  apply(simp add:abbr)
  apply(simp add:abbr)
  apply(simp add:general_structure_lemmas con_assms_def observation_inv_sig_def main_inv_lemmas)
  apply clarify 
  apply(subgoal_tac "det ms t @ [ya] = det ms' t") prefer 2
  apply clarsimp
  apply(subgoal_tac "\<forall>i. own\<^sub>W ms i = Some t \<longrightarrow> i\<in>detaddrs ms t \<or> i = the(s ms t)") prefer 2
  apply clarsimp
  apply meson
  apply(case_tac "loc \<notin> detaddrs ms t") 
  apply (metis lessI nth_append_length)
  apply clarify
  apply(case_tac "det ms t = []")
  apply (metis Suc_le_length_iff detaddrs_def empty_Collect_eq inlist_def insert_absorb insert_not_empty less_eq_Suc_le list.distinct(1))
  apply(subgoal_tac "\<forall> loc. loc\<in>detaddrs ms t \<longrightarrow> loc\<in>detaddrs ms' t") apply clarsimp 
  apply metis 
  apply (metis suppotingrandom1)
  apply clarify apply(case_tac "b") apply(simp_all)
  apply blast
  apply blast
  apply(case_tac "nondet_val ms t", simp_all)
  apply(simp add:abbr)
  apply(simp add:abbr)
  apply(case_tac " det ms t \<noteq> [] ", simp_all)
  apply(simp add:abbr)
  apply(simp add:abbr)
  apply(simp add:general_structure_lemmas con_assms_def observation_inv_sig_def main_inv_lemmas)
  apply clarify 
  apply(case_tac "det ms t=[]") 
  apply fastforce
  apply(case_tac "length(det ms t) = Suc 0")
  apply (metis less_Suc0)
  apply(subgoal_tac "\<forall> loc. loc\<in>detaddrs ms t \<longrightarrow> loc\<in>detaddrs ms' t \<or> loc = hd(det ms t)") apply clarsimp 
  apply meson 
  apply(subgoal_tac "hd(det ms t) = det ms t!0") prefer 2
  apply (meson blind_isabelle_hdlist)
  apply (metis suppotingrandom4)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all)
  apply(simp add:abbr)
  apply(simp add:abbr)
  apply(simp add:abbr)
  apply(simp add:general_structure_lemmas con_assms_def observation_inv_sig_def main_inv_lemmas)
  apply clarify apply(simp add:step_def RdX_def) 
  apply blast
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(simp add:abbr)
  apply(simp add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all)
  apply(simp add:abbr)
  apply(simp add:abbr)
  apply(simp add:general_structure_lemmas con_assms_def observation_inv_sig_def main_inv_lemmas)
  apply clarify apply(simp add:step_def RdX_def) 
  apply blast
  apply(case_tac "reg ms t = Suc 0", simp_all)
  apply(simp add:abbr)
  apply(simp add:abbr)
  defer
  apply(clarify) apply(simp add:cas_step_rcu_def) apply clarify
  apply(case_tac "snd (CAS t (a, b) (the (s ms t)) (the (n ms t)) \<sigma> ts')", simp_all)
  apply(case_tac "loc = y", simp_all) 
  apply(case_tac "y = ya", simp_all) 
  apply(case_tac "loc = ya", simp_all)
  apply metis
  apply blast
  apply(simp add:get_C_val_def FAAZ_def)
  apply(case_tac "repeat ms t", simp_all)
  apply clarsimp 
  apply metis
  apply clarsimp
  by metis 

(*---------------------------------------------------------------------*)






(*------------------------observation_inv_sig Correctness---------------------------*)




lemma Local_correctness_observation_inv_sig:
  "main_inv ms ps \<Longrightarrow> 
  t<T_max \<Longrightarrow>
  general_structure ms \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  cvd[C,vala] \<sigma> \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms  \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  con_assms ms ps \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
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
  apply (simp add:abbr)
  apply(simp add:observation_inv_sig_def)
  apply(simp add:abbr observation_inv_sig_def con_assms_def )
  apply (metis cvd_backwards_WrX )
  apply (simp add:abbr)
  apply(simp add:observation_inv_sig_def)
  apply(simp add:observation_inv_sig_def con_assms_def abbr)
  apply(case_tac "repeat ms t", simp_all)
  apply (metis cvd_backwards_WrX)
  apply (metis cvd_backwards_WrX )
  apply (simp add:abbr)
  apply(simp add:observation_inv_sig_def)
  apply(simp add:observation_inv_sig_def con_assms_def abbr)
  apply (metis cvd_backwards_WrX )
  (*FAAZ*) defer 
  apply(simp add:abbr observation_inv_sig_def) apply clarify
  apply(simp add:Wcap_def own\<^sub>W_n_by_t_imp_def)
  apply (metis not_cvd_RdX_pres)
  apply(simp add:writeto_star_n_def observation_inv_sig_def con_assms_def)
  apply (metis not_cvd_WrX_pres)  
  (*cas_step_rcu*) defer
  apply (simp add:abbr)
  apply(simp add:observation_inv_sig_def)
  apply(simp add:abbr observation_inv_sig_def con_assms_def)
  apply (metis cvd_backwards_WrX)
  apply(simp add:abbr observation_inv_sig_def con_assms_def)
  apply(simp add:abbr observation_inv_sig_def con_assms_def)
  apply(case_tac "CAS_succ ms t", simp_all)
  apply(simp add:abbr observation_inv_sig_def con_assms_def)
  apply(simp add:abbr observation_inv_sig_def con_assms_def)
  apply(simp add:abbr observation_inv_sig_def con_assms_def)
  apply(simp add:abbr observation_inv_sig_def con_assms_def)
  apply clarify apply(case_tac "b", simp_all)
  apply auto[1]
  apply auto[1]
  apply(case_tac "nondet_val ms t", simp_all)
  apply(simp add:abbr observation_inv_sig_def con_assms_def)
  apply(simp add:abbr observation_inv_sig_def con_assms_def)
  apply(case_tac "det ms t \<noteq> []", simp_all)
  apply(simp add:abbr observation_inv_sig_def con_assms_def)
  apply(simp add:abbr observation_inv_sig_def con_assms_def)
  apply(simp add:abbr observation_inv_sig_def con_assms_def)
  apply(simp add:Wcap_def own\<^sub>W_n_by_t_imp_def)
  apply clarify
  apply(case_tac "loc \<noteq> hd (det ms t)", simp_all)
  apply auto[1] 
  apply(simp add:Rcap_def)
  apply (metis length_greater_0_conv)
  apply(simp add:abbr observation_inv_sig_def con_assms_def)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all)
  apply(simp add:abbr observation_inv_sig_def con_assms_def)
  apply(simp add:abbr observation_inv_sig_def con_assms_def) 
  apply(simp add:abbr observation_inv_sig_def con_assms_def) apply clarify 
  apply(simp add:Wcap_def own\<^sub>W_n_by_t_imp_def)
  apply(simp add:observation_inv_sig_def)
  apply (metis not_cvd_RdX_pres)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(simp add:abbr observation_inv_sig_def con_assms_def) apply clarify 
  apply(simp add:Wcap_def own\<^sub>W_n_by_t_imp_def)
  apply(simp add:abbr observation_inv_sig_def con_assms_def) apply clarify 
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all)
  apply(simp add:abbr observation_inv_sig_def con_assms_def) apply clarify 
  apply(simp add:abbr observation_inv_sig_def con_assms_def) apply clarify 
  apply(simp add:abbr observation_inv_sig_def con_assms_def) apply clarify 
  apply (metis not_cvd_RdX_pres)
  apply(case_tac "reg ms t = Suc 0", simp_all)
  apply(simp add:abbr observation_inv_sig_def con_assms_def) apply clarify 
  apply(simp add:abbr observation_inv_sig_def con_assms_def) apply clarify 
(*FAAZ*)
  apply(simp add:abbr observation_inv_sig_def con_assms_def)
  apply(case_tac "repeat ms t", simp_all)
  apply(simp add:get_C_val_def)
  apply(subgoal_tac "cvd[C,vala] \<sigma>'") prefer 2
  using cvd_pres_by_FAAZ_unfold 
  apply (metis (no_types, lifting) wfs_2_def)
  apply(subgoal_tac "\<forall>t loc. t<T_max \<and> own\<^sub>W ms loc = Some t \<longrightarrow> t<T_max \<and> own\<^sub>W ms' loc = Some t") prefer 2
  apply clarsimp
  apply(subgoal_tac "\<forall>loc. isfree_addr loc ps \<longrightarrow> isfree_addr loc ps'") prefer 2
  apply clarsimp
  apply clarsimp
  apply (elim disjE) prefer 2
  apply (meson FAAZ_is_RMW_R testtttttt wfs_2_def wfs_2_preserved)
  apply (meson FAAZ_is_RMW_R testtttttt wfs_2_def wfs_2_preserved)
  apply(simp add:get_C_val_def)
  apply(subgoal_tac "cvd[C,vala] \<sigma>'") prefer 2
  using cvd_pres_by_FAAZ_unfold 
  apply (metis (no_types, lifting) wfs_2_def)
  apply(subgoal_tac "\<forall>t loc. t<T_max \<and> own\<^sub>W ms loc = Some t \<longrightarrow> t<T_max \<and> own\<^sub>W ms' loc = Some t") prefer 2
  apply clarsimp
  apply(subgoal_tac "\<forall>loc. isfree_addr loc ps \<longrightarrow> isfree_addr loc ps'") prefer 2
  apply clarsimp
  apply clarsimp
  apply (elim disjE) prefer 2
  apply (meson FAAZ_is_RMW_R testtttttt wfs_2_def wfs_2_preserved)
  apply (meson FAAZ_is_RMW_R testtttttt wfs_2_def wfs_2_preserved)
(*cas_step_rcu*)
  apply (simp add:cas_step_rcu_def)
  apply (simp add:observation_inv_sig_def)
  apply (simp add:CAS_def)
  apply(clarify)
  apply(case_tac "ya", simp_all)  prefer 2
  apply(case_tac "value \<sigma> (a, b) = yb", simp_all)
  apply(subgoal_tac "cvd[C,vala] \<sigma>'") prefer 2 
  apply (metis CAS_def cvd_pres_by_CAS_unfold_pt1 fst_conv wfs_2_def) apply clarsimp
  apply(simp add:covered_v_def Rcap_def main_inv_lemmas Wcap_def)
  apply metis
  apply(case_tac "value \<sigma> (a, b) = yb", simp_all)
  apply(case_tac "loc = yb", simp_all add:general_structure_lemmas)
  apply (metis (no_types, opaque_lifting) RMW_exist_w_in_post covered_v_def relating_step_to_update_trans_1)
  apply(case_tac "loc = y", simp_all add:Wcap_def)
  apply (meson allocated_addresses_def allocated_n_addr_def isfree_addr_def)
  by (metis (no_types, opaque_lifting) RMW_exist_w_in_post covered_v_def relating_step_to_update_trans_1)
  

(*--------------------------------------------------------------*)







(*-------------------own\<^sub>W_n_by_t_imp ms----------------------*)

lemma own\<^sub>W_n_by_t_imp_preservation:
  "main_inv ms ps \<Longrightarrow> 
  t<T_max \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  allocated_addresses ms ps\<Longrightarrow>
  general_structure ms \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms'"
  apply(simp add:step_def preCond_def)
  apply(case_tac "pc ms t", simp_all)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def) 
  apply clarify 
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply clarsimp apply(case_tac "ta = t", simp_all) 
  apply (simp add: main_inv_2_def main_inv_3_def main_inv_def)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp split:if_splits add: allocated_addresses_lemmas)
  apply(case_tac "repeat ms t", simp_all)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  defer                                         (*FAAZ*)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp split:if_splits add: allocated_addresses_lemmas)
  apply(simp add:Rcap_def)
  apply clarsimp
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)      
  defer                                         (*CAS*)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply(case_tac "CAS_succ ms t", simp_all)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply clarsimp
  apply(case_tac "nondet_val ms t", simp_all)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def) 
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def) 
  apply(case_tac "det ms t = []", simp_all)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def) 
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def) 
  defer                                   (*free(pop(detatched))*)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def) 
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def)
  apply clarsimp
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def) 
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def) 
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def) 
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def) 
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def) defer
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def) 
  apply(case_tac "reg ms t = Suc 0", simp_all)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def) 
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def) 
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def get_C_val_def Rcap_def)  (*FAAZ*)
  apply(case_tac "repeat ms t", simp_all)
  apply clarsimp
  apply clarsimp
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def cas_step_rcu_def Rcap_def)
  apply clarsimp
  apply(case_tac "ya", simp_all)
  apply (metis (no_types, lifting) general_structure_def n_differ_from_s_inside_def n_differ_from_s_outside_def option.sel)
  apply(simp add:abbr own\<^sub>W_n_by_t_imp_def Rcap_def)   (*free[pop[detached[t]]]*)
  apply (meson general_structure_def length_greater_0_conv n_differ_from_det_def)
  apply clarify
  by(simp add:OpSem.step_def)

  


(*--------------------------------------------------------------*)








(*-----------------------------General Struct Supp-------------------------------------------*)

(*FAAZ for n_differ*)
lemma faaz_n_differ:
  " main_inv ms ps' \<Longrightarrow>
    t < T_max \<Longrightarrow>
    n_differ ms \<Longrightarrow>
    ms \<sigma> s:=\<^sup>FC t ms' \<sigma>' \<and> ps = ps' \<Longrightarrow>
    preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
    pc ms t = I8 \<Longrightarrow>
    psem_rules ps \<Longrightarrow>
    allocated_addresses ms ps' \<Longrightarrow> n_differ ms'"
  unfolding general_structure_def
  unfolding get_C_val_def FAAZ_def n_differ_def allocated_addresses_lemmas main_inv_lemmas
  apply clarify 
  apply(case_tac "ta\<noteq>t") 
  apply simp
  apply(case_tac "taa\<noteq>t") 
  apply simp
  by meson
  
(*FAAZ for n_differ_from_s_outside*)
lemma faaz_n_differ_from_s_outside:
  " main_inv ms ps \<Longrightarrow>
    general_structure ms \<Longrightarrow>
    t < T_max \<Longrightarrow>
    wfs_2 \<sigma> \<Longrightarrow>
    cvd[C,l] \<sigma> \<Longrightarrow>
    n_differ_from_s_outside ms \<Longrightarrow>
    ms \<sigma> s:=\<^sup>FC t ms' \<sigma>' \<and> ps = ps' \<Longrightarrow>
    preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
    pc ms t = I8 \<Longrightarrow>
    con_assms ms ps \<Longrightarrow>
    own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
    observation_inv_sig ms ps \<sigma> \<Longrightarrow> n_differ_from_s_outside ms'"
  unfolding general_structure_def preCond_def own\<^sub>W_n_by_t_imp_def
  apply(simp add:get_C_val_def FAAZ_def n_differ_from_s_outside_def allocated_addresses_lemmas main_inv_lemmas)
   apply clarify
  apply(case_tac "ta = t")
  apply(subgoal_tac "n_dec ms ta") prefer 2
  apply meson
  apply(subgoal_tac "n ms ta = Some i") prefer 2
  apply auto[1]
  apply clarify
  apply(subgoal_tac "taa \<notin> own\<^sub>R ms i") prefer 2
  apply auto[1]
  apply(subgoal_tac "\<forall>loca. taa \<notin> own\<^sub>R ms loca \<longrightarrow> taa\<notin>own\<^sub>R ms' loca") prefer 2
  apply auto[1]
  apply(subgoal_tac "\<forall>loca. taa \<in> own\<^sub>R ms loca \<longrightarrow> taa\<in>own\<^sub>R ms' loca") prefer 2
  apply auto[1]
  apply blast
  apply(case_tac "taa \<noteq> t")
  apply(subgoal_tac "ta \<noteq> t") prefer 2 apply auto[1]
  apply(subgoal_tac "\<forall>loca. taa \<notin> own\<^sub>R ms loca \<longrightarrow> taa\<notin>own\<^sub>R ms' loca") prefer 2
  apply auto[1]
  apply(subgoal_tac "\<forall>loca. taa \<in> own\<^sub>R ms loca \<longrightarrow> taa\<in>own\<^sub>R ms' loca") prefer 2
  apply auto[1]
  apply(subgoal_tac "\<forall>loca. ta \<notin> own\<^sub>R ms loca \<longrightarrow> ta\<notin>own\<^sub>R ms' loca") prefer 2
  apply auto[1]
  apply(subgoal_tac "\<forall>loca. ta \<in> own\<^sub>R ms loca \<longrightarrow> ta\<in>own\<^sub>R ms' loca") prefer 2
  apply auto[1]
  apply clarsimp
  apply meson
  apply(subgoal_tac "taa = t") prefer 2 apply auto[1]
  apply(subgoal_tac "ta \<noteq> t") prefer 2 apply auto[1]
  apply clarsimp
  apply(subgoal_tac "\<forall>loca. ta \<notin> own\<^sub>R ms loca \<longrightarrow> ta\<notin>own\<^sub>R ms' loca") prefer 2
  apply auto[1]
  apply(subgoal_tac "\<forall>loca. ta \<in> own\<^sub>R ms loca \<longrightarrow> ta\<in>own\<^sub>R ms' loca") prefer 2
  apply auto[1]
  apply(subgoal_tac "\<forall>loca. t \<in> own\<^sub>R ms loca \<longrightarrow> t\<in>own\<^sub>R ms' loca") prefer 2
  apply auto[1]
  apply clarsimp
  by (smt (verit) CollectD covered_v_def observation_inv_sig_def visible_writes_def)



(*FAAZ for n_differ_from_s_inside*)
lemma faaz_n_differ_from_s_inside:
  " main_inv ms ps \<Longrightarrow>
    general_structure ms \<Longrightarrow>
    t < T_max \<Longrightarrow>
    wfs_2 \<sigma> \<Longrightarrow>
    cvd[C,l] \<sigma> \<Longrightarrow>
    n_differ_from_s_inside ms \<Longrightarrow>
    ms \<sigma> s:=\<^sup>FC t ms' \<sigma>' \<and> ps = ps' \<Longrightarrow>
    preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
    pc ms t = I8 \<Longrightarrow>
    con_assms ms ps \<Longrightarrow>
    own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
     psem_rules ps \<Longrightarrow>
    observation_inv_sig ms ps \<sigma> \<Longrightarrow> n_differ_from_s_inside ms'"
  unfolding general_structure_def
  unfolding get_C_val_def FAAZ_def n_differ_from_s_inside_def allocated_addresses_lemmas main_inv_lemmas
  apply clarify
  apply(subgoal_tac "n ms t = n ms' t") prefer 2 apply simp
  apply(subgoal_tac "s ms' t = Some (snd (update_trans t (a, b) (value \<sigma> (a, b)) \<sigma> ts', value \<sigma> (a, b)))") prefer 2
  apply clarsimp apply clarsimp
  apply(case_tac "ta = t", simp_all)
  by (metis Up_reads_cvd_v observation_inv_sig_def own\<^sub>W_n_by_t_imp_def relating_step_to_update_trans_1)


(*FAAZ for s_differ_from_det_inside*)
lemma faaz_s_differ_from_det_inside:
  " main_inv ms ps \<Longrightarrow>
    general_structure ms \<Longrightarrow>
    wfs_2 \<sigma> \<Longrightarrow>
    cvd[C,l] \<sigma> \<Longrightarrow>
    t < T_max \<Longrightarrow>
    s_differ_from_det_inside ms \<Longrightarrow>
    ms \<sigma> s:=\<^sup>FC t ms' \<sigma>' \<and> ps = ps' \<Longrightarrow>
    preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
    pc ms t = I8 \<Longrightarrow>
    con_assms ms ps \<Longrightarrow>
    own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
     psem_rules ps \<Longrightarrow>
    observation_inv_sig ms ps \<sigma> \<Longrightarrow> s_differ_from_det_inside ms'"
  unfolding general_structure_def
  unfolding get_C_val_def FAAZ_def s_differ_from_det_inside_def allocated_addresses_lemmas main_inv_lemmas
  apply clarify
  apply(case_tac "ta\<noteq>t")
  apply simp 
  apply (metis (no_types, lifting) insertE) apply clarsimp 
  by (smt (verit) CollectD covered_v_def observation_inv_sig_def own\<^sub>W_and_det_things_def visible_writes_def)
  

(*FAAZ for n_differ_from_det*)
lemma faaz_n_differ_from_det:
  " main_inv ms ps \<Longrightarrow>
    t < T_max \<Longrightarrow>
    wfs_2 \<sigma> \<Longrightarrow>
    n_differ_from_det ms \<Longrightarrow>
    ms \<sigma> s:=\<^sup>FC t ms' \<sigma>' \<and> ps = ps' \<Longrightarrow>
    preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
    pc ms t = I8 \<Longrightarrow>
    con_assms ms ps \<Longrightarrow>
     psem_rules ps \<Longrightarrow>
    allocated_addresses ms ps \<Longrightarrow> n_differ_from_det ms'"
  unfolding general_structure_def
  unfolding get_C_val_def FAAZ_def n_differ_from_det_def allocated_addresses_lemmas main_inv_lemmas
  apply clarify
  apply(case_tac "ta\<noteq>t")
  apply simp
  apply auto[1]
  apply(case_tac "taa\<noteq>t")
  apply simp
  apply auto[1]
  apply clarsimp 
  by blast

(*FAAZ for det_differ_from_det*)
lemma faaz_det_differ_from_det:
  " main_inv ms ps \<Longrightarrow>
    t < T_max \<Longrightarrow>
    wfs_2 \<sigma> \<Longrightarrow>
    det_differ_from_det ms \<Longrightarrow>
    ms \<sigma> s:=\<^sup>FC t ms' \<sigma>' \<and> ps = ps' \<Longrightarrow>
    preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
    pc ms t = I8 \<Longrightarrow>
    con_assms ms ps \<Longrightarrow>
     psem_rules ps \<Longrightarrow>
    allocated_addresses ms ps \<Longrightarrow> det_differ_from_det ms'"
  unfolding general_structure_def
  unfolding get_C_val_def FAAZ_def det_differ_from_det_def allocated_addresses_lemmas main_inv_lemmas
  apply clarify
  apply(case_tac "ta\<noteq>t")
  apply simp
  by auto[1]

(*FAAZ for det_differ_inside*)
lemma faaz_det_differ_inside:
  " main_inv ms ps \<Longrightarrow>
    t < T_max \<Longrightarrow>
    wfs_2 \<sigma> \<Longrightarrow>
    det_differ_inside ms \<Longrightarrow>
    ms \<sigma> s:=\<^sup>FC t ms' \<sigma>' \<and> ps = ps' \<Longrightarrow>
    preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
    pc ms t = I8 \<Longrightarrow>
    con_assms ms ps \<Longrightarrow>
    psem_rules ps \<Longrightarrow>
    allocated_addresses ms ps \<Longrightarrow> det_differ_inside ms'"
  unfolding general_structure_def
  unfolding get_C_val_def FAAZ_def det_differ_inside_def allocated_addresses_lemmas main_inv_lemmas
  apply clarify
  apply(case_tac "ta\<noteq>t")
  apply simp
  by auto[1]

(*FAAZ for own\<^sub>W_and_det_things*)
lemma faaz_own\<^sub>W_and_det_things:
  " main_inv ms ps \<Longrightarrow>
    t < T_max \<Longrightarrow>
    wfs_2 \<sigma> \<Longrightarrow>
    cvd[C,l] \<sigma> \<Longrightarrow> 
    own\<^sub>W_and_det_things ms \<Longrightarrow>
    ms \<sigma> s:=\<^sup>FC t ms' \<sigma>' \<and> ps = ps' \<Longrightarrow>
    preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
    pc ms t = I8 \<Longrightarrow>
    con_assms ms ps \<Longrightarrow>
    psem_rules ps \<Longrightarrow>
    allocated_addresses ms ps \<Longrightarrow>  own\<^sub>W_and_det_things ms'"
  unfolding general_structure_def
  unfolding get_C_val_def FAAZ_def own\<^sub>W_and_det_things_def allocated_addresses_lemmas main_inv_lemmas
  apply clarify
  apply(case_tac "ta\<noteq>t")
  apply simp
  by auto[1]








(*----------------general_structure ms preservation--------------------*)

lemma general_structure_preservation:
  "main_inv ms ps \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,l] \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  general_structure ms \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  general_structure ms'"
  apply(simp add:step_def)
  apply(case_tac "pc ms t", simp_all)
  apply(simp add: abbr general_structure_def)
  apply(intro conjI impI)
  apply(simp add: n_differ_def)
  apply blast
  apply(simp add: n_differ_def n_differ_from_s_outside_def)
  apply blast
  apply (simp add: n_differ_from_s_inside_def)
  apply (simp add: s_differ_from_det_inside_def)
  apply(simp add:n_differ_from_det_def)
  apply blast
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(simp add: abbr general_structure_def)
  apply(intro conjI impI)
  apply(simp add: n_differ_def)
  apply blast
  apply(simp add: n_differ_def n_differ_from_s_outside_def)
  apply blast
  apply (simp add: n_differ_from_s_inside_def)
  apply (simp add: s_differ_from_det_inside_def)
  apply(simp add:n_differ_from_det_def)
  apply blast
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(simp add: abbr general_structure_def)
  apply(intro conjI impI)
  apply(simp add: n_differ_def)
  apply blast
  apply(simp add: n_differ_def n_differ_from_s_outside_def)
  apply blast
  apply (simp add: n_differ_from_s_inside_def)
  apply (simp add: s_differ_from_det_inside_def)
  apply(simp add:n_differ_from_det_def)
  apply blast
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(simp add: abbr general_structure_def)
  apply(intro conjI impI)
  apply(simp add: n_differ_def preCond_def) apply auto[1] 
  apply(case_tac "ta = t", simp_all) apply clarsimp
  apply (metis (no_types, opaque_lifting) allocated_addresses_def isfree_addr_def pecpec1)
  apply (metis (no_types, opaque_lifting) allocated_addresses_def isfree_addr_def pecpec1)
  apply(simp add: n_differ_from_s_outside_def preCond_def) apply auto[1]
  apply(case_tac "ta = t", simp add:general_structure_lemmas) apply clarsimp
  apply (metis empty_iff isfree_addr_def main_inv_2_def main_inv_def)
  apply(simp add:general_structure_lemmas)
  apply (metis (no_types, opaque_lifting) allocated_addresses_def isfree_addr_def pecpec1)
  apply(simp add:general_structure_lemmas) apply clarsimp 
  apply(case_tac "ta = t", simp_all)
  apply clarsimp
  apply(simp add:preCond_def)
  apply(simp add:s_differ_from_det_inside_def preCond_def) apply auto[1]
  apply (metis (no_types, lifting) insertE option.simps(3))
  apply(simp add:n_differ_from_det_def preCond_def) apply auto[1]
  apply (metis (no_types, opaque_lifting) allocated_addresses_def allocated_det_addr_def isfree_addr_def option.sel)
  apply(simp add:det_differ_from_det_def preCond_def) apply auto[1]
  apply(simp add:det_differ_inside_def) apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def) apply auto[1]
  apply (metis allocated_addresses_def allocated_det_addr_def isfree_addr_def)
(*rcu_enter*)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
(*rcu_exit*)
  apply(case_tac "repeat ms t")
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
(*rcu_enter 2*)
  apply(case_tac "repeat ms t")
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
(*FAAZ*)
  apply (metis Unique_allocs_def constant_alloc_ass_def faaz_det_differ_from_det faaz_det_differ_inside faaz_n_differ faaz_n_differ_from_det faaz_n_differ_from_s_inside faaz_n_differ_from_s_outside faaz_own\<^sub>W_and_det_things faaz_s_differ_from_det_inside general_structure_def newran_def psem_rules_def wfs_2_def)
(*v:=*s*)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) apply auto[1]
  apply(simp add:s_differ_from_det_inside_def) apply auto[1] apply blast
  apply(simp add:n_differ_from_det_def)
  apply (metis (no_types, lifting) mstate.select_convs(3) mstate.select_convs(6) mstate.select_convs(8) mstate.surjective mstate.update_convs(1) mstate.update_convs(5))
  apply(simp add:det_differ_from_det_def) apply auto[1]
  apply(simp add:det_differ_inside_def) apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def) apply auto[1]
(**n:=newv*)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
(*cas_step_rcu*) 
  apply(simp add: cas_step_rcu_def general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1] apply meson apply meson
  apply(simp add:n_differ_from_s_outside_def) apply auto[1] apply meson apply meson
  apply(simp add:n_differ_from_s_inside_def) apply auto[1] apply meson apply meson
  apply(simp add:s_differ_from_det_inside_def) apply auto[1] apply blast apply blast apply blast
  apply(simp add:n_differ_from_det_def) apply auto[1] apply blast apply (metis (no_types, lifting)) apply (metis (no_types, lifting))
  apply(simp add:det_differ_from_det_def) apply auto[1]
  apply(simp add:det_differ_inside_def) apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def) apply auto[1]
  apply(case_tac "det ms ta ! i = yb", simp_all) apply auto[1]
  apply(simp add:observation_inv_sig_def)
  apply(simp add:CAS_def)
  apply(case_tac "value \<sigma> (a, b) = det ms ta ! i", simp_all)
  using visible_writes_def covered_v_def
  apply (smt (verit) CollectD)
  apply (simp add: n_differ_from_det_def)
 (*rcu_exit*)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
(*go_to_I14*)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def)
  apply(simp add:n_differ_from_det_def)
  apply(simp add:n_differ_from_det_def)
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
(*repeat?*)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:n_differ_from_s_outside_def)
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
(*CAS_succ choice*)
  apply(case_tac "CAS_succ ms t", simp_all)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
(*insert[detached[t],s]*)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) 
  apply(simp add:n_differ_from_det_def own\<^sub>W_n_by_t_imp_def) 
  apply clarsimp
  apply(intro conjI impI)
  apply auto[1]
  apply (smt (verit) Wcap_def bot_nat_0.extremum_strict insertCI less_Suc_eq list.size(3) nth_append nth_append_length option.sel)
  apply auto[1]
  apply blast
  apply(simp add:det_differ_from_det_def own\<^sub>W_n_by_t_imp_def) apply auto[1]
  apply (smt (verit) Wcap_def bot_nat_0.extremum_strict insertCI less_Suc_eq list.size(3) map_upd_eqD1 nth_append nth_append_length own\<^sub>W_and_det_things_def)
  apply (smt (verit) Wcap_def aap_supplem_1 diff_is_0_eq diff_zero insertCI less_Suc_eq less_Suc_eq_le list.size(3) map_upd_eqD1 nth_append_length own\<^sub>W_and_det_things_def)
  apply(simp add:det_differ_inside_def det_differ_from_det_def own\<^sub>W_n_by_t_imp_def) apply auto[1]
  apply safe
  apply(simp add:own\<^sub>W_and_det_things_def s_differ_from_det_inside_def)
  apply (smt (verit) Rcap_def aap_supplem_1 bot_nat_0.extremum_strict insertCI less_Suc_eq list.size(3) nth_append_length)
  apply(simp add:own\<^sub>W_and_det_things_def s_differ_from_det_inside_def det_differ_inside_def)
  apply auto[1] 
  apply(subgoal_tac "\<forall>i. i<length(det ms t) \<longrightarrow> own\<^sub>W ms ((det ms t) ! i) = Some t") prefer 2  
  apply (metis gr_implies_not_zero list.size(3))  
  apply (metis (no_types, lifting) Wcap_def insertCI less_Suc_eq nth_append nth_append_length)
(*nondet()*)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
(*nondet choice*)
  apply(case_tac "nondet_val ms t", simp_all)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
(*move_to_r5 if det ms t=[]*)
  apply(case_tac "det ms t \<noteq> []", simp_all)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
(*free[pop[detached[t]]]*)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply (smt (z3) One_nat_def diff_less length_greater_0_conv length_tl lessI less_trans_Suc nth_tl)
  apply(simp add:det_differ_from_det_def) 
  apply (simp add: less_diff_conv nth_tl)
  apply(simp add:det_differ_inside_def) 
  apply (simp add: less_diff_conv nth_tl)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply (simp add: less_diff_conv nth_tl)
  apply (metis (no_types, lifting) Nitpick.size_list_simp(2) Suc_less_eq det_differ_from_det_def det_differ_inside_def length_greater_0_conv nat.distinct(1) nth_tl)
(*r[N]:={0}*)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
(*if CRTsync1 then...splits*)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
(*r[i]:=rcu[CTRsync\<^sub>1 ms t]*)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) apply auto[1]
  apply(simp add:s_differ_from_det_inside_def) apply auto[1] apply blast
  apply(simp add:n_differ_from_det_def) apply auto[1] apply blast
  apply(simp add:det_differ_from_det_def) apply auto[1]
  apply(simp add:det_differ_inside_def) apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def) apply auto[1]
(*if CTRsync\<^sub>2 ms t < T_max splits*)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
(*r ms t (CTRsync\<^sub>2 ms t) = 0 splits*)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
(*loadCTRsync\<^sub>2*)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) apply auto[1]
  apply(simp add:s_differ_from_det_inside_def) apply auto[1] apply blast
  apply(simp add:n_differ_from_det_def) apply auto[1] apply blast
  apply(simp add:det_differ_from_det_def) apply auto[1]
  apply(simp add:det_differ_inside_def) apply auto[1]
  apply(simp add:own\<^sub>W_and_det_things_def) apply auto[1]
(*reg ms t = Suc 0 splits*)
  apply(case_tac "reg ms t = Suc 0", simp_all)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  apply(simp add:own\<^sub>W_and_det_things_def)
  apply(simp add: abbr general_structure_def preCond_def)
  apply(intro conjI impI)
  apply(simp add:n_differ_def) apply auto[1]
  apply(simp add:n_differ_from_s_outside_def) apply auto[1]
  apply(simp add:n_differ_from_s_inside_def) 
  apply(simp add:s_differ_from_det_inside_def) apply auto[1]
  apply(simp add:n_differ_from_det_def) 
  apply(simp add:det_differ_from_det_def)
  apply(simp add:det_differ_inside_def)
  by(simp add:own\<^sub>W_and_det_things_def)


(*--------------------------------------------------------------------*)







(*----------------Local Correctness--------------------*)

lemma Local_Correctness_preservation:
  "main_inv ms ps \<Longrightarrow> 
  t<T_max \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  general_structure ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms' t) t"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms t", simp_all)
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) 
  apply (meson insertI1)
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(case_tac "repeat ms t", simp_all)
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(intro conjI impI) 
  apply clarsimp
  apply(simp add:general_structure_lemmas) apply clarify
  apply (metis less_nat_zero_code list.size(3))
  apply meson
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def get_C_val_def) apply clarsimp
  apply(intro conjI impI)
  apply(simp add:Rcap_def)
  apply(simp add:Wcap_def) 
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) 
(*cas_step*) defer
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply (metis own\<^sub>W_n_by_t_imp_def)
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(case_tac "CAS_succ ms t", simp_all) 
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:general_structure_def own\<^sub>W_and_det_things_def)
  apply(simp add:main_inv_lemmas) apply clarsimp
  apply(subgoal_tac "length(det ms t @ [ya]) = Suc(length(det ms t))") prefer 2
  apply (meson length_append_singleton)
  apply (metis aap_supplem_1 bot_nat_0.extremum_strict less_Suc_eq list.size(3) nth_append_length)
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(case_tac "nondet_val ms t", simp_all)
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(case_tac "det ms t \<noteq> [] ", simp_all)
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp defer
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp defer
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all)
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
(*r[i]:=rcu[counter]*) defer
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all)
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
(*load(counter)*) defer
  apply(case_tac "reg ms t = Suc 0", simp_all)
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
(*dealing with cas_step_rcu*)
  apply(simp add:cas_step_rcu_def) apply clarsimp
  apply(case_tac "ya", simp_all)
  apply(simp add:abbr Rcap_def Wcap_def) apply clarsimp
  apply (metis general_structure_def less_nat_zero_code list.size(3) n_differ_from_det_def)
  apply(simp add:abbr Rcap_def Wcap_def) defer defer
(*dealing with r[i]:=rcu[counter]*)
  apply(simp add:load_rcu_to_r_def) apply clarsimp
  apply(simp add:abbr Rcap_def Wcap_def)
(*dealing with rcu_temp_copy*)
  apply(simp add:rcu_temp_copy_def)
  apply clarsimp 
  apply(simp add:abbr Rcap_def Wcap_def) defer
  apply(intro conjI impI)
  apply (simp add: det_differ_inside_def general_structure_def nth_tl)
  apply(subgoal_tac "\<forall>j. j<length(det ms t) \<longrightarrow> own\<^sub>W ms (det ms t!j) = Some t") prefer 2 
  apply blast
  apply safe
  sledgehammer
  sorry
(*--------------------------------------------------------------------*)






(*----------------- Supporting Global Correctness -----------------*)

lemma Global_Correctness_preservation_S1:
  "pc ms t = S1 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr)
  apply(simp_all add:abbr Rcap_def Wcap_def)
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] by auto[1]



lemma Global_Correctness_preservation_S2:
  "pc ms t = S2 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr)
  apply(case_tac[!] "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply(case_tac[!] "CTRsync\<^sub>1 ms t = t", simp_all add:abbr Rcap_def Wcap_def)
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] apply auto[1]
  apply auto[1] apply auto[1] apply auto[1] by auto[1]




lemma Global_Correctness_preservation_S3:
  "pc ms t = S3 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr)
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify apply auto[1]
  apply(simp add:Rcap_def Wcap_def) apply clarify by auto[1]








lemma Global_Correctness_preservation_S4:
  "pc ms t = S4 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr)
  apply(case_tac[!] "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) by metis






lemma Global_Correctness_preservation_S5:
  "pc ms t = S5 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr)
  apply(case_tac[!] "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) by metis






lemma Global_Correctness_preservation_S6:
  "pc ms t = S6 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  apply (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)
  apply(simp add:Rcap_def Wcap_def) 
  by (metis canonically_ordered_monoid_add_class.lessE con_assms_def counters_limit_def le_neq_implies_less not_add_less1)





lemma Global_Correctness_preservation_S7:
  "pc ms t = S7 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr)
  apply(case_tac[!] "reg ms t = Suc 0", simp_all add:abbr)
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) by metis








lemma Global_Correctness_preservation_R1:
  "pc ms t = R1 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr)
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis apply(simp add:Rcap_def Wcap_def) by metis




lemma Global_Correctness_preservation_R2:
  "pc ms t = R2 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(clarify) apply(case_tac "b", simp_all)
  apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) apply(case_tac "b", simp_all)
  apply(simp add:Rcap_def Wcap_def) apply(clarify) by(case_tac "b", simp_all)




lemma Global_Correctness_preservation_R3:
  "pc ms t = R3 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr)
  apply(case_tac[!] "nondet_val ms t", simp_all add:abbr)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) 
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) by metis




lemma Global_Correctness_preservation_R4:
  "pc ms t = R4 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr)
  apply(case_tac[!] "det ms t \<noteq> []", simp_all add:abbr)
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) 
  apply(simp add:Rcap_def Wcap_def) 
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
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) apply metis
  apply(simp add:Rcap_def Wcap_def) by metis




lemma Global_Correctness_preservation_R5:
  "pc ms t = R5 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr)
  apply(intro conjI impI)
  apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(intro conjI impI)
  apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(intro conjI impI)
  apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(intro conjI impI)
  apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(intro conjI impI)
  apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(case_tac "repeat ms ta", simp_all)
  apply(intro conjI impI)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(simp add:Rcap_def Wcap_def)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis con_assms_def counters_limit_def leD)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis con_assms_def counters_limit_def leD)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis con_assms_def counters_limit_def leD)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(simp add:Rcap_def Wcap_def)
  apply (metis length_greater_0_conv singleton_iff)
  apply(intro conjI impI)
  apply (metis con_assms_def counters_limit_def leD)
  apply (metis con_assms_def counters_limit_def leD)
  apply (metis con_assms_def counters_limit_def leD)
  apply (metis con_assms_def counters_limit_def leD)
  apply (metis con_assms_def counters_limit_def leD)
  apply (metis con_assms_def counters_limit_def leD)
  apply (metis con_assms_def counters_limit_def leD)
  apply (metis con_assms_def counters_limit_def leD)
  by (metis con_assms_def counters_limit_def leD)



lemma Global_Correctness_preservation_cas_res:
  "pc ms t = cas_res \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr cas_step_rcu_def Rcap_def Wcap_def)
  apply(case_tac[!] "CAS_succ ms t", simp_all add:abbr)
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) by(clarify, simp) 




lemma Global_Correctness_preservation_I1:
  "pc ms t = I1 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr cas_step_rcu_def Rcap_def Wcap_def)
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) by(clarify, simp) 



lemma Global_Correctness_preservation_I2:
  "pc ms t = I2 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr cas_step_rcu_def Rcap_def Wcap_def)
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) by(clarify, simp) 


lemma Global_Correctness_preservation_I3:
  "pc ms t = I3 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr cas_step_rcu_def Rcap_def Wcap_def)
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) by(clarify, simp) 





lemma Global_Correctness_preservation_I4:
  "pc ms t = I4 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr cas_step_rcu_def Rcap_def Wcap_def)
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply(case_tac "repeat ms ta", simp_all)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply(case_tac "CAS_succ ms ta", simp_all)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject)
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis con_assms_def counters_limit_def leD)
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  apply (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  apply(clarify, simp add:observation_inv_ms_def allocated_addresses_lemmas)
  by (metis insert_iff less_nat_zero_code list.size(3) option.inject) 
  


lemma Global_Correctness_preservation_I5:
  "pc ms t = I5 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr cas_step_rcu_def Rcap_def Wcap_def)
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) by(clarify, simp) 


lemma Global_Correctness_preservation_I6:
  "pc ms t = I6 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr cas_step_rcu_def Rcap_def Wcap_def)
  apply(case_tac[!] "repeat ms t", simp_all)
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) by(clarify, simp)





lemma Global_Correctness_preservation_I7:
  "pc ms t = I7 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr cas_step_rcu_def Rcap_def Wcap_def)
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) by(clarify, simp) 






lemma Global_Correctness_preservation_I8:
  "pc ms t = I8 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr get_C_val_def FAAZ_def cas_step_rcu_def Rcap_def Wcap_def)
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(case_tac "repeat ms t", simp_all)
  apply (metis con_assms_def counters_limit_def leD)
  apply (metis con_assms_def counters_limit_def leD)
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  by(clarify, simp) 







lemma Global_Correctness_preservation_I9:
  "pc ms t = I9 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr cas_step_rcu_def Rcap_def Wcap_def)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(case_tac "CAS_succ ms ta", simp_all)
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) apply(clarify, simp) apply(clarify, simp) 
  apply(clarify, simp) by(clarify, simp)





lemma Global_Correctness_preservation_I10:
  "pc ms t = I10 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr cas_step_rcu_def Rcap_def Wcap_def)
  apply metis apply metis apply metis apply metis apply metis
  apply metis apply metis apply metis apply metis apply metis
  apply metis apply metis apply metis apply metis apply metis
  apply metis apply metis apply metis apply metis apply metis
  apply metis apply metis apply metis by metis




lemma Global_Correctness_preservation_I11:
  "pc ms t = I11 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> observation_inv_ms ms \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr cas_step_rcu_def Rcap_def Wcap_def)
  apply(intro conjI impI)
  apply(clarify , case_tac "ya", simp_all)
  apply(clarify , case_tac "ya", simp_all)
  apply auto[1]
  apply (meson general_structure_def n_differ_from_s_outside_def)
  apply (meson general_structure_def n_differ_from_s_outside_def)
  apply (simp add: general_structure_lemmas)
  apply(subgoal_tac "n ms ta \<noteq> Some yb") prefer 2
  apply (metis option.distinct(1))
  apply(subgoal_tac "s ms ta \<noteq> Some yb") prefer 2
  apply presburger
  apply(subgoal_tac "\<forall>i. i<length (det ms ta) \<longrightarrow> det ms ta !i \<noteq> vala") prefer 2
  apply(simp add:observation_inv_sig_def)
  apply metis
  apply(simp add:CAS_def visible_writes_def covered_v_def)
  apply (metis Pair_inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(clarify, case_tac "ya", simp_all)
  apply(clarify, case_tac "ya", simp_all)
  apply(clarify, case_tac "ya", simp_all)
  apply(clarify, case_tac "ya", simp_all)
  apply(clarify, case_tac "ya", simp_all)
  apply(clarify, case_tac "ya", simp_all)
  apply(clarify)
  apply(intro conjI impI)
  apply (metis option.inject)
  apply (metis option.inject)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(case_tac "vala = yb", simp_all)
  apply metis
  apply(clarify, case_tac "ya", simp_all)
  apply(clarify)
  apply(intro conjI impI)
  apply (metis option.inject)
  apply (metis option.inject)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(case_tac "vala = yb", simp_all)
  apply metis
  apply(clarify, case_tac "ya", simp_all)
  apply(clarify)
  apply(intro conjI impI)
  apply (metis option.inject)
  apply (metis option.inject)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(case_tac "vala = yb", simp_all)
  apply metis
  apply(clarify, case_tac "yb", simp_all)
  apply(clarify)
  apply(intro conjI impI)
  apply (metis option.inject)
  apply (metis option.inject)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis Pair_inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.inject prod.inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "yb", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "yb", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "yb", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "yb", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply(case_tac "vala = yd", simp_all)
  apply(case_tac "CAS_succ ms ta", simp_all)
  apply (metis option.sel)
  apply (metis option.sel)
  apply metis
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  apply (metis option.sel prod.inject)
  apply(clarify, case_tac "ya", simp_all)
  apply(simp add:CAS_def visible_writes_def covered_v_def observation_inv_sig_def)
  by (metis option.sel prod.inject)
  
  




lemma Global_Correctness_preservation_I12:
  "pc ms t = I12 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr Rcap_def Wcap_def)
  by metis+

lemma Global_Correctness_preservation_I13:
  "pc ms t = I13 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr Rcap_def Wcap_def)
  by metis+



lemma Global_Correctness_preservation_I14:
  "pc ms t = I14 \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (simp_all add:step_def preCond_def)
  apply(case_tac "pc ms ta", simp_all add:abbr Rcap_def Wcap_def)
  by metis+


lemma Global_Correctness_preservation_finished:
  "pc ms t = finished \<Longrightarrow>
  main_inv ms ps \<Longrightarrow>  t<T_max \<Longrightarrow> ta<T_max \<Longrightarrow> t\<noteq>ta \<Longrightarrow> wfs_2 \<sigma> \<Longrightarrow> cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow> psem_rules ps \<Longrightarrow> allocated_addresses ms ps \<Longrightarrow> con_assms ms ps \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  by (simp_all add:step_def preCond_def)



(*----------------Global Correctness--------------------*)

lemma Global_Correctness_preservation:
  "main_inv ms ps \<Longrightarrow> 
  t<T_max \<Longrightarrow>
  ta<T_max \<Longrightarrow>
  t\<noteq>ta \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  cvd[C,vala] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms ta) ta \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow> 
  observation_inv_ms ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  con_assms ms ps \<Longrightarrow>
  preCond ms' ps' \<sigma>' (pc ms ta) ta"
  apply (case_tac "pc ms t")
  using Global_Correctness_preservation_I1 apply blast
  using Global_Correctness_preservation_I2 apply blast
  using Global_Correctness_preservation_I3 apply blast
  using Global_Correctness_preservation_I4 apply blast
  using Global_Correctness_preservation_I5 apply blast
  using Global_Correctness_preservation_I6 apply blast
  using Global_Correctness_preservation_I7 apply blast
  using Global_Correctness_preservation_I8 apply blast
  using Global_Correctness_preservation_I9 apply blast
  using Global_Correctness_preservation_I10 apply blast
  using Global_Correctness_preservation_I11 apply blast
  using Global_Correctness_preservation_I12 apply blast
  using Global_Correctness_preservation_I13 apply blast
  using Global_Correctness_preservation_I14 apply blast
  using Global_Correctness_preservation_cas_res apply blast
  using Global_Correctness_preservation_finished apply blast
  using Global_Correctness_preservation_R1 apply blast
  using Global_Correctness_preservation_R2 apply blast
  using Global_Correctness_preservation_R3 apply blast
  using Global_Correctness_preservation_R4 apply blast
  using Global_Correctness_preservation_R5 apply blast
  using Global_Correctness_preservation_S1 apply blast
  using Global_Correctness_preservation_S2 apply blast
  using Global_Correctness_preservation_S3 apply blast
  using Global_Correctness_preservation_S4 apply blast
  using Global_Correctness_preservation_S5 apply blast
  using Global_Correctness_preservation_S6 apply blast
  using Global_Correctness_preservation_S7 by blast




(*--------------------------------------------------------------------*)





















(*=======================================================*)
(*+++++++++++++++++++these "MIGHT" be useful+++++++++++++*)
(*=======================================================*)

(*---------------counter2_rule ms------------------------*)

lemma Local_counter2_rule:
  "main_inv ms ps \<Longrightarrow> 
  t<T_max \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps \<sigma> (pc ms t) t \<Longrightarrow> 
  counter2_rule ms \<Longrightarrow>
  con_assms ms ps \<Longrightarrow>
  general_structure ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  psem_rules ps \<Longrightarrow> 
  own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  counter2_rule ms'"
  apply (simp_all add:step_def preCond_def counter2_rule_def)
  apply(case_tac "pc ms t", simp_all add:abbr)
  apply clarsimp
  apply(simp split: if_splits)
  apply(simp add:general_structure_def n_differ_from_det_def Rcap_def own\<^sub>W_and_det_things_def)
  apply(simp add:allocated_addresses_lemmas)
  apply (metis less_nat_zero_code list.size(3))
  apply blast
  apply clarsimp 
  apply(case_tac "repeat ms t", simp)
  apply (metis (no_types, lifting) DiffD1)
  apply blast  
  defer (*FAAZ*)
  apply clarsimp
  apply blast
  apply clarsimp
  apply(case_tac "snd (CAS t (a, b) ya y \<sigma> ts')", simp_all)
  apply blast
  apply blast
  apply clarsimp
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply blast
  apply blast
  apply auto[1]
  apply clarsimp
  apply blast
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply clarsimp
  


  sorry
