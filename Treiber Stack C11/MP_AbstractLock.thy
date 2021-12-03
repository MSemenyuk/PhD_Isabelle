theory MP_AbstractLock
  imports Main AbstractLock_Proof_Rules OpSem_Proof_Rules
begin
datatype PC =
  L1
| L2
| L3
| L4
| L5



consts t1 :: T 
consts t2 :: T
consts d1 :: L
consts d2 :: L
consts l :: L


definition "thrdsvars \<equiv>  t1 \<noteq> t2 \<and> d1 \<noteq> d2"


record prog_state =
  pc :: "T \<Rightarrow> PC"
  state :: surrey_state
  lstate :: lib_state
  r :: V
  r2 :: V
  loc1 :: bool
  loc2 :: bool
  rel1 :: bool
  rel2 :: bool
  ver1 :: V
  ver2 :: V

definition 
  "update_pc t nv pcf \<equiv> pcf (t := nv)"


definition prog :: "T \<Rightarrow> prog_state \<Rightarrow> prog_state  \<Rightarrow> bool " where
"prog t s s' \<equiv> 
(
if t = t1
then
if (pc s) t = L1
then
     [(state s) (lstate s) t LOCKACQ(l) (state s') (lstate s') (loc1 s') (ver1 s')]
     \<and> (loc1 s' \<longrightarrow> pc s' = update_pc t L2 (pc s))
     \<and> (\<not> loc1 s' \<longrightarrow> pc s' = pc s)  
     \<and> (r s' = r s)
     \<and> (r2 s' = r2 s)
     \<and> (rel1 s' = rel1 s)  
     \<and> (rel2 s' = rel2 s) 
     \<and> (loc2 s' = loc2 s)
     \<and> (ver2 s' = ver2 s)
else
if (pc s) t = L2
then 
    (state s) [d1 := 5]\<^sub>t (state s')
    \<and> pc s' = update_pc t L3 (pc s)
    \<and> (lstate s = lstate s')
    \<and> (r s = r s')
    \<and> (rel1 s' = rel1 s)
    \<and> (rel2 s' = rel2 s) 
    \<and> (loc2 s' = loc2 s)
    \<and> (loc1 s' = loc1 s)
    \<and> (ver2 s' = ver2 s)
else
if (pc s) t = L3
then 
    (state s) [d2 := 5]\<^sub>t (state s')
    \<and> pc s' = update_pc t L4 (pc s)
    \<and> (lstate s = lstate s')
    \<and> (r s = r s')
    \<and> (rel1 s' = rel1 s)
    \<and> (rel2 s' = rel2 s) 
    \<and> (loc2 s' = loc2 s)
    \<and> (loc1 s' = loc1 s)
    \<and> (ver2 s' = ver2 s)
else
if (pc s) t = L4
then 
    [(state s) (lstate s) t LOCKREL(l) (lstate s') (state s')] 
     \<and> pc s' =  update_pc t L5 (pc s)
     \<and> (state s = state s')
     \<and> (r s = r s')
     \<and> (loc1 s' = loc1 s) 
     \<and> (loc2 s' = loc2 s)
     \<and> (rel2 s' = rel2 s)
     \<and> (rel1 s' = True)
     \<and> (ver2 s' = ver2 s)
else
False
else

if t = t2
then
if (pc s) t = L1
then
     [(state s) (lstate s) t LOCKACQ(l) (state s') (lstate s') (loc2 s')  (ver2 s')]
     \<and> (loc2 s' = True \<longrightarrow> pc s' = update_pc t L2 (pc s))
     \<and> (loc2 s' = False \<longrightarrow> pc s' = pc s) \<and> (r s = r s') \<and> (r2 s = r2 s')
     \<and> (rel1 s' = rel1 s)  \<and> (rel2 s' = rel2 s) \<and> (loc1 s = loc1 s')
else
if (pc s) t = L2
then 
    (state s) [r s' \<leftarrow> d1]\<^sub>t (state s')
    \<and> pc s' = update_pc t L3 (pc s)
    \<and> (lstate s = lstate s')
    \<and> (rel1 s' = rel1 s)  \<and> (rel2 s' = rel2 s)
    \<and> (loc2 s = loc2 s') \<and>  (loc1 s = loc1 s')
    \<and> (ver2 s' = ver2 s)
else
if (pc s) t = L3
then 
    (state s) [r2 s' \<leftarrow> d2]\<^sub>t (state s')
    \<and> pc s' = update_pc t L4 (pc s)
    \<and> (lstate s = lstate s')
    \<and> (rel1 s' = rel1 s)  \<and> (rel2 s' = rel2 s)
    \<and> (loc2 s = loc2 s') \<and>  (loc1 s = loc1 s') \<and> (r s = r s')
    \<and> (ver2 s' = ver2 s)
else
if (pc s) t = L4
then 
    [(state s) (lstate s) t LOCKREL(l) (lstate s') (state s')] 
     \<and> pc s' =   update_pc t L5 (pc s) \<and>
    (state s = state s') \<and> (r s = r s')
    \<and> (loc2 s' = loc2 s) \<and> (loc1 s' = loc1 s) 
    \<and> (rel1 s' = rel1 s)  \<and> (rel2 s' = True) \<and> (r s = r s')
    \<and> (ver2 s' = ver2 s)
else
False
else
False
)
"

definition "mutex s \<equiv> (rel1 s \<longrightarrow> loc1 s) \<and>
                      (rel2 s \<longrightarrow> loc2 s) \<and>
                      \<not> ((loc1 s \<and> \<not>rel1 s) \<and> (loc2 s \<and> \<not>rel2 s))"

(* need to add that ver2 s = 0 \<or> ver2 s = 2 *)
definition "global_inv s \<equiv> (wfs (state s)) \<and> (lib_wfs (lstate s) (state s)) \<and> thrdsvars \<and> mutex s "

definition "init_state s \<equiv> thrdsvars \<and> (wfs (state s)) \<and>  (lib_wfs (lstate s) (state s)) \<and> ([lib(l) =\<^sub>t1 0] (lstate s)) \<and> ([lib(l) =\<^sub>t2 0] (lstate s))
                  \<and> ([d1 =\<^sub>t1 0] (state s)) \<and> ([d1 =\<^sub>t2 0] (state s))  
                  \<and> ([d2 =\<^sub>t1 0] (state s)) \<and> ([d2 =\<^sub>t2 0] (state s))  
                  \<and> (loc1 s = False) \<and> (loc2 s = False) 
                  \<and> (rel1 s = False) \<and> (rel2 s = False) \<and> (r s = 0)
                  \<and>  cvd[lib(l), 0] (lstate s)"


definition "prog_inv t p s \<equiv> 
  global_inv s \<and>
  (if t = t1 
  then
    let t' = t2 in 
    (case p of
          L1 \<Rightarrow>  (\<not>rel1 s)  \<and> (\<not>loc1 s) 
                \<and> ([d1 =\<^sub>t 0] (state s))
                \<and> ([d2 =\<^sub>t 0] (state s))
                \<and> (\<not>loc2 s \<longrightarrow> ([lib(l) =\<^sub>t 0] (lstate s)) \<and> (\<not>[lib(l) \<approx>\<^sub>t' 2] (lstate s)))
                \<and> (\<not>loc2 s \<longrightarrow> ([lib(l) =\<^sub>t' 0] (lstate s)) \<and> (cvd[lib(l), 0] (lstate s)))
                \<and> (loc2 s \<and> \<not>rel2 s \<longrightarrow> cvd[lib(l), 1] (lstate s)) 
                \<and> (loc2 s \<and> rel2 s \<longrightarrow> (cvv[lib(l), 0] (lstate s)))
        | L2 \<Rightarrow>  (loc1 s) \<and> (\<not>rel1 s)
                \<and> ([d1 =\<^sub>t 0] (state s))
                \<and> ([d2 =\<^sub>t 0] (state s))
                \<and> (\<not>loc2 s \<longrightarrow>  \<not>[lib(l) \<approx>\<^sub>t' 2] (lstate s))
                \<and> cvv[lib(l),0] (lstate s) 
        | L3 \<Rightarrow>  (loc1 s) \<and> (\<not>rel1 s) 
                \<and> ([d1 =\<^sub>t 5] (state s))
                \<and> ([d2 =\<^sub>t 0] (state s))
                \<and> (\<not>loc2 s \<longrightarrow>  \<not>[lib(l) \<approx>\<^sub>t' 2] (lstate s))
                \<and> cvv[lib(l),0] (lstate s) 
        | L4 \<Rightarrow>  (loc1 s) \<and> (\<not>rel1 s)
                \<and> (\<not>loc2 s \<longrightarrow>  \<not>[lib(l) \<approx>\<^sub>t' 2] (lstate s))
                \<and> ([d1 =\<^sub>t 5] (state s))
                \<and> ([d2 =\<^sub>t 5] (state s))
                \<and> cvv[lib(l),0] (lstate s) 
        | L5 \<Rightarrow> (rel1 s) \<and> (loc1 s)
    )
  else
    if t = t2 then
      let t' = t1 in 
      (case p of
          L1 \<Rightarrow>  \<not>rel2 s \<and> \<not>loc2 s 
                \<and> (
                    (rel1 s \<and> ([lib(l) = 2]\<lparr>d1 =\<^sub>t 5\<rparr> (lstate s) (state s))
                     \<and> ([lib(l) = 2]\<lparr>d2 =\<^sub>t 5\<rparr> (lstate s) (state s)))                    
                  \<or> (  ([lib(l) =\<^sub>t 0] (lstate s)) \<and> [d1 =\<^sub>t 0] (state s)
                     \<and> [d2 =\<^sub>t 0] (state s))
                  \<or> (loc1 s \<and> \<not> rel1 s))
                \<and> (\<not>loc1 s \<longrightarrow> ([lib(l) =\<^sub>t' 0] (lstate s)) \<and> (cvd[lib(l), 0] (lstate s)))
                \<and> (loc1 s \<and> \<not>rel1 s \<longrightarrow> cvd[lib(l), 1] (lstate s))  
                \<and> (rel1 s \<longrightarrow> cvv[lib(l), 0] (lstate s))
        | L2 \<Rightarrow>   \<not>rel2 s \<and> loc2 s  \<and> (cvv[lib(l), 0] (lstate s))
                \<and> (ver2 s = 2 \<longrightarrow> [d1 =\<^sub>t 5] (state s) \<and> [d2 =\<^sub>t 5] (state s))   
                \<and> (ver2 s = 0 \<longrightarrow> [d1 =\<^sub>t 0] (state s) \<and> [d2 =\<^sub>t 0] (state s))
        | L3 \<Rightarrow>  \<not>rel2 s \<and> loc2 s  \<and> (cvv[lib(l), 0] (lstate s))
                \<and> (ver2 s = 2 \<longrightarrow> r s = 5 \<and> [d2 =\<^sub>t 5] (state s))   
                \<and> (ver2 s = 0 \<longrightarrow> r s = 0 \<and> [d2 =\<^sub>t 0] (state s))
        | L4 \<Rightarrow>  loc2 s \<and> \<not>rel2 s \<and> (cvv[lib(l), 0] (lstate s))
                \<and> (ver2 s = 2 \<longrightarrow> r s = 5 \<and> r2 s = 5) 
                \<and> (ver2 s = 0 \<longrightarrow> r s = 0 \<and> r2 s = 0)
        | L5 \<Rightarrow> loc2 s \<and> rel2 s
      )

  else
    False)
"

(* r s = 5 \<and> r1 s = 5 \<or> r s = 0 \<and> r s = 0 *)

lemmas autos = mutex_def global_inv_def update_pc_def prog_def prog_inv_def thrdsvars_def

lemma init_inv:
  assumes  "init_state s"
    and "global_inv s"
      and "t\<in>{t1,t2}"
    shows "prog_inv t L1 s"
  using assms
  apply (simp add: autos  init_state_def)
  apply(intro conjI impI; elim disjE)
  using lib_d_obs_not_p_obs zero_neq_numeral apply blast
  apply blast
  apply blast
  by blast

lemma global_inv_init:
  assumes "init_state s"
  shows "global_inv s"
  using assms
  apply (simp add: init_state_def autos)
  done




lemma t1_local:
  assumes "prog_inv t1 ((pc s) t1) s" 
      and "prog t1 s s'"
    shows "prog_inv t1 ((pc s') t1) s'"
  using assms 
  apply(case_tac "pc s t1", simp_all)
     apply(case_tac "pc s' t1", simp_all)
            apply (simp_all add: prog_inv_def prog_def global_inv_def thrdsvars_def update_pc_def)
         apply(unfold mutex_def, elim conjE)
  apply (smt PC.distinct(1) fun_upd_same lock_acquire_def lock_acquire_step_def prod.sel(1) prod.sel(2))
  apply(intro conjI)
  using lock_acqure_wfs_pres apply blast
  using lock_acqure_lib_wfs_pres apply blast
  using lock_acquire_cvd_odd_false apply force
            apply blast+
  using lock_acquire_cvd_odd_false apply force
            apply (metis PC.distinct(1))
  
           apply (metis (full_types) PC.distinct(1) lock_acqure_successfulib_client_pres_d_obs)
  apply (metis (full_types) PC.distinct(1) lock_acqure_successfulib_client_pres_d_obs)

      apply (smt PC.distinct(1) add_le_same_cancel2 lock_acquire_successful_p_obs of_nat_0 of_nat_le_0_iff) 
         defer 
  apply (metis PC.distinct(4) PC.simps(10) fun_upd_same)
  apply (metis PC.distinct(11) PC.distinct(5) fun_upd_same)
  apply (metis PC.distinct(13) PC.distinct(7) fun_upd_same)                       
  apply (metis d_obs_WrX_other d_obs_WrX_set step_pres_lib_wfs wfs_preserved)
  apply (meson d_obs_WrX_other d_obs_WrX_set step_pres_lib_wfs wfs_preserved)
   apply (metis lock_release_lib_wfs_pres)
  apply(elim conjE)
  apply simp
  apply(cases "loc2 s", simp_all)
  apply(cases "rel2 s", simp_all)
  defer
    apply (metis PC.distinct(1) even_Suc even_zero lock_acquire_cvd_odd_false)
   apply(cases "loc1 s'", simp_all)
  apply(elim conjE)
  using cvd_cvv_val apply blast
  using cvv_lock_acquire_pres by blast

lemma t2_local:
  assumes "prog_inv t2 ((pc s) t2) s" 
      and "prog t2 s s'"
    shows "prog_inv t2 ((pc s') t2) s'"
  using assms 
  apply(case_tac "t1 \<noteq> t2")
  apply(case_tac "pc s t2", simp_all)
     apply(case_tac "pc s' t2", simp_all)
            apply (simp_all add: prog_inv_def prog_def global_inv_def thrdsvars_def update_pc_def)
        apply(unfold mutex_def)
          apply simp_all
  apply (smt PC.distinct(1) fun_upd_same lock_acquire_def lock_acquire_step_def prod.sel(1) prod.sel(2))
       apply(elim conjE, intro conjI)  
  using lock_acqure_wfs_pres apply blast
  using lock_acqure_lib_wfs_pres apply blast
         apply (metis One_nat_def lock_acquire_cvd_odd_false odd_one)
      apply auto[1]
          apply (elim disjE conjE)
  using cvv_lock_acquire_pres apply blast
  apply (metis (full_types) PC.distinct(1) cvd_cvv_val cvv_lock_acquire_pres even_Suc even_zero lock_acquire_cvd_odd_false)
  apply (metis PC.distinct(1) even_Suc even_zero lock_acquire_cvd_odd_false)
         apply (intro conjI impI)
         apply (metis (full_types) PC.distinct(1) lock_acquire_cvd_odd_false lock_acquire_successful_c_o_s lock_acquire_successful_rv numeral_1_eq_Suc_0 numeral_One odd_one zero_neq_numeral)
  apply (metis (full_types) PC.distinct(1) lock_acquire_cvd_odd_false lock_acquire_successful_c_o_s lock_acquire_successful_rv numeral_1_eq_Suc_0 numeral_One odd_one zero_neq_numeral)
        defer
  apply (metis PC.distinct(3) PC.distinct(9) fun_upd_same)
  apply (metis PC.distinct(11) PC.distinct(5) fun_upd_same)
  apply (metis PC.distinct(13) PC.distinct(7) fun_upd_same)
     apply (metis d_obs_RdX_other d_obs_read_value step_pres_lib_wfs wfs_preserved)
  using d_obs_read_value step_pres_lib_wfs wfs_preserved apply blast
   apply (metis lock_release_lib_wfs_pres)
  apply (elim disjE)
    defer
    apply (metis (full_types) PC.distinct(1) lock_acqure_successfulib_client_pres_d_obs)
  apply (metis PC.distinct(1) even_Suc even_zero lock_acquire_cvd_odd_false)
  by (metis (full_types)  PC.distinct(1) cvv_val)

lemma t1_global:
  assumes "prog_inv t1 ((pc s) t1) s" 
      and "prog_inv t2 ((pc s) t2) s" 
      and "prog t2 s s'"
    shows "prog_inv t1 ((pc s') t1) s'"
  using assms 
  apply(case_tac "pc s t1")
     apply(case_tac "pc s t2")
  apply(case_tac "pc s' t1")
           apply(simp_all add: prog_inv_def prog_def global_inv_def mutex_def thrdsvars_def update_pc_def)
          apply(intro conjI)
  using lock_acqure_wfs_pres apply blast
  using lock_acqure_lib_wfs_pres apply blast
  apply (metis (full_types) lock_acquire_successfulib_diff_t_d_p_obs_pres lock_acquire_unsuccessful_diff_t_d_p_obs_pres)
  
  apply (metis (full_types) lock_acquire_successfulib_diff_t_d_p_obs_pres lock_acquire_unsuccessful_diff_t_d_p_obs_pres)

  apply (metis (full_types) OpSem.null_def lock_acquire_successful_not_p_obs_pres lock_acquire_unsuccessful_d_obs_pres)  
   
  apply (metis (full_types) lock_acquire_unsuccessful_d_obs_pres lock_acquire_unsuccessfulib_cvd_pres)

  apply (elim conjE, intro impI, simp)  
  
  using lock_acquire_successfulib_cvd apply fastforce
   apply fastforce 
            apply auto[3]
  using dobs_RdX_pres step_pres_lib_wfs wfs_preserved apply blast
  using dobs_RdX_pres step_pres_lib_wfs wfs_preserved apply blast
  apply(intro conjI)
  apply (metis lock_release_lib_wfs_pres)
  apply(case_tac "pc s t2"; simp)
      apply(case_tac "pc s' t1"; simp)
      apply (metis cvv_release)
  apply(case_tac "pc s t2"; simp)
      apply(case_tac "pc s' t1"; simp)
  using lock_acquire_cvd_odd_false apply fastforce
  apply (smt One_nat_def lock_acquire_cvd_odd_false lock_acquire_def lock_acquire_step_def odd_one prod.sel(1) prod.sel(2))
  apply (metis PC.distinct(9) even_Suc even_zero lock_acquire_cvd_odd_false)
  apply (metis One_nat_def PC.distinct(11) lock_acquire_cvd_odd_false odd_one)
  apply (metis PC.distinct(14) autos(3) fun_upd_def)
  apply(case_tac "pc s t2"; simp)
  apply(case_tac "pc s' t1"; simp)
  apply (metis)
  apply (metis)
  apply (smt One_nat_def lock_acquire_cvd_odd_false lock_acquire_def lock_acquire_step_def odd_one prod.sel(1) prod.sel(2))
  apply (metis)  
  apply (metis)
  apply(case_tac "pc s t2"; simp)
  apply(case_tac "pc s' t1"; simp)
  apply (metis)
  apply (metis)
  apply (metis)  
  apply (smt One_nat_def lock_acquire_cvd_odd_false lock_acquire_def lock_acquire_step_def odd_one prod.sel(1) prod.sel(2))
  apply (metis)
  apply blast+
  apply(case_tac "pc s t2"; simp)
       apply(case_tac "pc s' t1"; simp) 
  using lock_acquire_cvd_odd_false apply fastforce
  apply (metis PC.simps(10) autos(3) fun_upd_def)
  apply (smt One_nat_def lock_acquire_cvd_odd_false lock_acquire_def lock_acquire_step_def odd_one prod.sel(1) prod.sel(2))
  apply (metis PC.distinct(15) autos(3) fun_upd_def)
  apply (metis PC.distinct(17) autos(3) fun_upd_other)
  apply (metis)
  apply (metis)
  apply (metis)
  apply(case_tac "pc s t2"; simp)
       apply(case_tac "pc s' t1"; simp) 
  apply (metis PC.distinct(5) autos(3) fun_upd_apply)
  apply (metis PC.distinct(11) autos(3) fun_upd_other)
  apply (metis PC.distinct(15) autos(3) fun_upd_apply)
  apply (smt One_nat_def lock_acquire_cvd_odd_false lock_acquire_def lock_acquire_step_def odd_one prod.sel(1) prod.sel(2))
  apply (metis PC.simps(20) autos(3) fun_upd_apply)
  apply blast+
  apply(case_tac "pc s t2"; simp)
       apply(case_tac "pc s' t1"; simp) 
  apply (metis PC.distinct(7) autos(3) fun_upd_other)
  apply (metis PC.distinct(13) autos(3) fun_upd_other)
  apply (metis PC.distinct(17) autos(3) fun_upd_other)
  apply (metis PC.distinct(19) autos(3) fun_upd_other) 
  using lock_acqure_lib_wfs_pres lock_acqure_wfs_pres apply blast
  apply (smt PC.simps(25) autos(3) fun_upd_other step_pres_lib_wfs wfs_preserved)
    apply (smt PC.simps(25) autos(3) fun_upd_other step_pres_lib_wfs wfs_preserved)
  apply (smt PC.simps(25) autos(3) fun_upd_other lock_release_lib_wfs_pres)
  done

lemma t2_global:
  assumes "prog_inv t1 ((pc s) t1) s" 
      and "prog_inv t2 ((pc s) t2) s" 
      and "prog t1 s s'"
    shows "prog_inv t2 ((pc s') t2) s'"
  using assms 
  apply(subgoal_tac "t1 \<noteq> t2")
  apply(simp add: prog_def)
  apply(case_tac "pc s t1", simp_all)
    apply(case_tac "pc s t2", simp_all)
       apply(case_tac "pc s' t2", simp_all)
           apply(simp_all add: prog_inv_def global_inv_def thrdsvars_def update_pc_def)
           apply(unfold  mutex_def, elim conjE)
           apply simp
  apply(intro conjI)  
  using lock_acqure_wfs_pres apply blast
  using lock_acqure_lib_wfs_pres apply blast
               apply (metis (full_types)  lock_acquire_unsuccessful_d_obs_pres lock_acquire_unsuccessful_diff_t_d_p_obs_pres)
  
  apply (metis (full_types) lock_acquire_unsuccessful_d_obs_pres lock_acquire_unsuccessfulib_cvd_pres)
  using lock_acquire_successfulib_cvd apply force
 apply force
           apply auto[1]

          apply auto[1]
  
  apply auto[1]

  apply (intro conjI)
  apply (smt One_nat_def PC.simps(22) global_inv_def lock_acquire_cvd_odd_false lock_acquire_unsuccessful_diff_t_d_p_obs_pres lock_acqure_lib_wfs_pres lock_acqure_wfs_pres mutex_def odd_one thrdsvars_def)
  apply (smt One_nat_def PC.simps(23) global_inv_def lock_acquire_cvd_odd_false lock_acquire_unsuccessful_diff_t_d_p_obs_pres lock_acqure_lib_wfs_pres lock_acqure_wfs_pres mutex_def odd_one thrdsvars_def)
  apply (smt One_nat_def PC.simps(24) global_inv_def lock_acquire_cvd_odd_false lock_acqure_lib_wfs_pres lock_acqure_wfs_pres mutex_def odd_one thrdsvars_def)
  apply (smt PC.simps(25) fun_upd_other global_inv_def lock_acqure_lib_wfs_pres lock_acqure_wfs_pres mutex_def thrdsvars_def)
     defer defer defer
  apply (case_tac "pc s t1"; simp add: thrdsvars_def prog_def global_inv_def)
    apply (case_tac "pc s t2"; simp)
         apply (intro conjI)
  using lock_acqure_wfs_pres apply blast
  
  using lock_acqure_lib_wfs_pres apply blast
  apply (metis lock_acquire_cvd_odd_false numeral_1_eq_Suc_0 numeral_One odd_one)
    apply (case_tac "pc s' t2"; simp)
  apply auto[1]
  apply (metis PC.distinct(11) fun_upd_apply)
  apply (metis PC.distinct(15) fun_upd_other)
  using cvv_lock_acquire_pres apply blast
  apply auto[1]
         apply (intro conjI)
  using lock_acqure_wfs_pres apply blast
  using lock_acqure_lib_wfs_pres apply blast
  apply blast+
  apply auto[1]
    apply (case_tac "pc s t2"; simp)
  using step_pres_lib_wfs wfs_preserved apply blast
  using step_pres_lib_wfs wfs_preserved apply blast
    apply (case_tac "pc s t2"; simp)
  using step_pres_lib_wfs wfs_preserved apply blast
  using step_pres_lib_wfs wfs_preserved apply blast
  apply (case_tac "pc s t2"; simp)
  using step_pres_lib_wfs wfs_preserved apply blast
  apply (case_tac "pc s t2"; simp)
  using step_pres_lib_wfs wfs_preserved apply blast+
  apply (case_tac "pc s t2"; simp)
  apply (metis cvv_release lock_rel_c_obs_intro lock_release_lib_wfs_pres)
        apply blast+
  using lock_release_lib_wfs_pres apply force 
  apply (metis lock_acquire_cvd_odd_false numeral_1_eq_Suc_0 numeral_One odd_one)
  apply (case_tac "pc s' t2"; simp)
       apply auto[1]
  apply (smt cvv_lock_acquire_pres lock_acquire_successfulib_diff_t_d_p_obs_pres lock_acquire_unsuccessful_diff_t_d_p_obs_pres)
  apply (metis PC.distinct(9) fun_upd_apply)
  apply (metis PC.distinct(11) fun_upd_other)
  apply auto[1]
  by (smt PC.simps(23) cvv_lock_acquire_pres lock_acquire_cvd_odd_false lock_acquire_unsuccessful_diff_t_d_p_obs_pres lock_acqure_lib_wfs_pres lock_acqure_wfs_pres numeral_1_eq_Suc_0 numeral_One odd_one)

end
