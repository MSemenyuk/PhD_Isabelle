theory MPA
imports StackSemantics Lib_GeneralProofRules OpSem_Proof_Rules
begin

datatype PC =
  L1
| L2
| L3

consts t1 :: T 
consts t2 :: T
consts d :: L
consts f :: L

definition "thrdsvars \<equiv> t1 \<noteq> t2 \<and> 
                        d \<noteq> f"


record mp_state =
  pc :: "T \<Rightarrow> PC"
  state :: surrey_state
  lstate :: stacks_state
  r :: V 

definition 
  "update_pc t nv pcf \<equiv> pcf (t := nv)"


lemmas mp_sis [simp] = 
  update_pc_def 
  thrdsvars_def


definition prog :: "T \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool " where
"prog t s s' \<equiv> 
(
  if t = t1
    then
      if (pc s) t = L1
        then
           pc s'  = update_pc t L2 (pc s) \<and>
           (state s) [d:=5]\<^sub>t (state s') \<and> lstate s' = lstate s \<and>
           r s = r s'
        else
          if (pc s) t = L2
            then
              pc s' = update_pc t L3 (pc s) \<and>
              (lstate s) (state s) PUSH[1, True]\<^sub>t (lstate s') (state s') \<and>
              r s = r s'
            else
              False
  else
    if t = t2
      then
        if (pc s) t = L1
          then
            (pc s' = update_pc t L2 (pc s) \<and>
            ((lstate s) (state s) POP[1, True]\<^sub>t (lstate s') (state s')))
            \<or>
            (pc s'  = pc s \<and>
            (\<exists> v . v \<noteq> 1 \<and> ((lstate s) (state s) POP[v, True]\<^sub>t (lstate s') (state s'))))
         else
          if (pc s) t = L2
            then
              pc s' = update_pc t L3 (pc s) \<and> lstate s' = lstate s \<and>
              ((state s) [r s' \<leftarrow> d]\<^sub>t (state s'))
            else
              False
   else
    False
)"

definition prog_inv :: "T \<Rightarrow> PC \<Rightarrow> mp_state \<Rightarrow> bool " where
"prog_inv t p s \<equiv> let t' = t2 in
  if t = t1
    then
      (case p of
          L1 \<Rightarrow> \<not>[POP \<approx>\<^sub>t' 1] (lstate s) \<and> [d =\<^sub>t 0] (state s)
        | L2 \<Rightarrow> \<not>[POP \<approx>\<^sub>t' 1] (lstate s) \<and> [d =\<^sub>t 5] (state s)
        | L3 \<Rightarrow> [d =\<^sub>t 5] (state s)
      )
  else 
     if t = t2 then
      (case p of
          L1 \<Rightarrow> [POP = 1]\<lparr>d =\<^sub>t 5\<rparr> (lstate s) (state s)
        | L2 \<Rightarrow> [d =\<^sub>t 5] (state s)
        | L3 \<Rightarrow> r s = 5 
      )
  else False
"

lemma t1_local:
  assumes "thrdsvars"
      and "wfs (state s)"
      and "ops_wfs (lstate s) (state s)"
      and "prog_inv t1 ((pc s) t1) s" 
      and "prog t1 s s'"
    shows "prog_inv t1 ((pc s') t1) s'"
  using assms 
  apply (simp add: prog_def prog_inv_def)
  apply (cases "pc s t1"; simp)
  using d_obs_WrX_set apply blast
  using d_obs_push_pres apply blast
  done

lemma t1_global :
  assumes "prog_inv t1 ((pc s) t1) s"
      and "wfs (state s)"
      and "ops_wfs (lstate s) (state s)"
   and "prog_inv t2 ((pc s) t2) s"
  and "thrdsvars"
  and "prog t2 s s'"
shows  "prog_inv t1 ((pc s') t1) s'"
  using assms 
  apply (simp add: prog_inv_def prog_def)
  apply (cases "(pc s) t1";cases "(pc s) t2";cases  "pc s' t1"; simp)
             apply(elim conjE exE disjE, intro conjI)
  using not_p_pops_pop_pres apply blast
  using d_obs_pop_pres apply auto[1]
             apply(intro conjI)
  using not_p_pops_pop_pres apply blast
  using d_obs_pop_pres apply blast
  apply auto[1]
           apply auto[1]
  using dobs_RdX_pres apply blast
         apply(intro conjI)
          apply auto[1]
  apply auto[1]
  using d_obs_pop_pres not_p_pops_pop_pres apply blast
  apply auto[1]
  using dobs_RdX_pres apply blast  
  apply auto[1]  
  apply auto[1]
  using d_obs_pop_pres apply blast
  using dobs_RdX_pres by blast



lemma t2_local:
  assumes "thrdsvars"
      and "wfs (state s)"
       and "ops_wfs (lstate s) (state s)"
     and "prog_inv t2 ((pc s) t2) s" 
      and "prog t2 s s'"
    shows "prog_inv t2 ((pc s') t2) s'"
  using assms 
  apply (simp add: prog_def prog_inv_def)
  apply (cases "pc s t2", auto)
  using c_pops_transfer apply blast
  using p_pops_pop_pres_poped_value_unknown apply blast
  using d_obs_read_value by blast


lemma t2_global :
  assumes "wfs (state s)" 
        and "ops_wfs (lstate s) (state s)"
   and "prog_inv t2 ((pc s) t2) s"
   and "prog_inv t1 ((pc s) t1) s"
  and "thrdsvars"
  and "prog t1 s s'"
shows  "prog_inv t2 ((pc s') t2) s'"
  using assms 
  apply (simp add: prog_inv_def prog_def)
  apply (cases "(pc s) t2";cases "(pc s) t1"; cases "(pc s') t2")
                      apply simp_all
  defer
  using c_pops_intro apply blast
  apply(elim conjE)
   apply (simp add: d_obs_def d_obs_t_def)
  using d_obs_push_pres apply blast
  apply (elim conjE)
  using not_p_pops_c_obs_client_write
  by blast



theorem final_inv:
  assumes "wfs (state s)"   
  assumes "ops_wfs (lstate s) (state s)"   
  and "thrdsvars"
  and "t \<in> {t1, t2}"
  and "t' \<in> {t1, t2}"
  and "prog_inv t ((pc s) t) s"
  and "prog_inv t' ((pc s) t') s" 
  and "prog t' s s'"
shows "prog_inv t ((pc s') t) s'"
  using assms apply (simp del: thrdsvars_def) 
  using t1_global t1_local t2_global t2_local 
  by blast
    
end
