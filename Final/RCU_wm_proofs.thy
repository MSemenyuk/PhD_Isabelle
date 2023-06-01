theory RCU_wm_proofs
imports RCU_model
begin 

(*
\<lbrace> [rcu[t] =\<^sub>t 0] \<rbrace>
 rcu[t] := 1                     **I5**         \<parallel>
   \<lbrace> [rcu[t] =\<^sub>t 1] \<rbrace>                            \<parallel>
                                                \<parallel>
  rcu[t] := 0                    **I6**         \<parallel>     rcu[t'] := 0
                                                \<parallel>
   \<lbrace> [rcu[t] =\<^sub>t 0] \<rbrace>                             \<parallel>       
                                                \<parallel>
  rcu[t] := 1                    **I7**         \<parallel>     rcu[t'] := 1 
                                                \<parallel>
  \<lbrace> [rcu[t] =\<^sub>t 1]  \<rbrace>                             \<parallel>    \<lbrace> [rcu[t'] =\<^sub>t\<^sub>' 1] \<rbrace>
                                                \<parallel>
  \<lbrace> \<forall> t' u. cvd(C, u)                           \<parallel>    \<lbrace> \<forall> t'' u. cvd(C, v) 
        \<and> t'\<in> own\<^sub>R ms u \<longrightarrow>                     \<parallel>          \<and> t''\<in> own\<^sub>R ms v \<longrightarrow>    
        [[C = u]]_t\<lparr>rcu[t'] =\<^sub>t 1\<rparr>   \<rbrace>            \<parallel>          [[C = v]]_t\<lparr>rcu[t''] =\<^sub>t\<^sub>' 1\<rparr>   \<rbrace>
                                                \<parallel>
                                                \<parallel>
  s\<^sub>t \<longleftarrow>\<^sup>F\<^sup>A\<^sup>A\<^sup>Z C                     **I8**        \<parallel>      s\<^sub>t\<^sub>' \<longleftarrow>\<^sup>F\<^sup>A\<^sup>A\<^sup>Z C 
                                                \<parallel>
  \<lbrace> [rcu[t] =\<^sub>t 1] \<rbrace>                             \<parallel>    \<lbrace> [rcu[t'] =\<^sub>t\<^sub>' 1] \<rbrace>  
                                                \<parallel>
  \<lbrace> (t'\<in> own\<^sub>R ms s\<^sub>t \<longrightarrow> [rcu[t'] =\<^sub>t 1])          \<parallel>   \<lbrace> (t''\<in> own\<^sub>R ms s\<^sub>t\<^sub>' \<longrightarrow> [rcu[t''] =\<^sub>t\<^sub>' 1])
     \<and> (\<forall> t' u. cvd(C, u)                       \<parallel>      \<and> (\<forall> t'' u. cvd(C, u)       
               \<and> t'\<in> own\<^sub>R ms u \<longrightarrow>              \<parallel>                \<and> t''\<in> own\<^sub>R ms u \<longrightarrow>    
                  [[C = u]]_t\<lparr>rcu[t'] =\<^sub>t 1\<rparr>)\<rbrace>    \<parallel>                   [[C = u]]_t\<lparr>rcu[t''] =\<^sub>t\<^sub>' 1\<rparr>)\<rbrace>
                                                \<parallel>
   CAS\<^sup>R\<^sup>A( &C, s\<^sub>t, n\<^sub>t)              **I11**       \<parallel>      CAS\<^sup>R\<^sup>A( &C, s\<^sub>t\<^sub>', n\<^sub>t\<^sub>')
                                                \<parallel>
  \<lbrace> [rcu[t] =\<^sub>t 1] \<rbrace>                             \<parallel>    \<lbrace> [rcu[t'] =\<^sub>t\<^sub>' 1] \<rbrace>  
                                                \<parallel>
  \<lbrace> t'\<in> own\<^sub>R ms s\<^sub>t \<longrightarrow> [rcu[t'] =\<^sub>t 1] \<rbrace>          \<parallel>   \<lbrace> t''\<in> own\<^sub>R ms s\<^sub>t\<^sub>' \<longrightarrow> [rcu[t''] =\<^sub>t\<^sub>' 1] \<rbrace>
                                                \<parallel>
                                                \<parallel>
  rcu[t] := 0                    **I12**        \<parallel>     rcu[t'] := 0
                                                \<parallel>
                                                \<parallel>
  \<lbrace> t'\<in> own\<^sub>R ms s\<^sub>t \<longrightarrow> [rcu[t'] =_t 1] \<rbrace>         \<parallel>
                                                \<parallel>
 4 reg\<^sub>t <-- rcu[t']              **S3**         \<parallel>     reg\<^sub>t' <-- rcu[t]       

*)





(****************-----------PRELIMINARY-----------*****************)

lemma Failed_CAS_preserves_d_obs_1:
  assumes "[x =\<^sub>t u] \<sigma>"
    and "\<sigma>' = read_trans t False w \<sigma>"
    and "w \<in> visible_writes \<sigma> t l"
    and "x \<noteq> l"
  shows "[x =\<^sub>t u] \<sigma>'"
  using assms
  apply(simp add:cas_step_def CAS_def) 
  apply(simp add:d_obs_t_def d_obs_def)
  by (metis lastWr_read_pres)


lemma Failed_CAS_preserves_d_obs_supporting_for_later:
  assumes "[x =\<^sub>t u] \<sigma>"
    and "\<sigma>' = read_trans t' False w \<sigma>"
    and "w \<in> visible_writes \<sigma> t' l"
    and "x \<noteq> l"
  shows "[x =\<^sub>t u] \<sigma>'"
  using assms
  apply(case_tac "t = t'") using Failed_CAS_preserves_d_obs_1 apply blast
  apply(simp add:cas_step_def CAS_def) 
  apply(simp add:d_obs_t_def d_obs_def)
  apply(simp add:read_trans_def rev_app_def)
  by (metis assms(2) lastWr_read_pres)



lemma Failed_CAS_preserves_d_obs_3:
  assumes "[x =\<^sub>t u] \<sigma>"
  and " w \<in> visible_writes \<sigma> t l "
  and "l \<noteq> x"
  and "\<sigma>' = read_trans t False w \<sigma>"
shows "[x =\<^sub>t u] \<sigma>'"
  using assms 
  by (metis Failed_CAS_preserves_d_obs_1)
  


lemma relating_step_to_update_trans_1:
  assumes "\<sigma>' = update_trans t w nv' \<sigma> ts'"
  and "k = value \<sigma> w"
  and "w \<notin> covered \<sigma>"
  and "valid_fresh_ts \<sigma> w ts'"
  and "w \<in> visible_writes \<sigma> t l"
  shows "OpSem.step t (Update l k nv') \<sigma> \<sigma>'"
  using assms apply (simp add:OpSem.step_def) 
  by (metis prod.exhaust_sel)
  


lemma d_obs_other_representation_2: \<comment> \<open>Rule: DV-Other\<close>
  assumes "wfs \<sigma>"
  and "[x =\<^sub>t u] \<sigma>"
  and "w \<in> visible_writes \<sigma> t l"
  and "w \<notin> covered \<sigma>"
  and "valid_fresh_ts \<sigma> w ts'"
  and "\<sigma>' = update_trans t w nv' \<sigma> ts'" 
  and "l \<noteq> x"
  shows "[x =\<^sub>t u] \<sigma>'"
  using assms d_obs_other
  by (metis avar.simps(3) relating_step_to_update_trans_1) 


lemma Succ_CAS_preserves_d_obs_1:
  assumes "[x =\<^sub>t u] \<sigma>"
    and " w \<in> visible_writes \<sigma> t l"
    and " w \<notin> covered \<sigma>"
    and "valid_fresh_ts \<sigma> w ts'"
    and "wfs \<sigma>"
    and "\<sigma>' = update_trans t w nv' \<sigma> ts'"
    and "x \<noteq> l"
  shows "[x =\<^sub>t u] \<sigma>'"
  using assms 
  by (metis d_obs_other_representation_2)




lemma CAS_preserves_d_obs_7:
  assumes "[(rcu_0 + t) =\<^sub>t u] \<sigma>"
  and "cas_step t C cv nv \<sigma> \<sigma>'"
  and "C \<noteq> (rcu_0 + t)"
  and "wfs \<sigma>"
shows "[(rcu_0 + t) =\<^sub>t u] \<sigma>'"
  using assms apply(simp add:cas_step_def CAS_def) apply clarsimp
  apply(case_tac "value \<sigma> (a, b) = cv", simp_all)
  prefer 2 
  apply (meson Failed_CAS_preserves_d_obs_3) 
  using d_obs_other_representation_2 by blast


lemma CAS_preserves_d_obs_8:
  assumes "[(rcu_0 + t) =\<^sub>t u] \<sigma>"
  and "cas_step_rcu ms \<sigma> t l cv nv ms' \<sigma>'"
  and "C \<noteq> (rcu_0 + t)"
  and "wfs \<sigma>"
shows "cas_step t l cv nv \<sigma> \<sigma>'"
  using assms apply(simp add:cas_step_rcu_def cas_step_def CAS_def) apply clarsimp
  apply(case_tac "value \<sigma> (a, b) = cv", simp_all)
  prefer 2 
  apply (meson Failed_CAS_preserves_d_obs_3) 
  apply blast  
  by blast



lemma CAS_preserves_d_obs_9:
  assumes "[(rcu_0 + t) =\<^sub>t u] \<sigma>"
  and "cas_step_rcu ms \<sigma> t C cv nv ms' \<sigma>'"
  and "C \<noteq> (rcu_0 + t)"
  and "wfs \<sigma>"
shows "[(rcu_0 + t) =\<^sub>t u] \<sigma>'"
  using assms apply(subgoal_tac "cas_step t C cv nv \<sigma> \<sigma>'", simp_all)
  using CAS_preserves_d_obs_7 apply blast
  by (simp add: CAS_preserves_d_obs_8)



lemma shows_WM_local_corr_1:
  " pre_cond \<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>' \<Longrightarrow>
  wfs \<sigma> \<Longrightarrow> cvd[C, u] \<sigma> \<Longrightarrow> the (n ms t)\<noteq>(rcu_0+t) \<Longrightarrow> C \<noteq> (rcu_0 + t) \<Longrightarrow>
((pre_step \<in> {I5,I7}         \<and> pre_cond = [(rcu_0 + t) =\<^sub>t 0] \<sigma>) \<longrightarrow>  [(rcu_0 + t) =\<^sub>t 1] \<sigma>') \<and>
((pre_step \<in> {I6}            \<and> pre_cond = [(rcu_0 + t) =\<^sub>t 1] \<sigma>) \<longrightarrow>  [(rcu_0 + t) =\<^sub>t 0] \<sigma>') \<and>
((pre_step \<in> {I8,I9,I10,I11} \<and> pre_cond = [(rcu_0 + t) =\<^sub>t 1] \<sigma>) \<longrightarrow>  [(rcu_0 + t) =\<^sub>t 1] \<sigma>')"
  apply(simp add:step_def abbr)
  apply(case_tac pre_step, simp_all add:abbr)
  apply (metis d_obs_WrX_set)
  apply (meson d_obs_WrX_set)
  using d_obs_WrX_set apply blast
     defer
  apply (metis d_obs_RdX_other d_obs_RdX_pres)
  apply (metis d_obs_WrX_other)
  apply(clarify)
  using CAS_preserves_d_obs_9 apply blast
  apply(simp add:get_C_val_def)
  by (metis FAAZ_def d_obs_other_representation_2 fst_conv)






lemma shows_WM_local_corr_2:
  " cvd[C, u] \<sigma> \<and> ta\<in> own\<^sub>R ms u \<longrightarrow>  [[C = u]]\<lparr>(rcu_0+ta) = 1\<rparr> \<sigma>  
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>' \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow> cvd[C, u] \<sigma> \<Longrightarrow>
pre_step \<in> {I7} \<Longrightarrow> (rcu_0 + t) \<noteq> C \<Longrightarrow> (rcu_0 + ta) \<noteq> C \<Longrightarrow> t \<noteq> ta
  \<Longrightarrow>  cvd[C, u] \<sigma>' \<and> ta\<in> own\<^sub>R ms' u \<Longrightarrow>  [[C = u]]\<lparr>(rcu_0+ta) = 1\<rparr> \<sigma>'"
  apply (simp_all add:step_def abbr wfs_2_def)
  apply safe 
  by (metis add_left_cancel c_obs_last_WrX_diff_pres wfs_2_def)





lemma testingthisone3:
  "[C =\<^sub>t u] \<sigma> \<Longrightarrow> wfs \<sigma> \<Longrightarrow>
  \<forall> w \<in> visible_writes \<sigma> t C . value \<sigma> w = u"
  using d_obs_p_obs_agree p_obs_def by blast


lemma testingthisone4:
  "[C =\<^sub>t u] \<sigma> \<Longrightarrow> wfs \<sigma> \<Longrightarrow> \<forall> w \<in> visible_writes \<sigma> t C. value \<sigma> w = u \<longrightarrow>
                         d_obs \<sigma> (modView \<sigma> w) y k \<Longrightarrow>
  \<forall> w \<in> visible_writes \<sigma> t C. d_obs \<sigma> (modView \<sigma> w) y k"
  using testingthisone3 by auto


lemma testingthisone5:
  "[C =\<^sub>t u] \<sigma> \<Longrightarrow> wfs \<sigma> \<Longrightarrow> [[C = u]]\<lparr>y = k\<rparr> \<sigma> \<Longrightarrow>
  \<forall> w \<in> visible_writes \<sigma> t C. d_obs \<sigma> (modView \<sigma> w) y k" 
  by (metis c_obs_last_def d_obs_lastWr_visible testingthisone3)

lemma testingthisone6:
  "[C =\<^sub>t u] \<sigma> \<Longrightarrow> wfs \<sigma> \<Longrightarrow> [[C = u]]\<lparr>y = k\<rparr> \<sigma> \<Longrightarrow>
view y = (lastWr \<sigma> y) \<Longrightarrow>
  d_obs \<sigma> view y k"
  by (simp add: c_obs_last_def d_obs_def d_obs_t_def)


lemma testingthisone7:
  "[x =\<^sub>t u] \<sigma> \<Longrightarrow> wfs \<sigma> \<Longrightarrow> [[x = u]]\<lparr>y = k\<rparr> \<sigma> \<Longrightarrow>
(thrView \<sigma> t) y = (lastWr \<sigma> y) \<Longrightarrow>
  d_obs_t \<sigma> t y k" 
  by (simp add: c_obs_last_def d_obs_def d_obs_t_def)




lemma FAAZ_expanded_is_Up:
  "wfs \<sigma> \<Longrightarrow> 
w \<in> visible_writes \<sigma> t x \<Longrightarrow> 
w \<notin> covered \<sigma> \<Longrightarrow> 
valid_fresh_ts \<sigma> w ts' \<Longrightarrow> 
\<sigma>' = update_trans t w u \<sigma> ts'
\<Longrightarrow> cvd[x, u] \<sigma> 
\<Longrightarrow>  OpSem.step t (Update x u u) \<sigma> \<sigma>'"
  apply(simp add:OpSem.step_def)
  by (metis Up_reads_cvd_v eq_fst_iff relating_step_to_update_trans_1)
  
lemma FAAZ_step_is_Up:
  "wfs \<sigma> \<Longrightarrow> 
get_C_val ms \<sigma> t ms' \<sigma>'
\<Longrightarrow> cvd[C, u] \<sigma> 
\<Longrightarrow>  OpSem.step t (Update C u u) \<sigma> \<sigma>'"
  apply(simp add:get_C_val_def FAAZ_def)
  using Up_reads_cvd_v relating_step_to_update_trans_1 by blast




lemma shows_WM_local_corr_supp2:
  " cvd[C, u] \<sigma> \<longrightarrow>  [[C = u]]\<lparr>y = k\<rparr> \<sigma>  
\<Longrightarrow> OpSem.step t (Update C u u') \<sigma> \<sigma>'
\<Longrightarrow> wfs_2 \<sigma> 
\<Longrightarrow> y\<noteq> C
\<Longrightarrow> cvd[C, u] \<sigma> 
\<Longrightarrow> [y =\<^sub>t k] \<sigma>'"
  apply (simp_all add:step_def abbr get_C_val_def FAAZ_def) 
  using c_obs_last_UpRA_d_obs by auto

lemma shows_WM_local_corr_supp3:
  " cvd[C, u] \<sigma> \<and> ta\<in>own\<^sub>R ms u\<longrightarrow>  [[C = u]]\<lparr>(rcu_0+ta) = k\<rparr> \<sigma>  
\<Longrightarrow> OpSem.step t (Update C u u) \<sigma> \<sigma>'
\<Longrightarrow> wfs_2 \<sigma> 
\<Longrightarrow> (rcu_0+ta)\<noteq> C
\<Longrightarrow> (rcu_0+t)\<noteq> C
\<Longrightarrow> t\<noteq>ta
\<Longrightarrow> cvd[C, u] \<sigma> 
\<Longrightarrow> ta\<in>own\<^sub>R ms u
\<Longrightarrow> [(rcu_0+ta) =\<^sub>t k] \<sigma>'"
  apply (simp_all add:step_def abbr get_C_val_def FAAZ_def) 
  using shows_WM_local_corr_supp2 by auto



lemma shows_WM_local_corr_supp4:
  " cvd[C, u] \<sigma> \<and> ta\<in>own\<^sub>R ms u\<longrightarrow>  [[C = u]]\<lparr>(rcu_0+ta) = k\<rparr> \<sigma>  
\<Longrightarrow> get_C_val ms \<sigma> t ms' \<sigma>'
\<Longrightarrow> wfs_2 \<sigma> 
\<Longrightarrow> (rcu_0+ta)\<noteq> C
\<Longrightarrow> (rcu_0+t)\<noteq> C
\<Longrightarrow> t\<noteq>ta
\<Longrightarrow> cvd[C, u] \<sigma> 
\<Longrightarrow> ta\<in>own\<^sub>R ms u
\<Longrightarrow> [(rcu_0+ta) =\<^sub>t k] \<sigma>'"
  apply (simp_all add:step_def abbr get_C_val_def FAAZ_def) 
  using shows_WM_local_corr_supp2 
  by (metis Up_reads_cvd_v relating_step_to_update_trans_1)


lemma shows_WM_local_corr_3:
  " cvd[C, u] \<sigma> \<and> ta\<in>own\<^sub>R ms u\<longrightarrow>  [[C = u]]\<lparr>(rcu_0+ta) = 1\<rparr> \<sigma>  
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>' \<Longrightarrow>
pre_step \<in> {I8}
\<Longrightarrow> wfs_2 \<sigma> 
\<Longrightarrow> (rcu_0+ta)\<noteq> C
\<Longrightarrow> (rcu_0+t)\<noteq> C
\<Longrightarrow> t\<noteq>ta
\<Longrightarrow> cvd[C, u] \<sigma> 
\<Longrightarrow> ta\<in>own\<^sub>R ms u
\<Longrightarrow> [(rcu_0+ta) =\<^sub>t 1] \<sigma>'"
  apply (simp_all add:step_def abbr get_C_val_def FAAZ_def) 
  using shows_WM_local_corr_supp2 
  by (metis Up_reads_cvd_v relating_step_to_update_trans_1)

lemma c_obs_tdash_Rd_pres_c_obs:
"wfs_2 \<sigma> \<Longrightarrow> cvd[x, u] \<sigma> \<Longrightarrow> [[x = u]]\<lparr>y = k\<rparr> \<sigma> \<Longrightarrow> z\<noteq>x \<Longrightarrow>
x\<noteq>y \<Longrightarrow>  \<sigma> [w \<leftarrow> z]\<^sub>t' \<sigma>' \<Longrightarrow> [[x = u]]\<lparr>y = k\<rparr> \<sigma>'" 
  using c_obs_last_RdX_pres 
  apply(metis (full_types))
  done

lemma c_obs_t_Rd_pres_c_obs:
"wfs_2 \<sigma> \<Longrightarrow> cvd[x, u] \<sigma> \<Longrightarrow> [[x = u]]\<lparr>y = k\<rparr> \<sigma> \<Longrightarrow> 
x\<noteq>y \<Longrightarrow>  \<sigma> [w \<leftarrow> y]\<^sub>t' \<sigma>' \<Longrightarrow> [[x = u]]\<lparr>y = k\<rparr> \<sigma>'" 
  using c_obs_last_RdX_pres 
  by (metis)




(***************************************************************)
(***********-----------END OF PREMLIMINARY--------------********)
(***************************************************************)






lemma I1_preserves_pre_block:
  "pre_block ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I1}
\<Longrightarrow> s ms t = None
\<Longrightarrow> pre_block ta ms' \<sigma>'"  
  apply(simp add:step_def enter_rcu_def)
  by(simp add:pre_block_def abbr) 



lemma I2_preserves_pre_block:
  "pre_block ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I2}
\<Longrightarrow> s ms t = None
\<Longrightarrow> pre_block ta ms' \<sigma>'"  
  apply(simp add:step_def enter_rcu_def)
  by(simp add:pre_block_def abbr) 




lemma I3_preserves_pre_block:
  "pre_block ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta 
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I3}
\<Longrightarrow> s ms t = None
\<Longrightarrow> pre_block ta ms' \<sigma>'"  
  apply(simp add:step_def enter_rcu_def)
  by(simp add:pre_block_def abbr) 



lemma I4_preserves_pre_block:
  "pre_block ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I4}
\<Longrightarrow> s ms t = None 
\<Longrightarrow> pre_block ta ms' \<sigma>'"  
  apply(simp add:step_def enter_rcu_def)
  apply(simp add:pre_block_def abbr) 
  using c_obs_last_skip_pres [where x=C and u=l  and \<sigma>=\<sigma> and \<sigma>'=\<sigma>']
  apply clarsimp
  by (metis insert_iff)




lemma I5_preserves_pre_block:
  "pre_block ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I5}
\<Longrightarrow> s ms t = None 
\<Longrightarrow> pre_block ta ms' \<sigma>'"  
  apply(simp add:step_def enter_rcu_def)
  apply(simp add:pre_block_def) apply clarify apply(simp add:abbr)
  apply(case_tac "ta \<in> own\<^sub>R ms u", simp_all) 
  by (metis add_left_imp_eq c_obs_last_WrX_diff_pres cvd_backwards_WrX wfs_2_def)
  






lemma I6_first_preserves_pre_block:
  "pre_block ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta          \<comment> \<open>\<not>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I6}
\<Longrightarrow> s ms t = None
\<Longrightarrow> \<not>repeat ms t
\<Longrightarrow> pre_block ta ms' \<sigma>'"
  apply(simp add:step_def enter_rcu_def)
  apply(simp add:pre_block_def) apply clarify apply(simp add:abbr)
  by (metis add_left_imp_eq c_obs_last_WrX_diff_pres cvd_backwards_WrX wfs_2_def)




lemma I6_second_preserves_pre_block:
  "pre_block ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta         \<comment> \<open>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I6}
\<Longrightarrow> repeat ms t
\<Longrightarrow> pre_block ta ms' \<sigma>'"
  apply(simp add:step_def enter_rcu_def)
  apply(simp add:pre_block_def) apply clarify apply(simp add:abbr)
  apply(case_tac "u = the (s ms t)", simp_all)
  apply (metis add_left_imp_eq c_obs_last_WrX_diff_pres cvd_backwards_WrX wfs_2_def)
  by (metis add_left_imp_eq c_obs_last_WrX_diff_pres cvd_backwards_WrX wfs_2_def)




lemma I7_first_preserves_pre_block:
  "pre_block ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta         \<comment> \<open>\<not>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I7}
\<Longrightarrow> \<not>repeat ms t
\<Longrightarrow> pre_block ta ms' \<sigma>'"
  apply(simp add:step_def enter_rcu_def)
  apply(simp add:pre_block_def) apply clarify apply(simp add:abbr)
  by (metis add_left_imp_eq c_obs_last_WrX_diff_pres cvd_backwards_WrX wfs_2_def)




lemma I7_second_preserves_pre_block:
  "pre_block ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta          \<comment> \<open>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I7}
\<Longrightarrow> repeat ms t 
\<Longrightarrow> pre_block ta ms' \<sigma>'"
  apply(simp add:step_def enter_rcu_def)
  apply(simp add:pre_block_def post_block_def) apply clarify apply(simp add:abbr)
  by (metis add_left_imp_eq c_obs_last_WrX_diff_pres cvd_backwards_WrX wfs_2_def)


(*dealing with ENTERING the critical region*)


lemma FAAZ_returns_l_on_s:
"  book_keeping \<sigma> l t ta
\<Longrightarrow> w \<in> visible_writes \<sigma> t l 
\<Longrightarrow> valid_fresh_ts \<sigma> w ts'
\<Longrightarrow> w \<notin> covered \<sigma> 
\<Longrightarrow> \<sigma>' = update_trans t w l \<sigma> ts'
\<Longrightarrow> cvd[C,l] \<sigma>'"
  apply simp using wfs_2_def
  by (metis avar.simps(3) covered_diff_var_pres cvd_RMW_new_cvd relating_step_to_update_trans_1)


lemma I8_first_preserves_pre_block:
  "pre_block ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta          \<comment> \<open>\<not>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I8} 
\<Longrightarrow> pre_block ta ms' \<sigma>'" 
  apply(simp add:step_def) apply auto
  apply(simp add:get_C_val_def FAAZ_def) 
  apply(simp add:pre_block_def) 
  apply(subgoal_tac "\<sigma> RMW[C,l,l]\<^sub>t \<sigma>'") 
  prefer 2 
  apply (metis FAAZ_def FAAZ_is_RMW_R fst_conv)
  apply clarsimp
  by (metis These_writes_releasing_def c_obs_last_Up_same_loc_pres_col_global cvd_changes_by_Succ_CAS insert_iff last_write_write_on testtttttt wfs_2_def wfs_2_preserved)






lemma I9_preserves_pre_block:
  "pre_block ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta         \<comment> \<open>\<not>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I9}
\<Longrightarrow> pre_block ta ms' \<sigma>'"
  apply(simp add:step_def enter_rcu_def)
  apply(simp add:pre_block_def abbr) apply auto 
  by (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  



lemma I10_preserves_pre_block:
  "pre_block ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta          \<comment> \<open>\<not>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I10}
\<Longrightarrow> the (n ms t) \<noteq> (rcu_0 + ta) \<and> the (n ms t) \<noteq> (rcu_0 + t)
\<Longrightarrow> C \<noteq> the (n ms t)
\<Longrightarrow> pre_block ta ms' \<sigma>'"
  apply(simp add:step_def abbr)
  using c_obs_last_WrX_diff_pres [where x = C and u=l] 
  apply(simp add:pre_block_def)
  by (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX wfs_2_def)




(*dealing with CAS, has 2 possible outcomes: (pre_block) if fail and (post_block) if succ*)


lemma succ_CAS_I11_pres_post:
" pre_block ta ms \<sigma>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>' \<Longrightarrow>
pre_step \<in> {I11}
\<Longrightarrow> book_keeping \<sigma> l t ta
\<Longrightarrow> l = the(s ms t)
\<Longrightarrow> CAS_succ ms' t 
\<Longrightarrow> post_block t ta ms' \<sigma>' "
  apply(simp add:step_def cas_step_rcu_def post_block_def)
  apply(simp add:pre_block_def wfs_2_def)
  apply clarify apply(simp add:CAS_def) apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  by (metis relating_step_to_update_trans_1 shows_WM_local_corr_supp2 wfs_2_def)


lemma fail_CAS_I11_pres_in_block:
" pre_block ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>' 
\<Longrightarrow> pre_step \<in> {I11}
\<Longrightarrow> \<not>CAS_succ ms' t 
\<Longrightarrow> pre_block ta ms' \<sigma>' "
  apply(simp add:step_def cas_step_rcu_def pre_block_def)
  apply clarify apply(simp add:CAS_def)
  apply(subgoal_tac "value \<sigma> (a, b) \<noteq> the (s ms t)", simp_all add:wfs_2_def) prefer 2
  apply force
  apply(subgoal_tac "\<sigma> [l \<leftarrow> C]\<^sub>t \<sigma>'")
  apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply(simp add:OpSem.step_def read_trans_def RdX_def)
  by (smt (z3) CollectD covered_v_def visible_writes_def)
  



lemma CAS_I11_pres_preblock_or_post:
" pre_block ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>' 
\<Longrightarrow> pre_step \<in> {I11}
\<Longrightarrow> pre_block ta ms' \<sigma>' \<or> post_block t ta ms' \<sigma>'"
  apply(case_tac "CAS_succ ms' t")
  apply(subgoal_tac "post_block t ta ms' \<sigma>'")
  apply blast 
  apply(case_tac "l = the(s ms t) ") 
  using succ_CAS_I11_pres_post
  apply blast 
  apply(subgoal_tac "\<not>CAS_succ ms' t ", simp_all)
  apply(simp add:step_def cas_step_rcu_def CAS_def)
  apply clarify
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (simp add: covered_v_def visible_writes_def)
  using fail_CAS_I11_pres_in_block book_keeping_def
  by blast



lemma cas_res_pres_post_block:
" post_block t ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>' 
\<Longrightarrow> pre_step = cas_res
\<Longrightarrow> CAS_succ ms' t 
\<Longrightarrow> post_block t ta ms' \<sigma>' "
  apply(simp add:step_def cas_step_rcu_def post_block_def)
  apply clarify by(case_tac "CAS_succ ms t", simp_all add:abbr)


lemma fail_cas_res_pres_in_block:
" pre_block ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>' 
\<Longrightarrow> pre_step = cas_res
\<Longrightarrow> \<not>CAS_succ ms' t 
\<Longrightarrow> pre_block ta ms' \<sigma>' "
  apply(simp add:step_def cas_step_rcu_def pre_block_def)
  apply clarify by(case_tac "CAS_succ ms t", simp_all add:abbr)



lemma succ_cas_res_pres_preblock_or_post:
" (\<not>CAS_succ ms t \<longrightarrow> pre_block ta ms \<sigma> )
 \<and>  ( CAS_succ ms t \<longrightarrow> post_block t ta ms \<sigma> )
\<Longrightarrow> book_keeping \<sigma> l t ta
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>' 
\<Longrightarrow> pre_step = cas_res
\<Longrightarrow> post_block t ta ms' \<sigma>' \<or> pre_block ta ms' \<sigma>'"
  apply(case_tac "CAS_succ ms t", simp_all) 
  using cas_res_pres_post_block [where t=t and ta=ta and ms=ms 
                          and \<sigma>=\<sigma> and pre_step=pre_step and ps=ps
                          and ms'=ms' and ps'=ps' and \<sigma>'=\<sigma>' and l=l]
  apply(subgoal_tac "CAS_succ ms' t", simp_all)
  apply(simp add:step_def abbr)
  apply(thin_tac "(post_block t ta ms \<sigma> \<Longrightarrow> CAS_succ ms' t \<Longrightarrow> post_block t ta ms' \<sigma>')")
  apply(subgoal_tac "pre_block ta ms' \<sigma>'") 
  apply fastforce
  using fail_cas_res_pres_in_block [where t=t and ta=ta and ms=ms
                          and \<sigma>=\<sigma> and pre_step=pre_step and ps=ps
                          and ms'=ms' and ps'=ps' and \<sigma>'=\<sigma>' and l=l]
  apply(subgoal_tac "\<not>CAS_succ ms' t", simp_all)
  by(simp add:step_def abbr)
  



lemma I12_preserves_post_block:
  "post_block t ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t ta          \<comment> \<open>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I12}
\<Longrightarrow> post_block t ta ms' \<sigma>'"
  apply(simp add:step_def enter_rcu_def)
  apply(simp add:pre_block_def post_block_def)
  apply(case_tac "ta \<in> own\<^sub>R ms (the (s ms t))", simp_all)
  apply(subgoal_tac " ta \<in> own\<^sub>R ms' (the (s ms t))", simp_all)  
  apply (meson abbr(10) add_left_imp_eq d_obs_WrX_other wfs_2_def)
  using update_pc_def giveup_readandwrite_ownership_def by auto

































(*weak memory invariant during reclamation/synchronisation*)


lemma S3_corr_val_preserves_post_block:
  "post_block t ta ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> pre_step \<in> {S3}
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> ta\<noteq>t  
\<Longrightarrow> post_block t ta ms' \<sigma>'"
  apply(case_tac "ta = (CTRsync\<^sub>1 ms t)")
  apply(simp add:step_def load_rcu_to_r_def post_block_def wfs_2_def)
  apply(case_tac "CTRsync\<^sub>1 ms t \<in> own\<^sub>R ms' (the (s ms' t))", simp_all)
  apply clarify apply auto
  apply (meson d_obs_RdX_pres)
  apply(simp add:step_def load_rcu_to_r_def post_block_def wfs_2_def)
  apply clarify apply auto
  by (meson add_left_imp_eq d_obs_RdX_other)


lemma S3_corr_val_preserves_post_sc:
  "post_block t ta ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> pre_step \<in> {S3}
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> ta\<noteq>t  
\<Longrightarrow> r ms t ta = 0
\<Longrightarrow> CTRsync\<^sub>1 ms t = ta
\<Longrightarrow> ta\<in> own\<^sub>R ms (the (s ms t)) \<longrightarrow> r ms' t ta = 1"
  apply(simp add:step_def load_rcu_to_r_def post_block_def wfs_2_def)
  apply(case_tac "CTRsync\<^sub>1 ms t \<in> own\<^sub>R ms' (the (s ms' t))", simp_all)
  apply clarify apply auto
  by (meson d_obs_read_value)


(*do the same for S6*)



lemma S6_corr_val_preserves_post_sc:
  "r ms t t' = 1 \<longrightarrow> post_block t t' ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> pre_step \<in> {S6}
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> r ms' t t' = 1 \<longrightarrow> post_block t t' ms' \<sigma>'"
  apply(simp add:step_def load_rcu_to_r_def post_block_def wfs_2_def rcu_temp_copy_def)
  apply clarify apply auto 
  by (metis d_obs_RdX_other d_obs_RdX_pres)
  

lemma S6_corr_val_preserves_post_sc_2:
  "r ms t ta = 1 \<longrightarrow> post_block t ta ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> pre_step \<in> {S6}
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> r ms t ta = 1 
\<Longrightarrow> post_block t ta ms' \<sigma>'"
  apply(subgoal_tac "r ms' t ta = 1") prefer 2
  apply(simp add:step_def rcu_temp_copy_def) apply auto
  by (metis One_nat_def S6_corr_val_preserves_post_sc insertI1)


lemma S6_corr_val_preserves_post_sc_3:
  "r ms t ta = 1 \<longrightarrow> post_block t ta ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> pre_step \<in> {S6}
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> r ms t ta = 1 
\<Longrightarrow> ta \<in> own\<^sub>R ms (the (s ms t))
\<Longrightarrow> [(rcu_0+ta) =\<^sub>t 1] \<sigma>'"
  apply (simp add:post_block_def) 
  apply(subgoal_tac "r ms' t ta = 1") prefer 2 apply(simp add:step_def rcu_temp_copy_def) apply auto
  apply(subgoal_tac "ta \<in> own\<^sub>R ms' (the (s ms' t))") prefer 2 apply(simp add:step_def rcu_temp_copy_def) apply auto
  by (metis One_nat_def S6_corr_val_preserves_post_sc insertI1 post_block_def)
  

lemma S6_corr_val_preserves_post_sc_4:
  "r ms t ta = 1 \<longrightarrow> post_block t ta ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> pre_step \<in> {S6}
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> r ms t ta = 1  
\<Longrightarrow> ta = CTRsync\<^sub>2 ms t
\<Longrightarrow> ta \<in> own\<^sub>R ms (the (s ms t)) \<longrightarrow> reg ms' t = 1"
  apply simp
  apply(case_tac "ta \<in> own\<^sub>R ms (the (s ms t))")
  apply(simp add:step_def rcu_temp_copy_def post_block_def wfs_2_def)
  apply(subgoal_tac "[(rcu_0+ta) =\<^sub>t 1] \<sigma>", simp_all add:d_obs_t_def OpSem.step_def)
  apply clarify
  apply(case_tac "RdX (rcu_0 + CTRsync\<^sub>2 ms t) v", simp_all) 
  apply (metis RdX_def action.inject(1) d_obs_p_obs_agree d_obs_t_def p_obs_def)
  apply (metis RdX_def action.distinct(1))
  by (metis RdX_def action.simps(7))

(*the S6 and S3 dependencies MIGHT need revisiting*)








(*-------------------------------------------------------------*)
(*-------------------------------------------------------------*)
(*-----------------RCU free(pop(det)) stuff--------------------*)
(*-------------------------------------------------------------*)
(*-------------------------------------------------------------*)


lemma sigma_obs_preserved_forall:
 "sigma_obs ms \<sigma> t' \<Longrightarrow>
  con_assms ms ps \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow> 
  These_writes_releasing \<sigma> C \<Longrightarrow> 
  t' < T_max \<and> t < T_max \<Longrightarrow>
  cvd[C, l] \<sigma> \<Longrightarrow>
  sigma_obs ms' \<sigma>' t'"
  apply(case_tac "t = t'", simp_all)
  apply(simp add:step_def abbr sigma_obs_def)
  apply(case_tac "pc ms t'", simp_all add:abbr)
  apply auto[1]
  apply auto[1]
  apply(simp add:con_assms_def rcu_locs_differ_def wfs_2_def)
  apply (meson d_obs_WrX_set)
  apply auto[1]
  using d_obs_WrX_set wfs_2_def apply blast
  using d_obs_WrX_set wfs_2_def apply blast
  using d_obs_WrX_set wfs_2_def apply blast
  using d_obs_WrX_set wfs_2_def apply blast
  apply(simp add:get_C_val_def FAAZ_def) apply auto[1] 
  using con_assms_def d_obs_other_representation_2 reservations_differ_def wfs_2_def apply blast
  apply auto[1]
  apply (metis RdX_def d_obs_Rd_pres isRd.simps(1) wfs_2_def)
  apply (metis con_assms_def d_obs_WrX_other rcu_locs_differ_def wfs_2_def)
  apply(simp add:cas_step_rcu_def)
  apply auto[1] 
  apply (metis CAS_def Failed_CAS_preserves_d_obs_supporting_for_later con_assms_def prod.inject reservations_differ_def)
  apply (metis CAS_def con_assms_def d_obs_other_representation_2 prod.inject reservations_differ_def wfs_2_def)
  apply (metis CAS_def Failed_CAS_preserves_d_obs_supporting_for_later con_assms_def d_obs_other_representation_2 fst_conv reservations_differ_def wfs_2_def)
  using d_obs_WrX_set wfs_2_def apply blast
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply auto[1]
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t' \<noteq> []", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t' < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t' = t'", simp_all add:abbr)
  apply auto[1]
  apply (metis RdX_def d_obs_Rd_pres isRd.simps(1) wfs_2_def)
  apply(case_tac "CTRsync\<^sub>2 ms t' < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t' = t'", simp_all add:abbr)
  apply(case_tac "r ms t' (CTRsync\<^sub>2 ms t') = 0", simp_all add:abbr)
  apply auto[1]
  apply (metis RdX_def d_obs_Rd_pres isRd.simps(1) wfs_2_def)
  apply(case_tac "reg ms t' = Suc 0", simp_all add:abbr)
  apply(simp add:step_def abbr sigma_obs_def)
  apply(subgoal_tac "pc ms t' = pc ms' t'") prefer 2 
  apply(case_tac "pc ms t", simp_all add:abbr get_C_val_def FAAZ_def cas_step_rcu_def)
  apply auto
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply(case_tac "reg ms t = Suc 0", simp_all add:abbr)
  apply(case_tac "pc ms t' \<in> {I6, I8, I9, I10, I11, I12, cas_res}", simp_all)
  apply(subgoal_tac "[(rcu_0 + t') =\<^sub>t' 1] \<sigma>", simp_all) prefer 2
  apply force
  apply(subgoal_tac "[(rcu_0 + t') =\<^sub>t' 1] \<sigma>'", simp_all)
  apply (metis (no_types, lifting) One_nat_def PC.simps(762) PC.simps(764) PC.simps(765) PC.simps(766) PC.simps(767) PC.simps(768) PC.simps(771))
  apply(thin_tac "case pc ms' t' of I6 \<Rightarrow> [(rcu_0 + t') =\<^sub>t' 1] \<sigma> | I8 \<Rightarrow> [(rcu_0 + t') =\<^sub>t' 1] \<sigma>
       | I9 \<Rightarrow> [(rcu_0 + t') =\<^sub>t' 1] \<sigma> | I10 \<Rightarrow> [(rcu_0 + t') =\<^sub>t' 1] \<sigma>
       | I11 \<Rightarrow> [(rcu_0 + t') =\<^sub>t' 1] \<sigma> | I12 \<Rightarrow> [(rcu_0 + t') =\<^sub>t' 1] \<sigma>
       | cas_res \<Rightarrow> [(rcu_0 + t') =\<^sub>t' 1] \<sigma> | _ \<Rightarrow> [(rcu_0 + t') =\<^sub>t' 0] \<sigma>")
  apply(case_tac "pc ms t", simp_all add:abbr)
  apply (metis add_left_imp_eq dobs_WrX_pres)
  apply (metis add_left_imp_eq dobs_WrX_pres)
  apply (metis add_left_imp_eq dobs_WrX_pres)
  apply(simp add:get_C_val_def FAAZ_def con_assms_def rcu_locs_differ_def)
  apply (metis dobs_RMW_pres relating_step_to_update_trans_1)
  apply (metis dobs_RdX_pres)
  apply (metis con_assms_def dobs_WrX_pres rcu_locs_differ_def)
  apply(simp add:cas_step_rcu_def CAS_def)
  apply clarify
  apply(case_tac "y", simp_all)
  apply(subgoal_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (metis con_assms_def dobs_RMW_pres relating_step_to_update_trans_1 reservations_differ_def)
  apply (metis prod.inject)
  apply (metis Failed_CAS_preserves_d_obs_supporting_for_later Pair_inject con_assms_def reservations_differ_def)
  apply (metis add_left_imp_eq dobs_WrX_pres)
  apply presburger
  apply presburger
  apply presburger
  apply presburger
  apply (metis dobs_RdX_pres)
  apply presburger
  apply presburger
  apply (metis dobs_RdX_pres)
  apply presburger
  apply(subgoal_tac "[(rcu_0 + t') =\<^sub>t' 0] \<sigma>") prefer 2
  apply(case_tac "pc ms' t'", simp_all)
  apply(subgoal_tac "[(rcu_0 + t') =\<^sub>t' 0] \<sigma>'")
  apply(case_tac "pc ms' t'", simp_all)
  apply(thin_tac "case pc ms' t' of I6 \<Rightarrow> [(rcu_0 + t') =\<^sub>t' 1] \<sigma> | I8 \<Rightarrow> [(rcu_0 + t') =\<^sub>t' 1] \<sigma>
    | I9 \<Rightarrow> [(rcu_0 + t') =\<^sub>t' 1] \<sigma> | I10 \<Rightarrow> [(rcu_0 + t') =\<^sub>t' 1] \<sigma>
    | I11 \<Rightarrow> [(rcu_0 + t') =\<^sub>t' 1] \<sigma> | I12 \<Rightarrow> [(rcu_0 + t') =\<^sub>t' 1] \<sigma>
    | cas_res \<Rightarrow> [(rcu_0 + t') =\<^sub>t' 1] \<sigma> | _ \<Rightarrow> [(rcu_0 + t') =\<^sub>t' 0] \<sigma>")
  apply(case_tac "pc ms t", simp_all add:abbr)
  apply (metis add_left_imp_eq dobs_WrX_pres)
  apply (metis add_left_imp_eq dobs_WrX_pres)
  apply (metis add_left_imp_eq dobs_WrX_pres)
  apply(simp add:get_C_val_def FAAZ_def con_assms_def rcu_locs_differ_def)
  apply (metis dobs_RMW_pres relating_step_to_update_trans_1)
  apply (metis dobs_RdX_pres)
  apply (metis con_assms_def dobs_WrX_pres rcu_locs_differ_def)
  apply(simp add:cas_step_rcu_def CAS_def)
  apply clarify
  apply(case_tac "y", simp_all)
  apply(subgoal_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (metis con_assms_def dobs_RMW_pres relating_step_to_update_trans_1 reservations_differ_def)
  apply (metis prod.inject)
  apply (metis Failed_CAS_preserves_d_obs_supporting_for_later Pair_inject con_assms_def reservations_differ_def)
  apply (metis add_left_imp_eq dobs_WrX_pres)
  apply presburger
  apply presburger
  apply presburger
  apply presburger
  apply (metis dobs_RdX_pres)
  apply presburger
  apply presburger
  apply (metis dobs_RdX_pres)
  by presburger







lemma covered_exists_after_step:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow>
  book_keeping \<sigma> l t t' \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  \<exists>u'. cvd[C,u'] \<sigma>'  "    
  apply(simp add:step_def)
  apply(case_tac "pc ms t", simp_all add:abbr wfs_2_def)
  apply blast+
  using cvd_WrX_other_var_pres apply blast
  using cvd_WrX_other_var_pres apply blast
  using cvd_WrX_other_var_pres apply blast
  using FAAZ_step_is_Up cvd_RMW_new_cvd apply blast
  using cvd_Rdx_pres apply blast
  apply (metis con_assms_def cvd_WrX_other_var_pres rcu_locs_differ_def)
  apply(simp add:cas_step_rcu_def) apply clarify
  apply(case_tac "y", simp_all add:CAS_def)
  apply(subgoal_tac "\<sigma> RMW[C, l, the(n ms t)]\<^sub>t \<sigma>'")
  using cvd_RMW_new_cvd apply blast
  apply (smt (z3) CollectD covered_v_def prod.inject relating_step_to_update_trans_1 visible_writes_def)
  apply (metis CAS_def Pair_inject cvd_pres_by_CAS_unfold_pt1 fst_conv wfs_2_def)
  using cvd_WrX_other_var_pres apply blast
  apply blast
  apply blast
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply metis
  apply metis
  apply blast
  apply blast
  apply metis
  using cvd_Rdx_pres apply blast
  apply metis
  apply metis
  using cvd_Rdx_pres apply blast
  by metis
  












lemma showing_block_cond_pres_local:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow> 
  book_keeping \<sigma> l t t' \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  t' < T_max \<Longrightarrow>
  cvd[C,u] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  block_cond t t' ms \<sigma> \<Longrightarrow>
  det_block t ms \<sigma>  \<Longrightarrow>                    
  block_cond t t' ms' \<sigma>'" 
  apply(subgoal_tac "\<exists>u'. cvd[C,u'] \<sigma>'") prefer 2 
  using covered_exists_after_step apply blast apply clarify
  apply(unfold block_cond_def)
  apply(case_tac "pc ms t = I1") 
  apply(subgoal_tac "pc ms' t = I2") prefer 2 apply(simp add:step_def abbr)
  apply(subgoal_tac "s ms t = None") prefer 2 apply(simp add:preCond_def)
  using I1_preserves_pre_block  apply simp apply blast
  apply(case_tac "pc ms t = I2") 
  apply(subgoal_tac "pc ms' t = I3") prefer 2 apply(simp add:step_def abbr)
  apply(subgoal_tac "s ms t = None") prefer 2 apply(simp add:preCond_def)
  using I2_preserves_pre_block  apply simp apply blast
  apply(case_tac "pc ms t = I3") 
  apply(subgoal_tac "pc ms' t = I4") prefer 2 apply(simp add:step_def abbr)
  apply(subgoal_tac "s ms t = None") prefer 2 apply(simp add:preCond_def)
  using I3_preserves_pre_block  apply simp apply blast
  apply(case_tac "pc ms t = I4") 
  apply(subgoal_tac "pc ms' t = I5") prefer 2 apply(simp add:step_def abbr) apply auto[1]
  apply(subgoal_tac "s ms t = None") prefer 2 apply(simp add:preCond_def)
  using I4_preserves_pre_block  apply simp apply blast
  apply(case_tac "pc ms t = I5") 
  apply(subgoal_tac "pc ms' t = I6") prefer 2 apply(simp add:step_def abbr)
  apply(subgoal_tac "s ms t = None") prefer 2 apply(simp add:preCond_def)
  using I5_preserves_pre_block  apply simp apply blast
  apply(case_tac "pc ms t = I6")
  apply(subgoal_tac "pc ms' t = I7") prefer 2 apply(simp add:step_def abbr) apply auto[1]
  apply(case_tac "\<not>repeat ms t")
  apply(subgoal_tac "s ms t = None") prefer 2 apply(simp add:preCond_def)
  using I6_first_preserves_pre_block  apply simp apply blast
  apply (metis I6_second_preserves_pre_block PC.simps(762) PC.simps(763) insert_iff)
  apply(case_tac "pc ms t = I7")
  apply(subgoal_tac "pc ms' t = I8") prefer 2 apply(simp add:step_def abbr) apply auto[1]
  using I7_first_preserves_pre_block
  apply (metis I7_second_preserves_pre_block book_keeping_def insert_iff)
  apply(case_tac "pc ms t = I8")
  apply(subgoal_tac "pc ms' t = I9") prefer 2 apply(simp add:step_def abbr get_C_val_def) apply auto[1]
  using I8_first_preserves_pre_block 
  apply (metis PC.simps(764) PC.simps(765) insert_iff)
  apply(case_tac "pc ms t = I9")
  apply(subgoal_tac "pc ms' t = I10") prefer 2 apply(simp add:step_def abbr get_C_val_def) apply auto[1]
  using I9_preserves_pre_block 
  apply (metis PC.simps(765) PC.simps(766) insert_iff)
  apply(case_tac "pc ms t = I10")
  apply(subgoal_tac "pc ms' t = I11") prefer 2 apply(simp add:step_def abbr get_C_val_def) apply auto[1]
  apply(simp add:con_assms_def)
  apply(subgoal_tac "C \<noteq> the (n ms t)", simp_all)
  apply (smt (verit, ccfv_SIG) I10_preserves_pre_block book_keeping_def insert_iff rcu_locs_differ_def)
  apply(simp add:rcu_locs_differ_def)
  apply blast
  apply(case_tac "pc ms t = I11")
  apply(subgoal_tac "pc ms' t = cas_res") prefer 2 apply(simp add:step_def cas_step_rcu_def) apply auto[1]
  apply(case_tac "CAS_succ ms' t")
  apply(subgoal_tac "l = the(s ms t)")
  using succ_CAS_I11_pres_post 
  apply (metis PC.simps(767) PC.simps(771) book_keeping_def insert_iff)
  apply(simp add:step_def cas_step_rcu_def CAS_def)
  apply clarify
  apply(case_tac "y", simp_all)
  apply (smt (z3) CollectD covered_v_def prod.inject visible_writes_def)
  apply (metis book_keeping_def fail_CAS_I11_pres_in_block insertI1)
  apply(case_tac "pc ms t = cas_res")
  apply(case_tac "CAS_succ ms t")
  apply(subgoal_tac "pc ms' t = I12") prefer 2 apply(simp add:step_def abbr) apply auto[1]
  apply(subgoal_tac "book_keeping \<sigma> l t t'") prefer 2 
  using book_keeping_def apply presburger
  apply(subgoal_tac "CAS_succ ms' t", simp_all) prefer 2 apply(simp add:step_def abbr)
  using cas_res_pres_post_block
  using book_keeping_def apply blast 
  apply(subgoal_tac "pc ms' t = I6") prefer 2 apply(simp add:step_def abbr) apply auto[1]
  apply(subgoal_tac "book_keeping \<sigma> l t t'") prefer 2 
  using book_keeping_def apply presburger
  apply(subgoal_tac "\<not>CAS_succ ms' t", simp_all) prefer 2 apply(simp add:step_def abbr)
  using fail_cas_res_pres_in_block
  using book_keeping_def  apply blast
  apply(case_tac "pc ms t = I12")
  apply(subgoal_tac "pc ms' t = R1") prefer 2 apply(simp add:step_def abbr) apply auto[1]
  using I12_preserves_post_block book_keeping_def apply blast
  apply(simp add:step_def)
  apply(case_tac "pc ms t", simp_all)
  apply(simp_all add:abbr step_def block_cond_def)
  apply auto[1]
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t = []", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all add:abbr)
  apply auto[1]
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply auto[1]
  by(case_tac "reg ms t = Suc 0", simp_all add:abbr)




lemma showing_block_cond_pres_local_2:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow> 
  book_keeping \<sigma> l t t' \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  t' < T_max \<Longrightarrow>
  cvd[C,u] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  allocated_addresses ms ps \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  \<forall>t'a. t'a<T_max \<and> t'a\<noteq>t \<longrightarrow> block_cond t t'a ms \<sigma> \<Longrightarrow>
  det_block t ms \<sigma>  \<Longrightarrow>                    
  \<forall>t'a. t'a<T_max \<and> t'a\<noteq>t  \<longrightarrow> block_cond t t'a ms' \<sigma>' " 
  apply safe
  by (metis book_keeping_def con_assms_def reservations_differ_def showing_block_cond_pres_local)
  




lemma I1_preserves_pre_block_global_pre:
  "block_cond t' t'a ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' t'a
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I1}
\<Longrightarrow> block_cond t' t'a ms' \<sigma>' "  
  apply(simp add:step_def)
  apply(simp add:abbr pre_block_def)
  apply(simp add:block_cond_def)
  apply(case_tac "pc ms t'", simp_all)
  apply(simp_all add:pre_block_def abbr)
  by(simp_all add:post_block_def abbr)


lemma I2_preserves_pre_block_global_pre:
  "block_cond t' t'a ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' t'a
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I2}
\<Longrightarrow> block_cond t' t'a ms' \<sigma>' "  
  apply(simp add:step_def)
  apply(simp add:abbr pre_block_def)
  apply(simp add:block_cond_def)
  apply(case_tac "pc ms t'", simp_all)
  apply(simp_all add:pre_block_def abbr)
  by(simp_all add:post_block_def abbr)

lemma I3_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I3}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' "  
  apply(simp add:step_def)
  apply(simp add:abbr pre_block_def)
  apply(simp add:block_cond_def)
  apply(case_tac "pc ms t'", simp_all)
  apply(simp_all add:pre_block_def abbr)
  by(simp_all add:post_block_def abbr)


lemma I4_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> full_inv ms ps \<sigma>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> preCond ms ps (pc ms ta) ta
\<Longrightarrow> preCond ms ps (pre_step) t
\<Longrightarrow> pre_step \<in> {I4}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' "  
  apply(simp add:step_def full_inv_def)
  apply(simp add:abbr pre_block_def)
  apply(simp add:block_cond_def)
  apply(subgoal_tac "pc ms t' = pc ms' t'") prefer 2 apply auto[1]
  apply(case_tac "pc ms t'", simp_all) 
  apply(simp_all add:pre_block_def abbr)
  apply(simp_all add:post_block_def abbr)
  apply auto[1]
  apply (metis isfree_addr_def observation_inv_sig_def)
  apply auto[1]
  apply (metis isfree_addr_def observation_inv_sig_def)
  apply auto[1]
  apply (metis isfree_addr_def observation_inv_sig_def)
  apply auto[1]
  apply (metis isfree_addr_def observation_inv_sig_def)
  apply auto[1]
  apply (metis isfree_addr_def observation_inv_sig_def)
  apply auto[1]
  apply (metis isfree_addr_def observation_inv_sig_def)
  apply auto[1]
  apply (metis isfree_addr_def observation_inv_sig_def)
  apply auto[1]
  apply (metis isfree_addr_def observation_inv_sig_def)
  apply auto[1]
  apply (metis isfree_addr_def observation_inv_sig_def)
  apply auto[1]
  apply (metis isfree_addr_def observation_inv_sig_def)
  apply auto[1]
  apply (metis isfree_addr_def observation_inv_sig_def)
  apply auto[1]
  apply(case_tac "ta = t", simp_all) prefer 2
  apply (metis insert_iff)
  apply(subgoal_tac "t'<T_max") 
  apply(subgoal_tac "t' \<in> own\<^sub>R ms ( the( s ms t'))")
  apply(subgoal_tac " s ms t' \<noteq>None")
  apply (metis allocated_addresses_def allocated_s_addr_def isfree_addr_def option.collapse)
  apply(simp add:preCond_def)
  apply(simp add:preCond_def)
  apply (meson Rcap_def insertCI)
  apply blast
  apply(case_tac "CAS_succ ms' t' ", simp_all)
  apply(case_tac "ta = t", simp_all) 
  apply(simp add:preCond_def) apply clarsimp
  apply (smt (z3) Rcap_def allocated_addresses_def allocated_s_addr_def insert_iff isfree_addr_def)
  apply clarsimp
  apply(subgoal_tac "\<forall>i. i\<noteq>loc \<longrightarrow> own\<^sub>R ms (i) = own\<^sub>R ms' (i)")
  apply (metis insert_iff)
  apply (metis insert_iff)
  apply(case_tac "ta = t", simp_all) 
  apply(simp add:preCond_def) apply clarsimp
  apply (metis isfree_addr_def observation_inv_sig_def)
  apply clarsimp
  apply (metis insert_iff)      
  apply clarsimp
  apply(case_tac "ta = t", simp_all) prefer 2
  apply (metis insert_iff)
  apply(subgoal_tac "t'<T_max") 
  apply(subgoal_tac "t' \<in> own\<^sub>R ms ( the( s ms t'))")
  apply(subgoal_tac " s ms t' \<noteq>None")
  apply (metis allocated_addresses_def allocated_s_addr_def isfree_addr_def option.collapse)
  apply(simp add:preCond_def)
  apply(simp add:preCond_def)
  apply (meson Rcap_def insertCI)
  by linarith







lemma I8_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> full_inv ms ps \<sigma>
\<Longrightarrow> step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> preCond ms ps (pc ms ta) ta
\<Longrightarrow> preCond ms ps (pc ms t) t
\<Longrightarrow> sigma_obs ms \<sigma> t
\<Longrightarrow> pc ms t = I8
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(case_tac "t \<noteq> ta", simp_all add:full_inv_def)
   apply(unfold block_cond_def)
   apply(simp add:step_def)
   apply(subgoal_tac "pc ms' t = I9", simp_all add:step_def get_C_val_def)
   prefer 2 apply auto[1]
   apply(subgoal_tac "pc ms t' = pc ms' t'", simp_all add:get_C_val_def) prefer 2
   apply auto[1]
   apply(case_tac "pc ms t'", simp_all)
   apply(simp add:pre_block_def FAAZ_def)
   apply(simp add:preCond_def)
   apply clarify
   apply auto[1]
   apply(subgoal_tac "l = value \<sigma> (a, b)") prefer 2
   apply (simp add: covered_v_def visible_writes_def)
   apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2
   apply (meson cvd_changes_by_Succ_CAS relating_step_to_update_trans_1)
   apply(case_tac "u \<noteq> value \<sigma> (a, b)", simp_all)
   apply (meson relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply (metis c_obs_last_Up_same_loc_pres_col_global c_obs_last_def relating_step_to_update_trans_1 x_has_lastWr)
   apply(subgoal_tac "l = value \<sigma> (a, b)") prefer 2
   apply (simp add: covered_v_def visible_writes_def)
   apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2
   apply (meson cvd_changes_by_Succ_CAS relating_step_to_update_trans_1)
   apply(case_tac "u \<noteq> value \<sigma> (a, b)", simp_all)
   apply (meson relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply (metis c_obs_last_Up_same_loc_pres_col_global c_obs_last_def relating_step_to_update_trans_1 x_has_lastWr)
   apply(simp add:pre_block_def FAAZ_def)
   apply(simp add:preCond_def)
   apply clarify
   apply auto[1]
   apply(subgoal_tac "l = value \<sigma> (a, b)") prefer 2
   apply (simp add: covered_v_def visible_writes_def)
   apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2
   apply (meson cvd_changes_by_Succ_CAS relating_step_to_update_trans_1)
   apply(case_tac "u \<noteq> value \<sigma> (a, b)", simp_all)
   apply (meson relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply (metis c_obs_last_Up_same_loc_pres_col_global c_obs_last_def relating_step_to_update_trans_1 x_has_lastWr)
   apply(subgoal_tac "l = value \<sigma> (a, b)") prefer 2
   apply (simp add: covered_v_def visible_writes_def)
   apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2
   apply (meson cvd_changes_by_Succ_CAS relating_step_to_update_trans_1)
   apply(case_tac "u \<noteq> value \<sigma> (a, b)", simp_all)
   apply (meson relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply (metis c_obs_last_Up_same_loc_pres_col_global c_obs_last_def relating_step_to_update_trans_1 x_has_lastWr)
   apply(simp add:pre_block_def FAAZ_def)
   apply(simp add:preCond_def)
   apply clarify
   apply auto[1]
   apply(subgoal_tac "l = value \<sigma> (a, b)") prefer 2
   apply (simp add: covered_v_def visible_writes_def)
   apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2
   apply (meson cvd_changes_by_Succ_CAS relating_step_to_update_trans_1)
   apply(case_tac "u \<noteq> value \<sigma> (a, b)", simp_all)
   apply (meson relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply (metis c_obs_last_Up_same_loc_pres_col_global c_obs_last_def relating_step_to_update_trans_1 x_has_lastWr)
   apply(subgoal_tac "l = value \<sigma> (a, b)") prefer 2
   apply (simp add: covered_v_def visible_writes_def)
   apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2
   apply (meson cvd_changes_by_Succ_CAS relating_step_to_update_trans_1)
   apply(case_tac "u \<noteq> value \<sigma> (a, b)", simp_all)
   apply (meson relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply (metis c_obs_last_Up_same_loc_pres_col_global c_obs_last_def relating_step_to_update_trans_1 x_has_lastWr)
   apply(simp add:pre_block_def FAAZ_def)
   apply(simp add:preCond_def)
   apply clarify
   apply auto[1]
   apply(case_tac "u \<noteq> value \<sigma> (a, b)", simp_all)
   apply (metis (no_types, opaque_lifting) Up_reads_cvd_v cvd_changes_by_Succ_CAS relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply (metis These_writes_releasing_def Up_reads_cvd_v c_obs_last_Up_same_loc_pres_col_global covered_v_def relating_step_to_update_trans_1)
   apply(subgoal_tac "l = value \<sigma> (a, b)") prefer 2
   apply (simp add: covered_v_def visible_writes_def)
   apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2
   apply (meson cvd_changes_by_Succ_CAS relating_step_to_update_trans_1)
   apply(case_tac "u \<noteq> value \<sigma> (a, b)", simp_all)
   apply (meson relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply (metis c_obs_last_Up_same_loc_pres_col_global c_obs_last_def relating_step_to_update_trans_1 x_has_lastWr)
   apply(simp add:pre_block_def FAAZ_def)
   apply(simp add:preCond_def)
   apply clarify
   apply(case_tac "u \<noteq> value \<sigma> (a, b)", simp_all)
   apply (metis (no_types, opaque_lifting) Up_reads_cvd_v cvd_changes_by_Succ_CAS relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply (metis These_writes_releasing_def Up_reads_cvd_v c_obs_last_Up_same_loc_pres_col_global covered_v_def relating_step_to_update_trans_1)
   apply(simp add:pre_block_def FAAZ_def)
   apply(simp add:preCond_def)
   apply clarify
   apply(subgoal_tac "l = value \<sigma> (a, b)") prefer 2
   apply (simp add: covered_v_def visible_writes_def)
   apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2
   apply (meson cvd_changes_by_Succ_CAS relating_step_to_update_trans_1)
   apply(case_tac "u \<noteq> value \<sigma> (a, b)", simp_all)
   apply (meson relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply (metis c_obs_last_Up_same_loc_pres_col_global c_obs_last_def relating_step_to_update_trans_1 x_has_lastWr)
   apply(simp add:pre_block_def FAAZ_def)
   apply(simp add:preCond_def)
   apply clarify
   apply(case_tac "u \<noteq> value \<sigma> (a, b)", simp_all)
   apply (metis (no_types, opaque_lifting) Up_reads_cvd_v cvd_changes_by_Succ_CAS relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply (metis These_writes_releasing_def Up_reads_cvd_v c_obs_last_Up_same_loc_pres_col_global covered_v_def relating_step_to_update_trans_1)
   apply(simp add:pre_block_def FAAZ_def)
   apply(simp add:preCond_def)
   apply clarify
   apply(subgoal_tac "l = value \<sigma> (a, b)") prefer 2
   apply (simp add: covered_v_def visible_writes_def)
   apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2
   apply (meson cvd_changes_by_Succ_CAS relating_step_to_update_trans_1)
   apply(case_tac "u \<noteq> value \<sigma> (a, b)", simp_all)
   apply (meson relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply (metis c_obs_last_Up_same_loc_pres_col_global c_obs_last_def relating_step_to_update_trans_1 x_has_lastWr)
   apply(simp add:pre_block_def FAAZ_def)
   apply(simp add:preCond_def)
   apply clarify
   apply(subgoal_tac "l = value \<sigma> (a, b)") prefer 2
   apply (simp add: covered_v_def visible_writes_def)
   apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2
   apply (meson cvd_changes_by_Succ_CAS relating_step_to_update_trans_1)
   apply(case_tac "u \<noteq> value \<sigma> (a, b)", simp_all)
   apply (meson relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply (metis c_obs_last_Up_same_loc_pres_col_global c_obs_last_def relating_step_to_update_trans_1 x_has_lastWr)
   apply(simp add:pre_block_def FAAZ_def)
   apply(simp add:preCond_def)
   apply clarify
   apply(subgoal_tac "l = value \<sigma> (a, b)") prefer 2
   apply (simp add: covered_v_def visible_writes_def)
   apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2
   apply (meson cvd_changes_by_Succ_CAS relating_step_to_update_trans_1)
   apply(case_tac "u \<noteq> value \<sigma> (a, b)", simp_all)
   apply (meson relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply (metis c_obs_last_Up_same_loc_pres_col_global c_obs_last_def relating_step_to_update_trans_1 x_has_lastWr)
   apply(simp add:pre_block_def post_block_def FAAZ_def)
   apply(simp add:preCond_def)
   apply clarify apply auto[1]
   apply(subgoal_tac "l = value \<sigma> (a, b)") prefer 2
   apply (simp add: covered_v_def visible_writes_def)
   apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2
   apply (meson cvd_changes_by_Succ_CAS relating_step_to_update_trans_1)
   apply (metis These_writes_releasing_def c_obs_last_Up_same_loc_pres_col_global covered_v_def insert_iff relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply(simp add:observation_inv_sig_def Wcap_def covered_v_def visible_writes_def) apply auto[1]
   apply(subgoal_tac "[(rcu_0 + ta) =\<^sub>t' (Suc 0)] \<sigma>") prefer 2 
   apply (metis c_obs_last_Up_same_loc_pres_col_global c_obs_last_def covered_v_def cvd_changes_by_Succ_CAS insert_iff lastWr_visible relating_step_to_update_trans_1 surj_pair wfs_2_def wfs_2_preserved x_has_lastWr)
   apply(subgoal_tac "\<sigma> RMW\<^sup>R[C,l,l]\<^sub>t \<sigma>'") 
   apply (metis (no_types, opaque_lifting) c_obs_last_Up_same_loc_pres_col_global c_obs_last_def covered_v_def cvd_changes_by_Succ_CAS insert_iff surj_pair wfs_2_preserved x_has_lastWr)
   apply (metis lastWr_visible relating_step_to_update_trans_1 wfs_2_def)
   apply(simp add:pre_block_def post_block_def FAAZ_def)
   apply(simp add:preCond_def)
   apply clarify apply auto[1]
   apply(subgoal_tac "l = value \<sigma> (a, b)") prefer 2
   apply (simp add: covered_v_def visible_writes_def)
   apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2
   apply (meson cvd_changes_by_Succ_CAS relating_step_to_update_trans_1)
   apply (metis insert_iff)
   apply(simp add:observation_inv_sig_def Wcap_def covered_v_def visible_writes_def) apply auto[1]
   apply(subgoal_tac "[(rcu_0 + ta) =\<^sub>t' (Suc 0)] \<sigma>") prefer 2 
   apply (metis)
   apply(subgoal_tac "\<sigma> RMW\<^sup>R[C,l,l]\<^sub>t \<sigma>'") 
   apply (metis (no_types, opaque_lifting))
   apply (metis )
   apply (metis dobs_RMW_pres relating_step_to_update_trans_1)
   apply (metis dobs_RMW_pres relating_step_to_update_trans_1)
   apply(subgoal_tac "CAS_succ ms t' = CAS_succ ms' t'", simp_all) prefer 2 apply auto[1]
   apply(case_tac "CAS_succ ms t'", simp_all)
   apply(simp add:pre_block_def post_block_def FAAZ_def)
   apply(simp add:preCond_def)
   apply clarify
   apply auto[1]
   apply(subgoal_tac "l = value \<sigma> (a, b)") prefer 2
   apply (simp add: covered_v_def visible_writes_def)
   apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2
   apply (meson cvd_changes_by_Succ_CAS relating_step_to_update_trans_1)
   apply (metis insert_iff)
   apply(case_tac "ya = value \<sigma> (a, b)", simp_all)
   apply(simp add:observation_inv_sig_def Wcap_def covered_v_def visible_writes_def) apply auto[1]
   apply (metis dobs_RMW_pres lastWr_visible relating_step_to_update_trans_1 wfs_2_def)
   apply(simp add:observation_inv_sig_def Wcap_def covered_v_def visible_writes_def) apply auto[1]
   apply(subgoal_tac "[(rcu_0 + ta) =\<^sub>t' (Suc 0)] \<sigma>") prefer 2
   apply force
   apply(subgoal_tac "\<sigma> RMW\<^sup>R[C,l,l]\<^sub>t \<sigma>'")
   apply (metis dobs_RMW_pres)
   apply (metis lastWr_visible relating_step_to_update_trans_1 wfs_2_def)
   apply(simp add:pre_block_def FAAZ_def)
   apply(simp add:preCond_def)
   apply clarify
   apply auto[1]
   apply(subgoal_tac "l = value \<sigma> (a, b)") prefer 2
   apply (simp add: covered_v_def visible_writes_def)
   apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2
   apply (meson cvd_changes_by_Succ_CAS relating_step_to_update_trans_1)
   apply(case_tac "u \<noteq> value \<sigma> (a, b)", simp_all)
   apply (meson relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply (metis c_obs_last_Up_same_loc_pres_col_global c_obs_last_def relating_step_to_update_trans_1 x_has_lastWr)
   apply(subgoal_tac "l = value \<sigma> (a, b)") prefer 2
   apply (simp add: covered_v_def visible_writes_def)
   apply(subgoal_tac "cvd[C,l] \<sigma>'") prefer 2
   apply (meson cvd_changes_by_Succ_CAS relating_step_to_update_trans_1)
   apply (metis These_writes_releasing_def c_obs_last_Up_same_loc_pres_col_global covered_v_def insert_iff relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
   apply(simp add:pre_block_def post_block_def FAAZ_def)
   apply(simp add:preCond_def)
   apply clarify
   apply(case_tac "ya = value \<sigma> (a, b)", simp_all)
   apply(simp add:observation_inv_sig_def Wcap_def covered_v_def visible_writes_def) apply auto[1]
   apply metis 
   apply(subgoal_tac "[(rcu_0 + ta) =\<^sub>t' (Suc 0)] \<sigma>") prefer 2
   apply force
   apply(subgoal_tac "\<sigma> RMW\<^sup>R[C,l,l]\<^sub>t \<sigma>'")
   apply (metis)
   apply (metis) 
   apply (metis dobs_RMW_pres relating_step_to_update_trans_1)
  apply(subgoal_tac "\<sigma> RMW[C,l,l]\<^sub>t \<sigma>'") prefer 2
  apply (meson FAAZ_is_RMW_R)
  apply(simp add:step_def)
  apply(subgoal_tac "pc ms' t = I9", simp_all add:step_def get_C_val_def)
  prefer 2 apply auto[1]
  apply(subgoal_tac "pc ms t' = pc ms' t'", simp_all add:get_C_val_def) prefer 2
  apply auto[1]
  apply(case_tac "pc ms t'", simp_all)
  apply(simp add:pre_block_def FAAZ_def)
  apply(simp add:preCond_def)
  apply clarify
  apply(subgoal_tac "l = u", simp_all) prefer 2
  apply (metis cvd_changes_by_Succ_CAS wfs_2_preserved x_has_lastWr)
  apply(subgoal_tac "u = value \<sigma> (a, b)") prefer 2
  apply (metis Up_reads_cvd_v relating_step_to_update_trans_1)
  apply simp
  apply(subgoal_tac "[(rcu_0 + t) =\<^sub>t (Suc 0)] \<sigma>")
  apply(simp add:These_writes_releasing_def)
  apply (metis OpSem_definite.c_obs_RMW_intro covered_v_def surj_pair testtttttt)
  apply(simp add:sigma_obs_def)
  apply(simp add:pre_block_def FAAZ_def)
  apply(simp add:preCond_def)
  apply clarify
  apply(subgoal_tac "l = u", simp_all) prefer 2
  apply (metis cvd_changes_by_Succ_CAS wfs_2_preserved x_has_lastWr)
  apply(subgoal_tac "u = value \<sigma> (a, b)") prefer 2
  apply (metis Up_reads_cvd_v relating_step_to_update_trans_1)
  apply simp
  apply(subgoal_tac "[(rcu_0 + t) =\<^sub>t (Suc 0)] \<sigma>")
  apply(simp add:These_writes_releasing_def)
  apply (metis OpSem_definite.c_obs_RMW_intro covered_v_def surj_pair testtttttt)
  apply(simp add:sigma_obs_def)
  apply(simp add:pre_block_def FAAZ_def)
  apply(simp add:preCond_def)
  apply clarify
  apply(subgoal_tac "l = u", simp_all) prefer 2
  apply (metis cvd_changes_by_Succ_CAS wfs_2_preserved x_has_lastWr)
  apply(subgoal_tac "u = value \<sigma> (a, b)") prefer 2
  apply (metis Up_reads_cvd_v relating_step_to_update_trans_1)
  apply simp
  apply(subgoal_tac "[(rcu_0 + t) =\<^sub>t (Suc 0)] \<sigma>")
  apply(simp add:These_writes_releasing_def)
  apply (metis OpSem_definite.c_obs_RMW_intro covered_v_def surj_pair testtttttt)
  apply(simp add:sigma_obs_def)
  apply(simp add:pre_block_def FAAZ_def)
  apply(simp add:preCond_def)
  apply clarify
  apply(subgoal_tac "l = u", simp_all) prefer 2
  apply (metis cvd_changes_by_Succ_CAS wfs_2_preserved x_has_lastWr)
  apply(subgoal_tac "u = value \<sigma> (a, b)") prefer 2
  apply (metis Up_reads_cvd_v relating_step_to_update_trans_1)
  apply simp
  apply(subgoal_tac "[(rcu_0 + t) =\<^sub>t (Suc 0)] \<sigma>")
  apply(simp add:These_writes_releasing_def)
  apply (metis OpSem_definite.c_obs_RMW_intro covered_v_def surj_pair testtttttt)
  apply(simp add:sigma_obs_def)
  apply(simp add:pre_block_def FAAZ_def)
  apply(simp add:preCond_def)
  apply clarify
  apply(subgoal_tac "l = u", simp_all) prefer 2
  apply (metis cvd_changes_by_Succ_CAS wfs_2_preserved x_has_lastWr)
  apply(subgoal_tac "u = value \<sigma> (a, b)") prefer 2
  apply (metis Up_reads_cvd_v relating_step_to_update_trans_1)
  apply simp
  apply(subgoal_tac "[(rcu_0 + t) =\<^sub>t (Suc 0)] \<sigma>")
  apply(simp add:These_writes_releasing_def)
  apply (metis OpSem_definite.c_obs_RMW_intro covered_v_def surj_pair testtttttt)
  apply(simp add:sigma_obs_def)
  apply(simp add:pre_block_def FAAZ_def preCond_def)
  apply clarify
  apply(subgoal_tac "l = u", simp_all) prefer 2
  apply (metis cvd_changes_by_Succ_CAS wfs_2_preserved x_has_lastWr)
  apply(subgoal_tac "u = value \<sigma> (a, b)") prefer 2
  apply (metis Up_reads_cvd_v relating_step_to_update_trans_1)
  apply simp
  apply(simp add:These_writes_releasing_def)
  apply(simp add:sigma_obs_def)
  apply (metis (no_types, opaque_lifting) OpSem_definite.c_obs_RMW_intro last_write_write_on surj_pair wfs_2_def)
  apply(simp add:pre_block_def FAAZ_def preCond_def)
  apply clarify
  apply(subgoal_tac "l = u", simp_all) prefer 2
  apply (metis cvd_changes_by_Succ_CAS wfs_2_preserved x_has_lastWr)
  apply(subgoal_tac "u = value \<sigma> (a, b)") prefer 2
  apply (metis Up_reads_cvd_v relating_step_to_update_trans_1)
  apply simp
  apply(simp add:These_writes_releasing_def)
  apply(simp add:sigma_obs_def)
  apply (metis (no_types, opaque_lifting) OpSem_definite.c_obs_RMW_intro last_write_write_on surj_pair wfs_2_def)
  apply(simp add:pre_block_def FAAZ_def preCond_def)
  apply clarify
  apply(subgoal_tac "l = u", simp_all) prefer 2
  apply (metis cvd_changes_by_Succ_CAS wfs_2_preserved x_has_lastWr)
  apply(subgoal_tac "u = value \<sigma> (a, b)") prefer 2
  apply (metis Up_reads_cvd_v relating_step_to_update_trans_1)
  apply simp
  apply(simp add:These_writes_releasing_def)
  apply(simp add:sigma_obs_def)
  apply (metis (no_types, opaque_lifting) OpSem_definite.c_obs_RMW_intro last_write_write_on surj_pair wfs_2_def)
  apply(simp add:pre_block_def FAAZ_def preCond_def)
  apply clarify
  apply(subgoal_tac "l = u", simp_all) prefer 2
  apply (metis cvd_changes_by_Succ_CAS wfs_2_preserved x_has_lastWr)
  apply(subgoal_tac "u = value \<sigma> (a, b)") prefer 2
  apply (metis Up_reads_cvd_v relating_step_to_update_trans_1)
  apply simp
  apply(simp add:These_writes_releasing_def)
  apply(simp add:sigma_obs_def)
  apply (metis (no_types, opaque_lifting) OpSem_definite.c_obs_RMW_intro last_write_write_on surj_pair wfs_2_def)
  apply(simp add:pre_block_def FAAZ_def preCond_def)
  apply clarify
  apply(subgoal_tac "l = u", simp_all) prefer 2
  apply (metis cvd_changes_by_Succ_CAS wfs_2_preserved x_has_lastWr)
  apply(subgoal_tac "u = value \<sigma> (a, b)") prefer 2
  apply (metis Up_reads_cvd_v relating_step_to_update_trans_1)
  apply simp
  apply(simp add:These_writes_releasing_def)
  apply(simp add:sigma_obs_def)
  apply (metis (no_types, opaque_lifting) OpSem_definite.c_obs_RMW_intro last_write_write_on surj_pair wfs_2_def)
  apply(simp add:pre_block_def FAAZ_def preCond_def)
  apply clarify
  apply(subgoal_tac "l = u", simp_all) prefer 2
  apply (metis cvd_changes_by_Succ_CAS wfs_2_preserved x_has_lastWr)
  apply(subgoal_tac "u = value \<sigma> (a, b)") prefer 2
  apply (metis Up_reads_cvd_v relating_step_to_update_trans_1)
  apply simp
  apply(simp add:These_writes_releasing_def)
  apply(simp add:sigma_obs_def)
  apply (metis (no_types, opaque_lifting) OpSem_definite.c_obs_RMW_intro last_write_write_on surj_pair wfs_2_def)
  apply(simp add:post_block_def FAAZ_def preCond_def)
  apply clarify
  apply simp
  apply(simp add:These_writes_releasing_def sigma_obs_def)
  apply(simp add:observation_inv_sig_def visible_writes_def covered_v_def Wcap_def)
  apply (metis dobs_RMW_pres)
  apply(subgoal_tac "CAS_succ ms t' = CAS_succ ms' t'", simp_all) prefer 2 apply auto[1]
  apply(case_tac "CAS_succ ms t'", simp_all)
  apply(simp add:post_block_def FAAZ_def preCond_def)
  apply clarify
  apply simp
  apply(simp add:These_writes_releasing_def sigma_obs_def)
  apply(simp add:observation_inv_sig_def visible_writes_def covered_v_def Wcap_def)
  apply (metis dobs_RMW_pres)
  apply(simp add:pre_block_def FAAZ_def preCond_def)
  apply clarify
  apply(subgoal_tac "l = u", simp_all) prefer 2
  apply (metis cvd_changes_by_Succ_CAS wfs_2_preserved x_has_lastWr)
  apply(subgoal_tac "u = value \<sigma> (a, b)") prefer 2
  apply (metis Up_reads_cvd_v relating_step_to_update_trans_1)
  apply simp
  apply(simp add:These_writes_releasing_def)
  apply(simp add:sigma_obs_def)
  apply (metis (no_types, opaque_lifting) OpSem_definite.c_obs_RMW_intro last_write_write_on surj_pair wfs_2_def)
  apply(simp add:post_block_def FAAZ_def preCond_def)
  apply clarify
  apply simp
  apply(simp add:These_writes_releasing_def sigma_obs_def)
  apply(simp add:observation_inv_sig_def visible_writes_def covered_v_def Wcap_def)
  by (metis dobs_RMW_pres)
  
   
                






lemma I11_preserves_pre_block_global_pre:
  "t' \<noteq> ta \<and> pre_block ta ms \<sigma>
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> full_inv ms ps \<sigma>
\<Longrightarrow> step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'
\<Longrightarrow> preCond ms ps (pc ms t) t
\<Longrightarrow> \<forall>t'. t'<T_max \<and> t'\<noteq> t \<longrightarrow> t'\<notin> own\<^sub>R ms (the(n ms t))
\<Longrightarrow> sigma_obs ms \<sigma> t
\<Longrightarrow> pc ms t = I11
\<Longrightarrow> t' \<noteq> ta \<and> pre_block ta ms' \<sigma>' " 
  apply(intro conjI impI) apply linarith
  apply(simp add:pre_block_def step_def cas_step_rcu_def)
  apply clarify
  apply(case_tac "y", simp_all)
  apply(subgoal_tac "\<sigma> RMW\<^sup>R[C, l, u]\<^sub>t \<sigma>'") prefer 2
  apply(simp add:CAS_def )
  apply(subgoal_tac "l = the(s ms t)") 
  apply (metis cvd_changes_by_Succ_CAS old.prod.inject relating_step_to_update_trans_1 testtttttt wfs_2_preserved)
  apply (metis Pair_inject Up_reads_cvd_v relating_step_to_update_trans_1)
  apply(case_tac "ta\<noteq>t")
  apply (metis CAS_def cvd_RMW_new_cvd prod.inject relating_step_to_update_trans_1 testtttttt wfs_2_def wfs_2_preserved)
  apply meson 
  apply (simp add: If_visible_then_releasing OpSem_definite.c_obs_RMW_intro lastWr_visible sigma_obs_def wfs_2_def)
  apply(subgoal_tac "\<sigma> [l \<leftarrow> C]\<^sub>t \<sigma>'") prefer 2
  apply(simp add:CAS_def )
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)") 
  apply (simp add: If_visible_then_releasing OpSem_definite.c_obs_RMW_intro lastWr_visible sigma_obs_def wfs_2_def)
  apply clarsimp
  apply(simp add:OpSem.step_def)
  apply(case_tac "RdX C l", simp_all) 
  apply (smt (z3) CollectD RdX_def action.inject(1) covered_v_def visible_writes_def)
  apply (metis RdX_def action.distinct(1))
  apply (metis RdX_def action.distinct(3)) 
  by (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  



lemma I11_preserves_post_block_global_pre:
  "t' \<noteq> ta \<and> post_block t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> full_inv ms ps \<sigma>
\<Longrightarrow> step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'
\<Longrightarrow> preCond ms ps (pc ms t) t
\<Longrightarrow> \<forall>t'. t'<T_max \<and> t'\<noteq> t \<longrightarrow> t'\<notin> own\<^sub>R ms (the(n ms t))
\<Longrightarrow> sigma_obs ms \<sigma> t
\<Longrightarrow> pc ms t = I11
\<Longrightarrow> t' \<noteq> ta \<and> post_block t' ta ms' \<sigma>'  " 
  apply(intro conjI impI) apply linarith
  apply(simp add:post_block_def step_def cas_step_rcu_def)
  apply clarify
  apply(case_tac "y", simp_all) 
  apply (metis CAS_def Pair_inject dobs_RMW_pres relating_step_to_update_trans_1)
  by (metis CAS_def Failed_CAS_preserves_d_obs_supporting_for_later prod.inject)
  
  


lemma supporting_block_cond_sep[simp]:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> pc ms t' \<in> {I1, I2, I3, I4, I5 , I6,
                 I7, I8, I9, I10, I11, cas_res, I12, R1}
\<Longrightarrow>t' \<noteq> ta \<and> (post_block t' ta ms \<sigma> \<or> pre_block ta ms \<sigma>)"
  apply(simp add:block_cond_def)
  apply(case_tac "pc ms t'", simp_all)
  by blast


lemma I11_preserves_block_cond_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> full_inv ms ps \<sigma>
\<Longrightarrow> step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> preCond ms ps (pc ms ta) ta
\<Longrightarrow> preCond ms ps (pc ms t) t
\<Longrightarrow> sigma_obs ms \<sigma> t
\<Longrightarrow> pc ms t = I11
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(subgoal_tac "\<forall>t'. t'<T_max \<and> t'\<noteq> t \<longrightarrow> t'\<notin> own\<^sub>R ms (the(n ms t))") prefer 2
  apply(simp add:preCond_def)
  apply(simp add:full_inv_def general_structure_def n_differ_def n_differ_from_s_outside_def)
  apply (metis option.sel)
  apply(unfold block_cond_def)
  apply(subgoal_tac "pc ms t' = pc ms' t'") prefer 2
  apply(simp add:step_def cas_step_rcu_def)
  apply auto[1]
  apply(case_tac "pc ms t'")
  apply (metis I11_preserves_pre_block_global_pre PC.simps(757))
  apply (metis I11_preserves_pre_block_global_pre PC.simps(758))
  apply (metis I11_preserves_pre_block_global_pre PC.simps(759))
  apply (metis I11_preserves_pre_block_global_pre PC.simps(760))
  apply (metis I11_preserves_pre_block_global_pre PC.simps(761))
  apply (metis I11_preserves_pre_block_global_pre PC.simps(762))
  apply (metis I11_preserves_pre_block_global_pre PC.simps(763))
  apply (metis I11_preserves_pre_block_global_pre PC.simps(764))
  apply (metis I11_preserves_pre_block_global_pre PC.simps(765))
  apply (metis I11_preserves_pre_block_global_pre PC.simps(766))
  apply (metis I11_preserves_pre_block_global_pre PC.simps(767))
  apply (metis I11_preserves_post_block_global_pre PC.simps(768))
  apply simp
  apply simp
  apply(subgoal_tac "CAS_succ ms' t' = CAS_succ ms t'") prefer 2
  apply(simp add:step_def cas_step_rcu_def) apply auto[1]
  apply(case_tac "CAS_succ ms' t'")
  apply (metis I11_preserves_post_block_global_pre PC.simps(771))
  apply (metis I11_preserves_pre_block_global_pre PC.simps(771))
  apply simp
  apply (metis I11_preserves_post_block_global_pre PC.simps(773))
  by simp_all




lemma I5_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {I5}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' "  
  apply(simp add:step_def)
  apply(simp add:abbr pre_block_def)
  apply(simp add:block_cond_def)
  apply(case_tac "pc ms t'", simp_all)
  apply(simp_all add:pre_block_def abbr)
  apply(simp_all add:post_block_def abbr preCond_def full_inv_def Rcap_def Wcap_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply(case_tac "ta \<noteq> t")
  apply (meson add_left_imp_eq dobs_WrX_pres)
  apply(simp add:general_structure_def own\<^sub>W_and_det_things_def)
  apply(subgoal_tac "t\<notin>own\<^sub>R ms (the (s ms t'))")
  apply blast
  apply (metis option.sel)
  apply(case_tac "CAS_succ ms t'", simp_all)
  apply (metis diff_add_inverse dobs_WrX_pres option.sel)
  apply (metis add_left_imp_eq c_obs_last_WrX_diff_pres cvd_backwards_WrX observation_inv_sig_def wfs_2_def)
  by (metis diff_add_inverse dobs_WrX_pres option.sel)




lemma I6_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {I6}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' "   
  apply(case_tac "t\<noteq>ta")
  apply(simp add:step_def)
  apply(simp add:abbr pre_block_def)
  apply(simp add:block_cond_def)
  apply(case_tac "repeat ms t", simp_all)
  apply(case_tac "pc ms t'", simp_all)
  apply(simp_all add:pre_block_def abbr)
  apply (metis add_left_imp_eq c_obs_last_WrX_diff_pres cvd_WrX_other_var_pres testtttttt wfs_2_def wfs_2_preserved)
  apply (metis add_left_imp_eq c_obs_last_WrX_diff_pres cvd_backwards_WrX wfs_2_def)
  apply(simp_all add:post_block_def abbr preCond_def full_inv_def Rcap_def Wcap_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis add_left_imp_eq dobs_WrX_pres)
  apply (metis add_left_imp_eq c_obs_last_WrX_diff_pres cvd_backwards_WrX dobs_WrX_pres wfs_2_def)
  apply (metis add_left_imp_eq dobs_WrX_pres)
  apply(case_tac "pc ms t'", simp_all)
  apply(simp_all add:pre_block_def abbr)
  apply (metis add_left_imp_eq c_obs_last_WrX_diff_pres cvd_WrX_other_var_pres testtttttt wfs_2_def wfs_2_preserved)
  apply (metis add_left_imp_eq c_obs_last_WrX_diff_pres cvd_backwards_WrX wfs_2_def)
  apply(simp_all add:post_block_def abbr preCond_def full_inv_def Rcap_def Wcap_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse wfs_2_def)
  apply (metis add_left_imp_eq dobs_WrX_pres)
  apply (metis add_left_imp_eq c_obs_last_WrX_diff_pres cvd_backwards_WrX dobs_WrX_pres wfs_2_def)
  apply (metis add_left_imp_eq dobs_WrX_pres)    
(*t = ta*)
  apply(simp add:step_def)
  apply(simp add:abbr pre_block_def)
  apply(case_tac "repeat ms t", simp_all)
  apply(unfold block_cond_def)
  apply(case_tac "pc ms t'", simp_all) 
  apply(simp_all add:pre_block_def abbr observation_inv_sig_def wfs_2_def)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply(simp_all add:post_block_def abbr observation_inv_sig_def wfs_2_def)
  apply (metis (no_types, lifting) Wcap_def insertCI option.sel)
  apply(simp add:Wcap_def)
  apply(case_tac "CAS_succ ms t'", simp_all)
  apply (metis (no_types, opaque_lifting) option.sel)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) Wcap_def insertCI option.sel)
  apply(case_tac "pc ms t'", simp_all) 
  apply(simp_all add:pre_block_def abbr observation_inv_sig_def wfs_2_def)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  apply(simp_all add:post_block_def abbr observation_inv_sig_def wfs_2_def)
  apply (metis (no_types, lifting) Wcap_def insertCI option.sel)
  apply(simp add:Wcap_def)
  apply(case_tac "CAS_succ ms t'", simp_all)
  apply (metis (no_types, opaque_lifting) option.sel)
  apply (metis (no_types, lifting) cvd_backwards_WrX)
  by (metis (no_types, lifting) Wcap_def insertCI option.sel)

  
  



lemma I7_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {I7}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' "  
  apply(simp add:step_def)
  apply(simp add:abbr pre_block_def)
  apply(simp add:block_cond_def)
  apply(case_tac "pc ms t'", simp_all)
  apply(simp_all add:pre_block_def abbr)
  apply(simp_all add:post_block_def abbr preCond_def full_inv_def Rcap_def Wcap_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres cvd_backwards_WrX diff_add_inverse observation_inv_sig_def wfs_2_def)
  apply(case_tac "ta \<noteq> t")
  apply (meson add_left_imp_eq dobs_WrX_pres)
  apply(simp add:general_structure_def own\<^sub>W_and_det_things_def)
  apply(subgoal_tac "t\<notin>own\<^sub>R ms (the (s ms t'))")
  apply blast
  apply (metis option.sel)
  apply(case_tac "CAS_succ ms t'", simp_all)
  apply (metis diff_add_inverse dobs_WrX_pres option.sel)
  apply (metis add_left_imp_eq c_obs_last_WrX_diff_pres cvd_backwards_WrX observation_inv_sig_def wfs_2_def)
  by (metis diff_add_inverse dobs_WrX_pres option.sel)



lemma I9_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {I9}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' "  
  apply(simp add:step_def)
  apply(simp add:abbr pre_block_def)
  apply(simp add:block_cond_def)
  apply(subgoal_tac "pc ms t' = pc ms' t'") prefer 2 apply auto[1]
  apply(case_tac "pc ms t'", simp_all)
  apply(simp_all add:pre_block_def abbr)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply(simp_all add:post_block_def abbr)
  apply clarsimp using dobs_RdX_pres apply blast
  apply(case_tac "CAS_succ ms' t'", simp_all)
  apply clarsimp using dobs_RdX_pres apply blast
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp using dobs_RdX_pres by blast
  
  
lemma I10_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {I10}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:step_def)
  apply(simp add:block_cond_def)
  apply(simp add:abbr pre_block_def)
  apply(case_tac "pc ms t'", simp_all add:con_assms_def)
  apply(simp_all add:pre_block_def abbr)
  apply (metis c_obs_last_WrX_diff_pres not_cvd_WrX_pres rcu_locs_differ_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres not_cvd_WrX_pres rcu_locs_differ_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres not_cvd_WrX_pres rcu_locs_differ_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres not_cvd_WrX_pres rcu_locs_differ_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres not_cvd_WrX_pres rcu_locs_differ_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres not_cvd_WrX_pres rcu_locs_differ_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres not_cvd_WrX_pres rcu_locs_differ_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres not_cvd_WrX_pres rcu_locs_differ_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres not_cvd_WrX_pres rcu_locs_differ_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres not_cvd_WrX_pres rcu_locs_differ_def wfs_2_def)
  apply (metis c_obs_last_WrX_diff_pres not_cvd_WrX_pres rcu_locs_differ_def wfs_2_def)
  apply(simp_all add:post_block_def abbr)
  apply (metis dobs_WrX_pres rcu_locs_differ_def)
  apply(case_tac "CAS_succ ms t'", simp_all)
  apply (metis dobs_WrX_pres rcu_locs_differ_def)
  apply (metis c_obs_last_WrX_diff_pres not_cvd_WrX_pres rcu_locs_differ_def wfs_2_def)
  by (metis dobs_WrX_pres rcu_locs_differ_def)


lemma cas_res_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {cas_res}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:step_def)
  apply(simp add:block_cond_def)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply(case_tac "pc ms t'", simp_all add:con_assms_def pre_block_def abbr post_block_def)
  by(case_tac "pc ms t'", simp_all add:con_assms_def pre_block_def abbr post_block_def)
  


lemma I12_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {I12}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:step_def abbr)
  apply(simp add:block_cond_def )
  apply(case_tac "pc ms t'", simp_all)
  apply(simp_all add:pre_block_def con_assms_def)
  apply clarify
  apply(simp_all add:preCond_def full_inv_def Rcap_def Wcap_def)
  apply clarify+
  apply (metis add_diff_cancel_left' c_obs_last_WrX_diff_pres cvd_backwards_WrX observation_inv_sig_def wfs_2_def)
  apply (metis add_diff_cancel_left' c_obs_last_WrX_diff_pres cvd_backwards_WrX observation_inv_sig_def wfs_2_def)
  apply (metis add_diff_cancel_left' c_obs_last_WrX_diff_pres cvd_backwards_WrX observation_inv_sig_def wfs_2_def)
  apply (metis add_diff_cancel_left' c_obs_last_WrX_diff_pres cvd_backwards_WrX observation_inv_sig_def wfs_2_def)
  apply (metis add_diff_cancel_left' c_obs_last_WrX_diff_pres cvd_backwards_WrX observation_inv_sig_def wfs_2_def)
  apply (metis add_diff_cancel_left' c_obs_last_WrX_diff_pres cvd_backwards_WrX observation_inv_sig_def wfs_2_def)
  apply (metis add_diff_cancel_left' c_obs_last_WrX_diff_pres cvd_backwards_WrX observation_inv_sig_def wfs_2_def)
  apply (metis add_diff_cancel_left' c_obs_last_WrX_diff_pres cvd_backwards_WrX observation_inv_sig_def wfs_2_def)
  apply (metis add_diff_cancel_left' c_obs_last_WrX_diff_pres cvd_backwards_WrX observation_inv_sig_def wfs_2_def)
  apply (metis add_diff_cancel_left' c_obs_last_WrX_diff_pres cvd_backwards_WrX observation_inv_sig_def wfs_2_def)
  apply (metis add_diff_cancel_left' c_obs_last_WrX_diff_pres cvd_backwards_WrX observation_inv_sig_def wfs_2_def)
  apply(simp_all add:post_block_def con_assms_def)
  apply (metis add_left_imp_eq dobs_WrX_pres option.sel)
  apply(case_tac "CAS_succ ms t'", simp_all)
  apply (metis add_left_imp_eq dobs_WrX_pres option.sel)
  apply (metis add_diff_cancel_left' c_obs_last_WrX_diff_pres cvd_backwards_WrX observation_inv_sig_def wfs_2_def)
  by (metis add_left_imp_eq dobs_WrX_pres option.sel)
  

lemma I13_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {I13}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:step_def)
  apply(simp add:block_cond_def)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply(case_tac "pc ms t'", simp_all add:con_assms_def pre_block_def abbr post_block_def)
  by(case_tac "pc ms t'", simp_all add:con_assms_def pre_block_def abbr post_block_def)
  
lemma I14_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {I14}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:step_def)
  apply(simp add:block_cond_def)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply(case_tac "pc ms t'", simp_all add:con_assms_def pre_block_def abbr post_block_def)
  by(case_tac "pc ms t'", simp_all add:con_assms_def pre_block_def abbr post_block_def)
  

lemma finished_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {finished}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  by(simp add:step_def)
  

lemma R1_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {R1}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:step_def)
  apply(simp add:block_cond_def)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply(case_tac "pc ms t'", simp_all add:con_assms_def pre_block_def abbr post_block_def)
  by(case_tac "pc ms t'", simp_all add:con_assms_def pre_block_def abbr post_block_def)


lemma R2_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {R2}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:step_def abbr)
  apply clarify
  apply(simp add:block_cond_def)
  by(case_tac "pc ms t'", simp_all add:con_assms_def pre_block_def abbr post_block_def)


lemma R3_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {R3}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:step_def abbr)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(simp_all add:block_cond_def)
  apply(case_tac "pc ms t'", simp_all add:con_assms_def pre_block_def abbr post_block_def)
  by(case_tac "pc ms t'", simp_all add:con_assms_def pre_block_def abbr post_block_def)


lemma R4_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {R4}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:step_def abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply(simp_all add:block_cond_def)
  apply(case_tac "pc ms t'", simp_all add:con_assms_def pre_block_def abbr post_block_def)
  by(case_tac "pc ms t'", simp_all add:con_assms_def pre_block_def abbr post_block_def)


lemma R5_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {R5}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:step_def abbr) apply clarify
  apply(simp_all add:block_cond_def)
  by(case_tac "pc ms t'", simp_all add:con_assms_def pre_block_def abbr post_block_def)
  

lemma S1_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {S1}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:step_def abbr)
  apply(simp add:block_cond_def )
  apply(case_tac "pc ms t'", simp_all)
  apply(simp_all add:pre_block_def con_assms_def)
  apply clarify
  apply(simp_all add:preCond_def full_inv_def Rcap_def Wcap_def)
  by(simp_all add:post_block_def con_assms_def)
  



lemma S2_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {S2}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:step_def abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all add:abbr)
  apply(simp_all add:block_cond_def )
  apply(case_tac "pc ms t'", simp_all)
  apply(simp_all add:pre_block_def con_assms_def)
  apply clarify+
  apply(simp_all add:post_block_def con_assms_def)
  apply(case_tac "pc ms t'", simp_all)
  apply(simp_all add:pre_block_def con_assms_def)
  apply clarify+
  apply(simp_all add:post_block_def con_assms_def)
  apply(case_tac "pc ms t'", simp_all)
  apply(simp_all add:pre_block_def con_assms_def)
  apply clarify+
  by(simp_all add:post_block_def con_assms_def)


lemma S3_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {S3}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:step_def abbr)
  apply(simp add:block_cond_def )
  apply(subgoal_tac "pc ms' t' = pc ms t'") prefer 2 apply auto[1]
  apply(case_tac "pc ms t'", simp_all add: pre_block_def con_assms_def post_block_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp using dobs_RdX_pres apply presburger
  apply(subgoal_tac "CAS_succ ms t' = CAS_succ ms' t'") prefer 2 apply auto[1]
  apply(case_tac "CAS_succ ms t'", simp_all)
  apply clarsimp using dobs_RdX_pres apply presburger
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp using dobs_RdX_pres by presburger




lemma S4_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {S4}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:step_def abbr)
  apply(simp add:block_cond_def )
  apply(subgoal_tac "pc ms' t' = pc ms t'") prefer 2 apply auto[1]
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)
  apply(case_tac "pc ms t'", simp_all add: pre_block_def con_assms_def post_block_def)
  apply clarsimp 
  apply(case_tac "pc ms t'", simp_all add: pre_block_def con_assms_def post_block_def)
  by(case_tac "pc ms t'", simp_all add: pre_block_def con_assms_def post_block_def)
  



lemma S5_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {S5}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:block_cond_def )
  apply(simp add:step_def abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply(subgoal_tac "pc ms' t' = pc ms t'") prefer 2 apply auto[1]
  apply(case_tac "pc ms t'", simp_all add: pre_block_def con_assms_def post_block_def)
  by(case_tac "pc ms t'", simp_all add: pre_block_def con_assms_def post_block_def)
  




lemma S6_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {S6}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:block_cond_def )
  apply(simp add:step_def abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply(subgoal_tac "pc ms' t' = pc ms t'") prefer 2 apply auto[1]
  apply(case_tac "pc ms t'", simp_all add: pre_block_def con_assms_def post_block_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp using dobs_RdX_pres apply presburger
  apply(case_tac "CAS_succ ms t'", simp_all)
  apply clarsimp using dobs_RdX_pres apply presburger
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp using dobs_RdX_pres apply presburger
  apply(subgoal_tac "pc ms' t' = pc ms t'") prefer 2 apply auto[1]
  apply(case_tac "pc ms t'", simp_all add: pre_block_def con_assms_def post_block_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp using dobs_RdX_pres apply presburger
  apply(case_tac "CAS_succ ms t'", simp_all)
  apply clarsimp using dobs_RdX_pres apply presburger
  apply clarsimp apply (meson c_obs_last_RdX_pres not_cvd_RdX_pres wfs_2_def)
  apply clarsimp using dobs_RdX_pres by presburger




lemma S7_preserves_pre_block_global_pre:
  "block_cond t' ta ms \<sigma> 
\<Longrightarrow> book_keeping \<sigma> l t t'
\<Longrightarrow> book_keeping \<sigma> l t' ta
\<Longrightarrow> con_assms ms ps 
\<Longrightarrow> preCond ms ps pre_step t
\<Longrightarrow> preCond ms ps (pc ms t') t'
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> full_inv ms ps \<sigma> 
\<Longrightarrow> pre_step \<in> {S7}
\<Longrightarrow> block_cond t' ta ms' \<sigma>' " 
  apply(simp add:block_cond_def )
  apply(simp add:step_def abbr)
  apply(subgoal_tac "pc ms' t' = pc ms t'") prefer 2 apply auto[1]
  apply(case_tac "reg ms t = Suc 0", simp_all add:abbr)
  apply(case_tac "reg ms t = Suc 0", simp_all add:abbr)
  apply(case_tac "pc ms t'", simp_all add: pre_block_def con_assms_def post_block_def)
  by(case_tac "pc ms t'", simp_all add: pre_block_def con_assms_def post_block_def)
  






lemma showing_block_cond_pres_global:
 "con_assms ms ps \<Longrightarrow> 
  book_keeping \<sigma> l t t' \<Longrightarrow>
  book_keeping \<sigma> l t' ta \<Longrightarrow>
  full_inv ms ps \<sigma> \<Longrightarrow> 
  wfs_2 \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  t' < T_max \<Longrightarrow>
  cvd[C,u] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  preCond ms ps (pc ms t') t' \<Longrightarrow> 
  preCond ms ps (pc ms ta) ta \<Longrightarrow> 
  sigma_obs ms \<sigma> t \<Longrightarrow> 
  block_cond t' ta ms \<sigma> \<Longrightarrow>
  det_block t ms \<sigma>  \<Longrightarrow>                    
  block_cond t' ta ms' \<sigma>' " 
  apply(case_tac "pc ms t = I11") 
  using I11_preserves_block_cond_global_pre apply blast
  apply(case_tac "pc ms t = I8") 
  using I8_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = I4") 
  using I4_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = I1") 
  using I1_preserves_pre_block_global_pre block_cond_def apply blast
  apply(case_tac "pc ms t = I2") 
  using I2_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = I3") 
  using I3_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = I5") 
  using I5_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = I6") 
  using I6_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = I7") 
  using I7_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = I9") 
  using I9_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = I10") 
  using I10_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = cas_res") 
  using cas_res_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = I12") 
  using I12_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = I13") 
  using I13_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = I14") 
  using I14_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = R1") 
  using R1_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = R2") 
  using R2_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = R3") 
  using R3_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = R4") 
  using R4_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = R5") 
  using R5_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = S1") 
  using S1_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = S2") 
  using S2_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = S3") 
  using S3_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = S4") 
  using S4_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = S5") 
  using S5_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = S6") 
  using S6_preserves_pre_block_global_pre apply blast
  apply(case_tac "pc ms t = S7") 
  using S7_preserves_pre_block_global_pre apply blast
  apply auto[1] apply(simp add:step_def)
  by(case_tac "pc ms t", simp_all)












lemma showing_det_block_pres_global_FAAZ:
 "full_inv ms ps \<sigma> \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow> 
  book_keeping \<sigma> l t t' \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  t' < T_max \<Longrightarrow>
  t\<noteq> t' \<Longrightarrow>
  pc ms t = I8 \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  block_cond t t' ms \<sigma>  \<Longrightarrow>
  \<forall>t'a. t'a<T_max \<and> t'a\<noteq>t\<longrightarrow> block_cond t t'a ms \<sigma>  \<Longrightarrow>  
  det_block t ms \<sigma>  \<Longrightarrow>    
  det_block t' ms \<sigma> \<Longrightarrow>    
  det_block t' ms' \<sigma>'"
  apply(simp add: full_inv_def step_def get_C_val_def FAAZ_def det_block_def preCond_def These_writes_releasing_def)
  apply(clarsimp) 
  apply(simp add:Rcap_def Wcap_def)
  apply(case_tac "det ms t' ! j = value \<sigma> (a, b)", simp_all)
  apply (smt (verit) CollectD covered_v_def general_structure_def less_nat_zero_code list.size(3) observation_inv_sig_def own\<^sub>W_and_det_things_def visible_writes_def)
  apply(subgoal_tac "det ms t' ! j \<noteq> value \<sigma> (a, b)") prefer 2
  apply meson
  apply(case_tac "t\<in>own\<^sub>R ms (det ms t' ! j)") 
  apply (metis block_cond_def general_structure_def list.size(3) not_less_eq option.sel own\<^sub>W_and_det_things_def zero_less_Suc)
  apply(subgoal_tac "t'a \<in> own\<^sub>R ms (det ms t' ! j) \<longrightarrow> t'a \<in> own\<^sub>R ms' (det ms' t' ! j)")
  prefer 2 apply auto[1]
  apply(subgoal_tac "t'a \<noteq> t") prefer 2 apply auto[1]
  apply(subgoal_tac "OpSem.step t (Update C l l) \<sigma> \<sigma>'") prefer 2 
  apply (metis FAAZ_def FAAZ_is_RMW_R fst_eqD) 
  by (metis con_assms_def dobs_RMW_pres reservations_differ_def)
  
  
  









lemma showing_det_block_pres_global_CAS:
 "main_inv ms ps \<Longrightarrow> 
  con_assms ms ps \<Longrightarrow> 
  book_keeping \<sigma> l t t' \<Longrightarrow>
  psem_rules ps \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  t' < T_max \<Longrightarrow>
  t\<noteq> t' \<Longrightarrow>
  cvd[C,u] \<sigma> \<Longrightarrow>
  pc ms t = I11 \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  general_structure ms \<Longrightarrow>
  observation_inv_ms ms \<Longrightarrow>
  observation_inv_sig ms ps \<sigma> \<Longrightarrow>
  \<forall>t'a. t'a<T_max \<and> t'a\<noteq>t \<longrightarrow> block_cond t t'a ms \<sigma>  \<Longrightarrow>
  det_block t' ms \<sigma>  \<Longrightarrow>  
  det_block t ms \<sigma>  \<Longrightarrow>    
  det_block t' ms' \<sigma>'"
  apply(simp add:step_def cas_step_rcu_def det_block_def preCond_def These_writes_releasing_def)
  apply clarify
  apply(case_tac "b", simp_all)
  apply(case_tac "ya", simp_all)
  apply (metis (no_types, lifting) CAS_def con_assms_def dobs_RMW_pres prod.inject relating_step_to_update_trans_1 reservations_differ_def)
  apply(simp add:CAS_def)
  apply(case_tac "value \<sigma> (a, Fract aa ba) = yb", simp_all)
  using Failed_CAS_preserves_d_obs_supporting_for_later
  by (metis (no_types, lifting) con_assms_def reservations_differ_def)













lemma showing_det_block_pres_global:
 "full_inv ms ps \<sigma>\<Longrightarrow> 
  con_assms ms ps \<Longrightarrow> 
  book_keeping \<sigma> l t t' \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow>
  t<T_max \<Longrightarrow>
  t' < T_max \<Longrightarrow>
  t\<noteq> t' \<Longrightarrow>
  cvd[C,u] \<sigma> \<Longrightarrow>
  step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>' \<Longrightarrow> 
  preCond ms ps (pc ms t) t \<Longrightarrow> 
  \<forall>t'a. t'a<T_max \<and> t\<noteq>t'a \<longrightarrow> block_cond t t'a ms \<sigma>  \<Longrightarrow>
  det_block t' ms \<sigma>  \<Longrightarrow>  
  det_block t ms \<sigma>  \<Longrightarrow>    
  det_block t' ms' \<sigma>'" 
  apply(case_tac "pc ms t = I8") using showing_det_block_pres_global_FAAZ apply blast 
  apply(case_tac "pc ms t = I11") using showing_det_block_pres_global_CAS full_inv_def apply blast
  apply(simp add:det_block_def full_inv_def)
  apply(clarsimp)
  apply(simp add: step_def preCond_def)
  apply(case_tac "pc ms t", simp_all add:abbr)
  apply blast
  apply blast
  apply blast
  apply(case_tac "[(rcu_0 + t'a) =\<^sub>t' (Suc 0)] \<sigma>")
  apply meson apply auto[1]
  apply (metis (mono_tags, opaque_lifting) allocated_addresses_def allocated_det_addr_def isfree_addr_def list.size(3) not_less_eq zero_less_Suc)
  apply(case_tac "t'a \<noteq> t", simp_all)
  apply (metis (no_types, lifting) add_left_imp_eq dobs_WrX_pres)
  apply(simp add:Rcap_def Wcap_def own\<^sub>W_and_det_things_def)
  apply(simp add:general_structure_def)
  apply (metis bot_nat_0.extremum_strict list.size(3) option.sel own\<^sub>W_and_det_things_def)
  apply(case_tac "repeat ms t", simp_all)
  apply(case_tac "det ms t' ! j = the (s ms t)", simp_all)
  apply (metis (no_types, lifting) add_left_imp_eq dobs_WrX_pres)
  apply (smt (verit) Rcap_def Wcap_def add_left_imp_eq dobs_WrX_pres general_structure_def insertCI insertE length_0_conv less_Suc_eq_0_disj not_less_eq option.sel own\<^sub>W_and_det_things_def)
  apply (smt (verit) Rcap_def Wcap_def add_left_imp_eq dobs_WrX_pres general_structure_def length_0_conv less_Suc_eq_0_disj not_less_eq option.inject own\<^sub>W_and_det_things_def)
  apply (smt (verit) Rcap_def Wcap_def add_left_imp_eq dobs_WrX_pres general_structure_def length_0_conv less_Suc_eq_0_disj not_less_eq option.inject own\<^sub>W_and_det_things_def)
  apply clarsimp
  apply (metis (no_types, lifting) dobs_RdX_pres)
  apply(simp add:con_assms_def rcu_locs_differ_def)
  apply (metis (no_types, lifting) dobs_WrX_pres)
  apply (smt (verit) Diff_iff Rcap_def Wcap_def add_left_imp_eq dobs_WrX_pres general_structure_def insertCI insertE length_0_conv less_Suc_eq_0_disj not_less_eq option.sel own\<^sub>W_and_det_things_def)
  apply blast
  apply blast
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply blast
  apply blast
  apply blast
  apply blast 
  apply(clarsimp) apply blast
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply blast
  apply blast
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply blast
  apply blast
  apply (metis (no_types, lifting) DiffD1)
  apply blast
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(case_tac "CTRsync\<^sub>1 ms t = t", simp_all add:abbr)
  apply blast
  apply blast
  apply blast 
  apply clarsimp
  apply (metis (no_types, lifting) dobs_RdX_pres)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>2 ms t = t", simp_all add:abbr)
  apply blast
  apply blast
  apply blast
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply blast
  apply blast
  apply clarsimp
  apply (metis (no_types, lifting) dobs_RdX_pres)
  apply(case_tac "reg ms t = Suc 0", simp_all add: abbr)
  apply blast
  by blast
  

  
  




end