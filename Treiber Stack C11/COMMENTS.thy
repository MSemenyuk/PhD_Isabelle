
(*************************************************************************************)
(***************************************COMMENTS**************************************)
(*************************************************************************************)




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



