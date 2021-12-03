theory AbstractLock_Lib
imports Lib Lib_ProofRules
begin

definition "lock_acquire t w \<sigma>\<^sub>L \<sigma>\<^sub>C ts' \<equiv> 
    let v =  lib_value \<sigma>\<^sub>L w; v' = v + 1 in
     if (2 dvd v)
      then 
        (lib_update t w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts', (True, v))
      else 
        ((\<sigma>\<^sub>L ,\<sigma>\<^sub>C), (False, v))"


definition "lock_release t w \<sigma>\<^sub>L \<sigma>\<^sub>C ts' \<equiv>
            let v =  lib_value \<sigma>\<^sub>L w; v' = v + 1 in 
               lib_write t True w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts'"


definition "lock_acquire_step t x \<sigma>\<^sub>L \<sigma>\<^sub>C  \<sigma>\<^sub>L' \<sigma>\<^sub>C'  res ver \<equiv> 
            \<exists> w ts' . w \<in> lib_visible_writes \<sigma>\<^sub>L t x \<and>
             w \<notin> lib_covered \<sigma>\<^sub>L \<and>
             lib_valid_fresh_ts \<sigma>\<^sub>L w ts' \<and>
             \<sigma>\<^sub>L' = fst(fst(lock_acquire t w \<sigma>\<^sub>L \<sigma>\<^sub>C ts')) \<and>
             \<sigma>\<^sub>C' = snd(fst(lock_acquire t w \<sigma>\<^sub>L \<sigma>\<^sub>C ts')) \<and>
             res = fst(snd(lock_acquire t w \<sigma>\<^sub>L \<sigma>\<^sub>C ts')) \<and>
             ver = snd(snd(lock_acquire t w \<sigma>\<^sub>L \<sigma>\<^sub>C ts'))"


definition "lock_release_step t x \<sigma>\<^sub>L \<sigma>\<^sub>C \<sigma>\<^sub>L' \<sigma>\<^sub>C' \<equiv> 
            \<exists> w ts' . w \<in> lib_visible_writes \<sigma>\<^sub>L t x \<and>
              w \<notin> lib_covered \<sigma>\<^sub>L \<and>
              lib_valid_fresh_ts \<sigma>\<^sub>L w ts' \<and>
              \<sigma>\<^sub>L' = lock_release t w \<sigma>\<^sub>L \<sigma>\<^sub>C ts' \<and>
              \<sigma>\<^sub>C' =  \<sigma>\<^sub>C"

abbreviation Lock_acquire_abbr:: " surrey_state \<Rightarrow> lib_state \<Rightarrow> T \<Rightarrow> L \<Rightarrow> surrey_state \<Rightarrow> lib_state \<Rightarrow> bool \<Rightarrow> V  \<Rightarrow> bool" ("[_ _ _  LOCKACQ(_)  _ _ _ _]")
  where "[\<sigma>\<^sub>C \<sigma>\<^sub>L t LOCKACQ(x) \<sigma>\<^sub>C' \<sigma>\<^sub>L' r v] \<equiv> lock_acquire_step t x \<sigma>\<^sub>L \<sigma>\<^sub>C  \<sigma>\<^sub>L' \<sigma>\<^sub>C' r v"

abbreviation Lock_rel_abbr:: " surrey_state \<Rightarrow> lib_state \<Rightarrow> T \<Rightarrow> L  \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool" ("[_ _ _  LOCKREL(_)  _ _ ]")
  where "[\<sigma>\<^sub>C \<sigma>\<^sub>L t LOCKREL(x) \<sigma>\<^sub>L' \<sigma>\<^sub>C'] \<equiv> lock_release_step t x \<sigma>\<^sub>L \<sigma>\<^sub>C \<sigma>\<^sub>L' \<sigma>\<^sub>C'"


definition "lib_covered_val \<sigma> l v \<equiv> 
  (\<exists> ts . ts \<in> lib_writes_on \<sigma> l \<and> lib_value \<sigma> ts = v) \<and>
  (\<forall> ts . ts \<in> lib_writes_on \<sigma> l \<and> ts \<notin> lib_covered \<sigma> \<longrightarrow> lib_value \<sigma> ts > v)"


abbreviation l_covered_val_abbr:: "nat \<Rightarrow> nat \<Rightarrow> lib_state \<Rightarrow> bool" ("cvv[lib(_), _] _" [100, 100, 100])
 where "cvv[lib(l), u] \<sigma> \<equiv> lib_covered_val \<sigma> l u"




definition "even_not_covered_last ls x \<equiv> \<forall> w . w\<in>lib_writes_on ls x \<and> even (lib_value ls w) \<and> w\<notin>lib_covered ls \<longrightarrow> lib_lastWr ls x = w"


definition "abslock_invs ls x \<equiv> even_not_covered_last ls x" 


lemmas invs_abs = even_not_covered_last_def 

lemma abslock_even_not_covered_last_inv:
  assumes "lib_wfs ls cs" 
      and "wfs cs "
      and "even_not_covered_last ls x"
      and "lock_acquire_step t x ls cs ls' cs' res ver"
    shows "even_not_covered_last ls' x"
  using assms
  apply(simp add: even_not_covered_last_def abslock_invs_def)
  apply(intro conjI impI allI, elim conjE)
  apply(case_tac "res = False", simp)
   apply(simp add: invs_abs lock_acquire_step_def lock_acquire_def)
   apply auto[1]
  apply simp
  apply(subgoal_tac "a = x", simp)
   defer
   apply(simp add: lib_writes_on_def)
  apply(simp add: lock_acquire_step_def lock_acquire_def )
   apply(elim exE conjE)
 apply(case_tac "even (lib_value ls (aa, ba))", simp_all)
  apply(simp add: lib_update_def all_updates_l  lib_writes_on_def lib_value_def)
  apply safe
  apply(simp add: lib_visible_writes_def)
     apply (simp add: lib_writes_on_def)
  apply(simp add: lib_visible_writes_def)
    apply (simp add: lib_writes_on_def)
   apply(simp add: lib_visible_writes_def lib_writes_on_def)
   apply clarsimp
   apply(simp add: lib_visible_writes_def lib_writes_on_def)
  defer
   apply(simp add: lib_visible_writes_def lib_writes_on_def lib_lastWr_def lib_valid_fresh_ts_def)
  proof -
    fix b :: rat and aa :: nat and ba :: rat and ts' :: rat
    assume a1: "even (lib_val (lib_mods ls (x, ba)))"
    assume "ver = lib_val (lib_mods ls (x, ba))"
    assume a2: "aa = x \<and> (aa, ba) \<in> lib_writes ls \<and> tst (lib_thrView ls t x) \<le> ba"
    assume a3: "even (lib_val (if b = ts' then \<lparr>lib_val = Suc (lib_val (lib_mods ls (aa, ba))), lib_rel = True\<rparr> else lib_mods ls (x, b)))"
    assume a4: "\<forall>b. (x, b) \<in> lib_writes ls \<and> even (lib_val (lib_mods ls (x, b))) \<and> (x, b) \<notin> lib_covered ls \<longrightarrow> Max (tst ` {w. var w = x \<and> w \<in> lib_writes ls}) = b"
    assume a5: "(x, ba) \<notin> lib_covered ls"
    assume a6: "(x, b) \<in> lib_writes ls"
    assume a7: "b \<noteq> ba"
    assume a8: "(x, b) \<notin> lib_covered ls"
    have "Max (tst ` {p. var p = x \<and> p \<in> lib_writes ls}) = ba"
      using a5 a4 a2 a1 by meson
    then have "b = ts'"
      using a8 a7 a6 a4 a3 by auto
    then show "Max (tst ` {w. var w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)}) = b"
      using a3 a2 a1 by force
  next
  fix b :: rat and aa :: nat and ba :: rat and ts' :: rat
assume a1: "aa = x \<and> (aa, ba) \<in> lib_writes ls \<and> tst (lib_thrView ls t x) \<le> ba"
  assume a2: "b \<noteq> ba"
  assume a3: "(x, b) \<in> lib_writes ls"
  assume a4: "(x, ba) \<notin> lib_covered ls"
  assume "ver = lib_val (lib_mods ls (x, ba))"
  assume a5: "(x, b) \<notin> lib_covered ls"
  assume a6: "even (lib_val (lib_mods ls (x, ba)))"
  assume a7: "even (lib_val (if b = ts' then \<lparr>lib_val = Suc (lib_val (lib_mods ls (aa, ba))), lib_rel = True\<rparr> else lib_mods ls (x, b)))"
  assume a8: "\<forall>b. (x, b) \<in> lib_writes ls \<and> even (lib_val (lib_mods ls (x, b))) \<and> (x, b) \<notin> lib_covered ls \<longrightarrow> lib_lastWr ls x = (x, b)"
  then have "lib_lastWr ls x = (x, ba)"
    using a6 a4 a1 by blast
  then have "b = ts' \<or> (x, b) = (x, ba)"
    using a8 a7 a5 a3 by presburger
  then show "lib_lastWr (ls\<lparr>lib_thrView := (lib_thrView ls) (t := ts_oride ((lib_thrView ls t)(x := (x, ts'))) (lib_modView ls (x, ba) LVARS)), lib_modView := (lib_modView ls) ((x, ts') := (lib_modView ls (x, ts')) (CVARS := ts_oride (thrView cs t) (lib_modView ls (x, ba) CVARS), LVARS := ts_oride ((lib_thrView ls t)(x := (x, ts'))) (lib_modView ls (x, ba) LVARS))), lib_mods := (lib_mods ls) ((x, ts') := \<lparr>lib_val = Suc (lib_val (lib_mods ls (x, ba))), lib_rel = True\<rparr>), lib_writes := insert (x, ts') (lib_writes ls), lib_covered := insert (x, ba) (lib_covered ls)\<rparr>) x = (x, b)"
    using a7 a6 a2 a1 by simp
qed

lemma lock_release_last: "lib_wfs ls cs \<Longrightarrow> ls' = lock_release t (aa, ba) ls cs ts' \<Longrightarrow>
       lib_valid_fresh_ts ls (aa, ba) ts' \<Longrightarrow>
       (aa, ba) = lib_lastWr ls x \<Longrightarrow> (aa, ts') = lib_lastWr ls' aa"
  apply(simp add:lock_release_def lib_lastWr_def lib_writes_on_def  tst_def var_def)
  apply(simp add: lib_write_def all_updates_l lib_valid_fresh_ts_def)
  apply(elim conjE)
  apply(subgoal_tac "ts'>ba") defer
   apply blast
  apply(subgoal_tac "{w. fst w = x \<and> (w = (x, ts') \<or> w \<in> lib_writes ls)} =
        {w. fst w = x \<and>  w \<in> lib_writes ls} \<union> {(x,ts')}", simp)
  apply(case_tac "ts'\<in>(snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
  apply (smt image_iff less_imp_neq lib_writes_on_def mem_Collect_eq tst_def var_def)
   apply(subgoal_tac "finite {w. fst w = x \<and> w \<in> lib_writes ls}")
  apply (smt Max_in Max_less_iff empty_iff finite_imageI finite_insert infinite_growing insertE insertI1)
   apply(simp add: lib_wfs_def)
   apply (simp add: lib_writes_on_def var_def)
  apply(case_tac "ts'\<in>(snd ` {w. fst w = x \<and> w \<in> lib_writes ls})")
   apply auto[1]
  apply(subgoal_tac "finite {w. fst w = x \<and> w \<in> lib_writes ls}")
  apply simp
  apply auto[1]
   apply(simp add: lib_wfs_def)
   by (simp add: lib_writes_on_def var_def)  


lemma abslock_release_even_not_covered_last_inv:
  assumes "lib_wfs ls cs" 
      and "wfs cs "
      and "even_not_covered_last ls x"
      and "[lib(x) =\<^sub>t u] ls"
      and "odd u"
      and "lock_release_step t x ls cs ls' cs'"
    shows "even_not_covered_last ls' x"
  using assms
  apply(simp add: even_not_covered_last_def lock_release_step_def)
  apply(intro allI impI, elim exE conjE)
  apply(subgoal_tac "(aa, ba) = lib_lastWr ls x")
   defer
  apply(subgoal_tac "aa = x", simp)
    apply (simp add: lib_dobs_visible_writes_last) 
   apply(simp add: lib_visible_writes_def lib_writes_on_def)
  apply(subgoal_tac "lib_value ls (aa, ba) = u") defer
  using lib_dobs_visible_writes apply blast
  apply(subgoal_tac "(aa, ts') = lib_lastWr ls' aa") defer
  using lock_release_last apply blast
  apply(subgoal_tac "aa = x \<and> a = x") defer
  apply(simp add: lib_visible_writes_def lib_writes_on_def lib_lastWr_def)
  apply(case_tac "b = ts'", simp_all)
  apply(simp add: lib_lastWr_def lock_release_def lib_value_def lib_writes_on_def)
  apply(simp add: var_def tst_def lib_visible_writes_def)
  apply(simp add: lib_write_def all_updates_l)
  done



end