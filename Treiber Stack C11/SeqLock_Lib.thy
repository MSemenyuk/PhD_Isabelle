theory SeqLock_Lib
  imports Main   Lib_ProofRules AbstractLock_Lib
begin
datatype PC =
  L1
| L2
| L3
| L4


consts t1 :: T 
consts t2 :: T
consts glb :: L
consts l :: L

record prog_state =
  pc :: "T \<Rightarrow> PC"
  r :: "T \<Rightarrow> V"
  loc :: "T \<Rightarrow> bool"

record refinement_rel =
  write_rel :: "(L\<times>TS) \<Rightarrow> (L\<times>TS)"

definition 
  "update_pc t nv pcf \<equiv> pcf (t := nv)"

definition 
  "update_loc t nv pcf \<equiv> pcf (t := nv)"


definition seqLock :: "T \<Rightarrow> prog_state \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> prog_state \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool " where
"seqLock t s ls cs s' ls' cs' \<equiv> 
(
if (pc s) t = L1
then
    ((ls) (cs) [r s' t \<leftarrow> lib(glb)]\<^sub>t (ls') (cs')) \<and>
    (even (r s' t)  \<longrightarrow> pc s' =  update_pc t L2 (pc s)) \<and>
    (\<not>even(r s' t) \<longrightarrow> pc s' =  pc s) \<and>
    (loc s' t  = loc s t) \<and> (\<forall>tt . tt\<noteq>t \<longrightarrow> r s' tt = r s tt)
    \<and> (\<forall>tt . tt\<noteq>t \<longrightarrow> loc s' tt = loc s tt)
else
if (pc s) t = L2
then 
    ((ls) (cs) CAS[lib(glb), loc s' t, (r s t), (r s t + 1)]\<^sub>t (ls') (cs')) \<and>
    (loc s' t \<longrightarrow> pc s' = update_pc t L3 (pc s)) \<and>
    (\<not>loc s' t \<longrightarrow> pc s' = update_pc t L1 (pc s)) \<and>
    (r s' = r s) 
    \<and> (\<forall>tt . tt\<noteq>t \<longrightarrow> loc s' tt = loc s tt)
else
False
)"

definition "seqLock_inv t p ls cs  s \<equiv> 
    (case p of
          L1 \<Rightarrow> True
        | L2 \<Rightarrow> even (r s t)
        | L3 \<Rightarrow> loc s t \<and> even (r s t)
    )
"

definition seqLock_release :: "T \<Rightarrow> prog_state \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> V \<Rightarrow>  prog_state \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool " where
"seqLock_release t s ls cs ver s' ls' cs' \<equiv> 
(
if (pc s) t = L1
then
    ((ls) (cs) [lib(glb) :=\<^sup>R (ver + 1)]\<^sub>t (ls') (cs')) \<and>
    pc s' = update_pc t L2 (pc s)
else
if (pc s) t = L2
then 
      True
else
False
)"

definition "seqLock_release_inv t p ls cs s \<equiv> 
    (case p of
          L1 \<Rightarrow> \<exists> v . ([lib(glb) =\<^sub>t v] ls) \<and> (odd v)
        | L2 \<Rightarrow> True
    )
"

lemma inv:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "seqLock t s ls cs s' ls' cs'"
      and "seqLock_inv t (pc s t) ls cs  s"
    shows "seqLock_inv t (pc s' t) ls' cs'  s'"
  using assms
    apply(simp add: seqLock_def seqLock_inv_def update_pc_def)
    apply(case_tac "pc s t", simp_all)
    apply(case_tac "pc s' t", simp_all)
    apply(simp add: update_pc_def )
    apply safe
    apply simp+
              apply auto
    apply(simp_all add: update_pc_def )
  by (meson PC.distinct(3) fun_upd_eqD)

lemma inv_interf:
  assumes "wfs cs"
      and "lib_wfs ls cs"
      and "seqLock t' s ls cs s' ls' cs'"
      and "seqLock_inv t' (pc s t') ls cs  s"
      and "seqLock_inv t (pc s t) ls cs  s"
    shows "seqLock_inv t (pc s' t) ls' cs'  s'"
  using assms
  apply(case_tac "t = t'", simp_all)
   apply (meson assms(3) inv seqLock_inv_def)
    apply(simp add: seqLock_def seqLock_inv_def update_pc_def)
  apply(cases "pc s t'", simp_all)
  apply(cases "pc s t", simp_all)
      apply(cases "pc s' t", simp_all)
        apply(elim conjE)
    apply(simp_all add: update_pc_def )
  apply auto[1]
  apply auto
  apply(cases "pc s t", simp_all)
  apply presburger
  by presburger


(*Proof of refinement*)

(*
cc = concrete client state
ac = abstract client state
al = abstract lock state
cl = concrete lock state
*)


definition "writes_rel_inv al cl rr \<equiv> \<forall> cw . cw\<in>lib_writes_on cl glb \<longrightarrow>
            (\<exists> aw . aw\<in>lib_writes_on al l \<and>
            tst cw = tst aw \<and>
            lib_modView al aw CVARS = lib_modView cl cw CVARS \<and>
            lib_value al aw = lib_value cl cw \<and>                  
            lib_rel (lib_mods al aw) = lib_rel (lib_mods cl cw) \<and>
            (cw\<in>lib_covered cl \<longrightarrow> aw\<in>lib_covered al)\<and>
            (cw\<notin>lib_covered cl \<longrightarrow> aw\<notin>lib_covered al))"



definition "same_writes al cl rr  \<equiv> tst `lib_writes_on cl glb = tst ` lib_writes_on al l"

definition "thrView_rel al cl t \<equiv> tst (lib_thrView cl t glb) \<ge> tst (lib_thrView al t l)"

definition refinement_rel :: "lib_state \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> surrey_state \<Rightarrow> T \<Rightarrow> refinement_rel \<Rightarrow> bool"
  where "refinement_rel al cl ac cc t rr \<equiv>  writes_rel_inv al cl rr  \<and>
                                               thrView_rel al cl t \<and>
                                               same_writes al cl rr"

lemmas invs =  writes_rel_inv_def thrView_rel_def update_pc_def  
                    seqLock_inv_def   even_not_covered_last_def
                     refinement_rel_def 


lemma not_acquired_sttutering:
  assumes "wfs cc"
  and "wfs ac"
  and "ac = cc"
  and "lib_wfs al ac"
  and "lib_wfs cl cc"
  and "abslock_invs al l"
  and "refinement_rel al cl ac cc t rr"
  and "pc s t = L2"
  and "loc s' t = False"
  and "seqLock_inv t (pc s t) cl cc  s"
  and "seqLock t s cl cc s' cl' cc'"      
  and "al' = al"
  and "ac' = ac"
shows "refinement_rel al' cl' ac' cc' t rr \<and> ac' = cc'"
  using assms
  apply(simp add: refinement_rel_def seqLock_def lib_CAS_step_def)
  apply(elim conjE exE)
  apply(case_tac "lib_value cl (a, b) = r s t", simp_all)
  apply(simp add: lib_read_def all_updates_l)
  apply(intro conjI impI)
  apply(simp add: writes_rel_inv_def)
        apply(intro allI conjI impI)
        apply(simp add: lib_writes_on_def lib_value_def)
        apply(erule_tac x=ba in allE)
        apply(elim conjE, simp)
       apply(simp add: thrView_rel_def ts_oride_def)
       apply (simp_all add: lib_syncing_def)
  apply(simp add: writes_rel_inv_def)
    apply(intro allI conjI impI)
  apply(simp add: lib_writes_on_def)
  apply (metis (no_types, lifting) lib_state.select_convs(4) lib_state.surjective lib_state.update_convs(2) lib_value_def)
  apply(simp add: thrView_rel_def)
   apply(intro allI conjI impI)
   apply(simp add: lib_value_def lib_valid_fresh_ts_def lib_writes_on_def update_pc_def tst_def)
  apply (simp add: lib_visible_writes_def tst_def)
  by(simp add: same_writes_def lib_writes_on_def)

lemma new_state_writes_on: "lib_wfs cl cc \<Longrightarrow> (xc, ts')\<notin>lib_writes_on cl xc \<Longrightarrow> lib_writes_on
        (cl\<lparr>lib_thrView := (lib_thrView cl)
              (t := ts_oride ((lib_thrView cl t)(xc := (xc, ts')))
                     (lib_modView cl (xc, b) LVARS)),
              lib_modView := (lib_modView cl)
                ((xc, ts') := (lib_modView cl (xc, ts'))
                   (CVARS :=
                      ts_oride (thrView cc t)
                       (lib_modView cl (xc, b) CVARS),
                    LVARS :=
                      ts_oride ((lib_thrView cl t)(xc := (xc, ts')))
                       (lib_modView cl (xc, b) LVARS))),
              lib_mods := (lib_mods cl)
                ((xc, ts') :=
                   \<lparr>lib_val = v, lib_rel = bo\<rparr>),
              lib_writes := insert (xc, ts') (lib_writes cl),
              lib_covered := insert (xc, b) (lib_covered cl)\<rparr>)
        xc = lib_writes_on cl xc \<union> {(xc,ts')}"
  apply(simp add: lib_writes_on_def)
  apply(subgoal_tac " {w. fst w = xc \<and> w \<in> lib_writes cl} \<noteq> {}")
  apply(subgoal_tac "finite ( {w. fst w = xc \<and> w \<in> lib_writes cl})")
    apply force
  apply(simp add: lib_wfs_def)
   apply (simp add: lib_writes_on_def var_def) 
  apply(simp add: lib_wfs_def)
   apply (simp add: lib_writes_on_def var_def)
  by (metis eq_fst_iff)




lemma refinement_step_lock_acquired:
  assumes "wfs cc"
  and "wfs ac"
  and "ac = cc"
  and "lib_wfs al ac"
  and "lib_wfs cl cc"
  and "abslock_invs al l"
  and "refinement_rel al cl ac cc t rr"
  and "pc s t = L2"
  and "loc s' t = True"
  and "seqLock_inv t (pc s t) cl cc  s"
  and "seqLock t s cl cc s' cl' cc'"      
shows "\<exists> al' ac' ver rr' . [ac al t LOCKACQ(l) ac' al' True  ver] \<and> refinement_rel al' cl' ac' cc' t rr' \<and> ac'=cc'"
  using assms
  apply (simp add: refinement_rel_def lock_acquire_step_def)
  apply(simp add: seqLock_def lib_CAS_step_def  invs same_writes_def)
  apply(subgoal_tac "\<exists>tt . (tt::T)\<noteq>t") defer
   apply (metis Zero_not_Suc)
  apply(elim exE)
  apply(elim conjE)
  apply(rotate_tac 14)
  apply(erule_tac x = tt in allE, simp)
  apply(rotate_tac 1)
  apply(elim conjE exE)
  apply(subgoal_tac "a = glb", simp)
   defer
   apply (simp add: a_is_x)
  apply(erule_tac x=glb in allE)
  apply(erule_tac x=b in allE, simp)
  apply(subgoal_tac "(glb, b) \<in> lib_writes_on cl glb", simp)
   defer apply(simp add: lib_visible_writes_def)
  apply(elim exE)
  apply(subgoal_tac "aa = l", simp) defer
  apply (metis (mono_tags, hide_lams) a_is_x abslock_invs_def assms(2)  assms(4) assms(6) even_not_covered_last_def lib_last_in_visible_writes )
  apply(elim conjE)
  apply(case_tac "lib_value cl (glb ,b) = r s t", simp_all)
     apply(case_tac "lib_releasing cl (glb, b)")
  apply(rule_tac x = "if lib_releasing cl (glb,b) then
 al\<lparr>lib_thrView := (lib_thrView al)
          (t := ts_oride ((lib_thrView al t)(l := (l, ts')))
                 (lib_modView al (l, b) LVARS)),
          lib_modView := (lib_modView al)
            ((l, ts') := (lib_modView al (l, ts'))
               (CVARS :=
                  ts_oride (thrView cc t)
                   (lib_modView al (l, b) CVARS),
                LVARS :=
                  ts_oride ((lib_thrView al t)(l := (l, ts')))
                   (lib_modView al (l, b) LVARS))),
          lib_mods := (lib_mods al)
            ((l, ts') :=
               \<lparr>lib_val = Suc (lib_value al (l, b)),
                  lib_rel = True\<rparr>),
          lib_writes := insert (l, ts') (lib_writes al),
          lib_covered := insert (l, b) (lib_covered al)\<rparr>
else  al
       \<lparr>lib_thrView := (lib_thrView al)
          (t := (lib_thrView al t)(l := (l, ts'))),
          lib_modView := (lib_modView al)
            ((l, ts') := (lib_modView al (l, ts'))
               (CVARS := thrView cc t,
                LVARS := (lib_thrView al t)(l := (l, ts')))),
          lib_mods := (lib_mods al)
            ((l, ts') := \<lparr>lib_val = Suc (r s t), lib_rel = True\<rparr>),
          lib_writes := insert (l, ts') (lib_writes al),
          lib_covered := insert (l, b) (lib_covered al)\<rparr>" in exI)
         apply(simp add: lib_update_def lock_acquire_def  all_updates_l)
  apply(intro conjI)
     apply(rule_tac x = "lib_value al (l, b)" in exI)
     apply(rule_tac x = "l" in exI)
      apply(rule_tac x = "b" in exI)
  apply(simp_all add: lib_releasing_def)
      apply(intro conjI)
  apply (metis abslock_invs_def even_not_covered_last_def lib_last_in_visible_writes)
  apply(rule_tac x=ts' in exI, intro conjI)
  using new_ts_is_the_same apply blast
      defer
      apply(simp add: lib_writes_on_def lib_value_def)
      apply(intro allI  impI)
  using assms(7)
               apply(simp add: refinement_rel_def writes_rel_inv_def, elim conjE)
  apply(erule_tac x="glb" in allE)
               apply(erule_tac x="ba" in allE)
      apply(simp add: lib_writes_on_def)
  apply(case_tac "(glb, ba) \<in> lib_writes cl", simp_all)
      apply(elim conjE, intro conjI impI)
  apply blast+
      apply (simp add: lib_value_def)
      apply(intro conjI impI, elim conjE)
              apply (simp add:lib_wfs_def subset_iff)
             apply(elim conjE, simp)
             apply(subgoal_tac "(l, ts') \<notin> lib_writes al")
              apply (simp add:lib_wfs_def subset_iff)
            apply force
  apply (smt Collect_cong tst_eq_writes_on)
  apply linarith+
          apply blast+
    apply(simp add: ts_oride_def lib_writes_on_def lib_visible_writes_def)
    apply(intro conjI impI)
  using assms(7) apply(simp add: refinement_rel_def writes_rel_inv_def)
     apply(elim conjE)
  apply(erule_tac x = glb in allE)
     apply(erule_tac x = b in allE)
     apply(subgoal_tac "lib_modView al (l, b) LVARS l = (l,b) \<and>
            lib_modView cl (glb, b) LVARS glb = (glb, b)")
      apply simp
     apply(simp add: lib_wfs_def)
  apply(subgoal_tac "tst (lib_modView al (l, b) LVARS l) =  tst (lib_modView cl (glb, b) LVARS glb)")
     apply linarith
      apply(subgoal_tac "lib_modView al (l, b) LVARS l = (l,b) \<and>
            lib_modView cl (glb, b) LVARS glb = (glb, b)")
      apply simp
    apply(simp add: lib_wfs_def)
   apply(simp add: lib_writes_on_def)
   apply(subgoal_tac "{w. var w = glb \<and> (w = (glb, ts') \<or> w \<in> lib_writes cl)} = {w. var w = glb \<and> (w \<in> lib_writes cl)} \<union> {(glb, ts')}
\<and> {w. var w = l \<and> (w = (l, ts') \<or> w \<in> lib_writes al)} = {w. var w = l \<and> (w \<in> lib_writes al)} \<union> {(l, ts')}")
    apply simp
   apply(intro conjI)
    apply(subgoal_tac "finite ( {w. var w = glb \<and> w \<in> lib_writes cl})")
  apply(simp add: var_def tst_def)
  using Collect_cong apply auto[1]
  apply (metis lib_wfs_def lib_writes_on_def)
    apply(subgoal_tac "finite ( {w. var w = glb \<and> w \<in> lib_writes cl})")
  apply(simp add: var_def tst_def)
  using Collect_cong apply auto[1]
   apply (metis lib_wfs_def lib_writes_on_def)
  using assms(7)
  apply(simp add:refinement_rel_def writes_rel_inv_def, elim conjE)
    apply(erule_tac x=glb in allE)
  apply(erule_tac x=b in allE, simp)
  apply(elim exE conjE)
  apply(subgoal_tac "ab = l", simp)
   defer
  apply (metis Pair_inject abslock_invs_def even_not_covered_last_def)
   apply(rule_tac x = " al
       \<lparr>lib_thrView := (lib_thrView al)
          (t := (lib_thrView al t)(l := (l, ts'))),
          lib_modView := (lib_modView al)
            ((l, ts') := (lib_modView al (l, ts'))
               (CVARS := thrView cc t,
                LVARS := (lib_thrView al t)(l := (l, ts')))),
          lib_mods := (lib_mods al)
            ((l, ts') := \<lparr>lib_val = Suc (r s t), lib_rel = True\<rparr>),
          lib_writes := insert (l, ts') (lib_writes al),
          lib_covered := insert (l, b) (lib_covered al)\<rparr>" in exI)
         apply(simp add: lib_update_def lock_acquire_def  all_updates_l)
  apply(intro conjI)
   apply(simp_all add: lib_releasing_def)
  apply(intro conjI)
     apply(rule_tac x = "lib_value al (l, b)" in exI)
     apply(rule_tac x = "l" in exI)
      apply(rule_tac x = "b" in exI)
    apply(intro conjI, simp_all)
  apply(intro conjI)
  apply (metis abslock_invs_def even_not_covered_last_def lib_last_in_visible_writes)
  apply(rule_tac x=ts' in exI, intro conjI)
  using new_ts_is_the_same apply blast
      defer
      apply(simp add: lib_writes_on_def lib_value_def)
      apply(intro allI  impI)
  using assms(7)
               apply(simp add: refinement_rel_def writes_rel_inv_def)
  apply(erule_tac x="glb" in allE)
               apply(erule_tac x="ba" in allE)
      apply(simp add: lib_writes_on_def)
  apply(case_tac "(glb, ba) \<in> lib_writes cl", simp_all)
      apply(elim conjE, intro conjI impI)
  apply blast+
      apply (simp add: lib_value_def)
      apply(intro conjI impI, elim conjE)
              apply (simp add:lib_wfs_def subset_iff)
             apply(elim conjE, simp)
             apply(subgoal_tac "(l, ts') \<notin> lib_writes al")
              apply (simp add:lib_wfs_def subset_iff)
            apply force
  apply (smt Collect_cong tst_eq_writes_on)
          apply linarith+
  apply blast
          apply blast
          apply blast
          apply blast
          apply blast
          apply blast
    apply(simp add: ts_oride_def lib_writes_on_def lib_visible_writes_def)
   apply(subgoal_tac "{w. var w = glb \<and> (w = (glb, ts') \<or> w \<in> lib_writes cl)} = {w. var w = glb \<and> (w \<in> lib_writes cl)} \<union> {(glb, ts')}
\<and> {w. var w = l \<and> (w = (l, ts') \<or> w \<in> lib_writes al)} = {w. var w = l \<and> (w \<in> lib_writes al)} \<union> {(l, ts')}")
    apply simp
   apply(intro conjI)
    apply(subgoal_tac "finite ( {w. var w = glb \<and> w \<in> lib_writes cl})")
  apply(simp add: var_def tst_def)
  using Collect_cong apply auto[1]
  apply (metis lib_wfs_def lib_writes_on_def)
    apply(subgoal_tac "finite ( {w. var w = glb \<and> w \<in> lib_writes cl})")
  apply(simp add: var_def tst_def)
  using Collect_cong apply auto[1]
   apply (metis lib_wfs_def lib_writes_on_def)
done



(*************Release Operation Refinement**************)


lemma refinement_step_release:
  assumes "wfs cc"
  and "wfs ac"
  and "ac = cc"
  and "lib_wfs al ac"
  and "lib_wfs cl cc"
  and "abslock_invs al l"
  and "refinement_rel al cl ac cc t rr"
  and "[lib(glb) =\<^sub>t ver] cl"
  and "odd ver"
  and "pc s t = L1"
  and "seqLock_release t s cl cc ver s' cl' cc'"      
shows "\<exists> al' ac'  . [ac al t LOCKREL(l) al' ac'] \<and> refinement_rel al' cl' ac' cc' t rr'  \<and>  ac'=cc'"
  using assms
  apply(simp add: seqLock_release_def lock_release_step_def lib_write_step_def refinement_rel_def)
  apply(simp add: lib_write_def  all_updates_l writes_rel_inv_def)
  apply(elim conjE exE)
  apply(rule_tac x = "al
       \<lparr>lib_thrView := (lib_thrView al)
          (t := (lib_thrView al t)(l := (l, ts'))),
          lib_modView := (lib_modView al)
            ((l, ts') := (lib_modView al (l, ts'))
               (CVARS := thrView cc t,
                LVARS := (lib_thrView al t)(l := (l, ts')))),
          lib_mods := (lib_mods al)
            ((l, ts') :=
               \<lparr>lib_val = Suc (lib_value cl (a, b)), lib_rel = True\<rparr>),
          lib_writes := insert (l, ts') (lib_writes al)\<rparr>" in exI)
  apply(intro conjI )
  apply(erule_tac x = a in allE)
     apply(erule_tac x = b in allE)
  apply (simp add: lib_visible_writes_def)
     apply(elim conjE exE)
  apply(subgoal_tac "aa = l", simp) 
  apply(rule_tac x = l in exI)
     apply(rule_tac x = b in exI)
  apply(intro conjI)
        apply blast
  apply (meson order.trans thrView_rel_def)
      apply blast
     apply(rule_tac x = ts' in exI)
     apply(intro conjI)
      apply(simp add: same_writes_def lib_writes_on_def lib_valid_fresh_ts_def)
  apply(intro allI impI)
      apply (smt Collect_cong tst_eq_writes_on_not)
      apply(simp add: lock_release_def lib_write_def all_updates_l)
     apply(simp add: lib_writes_on_def)
    apply(intro allI impI)
     apply(simp add: lib_writes_on_def lib_value_def)
    apply(case_tac "ba = ts'", simp_all)
     apply(case_tac "glb = a", simp_all)
  apply(intro conjI impI)
        apply (metis lib_dobs_visible_writes lib_value_def)
       apply(subgoal_tac "(glb, ts') \<notin> lib_writes cl")
  apply(simp add: lib_wfs_def)
  using subset_iff apply auto[1]
  apply(simp add: lib_valid_fresh_ts_def lib_visible_writes_def lib_writes_on_def)
       apply blast
  apply(elim conjE disjE)
       apply(simp add: same_writes_def lib_writes_on_def var_def tst_def lib_visible_writes_def)
       apply(subgoal_tac "(glb, ts') \<notin> lib_writes cl")
        apply(subgoal_tac "ts' \<notin> snd ` {w. fst w = glb \<and> w \<in> lib_writes cl}")
       apply(subgoal_tac "(l, ts') \<notin> lib_writes al")
  apply(simp add: lib_wfs_def)
   apply auto[1]
   apply (simp add: image_iff)
   using imageE apply force
   apply (simp add: fresh_ts_not_in_writes)
   apply blast
   using a_is_x apply blast
     apply blast
   apply(simp add: thrView_rel_def)
   using a_is_x apply blast
   apply(simp add: same_writes_def lib_writes_on_def tst_def var_def lib_visible_writes_def)
   apply(subgoal_tac "finite {w. fst w = glb \<and> w \<in> lib_writes cl}")
    apply(subgoal_tac "finite {w. fst w = l \<and> w \<in> lib_writes al}")
   apply(subgoal_tac "{w. fst w = glb \<and> (w = (glb, ts') \<or> w \<in> lib_writes cl)} =
        {w. fst w = glb \<and> (w \<in> lib_writes cl)} \<union> {(glb,ts')}")
   apply(subgoal_tac "{w. fst w = l \<and> (w = (l, ts') \<or> w \<in> lib_writes al)} = 
        {w. fst w = l \<and> ( w \<in> lib_writes al)} \<union> {(l,ts')}")
       apply simp_all
   apply (simp add: writes_ts_rewrite)
   apply (simp add: writes_ts_rewrite)
   apply(simp add: lib_wfs_def lib_writes_on_def)
   using var_def apply auto[1]
   apply(simp add: lib_wfs_def lib_writes_on_def)
   using var_def apply auto[1]
   done


end
