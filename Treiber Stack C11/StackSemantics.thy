theory StackSemantics
imports OpSem 
begin

datatype VARS = CVARS | LVARS
datatype OP = INIT | PUSH | POP 

type_synonym OPS = "(OP \<times> TS)"
type_synonym W = "L \<times> TS"

fun isPush :: "OP\<Rightarrow>bool" where
"isPush PUSH = True" |
"isPush _ = False"

fun isPop :: "OP \<Rightarrow>bool" where
"isPop POP = True" |
"isPop _ = False"



record lib_write_record =
  lib_val :: V
  lib_rel :: bool


record ops_record =
  val :: "V"
  op_sync :: "bool"


record stacks_state =
  ops :: "OPS set"
  ops_mods :: "OPS \<Rightarrow> ops_record"
  ops_matched :: "(OPS \<times> OPS) set" 
  ops_thrView :: "T \<Rightarrow> OPS"
  ops_modView_cli :: "OPS \<Rightarrow> L \<Rightarrow> W"


definition "getOp op \<equiv> fst op "
definition "getTs op \<equiv> snd op "

definition "op_value op \<sigma> \<equiv> val (ops_mods \<sigma> op)"




definition "ops_init_matched_pairs \<sigma> \<equiv> {oppair . oppair\<in>ops_matched \<sigma> \<and> getOp (fst oppair) = INIT}"

definition "ops_vts_push t ts' \<sigma> \<equiv> ts' > getTs (ops_thrView \<sigma> t) \<and> ts'\<notin> getTs `ops \<sigma> \<and>
                           (\<forall> oppair . oppair \<in> ops_matched \<sigma> \<longrightarrow>
                                     getTs(fst oppair) > ts' \<or> getTs(snd oppair) < ts')"

definition "ops_vts_pop t ts' \<sigma> \<equiv> ts' > getTs (ops_thrView \<sigma> t) \<and> ts'\<notin> getTs `ops \<sigma> \<and>
                           (\<forall> oppair . oppair \<in> ((ops_matched \<sigma>) - (ops_init_matched_pairs \<sigma>)) \<longrightarrow>
                                     getTs(fst oppair) > ts' \<or> getTs(snd oppair) < ts')"

definition "ops_init \<sigma> \<equiv> {opp. getOp opp = INIT \<and> opp\<in>ops \<sigma>}"
definition "ops_on op \<sigma> \<equiv> {opp . getOp opp = op \<and> opp\<in>ops \<sigma>}"
definition "ops_obs t op \<sigma> \<equiv> {opp. opp\<in>ops_on op \<sigma> \<and> getTs (ops_thrView \<sigma> t) \<le> getTs (opp)}"
definition "ops_mtch_push \<sigma> \<equiv> {opp . getOp opp = PUSH \<and> opp\<in> fst`(ops_matched \<sigma>)}" (*matched (used) pushes*)
definition "ops_up_to_thrView ts' op \<sigma> \<equiv> {opp . opp\<in>ops_on op \<sigma> \<and> getTs opp \<le> ts'}"
definition "ops_last_unmatched_push t ts' luo \<sigma> \<equiv> luo \<in> ((ops_on PUSH \<sigma>) \<union> (ops_init \<sigma>)) \<and> getTs luo = Max (snd`(ops_up_to_thrView ts' PUSH \<sigma>))"
definition "ops_unmatched_push \<sigma> \<equiv> ops_on PUSH \<sigma> - ops_mtch_push \<sigma>"

definition "ops_umatched_upto_ts ts' \<sigma> \<equiv> {opp. opp\<in>ops_unmatched_push \<sigma> \<union> ops_init \<sigma> \<and> getTs opp < ts'}"
definition "lastUnmatchedPush ts' mop \<sigma> \<equiv>  mop\<in>ops_umatched_upto_ts ts' \<sigma> \<and> getTs mop = Max (getTs `(ops_umatched_upto_ts ts' \<sigma>))"


definition "umpbtv t \<sigma> \<equiv> {opp . opp \<in> ((ops_on PUSH \<sigma> - ops_mtch_push \<sigma>) \<union> ops_init \<sigma>)  \<and> getTs opp \<le> getTs (ops_thrView \<sigma> t)}"
definition "last_umpbtv t mop  \<sigma> \<equiv>  mop \<in> umpbtv t \<sigma> \<and> getTs mop = Max (getTs`umpbtv t \<sigma>)"

definition "matchable t \<sigma> \<equiv> {mop . last_umpbtv t mop \<sigma>} \<union> (ops_obs t PUSH \<sigma> - ops_mtch_push \<sigma>)"

definition "op_releasing \<sigma> op \<equiv>  op_sync (ops_mods \<sigma> op)"
definition "op_syncing \<sigma> op b \<equiv>  op_releasing \<sigma> op \<and> b"
definition "lastOp lop \<sigma> \<equiv> lop = (getOp lop, (Max (getTs`(ops \<sigma>))))"

definition "lastPush \<sigma> \<equiv> (PUSH, Max (snd`ops_unmatched_push \<sigma>))"
definition "oneBeforeLastPush \<sigma> \<equiv> (PUSH, Max (snd `(ops_unmatched_push \<sigma> - {lastPush \<sigma>})))"

(*
A PUSH need to be customisable in a way that it can be both releasing/acquiring!!
*)

definition "op_push t v ts sync \<sigma> \<sigma>\<^sub>C \<equiv> \<sigma> \<lparr>ops := ops \<sigma> \<union> {(PUSH, ts)},
                                          ops_mods := (ops_mods \<sigma>)((PUSH,ts):=(ops_mods \<sigma> (PUSH, ts))\<lparr>val :=  v, op_sync:=  sync\<rparr>),
                                          ops_thrView := (ops_thrView \<sigma>)(t := (PUSH, ts)),
                                          ops_modView_cli := (ops_modView_cli \<sigma>)((PUSH, ts) := (thrView \<sigma>\<^sub>C t))\<rparr>"

lemma ops_matched_push: "ops_matched (op_push t v ts sync \<sigma> \<sigma>\<^sub>C) = ops_matched \<sigma>"
  by(simp add: op_push_def)
  
definition "op_pop t mop ts sync \<sigma> \<sigma>\<^sub>C \<equiv> if getOp mop = INIT
                                        then
                                          (\<sigma>\<lparr>ops := ops \<sigma> \<union> {(POP, ts)},
                                           ops_mods := (ops_mods \<sigma>)((POP,ts):=(ops_mods \<sigma> (POP, ts))\<lparr>val := 0, op_sync:= sync\<rparr>),
                                           ops_matched := ops_matched \<sigma> \<union> {(mop, (POP, ts))},
                                           ops_thrView := (ops_thrView \<sigma>)(t :=  (POP, ts)),
                                           ops_modView_cli := (ops_modView_cli \<sigma>)((POP, ts) := (thrView \<sigma>\<^sub>C t))\<rparr>, \<sigma>\<^sub>C)
                                        else 
                                          (\<sigma>\<lparr>ops := ops \<sigma> \<union> {(POP, ts)},
                                           ops_mods := (ops_mods \<sigma>)((POP,ts):=(ops_mods \<sigma> (POP, ts))\<lparr>val := (op_value mop \<sigma>), op_sync:=sync\<rparr>),
                                           ops_matched := ops_matched \<sigma> \<union> {(mop, (POP, ts))},
                                           ops_thrView := (ops_thrView \<sigma>)(t :=  (POP, ts)),
                                           ops_modView_cli := (ops_modView_cli \<sigma>)((POP, ts) := (thrView \<sigma>\<^sub>C t))\<rparr>,
                                           (let new_cli_tv = ts_oride (thrView \<sigma>\<^sub>C t) (ops_modView_cli \<sigma> mop) in
                                             if op_syncing \<sigma> mop sync then \<sigma>\<^sub>C;;update_thrView t new_cli_tv else \<sigma>\<^sub>C))"

definition "push_step t v b \<sigma> \<sigma>\<^sub>C \<sigma>' \<sigma>\<^sub>C' \<equiv> \<exists> ts'.  ops_vts_push t ts' \<sigma>
                              \<and> \<sigma>' = op_push t v ts' b \<sigma> \<sigma>\<^sub>C \<and>  \<sigma>\<^sub>C' =  \<sigma>\<^sub>C" 

definition "pop_step t v b \<sigma> \<sigma>\<^sub>C \<sigma>' \<sigma>\<^sub>C' \<equiv> \<exists> mop ts'.   ops_vts_pop t ts'  \<sigma> \<and> lastUnmatchedPush ts' mop \<sigma> \<and> op_value mop \<sigma> = v
                              \<and> \<sigma>' = fst (op_pop t mop ts' b \<sigma> \<sigma>\<^sub>C) \<and> \<sigma>\<^sub>C' = snd (op_pop t mop ts' b \<sigma> \<sigma>\<^sub>C)"



abbreviation op_push_state_abbr:: "stacks_state \<Rightarrow> surrey_state \<Rightarrow> V \<Rightarrow> bool \<Rightarrow> T \<Rightarrow> stacks_state \<Rightarrow> surrey_state \<Rightarrow> bool" ("_ _ PUSH[_, _]\<^sub>_ _ _" [100,100,100,100,100,100,100])
  where "\<sigma> \<sigma>\<^sub>C PUSH[v, b]\<^sub>t \<sigma>' \<sigma>\<^sub>C' \<equiv> push_step t v b \<sigma> \<sigma>\<^sub>C \<sigma>' \<sigma>\<^sub>C'"

abbreviation  lib_WrR_state_abbr:: "stacks_state \<Rightarrow> surrey_state \<Rightarrow> V => bool \<Rightarrow> T \<Rightarrow> stacks_state \<Rightarrow>surrey_state \<Rightarrow> bool" ("_ _ POP[_, _]\<^sub>_ _ _" [100,100,100,100,100,100])
  where "\<sigma> \<sigma>\<^sub>C POP[v, b]\<^sub>t \<sigma>' \<sigma>\<^sub>C' \<equiv> pop_step t v b \<sigma> \<sigma>\<^sub>C \<sigma>' \<sigma>\<^sub>C'"


definition "p_pop2 \<sigma> t u \<equiv> \<exists> opp. opp \<in> matchable t \<sigma> \<and> u = op_value opp \<sigma>" 

definition "p_pop \<sigma> t u \<equiv> \<exists> opp. opp \<in> ops_unmatched_push \<sigma> \<and> u = op_value opp \<sigma>" 


definition "d_pop t u \<sigma> \<equiv>  lastOp (ops_thrView \<sigma> t) \<sigma> \<and>
                              op_value (ops_thrView \<sigma> t) \<sigma> = u \<and> getOp (ops_thrView \<sigma> t) \<in> {INIT, PUSH}"

definition "c_pop2 \<sigma> \<sigma>\<^sub>C u t y v \<equiv> \<forall> opp . opp \<in> matchable t \<sigma> \<and> u = op_value opp \<sigma> \<longrightarrow>
                d_obs \<sigma>\<^sub>C (ops_modView_cli \<sigma> opp) y v \<and> op_releasing \<sigma>  opp"

definition "c_pop \<sigma> \<sigma>\<^sub>C u t y v \<equiv> \<forall> opp . opp \<in> ops_unmatched_push \<sigma> \<and> u = op_value opp \<sigma> \<longrightarrow>
                d_obs \<sigma>\<^sub>C (ops_modView_cli \<sigma> opp) y v \<and> op_releasing \<sigma>  opp"


definition
  "ops_wfs \<sigma>\<^sub>L \<sigma>\<^sub>C \<equiv> 
          finite (ops \<sigma>\<^sub>L) \<and>
          (\<forall> t .  ops_thrView \<sigma>\<^sub>L t \<in> ops \<sigma>\<^sub>L) \<and>
          fst`(ops_matched \<sigma>\<^sub>L) \<subseteq> ops \<sigma>\<^sub>L \<and>
          snd`(ops_matched \<sigma>\<^sub>L) \<subseteq> ops \<sigma>\<^sub>L \<and>
          (\<forall> op1 op2 . op1 \<in> ops \<sigma>\<^sub>L \<and>  op2 \<in> ops \<sigma>\<^sub>L \<and> getTs op1 = getTs op2
                 \<longrightarrow> getOp op1 = getOp op2) \<and>
          (\<forall> op1 op2. (op1, op2) \<in> ops_matched \<sigma>\<^sub>L \<longrightarrow> getTs op1 < getTs op2) \<and>
          (\<forall> op . lastOp op \<sigma>\<^sub>L \<and> getOp op\<in>{INIT, PUSH} \<longrightarrow> op\<notin>fst`(ops_matched \<sigma>\<^sub>L)) \<and>
          (\<forall> op . op\<in>fst`(ops_matched \<sigma>\<^sub>L) \<longrightarrow> getOp op\<in>{INIT, PUSH}) \<and>
          (\<forall> op . op\<in>snd`(ops_matched \<sigma>\<^sub>L) \<longrightarrow> getOp op\<in>{POP}) \<and>
          (\<forall> op1 op2 . op1 \<in> ops_init \<sigma>\<^sub>L \<and> op2 \<in>ops_init \<sigma>\<^sub>L \<longrightarrow>
                getTs op1 = getTs op2) \<and>
          (\<forall> op opinit . op \<in> ops \<sigma>\<^sub>L \<and> getOp op \<noteq> INIT \<and> opinit \<in> ops_init \<sigma>\<^sub>L
                 \<longrightarrow> getTs op > getTs opinit) \<and>
          (ops_init \<sigma>\<^sub>L \<noteq> {}) \<and>
          (\<forall> op. op \<in> ops_init \<sigma>\<^sub>L \<longrightarrow> op_value op \<sigma>\<^sub>L = 0) \<and>
          (\<forall> x op . ops_modView_cli \<sigma>\<^sub>L op  x \<in> writes_on \<sigma>\<^sub>C x) \<and>
          (finite (ops_matched \<sigma>\<^sub>L))"




definition "cliV_pushes_gt_init \<sigma> \<sigma>\<^sub>C \<equiv> (\<forall>x opi op. opi\<in>ops_init \<sigma> \<and> op\<in>ops_on PUSH \<sigma> \<longrightarrow>  snd ((ops_modView_cli \<sigma> op) x) \<ge> snd ((ops_modView_cli \<sigma> opi) x))"

definition "cliV_init \<sigma> \<sigma>\<^sub>C \<equiv> \<forall> x t opi .  opi\<in>ops_init \<sigma> \<longrightarrow>  snd ((ops_modView_cli \<sigma> opi) x)  \<le> snd (thrView \<sigma>\<^sub>C t x)"

definition "ops_wfs_ext  \<sigma> \<sigma>\<^sub>C \<equiv> cliV_init \<sigma> \<sigma>\<^sub>C \<and> cliV_pushes_gt_init \<sigma> \<sigma>\<^sub>C"


definition "matched_pairs_ts \<sigma> \<equiv> {(a,b) . ((INIT,a) ,(POP,b))\<in>ops_matched \<sigma> \<or> ((PUSH,a) ,(POP,b))\<in>ops_matched \<sigma>}"

lemma "ops_wfs \<sigma> c \<Longrightarrow> 
       op\<in>ops_matched \<sigma> \<Longrightarrow>
       (snd (fst op), snd (snd op))\<in>matched_pairs_ts \<sigma>"
  apply(simp add: matched_pairs_ts_def getTs_def)
  apply(case_tac "getOp (fst op) = INIT")
   apply(intro disjI1)
  apply(unfold ops_wfs_def)[1]
  apply(simp add: getOp_def getTs_def ops_init_def)
   apply (metis   imageI image_subset_iff surjective_pairing)
  apply(subgoal_tac "getOp (fst op) = PUSH") defer
  apply(unfold ops_wfs_def)[1]
   apply(simp add: getOp_def getTs_def ops_init_def) 
  apply (metis image_eqI prod.collapse)
   apply(intro disjI2)
  apply(unfold ops_wfs_def)[1]
  apply(simp add: getOp_def getTs_def ops_init_def)
  by (metis imageI surjective_pairing)


abbreviation d_pop_abbr:: "T \<Rightarrow> nat \<Rightarrow> stacks_state \<Rightarrow> bool" ("[POP =\<^sub>_ _] _" [100, 100, 100])
  where "[POP =\<^sub>t u] \<sigma> \<equiv> d_pop t u \<sigma>"

abbreviation p_pop_abbr:: "T \<Rightarrow> V \<Rightarrow>  stacks_state \<Rightarrow> bool" ("[POP \<approx>\<^sub>_ _] _" [100, 100, 100])
  where "[POP \<approx>\<^sub>t u] \<sigma> \<equiv> p_pop \<sigma> t u"

abbreviation lib_c_obs_abbr:: "V \<Rightarrow>  L \<Rightarrow> T \<Rightarrow> V \<Rightarrow> stacks_state \<Rightarrow> surrey_state \<Rightarrow> bool" ("[POP = _]\<lparr>_ =\<^sub>_ _ \<rparr> _ _" [100, 100, 100,100, 100, 100])
  where "[POP = u]\<lparr>y =\<^sub>t v\<rparr> \<sigma> \<sigma>\<^sub>C \<equiv> c_pop \<sigma> \<sigma>\<^sub>C u t y v"


lemmas all_defs =  d_pop_def   matchable_def ops_obs_def getTs_def  getOp_def  ops_on_def last_umpbtv_def  umpbtv_def 

lemma init_gt: "(\<forall>op opinit.
                op \<in> ops \<sigma> \<and>
                getOp op \<noteq> INIT \<and> opinit \<in> ops \<sigma> \<and> getOp opinit = INIT \<longrightarrow>
                getTs opinit < getTs op) \<Longrightarrow>
                op\<in>ops \<sigma> \<Longrightarrow> getOp op \<noteq> INIT \<Longrightarrow> opi\<in>ops \<sigma> \<Longrightarrow>
                getOp opi = INIT \<Longrightarrow> getTs op > getTs opi" 
          by blast

lemma wfs_ops_wfs_ext_pres:
  assumes "ops_wfs \<sigma> \<sigma>\<^sub>C"
    and "wfs \<sigma>\<^sub>C"
    and "\<sigma> \<sigma>\<^sub>C PUSH[v, b]\<^sub>t \<sigma>' \<sigma>\<^sub>C'" 
    and "ops_wfs_ext  \<sigma> \<sigma>\<^sub>C"
  shows "ops_wfs_ext \<sigma>' \<sigma>\<^sub>C'"
  using assms
  apply(simp add: ops_wfs_ext_def cliV_pushes_gt_init_def cliV_init_def)
  apply(case_tac "ops_on PUSH \<sigma> = {}", simp_all)
  apply(intro  allI impI conjI)
     apply(case_tac "(a, ba) \<in> ops_init \<sigma>") defer
    apply(simp add: ops_wfs_def ops_init_def getOp_def getTs_def push_step_def op_push_def, elim exE conjE, simp)
   apply(simp add: ops_on_def ops_wfs_def ops_init_def getOp_def getTs_def push_step_def op_push_def, elim exE conjE, simp)
   defer
   apply(simp add: ops_on_def ops_wfs_def ops_init_def getOp_def getTs_def push_step_def op_push_def, elim exE conjE, simp)
   apply(intro  allI impI conjI, elim conjE exE)
  apply(case_tac "(a, ba) \<in> ops_init \<sigma>") defer
   apply(simp add: ops_wfs_def ops_init_def getOp_def getTs_def push_step_def op_push_def, elim exE conjE, simp)
  apply(case_tac "(aa, baa) \<in> ops_on PUSH \<sigma>")
   apply(simp add:  ops_init_def getOp_def getTs_def push_step_def op_push_def, elim exE conjE, simp)
   apply(simp add: ops_on_def  ops_init_def getOp_def getTs_def push_step_def op_push_def, elim exE conjE, simp)
  apply(simp add:  push_step_def op_push_def, elim exE conjE)
     apply(simp add:  ops_init_def getOp_def getTs_def push_step_def op_push_def)
  done


lemma wfs_ops_wfs_ext_pop_pres:
  assumes "ops_wfs \<sigma> \<sigma>\<^sub>C"
    and "wfs \<sigma>\<^sub>C"
    and "\<sigma> \<sigma>\<^sub>C POP[v, b]\<^sub>t \<sigma>' \<sigma>\<^sub>C'" 
    and "ops_wfs_ext  \<sigma> \<sigma>\<^sub>C"
  shows "ops_wfs_ext \<sigma>' \<sigma>\<^sub>C'"
  using assms
  apply(simp add: ops_wfs_ext_def cliV_pushes_gt_init_def cliV_init_def)
  apply(case_tac "ops_on PUSH \<sigma> = {}", simp_all)
   apply(intro  allI impI conjI)
  apply(simp add: pop_step_def op_pop_def,elim exE)
    apply(simp add: ops_init_def)
    apply(case_tac "getOp (aa, baa) = INIT", simp_all)
     apply(intro conjI impI)
  apply(simp add: getOp_def)
     apply blast
    apply(case_tac "op_syncing \<sigma> (aa, baa) b", simp_all)
     apply(simp add: rev_app_def update_thrView_def)
  apply(case_tac "a = POP \<and> ba = ts'", simp_all)
      apply (simp add: getOp_def)
     apply(case_tac "ta = t", simp_all)
  apply(intro conjI impI)
  apply blast
      apply (simp add: getOp_def ts_oride_def) 
  using dual_order.trans tst_def apply fastforce
  apply blast
  apply (metis OP.distinct(3) fst_conv getOp_def)
   apply(simp add: pop_step_def op_pop_def,elim exE)
   apply(case_tac "getOp (ab, bb) = INIT", simp_all)
  apply(simp add: ops_init_def ops_on_def)
  apply blast
  apply(simp add: ops_init_def ops_on_def)
   apply blast
  apply(intro conjI impI allI)
   apply(simp add: pop_step_def op_pop_def,elim exE)
  apply(case_tac "getOp (aa, baa) = INIT", simp_all)
  apply(simp add: ops_init_def ops_on_def)
  apply (metis OP.distinct(3) fst_conv getOp_def)
   apply(simp add: ops_init_def ops_on_def)
   apply(case_tac "op_syncing \<sigma> (aa, baa) b", simp_all)
  apply(intro conjI impI)
  apply (simp add: getOp_def)
    apply(simp add: rev_app_def update_thrView_def)
    apply(case_tac "ta = t", simp_all)
  apply(simp add: ts_oride_def getOp_def)
  using dual_order.trans tst_def apply fastforce
  apply blast
  apply (metis OP.distinct(3) fst_conv getOp_def)
  apply(simp add: pop_step_def op_pop_def,elim exE)
  apply(case_tac "getOp (ab, bb) = INIT",simp_all)
   apply(simp add: ops_init_def ops_on_def)
  apply (metis OP.distinct(3) fst_conv getOp_def)
   apply(simp add: ops_init_def ops_on_def)
  by (metis OP.distinct(3) fst_conv getOp_def)


lemma wfs_push_pres:
  assumes "ops_wfs \<sigma> \<sigma>\<^sub>C"
    and "wfs \<sigma>\<^sub>C"
    and "\<sigma> \<sigma>\<^sub>C PUSH[v, b]\<^sub>t \<sigma>' \<sigma>\<^sub>C'" 
  shows "ops_wfs \<sigma>' \<sigma>\<^sub>C'"
  using assms
  apply(simp add: push_step_def op_push_def)
  apply(elim exE conjE)
  apply(unfold ops_wfs_def)
  apply(intro conjI)
  apply simp+
           apply (simp add: subset_insertI2)
  apply simp 
          apply (simp add: subset_Un_eq)
  apply(intro allI impI conjI, simp add: getOp_def getTs_def ops_init_def ops_vts_push_def)
  apply (metis imageI old.prod.inject prod.collapse)
  apply(intro allI impI conjI, simp add: getOp_def getTs_def ops_init_def ops_vts_push_def)
        apply auto[1]
       apply(intro allI impI conjI, elim conjE exE)
       apply(unfold ops_vts_push_def)[1]
       apply(simp add: getOp_def getTs_def ops_init_def ops_vts_push_def lastOp_def)
       apply(elim conjE exE)
(* apply (smt Max.coboundedI Max_eq_if finite_imageI finite_insert image_subset_iff insertE snd_conv subsetD subset_insertI)*)          
       defer
       apply(intro allI impI conjI, elim conjE exE)
       apply(unfold ops_vts_push_def)[1]
       apply(simp add: getOp_def getTs_def ops_init_def ops_vts_push_def lastOp_def)
  apply(elim conjE exE)
  apply (metis prod.collapse)
       apply(intro allI impI conjI, elim conjE exE)
       apply(unfold ops_vts_push_def)[1]
       apply(simp add: getOp_def getTs_def ops_init_def ops_vts_push_def lastOp_def)
      apply(elim conjE exE)
  apply (metis surjective_pairing)
       apply(intro allI impI conjI, elim conjE exE)
       apply(unfold ops_vts_push_def)[1]
       apply(simp add: getOp_def getTs_def ops_init_def ops_vts_push_def lastOp_def)
     apply(elim conjE exE)
     apply auto[1]
    defer
    apply simp
    apply(unfold ops_init_def getOp_def getTs_def)[1]
     apply simp
  apply(intro allI impI)
  apply(simp add:op_value_def ops_init_def)
  apply (metis OP.distinct(1) fst_conv getOp_def prod.collapse)
    apply(intro conjI allI impI)
    apply(unfold  wfs_def)[1]
    apply(elim conjE)
  apply(subgoal_tac "writes_on \<sigma>\<^sub>C' x = writes_on \<sigma>\<^sub>C x", simp)
     apply force
    apply(unfold writes_on_def)[1]
     apply simp
  apply simp
    defer
   apply(intro allI impI, elim conjE)
   apply(simp add: ops_init_def getTs_def getOp_def ops_vts_push_def)
   apply(elim conjE exE)
  apply(case_tac "opinit = (PUSH, ts')")
    apply simp
   apply simp
   apply(case_tac "op \<noteq> (PUSH, ts')")
    apply simp 
  apply auto[1]
   apply simp
   apply(case_tac "(ops_thrView \<sigma> t) = opinit")
    apply blast
   apply(subgoal_tac "snd (ops_thrView \<sigma> t) > snd opinit")
    apply linarith  
   apply (metis prod.collapse)
  apply(case_tac "fst op \<noteq> PUSH", simp_all)
  using assms
  apply safe[1] apply simp_all
  apply (metis (no_types, hide_lams) Max.coboundedI finite.insertI finite_imageI image_subset_iff not_le snd_conv subset_insertI)
  apply clarify
  by (metis (no_types, hide_lams) Max.coboundedI finite.insertI finite_imageI fst_eqD image_subset_iff leD snd_eqD subset_insertI)


lemma lem1: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> ops_vts_pop t ts' \<sigma> \<Longrightarrow>
       lastUnmatchedPush ts' w \<sigma> \<Longrightarrow> getOp w = PUSH \<or> getOp w = INIT "
  apply (simp add: lastUnmatchedPush_def getOp_def ops_umatched_upto_ts_def ops_init_def)
  by (metis (mono_tags, lifting) DiffD1 getOp_def mem_Collect_eq ops_on_def ops_unmatched_push_def)

lemma lem2: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> ops_vts_pop t ts' \<sigma> \<Longrightarrow>
       lastUnmatchedPush ts' w \<sigma> \<Longrightarrow> getTs w < ts'"
  apply (simp add: lastUnmatchedPush_def getOp_def ops_umatched_upto_ts_def ops_init_def)
  done

lemma lem3: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> ops_vts_pop t ts' \<sigma> \<Longrightarrow>
       lastUnmatchedPush ts' (a,b) \<sigma> \<Longrightarrow> getOp (a,b) = PUSH \<Longrightarrow> (c,d)\<in>ops_init \<sigma> \<Longrightarrow> b > d"
  apply (simp add: lastUnmatchedPush_def getOp_def ops_umatched_upto_ts_def ops_init_def)
  apply(simp add:ops_wfs_def getTs_def getOp_def ops_init_def ops_unmatched_push_def)
  by (metis (no_types, lifting) OP.distinct(1) getOp_def mem_Collect_eq old.prod.exhaust old.prod.inject ops_on_def prod.collapse snd_conv)



lemma wfs_pop_pres:
  assumes "ops_wfs \<sigma> \<sigma>\<^sub>C"
    and "wfs \<sigma>\<^sub>C"
    and "\<sigma> \<sigma>\<^sub>C POP[v, b]\<^sub>t \<sigma>' \<sigma>\<^sub>C'" 
  shows "ops_wfs \<sigma>' \<sigma>\<^sub>C'"
  using assms
  apply(simp add: pop_step_def op_pop_def)
  apply(elim exE conjE)
  apply(unfold ops_wfs_def)
  apply(intro conjI; elim conjE exE)
  apply(case_tac "getOp (a, ba) = INIT", simp_all)
             apply(case_tac "getOp (a, ba) = INIT", simp_all)
              apply(intro conjI disjI2)
  apply(simp add: ops_init_def getOp_def getTs_def lastUnmatchedPush_def ops_umatched_upto_ts_def ops_unmatched_push_def ops_on_def, elim exE)
               apply blast
  apply blast
              apply(intro conjI disjI2)
  apply(simp add: ops_init_def getOp_def getTs_def lastUnmatchedPush_def ops_umatched_upto_ts_def ops_unmatched_push_def ops_on_def, elim exE)
               apply blast
  apply blast
            apply blast
  apply(case_tac "getOp (a, ba) = INIT", simp_all)
  apply(intro conjI impI allI, elim exE conjE disjE)
  apply(simp add: getTs_def getOp_def)
              apply(simp add: getTs_def getOp_def ops_vts_pop_def)
  apply (metis image_iff old.prod.inject prod.collapse)
  apply(simp add: getTs_def getOp_def)
               apply(simp add: getTs_def getOp_def ops_vts_pop_def)
             apply (metis image_iff old.prod.inject prod.collapse)
            apply meson
  apply(intro conjI impI allI, elim exE conjE disjE)
  apply(simp add: getTs_def getOp_def)
              apply(simp add: getTs_def getOp_def ops_vts_pop_def)
             apply (metis image_iff old.prod.inject prod.collapse)
              apply(simp add: getTs_def getOp_def ops_vts_pop_def)
            apply (metis image_iff old.prod.inject prod.collapse)
  apply(simp add: getTs_def getOp_def)
  apply(case_tac "getOp (a, ba) = INIT", simp_all)
           apply(simp add: getTs_def getOp_def ops_vts_pop_def lastUnmatchedPush_def ops_init_matched_pairs_def ops_umatched_upto_ts_def)
           apply(simp add: getTs_def getOp_def ops_vts_pop_def lastUnmatchedPush_def ops_init_matched_pairs_def ops_umatched_upto_ts_def)
  apply(case_tac "getOp (a, ba) = INIT", simp_all)
  apply(intro conjI impI allI, elim exE conjE disjE)
           apply(simp add:lastOp_def getTs_def getOp_def ops_vts_pop_def lastUnmatchedPush_def ops_init_matched_pairs_def ops_umatched_upto_ts_def)
 apply(simp add:  ops_unmatched_push_def ops_on_def ops_init_def getOp_def getTs_def )
   (*apply (metis Collect_conv_if Max_less_iff all_not_in_conv empty_is_image ex_in_conv ex_min_if_finite finite.simps finite_imageI getOp_def imageE image_constant image_eqI insertI1 insert_compr insert_not_empty prod.exhaust_sel singleton_conv)*)
  defer
           apply(simp add:lastOp_def getTs_def getOp_def ops_vts_pop_def lastUnmatchedPush_def ops_init_matched_pairs_def ops_umatched_upto_ts_def)
           apply(simp add:lastOp_def getTs_def getOp_def ops_vts_pop_def lastUnmatchedPush_def ops_init_matched_pairs_def ops_umatched_upto_ts_def)
 apply(simp add:  ops_unmatched_push_def ops_on_def ops_init_def getOp_def getTs_def )
  (*apply (smt Max.coboundedI Max_eq_if finite_imageI finite_insert image_iff snd_conv subsetD subset_insertI)*)
           defer
  apply(intro conjI impI allI, elim exE conjE disjE)
           apply(simp add:lastOp_def getTs_def getOp_def ops_vts_pop_def lastUnmatchedPush_def ops_init_matched_pairs_def ops_umatched_upto_ts_def)
            apply(case_tac "op_syncing \<sigma> (a, ba) b",simp_all)
  apply(simp add:lastOp_def getTs_def getOp_def ops_vts_pop_def lastUnmatchedPush_def ops_init_matched_pairs_def ops_umatched_upto_ts_def)
 apply(simp add:  ops_unmatched_push_def ops_on_def ops_init_def getOp_def getTs_def )
  
  (*apply (metis Max_less_iff all_not_in_conv ex_in_conv ex_min_if_finite finite.simps finite_imageI getOp_def imageE image_constant image_constant_conv image_eqI insertCI insert_compr insert_not_empty prod.exhaust_sel singleton_conv)*)
             defer
              apply(simp add: lastOp_def getTs_def getOp_def )
             apply(case_tac "baa\<notin>(snd ` ops \<sigma>)")
              apply(subgoal_tac "baa = ts'")
               apply(simp add: ops_vts_pop_def getTs_def getOp_def ops_init_matched_pairs_def lastUnmatchedPush_def ops_umatched_upto_ts_def)
              apply (meson Max_eq_iff finite.simps finite_imageI insertE insert_not_empty)
             apply simp
             apply(case_tac "ba = baa")
               apply(simp add: ops_vts_pop_def getTs_def getOp_def ops_init_matched_pairs_def lastUnmatchedPush_def ops_umatched_upto_ts_def)
             apply linarith
               apply(simp add: lastOp_def ops_vts_pop_def getTs_def getOp_def ops_init_matched_pairs_def lastUnmatchedPush_def ops_umatched_upto_ts_def)
            apply(simp add: ops_unmatched_push_def ops_init_def getOp_def getTs_def)
  (*apply (smt Max.coboundedI Max_eq_if finite_imageI finite_insert image_iff snd_conv subsetD subset_insertI)*)
            defer
            apply(intro impI)
  apply(simp add:ops_on_def lastUnmatchedPush_def ops_umatched_upto_ts_def ops_unmatched_push_def ops_init_def getOp_def getTs_def)
           apply (metis fst_eqD getOp_def)
          apply(case_tac "getOp (a, ba) = INIT", simp_all)
  apply(simp add: ops_init_def getTs_def getOp_def)
          apply(simp add: ops_init_def getTs_def getOp_def)
          apply(simp add: ops_init_def getTs_def getOp_def)
         apply(intro conjI impI allI)
         apply(case_tac " a = INIT", simp_all)
  apply(simp add: lastUnmatchedPush_def ops_on_def ops_init_def  getOp_def ops_umatched_upto_ts_def ops_unmatched_push_def)
  apply (metis (no_types, hide_lams) getTs_def snd_conv)
         apply(elim conjE exE disjE)
  apply(subgoal_tac "a = PUSH")
  apply(subgoal_tac "ba > bb")
  apply(subgoal_tac "ts' > ba")
  apply linarith
  using lem2
            apply (metis assms(1) getTs_def old.prod.inject prod.collapse)
           apply(subgoal_tac "(INIT, bb)\<in>ops_init \<sigma>")
  using lem3
            apply (metis assms(1) getOp_def old.prod.inject prod.collapse)
           apply(simp add: ops_init_def getOp_def getTs_def)
  using lem1
  
  apply (metis assms(1) fst_conv getOp_def)
         apply simp
        apply(case_tac "getOp (a, ba) = INIT", simp_all)
         apply(simp add: ops_init_def getOp_def getTs_def)
  apply(simp add: ops_init_def getOp_def getTs_def)
        apply(case_tac "getOp (a, ba) = INIT", simp_all)
  apply(simp add: ops_init_def getOp_def getTs_def op_value_def)
  apply(simp add: ops_init_def getOp_def getTs_def op_value_def)
      apply(case_tac "getOp (a, ba) = INIT", simp_all)
      apply(intro allI impI conjI)
       apply(simp add: update_thrView_def rev_app_def)
  apply(unfold wfs_def writes_on_def var_def tst_def)[1]
       apply(simp add: ops_init_def getOp_def getTs_def op_value_def) 
       apply(simp add: update_thrView_def rev_app_def)
      apply(unfold wfs_def writes_on_def var_def tst_def)[1]
      apply(simp add: ops_init_def getOp_def getTs_def op_value_def)
  apply safe[1] apply simp_all 
  apply (metis Max_ge finite.insertI finite_imageI insertI1 leD)
  apply safe[1] apply simp_all 
  apply (smt Max.coboundedI finite_imageI finite_insert fst_conv image_insert insertI1 leD mk_disjoint_insert subset_iff)
  apply clarify
  apply (smt Max.coboundedI finite_imageI finite_insert image_insert insertI1 leD mk_disjoint_insert snd_conv subsetD subset_insertI)
  apply safe[1] apply simp_all 
  apply (metis Max_ge finite.insertI finite_imageI insertI1 leD)
  apply safe[1] apply simp_all 
  apply clarify
  apply (metis (mono_tags, hide_lams) Max.coboundedI finite.insertI finite_imageI image_subset_iff leD snd_conv subset_insertI)
  apply clarify
  by (metis (mono_tags, hide_lams) Max.coboundedI finite.insertI finite_imageI image_subset_iff leD snd_conv subset_insertI)

         
         
lemma d_pops_intro:
  assumes "[POP =\<^sub>t u] \<sigma>"
    and "\<sigma> \<sigma>\<^sub>C PUSH[v, b]\<^sub>t \<sigma>' \<sigma>\<^sub>C'" 
    and "ops_wfs \<sigma> \<sigma>\<^sub>C"
    shows "[POP =\<^sub>t v] \<sigma>'"
  using assms
   apply(simp add: all_defs)
  apply(simp add: lastOp_def)
    apply(simp add:  op_value_def lastOp_def getTs_def getOp_def push_step_def ops_vts_push_def op_push_def) 
  apply(elim exE conjE, intro conjI)
    apply(subgoal_tac "ops \<sigma>' = ops \<sigma> \<union> {(PUSH, ts')}")
     apply(subgoal_tac "Max (snd ` ops \<sigma>) < ts'")
  apply (simp add: ops_wfs_def)
  apply (smt Max_in Max_less_iff finite_imageI finite_insert infinite_growing insertE insertI1 insert_not_empty mk_disjoint_insert)
  apply auto[1]
    apply (simp add: ops_wfs_def)
  apply(subgoal_tac "(ops_thrView \<sigma>' t) = (PUSH, ts')", simp)
   apply auto[1]
  by simp


lemma lastOp_is_lastUnmatched: "ops_wfs \<sigma> \<sigma>c \<Longrightarrow> lastOp op1 \<sigma> \<Longrightarrow> ts'> getTs (ops_thrView \<sigma> t) \<Longrightarrow> getOp op1\<in>{PUSH, INIT} \<Longrightarrow> op1 = ops_thrView \<sigma> t \<Longrightarrow>  op1\<in>ops_umatched_upto_ts ts' \<sigma>"
  apply(simp add: ops_umatched_upto_ts_def)
  apply safe
  apply(simp add: ops_unmatched_push_def ops_on_def ops_wfs_def)
  apply (metis (no_types, lifting) lastOp_def mem_Collect_eq ops_mtch_push_def)
  by (simp add: ops_mtch_push_def ops_wfs_def ops_init_def)  




lemma lastOp_is_lastUnmatchedPush: "ops_wfs \<sigma> \<sigma>c \<Longrightarrow> lastOp op1 \<sigma> \<Longrightarrow> op1 = ops_thrView \<sigma> t \<Longrightarrow> getOp op1\<in>{PUSH, INIT} \<Longrightarrow>
            lastUnmatchedPush ts' op2 \<sigma> \<Longrightarrow> ts' > getTs op1 \<Longrightarrow>  op1 = op2"
  apply(simp add: lastUnmatchedPush_def)
  apply(subgoal_tac "(getOp (ops_thrView \<sigma> t), Max (getTs ` ops \<sigma>)) = op1")
  defer
  apply (simp add: lastOp_def)
  apply(subgoal_tac "op1\<in>ops_umatched_upto_ts ts' \<sigma>")
   defer
   apply (simp add: lastOp_is_lastUnmatched)
  apply(simp add: lastOp_def)
  apply(subgoal_tac " Max (getTs ` ops \<sigma>) \<ge> Max (getTs ` ops_umatched_upto_ts ts' \<sigma>)")
   defer
  apply(simp add: ops_umatched_upto_ts_def ops_unmatched_push_def ops_on_def ops_mtch_push_def ops_wfs_def)
  apply (metis (no_types, lifting) Max_ge finite_imageI image_eqI mem_Collect_eq ops_init_def)
  apply(subgoal_tac "Max (getTs ` ops \<sigma>) \<in> getTs ` ops_umatched_upto_ts ts' \<sigma>")
   defer
  apply (metis (no_types, hide_lams)   getTs_def imageI old.prod.exhaust    snd_conv)
  apply(subgoal_tac "Max (getTs ` ops \<sigma>) = Max (getTs ` ops_umatched_upto_ts ts' \<sigma>)")
   defer
  apply(simp add: ops_wfs_def)
   apply(subgoal_tac "finite (ops_umatched_upto_ts ts' \<sigma>)")
    apply (metis Max.boundedE eq_Max_iff equals0D finite_imageI)
  apply(simp add: ops_umatched_upto_ts_def ops_unmatched_push_def ops_on_def)
  apply(elim conjE)
    apply (smt infinite_super mem_Collect_eq ops_init_def subset_eq)
  apply(subgoal_tac "getTs op1 = getTs op2")
    defer
   apply (metis getTs_def snd_conv)
  apply(subgoal_tac "op2 \<in> ops \<sigma> ") defer
  apply(simp add: ops_umatched_upto_ts_def ops_unmatched_push_def ops_on_def)
   apply (metis (no_types, lifting) mem_Collect_eq ops_init_def)
  apply(subgoal_tac "ops_thrView \<sigma> t \<in> ops \<sigma> ")
   defer
  apply(simp add: ops_wfs_def)
  apply(simp add: ops_wfs_def)
  by (metis getOp_def getTs_def surjective_pairing)

lemma d_pops_lastUnmatchedPush_value:"ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> [POP =\<^sub>t u] \<sigma> \<Longrightarrow> ops_vts_pop t ts'  \<sigma> \<Longrightarrow>  lastUnmatchedPush ts' mop \<sigma>
\<Longrightarrow> op_value mop \<sigma> = u"
  apply(simp add: d_pop_def ops_vts_pop_def)
  apply(subgoal_tac "ops_thrView \<sigma> t = mop")
   apply simp
  apply(elim conjE)
  using lastOp_is_lastUnmatchedPush
  by (simp add: lastOp_is_lastUnmatchedPush insert_commute)


lemma d_pops_pop_val:
  assumes "[POP =\<^sub>t u] \<sigma>"
    and "ops_wfs \<sigma> \<sigma>\<^sub>C"
    and "\<sigma> \<sigma>\<^sub>C POP[v, b]\<^sub>t \<sigma>' \<sigma>\<^sub>C'" 
    shows "v = u"
  using assms
  apply(simp add: pop_step_def op_pop_def)
  apply(elim exE conjE)
  apply (case_tac "getOp (a, ba) = INIT", simp_all)
  apply(subgoal_tac "op_value (a, ba) \<sigma> = u")
  apply linarith
  using d_pops_lastUnmatchedPush_value
  apply (simp add: d_pops_lastUnmatchedPush_value)
  by (meson d_pops_lastUnmatchedPush_value)


lemma l1: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
           ops_vts_push t ts' \<sigma>  \<Longrightarrow>
           \<sigma>' = op_push t v ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
           ops \<sigma>' = ops \<sigma> \<union> {(PUSH, ts')}"
  by(simp add: ops_vts_push_def op_push_def)

lemma l2 [simp]: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
                 ops_vts_push t ts' \<sigma>  \<Longrightarrow>
                 \<sigma>' = op_push t v ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
                 ops_on PUSH  \<sigma>' = ops_on PUSH \<sigma> \<union> {(PUSH, ts')}"
  apply(simp add:  ops_vts_push_def op_push_def ops_on_def getOp_def getTs_def )
  apply(unfold ops_wfs_def, simp)
  by (smt Collect_cong fst_conv insert_compr mem_Collect_eq)


lemma l3 [simp]: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
                  ops_vts_push t ts' \<sigma>  \<Longrightarrow>
                  \<sigma>' = op_push t v ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
                  ops_init  \<sigma>' = ops_init \<sigma>"
  apply(simp add:  ops_vts_push_def op_push_def ops_on_def getOp_def getTs_def ops_init_def)
  apply(unfold ops_wfs_def, simp)
  by (metis OP.distinct(1) fst_eqD)

lemma l4 [simp]: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> 
                  ops_vts_push t ts' \<sigma>  \<Longrightarrow>
                  \<sigma>' = op_push t v ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
                  ops_mtch_push  \<sigma>' = ops_mtch_push \<sigma>"
  apply(simp add:  ops_vts_push_def op_push_def ops_on_def getOp_def getTs_def ops_mtch_push_def)
  done

lemma l5 [simp]: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
               ops_vts_push t ts' \<sigma>  \<Longrightarrow> 
              \<sigma>' = op_push t v ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
               (PUSH, ts') \<in> ops_obs t PUSH \<sigma>'"
  apply(simp add:  ops_vts_push_def op_push_def ops_on_def getOp_def getTs_def ops_mtch_push_def ops_obs_def)
  done

lemma l6:  "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
            ops_vts_push t ts' \<sigma>  \<Longrightarrow>
            \<sigma>' = op_push t v ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
           (PUSH, ts') \<in> matchable t \<sigma>'"
  apply(simp add: ops_vts_push_def op_push_def matchable_def last_umpbtv_def umpbtv_def)
  apply(intro disjI2)
  apply(simp add: ops_mtch_push_def getOp_def getTs_def)
  apply(unfold ops_wfs_def)
  by (metis in_mono rev_image_eqI snd_conv)

lemma l7 [simp]: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> 
                  ops_vts_push t ts' \<sigma>  \<Longrightarrow>
                  \<sigma>' = op_push t v ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow> 
                  ops_thrView \<sigma>' t = (PUSH, ts')"
  apply(simp add:  ops_vts_push_def op_push_def ops_on_def getOp_def getTs_def ops_mtch_push_def ops_obs_def)
  done

lemma l8:  "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
           ops_vts_push t ts' \<sigma>  \<Longrightarrow>
           \<sigma>' = op_push t v ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
           umpbtv t \<sigma> \<subseteq>  umpbtv t \<sigma>' "
  apply(simp add: umpbtv_def)
  apply(subgoal_tac "getTs (ops_thrView \<sigma> t) < getTs (PUSH, ts')")
  defer
  apply(simp add: ops_vts_push_def)
   apply (simp add: getTs_def)
  apply(subgoal_tac "finite (umpbtv t \<sigma>)")
  defer
   apply(simp add:  umpbtv_def ops_on_def ops_mtch_push_def ops_init_def)
  apply(unfold ops_wfs_def)[1]
  using mem_Collect_eq rev_finite_subset subsetI apply force
  by force



lemma l9:  "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
            ops_vts_push t ts' \<sigma>  \<Longrightarrow>
            \<sigma>' = op_push t v ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow> 
           (PUSH, ts') \<in> umpbtv t \<sigma>' "
  apply(simp add: umpbtv_def)
  apply(subgoal_tac "getTs (ops_thrView \<sigma> t) < getTs (PUSH, ts')")
  defer
  apply(simp add: ops_vts_push_def)
   apply (simp add: getTs_def)
  apply(subgoal_tac "finite (umpbtv t \<sigma>)")
  defer
   apply(simp add:  umpbtv_def ops_on_def ops_mtch_push_def ops_init_def)
   apply(unfold ops_wfs_def)[1]
  using mem_Collect_eq rev_finite_subset subsetI
  apply force
  apply(simp add: ops_vts_push_def ops_mtch_push_def)
  apply(intro impI)
   apply(unfold ops_wfs_def)[1]
  by (metis getTs_def imageI old.prod.inject prod.collapse subset_iff)

lemma l10: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
            getOp (ops_thrView \<sigma> t) = PUSH \<Longrightarrow>
            ops_thrView \<sigma> t \<notin> fst`(ops_matched \<sigma>)  \<Longrightarrow> 
            getTs (ops_thrView \<sigma> t) =  Max (getTs `umpbtv t \<sigma>)"
  apply(simp add: umpbtv_def ops_on_def ops_mtch_push_def ops_init_def getTs_def getOp_def)
  apply(subgoal_tac "finite {opp.
          (fst opp = PUSH \<and>
           opp \<in> ops \<sigma> \<and>
           (fst opp = PUSH \<longrightarrow>
            opp \<notin> fst ` ops_matched \<sigma>) \<or>
           fst opp = INIT \<and> opp \<in> ops \<sigma>) \<and>
          snd opp \<le> snd (ops_thrView \<sigma> t)}") defer
  apply(unfold ops_wfs_def)[1]
   apply simp
  apply(subgoal_tac " ops_thrView \<sigma> t \<in> ops \<sigma>")
  defer
  apply(unfold ops_wfs_def)[1]
   apply metis
  apply (simp add:snd_def)
  by (smt Max_eqI finite_imageI image_iff mem_Collect_eq order_refl)


lemma l11:  "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> wfs \<sigma>\<^sub>C \<Longrightarrow>
            \<sigma>\<^sub>C = \<sigma>\<^sub>C' \<Longrightarrow> 
            ops_vts_push t ts' \<sigma>  \<Longrightarrow>
            \<sigma>' = op_push t v ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
            last_umpbtv t (PUSH, ts')  \<sigma>'"
  apply(subgoal_tac "ops_wfs \<sigma>' \<sigma>\<^sub>C'")
  apply(subgoal_tac "ops_thrView \<sigma>' t = (PUSH,ts')")
   apply(subgoal_tac "(PUSH,ts')\<notin> fst`(ops_matched \<sigma>')") 
    apply(simp add: last_umpbtv_def)
    apply (intro conjI)
  using l9 apply blast
  using l10 [where \<sigma> = \<sigma>']  
     apply (smt fst_conv getOp_def l7)
  apply (metis (mono_tags, lifting) Diff_iff OP.distinct(1) Un_iff fstI getOp_def l9 mem_Collect_eq ops_init_def ops_mtch_push_def umpbtv_def)
   apply simp
  apply(unfold ops_wfs_def op_push_def)
  apply(intro conjI)
  apply simp
  apply simp
  apply simp
  apply (simp add: subset_insertI2)
  apply simp
         apply (simp add: subset_insertI2)
  apply(intro conjI allI impI, simp)
  apply (metis getTs_def image_eqI ops_vts_push_def snd_conv surjective_pairing)
  apply(intro conjI allI impI, simp)
       apply (metis prod.collapse)
      apply(intro conjI allI impI, simp)
  apply(unfold  lastOp_def getOp_def getTs_def ops_vts_push_def, simp)[1]
      defer 
        apply(intro conjI allI impI, simp)
  apply (metis old.prod.exhaust)
        apply(intro conjI allI impI, simp)
     apply (metis fst_conv getOp_def  prod.exhaust_sel)
          apply(intro conjI allI impI, simp add: ops_init_def)
  apply (metis OP.distinct(1) fst_conv getOp_def surjective_pairing)
          apply(intro conjI allI impI, simp)
   apply(unfold   getOp_def getTs_def ops_vts_push_def, simp)[1]
   apply clarsimp
    apply(elim disjE)
     apply(simp add: ops_init_def)
  apply (metis OP.distinct(1) dual_order.strict_trans fst_conv getOp_def prod.collapse)
    apply auto[1]
    apply(subgoal_tac "ops_wfs \<sigma> \<sigma>\<^sub>C")
  apply(simp add: ops_init_def)
  apply (metis OP.distinct(1) fst_conv getOp_def)
  apply(unfold ops_wfs_def)[1]
    apply(simp add: ops_init_def)
  apply (metis OP.distinct(1) fst_conv getOp_def)
    apply(unfold ops_init_def getOp_def getTs_def, simp)[1]
   apply(unfold ops_init_def op_value_def getOp_def getTs_def, simp)
   apply clarsimp
  apply(elim conjE )
    apply(subgoal_tac "ops_wfs \<sigma> \<sigma>\<^sub>C")
  apply(unfold ops_wfs_def)[1]
    apply(simp add: ops_init_def getOp_def getTs_def lastOp_def op_value_def)  
  apply(unfold ops_wfs_def)[1]
    apply(simp add: ops_init_def getOp_def getTs_def lastOp_def op_value_def)    
   apply(elim conjE exE)
   defer
  apply(simp add: ops_init_def getOp_def getTs_def lastOp_def op_value_def)  
  apply safe[1] 
   defer
  apply (smt Max.coboundedI finite_imageI finite_insert fst_conv image_insert insert_subset leD mk_disjoint_insert snd_conv subset_insertI)
proof -
  fix a :: OP and ba :: rat and baa :: rat and aa :: OP and bb :: rat and ab :: OP and bc :: rat
  assume "fst (a, Max (insert ts' (snd ` ops \<sigma>))) = INIT"
  assume "a = fst (a, Max (insert ts' (snd ` ops \<sigma>)))"
  assume a1: "(a, Max (insert ts' (snd ` ops \<sigma>))) = fst ((aa, bb), ab, bc)"
  assume a2: "((aa, bb), ab, bc) \<in> ops_matched \<sigma>"
assume a3: "snd ` ops_matched \<sigma> \<subseteq> ops \<sigma>"
assume a4: "finite (ops \<sigma>)"
  assume a5: "\<forall>a b aa ba. ((a, b), aa, ba) \<in> ops_matched \<sigma> \<longrightarrow> b < ba"
  have "bc \<in> snd ` ops \<sigma>"
    using a3 a2 by (metis (no_types) image_iff snd_conv subsetD)
  then show False
    using a5 a4 a2 a1 by (metis Max.coboundedI finite_imageI finite_insert fst_conv insert_iff not_le)
qed

lemma l12:  "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> 
              wfs \<sigma>\<^sub>C \<Longrightarrow>
             \<sigma>\<^sub>C = \<sigma>\<^sub>C' \<Longrightarrow>
             op\<in> ops \<sigma> \<Longrightarrow>
             ops_vts_push t ts' \<sigma>  \<Longrightarrow>
             \<sigma>' = op_push t v ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow> 
             \<not>last_umpbtv t op  \<sigma> \<Longrightarrow>
             \<not>last_umpbtv t op  \<sigma>'"
  apply(simp add: last_umpbtv_def)
  apply(intro impI conjI)
  apply(simp add: ops_vts_push_def getTs_def getOp_def )
  apply(subgoal_tac "Max (snd ` umpbtv t (op_push t v ts' b \<sigma> \<sigma>\<^sub>C')) = ts'")
  apply (metis image_iff)
  by (metis (no_types, lifting) getTs_def image_cong l11 last_umpbtv_def ops_vts_push_def prod.collapse snd_conv)

lemma l13:  "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
             ops_vts_push t ts' \<sigma>  \<Longrightarrow>
             \<sigma>' = op_push t v ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
             op2\<in> umpbtv t \<sigma>' - umpbtv t \<sigma> \<Longrightarrow>
             getTs op2>getTs (ops_thrView \<sigma> t)"
  apply(simp add:  umpbtv_def op_push_def )
  apply(simp add: ops_vts_push_def)
  by (metis getTs_def leI  snd_eqD)



lemma l14:  "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> t \<noteq> t'  \<Longrightarrow> 
             ops_vts_push t' ts' \<sigma>  \<Longrightarrow>
             \<sigma>' = op_push t' v ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
             umpbtv t \<sigma>' \<subseteq> umpbtv t \<sigma> \<union> {(PUSH, ts')} "
  apply(simp add: last_umpbtv_def umpbtv_def op_push_def)
  apply(unfold ops_vts_push_def ops_obs_def, simp)[1]
  by blast

lemma l17:  "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> t \<noteq> t'  \<Longrightarrow>
       ops_vts_push t' ts' \<sigma>  \<Longrightarrow>
       \<sigma>' = op_push t' v ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
       ts' < getTs (ops_thrView \<sigma> t) \<Longrightarrow> 
       umpbtv t \<sigma>' = umpbtv t \<sigma> \<union> {(PUSH, ts')} "
  apply(simp add:  umpbtv_def op_push_def ops_on_def getOp_def getTs_def ops_init_def ops_mtch_push_def)
  apply safe
    apply simp
   apply(unfold ops_wfs_def)[1]
  apply simp
  apply (metis (no_types, hide_lams) fst_conv getTs_def ops_vts_push_def snd_conv sup.strict_coboundedI2 sup.strict_order_iff)
  by simp



lemma umpbtv_not_empty: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> umpbtv t \<sigma> \<noteq> {}"
  apply(simp add:  umpbtv_def )
  apply(unfold ops_wfs_def)[1]
  apply(subgoal_tac "\<exists> a b . (a,b)\<in>ops_init \<sigma>")
  defer
  apply (metis all_not_in_conv  prod.exhaust_sel)
  apply(elim exE)
  apply(rule_tac x = a in exI)
  apply(rule_tac x = b in exI)
  apply(intro conjI)
   apply blast
  apply(unfold ops_init_def)[1]
  by (metis (mono_tags, lifting) less_eq_rat_def mem_Collect_eq)

lemma l16:"ops_wfs \<sigma> \<sigma>c \<Longrightarrow> 
           op\<in>umpbtv t \<sigma> \<Longrightarrow>
           getTs op \<le> getTs (ops_thrView \<sigma> t)"
  apply(simp add:  umpbtv_def)
  done

lemma l18:  "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> t\<noteq>t' \<Longrightarrow>
          ops_vts_push t' ts' \<sigma>  \<Longrightarrow> 
        \<sigma>' = op_push t' v ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
         Max (getTs ` umpbtv t \<sigma>') \<ge> Max (getTs ` umpbtv t \<sigma>) "
  apply(subgoal_tac "umpbtv t \<sigma> \<subseteq> umpbtv t \<sigma>'") defer
  apply(simp add:  umpbtv_def op_push_def)
   apply(unfold ops_vts_push_def, simp)[1]
   apply(simp add: getTs_def ops_on_def)
   apply blast
  apply(subgoal_tac "umpbtv t \<sigma>' \<subseteq> umpbtv t \<sigma> \<union> {(PUSH, ts')}")
  defer
  using l14 apply blast
  apply safe
  apply(subgoal_tac " Max (getTs ` umpbtv t (op_push t' v ts' b \<sigma> \<sigma>\<^sub>C))\<in>getTs ` umpbtv t (op_push t' v ts' b \<sigma> \<sigma>\<^sub>C)")
   defer
   apply(subgoal_tac "finite (getTs `umpbtv t (op_push t' v ts' b \<sigma> \<sigma>\<^sub>C))")
  apply(subgoal_tac "getTs ` umpbtv t (op_push t' v ts' b \<sigma> \<sigma>\<^sub>C) \<noteq> {}")
  using Max_eq_iff apply blast
  using umpbtv_not_empty apply force
   apply(unfold ops_wfs_def)[1]
  apply(simp add:  umpbtv_def op_push_def)
   apply(simp add: getTs_def ops_on_def ops_init_def)
  apply(case_tac "getTs (ops_thrView \<sigma> t) < ts'")
  apply(simp add:  umpbtv_def op_push_def)
  apply(simp add: getTs_def ops_on_def ops_init_def getOp_def ops_mtch_push_def)
  apply (smt Collect_mono_iff eq_iff snd_conv sup.absorb2 sup.strict_order_iff)
  apply(subgoal_tac "getTs (ops_thrView \<sigma> t) \<noteq> ts'")
   apply simp
   defer
   apply(simp add: ops_vts_push_def)
  apply(unfold ops_wfs_def)[1]  
   apply (meson imageI)
  apply(subgoal_tac " getTs (ops_thrView \<sigma> t) > ts'") defer
   apply linarith
  apply(subgoal_tac "getTs (ops_thrView \<sigma> t) \<ge>  Max (getTs ` umpbtv t \<sigma>)", simp_all)
   defer
   apply(subgoal_tac "Max (getTs ` umpbtv t \<sigma>)\<in>getTs ` umpbtv t \<sigma>")
  using l16 apply fastforce
   apply(subgoal_tac "finite (getTs ` umpbtv t \<sigma>)")
   apply(subgoal_tac " (getTs ` umpbtv t \<sigma>) \<noteq> {}") 
  using Max_eq_iff apply blast
  apply (simp add: umpbtv_not_empty)
  apply(unfold ops_wfs_def)[1]  
  apply(simp add:  umpbtv_def op_push_def)
  apply(simp add: getTs_def ops_on_def ops_init_def getOp_def ops_mtch_push_def)
  apply(subgoal_tac "umpbtv t (op_push t' v ts' b \<sigma> \<sigma>\<^sub>C) = insert (PUSH, ts') (umpbtv t \<sigma>)")
   defer
   apply (simp add: l17)
  apply simp
  apply(case_tac "ts' < Max (getTs ` umpbtv t \<sigma>)")
  apply(subgoal_tac "Max (insert (getTs (PUSH, ts')) (getTs ` umpbtv t \<sigma>)) =  Max (getTs ` umpbtv t \<sigma>)")
    apply linarith
  apply(subgoal_tac "finite (getTs ` umpbtv t \<sigma>)")
    apply(subgoal_tac "(getTs ` umpbtv t \<sigma>) \<noteq> {}")
  apply(simp add: getTs_def)
  apply (simp add: umpbtv_not_empty)
   apply (simp add: umpbtv_not_empty)
   apply(unfold ops_wfs_def)[1]  
  apply(unfold  umpbtv_def op_push_def)[1]
   apply(simp add: getTs_def ops_on_def ops_init_def getOp_def ops_mtch_push_def)
 apply(subgoal_tac "Max (insert (getTs (PUSH, ts')) (getTs ` umpbtv t \<sigma>)) = ts'")
  apply linarith
  apply(subgoal_tac "finite (getTs ` umpbtv t \<sigma>)")
    apply(subgoal_tac "(getTs ` umpbtv t \<sigma>) \<noteq> {}")
  apply(simp add: getTs_def)
  apply (simp add: umpbtv_not_empty)
   apply(unfold ops_wfs_def)[1]  
  apply(unfold  umpbtv_def op_push_def)[1]
  apply(simp add: getTs_def ops_on_def ops_init_def getOp_def ops_mtch_push_def)
  done



lemma l20: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
           op \<in> umpbtv t \<sigma> \<Longrightarrow>
           op \<in> umpbtv t \<sigma>' \<Longrightarrow>
           ops_vts_push t' ts' \<sigma>  \<Longrightarrow>
           \<sigma>' = op_push t' v ts' b \<sigma> \<sigma>\<^sub>C  \<Longrightarrow>
           getTs op \<noteq> Max (getTs ` umpbtv t \<sigma>) \<Longrightarrow>
           getTs op < Max (getTs ` umpbtv t \<sigma>)"
  apply(subgoal_tac "finite (getTs ` umpbtv t \<sigma>)")
  apply(simp add:  umpbtv_def op_push_def)
  apply (smt Max_ge mem_Collect_eq rev_image_eqI sup.orderE sup.strict_order_iff)
  apply(unfold  umpbtv_def ops_wfs_def)
  by (simp add: ops_init_def ops_on_def)

lemma s3t: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
            wfs \<sigma>\<^sub>C \<Longrightarrow>
           op\<in>ops \<sigma> \<Longrightarrow>
           op\<in>ops \<sigma>' \<Longrightarrow>
           op\<notin>matchable t \<sigma> \<Longrightarrow>
           ops_vts_push t' ts' \<sigma>  \<Longrightarrow>
           \<sigma>' = op_push t' v ts' b \<sigma> \<sigma>\<^sub>C  \<Longrightarrow>
           op\<notin>matchable t \<sigma>'"
  apply(case_tac "t = t'")
   apply(simp add: matchable_def)
   apply(intro conjI impI; elim conjE)
  using l12 apply blast
   apply(case_tac "op \<in> ops_obs t' PUSH \<sigma>", simp_all)
  apply(simp add: ops_obs_def ops_on_def getTs_def getOp_def)
  apply (metis dual_order.strict_implies_order dual_order.strict_trans getTs_def ops_vts_push_def order.not_eq_order_implies_strict)
   apply(simp add: matchable_def)
  apply(intro conjI impI; elim conjE)
  apply(simp add: last_umpbtv_def)
   defer
  apply(case_tac "op \<in> ops_obs t PUSH \<sigma>", simp_all)
  apply(simp add: last_umpbtv_def umpbtv_def op_push_def)
   apply(unfold ops_vts_push_def ops_obs_def, simp)[1]
   apply (simp add: ops_on_def)
  apply(intro impI)
  apply(case_tac "op \<in> ops_obs t PUSH \<sigma>", simp_all) 
  apply(simp add: last_umpbtv_def umpbtv_def op_push_def)
   apply(unfold ops_vts_push_def ops_obs_def ops_on_def getTs_def getOp_def, simp)[1]
   apply(simp add: ops_init_def getOp_def)
  apply(case_tac "op = (PUSH, ts')")
   apply (metis getTs_def image_eqI ops_vts_push_def snd_conv)
  apply(case_tac " op \<in> umpbtv t \<sigma>", simp_all)
   defer
  apply(subgoal_tac "umpbtv t \<sigma>' \<subseteq> umpbtv t \<sigma> \<union> {(PUSH, ts')}")
  apply auto[1]
  using l14 apply blast
  apply(subgoal_tac "umpbtv t \<sigma>' \<subseteq> umpbtv t \<sigma> \<union> {(PUSH, ts')}") 
   defer
  using l14 apply blast
  apply(subgoal_tac "Max (getTs ` umpbtv t \<sigma>) \<le> Max (getTs ` umpbtv t (op_push t' v ts' b \<sigma> \<sigma>\<^sub>C))")
   defer  apply (simp add: l18)
  apply(subgoal_tac "getTs op \<noteq> ts'") defer
   apply (meson image_iff ops_vts_push_def)
  apply(subgoal_tac "getTs op < Max (getTs ` umpbtv t \<sigma>)") defer
  using l20 apply blast
  by linarith

lemma op_pre_post: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> \<sigma> \<sigma>\<^sub>C PUSH[u, True]\<^sub>t \<sigma>' \<sigma>\<^sub>C' \<Longrightarrow> op\<in>ops \<sigma> \<Longrightarrow> op\<in>ops \<sigma>'"
  apply(simp add:  push_step_def op_push_def op_value_def)
   apply(elim exE)
  by simp

lemma mods_pre: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> ops_vts_push t ts' \<sigma> \<Longrightarrow> \<sigma>' = op_push t u ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow> op\<in>ops \<sigma> \<Longrightarrow> ops_mods \<sigma>' op = ops_mods \<sigma> op"
  apply(simp add:   op_push_def ops_vts_push_def getTs_def getOp_def) 
  apply(intro conjI impI)
  using image_iff by fastforce

lemma value_pre: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> \<sigma> \<sigma>\<^sub>C PUSH[u, True]\<^sub>t \<sigma>' \<sigma>\<^sub>C' \<Longrightarrow> op\<in>ops \<sigma> \<Longrightarrow> op_value op \<sigma> = op_value op \<sigma>'"
  apply(simp add:  push_step_def  op_value_def )
  apply(elim exE conjE)
  apply(subgoal_tac "op\<in>ops \<sigma>'")
   defer
   apply(simp add:  op_pre_post)
  using op_pre_post push_step_def apply blast
  by (simp add: mods_pre)

lemma s33t: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
           op\<notin>ops \<sigma> \<Longrightarrow>
           op\<in>matchable t \<sigma>' \<Longrightarrow>
           ops_vts_push t ts' \<sigma>  \<Longrightarrow>
           \<sigma>' = op_push t v ts' b \<sigma> \<sigma>\<^sub>C  \<Longrightarrow>
           op = (PUSH,ts')"
  apply(simp add: p_pop_def push_step_def op_push_def op_releasing_def matchable_def last_umpbtv_def
      umpbtv_def ops_obs_def ops_on_def)
  using ops_init_def by auto

lemma releasing_ts: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
           ops_vts_push t ts' \<sigma>  \<Longrightarrow>
           \<sigma>' = op_push t v ts' b \<sigma> \<sigma>\<^sub>C  \<Longrightarrow>
           op_releasing \<sigma>' (PUSH, ts') = b"
  apply(simp add:  push_step_def op_push_def op_releasing_def matchable_def last_umpbtv_def)
  done

lemma is_op_releasing: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
          wfs \<sigma>\<^sub>C \<Longrightarrow> u > 0 \<Longrightarrow>
       \<not>[POP \<approx>\<^sub>t' u] \<sigma> \<Longrightarrow>
        \<sigma> \<sigma>\<^sub>C PUSH[u, True]\<^sub>t \<sigma>' \<sigma>\<^sub>C' \<Longrightarrow>
        op \<in> matchable t' \<sigma>' \<Longrightarrow>
       u = op_value op \<sigma>' \<Longrightarrow>
       op_releasing \<sigma>' op"
  apply(subgoal_tac "ops_wfs \<sigma>' \<sigma>\<^sub>C'")
   defer
  using wfs_push_pres apply blast
  apply(case_tac "op \<in> matchable t' \<sigma>")
   apply(simp add: p_pop_def push_step_def op_push_def op_releasing_def)
   apply(elim exE conjE)
   apply(subgoal_tac "op_value op \<sigma>' \<noteq> op_value op \<sigma>")
    apply(subgoal_tac "op\<in>ops \<sigma>")   
     apply (metis Un_empty_right Un_insert_right op_push_def push_step_def value_pre)
    apply(simp add: matchable_def ops_obs_def last_umpbtv_def ops_on_def getOp_def getTs_def ops_mtch_push_def
      umpbtv_def) 
  using ops_init_def apply auto[1]
  apply(subgoal_tac "op \<in> ops_unmatched_push \<sigma>")
    apply (metis old.prod.exhaust op_value_def)
  apply(simp add: matchable_def ops_unmatched_push_def ops_mtch_push_def ops_on_def getOp_def last_umpbtv_def getTs_def ops_obs_def umpbtv_def ops_init_def) 
  apply(intro conjI impI) defer
  apply blast
  apply (metis OP.distinct(1))
  apply(simp add: push_step_def)
  apply(elim exE conjE)
  apply(case_tac "op\<in>ops \<sigma>")
   apply (metis op_pre_post push_step_def s3t)
  apply(subgoal_tac "op = (PUSH, ts')")
  using releasing_ts apply blast
  apply(subgoal_tac "op\<in>ops \<sigma>'")
  apply (metis Un_insert_right insertE l1 sup_bot_right)
  apply(simp add: matchable_def ops_obs_def ops_on_def last_umpbtv_def umpbtv_def getOp_def getTs_def)
  using ops_init_def apply auto[1]
  apply(subgoal_tac "fst op = PUSH")
   apply(unfold ops_wfs_def getTs_def getOp_def ops_init_def ops_on_def)[1] 
   apply blast
  apply(unfold ops_wfs_def)
  apply(elim conjE)
  by (smt getOp_def mem_Collect_eq neq0_conv ops_init_def)




lemma ops_unmatched_push_post: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> ops_vts_push t ts' \<sigma> \<Longrightarrow>  \<sigma>' = op_push t v ts' b \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
ops_unmatched_push \<sigma>' = ops_unmatched_push \<sigma> \<union> {(PUSH, ts')}"
  apply(simp add: ops_unmatched_push_def op_push_def ops_vts_push_def getOp_def getTs_def ops_init_def ops_on_def
ops_mtch_push_def)
  apply(unfold  ops_wfs_def)
  apply(simp add: getOp_def getTs_def ops_init_def lastOp_def)
  apply(elim conjE exE)
  apply(subgoal_tac "(PUSH, ts') \<notin> fst ` ops_matched \<sigma>")
  defer
   apply (metis imageI snd_eqD subset_iff)
  apply(subgoal_tac "(PUSH, ts') \<notin> {opp. fst opp = PUSH \<and> opp \<in> fst ` ops_matched \<sigma>}")
  defer
   apply blast
  apply(subgoal_tac " {opp. fst opp = PUSH \<and> (opp = (PUSH, ts') \<or> opp \<in> ops \<sigma>)} =
          insert (PUSH, ts')
           ({opp. fst opp = PUSH \<and> opp \<in> ops \<sigma>})")
  apply auto[1]
  by auto


lemma ops_unmatched_pops_post: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> getOp mop \<noteq> INIT \<Longrightarrow>  ops_vts_pop t ts'  \<sigma> \<Longrightarrow> lastUnmatchedPush ts' mop \<sigma> \<Longrightarrow> op_value mop \<sigma> = v
                              \<Longrightarrow> \<sigma>' = fst (op_pop t mop ts' b \<sigma> \<sigma>\<^sub>C) \<Longrightarrow> \<sigma>\<^sub>C' = snd (op_pop t mop ts' b \<sigma> \<sigma>\<^sub>C) \<Longrightarrow>
ops_unmatched_push \<sigma>' = ops_unmatched_push \<sigma> - {mop}"
  apply(simp add: ops_unmatched_push_def op_pop_def 
        ops_vts_push_def getOp_def getTs_def ops_init_def ops_on_def
        ops_mtch_push_def)
  apply safe
     apply simp
  apply blast
  apply blast
  by blast


lemma A_sub_b: "a \<in> A \<Longrightarrow> a \<notin> B \<Longrightarrow> A = B \<union> {b} \<Longrightarrow> a = b"
  by simp

lemma push_op_matchable_in_ops_unmatched_push: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>getOp op = PUSH \<Longrightarrow>  op\<in>matchable t \<sigma> \<Longrightarrow> op\<in>ops_unmatched_push \<sigma>"
  apply(simp add:ops_obs_def ops_on_def matchable_def last_umpbtv_def ops_mtch_push_def umpbtv_def ops_init_def getOp_def getTs_def ops_unmatched_push_def)
  by blast

lemma value_gt_zero_not_init: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow> op\<in>ops \<sigma> \<Longrightarrow> op_value op \<sigma> > 0 \<Longrightarrow> getOp op \<noteq> INIT"
  apply(unfold ops_wfs_def getOp_def ops_init_def)
  by (metis (mono_tags, lifting) gr_implies_not0 mem_Collect_eq)


lemma is_op_releasing_unmatched: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
          wfs \<sigma>\<^sub>C \<Longrightarrow> u > 0 \<Longrightarrow>
       \<not>[POP \<approx>\<^sub>t' u] \<sigma> \<Longrightarrow>
        \<sigma> \<sigma>\<^sub>C PUSH[u, True]\<^sub>t \<sigma>' \<sigma>\<^sub>C' \<Longrightarrow>
        op \<in> ops_unmatched_push \<sigma>' \<Longrightarrow>
       u = op_value op \<sigma>' \<Longrightarrow>
       op_releasing \<sigma>' op"
  apply(subgoal_tac "ops_wfs \<sigma>' \<sigma>\<^sub>C'")
   defer
  using wfs_push_pres apply blast
  apply(case_tac "op \<in> ops_unmatched_push \<sigma>")
   apply(simp add: p_pop_def push_step_def op_push_def op_releasing_def)
   apply(elim exE conjE)
   apply(subgoal_tac "op_value op \<sigma>' \<noteq> op_value op \<sigma>")
    apply(subgoal_tac "op\<in>ops \<sigma>")   
     apply (metis Un_empty_right Un_insert_right op_push_def push_step_def value_pre)
    apply(simp add: ops_unmatched_push_def matchable_def ops_obs_def last_umpbtv_def ops_on_def getOp_def getTs_def ops_mtch_push_def
      umpbtv_def) 
  using ops_init_def apply auto[1]
   apply (smt old.prod.exhaust)
  apply(simp add: push_step_def)
  apply(elim exE)
  apply(subgoal_tac "op = (PUSH, ts')", simp)
  using releasing_ts apply blast
  apply(simp add: ops_unmatched_push_def ops_on_def ops_mtch_push_def)
  apply(case_tac "op \<in> ops \<sigma>", simp_all)
   apply (metis ops_matched_push)
  apply(case_tac "getOp op = PUSH", simp_all)
  apply(simp add: op_push_def)
  apply(elim conjE)
     by (metis (no_types, lifting) insert_iff stacks_state.ext_inject stacks_state.surjective stacks_state.update_convs(1) stacks_state.update_convs(2) stacks_state.update_convs(4) stacks_state.update_convs(5))




lemma c_pops_intro:
  assumes "ops_wfs \<sigma> \<sigma>\<^sub>C"
    and "wfs \<sigma>\<^sub>C"
    and "\<not>[POP \<approx>\<^sub>t' u] \<sigma>"
  and "[y =\<^sub>t v] \<sigma>\<^sub>C"
  and "\<sigma> \<sigma>\<^sub>C PUSH[u, True]\<^sub>t \<sigma>' \<sigma>\<^sub>C'" 
  and "u > 0"
shows "[POP = u]\<lparr>y =\<^sub>t' v\<rparr> \<sigma>' \<sigma>\<^sub>C'"
  using assms
    apply(simp add: c_pop_def p_pop_def)
  apply(intro allI conjI impI, elim conjE)
  apply(simp add: push_step_def op_push_def)
  apply(elim exE conjE)
   apply(simp add: d_obs_def)
  defer
    using assms(3) is_op_releasing_unmatched apply blast
  apply(intro conjI) defer
  using d_obs_def d_obs_t_def apply blast
   apply(simp add: d_obs_t_def d_obs_def)
    apply(subgoal_tac "(a, b) = (PUSH, ts')", simp)
  apply (metis (no_types, lifting) fun_upd_same stacks_state.select_convs(5) stacks_state.surjective stacks_state.update_convs(5))
  apply(case_tac "(a, b)\<in>ops_unmatched_push \<sigma>", simp_all)
  apply(subgoal_tac "u = op_value (a, b) \<sigma>")
    apply blast
  apply(subgoal_tac "(a, b) \<in> ops \<sigma>")
  using assms(5) value_pre apply auto[1]
   apply(simp add: ops_unmatched_push_def ops_on_def)
  apply(subgoal_tac "ops_wfs \<sigma>' \<sigma>\<^sub>C'") defer
  using assms(5) wfs_push_pres apply blast
  apply(elim conjE)         
   apply(subgoal_tac "ops_unmatched_push \<sigma>' = ops_unmatched_push \<sigma> \<union> {(PUSH, ts')}") defer
  using ops_unmatched_push_post  assms(5)
    apply (metis Un_commute insert_is_Un op_push_def)
  apply(subgoal_tac "ops_matched \<sigma>' = ops_matched \<sigma>") defer
   apply simp
   apply (metis assms(5) ops_matched_push push_step_def)
  apply(subgoal_tac "(a,b) \<notin> fst` ops_matched \<sigma>'") defer
  apply(simp add: matchable_def last_umpbtv_def ops_mtch_push_def umpbtv_def ops_init_def getOp_def getTs_def)
   apply(case_tac "a = PUSH", simp_all)
  by (smt DiffD1 DiffD2 insertI1 mem_Collect_eq ops_mtch_push_def ops_on_def ops_unmatched_push_def)


lemma lastUnmatchedPush_in_matchable: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
       getOp op \<noteq> INIT \<Longrightarrow>
        ops_vts_pop t ts' \<sigma> \<Longrightarrow>
        lastUnmatchedPush ts' op \<sigma> \<Longrightarrow>
       op \<in> matchable t \<sigma>"
  apply(simp add: ops_vts_pop_def lastUnmatchedPush_def matchable_def)
  apply(elim conjE)
  apply(simp add: ops_umatched_upto_ts_def)
  apply(elim conjE disjE) defer
   apply (simp add: ops_init_def)
  apply(subgoal_tac "getOp op = PUSH") defer
   apply (simp add: ops_on_def ops_unmatched_push_def)
  apply simp
  apply(subgoal_tac "op\<notin>ops_mtch_push \<sigma>") defer
   apply (simp add: ops_unmatched_push_def)
  apply(case_tac "getTs op \<ge> getTs (ops_thrView \<sigma> t)")
   apply (metis (no_types, lifting) DiffD1 mem_Collect_eq ops_obs_def ops_unmatched_push_def)
   apply(intro disjI1 conjI, simp)
   apply(simp add:   last_umpbtv_def umpbtv_def)
   apply(intro conjI)
   apply (simp add: ops_unmatched_push_def)
  apply(simp add: ops_unmatched_push_def ops_mtch_push_def)
  apply(simp add: ops_init_def getOp_def getTs_def ops_on_def)
  apply(subgoal_tac " {opp.
          (fst opp = PUSH \<and>
           opp \<in> ops \<sigma> \<and> (fst opp = PUSH \<longrightarrow> opp \<notin> fst ` ops_matched \<sigma>) \<or>
           fst opp = INIT \<and> opp \<in> ops \<sigma>) \<and>
          snd opp \<le> snd (ops_thrView \<sigma> t)} \<subseteq> {opp.
          (fst opp = PUSH \<and>
           opp \<in> ops \<sigma> \<and> (fst opp = PUSH \<longrightarrow> opp \<notin> fst ` ops_matched \<sigma>) \<or>
           fst opp = INIT \<and> opp \<in> ops \<sigma>) \<and>
          snd opp < ts'}")
  defer
   apply (simp add: Collect_mono_iff)
  apply(elim conjE)
 apply(subgoal_tac " {opp.
          (fst opp = PUSH \<and>
           opp \<in> ops \<sigma> \<and> (fst opp = PUSH \<longrightarrow> opp \<notin> fst ` ops_matched \<sigma>) \<or>
           fst opp = INIT \<and> opp \<in> ops \<sigma>) \<and>
          snd opp \<le> snd (ops_thrView \<sigma> t)} = {opp.
          (fst opp = PUSH \<and>
           opp \<in> ops \<sigma> \<and> (fst opp = PUSH \<longrightarrow> opp \<notin> fst ` ops_matched \<sigma>) \<or>
           fst opp = INIT \<and> opp \<in> ops \<sigma>) \<and>
          snd opp < ts'}")
   defer
   apply safe defer
    apply(unfold ops_wfs_def ops_init_def ops_on_def)[1]
  apply simp
  apply (metis OP.distinct(1)  dual_order.trans  fst_conv getOp_def getTs_def le_cases linear not_le_imp_less not_less_iff_gr_or_eq old.prod.exhaust snd_conv)
   defer
  apply(subgoal_tac "(a, b)\<in>{opp.
                       (fst opp = PUSH \<and>
                        opp \<in> ops \<sigma> \<and>
                        (fst opp = PUSH \<longrightarrow> opp \<notin> fst ` ops_matched \<sigma>) \<or>
                        fst opp = INIT \<and> opp \<in> ops \<sigma>) \<and>
                       snd opp < ts'}")
    apply(subgoal_tac " b \<le> Max (snd `{opp.
                       (fst opp = PUSH \<and>
                        opp \<in> ops \<sigma> \<and>
                        (fst opp = PUSH \<longrightarrow> opp \<notin> fst ` ops_matched \<sigma>) \<or>
                        fst opp = INIT \<and> opp \<in> ops \<sigma>) \<and>
                       snd opp < ts'})")
     defer
  apply(subgoal_tac "finite (snd `{opp.
                       (fst opp = PUSH \<and>
                        opp \<in> ops \<sigma> \<and>
                        (fst opp = PUSH \<longrightarrow> opp \<notin> fst ` ops_matched \<sigma>) \<or>
                        fst opp = INIT \<and> opp \<in> ops \<sigma>) \<and>
                       snd opp < ts'})")  
      apply (metis (no_types, lifting) Max.coboundedI eq_snd_iff image_eqI)
  apply(unfold ops_wfs_def ops_init_def getOp_def getTs_def)[1]  
     apply simp
    apply blast 
  apply simp
  by auto


lemma lastUnmatchedPush_in_ops_unmatched_push: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
       getOp op \<noteq> INIT \<Longrightarrow>
        ops_vts_pop t ts' \<sigma> \<Longrightarrow>
        lastUnmatchedPush ts' op \<sigma> \<Longrightarrow>
       op \<in> ops_unmatched_push \<sigma>"
  apply(simp add: ops_unmatched_push_def lastUnmatchedPush_def) 
  by (simp add: ops_init_def ops_umatched_upto_ts_def ops_unmatched_push_def)

lemma pop_pres_writes_on: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
                           wfs \<sigma>\<^sub>C \<Longrightarrow>
                           \<sigma> \<sigma>\<^sub>C POP[u, True]\<^sub>t \<sigma>' \<sigma>\<^sub>C' \<Longrightarrow> 
                           writes_on \<sigma>\<^sub>C x = writes_on \<sigma>\<^sub>C' x"
  apply(simp add: pop_step_def op_pop_def)
  apply(elim exE conjE)
  apply(case_tac "getOp (a, b) = INIT", simp_all)
  apply(unfold writes_on_def update_thrView_def rev_app_def)[1]
  apply simp
  done


lemma c_pops_transfer:
  assumes "ops_wfs \<sigma> \<sigma>\<^sub>C"
  and "wfs \<sigma>\<^sub>C"
  and "u \<noteq> 0"
  and "[POP = u]\<lparr>y =\<^sub>t v\<rparr> \<sigma> \<sigma>\<^sub>C"
  and "\<sigma> \<sigma>\<^sub>C POP[u, True]\<^sub>t \<sigma>' \<sigma>\<^sub>C'" 
  shows "[y =\<^sub>t v] \<sigma>\<^sub>C'"
  using assms
  apply(simp add: c_pop_def pop_step_def)
  apply(elim exE conjE)
  apply(simp add: d_obs_t_def d_obs_def)
  apply(intro conjI)
   apply(simp add: lastWr_def)
   apply(subgoal_tac "writes_on (snd (op_pop t (a, b) ts' True \<sigma> \<sigma>\<^sub>C)) y = writes_on \<sigma>\<^sub>C y")
  defer
    apply (simp add: op_pop_def)
    apply(case_tac "getOp (a, b) = INIT", simp_all)
    apply(simp add: rev_app_def update_thrView_def)
    apply(unfold writes_on_def)[1]
    apply(case_tac "op_syncing \<sigma> (a, b) True", simp_all)
  defer
   apply (simp add: op_pop_def)
   apply(subgoal_tac "(a, b)\<in>ops \<sigma>")
   apply(case_tac "getOp (a, b) = INIT", simp_all)
  apply(unfold ops_wfs_def)[1]
     apply (simp add: getOp_def ops_init_def)
    apply(case_tac "op_syncing \<sigma> (a, b) True", simp_all)
     apply(simp add: rev_app_def update_thrView_def ts_oride_def)
   apply(subgoal_tac "(a, b) \<in> ops_unmatched_push \<sigma>")
    apply(intro conjI impI)
       apply blast
  using lastUnmatchedPush_in_ops_unmatched_push
  apply(simp add: ts_oride_def lastUnmatchedPush_in_matchable)
     apply (simp add: lastUnmatchedPush_in_ops_unmatched_push)
   apply(subgoal_tac "(a, b) \<in> ops_unmatched_push \<sigma>")
    using op_syncing_def apply blast
      apply (simp add: lastUnmatchedPush_in_ops_unmatched_push)
     apply(case_tac "getOp (a, b) = INIT", simp_all)
    apply(simp add: lastUnmatchedPush_def ops_umatched_upto_ts_def ops_unmatched_push_def ops_init_def)
    apply (simp add: ops_on_def)
    apply(simp add: lastUnmatchedPush_def ops_umatched_upto_ts_def ops_unmatched_push_def ops_init_def)
    apply (simp add: ops_on_def)
    apply(subgoal_tac "(a, b) \<in> ops_unmatched_push \<sigma>")
    apply(simp add: op_pop_def)
     apply(case_tac "getOp (a, b) = INIT", simp_all)
      apply blast
    apply(case_tac "op_syncing \<sigma> (a, b) True", simp_all)
      apply(simp add: rev_app_def update_thrView_def ts_oride_def )
    apply(subgoal_tac "(a, b) \<in> ops_unmatched_push \<sigma>")
       apply simp
    apply(erule_tac x=a in allE)
       apply(erule_tac x=b in allE)
    apply simp
    apply(elim conjE)
       apply (subgoal_tac "lastWr (\<sigma>\<^sub>C\<lparr>thrView := (thrView \<sigma>\<^sub>C)(t := ts_oride (thrView \<sigma>\<^sub>C t) (ops_modView_cli \<sigma> (a, b)))\<rparr>) y = lastWr \<sigma>\<^sub>C y")
        apply simp defer
        apply(simp add: lastWr_def)
    apply(subgoal_tac "writes_on
             (\<sigma>\<^sub>C\<lparr>thrView := (thrView \<sigma>\<^sub>C)
                    (t := ts_oride (thrView \<sigma>\<^sub>C t) (ops_modView_cli \<sigma> (a, b)))\<rparr>)
             y = writes_on \<sigma>\<^sub>C  y", simp)
    using assms(5) pop_pres_writes_on apply blast
    apply blast
      apply blast
    apply(subgoal_tac "getOp (a,b) \<noteq> INIT")
      apply (simp add: lastUnmatchedPush_in_ops_unmatched_push)
    apply(simp add: lastUnmatchedPush_def ops_umatched_upto_ts_def ops_unmatched_push_def ops_on_def)
    apply(unfold ops_wfs_def ops_init_def getOp_def getTs_def)[1]
     apply auto[1]
    apply(simp add:lastWr_def value_def)
    done


lemma d_obs_push_pres:
  assumes "wfs cs"
  and "ops_wfs ls cs"
and "ls cs PUSH[u, b]\<^sub>t' ls' cs'"
and "[x =\<^sub>t v] cs"
shows "[x =\<^sub>t v] cs'"
  using assms
  apply(simp add: push_step_def)
  apply(elim exE)
  apply simp
  done


lemma last_write_write_on [simp]: "wfs \<sigma> \<Longrightarrow>  lastWr \<sigma> x \<in> writes_on \<sigma> x"
  apply(simp add: lastWr_def )
  apply(case_tac "Max (tst`(writes_on \<sigma> x)) \<in> tst`(writes_on \<sigma> x)")
  defer apply simp
  by (auto simp add: tst_def var_def writes_on_def)

lemma last_write_max: "wfs \<sigma> \<Longrightarrow> w \<in> writes_on \<sigma> x \<Longrightarrow> tst w \<le> tst (lastWr \<sigma> x)"
  by(simp add: lastWr_def)

lemma d_obs_lastWr_visible: 
  "wfs \<sigma> \<Longrightarrow> [x =\<^sub>t u] \<sigma> \<Longrightarrow> w \<in> visible_writes \<sigma> t x \<Longrightarrow> w = lastWr \<sigma> x"
  apply (simp add: tst_def d_obs_def d_obs_t_def lastWr_def var_def visible_writes_def, auto)
  by (metis dual_order.antisym lastWr_def last_write_max last_write_write_on prod.collapse tst_def var_def writes_on_var)


lemma d_obs_pop_pres:
  assumes "wfs cs"
  and "ops_wfs ls cs"
and "ls cs POP[u, b]\<^sub>t ls' cs'"
and "[x =\<^sub>t' v] cs"
shows "[x =\<^sub>t' v] cs'"
  using assms
  apply(simp add: d_obs_t_def d_obs_def)
  apply(subgoal_tac "lastWr cs' x = lastWr cs x") defer
   apply(simp add: lastWr_def)
   apply(subgoal_tac "writes_on cs' x = writes_on cs x", simp)
  apply(simp add: pop_step_def op_pop_def rev_app_def)
   apply (smt assms(3) op_syncing_def pop_pres_writes_on snd_conv)
  apply simp
  apply(intro conjI) defer
  apply(simp add: pop_step_def op_pop_def  value_def update_thrView_def rev_app_def lastWr_def)
   apply(elim exE)
   apply(case_tac "op_syncing ls (a, ba) b", simp_all)
  apply(simp add: pop_step_def op_pop_def  value_def update_thrView_def rev_app_def lastWr_def)
  apply(cases b) defer
  apply(simp add: pop_step_def)
   apply(elim exE)
   apply(simp add: d_obs_t_def d_obs_def op_pop_def rev_app_def)
   apply (simp add: op_syncing_def)
  apply(elim conjE)
  apply(simp add: pop_step_def op_pop_def)
   apply(elim exE conjE)
  apply (case_tac "getOp (a, ba) = INIT", simp_all)
  apply(case_tac "op_syncing ls (a, ba) b", simp_all)
  apply(subgoal_tac "ops_modView_cli ls (a, ba) x\<in>writes_on cs x") defer
  apply(unfold ops_wfs_def)[1]
   apply blast
  apply(subgoal_tac "tst(ops_modView_cli ls (a, ba) x) \<le> tst (lastWr cs x)")
   defer
  using last_write_max apply blast
    apply(simp add: update_thrView_def rev_app_def)
  apply(intro impI)
     apply(simp add:  ts_oride_def)
  apply(intro impI)
  apply(unfold wfs_def)[1]
  by (smt assms(1) assms(4) d_obs_lastWr_visible mem_Collect_eq visible_writes_def)

lemma not_p_pops_write_pres:
  assumes "wfs cs"
  and "ops_wfs ls cs"
  and "\<not>[POP \<approx>\<^sub>t' u] ls"
  and "ls' = ls"
and "cs [x := v]\<^sub>t cs'"
shows "\<not>[POP \<approx>\<^sub>t' u] ls'"
  using assms
  apply(simp add: p_pop_def step_def )
  done

lemma not_p_pops_read_pres:
  assumes "wfs cs"
  and "ops_wfs ls cs"
  and "\<not>[POP \<approx>\<^sub>t' u] ls"
and "cs [v \<leftarrow> x]\<^sub>t cs'"
and "ls' = ls"
shows "\<not>[POP \<approx>\<^sub>t' u] ls'"
  using assms
  by auto

lemma mop_pop_not_matchable_post: "ops_wfs \<sigma> \<sigma>\<^sub>C \<Longrightarrow>
      getOp mop = PUSH \<Longrightarrow>
      ops_vts_pop t ts'  \<sigma> \<Longrightarrow> 
      lastUnmatchedPush ts' mop \<sigma> \<Longrightarrow> 
      op_value mop \<sigma> = v \<Longrightarrow>
      \<sigma>' = fst (op_pop t mop ts' b \<sigma> \<sigma>\<^sub>C) \<Longrightarrow>
      \<sigma>\<^sub>C' = snd (op_pop t mop ts' b \<sigma> \<sigma>\<^sub>C) \<Longrightarrow>
      mop\<notin>matchable t \<sigma>'"
  apply(subgoal_tac "mop\<in>matchable t \<sigma>")
  defer 
  apply (simp add: lastUnmatchedPush_in_matchable)
  apply(simp add: op_pop_def matchable_def)
  apply(case_tac "op_syncing \<sigma> mop b", simp_all)
  apply(simp add: last_umpbtv_def umpbtv_def ops_on_def ops_mtch_push_def ops_obs_def ops_init_def)
  apply(simp add: last_umpbtv_def umpbtv_def ops_on_def ops_mtch_push_def ops_obs_def ops_init_def)
  done


lemma ops_on_push_pops_pres: "ops_wfs ls cs \<Longrightarrow> ls cs POP[v , b]\<^sub>t ls' cs' \<Longrightarrow> ops_on PUSH ls = ops_on PUSH ls'"
  apply(simp add: pop_step_def op_pop_def ops_on_def)
  apply(elim conjE exE)
  apply(case_tac "getOp (a, ba) = INIT", simp_all)
  apply(unfold  ops_wfs_def getOp_def getTs_def)
  by auto


lemma ops_obs_subset_pop:  "ops_wfs ls cs \<Longrightarrow> ls cs POP[v , b]\<^sub>t ls' cs' \<Longrightarrow> ops_obs t PUSH ls' \<subseteq> ops_obs t PUSH ls"
  apply(simp add: ops_obs_def)
  apply(subgoal_tac "getTs (ops_thrView ls' t) > getTs (ops_thrView ls t)")
  using ops_on_push_pops_pres apply auto[1]
  apply(simp add: pop_step_def op_pop_def ops_vts_pop_def)
  apply(elim exE conjE)
  apply(case_tac " getOp (a, ba) = INIT", simp_all)
   apply (simp add: getTs_def)
  by (simp add: getTs_def)

lemma ops_mtch_push_subset_pop:  "ops_wfs ls cs \<Longrightarrow>
   ops_vts_pop t ts' ls \<Longrightarrow>
   lastUnmatchedPush ts' mop ls \<Longrightarrow>
   ls' = fst (op_pop t mop ts' b ls cs) \<Longrightarrow> getOp mop = PUSH \<Longrightarrow>
   ops_mtch_push ls' = ops_mtch_push ls \<union> {mop}"
  apply(simp add:  op_pop_def ops_mtch_push_def)
  apply(subgoal_tac "finite({opp. getOp opp = PUSH \<and> opp \<in> fst ` ops_matched ls})")
   apply blast
  apply(unfold ops_wfs_def)
  by (metis (no_types, lifting) mem_Collect_eq rev_finite_subset subset_iff)




lemma not_p_pops_pop_pres:
  assumes "wfs cs"
      and "ops_wfs ls cs"
      and "u \<noteq> 0"
      and "\<not>[POP \<approx>\<^sub>t' u] ls"
      and "ls cs POP[v , b]\<^sub>t ls' cs'"
    shows "\<not>[POP \<approx>\<^sub>t' u] ls'"
  using assms
  apply(simp add: pop_step_def p_pop_def)
  apply(elim exE conjE, intro allI impI)
  apply(case_tac "aa = INIT")
   apply(unfold ops_wfs_def ops_init_def)[1]
   apply(subgoal_tac "(aa, baa) \<in> ops ls")
  apply(subgoal_tac "op_value (aa, baa) ls = op_value (aa, baa) ls'")
     apply (simp add: getOp_def)
    apply(unfold op_pop_def op_value_def getOp_def, simp)[1]
   apply(simp add: matchable_def getOp_def ops_mtch_push_def ops_obs_def ops_on_def getTs_def last_umpbtv_def umpbtv_def op_pop_def op_value_def)
   apply(case_tac "a = INIT", simp_all)
  apply(simp add: ops_init_def getOp_def ops_unmatched_push_def ops_on_def)
  apply(simp add: ops_init_def getOp_def ops_unmatched_push_def ops_on_def)
  apply(unfold ops_wfs_def ops_init_def)[1]
  apply(simp add: ops_unmatched_push_def getOp_def ops_mtch_push_def ops_on_def op_pop_def)
  apply(case_tac " a = INIT", simp_all)
  apply(simp add: op_value_def)
   apply auto[1]
  apply(simp add: op_value_def)
  by auto

lemma p_pops_pop_pres:
  assumes "wfs cs"
  and "ops_wfs ls cs"
and "[POP = u]\<lparr>y =\<^sub>t v\<rparr> ls cs"
and "ls cs POP[z, b]\<^sub>t ls' cs'"
and "u \<noteq> z"
and "u > 0"
and "z > 0"
shows "[POP = u]\<lparr>y =\<^sub>t v\<rparr> ls' cs'"
  using assms
  apply(simp add: c_pop_def pop_step_def )
  apply(elim exE conjE, intro allI impI)
  apply(subgoal_tac "a \<noteq> INIT")
   defer
   apply(simp add: op_pop_def)
   apply safe
    apply(case_tac "getOp (INIT, ba) = INIT", simp_all)
     apply(unfold ops_umatched_upto_ts_def lastUnmatchedPush_def getTs_def ops_mtch_push_def ops_on_def ops_wfs_def ops_init_def getOp_def op_value_def ops_unmatched_push_def)[1]
  apply simp
     apply (metis less_irrefl_nat)
     apply(unfold ops_umatched_upto_ts_def lastUnmatchedPush_def getTs_def ops_mtch_push_def ops_on_def ops_wfs_def ops_init_def getOp_def op_value_def ops_unmatched_push_def)[1]
    apply simp
   apply(subgoal_tac "(ops_modView_cli (fst (op_pop t (a, ba) ts' b ls cs)) (aa, baa)) = (ops_modView_cli ls (aa, baa))") defer
    apply(simp add: op_pop_def getOp_def op_value_def ops_unmatched_push_def ops_on_def)
   defer
   apply(simp add: d_obs_def, intro conjI)
    apply(subgoal_tac " (aa, baa) \<in> ops_unmatched_push ls")
     apply(subgoal_tac " (a, ba) \<in> ops_unmatched_push ls")
    apply(simp add: op_pop_def getOp_def op_value_def ops_unmatched_push_def ops_on_def)
      apply(simp add: lastWr_def update_thrView_def)
  apply (metis (full_types) assms(1) assms(2) assms(4) op_syncing_def pop_pres_writes_on)
      apply(simp add:  ops_unmatched_push_def )
  apply (metis DiffE assms(2) fst_conv getOp_def lastUnmatchedPush_in_ops_unmatched_push ops_unmatched_push_def)
     apply(simp add:  ops_unmatched_push_def )
  apply (metis Diff_iff fst_conv getOp_def ops_unmatched_pops_post ops_unmatched_push_def)
    apply(subgoal_tac " (aa, baa) \<in> ops_unmatched_push ls")
  apply(subgoal_tac " (a, ba) \<in> ops_unmatched_push ls")
    apply(simp add: op_pop_def getOp_def op_value_def ops_unmatched_push_def ops_on_def)
     apply(simp add: lastWr_def update_thrView_def value_def rev_app_def)
     apply(unfold writes_on_def tst_def)[1]
  apply simp
  apply blast
      apply(simp add:  ops_unmatched_push_def )
  apply (metis DiffE assms(2) fst_conv getOp_def lastUnmatchedPush_in_ops_unmatched_push ops_unmatched_push_def)
     apply(simp add:  ops_unmatched_push_def )
   apply (metis Diff_iff fst_conv getOp_def ops_unmatched_pops_post ops_unmatched_push_def)
    apply(subgoal_tac " (aa, baa) \<in> ops_unmatched_push ls")
  apply(subgoal_tac " (a, ba) \<in> ops_unmatched_push ls")
    apply(simp add: op_releasing_def op_pop_def getOp_def op_value_def ops_unmatched_push_def ops_on_def)
  apply (simp add: getOp_def lastUnmatchedPush_in_ops_unmatched_push)
   by (metis Diff_iff fst_conv getOp_def ops_unmatched_pops_post)

lemma p_pops_pop_pres_poped_value_unknown:
  assumes "wfs cs"
  and "ops_wfs ls cs"
and "[POP = u]\<lparr>y =\<^sub>t v\<rparr> ls cs"
and "ls cs POP[z, b]\<^sub>t ls' cs'"
and "u \<noteq> z"
and "u > 0"
shows "[POP = u]\<lparr>y =\<^sub>t v\<rparr> ls' cs'"
  using assms
  apply(simp add: c_pop_def pop_step_def )
  apply(elim exE conjE, intro allI impI)
  apply(case_tac "z \<noteq> 0")
  apply(subgoal_tac "a \<noteq> INIT")
   defer
   apply(simp add: op_pop_def)
   apply safe
    apply(case_tac "getOp (INIT, ba) = INIT", simp_all)
     apply(unfold ops_umatched_upto_ts_def lastUnmatchedPush_def getTs_def ops_mtch_push_def ops_on_def ops_wfs_def ops_init_def getOp_def op_value_def ops_unmatched_push_def)[1]
     apply simp
      apply (metis less_irrefl_nat)
  apply (simp add: ops_vts_pop_def getTs_def)
      apply (simp add: getOp_def)

     apply(unfold ops_umatched_upto_ts_def lastUnmatchedPush_def getTs_def ops_mtch_push_def ops_on_def ops_wfs_def ops_init_def getOp_def op_value_def ops_unmatched_push_def)[1]
    apply simp
   apply(subgoal_tac "(ops_modView_cli (fst (op_pop t (a, ba) ts' b ls cs)) (aa, baa)) = (ops_modView_cli ls (aa, baa))") defer
    apply(simp add: op_pop_def getOp_def op_value_def ops_unmatched_push_def ops_on_def)
   defer
   apply(simp add: d_obs_def, intro conjI)
    apply(subgoal_tac " (aa, baa) \<in> ops_unmatched_push ls")
     apply(subgoal_tac " (a, ba) \<in> ops_unmatched_push ls")
    apply(simp add: op_pop_def getOp_def op_value_def ops_unmatched_push_def ops_on_def)
      apply(simp add: lastWr_def update_thrView_def)
  apply (metis (full_types) assms(1) assms(2) assms(4) op_syncing_def pop_pres_writes_on)
      apply(simp add:  ops_unmatched_push_def )
  apply (metis DiffE assms(2) fst_conv getOp_def lastUnmatchedPush_in_ops_unmatched_push ops_unmatched_push_def)
     apply(simp add:  ops_unmatched_push_def )
  apply (metis Diff_iff fst_conv getOp_def ops_unmatched_pops_post ops_unmatched_push_def)
    apply(subgoal_tac " (aa, baa) \<in> ops_unmatched_push ls")
  apply(subgoal_tac " (a, ba) \<in> ops_unmatched_push ls")
    apply(simp add: op_pop_def getOp_def op_value_def ops_unmatched_push_def ops_on_def)
     apply(simp add: lastWr_def update_thrView_def value_def rev_app_def)
     apply(unfold writes_on_def tst_def)[1]
  apply simp
  apply blast
      apply(simp add:  ops_unmatched_push_def )
  apply (metis DiffE assms(2) fst_conv getOp_def lastUnmatchedPush_in_ops_unmatched_push ops_unmatched_push_def)
     apply(simp add:  ops_unmatched_push_def )
   apply (metis Diff_iff fst_conv getOp_def ops_unmatched_pops_post ops_unmatched_push_def)
  apply (metis (full_types) assms(1) assms(2) assms(3) assms(4) assms(5) assms(6)  c_pop_def  p_pops_pop_pres)
    apply(simp add: op_pop_def getOp_def op_value_def ops_unmatched_push_def ops_on_def)
   apply(simp add: lastWr_def update_thrView_def value_def rev_app_def op_value_def)
  apply(case_tac " a = INIT", simp_all)
    apply auto[1]
   apply safe
    apply(simp add: d_obs_def lastWr_def value_def)
    apply(unfold writes_on_def update_thrView_def rev_app_def op_syncing_def)[1]
  apply clarsimp
  apply(case_tac "op_syncing ls
            (PUSH,
             Max (snd `
                  {opp.
                   (fst opp = PUSH \<and>
                    opp \<in> ops ls \<and>
                    (fst opp = PUSH \<longrightarrow> opp \<notin> fst ` ops_matched ls) \<or>
                    fst opp = INIT \<and> opp \<in> ops ls) \<and>
                   snd opp < ts'}))
            b", simp_all)

  apply(simp add: op_releasing_def op_pop_def getOp_def op_value_def ops_unmatched_push_def ops_on_def)
apply(case_tac "a = INIT", simp_all)
  apply (simp add: ops_mtch_push_def getOp_def lastUnmatchedPush_in_ops_unmatched_push)
    apply blast
  apply (simp add: ops_mtch_push_def getOp_def lastUnmatchedPush_in_ops_unmatched_push)
  by blast


lemma not_p_pops_c_obs: "wfs cs \<Longrightarrow> ops_wfs ls cs \<Longrightarrow> \<not> [POP \<approx>\<^sub>t u] ls \<Longrightarrow>
        [POP = u]\<lparr>x =\<^sub>t v\<rparr> ls cs"
  apply(simp add: p_pop_def c_pop_def)
  apply(intro conjI allI impI)
  apply auto[1]
  by blast

lemma not_p_pops_c_obs_client_write: "wfs cs \<Longrightarrow> ops_wfs ls cs \<Longrightarrow> \<not> [POP \<approx>\<^sub>t u] ls 
      \<Longrightarrow> cs [x := z]\<^sub>t' cs' \<Longrightarrow>  [POP = u]\<lparr>x =\<^sub>t v\<rparr> ls cs'"
  apply(simp add: p_pop_def c_pop_def)
  apply(intro conjI allI impI)
  apply auto[1]
  by blast


end