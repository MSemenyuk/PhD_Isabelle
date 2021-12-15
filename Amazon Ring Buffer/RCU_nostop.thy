theory RCU_nostop imports RCU_Lems
begin


lemmas rcu_metis = 
OpSemExtProof.c_obs_pres_write_diff_var_ext 
OpSemExtProof.ext_write_other_pres_d_obs 
OpSemExtProof.not_p_obs_other_pres_not_p_obs 
OpSemExtProof.p_obs_contradiction 
OpSem_ProofRules.d_obs_diff_false
getVWNC_var numeral_eq_iff 
semiring_norm(89)
not_p_obs_other_value
neq0_conv
c_obs_write_diff_var_pres 
lessI mod_less 
mod_self 
numeral_2_eq_2
ext_d_obs_rd_pres3 
not_gr_zero 
not_p_obs_value


lemmas rcu_simps =  
OpSem_ProofRules.d_obs_diff_false 
OpSemExtProof.ext_c_obs_rdx_pres 
OpSemExtProof.not_p_obs_other_pres_not_p_obs 
OpSemExtProof.not_p_obs_write_pres_c_obs_diff_var 
OpSemExtProof.read_pres_wfs 
OpSemExtProof.write_pres_wfs 
OpSemExtProof.ext_d_obs_d_obs 
OpSemExtProof.ext_write_other_pres_d_obs
OpSemExtProof.c_obs_read_d_obs
OpSemExtProof.read_pres_d_obs 
OpSemExtProof.d_obs_read_value 
enc_wr_prs 
enc_intro 
enc_rd_prs 
getVWNC_var 
not_p_obs_other_value 
p_obs_contradiction_2
not_p_obs_value 
read_pres_d_obs_other_var 
no_val_read_pres 
no_val_maintain 
getVWNC_var not_p_obs_other_value 
d_vorder_not_pobs 


consts 
  w  :: L
  r :: L
  m  :: L 
  n1 :: L 
  n2 :: L 
  

definition "global s  \<equiv> 
  wfs s \<and> 
  w \<noteq> r \<and> w \<noteq> m \<and> w \<noteq> n1 \<and> w \<noteq> n2
\<and> r \<noteq> m \<and> r \<noteq> n1 \<and> r \<noteq> n2 
\<and> m \<noteq> n1 \<and> m \<noteq> n2
\<and> n1 \<noteq> n2  
"

lemmas opsemsyntax [simp] =  global_def

record RCU =
wr :: V
rr1 :: V
rr2 :: V
a :: nat
mb :: nat
\<sigma> :: surrey_state

(*
definition "r_inv wrv mbv rr1v rr2v av s \<equiv> 
      (\<forall> j. j \<noteq> 0 \<and> j \<noteq> 1 \<longrightarrow> \<not> [ w \<approx>\<^sub>3 j] s) 
     \<and> (\<forall> j. j \<noteq> 1 \<and> j \<noteq> 2 \<longrightarrow> \<not> [ m \<approx>\<^sub>3 j] s) 
     \<and> [ w = 1]\<lparr> w =\<^sub>3 1\<rparr> s 
     \<and> [ w = 1]\<lparr> m =\<^sub>3 (mbv mod 2 + 1)\<rparr> s 
     \<and> ([w \<approx>\<^sub>3 1] s \<longrightarrow> [w =\<^sub>2 1] s) 
     \<and> (rr2v = 1 \<longrightarrow> [ m =\<^sub>3 (mbv mod 2 + 1)] s \<and> [w =\<^sub>3 1] s)
     \<and> ([ r \<approx>\<^sub>2 1] s \<longrightarrow> rr2v = 1)
     \<and> av \<noteq> 0 
     \<and> (mbv = 1 \<or> mbv = 2)
     \<and> ((\<not>[n1 \<approx>\<^sub>3 0] s  \<and> \<not>[n2 \<approx>\<^sub>3 0] s \<and> wrv = 0) \<or> 
          (rr2v = 1 \<and> (mbv = 1 \<longrightarrow> \<not>[n2 \<approx>\<^sub>3 0] s) \<and> (mbv = 2 \<longrightarrow> \<not>[n1 \<approx>\<^sub>3 0] s)))
"
*)

definition "r_inv wrv mbv rr1v rr2v av s \<equiv> 
      (\<forall> j. j \<noteq> 0 \<and> j \<noteq> 1 \<longrightarrow> \<not> [ w \<approx>\<^sub>3 j] s) 
     \<and> (\<forall> j. j \<noteq> 1 \<and> j \<noteq> 2 \<longrightarrow> \<not> [ m \<approx>\<^sub>3 j] s) 
     \<and> [ w = 1]\<lparr> w =\<^sub>3 1\<rparr> s 
     \<and> [ w = 1]\<lparr> m =\<^sub>3 (mbv mod 2 + 1)\<rparr> s 
     \<and> (rr2v = 1 \<longrightarrow> [ m =\<^sub>3 (mbv mod 2 + 1)] s \<and> [w =\<^sub>3 1] s)
     \<and> ([ r \<approx>\<^sub>2 1] s \<longrightarrow> rr2v = 1)
     \<and> av \<noteq> 0 
     \<and> (mbv = 1 \<or> mbv = 2)
     \<and> ((\<not>[n1 \<approx>\<^sub>3 0] s  \<and> \<not>[n2 \<approx>\<^sub>3 0] s \<and> wrv = 0) \<or> 
          (rr2v = 1 \<and> (mbv = 1 \<longrightarrow> \<not>[n2 \<approx>\<^sub>3 0] s) \<and> (mbv = 2 \<longrightarrow> \<not>[n1 \<approx>\<^sub>3 0] s)))
"

lemma RCU:
"
\<parallel>-   \<lbrace>global \<acute>\<sigma> \<and> (\<acute>wr = 0) \<and> (\<acute>rr1 = 0) \<and> (\<acute>rr2 = 0)
       \<and> \<acute>mb \<in> {1, 2} \<and> [ m =\<^sub>2 \<acute>mb]\<acute>\<sigma> \<and> [ m =\<^sub>3 \<acute>mb]\<acute>\<sigma> 
       \<and> \<acute>a \<noteq> 0 
       \<and> \<not>[n1 \<approx>\<^sub>3 0] \<acute>\<sigma> \<and> \<not>[n2 \<approx>\<^sub>3 0] \<acute>\<sigma>
       \<and> [ w =\<^sub>2 0]\<acute>\<sigma> \<and> [ w =\<^sub>3 0]\<acute>\<sigma> \<and> [ r =\<^sub>2 0]\<acute>\<sigma>  \<rbrace>  
COBEGIN
  \<lbrace>global \<acute>\<sigma> 
    \<and> [ w =\<^sub>2 0]\<acute>\<sigma> \<and> \<not> [ w \<approx>\<^sub>3 1]\<acute>\<sigma> \<and> [ m =\<^sub>2 \<acute>mb]\<acute>\<sigma>
    \<and> (\<forall> j. j \<noteq> 0 \<and> j \<noteq> 1 \<longrightarrow> \<not> [ r \<approx>\<^sub>2 j]\<acute>\<sigma>) \<and> \<acute>mb \<in>{1,2} \<rbrace>

  < m :=\<^sub>2 (\<acute>mb mod 2) + 1 \<acute>\<sigma>> ;;

  \<lbrace> global \<acute>\<sigma> 
    \<and> [ w =\<^sub>2 0]\<acute>\<sigma> \<and> \<not> [ w \<approx>\<^sub>3 1]\<acute>\<sigma> \<and> [ m =\<^sub>2 (\<acute>mb mod 2 + 1)]\<acute>\<sigma>
    \<and> (\<forall> j. j \<noteq> 0 \<and> j \<noteq> 1 \<longrightarrow> \<not> [ r \<approx>\<^sub>2 j]\<acute>\<sigma>) \<and> \<acute>mb \<in>{1,2} \<rbrace>
   <w :=\<^sup>R\<^sub>2 1 \<acute>\<sigma>> ;;

   DO \<lbrace> global \<acute>\<sigma> \<and> (\<forall> j. j \<noteq> 0 \<and> j \<noteq> 1 \<longrightarrow> \<not> [ r \<approx>\<^sub>2 j]\<acute>\<sigma>) \<and> \<acute>mb \<in>{1,2}  \<rbrace>
     <\<acute>wr \<leftarrow>\<^sub>2 r\<acute>\<sigma>>
   UNTIL \<acute>wr = 1 
   INV \<lbrace> global \<acute>\<sigma> \<and> (\<forall> j. j \<noteq> 0 \<and> j \<noteq> 1 \<longrightarrow> \<not> [ r \<approx>\<^sub>2 j] \<acute>\<sigma>) \<and> \<acute>mb \<in>{1,2} \<rbrace>
   OD ;;
   \<lbrace> global \<acute>\<sigma> \<and> \<acute>wr = 1 \<and> \<acute>mb \<in>{1,2} \<rbrace>
    IF \<acute>mb = 1 
    THEN  \<lbrace> global \<acute>\<sigma> \<and> \<acute>wr = 1 \<and> \<acute>mb = 1  \<rbrace>
      < n1 :=\<^sub>2 0 \<acute>\<sigma>>   
    ELSE \<lbrace> global \<acute>\<sigma> \<and> \<acute>wr = 1 \<and> \<acute>mb = 2 \<rbrace>
      < n2 :=\<^sub>2 0 \<acute>\<sigma>>   
    FI
   \<lbrace> global \<acute>\<sigma> \<rbrace>

  \<parallel> 

  \<lbrace> global \<acute>\<sigma> 
     \<and> (\<forall> j. j \<noteq> 0 \<and> j \<noteq> 1 \<longrightarrow> \<not> [ w \<approx>\<^sub>3 j]\<acute>\<sigma>) 
     \<and> (\<forall> j. j \<noteq> 1 \<and> j \<noteq> 2 \<longrightarrow> \<not> [ m \<approx>\<^sub>3 j]\<acute>\<sigma>)
     \<and> \<not> [ r \<approx>\<^sub>2 1]\<acute>\<sigma> 
     \<and> [ w = 1]\<lparr> w =\<^sub>3 1\<rparr>\<acute>\<sigma> \<and> [ w = 1]\<lparr> m =\<^sub>3 (\<acute>mb mod 2 + 1)\<rparr> \<acute>\<sigma>
     \<and> ([w \<approx>\<^sub>3 1]\<acute>\<sigma> \<longrightarrow> [w =\<^sub>2 1]\<acute>\<sigma>)
     \<and> \<acute>rr1 = 0 \<and> \<acute>rr2 = 0  \<and> \<acute>wr = 0 \<and> \<acute>mb \<in> {1, 2}  
     \<and> \<acute>a \<noteq> 0 
     \<and> \<not>[n1 \<approx>\<^sub>3 0] \<acute>\<sigma> \<and> \<not>[n2 \<approx>\<^sub>3 0] \<acute>\<sigma>\<rbrace>
  
  WHILE \<acute>rr2 = 0 INV 
  \<lbrace> global \<acute>\<sigma> \<and> r_inv \<acute>wr \<acute>mb \<acute>rr1 \<acute>rr2 \<acute>a \<acute>\<sigma> \<rbrace>  
  DO
    \<lbrace> global \<acute>\<sigma> \<and> r_inv \<acute>wr \<acute>mb \<acute>rr1 \<acute>rr2 \<acute>a \<acute>\<sigma> \<rbrace>
      <\<acute>rr1 \<leftarrow>\<^sub>3 m \<acute>\<sigma>> ;; 
    \<lbrace> global \<acute>\<sigma> \<and> r_inv \<acute>wr \<acute>mb \<acute>rr1 \<acute>rr2 \<acute>a \<acute>\<sigma>
      \<and> (\<acute>rr2 = 1 \<longrightarrow> \<acute>rr1 = (\<acute>mb mod 2) + 1)
      \<and> (\<acute>rr1 = 1 \<or> \<acute>rr1 = 2)
      \<rbrace>

    IF \<acute>rr1 = 1 
    THEN  \<lbrace> global \<acute>\<sigma> \<and> r_inv \<acute>wr \<acute>mb \<acute>rr1 \<acute>rr2 \<acute>a \<acute>\<sigma>
      \<and> (\<acute>rr2 = 1 \<longrightarrow> \<acute>rr1 = (\<acute>mb mod 2) + 1)
      \<and> \<acute>rr1 = 1\<rbrace>
      <\<acute>a \<leftarrow>\<^sub>3 n1 \<acute>\<sigma>>   
    ELSE \<lbrace> global \<acute>\<sigma> \<and> r_inv \<acute>wr \<acute>mb \<acute>rr1 \<acute>rr2 \<acute>a \<acute>\<sigma>
      \<and> (\<acute>rr2 = 1 \<longrightarrow> \<acute>rr1 = (\<acute>mb mod 2) + 1)
      \<and> \<acute>rr1 = 2\<rbrace>
      <\<acute>a \<leftarrow>\<^sub>3 n2 \<acute>\<sigma>>   
    FI ;;
  
    \<lbrace> global \<acute>\<sigma> \<and> r_inv \<acute>wr \<acute>mb \<acute>rr1 \<acute>rr2 \<acute>a \<acute>\<sigma> \<rbrace>

     <\<acute>rr2 \<leftarrow>\<^sup>A\<^sub>3 w \<acute>\<sigma>>;;

    \<lbrace> global \<acute>\<sigma> \<and> r_inv \<acute>wr \<acute>mb \<acute>rr1 \<acute>rr2 \<acute>a \<acute>\<sigma> \<and> (\<acute>rr2 = 0 \<or> \<acute>rr2 = 1)  \<rbrace>

    <r :=\<^sub>3 \<acute>rr2 \<acute>\<sigma>>   
  OD
  \<lbrace> global \<acute>\<sigma>  \<and> \<acute>a \<noteq> 0
 \<rbrace>

COEND 
  \<lbrace>\<acute>a \<noteq> 0 \<rbrace>
"  
  apply (oghoare; (simp add: rcu_simps r_inv_def Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff )?; clarify)  
  apply (auto simp add: rcu_simps)[2]
  apply linarith
  apply (smt OpSemExtProof.p_obs_contradiction d_obs_value ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 not_p_obs_value)
  apply (metis Suc_inject OpSemExtProof.ext_d_obs_d_obs OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs)
  apply (metis One_nat_def OpSemExtProof.p_obs_contradiction bits_one_mod_two_eq_one ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 neq0_conv not_p_obs_value numeral_2_eq_2)
  apply (metis OpSemExtProof.p_obs_contradiction ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 mod_self neq0_conv not_p_obs_value)
  apply (smt OpSemExtProof.c_obs_read_d_obs OpSemExtProof.c_obs_read_pres OpSemExtProof.p_obs_contradiction d_obs_value ext_d_obs_rd_pres3 not_gr_zero not_p_obs_value)
  apply (smt OpSemExtProof.c_obs_pres_write_diff_var_ext OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs getVWNC_var numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (metis OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs getVWNC_var neq0_conv numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (metis OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs getVWNC_var neq0_conv numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (metis getVWNC_var neq0_conv numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (metis getVWNC_var neq0_conv numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (metis getVWNC_var neq0_conv numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (metis getVWNC_var neq0_conv numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (smt One_nat_def OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs bits_one_mod_two_eq_one c_obs_write_diff_var_pres getVWNC_var mod_self numeral_2_eq_2 numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (metis OpSemExtProof.ext_c_obs_intro OpSemExtProof.ext_d_obs_d_obs c_obs_same_var_write_pres_diff getVWNC_var numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (metis OpSemExtProof.p_obs_contradiction OpSemExtProof.read_pres_d_obs ext_c_obs_read_diff_var_pres gr0I not_p_obs_value)
  apply (metis OpSemExtProof.p_obs_contradiction OpSemExtProof.read_pres_d_obs ext_c_obs_read_diff_var_pres not_gr0 not_p_obs_value)
  apply linarith
  apply linarith
  apply (smt One_nat_def OpSemExtProof.not_p_obs_other_pres_not_p_obs bits_one_mod_two_eq_one c_obs_write_diff_var_pres d_obs_implies_p_obs getVWNC_var mod_self numeral_2_eq_2 numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (smt OpSemExtProof.ext_c_obs_intro OpSemExtProof.ext_d_obs_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs c_obs_same_var_write_pres_diff d_obs_implies_p_obs getVWNC_var numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (metis OpSemExtProof.p_obs_contradiction ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 not_gr_zero not_p_obs_value)
  apply (metis OpSemExtProof.p_obs_contradiction ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 not_gr_zero not_p_obs_value)
  apply (smt One_nat_def OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs bits_one_mod_two_eq_one c_obs_pres_write_diff_var_ext_2 numeral_eq_iff one_neq_zero semiring_norm(89))
  apply (smt One_nat_def OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs c_obs_pres_write_diff_var_ext_2 mod_self numeral_eq_iff one_neq_zero semiring_norm(89))
  apply (smt One_nat_def OpSemExtProof.not_p_obs_other_pres_not_p_obs bits_one_mod_two_eq_one c_obs_write_diff_var_pres d_obs_implies_p_obs getVWNC_var mod_self numeral_2_eq_2 numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (smt OpSemExtProof.ext_c_obs_intro OpSemExtProof.ext_d_obs_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs c_obs_same_var_write_pres_diff d_obs_implies_p_obs getVWNC_var numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (metis OpSemExtProof.p_obs_contradiction ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 not_gr_zero not_p_obs_value)
  apply (metis OpSemExtProof.p_obs_contradiction ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 not_gr_zero not_p_obs_value)
  apply (smt One_nat_def OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs bits_one_mod_two_eq_one c_obs_pres_write_diff_var_ext_2 numeral_eq_iff one_neq_zero semiring_norm(89))
  apply (smt One_nat_def OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs c_obs_pres_write_diff_var_ext_2 mod_self numeral_eq_iff one_neq_zero semiring_norm(89))
  apply (smt One_nat_def OpSemExtProof.not_p_obs_other_pres_not_p_obs bits_one_mod_two_eq_one c_obs_write_diff_var_pres d_obs_implies_p_obs getVWNC_var mod_self numeral_2_eq_2 numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (smt OpSemExtProof.ext_c_obs_intro OpSemExtProof.ext_d_obs_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs c_obs_same_var_write_pres_diff d_obs_implies_p_obs getVWNC_var numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (metis OpSemExtProof.p_obs_contradiction ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 gr0I not_p_obs_value)
  apply (metis OpSemExtProof.p_obs_contradiction ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 gr0I not_p_obs_value)
  apply (smt One_nat_def OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs bits_one_mod_two_eq_one c_obs_pres_write_diff_var_ext_2 numeral_eq_iff one_neq_zero semiring_norm(89))
  apply (smt One_nat_def OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs c_obs_pres_write_diff_var_ext_2 mod_self numeral_eq_iff one_neq_zero semiring_norm(89))
  apply (smt One_nat_def OpSemExtProof.not_p_obs_other_pres_not_p_obs bits_one_mod_two_eq_one c_obs_write_diff_var_pres d_obs_implies_p_obs getVWNC_var mod_self numeral_2_eq_2 numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (smt OpSemExtProof.ext_c_obs_intro OpSemExtProof.ext_d_obs_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs c_obs_same_var_write_pres_diff d_obs_implies_p_obs getVWNC_var numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (smt OpSemExtProof.p_obs_contradiction ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 gr0I nat.inject not_p_obs_value)
  apply (smt OpSemExtProof.p_obs_contradiction ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 gr0I nat.inject not_p_obs_value)
  apply (metis One_nat_def n_not_Suc_n one_mod_two_eq_one)
  apply (smt One_nat_def OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs c_obs_pres_write_diff_var_ext_2 numeral_eq_iff one_neq_zero semiring_norm(89))
  apply (smt One_nat_def OpSemExtProof.not_p_obs_other_pres_not_p_obs bits_one_mod_two_eq_one c_obs_write_diff_var_pres d_obs_implies_p_obs getVWNC_var mod_self numeral_2_eq_2 numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (smt OpSemExtProof.ext_c_obs_intro OpSemExtProof.ext_d_obs_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs c_obs_same_var_write_pres_diff d_obs_implies_p_obs getVWNC_var numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (smt OpSemExtProof.p_obs_contradiction ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 gr0I nat.inject not_p_obs_value numeral_2_eq_2)
  apply (smt OpSemExtProof.p_obs_contradiction ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 gr0I nat.inject not_p_obs_value numeral_2_eq_2)
  apply (smt One_nat_def OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs bits_one_mod_two_eq_one c_obs_pres_write_diff_var_ext_2 numeral_eq_iff one_neq_zero semiring_norm(89))
  apply (metis mod_self n_not_Suc_n numeral_2_eq_2)
  apply (smt One_nat_def OpSemExtProof.not_p_obs_other_pres_not_p_obs bits_one_mod_two_eq_one c_obs_write_diff_var_pres d_obs_implies_p_obs getVWNC_var mod_self numeral_2_eq_2 numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (smt OpSemExtProof.ext_c_obs_intro OpSemExtProof.ext_d_obs_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs c_obs_same_var_write_pres_diff d_obs_implies_p_obs getVWNC_var numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (metis OpSemExtProof.p_obs_contradiction ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 gr0I not_p_obs_value)
  apply (metis OpSemExtProof.p_obs_contradiction ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 not_gr_zero not_p_obs_value)  
  apply (smt One_nat_def OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs bits_one_mod_two_eq_one c_obs_pres_write_diff_var_ext_2 numeral_eq_iff one_neq_zero semiring_norm(89))  
  apply (smt One_nat_def OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs c_obs_pres_write_diff_var_ext_2 mod_self numeral_eq_iff one_neq_zero semiring_norm(89))  
  apply (smt One_nat_def OpSemExtProof.not_p_obs_other_pres_not_p_obs bits_one_mod_two_eq_one c_obs_write_diff_var_pres d_obs_implies_p_obs getVWNC_var mod_self numeral_2_eq_2 numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (smt OpSemExtProof.ext_c_obs_intro OpSemExtProof.ext_d_obs_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs c_obs_same_var_write_pres_diff d_obs_implies_p_obs getVWNC_var numeral_eq_iff rcu_simps(23) semiring_norm(89))
  apply (metis OpSemExtProof.p_obs_contradiction ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 gr0I not_p_obs_value)
  apply (metis OpSemExtProof.p_obs_contradiction ext_c_obs_read_diff_var_pres ext_d_obs_rd_pres3 gr0I not_p_obs_value)
  apply (smt One_nat_def OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs bits_one_mod_two_eq_one c_obs_pres_write_diff_var_ext_2 numeral_eq_iff semiring_norm(89))
  apply (smt OpSemExtProof.ext_write_other_pres_d_obs OpSemExtProof.not_p_obs_other_pres_not_p_obs c_obs_pres_write_diff_var_ext_2 mod_self numeral_eq_iff semiring_norm(89))

  done

end