theory ordered_set_sd
imports Main
begin


definition "sd_ordereded (A::'a set) (f::'a\<Rightarrow>nat) \<equiv> \<forall> e . e\<in> A \<and> f e>0 \<longrightarrow> (\<exists> e'. e'\<in>A \<and> f e' = (f e)-1)"

definition "sd_earlier (A::'a set) (f::'a\<Rightarrow>nat) (u::nat) \<equiv> \<exists>e' . e'\<in>A \<and> f e' = u"

lemma base1: "sd_ordereded A f \<Longrightarrow> e\<in>A \<Longrightarrow> f e > 0 \<Longrightarrow> u = f e \<Longrightarrow> u \<ge> 0 \<Longrightarrow> sd_earlier A f (u-1) "
  apply(simp add: sd_earlier_def sd_ordereded_def)
  done

lemma earlier_elements: "sd_ordereded A f  \<Longrightarrow> e\<in>A \<Longrightarrow> f e > 0 \<Longrightarrow> u < f e \<Longrightarrow> u \<ge> 0 \<Longrightarrow> sd_earlier A f u "
  apply(induction u rule:less_induct)
  apply clarsimp
    by (smt sd_earlier_def base1 diff_Suc_1 le0 strict_inc_induct zero_less_Suc)


lemma "sd_ordereded A f  \<Longrightarrow> e\<in>A \<Longrightarrow> f e  = 25 \<Longrightarrow> sd_earlier A f 14"
  using earlier_elements
  proof -
  assume a1: "f e = 25"
  assume a2: "sd_ordereded A f"
    assume a3: "e \<in> A"
    have "(14 \<noteq> f e \<and> f e \<noteq> 0) \<and> num.Bit1 num.One < num.Bit0 (num.Bit1 num.One)"
      using a1 by force
    then show ?thesis
      using a3 a2 a1 by (metis le0 nat_less_le numeral_le_iff earlier_elements semiring_norm(72) semiring_norm(74))
  qed


end