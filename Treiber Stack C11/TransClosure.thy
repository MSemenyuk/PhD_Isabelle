theory TransClosure
  imports "HOL-Lattice.Orders"
begin

lemma transcl_fresh:
    assumes  "\<forall>b .(b,b)\<notin> f\<^sup>+"
        and "a \<notin> Domain f \<union> Range f"
        and "g = f \<union> {(a,a')}"
        and "a \<noteq> a'"
      shows "\<forall>b . (b,b) \<notin> g\<^sup>+"
  using assms
  apply(subgoal_tac "\<forall> c . (c,a)\<notin> f\<^sup>+") defer
   apply (metis Range.intros UnI2 trancl_range)
    apply auto
    using  acyclic_def acyclic_insert rtranclD
    by metis 

lemma transcl_fresh_new:
    assumes  "\<forall>b .(b,b)\<notin> f\<^sup>+"
        and "a \<notin> Domain f \<union> Range f"
        and "g = f \<union> {(a,a')}"
        and "a \<noteq> a'"
      shows " (a,a) \<notin> g\<^sup>+"
  using assms
  apply(subgoal_tac "\<forall> c . (c,a)\<notin> f\<^sup>+") defer
   apply (metis Range.intros UnI2 trancl_range)
    apply auto
    using  acyclic_def acyclic_insert rtranclD
    by metis 


lemma transcl_fresh1:
    assumes  "\<forall>b . b\<in>Range f \<longrightarrow> (c,b)\<in> f\<^sup>+"
        and "a \<notin> Domain f \<union> Range f"
        and "g = f \<union> {(a,c)}"
        and "a \<noteq> c"
      shows "\<forall>b .  b\<in>Range g \<longrightarrow>  (a,b) \<in> g\<^sup>+"
  using assms
  apply(subgoal_tac "\<forall> c . (c,a)\<notin> f\<^sup>+") defer
   apply (metis Range.intros UnI2 trancl_range)
  apply auto
  using insertI1 sup.cobounded1 trancl.simps trancl_id trancl_mono trans_trancl 
  by (smt Range.intros assms(3) insertI1 sup.cobounded1 trancl.simps trancl_id trancl_mono trans_trancl)

lemma transcl_freshdd:
    assumes "\<forall>b .(b,b)\<notin> f\<^sup>+"
        and "a \<notin> Domain f \<union> Range f"
        and "(b,b')\<in>f\<^sup>+"
        and "g = f \<union> {(a,a')}"
        and "a \<noteq> a'"
      shows "(b,b') \<in> g\<^sup>+"
  using assms
  by (meson inf_sup_ord(3) trancl_mono)

lemma transcl_remove_top:
    assumes "\<forall> b. (b,b) \<notin> f\<^sup>+"
        and "\<forall> e. (a,e) \<in> f\<^sup>+"
        and "g = f - {(a,a')}"
        and "(c,d) \<in> f\<^sup>+"
        and "c \<noteq> a"
        and "d \<noteq> a"
      shows "(c,d) \<in> g\<^sup>+"
  using assms
  by blast


lemma transcl_remove_top11:
    assumes "\<forall> b. (b,b) \<notin> f\<^sup>+"
        and "\<forall> e. (a,e) \<in> f\<^sup>+"
        and "g = f - {(a,a')}"
        and "(c,d) \<notin> f\<^sup>+"
        and "c \<noteq> a"
        and "d \<noteq> a"
      shows "(c,d) \<notin> g\<^sup>+"
  using assms
  apply blast
  done



lemma transcl_remove_transitivity:
  assumes "f = {(a,b) | a b . a\<in>p \<and> b = nxt a}"
        and "\<forall> e1 e2 . e1\<in>p \<and> e2\<in>p \<and> e1\<noteq>e2 \<longrightarrow> nxt e1 \<noteq> nxt e2"
        and "p' = p \<union> {n}"
        and "n \<notin> p"
        and "\<forall> b . b\<in>p \<longrightarrow> (t, b)\<in>f\<^sup>+"
        and "(c,d) \<in> f"
        and "(x,y) \<in> f"
        and "(c,y) \<in> f\<^sup>+"
        and "c \<noteq> t"
        and "d \<noteq> t"
        and "c\<in>p"
        and "d\<in>p"
        and "x\<in>p - {c,d}"
        and "y\<in>p - {c,d}"
      shows "(c,x) \<in> f\<^sup>+"
  using assms
  oops

(*lemma transcl_fresh:
    assumes  "\<forall>b .(b,b)\<notin> f\<^sup>+"
        and "a \<notin> Domain f \<union> Range f"
        and "g = f \<union> {(a,a')}"
        and "a \<noteq> a'"
      shows "\<forall>b . (b,b) \<notin> g\<^sup>+"
    proof-
      have a1: "\<forall> c . (c,a)\<notin> f\<^sup>+"
        using assms 
        by (metis FieldI2 Field_def  trancl_domain trancl_range)
      show ?thesis
        using assms
        apply auto
        using a1 acyclic_def acyclic_insert rtranclD
      by (metis )

*)

end