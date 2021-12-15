theory RB_Relaxed_mike imports RCU_Lems 
begin

datatype F = B | W | Q | R 
datatype Pointer = Head | Tail

consts n :: nat   (*size of buffer, input*)
consts N :: nat   (*number of Arr\<^sub>W entries*)

(*(Wr T u t b \<sigma>)*)
(*
lemma pval_val:
  assumes "wfs \<sigma>"
  and "\<not> [x \<approx>\<^sub>t u] \<sigma>"
  and "u \<noteq> v"
  and "var w = x"
  and "ts = getTS \<sigma> w"
shows "\<not> [x \<approx>\<^sub>t u] (write_trans t b w v \<sigma> ts) "
  sorry
*)


lemma pval_val_same:
  assumes "wfs \<sigma>"
  and "\<not> [x \<approx>\<^sub>t u] \<sigma>"
  and "u \<noteq> v"
  and "var w = x"
shows "\<not> [x \<approx>\<^sub>t u] (Wr x v t b \<sigma>)"
  using assms
  apply (simp add: p_obs_def visible_writes_def value_def write_trans_def)
  apply(simp add: rev_app_def update_modView_def update_mods_def update_thrView_def update_wa_def)
  apply safe  
  using w_in_writes_on_var apply blast
  defer  
  apply (simp add: getVWNC_var)
   apply (simp add: getVWNC_var)
  apply(case_tac "(a, ba)
       \<in> writes_on \<sigma> x")
  apply (smt dual_order.strict_trans getTS_w_greater_tst_w getVWNC_in_visible_writes le_neq_trans less_le_not_le mem_Collect_eq visible_writes_def)
proof -
fix a :: nat and ba :: rat
  assume a1: "(a, ba) \<in> writes_on (\<sigma> \<lparr>thrView := (thrView \<sigma>) (t := (thrView \<sigma> t) (var w := (var w, getTS \<sigma> (getVWNC \<sigma> t (var w))))), modView := (modView \<sigma>) ((var w, getTS \<sigma> (getVWNC \<sigma> t (var w))) := (thrView \<sigma> t) (var w := (var w, getTS \<sigma> (getVWNC \<sigma> t (var w))))), mods := (mods \<sigma>) ((var w, getTS \<sigma> (getVWNC \<sigma> t (var w))) := \<lparr>val = v, is_releasing = b\<rparr>), writes := insert (var w, getTS \<sigma> (getVWNC \<sigma> t (var w))) (surrey_state.writes \<sigma>), write_available := (write_available \<sigma>) ((var w, getTS \<sigma> (getVWNC \<sigma> t (var w))) := True)\<rparr>) (var w)"
  assume a2: "x = var w"
  assume a3: "(a, ba) \<notin> writes_on \<sigma> x"
  assume a4: "ba \<noteq> getTS \<sigma> (getVWNC \<sigma> t (var w))"
  have f5: "\<forall>s n p. var p = n \<and> p \<in> surrey_state.writes (s::surrey_state) \<or> p \<notin> writes_on s n"
    using writes_on_def by force
  have "\<forall>s n p. writes_on (write_available_update p (s::surrey_state)) n = writes_on s n"
    by (metis (no_types) surrey_state.select_convs(1) surrey_state.surjective surrey_state.update_convs(5) writes_on_def)
  then have f6: "(a, ba) \<in> writes_on (\<sigma> \<lparr>thrView := (thrView \<sigma>) (t := (thrView \<sigma> t) (x := (x, getTS \<sigma> (getVWNC \<sigma> t x)))), modView := (modView \<sigma>) ((x, getTS \<sigma> (getVWNC \<sigma> t x)) := (thrView \<sigma> t) (x := (x, getTS \<sigma> (getVWNC \<sigma> t x)))), mods := (mods \<sigma>) ((x, getTS \<sigma> (getVWNC \<sigma> t x)) := \<lparr>val = v, is_releasing = b\<rparr>), writes := insert (x, getTS \<sigma> (getVWNC \<sigma> t x)) (surrey_state.writes \<sigma>)\<rparr>) x"
    using a2 a1 by blast
  have f7: "\<forall>s f. surrey_state.writes (writes_update f (s::surrey_state)) = f (surrey_state.writes s)"
    by auto
  have f8: "var (a, ba) = x"
    using f6 f5 by meson
  have "(a, ba) \<in> surrey_state.writes \<sigma>"
    using f7 f6 f5 a4 a2 by (metis insert_iff snd_conv)
  then show False
    using f8 a3 writes_on_def by force
qed



lemma pval_val_other:
  assumes "wfs \<sigma>"
  and "\<not> [x \<approx>\<^sub>t u] \<sigma>"
  and "u \<noteq> v"
  and "var w = x"
  and "t\<noteq>s"
shows "\<not> [x \<approx>\<^sub>t u] (Wr x v s b \<sigma>)"
  using assms apply simp
  apply (simp add: p_obs_def visible_writes_def value_def write_trans_def)
    apply(simp add: rev_app_def update_modView_def update_mods_def update_thrView_def update_wa_def)
  apply safe  
  using w_in_writes_on_var
  apply (simp add: w_in_writes_on_var getVWNC_var) 
  apply (simp add: getVWNC_var)

  apply(case_tac "(a, ba)
       \<in> writes_on \<sigma> x")
  apply (smt dual_order.strict_trans getTS_w_greater_tst_w getVWNC_in_visible_writes le_neq_trans less_le_not_le mem_Collect_eq visible_writes_def)
proof -
  fix a :: nat and ba :: rat
  assume a1: "ba \<noteq> getTS \<sigma> (getVWNC \<sigma> s (var w))"
  assume a2: "(a, ba) \<in> writes_on (\<sigma> \<lparr>thrView := (thrView \<sigma>) (s := (thrView \<sigma> s) (var w := (var w, getTS \<sigma> (getVWNC \<sigma> s (var w))))), modView := (modView \<sigma>) ((var w, getTS \<sigma> (getVWNC \<sigma> s (var w))) := (thrView \<sigma> s) (var w := (var w, getTS \<sigma> (getVWNC \<sigma> s (var w))))), mods := (mods \<sigma>) ((var w, getTS \<sigma> (getVWNC \<sigma> s (var w))) := \<lparr>val = v, is_releasing = b\<rparr>), writes := insert (var w, getTS \<sigma> (getVWNC \<sigma> s (var w))) (surrey_state.writes \<sigma>), write_available := (write_available \<sigma>) ((var w, getTS \<sigma> (getVWNC \<sigma> s (var w))) := True)\<rparr>) (var w)"
  assume a3: "(a, ba) \<notin> writes_on \<sigma> x"
  assume a4: "x = var w"
  have "(a, ba) \<in> \<lbrace>\<acute>var = var w \<and> \<acute>(\<in>) (surrey_state.writes (\<sigma> \<lparr>thrView := (thrView \<sigma>) (s := (thrView \<sigma> s) (var w := (var w, getTS \<sigma> (getVWNC \<sigma> s (var w))))), modView := (modView \<sigma>) ((var w, getTS \<sigma> (getVWNC \<sigma> s (var w))) := (thrView \<sigma> s) (var w := (var w, getTS \<sigma> (getVWNC \<sigma> s (var w))))), mods := (mods \<sigma>) ((var w, getTS \<sigma> (getVWNC \<sigma> s (var w))) := \<lparr>val = v, is_releasing = b\<rparr>), writes := insert (var w, getTS \<sigma> (getVWNC \<sigma> s (var w))) (surrey_state.writes \<sigma>), write_available := (write_available \<sigma>) ((var w, getTS \<sigma> (getVWNC \<sigma> s (var w))) := True)\<rparr>))\<rbrace>"
    using a2 writes_on_def by blast
  then have f5: "var (a, ba) = var w \<and> (a, ba) \<in> surrey_state.writes (\<sigma> \<lparr>thrView := (thrView \<sigma>) (s := (thrView \<sigma> s) (var w := (var w, getTS \<sigma> (getVWNC \<sigma> s (var w))))), modView := (modView \<sigma>) ((var w, getTS \<sigma> (getVWNC \<sigma> s (var w))) := (thrView \<sigma> s) (var w := (var w, getTS \<sigma> (getVWNC \<sigma> s (var w))))), mods := (mods \<sigma>) ((var w, getTS \<sigma> (getVWNC \<sigma> s (var w))) := \<lparr>val = v, is_releasing = b\<rparr>), writes := insert (var w, getTS \<sigma> (getVWNC \<sigma> s (var w))) (surrey_state.writes \<sigma>), write_available := (write_available \<sigma>) ((var w, getTS \<sigma> (getVWNC \<sigma> s (var w))) := True)\<rparr>)"
    by blast
  then have "(a, ba) \<notin> surrey_state.writes \<sigma>"
    using a4 a3 writes_on_def by fastforce
  then show False
    using f5 a1 by simp
qed



lemma pval_val:
  assumes "wfs \<sigma>"
  and "\<not> [x \<approx>\<^sub>t u] \<sigma>"
  and "u \<noteq> v"
  and "var w = x"
shows "\<not> [x \<approx>\<^sub>t u] (Wr x v t' b \<sigma>)"
  using assms apply (cases "t=t'")
  using pval_val_same apply blast
  using pval_val_other by blast




lemma pval_val_outside:
  assumes "wfs \<sigma>"
  and "N\<in> \<nat>"
  and "\<forall>j.[x \<approx>\<^sub>t j] \<sigma> \<longrightarrow> j<N"
  and "\<forall>k. k<N \<longrightarrow> [x \<approx>\<^sub>t k] \<sigma>"
  and "u\<in>\<nat> \<and> u<N"
shows "\<forall>z.(z>N\<longrightarrow>\<not>[x \<approx>\<^sub>t z] (Wr x u t' b \<sigma>))"
  using assms apply (cases "t=t'")
  apply (metis fst_conv not_less_iff_gr_or_eq pval_val)
  by (metis fst_conv not_less_iff_gr_or_eq pval_val)


lemma pval_val_outside_2:
  assumes "wfs \<sigma>"
  and "N \<in> \<nat>"
  and "[x =\<^sub>t 0] \<sigma>"
  and "u \<noteq> 0"
shows "\<exists>i.(([x =\<^sub>t i] (Wr x u t b \<sigma>))\<or>([x =\<^sub>t i] (Wr x 0 t' b \<sigma>)))" 
  using assms apply (cases "t=t'")
  using OpSem_ProofRules.ext_d_obs_d_obs apply blast
  using OpSem_ProofRules.ext_d_obs_d_obs by blast






(*
  assumes "wfs \<sigma>"
  and "\<not> [x \<approx>\<^sub>t u] \<sigma>"
  and "u \<noteq> v"
  and "var w = x"
shows "\<not> [x \<approx>\<^sub>t u] (Wr x v t b \<sigma>)"


lemma pval_val_all: 
  assumes "wfs \<sigma>"
  and "\<forall>i. i > k \<longrightarrow> \<not> [x \<approx>\<^sub>t i] \<sigma>"
  and "k < j" 
  and "u \<le> k"
  and "var w = x"
shows "\<not> [x \<approx>\<^sub>t j] (Wr x v t b \<sigma>) "
  using assms
  
  using pval_val sledgehammer
*)

consts   
  H :: L
  T :: L


record LB =
  hW ::  V               (*local copy of W*)
  tW ::  V               (*local copy of W*)
  q :: "(nat \<times> nat) list" (*for now assume well synchronised, need to think about weak memory *)
  tempR :: "(nat \<times> nat)"          (*local copy of word by R*)

  tloc :: V
  Data:: "nat  \<Rightarrow> nat"     (*returns a word Data_i*)
  countW :: nat  (* the index of the next element of Data to be written  *)
  countR :: nat  (* how many words from Data the read has read or reading (i.e., retrieved)  *)

  ownD :: "nat \<Rightarrow> F" (* ownership of data indices *)
  ownB :: "nat \<Rightarrow> F" (* ownership of bytes in buffer *)
  (* tries :: nat *)
  oom :: bool       (*signals W that it was OOM*)
  \<sigma> :: surrey_state

definition "global s \<equiv> wfs s \<and> H \<noteq> T"




lemmas opsemsyntax [simp] =  global_def
lemmas defs_del [simp del] =  Rd_def Let_def Wr_def Upd_def st_rd_def val_rd_def

(* thread 2 is the writer *)
(* thread 3 is the reader *)

(* Omit tries *)
(* Finish queueu + reader *)

(* We need this one to hold at minimum *)
definition "arrayInv s \<equiv> \<forall>i. (i<countR s \<longrightarrow> ownD s i = R)\<and> (countR s \<le> i \<and> i < countW s \<longrightarrow> ownD s i = B) \<and> (countW s \<le> i \<and> i < n \<longrightarrow> ownD s i = W) "


definition "q_entries_bounded s \<equiv> (\<forall>i. i < length(q s) \<longrightarrow> (fst(q s!i)+snd(q s!i)\<le>N)\<and>snd(q s!i)>0)"
definition "tempR_bounded s \<equiv> fst (tempR s) + snd (tempR s) \<le> N"
definition "counter_q_rel s \<equiv> (countW s-countR s=length(q s))"
definition "con_assms s  \<equiv>   0 < N \<and> 0<n \<and> (countR s\<le>countW s) \<and> (countW s\<le>n)
                             \<and> (\<forall>i.(i<n)\<longrightarrow>Data s i\<le>N \<and> Data s i>0)"
(*new
(typically)
\forall x . P(x) \<longrightarrow> Q(x)
\exists x . P(x) \<and> Q(x)

[H =\<^sub>2 i] means thread 2 sees the last write to H and this has value i.
[H \<approx>\<^sub>2 i] means that thread 2 can see the value i.
*)
definition "bounded_pointers s \<equiv> ((\<forall>i. i > N \<longrightarrow> \<not>[H \<approx>\<^sub>2 i] (\<sigma> s)))\<and>
                                 ((\<forall>j. j > N \<longrightarrow> \<not>[T \<approx>\<^sub>2 j] (\<sigma> s)))"

definition "basic_pointer_movement s \<equiv> 0\<le>hW s\<and> hW s\<le>N \<and> 0\<le>tW s\<and> tW s\<le>N"


 


definition "collection s \<equiv> arrayInv s \<and> q_entries_bounded s
                          \<and>tempR_bounded s \<and>counter_q_rel s \<and> con_assms s
                          \<and> bounded_pointers s \<and> basic_pointer_movement s"


definition "init s \<equiv>
                     [T =\<^sub>2 0] (\<sigma> s) \<and> [H =\<^sub>2 0] (\<sigma> s) \<and> [T =\<^sub>3 0] (\<sigma> s) \<and> (q s = []) \<and> (hW s = 0) \<and> (tW s = 0)
                        \<and> (\<forall>l. (l<n) \<longrightarrow>  ((Data s l > 0)\<and>(Data s l \<le> N)))
                        \<and> (\<forall>i. (i<n) \<longrightarrow>  ownD s i = W)
                        \<and> (\<forall>i. (i\<le>N) \<longrightarrow>  ownB s i = B)
                        \<and> (countW s = 0) \<and> (countR s = 0)
                        \<and> (tempR s = (0,0)) \<and> \<not> oom s "

definition "grd1 s \<equiv> (tW s = hW s) \<and> (Data s (countW s) \<le> N) "
definition "grd2 s \<equiv> (tW s > hW s) \<and> (Data s (countW s) < (tW s - hW s)) "
definition "grd3 s \<equiv> tW s < hW s "
definition "grd4 s \<equiv> Data s (countW s) \<le> N - hW s "
definition "grd5 s \<equiv> Data s (countW s) < tW s "
definition "no_space_for_word s \<equiv> (grd1 s \<longrightarrow> \<not>(Data s (countW s) \<le> N))\<and>
                                  (grd2 s \<longrightarrow> \<not>(Data s (countW s) < (tW s - hW s)))\<and>
                                  (grd3 s \<longrightarrow> \<not>(Data s (countW s) \<le> N - hW s \<or> Data s (countW s) < tW s))"



lemmas main_invariant_lemmas = collection_def arrayInv_def q_entries_bounded_def 
                                      counter_q_rel_def tempR_bounded_def con_assms_def
                                      init_def bounded_pointers_def basic_pointer_movement_def
                                      pval_val_same pval_val_other pval_val
lemmas guards = grd1_def grd2_def grd3_def grd4_def grd5_def no_space_for_word_def


lemma LoadBuffering:
 "\<parallel>-   \<lbrace> global \<acute>\<sigma>  \<and> \<acute>collection  \<and> \<acute>init \<rbrace>
COBEGIN
\<lbrace> global \<acute>\<sigma> \<and> \<acute>collection  \<and> \<not> \<acute>oom \<and> \<acute>init\<rbrace>
  WHILE \<acute>countW < n 
   INV \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> (\<exists> i. [H =\<^sub>2 i]\<acute>\<sigma>)\<rbrace>
   DO
    \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> (\<exists> i. [H =\<^sub>2 i]\<acute>\<sigma>) \<and> \<acute>countW < n\<rbrace> \<comment> \<open>A1\<close>
      <\<acute>hW \<leftarrow>\<^sub>2 H\<acute>\<sigma>> ;;  
    \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection  \<and> [H =\<^sub>2 \<acute>hW]\<acute>\<sigma> \<and> \<acute>countW < n\<rbrace>
      <\<acute>tW \<leftarrow>\<^sub>2 T\<acute>\<sigma>> ;;
    \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection  \<and> [H =\<^sub>2 \<acute>hW]\<acute>\<sigma> \<and> \<acute>countW < n\<rbrace>
      IF \<acute>grd1 \<comment> \<open>A2\<close>
      THEN \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> [H =\<^sub>2 \<acute>hW]\<acute>\<sigma> \<and> \<acute>countW < n \<and> \<acute>grd1 \<rbrace> \<comment> \<open>A3\<close>
            <T :=\<^sub>2 0 \<acute>\<sigma>> ;; \<comment> \<open>This might not need to be releasing\<close>  
            \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> [H =\<^sub>2 \<acute>hW]\<acute>\<sigma> \<and> \<acute>countW < n \<and> \<acute>grd1 \<rbrace>
            \<langle><H :=\<^sub>2 (\<acute>Data \<acute>countW) \<acute>\<sigma>> ,, \<acute>hW := 0 ,, \<acute>oom := False ,,
              (\<acute>ownB := ( \<lambda> x. if 0\<le> x \<and> x < (\<acute>Data \<acute>countW) then W else \<acute>ownB x ))\<rangle>
      ELSE \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> [H =\<^sub>2 \<acute>hW]\<acute>\<sigma> \<and> \<acute>countW < n \<and> \<not>\<acute>grd1 \<rbrace> 
            IF \<acute>grd2
            THEN \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> [H =\<^sub>2 \<acute>hW]\<acute>\<sigma> \<and> \<acute>countW < n \<and> \<acute>grd2\<rbrace> \<comment> \<open>A4\<close>
                \<langle><H :=\<^sub>2 \<acute>hW + (\<acute>Data \<acute>countW) \<acute>\<sigma>> ,, \<acute>oom := False ,,
                  (\<acute>ownB := ( \<lambda> x. if \<acute>hW \<le> x \<and> x < (\<acute>hW + (\<acute>Data \<acute>countW)) then W else \<acute>ownB x ))\<rangle>
            ELSE \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> [H =\<^sub>2 \<acute>hW]\<acute>\<sigma> \<and> \<acute>countW < n \<and> \<not>\<acute>grd1 \<and> \<not>\<acute>grd2\<rbrace>
                 IF \<acute>grd3
                 THEN \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> [H =\<^sub>2 \<acute>hW]\<acute>\<sigma> \<and> \<acute>countW < n \<and> \<acute>grd3 \<rbrace> \<comment> \<open>A5\<close>
                      IF \<acute>grd4
                      THEN \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> [H =\<^sub>2 \<acute>hW]\<acute>\<sigma> \<and> \<acute>countW < n \<and> \<acute>grd3 \<and> \<acute>grd4 \<rbrace> \<comment> \<open>A6\<close>
                      \<langle><H :=\<^sub>2 \<acute>hW + (\<acute>Data \<acute>countW) \<acute>\<sigma>> ,, \<acute>oom := False ,,
                         (\<acute>ownB := ( \<lambda> x. if \<acute>hW \<le> x \<and> x < (\<acute>hW + (\<acute>Data \<acute>countW)) then W else \<acute>ownB x ))\<rangle>
                      ELSE \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> [H =\<^sub>2 \<acute>hW]\<acute>\<sigma> \<and> \<acute>countW < n \<and> \<acute>grd3 \<and> \<not>\<acute>grd4 \<rbrace>
                            IF \<acute>grd5
                            THEN \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> [H =\<^sub>2 \<acute>hW]\<acute>\<sigma> \<and> \<acute>countW < n \<and> \<acute>grd3 \<and> \<acute>grd5 \<rbrace> \<comment> \<open>A7\<close>
                              \<langle><H :=\<^sub>2 (\<acute>Data \<acute>countW) \<acute>\<sigma>> ,, \<acute>hW := 0 ,, \<acute>oom := False ,,
                                (\<acute>ownB := ( \<lambda> x. if ((0 \<le> x \<and> x < (\<acute>Data \<acute>countW))\<or> x\<ge>T)\<and>x\<noteq>N then W else \<acute>ownB x ))\<rangle>
                            ELSE \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> [H =\<^sub>2 \<acute>hW]\<acute>\<sigma> \<and> \<acute>countW < n \<and> \<acute>no_space_for_word\<rbrace> \<comment> \<open>A8\<close>
                                \<langle>\<acute>oom := True\<rangle>
                                  \<comment> \<open>OOM\<close>
                            FI
                      FI
                 ELSE \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> [H =\<^sub>2 \<acute>hW]\<acute>\<sigma> \<and> \<acute>countW < n \<and> \<acute>no_space_for_word\<rbrace>
                      \<langle>\<acute>oom := True\<rangle>
                      \<comment> \<open>OOM\<close>
                 FI
           FI
     FI;;
     \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection  
        \<and> ((\<acute>oom=False \<and> [H =\<^sub>2 (\<acute>hW+(\<acute>Data \<acute>countW))]\<acute>\<sigma> ) \<comment> \<open>\<and> \<acute>hW  + \<acute>Data (\<acute>countW) \<le> N\<close> 
             \<or> (\<acute>oom=True \<and> [H =\<^sub>2 \<acute>hW]\<acute>\<sigma> \<and> \<acute>no_space_for_word)) \<and> \<acute>countW < n\<rbrace>
     IF \<acute>oom=True
     THEN \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> [H =\<^sub>2 \<acute>hW]\<acute>\<sigma> \<and> \<acute>no_space_for_word \<and> \<acute>countW < n\<rbrace> \<comment> \<open>OK\<close>
          SKIP
     ELSE \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection  \<and> \<acute>countW < n \<and> [H =\<^sub>2 (\<acute>hW+(\<acute>Data \<acute>countW))]\<acute>\<sigma>\<rbrace>
          \<langle>\<acute>q := \<acute>q @ [(\<acute>hW, (\<acute>Data \<acute>countW))],,  
           \<acute>ownD := (\<lambda> x. if x = \<acute>countW then B else \<acute>ownD x),, 
           \<acute>ownB := (\<lambda> x. if (\<acute>ownB x = W) then Q else \<acute>ownB x),,  
           \<acute>countW := (\<acute>countW+1)\<rangle> 
     FI
   OD 
    \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> \<acute>countW = n\<rbrace>

\<parallel>
 \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> \<acute>tempR = (0, 0) \<rbrace>
  WHILE \<acute>countR < n
  INV \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> \<acute>tempR=(0,0) \<rbrace>
  DO  \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> \<acute>countR < n \<and> \<acute>tempR=(0,0) \<rbrace>
      IF \<acute>countR < \<acute>countW THEN
                \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> \<acute>countR < \<acute>countW \<and> \<acute>tempR=(0,0) \<rbrace> \<comment> \<open>retrieve from Q, dequeue\<close>
                \<langle> \<acute>tempR  := (fst(hd \<acute>q),(snd(hd \<acute>q))) ,,  
                    \<acute>ownD := (\<lambda> x. if x = \<acute>countR then R else \<acute>ownD x),, 
                    \<acute>countR := \<acute>countR+1,, 
                    ( IF \<exists>i.(i<(fst(hd \<acute>q)+snd(hd \<acute>q)) \<and> [T =\<^sub>3 i] \<acute>\<sigma>) THEN (\<acute>ownB := ( \<lambda> x. if i \<le> x \<and> x < (fst(hd \<acute>q)+(snd(hd \<acute>q))) then R else \<acute>ownB x ))
                      ELSE (\<acute>ownB := ( \<lambda> x. if i > x \<and> x \<le> (fst(hd \<acute>q)+(snd(hd \<acute>q)))\<or>(x=N) then \<acute>ownB x else R ))FI),, 
                     \<acute>q := (tl \<acute>q) \<rangle>;;
                    \<lbrace> global \<acute>\<sigma> \<and>\<acute>collection \<and> \<acute>countR \<le> \<acute>countW  \<and> \<acute>tempR\<noteq>(0,0)\<rbrace> \<comment> \<open>Push T\<close>
                    \<langle><T :=\<^sub>3 (fst \<acute>tempR + snd \<acute>tempR) \<acute>\<sigma> > 
                    ,, \<acute> tempR := (0,0),, 
                   \<acute>ownB := (\<lambda> x. if \<acute>ownB x = R then B else \<acute>ownD x) \<rangle>
      ELSE
      \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> \<acute>tempR=(0,0) \<and> \<acute>countR < n\<rbrace>
      SKIP
      FI
  OD
\<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> \<acute>countR = n\<rbrace>



COEND
  \<lbrace> global \<acute>\<sigma> \<and> \<acute>collection \<and> \<acute>countW = n \<and> \<acute>countR = n\<rbrace>
  

"
  apply (oghoare)
  apply ((simp add: main_invariant_lemmas Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff; force)+)[4]
  apply ((simp add: guards main_invariant_lemmas Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)[1]
  apply (metis OpSem_ProofRules.d_obs_read_value OpSem_ProofRules.ext_d_obs_rd_pres d_obs_implies_p_obs le_less_linear)
  apply auto[1]
  apply ((simp add: guards main_invariant_lemmas Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)[1]
  apply clarsimp
  apply (meson not_less not_pobs_contradiction)
  apply auto[1]
  apply ((simp add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)
  using pval_val apply auto[1]
  apply ((simp add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)
  apply (metis OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs leD)
  apply ((simp add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)
  apply auto[3]
  apply ((simp add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)
  apply (smt OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs add.commute leD le_less_trans less_diff_conv less_imp_le)
  apply ((simp add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)
  apply auto[1]
  apply ((simp add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)
  apply (metis Nat.le_diff_conv2 OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs add.commute leD)
  apply auto[3]
  apply ((simp add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)
  apply (metis OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs leD)
  apply ((simp add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)
  apply auto[1]
  apply ((simp add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)
  apply (metis)
  apply ((simp add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)
  apply auto[1]
  apply auto[1]
  apply ((simp add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)
  apply (metis)
  apply ((simp add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)
  apply (metis)
  apply ((simp add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)
  apply (metis)
  apply ((simp add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)
  apply auto[1]
  apply auto[1]
  apply ((simp add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)
  apply (metis (no_types, lifting) Suc_diff_le d_obs_implies_p_obs fst_eqD le_less_linear less_antisym nth_append nth_append_length snd_conv)
  apply auto[1]
  apply ((simp add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)+)
  apply clarsimp
  apply (simp_all add: main_invariant_lemmas guards Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff)
          (*129*)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred hd_conv_nth length_0_conv length_tl less_numeral_extra(3) nat.inject nth_tl snd_conv zero_less_diff)
  apply clarify
  using pval_val apply auto[1]
  using OpSem_ProofRules.p_obs_contradiction apply blast
  apply clarify
  apply linarith
  apply (metis (no_types, lifting) less_numeral_extra(3) )
  using pval_val apply auto[1]
  apply clarify
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply clarify
  apply (intro conjI impI)
  apply (metis getVWNC_var leD pval_val)
  apply (metis OpSem_ProofRules.ext_write_other_pres_d_obs)
  apply clarify
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply clarify
  apply (intro conjI impI)
  apply (metis getVWNC_var leD pval_val)
  apply (metis OpSem_ProofRules.ext_write_other_pres_d_obs)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply linarith
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply linarith
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply linarith
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply clarify
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply clarify
  apply blast
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply clarify
  apply (intro conjI impI)
  apply (metis getVWNC_var leD pval_val)
  apply (metis OpSem_ProofRules.ext_write_other_pres_d_obs)
  apply clarify
  apply blast
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply (metis getVWNC_var leD pval_val)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono Suc_pred diff_is_0_eq hd_conv_nth leD length_0_conv length_tl nat_less_le nat.inject nth_tl zero_less_diff)
  apply clarify
  apply (meson not_less not_pobs_contradiction)
  apply (meson not_less not_pobs_contradiction)
  apply (metis fst_conv not_less_iff_gr_or_eq pval_val)
  apply (metis OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs leD)
  apply clarify
  apply (smt OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs add.commute leD le_less_trans less_diff_conv less_imp_le_nat)
  apply (metis Nat.le_diff_conv2 OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs add.commute leD)
  apply (metis OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs leD)
  apply (metis Suc_diff_le d_obs_implies_p_obs fst_conv le_less_linear less_antisym nth_append nth_append_length snd_conv)
  apply (meson le_less_linear not_pobs_contradiction)
  apply (meson le_less_linear not_pobs_contradiction)
  apply (metis fst_conv not_less_iff_gr_or_eq pval_val)
  apply (metis OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs leD)
  apply clarify
  apply (smt OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs add.commute leD le_less_trans less_diff_conv less_imp_le_nat)
  apply (metis Nat.le_diff_conv2 OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs add.commute leD)
  apply (metis OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs leD)
  apply (metis Suc_diff_le d_obs_implies_p_obs fst_conv le_less_linear less_antisym nth_append nth_append_length snd_conv)
  apply (meson le_less_linear not_pobs_contradiction)
  apply (meson le_less_linear not_pobs_contradiction)
  apply (metis fst_conv not_less_iff_gr_or_eq pval_val)
  apply (metis OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs leD)
  apply clarify
  apply (smt OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs add.commute leD le_less_trans less_diff_conv less_imp_le_nat)
  apply (metis Nat.le_diff_conv2 OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs add.commute leD)
  apply (metis OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs leD)
  apply (metis Suc_diff_le d_obs_implies_p_obs fst_conv le_less_linear less_antisym nth_append nth_append_length snd_conv)
  apply (meson le_less_linear not_pobs_contradiction)
  apply (meson le_less_linear not_pobs_contradiction)
  apply (metis fst_conv not_less_iff_gr_or_eq pval_val)
  apply (metis OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs leD)
  apply clarify
  apply (smt OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs add.commute leD le_less_trans less_diff_conv less_imp_le_nat)
  apply (metis Nat.le_diff_conv2 OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs add.commute leD)
  apply (metis OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs leD)
  apply (metis Suc_diff_le d_obs_implies_p_obs fst_conv le_less_linear less_antisym nth_append nth_append_length snd_conv)
  apply (meson le_less_linear not_pobs_contradiction)
  apply (meson le_less_linear not_pobs_contradiction)
  apply (metis fst_conv not_less_iff_gr_or_eq pval_val)
  apply (metis OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs leD)
  apply clarify
  apply (smt OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs add.commute leD le_less_trans less_diff_conv less_imp_le_nat)
  apply (metis Nat.le_diff_conv2 OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs add.commute leD)
  apply (metis OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs leD)
  apply (metis Suc_diff_le d_obs_implies_p_obs fst_conv le_less_linear less_antisym nth_append nth_append_length snd_conv)
  apply (meson le_less_linear not_pobs_contradiction)
  apply (meson le_less_linear not_pobs_contradiction)
  apply (metis fst_conv not_less_iff_gr_or_eq pval_val)
  apply (metis OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs leD)
  apply clarify
  apply (smt OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs add.commute leD le_less_trans less_diff_conv less_imp_le_nat)
  apply (metis Nat.le_diff_conv2 OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs add.commute leD)
  apply (metis OpSem_ProofRules.d_obs_not_p_obs OpSem_ProofRules.ext_d_obs_d_obs OpSem_ProofRules.write_pres_wfs leD)
  apply (metis Suc_diff_le d_obs_implies_p_obs fst_conv le_less_linear less_antisym nth_append nth_append_length snd_conv)
  apply (meson le_less_linear not_pobs_contradiction)
  by simp








(*(simp add: Collect_conj_eq[symmetric] Collect_imp_eq[symmetric] Collect_disj_eq[symmetric] Collect_mono_iff )?)*)