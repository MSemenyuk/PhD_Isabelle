theory RingBuffer_BD_latest_2
imports Main HOL.List
begin 


(*
      W_step_side                           R_step_side

LOCAL preserves inv    (done)         LOCAL preserves inv    (done)

LOCAL shows preW       (done)         LOCAL shows preR       (done) 

GLOBAL preserves preR  (done)         GLOBAL preserves preW  (done)  
*)


datatype PCW =
  A1 | A2 | A3 | A4 | A5 | A6 | A7 | A8
| Enqueue | idleW | OOM | FinishedW |  Write | BTS

datatype PCR =
 Release | idleR | Read

datatype F = W | R | Q | B | D | None
datatype Pointer = Head | Tail
consts N :: nat   (*size of buffer, input*)
consts n :: nat   (*number of Arr\<^sub>W entries*)

definition "F1_set={W,B,Q,R}"
definition "W_pre_acquire_set={A1,A2,A3,A4,A5,A6,A7,A8,idleW,FinishedW,OOM,BTS}"
definition "W_post_acquire_set={Write,Enqueue}"
definition "R_pre_dequeue_set={idleR}"
definition "R_post_dequeue_set={Read, Release}"

lemmas sets [simp]= F1_set_def W_pre_acquire_set_def W_post_acquire_set_def
                              R_pre_dequeue_set_def R_post_dequeue_set_def

(*Recorded variables*)
record rb_state =
  H :: nat
  T :: nat
  hW ::  nat               (*local copy of W*)
  tW ::  nat               (*local copy of W*)
  offset :: nat
  q :: "(nat \<times> nat) list"
  tempR :: "(nat \<times> nat)"          (*local copy of word by R*)


  data_index :: "(nat \<times> nat) \<Rightarrow> nat"   (*state of the buffer contents*)
  pcW :: PCW           (*records program counter of W*)
  pcR :: PCR           (*records program counter of W*)
  Data:: "nat  \<Rightarrow> nat"     (*returns a word Data_i*)

  tR :: nat
  numReads :: nat     (* how many words the reader has read *)
  numWrites :: nat    (* how many words the writer has written *)
  numEnqs :: nat  (* how many words from Data the writer has enqueued  *)
  numDeqs :: nat  (* how many words from Data the reader has retrieved *)
  ownT ::  F
  ownD :: "nat \<Rightarrow> F" (* ownership of Data indices *)
  ownB :: "nat \<Rightarrow> F" (* ownership of bytes in buffer *)

  

definition "con_assms s \<equiv>   0 < N \<and> 0<n  \<and> N>n \<and> numEnqs s\<le>n \<and> (numDeqs s\<le>numEnqs s)
                             \<and> (\<forall>i.(i<n)\<longrightarrow>Data s i\<le>N \<and> Data s i>0 )"

definition push_H :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`H := _" [200])
  where 
  "push_H v \<equiv> \<lambda>s. s \<lparr>H := v\<rparr>"
definition push_T :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`T := _" [200])
  where 
  "push_T v \<equiv> \<lambda>s. s \<lparr>T := v\<rparr>"
definition write_data_index :: "nat \<times> nat \<Rightarrow> nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`B.write _ := _" [200])  where
  "write_data_index a v  \<equiv>  
      \<lambda>s. s \<lparr> data_index  := \<lambda> x. if  a = x  then v else data_index s x \<rparr>"  
definition change_writes :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`numWrites := _" [200])
  where 
  "change_writes v \<equiv> \<lambda>s. s \<lparr>numWrites := v\<rparr>"
definition change_reads :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`numReads := _" [200])
  where 
  "change_reads v \<equiv> \<lambda>s. s \<lparr>numReads := v\<rparr>"
definition push_offset :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`offset := _" [200])
  where 
  "push_offset v \<equiv> \<lambda>s. s \<lparr>offset := v\<rparr>"


definition trans_ownT :: "F \<Rightarrow> F \<Rightarrow> rb_state \<Rightarrow> rb_state \<Rightarrow> rb_state" ("transownT [_ _ _]" [200]) where
  "trans_ownT a b s \<equiv> if ownT s = a then (\<lambda>s. s \<lparr> ownT := b \<rparr>)
                                    else (\<lambda>s. s \<lparr> ownT := ownT s\<rparr>)"

definition transfer_ownB :: "F \<Rightarrow> F \<Rightarrow> rb_state \<Rightarrow> rb_state" ("transownB [_ _]" [200]) where
  "transfer_ownB a b \<equiv> (\<lambda>s. s \<lparr> ownB := \<lambda> i. if (ownB s i = a)\<and>i\<le>N then b else (ownB s) i\<rparr>)"

definition set_ownB :: "nat\<times>nat\<Rightarrow> F \<Rightarrow> rb_state \<Rightarrow> rb_state" ("setownB [_ _]" [200]) where
  "set_ownB x a \<equiv> (\<lambda>s. s \<lparr> ownB := \<lambda> i. if ((i\<ge>fst(x)) \<and> (i<snd(x))) then a else (ownB s) i\<rparr>)"

definition transfer_ownD :: "nat\<Rightarrow> F \<Rightarrow> rb_state \<Rightarrow> rb_state" ("transownD [_ _]" [200]) where
  "transfer_ownD x a \<equiv> (\<lambda>s. s \<lparr> ownD := \<lambda> i. if i=x then a else (ownD s) i\<rparr>)"




(*-----------------------*)

definition set_hW :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`hW := _" [200])  where
  "set_hW v  \<equiv> \<lambda>s. s \<lparr> hW  := v\<rparr>"
definition set_tW :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`tW := _" [200])  where
  "set_tW v  \<equiv> \<lambda>s. s \<lparr> tW  := v\<rparr>"
definition set_tR :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`tR := _" [200])  where
  "set_tR v  \<equiv> \<lambda>s. s \<lparr> tR  := v\<rparr>"
definition set_tempR :: "(nat \<times> nat) \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`tempR := _" [200]) where
  "set_tempR v \<equiv> \<lambda>s. s \<lparr> tempR := v\<rparr>"
definition update_numEnqs :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`numEnqs := _" [200]) where
  "update_numEnqs v\<equiv> \<lambda>s. s \<lparr> numEnqs := v\<rparr>"
definition update_numDeqs :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`numDeqs := _" [200]) where
  "update_numDeqs v\<equiv> \<lambda>s. s \<lparr> numDeqs := v\<rparr>"
definition update_pcW :: "PCW \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`pcW := _" [200]) where
  "update_pcW v \<equiv> \<lambda>s. s \<lparr> pcW := v\<rparr>"
definition update_pcR :: "PCR \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`pcR := _" [200]) where
  "update_pcR v \<equiv> \<lambda>s. s \<lparr> pcR := v\<rparr>"
abbreviation update_b_err :: "rb_state \<Rightarrow> rb_state" ("ERROOM") where
  "update_b_err \<equiv> \<lambda>s. s \<lparr> pcW := OOM \<rparr>"
abbreviation update_bts_err :: "rb_state \<Rightarrow> rb_state" ("ERRBTS") where
  "update_bts_err \<equiv> \<lambda>s. s \<lparr> pcW := BTS \<rparr>"
definition update_q :: "(nat \<times> nat) list \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`q := _" [200])
  where 
  "update_q v  \<equiv> \<lambda>s. s \<lparr>q := v\<rparr>"
lemmas functs [simp] = push_H_def push_T_def set_hW_def set_tW_def
                        update_numEnqs_def update_numDeqs_def
                        set_tempR_def 
                        update_pcW_def update_pcR_def
                        transfer_ownB_def transfer_ownD_def trans_ownT_def
                        update_q_def
                        push_offset_def write_data_index_def
                        change_writes_def change_reads_def
                        set_tR_def set_ownB_def





(*  Define the if statement "guards"  *)

definition "off bo \<equiv> fst bo"
definition "len bo \<equiv> snd bo"
definition "grd1 s \<equiv> (tW s = hW s) \<and> (Data s (numEnqs s) \<le> N)"
definition "grd2 s \<equiv> (tW s > hW s) \<and> (Data s (numEnqs s) < (tW s - hW s))"
definition "grd3 s \<equiv> tW s < hW s"
definition "grd4 s \<equiv> Data s (numEnqs s) \<le> N - hW s"
definition "grd5 s \<equiv> Data s (numEnqs s) < tW s"
definition "no_space_for_word s \<equiv> (grd1 s \<longrightarrow> \<not>(Data s (numEnqs s) \<le> N))\<and>
                                  (grd2 s \<longrightarrow> \<not>(Data s (numEnqs s) < (tW s - hW s)))\<and>
                                  (grd3 s \<longrightarrow> \<not>(Data s (numEnqs s) \<le> N - hW s \<or> Data s (numEnqs s) < tW s))"
lemmas grd_simps [simp] = off_def len_def grd1_def grd2_def grd3_def grd4_def grd5_def no_space_for_word_def 
(***********************************************************************)





(*  Initial State  *)

definition "init s \<equiv> (H s = 0) \<and> (T s = 0) \<and> (offset s = 0) \<and> q s = [] \<and> (hW s = 0) \<and> (tW s = 0) \<and> (tR s = 0)
                        \<and> numReads s = 0 \<and> numWrites s = 0 \<and> (numEnqs s = 0) \<and> (numDeqs s = 0)
                        \<and> ( pcW s = idleW)
                        \<and> ( pcR s = idleR)
                        \<and> (\<forall>l. (l<n) \<longrightarrow>  ((Data s l > 0)\<and>(Data s l \<le> N)))
                        \<and> (\<forall>i. (i<n) \<longrightarrow>  ownD s i = W)
                        \<and> (\<forall>i. (i<N) \<longrightarrow>  ownB s i = B)
                        \<and> (ownB s N = None)
                        \<and> (ownT s = Q)
                        \<and> (tempR s = (0,0))
                        \<and> (\<forall>i. (i\<le>N)\<longrightarrow>(\<forall>j.(j\<le>N)\<longrightarrow>data_index s (i,j) <n))"
(***********************************************************************)



definition "case_1 s  \<equiv> \<exists>a b c d. (0\<le>a \<and> a\<le>b \<and> b\<le>c \<and> c\<le>d \<and> d\<le>N 
                                        \<and>(\<forall>i.(0\<le>i \<and> i<a)\<longrightarrow>ownB s i = B)
                                        \<and>(\<forall>i.(a\<le>i \<and> i<b)\<longrightarrow>ownB s i = R)
                                        \<and>(\<forall>i.(b\<le>i \<and> i<c)\<longrightarrow>ownB s i = Q)
                                        \<and>(\<forall>i.(c\<le>i \<and> i<d)\<longrightarrow>ownB s i = W)
                                        \<and>(\<forall>i.(d\<le>i \<and> i<N)\<longrightarrow>ownB s i = B)
                                        \<and>(ownB s N = None)
                                \<comment>\<open>general case rules\<close>
                                      \<comment>\<open>rules are simple\<close>
                                \<comment>\<open>describe T using ownB\<close>
                                  \<and>(T s = a)
                                \<comment>\<open>describe H using ownB\<close>
                                  \<and>(H s = d)
                                \<comment>\<open>describe W view (tempW) using ownB\<close>
                                  \<and>(d>c\<longrightarrow>offset s=c)
                                  \<and>(d>c\<longrightarrow>Data s (numEnqs s)=d-c)
                                \<comment>\<open>describe R view (tempR) using ownB\<close>
                                  \<and>(b>a\<longrightarrow>fst(tempR s)=a)
                                  \<and>(b>a\<longrightarrow>snd(tempR s)=b-a)
                                \<comment>\<open>describe Q view (hd(Q), last(Q)) using ownB\<close>
                                  \<and>(c>b\<longleftrightarrow>length(q s)>0)
                                  \<and>(c>b\<longrightarrow>fst(hd(q s)) =b)
                                  \<and>(c>b\<longrightarrow>fst(last(q s))+snd(last(q s)) =c)
                                \<comment>\<open>describe ownT using ownB\<close>
                                  \<and>(ownT s = R\<longrightarrow>b>a)
                                  \<and>((b=a\<and>c>b)\<longrightarrow>ownT s = Q)
                                  \<and>((b=a\<and>c=b)\<longrightarrow>ownT s \<in> {Q,W})
                                  \<and> (ownT s=W\<longrightarrow>((c=0\<and>d>0)\<or>(H s=T s)))
)"


lemma can_a_equal_d:
  assumes "\<forall>i.(i<N)\<longrightarrow>ownB s i=B"
  and "ownT s=Q"
  and "H s=k"
  and "T s=k"
  and "k<N"  
  and "q s=[]"
  and "ownB s N=None"
  shows "case_1 s"
  using assms apply (simp add:case_1_def)
  apply (rule_tac exI [where x ="k"])
  apply (rule_tac exI [where x ="k"])
  apply simp
  apply (rule_tac exI [where x ="k"])
  by simp



definition "case_2 s  \<equiv> \<exists>a b c d e f. (0\<le>a \<and> a\<le>b \<and> b\<le>c \<and> c<d \<and> d\<le>e \<and> e\<le>f \<and> f\<le>N
                                        \<and>(\<forall>i.(0\<le>i \<and> i<a)\<longrightarrow>ownB s i = R)
                                        \<and>(\<forall>i.(a\<le>i \<and> i<b)\<longrightarrow>ownB s i = Q)
                                        \<and>(\<forall>i.(b\<le>i \<and> i<c)\<longrightarrow>ownB s i = W)
                                        \<and>(\<forall>i.(c\<le>i \<and> i<d)\<longrightarrow>ownB s i = B)
                                        \<and>(\<forall>i.(d\<le>i \<and> i<e)\<longrightarrow>ownB s i = R)
                                        \<and>(\<forall>i.(e\<le>i \<and> i<f)\<longrightarrow>ownB s i = Q)
                                        \<and>(\<forall>i.(f\<le>i \<and> i<N)\<longrightarrow>ownB s i = D)
                                        \<and>(ownB s N = None)
                                \<comment>\<open>general case rules\<close>
                                  \<and>(a>0\<longrightarrow>e=d)                  \<comment>\<open>only 1 continuous read\<close>  
                                  \<and>(e>d\<longrightarrow>a=0)                  \<comment>\<open>only 1 continuous read\<close>  
                                  \<and>(f>e\<longrightarrow>a=0)                  \<comment>\<open>only 1 continuous queue\<close> 
                                  \<and>(c>0)                  \<comment>\<open>create the overlap, any way possible\<close> 
                                \<comment>\<open>describe T using ownB\<close>
                                  \<and>(T s = d)
                                \<comment>\<open>describe H using ownB\<close>
                                  \<and>(H s = c)
                                \<comment>\<open>describe W view (tempW) using ownB\<close>
                                  \<and>(c>b\<longrightarrow>offset s = b)
                                  \<and>(c>b\<longrightarrow>Data s (numEnqs s) = c-b)
                                \<comment>\<open>describe R view (tempR) using ownB\<close>
                                  \<and>(a>0\<longrightarrow>fst(tempR s)=0) 
                                  \<and>(a>0\<longrightarrow>snd(tempR s)=a)  
                                  \<and>(e>d\<longrightarrow>fst(tempR s)=d) 
                                  \<and>(e>d\<longrightarrow>snd(tempR s)=e-d)  
                                \<comment>\<open>describe Q view (hd(Q), last(Q)) using ownB\<close>
                                  \<and>((f>e\<or>b>a)\<longleftrightarrow>length(q s)>0)
                                  \<and>(f>e\<longrightarrow>fst(hd(q s)) =e)
                                  \<and>((f=e\<and>b>a)\<longrightarrow>fst(hd(q s)) =a)
                                  \<and>(b>a\<longrightarrow>fst(last(q s))+snd(last(q s)) =b)
                                  \<and>((b=a\<and>f>e)\<longrightarrow>fst(last(q s))+snd(last(q s)) =f)
                                \<comment>\<open>describe ownT using ownB\<close>
                                  \<and>(ownT s = R\<longrightarrow>(a>0\<or>e>d))
                                  \<and>((a=0\<and>e=d)\<longrightarrow>ownT s = Q)
                                  \<and>(ownT s\<noteq>W)
)"



lemma natural:
  assumes "a\<in>{0,3,4}"
  shows "a\<in>\<nat>"
  using assms apply simp
  by auto



lemma case_split:
  shows "H s\<ge>T s\<Longrightarrow> (case_1 s \<or> case_2 s) \<Longrightarrow> case_1 s"
  apply (simp add:case_1_def case_2_def) apply clarify
  by linarith


lemma case_split_2:
  shows "H s\<ge>T s\<Longrightarrow> (case_1 s \<or> case_2 s) \<Longrightarrow>\<not> case_2 s"
  by (simp add:case_1_def case_2_def) 

lemma case_split_3:
  shows "H s<T s\<Longrightarrow> (case_1 s \<or> case_2 s) \<Longrightarrow> case_2 s"
  apply (simp add:case_1_def case_2_def) apply clarify
  by linarith


lemma case_split_4:
  shows "H s<T s\<Longrightarrow> (case_1 s \<or> case_2 s) \<Longrightarrow>\<not> case_1 s"
  by (simp add:case_1_def case_2_def)


lemma case_split_5:
  shows "(case_1 s \<and> case_2 s) \<Longrightarrow>False"
  apply (simp add:case_1_def case_2_def) 
  apply clarify
  apply (case_tac "H s\<ge>T s") 
  apply(subgoal_tac "case_1 s") prefer 2 
  apply (metis leD)
  apply (metis case_split_4)
  apply(subgoal_tac "T s>H s") prefer 2
  apply blast
  apply(subgoal_tac "case_2 s") prefer 2
  apply (metis le_trans)
  using case_split_2 [where s=s] 
  by (metis le_trans)




(*
declare [[show_types]]
*)




(*   State of the queue   *)
(*   What Q should look like   *)

definition  "end x \<equiv> fst x + snd x"

lemmas end_simp [simp] = end_def 

definition "Q_boundness s \<equiv> (\<forall>x. (x \<in> set (q s)) \<longrightarrow> end x \<le> N)" 

definition "Q_offsets_differ s \<equiv> (\<forall>i j.(i<length(q s)\<and> j<length(q s)\<and> i\<noteq>j)\<longrightarrow>(fst(q s!i)\<noteq>fst(q s!j)))"

definition "Q_gap_structure s   \<equiv> 
          (\<forall>i. (i < length(q s) \<and> i > 0) \<longrightarrow>((end(q s!(i-1)) = fst(q s!i))\<or> (fst(q s!i) =0)))"

definition "Q_has_no_uroboros s \<equiv>
(\<forall>x. x \<in> set (q s)\<longrightarrow> fst x \<noteq> end (last (q s)))"

definition "Q_has_no_overlaps s \<equiv>
(\<forall> x y. (x \<in> set (q s) \<and> y \<in> set (q s)) \<longrightarrow> (fst(x) < fst(y) \<longrightarrow> end x \<le> fst y))"

definition "Q_elem_size s       \<equiv> \<forall>x.(x\<in>set(q s))\<longrightarrow>snd(x)>0"

definition "Q_basic_struct s \<equiv> Q_boundness s \<and> Q_gap_structure s \<and> Q_offsets_differ s
                              \<and> Q_has_no_overlaps s \<and> Q_has_no_uroboros s \<and> Q_elem_size s"


lemmas Q_basic_lemmas = Q_basic_struct_def  Q_has_no_overlaps_def 
                        Q_gap_structure_def Q_has_no_uroboros_def
                        Q_boundness_def     Q_offsets_differ_def
                        Q_elem_size_def

lemma proof_no_overlaps:
  assumes "Q_gap_structure s"
  and "Q_offsets_differ s"
  and "\<forall>i.(i<length(q s))\<longrightarrow> snd(q s!i)>0"
  and "length(q s)>1"
  and "Q_has_no_overlaps s"
shows "\<forall>x y.(x\<in>set(q s)\<and>y\<in>set(q s)\<and>length(q s)>1\<and>fst(x)\<noteq>fst(y))\<longrightarrow>
  (\<forall>j.(fst(x)\<le>j \<and> j<end(x))\<longrightarrow>(j<fst(y)\<or>j\<ge>end(y)))"
  using assms apply (simp add:Q_basic_lemmas) 
  apply safe 
  by (smt (verit, best) bot_nat_0.not_eq_extremum diff_is_0_eq le_trans linorder_neqE_nat zero_less_diff)

lemma tail_preserves_Q_boundness:
  assumes "Q_boundness s"
  and "tl(q s)\<noteq>[]"
shows "(\<forall>x. (x \<in> set (tl(q s))) \<longrightarrow> end x \<le> N)"
  using assms  apply (simp add:Q_boundness_def)
  by (simp add: list.set_sel(2) tl_Nil)

lemma tail_preserves_Q_offsets_differ:
  assumes "Q_offsets_differ s"
  and "tl(q s)\<noteq>[]"
shows "(\<forall>i j.(i<length(tl(q s))\<and> j<length(tl(q s))\<and> i\<noteq>j)\<longrightarrow>(fst((tl(q s))!i)\<noteq>fst((tl(q s))!j)))"
  using assms  apply (simp add:Q_offsets_differ_def) 
  by (simp add: Nitpick.size_list_simp(2) nth_tl tl_Nil)

lemma tail_preserves_Q_gap_structure:
  assumes "Q_gap_structure s"
  and "tl(q s)\<noteq>[]"
shows "(\<forall>i. (i < length(tl(q s)) \<and> i > 0) \<longrightarrow>((end((tl(q s))!(i-1)) = fst((tl(q s))!i))\<or> (fst((tl(q s))!i) =0)))"
  using assms  apply (simp add:Q_gap_structure_def) 
  by (smt (verit) One_nat_def Suc_pred add_diff_cancel_left' length_tl less_Suc_eq less_diff_conv not_less_eq nth_tl plus_1_eq_Suc)

lemma tail_preserves_Q_has_no_uroboros:
  assumes "Q_has_no_uroboros s"
  and "tl(q s)\<noteq>[]"
shows "(\<forall>x. x \<in> set (tl(q s)) \<longrightarrow> fst x \<noteq> end (last (tl(q s))))"
  using assms  apply (simp add:Q_has_no_uroboros_def)
  by (metis last_tl list.sel(2) list.set_sel(2))

lemma tail_preserves_Q_has_no_overlaps:
  assumes "Q_has_no_overlaps s"
  and "tl(q s)\<noteq>[]"
shows "(\<forall> x y. (fst(x) < fst(y) \<and> x \<in> set (tl(q s)) \<and> y \<in> set (tl(q s))) \<longrightarrow> (end x \<le> fst y))"
  using assms  apply (simp add:Q_has_no_overlaps_def) 
  by (metis list.sel(2) list.set_sel(2))

lemma tail_preserves_Q_basic_struct:
  assumes "Q_basic_struct s"
  and "tl(q s)\<noteq>[]"
shows "(\<forall>x. (x \<in> set (tl(q s))) \<longrightarrow> end x \<le> N) \<and> 
       (\<forall>i j.(i<length(tl(q s))\<and> j<length(tl(q s))\<and> i\<noteq>j)\<longrightarrow>(fst((tl(q s))!i)\<noteq>fst((tl(q s))!j))) \<and>
       (\<forall>i. (i < length(tl(q s)) \<and> i > 0) \<longrightarrow>((end((tl(q s))!(i-1)) = fst((tl(q s))!i))\<or> (fst((tl(q s))!i) =0)))\<and>
       (\<forall>x. x \<in> set (tl(q s)) \<longrightarrow> fst x \<noteq> end (last (tl(q s)))) \<and>
       (\<forall> x y. (fst(x) < fst(y) \<and> x \<in> set (tl(q s)) \<and> y \<in> set (tl(q s))) \<longrightarrow> (end x \<le> fst y))"
  using assms  apply (simp add:Q_basic_lemmas)
  apply(intro conjI impI)
  apply (metis list.sel(2) list.set_sel(2))
  using tail_preserves_Q_offsets_differ apply (metis One_nat_def Q_basic_struct_def assms(1) length_tl)
  using tail_preserves_Q_gap_structure apply (metis One_nat_def Q_basic_struct_def assms(1) end_simp length_tl)
  using tail_preserves_Q_has_no_uroboros apply (metis Q_basic_struct_def assms(1) end_simp old.prod.inject prod.collapse)
  by (metis list.sel(2) list.set_sel(2))











(*
(*have the idea of "can fit between T-N or not"*)
definition "T_is_outside_Q s    \<equiv> (\<forall>i.(i<length(q s) \<and> q s\<noteq>[])\<longrightarrow>(end(q s!i)<T s))"

definition "tempR_describes_T s \<equiv> ((fst(tempR s) =0) \<longrightarrow> (T s=0 \<or> T_is_outside_Q s))
                                 \<and>((fst(tempR s) >0) \<longrightarrow> (T s=fst(tempR s)))"

definition "Q_describes_T s     \<equiv> ((fst(hd(q s)) =0) \<longrightarrow> (T s=0 \<or> T_is_outside_Q s))
                                 \<and>((fst(hd(q s)) >0) \<longrightarrow> (T s=fst(hd(q s))))"
*)


(*have the idea of "can we describe ownB s i=R"*)
(*
definition "R_owns_no_bytes s   \<equiv> (\<forall>i.(i\<ge>0)\<longrightarrow>ownB s i\<noteq>R)"

definition "tempR_describes_ownB s \<equiv> (\<forall>i.(i<fst(tempR s))\<longrightarrow>ownB s i\<noteq>R)
                                    \<and>(\<forall>i.(i\<ge>end(tempR s))\<longrightarrow>ownB s i\<noteq>R)
                                    \<and>(\<forall>i.(fst(tempR s)\<le>i \<and> i<end(tempR s))\<longrightarrow>ownB s i=R)"
*)






definition "tempR_bounded s     \<equiv> end(tempR s)\<le>N"
definition "Q_no_overlap_tempR s\<equiv> (\<forall>x. (x \<in> set (q s))\<longrightarrow>
                  ((fst(tempR s)<fst(x)\<and>end(tempR s)\<le> fst(x))
                  \<or>(fst(x)<fst(tempR s)\<and>end(x)<fst(tempR s))))"
definition "Q_relates_tempR s   \<equiv> (end(tempR s) = fst(hd (q s))) \<or> (fst(hd(q s)) = 0)"
lemmas tmepR_extra_lemmas [simp] = tempR_bounded_def Q_no_overlap_tempR_def Q_relates_tempR_def


(*   Relating Q to other variables   *)
(*
definition "Q_bytes s     \<equiv> {i  . \<exists> k l. (k, l) \<in> set(q s) \<and> k \<le> i \<and> i < k+l}"

definition "Q_bytes_inv s \<equiv> \<forall> i. i \<in> Q_bytes s \<longleftrightarrow>  ownB s i = Q"

*)



  




definition "Q_holds_bytes s     \<equiv> q s\<noteq>[]\<longrightarrow>(\<forall>i.(i\<in>set(q s))\<longrightarrow>(\<forall>j.(fst(i)\<le>j \<and> j<end(i))\<longrightarrow>ownB s j=Q))"

definition "Q_reflects_writes s \<equiv> (\<forall>i.(i<length(q s))\<longrightarrow>data_index s (q s!i) = ((numDeqs s) +i))"

definition "Q_elem_rel s        \<equiv> (\<forall>i.(i<length(q s))\<longrightarrow>snd(q s!i) =Data s ((numDeqs s) +i))"

definition "Q_reflects_ownD s   \<equiv> (\<forall>i.(i<length(q s))\<longrightarrow>ownD s (i+(numDeqs s)) =B)"





lemma tail_preserves_Q_holds_bytes:
  assumes "Q_holds_bytes s"
  and "(tl(q s))\<noteq>[]"
shows "(tl(q s))\<noteq>[]\<longrightarrow>(\<forall>i.(i\<in>set(tl(q s)))\<longrightarrow>(\<forall>j.(fst(i)\<le>j \<and> j<end(i))\<longrightarrow>ownB s j=Q))"
  using assms  apply (simp add:Q_holds_bytes_def)
  by (metis list.sel(2) list.set_sel(2))

lemma tail_preserves_Q_reflects_writes:
  assumes "Q_reflects_writes s"
  and "(tl(q s))\<noteq>[]"
shows "(\<forall>i.(i<length(tl(q s)))\<longrightarrow>data_index s ((tl(q s))!i) = ((numDeqs s) +i +1))"
  using assms  apply (simp add:Q_reflects_writes_def)
  by (simp add: nth_tl)

lemma tail_preserves_Q_elem_size:
  assumes "Q_elem_rel s"
  and "(tl(q s))\<noteq>[]"
shows "(\<forall>i.(i<length(tl(q s)))\<longrightarrow>snd((tl(q s))!i) =Data s ((numDeqs s) +i +1))"
  using assms  apply (simp add:Q_elem_size_def)
  by (simp add: Q_elem_rel_def nth_tl)

lemma tail_preserves_Q_reflects_ownD:
  assumes "Q_reflects_ownD s"
  and "(tl(q s))\<noteq>[]"
shows "(\<forall>i.(i<length(tl(q s)))\<longrightarrow>ownD s (i+(numDeqs s) +1) =B)"
  using assms  apply (simp add:Q_reflects_ownD_def) 
  by (metis One_nat_def Suc_eq_plus1 add.assoc less_diff_conv plus_1_eq_Suc)

lemma Q_offsets_imply_tail_offsets:
  assumes "Q_offsets_differ s"
  shows "(\<forall>i j.(i<length(tl(q s))\<and> j<length(tl(q s))\<and> i\<noteq>j)\<longrightarrow>(fst(tl(q s)!i)\<noteq>fst(tl(q s)!j)))"
  using assms apply (simp add:Q_offsets_differ_def)
  by (metis (no_types, lifting) Nat.lessE One_nat_def Suc_pred length_tl less_Suc_eq_0_disj nth_tl old.nat.inject zero_less_diff)

lemma Q_head_relates_tail:
  assumes "Q_offsets_differ s"
  shows "\<forall>i.(i<length(tl(q s)))\<longrightarrow>fst(q s!0)\<noteq> fst(tl(q s)!i)"
  using assms apply (simp add:Q_offsets_differ_def)
  by (metis One_nat_def Suc_pred length_tl less_Suc_eq_0_disj not_less_eq nth_tl zero_less_diff)

lemma Exists_one_implies_exist_no_more:
  assumes "Q_offsets_differ s"
  and "Q_gap_structure s"
shows "if \<exists>j.(fst(q s!j) =0 \<and> j<length(q s)) then (\<exists>j.(\<forall>i.(i<length(q s) \<and> i\<noteq>j \<and> i>0)\<longrightarrow>(end(q s!(i-1)) =fst(q s!i))))
  else (\<forall>i.(i>0 \<and> i<length(q s))\<longrightarrow>end(q s!(i-1)) = fst(q s!i))"
  using assms apply (simp add:Q_basic_lemmas)
  apply (case_tac "\<exists>j.(fst(q s!j) =0 \<and> j<length(q s))", simp_all)
  apply (metis gr_implies_not0)
  by (metis less_nat_zero_code)
  
lemma Q_hd_zero_implies_structure:
  assumes "Q_offsets_differ s"
  and "Q_gap_structure s"
  and "fst(hd(q s)) =0"
shows "\<forall>i.(i>0 \<and> i<length(q s))\<longrightarrow>end(q s!(i-1)) =fst(q s!i)"
  using assms apply(simp add:Q_basic_lemmas)
  by (metis drop0 hd_drop_conv_nth less_Suc_eq_0_disj less_imp_Suc_add not_gr_zero)

lemma data_index_preserved_lemma:
  assumes "Q_reflects_writes s"
  and "length(q s)>0"
  shows "data_index s(q s!0) = numDeqs s"
  using assms by (simp add:Q_reflects_writes_def)


definition "Q_structure s \<equiv>q s\<noteq>[]\<longrightarrow>(Q_basic_struct s \<and> 
                                      \<comment> \<open>Q_holds_bytes s \<and>\<close>
                                      Q_reflects_writes s \<and> 
                                      Q_elem_rel s \<and> 
                                      Q_reflects_ownD s)"


 
lemmas Q_lemmas = Q_holds_bytes_def Q_reflects_writes_def Q_reflects_ownD_def
                  Q_structure_def Q_relates_tempR_def Q_elem_rel_def
                  Q_elem_size_def Q_no_overlap_tempR_def



lemma head_q0:
  assumes "length(q s)>0"
  shows "hd(q s) = (q s!0)"
  using assms apply (simp add:Q_reflects_writes_def)
  by (simp add: hd_conv_nth)

lemma overlap:
  assumes "Q_structure s \<and> length(q s)>1"
  shows "\<nexists>k.(\<forall>i j.(i<length(q s)\<and> j<length(q s)\<and> i\<noteq>j)\<longrightarrow>(k\<ge>fst(q s!i)\<and> k<end(q s!i)\<and>k\<ge>fst(q s!j)\<and>k<end(q s!j)))"
  using assms apply simp 
  apply(simp add:Q_lemmas Q_basic_lemmas) 
  apply(elim conjE impE) apply clarify 
  apply simp 
  by (smt One_nat_def Suc_lessD add_diff_cancel_left' le_0_eq le_less_trans less_numeral_extra(1) not_less nth_mem plus_1_eq_Suc prod.collapse)

lemma Q_has_0_elem:
  assumes "Q_gap_structure s"
  and "Q_offsets_differ s"
  and "hd(q s) =(0,a)"
shows "fst(hd(q s)) =0\<longrightarrow>(\<forall>i.(i<length(q s)\<and> i>0)\<longrightarrow>end(q s!(i-1)) =fst(q s!i))"
  using assms apply auto
  apply (simp add:Q_gap_structure_def Q_offsets_differ_def)
  by (metis gr_implies_not_zero head_q0 not_gr_zero old.prod.inject prod.collapse)


lemma Q_gap_lemmas_1:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "last(q s)\<in>set(q s)"
  using assms by (simp add:con_assms_def)

lemma Q_gap_lemmas_2:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>i.(i<length(q s))\<longrightarrow>(q s!i)\<in>set(q s)"
  using assms by (simp add:con_assms_def)

lemma Q_gap_lemmas_3:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>x y.(x\<in>set(q s) \<and> y\<in>set(q s) \<and> fst(y)\<noteq>fst(x))\<longrightarrow>(fst(x)>fst(y)\<or>fst(y)>fst(x))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by linarith


lemma Q_gap_lemmas_4:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>x y.(x\<in>set(q s) \<and> y\<in>set(q s) \<and> fst(y)>fst(x))\<longrightarrow>end(y)>fst(x)"
  using assms by (simp add:con_assms_def Q_lemmas Q_basic_lemmas)

lemma Q_gap_lemmas_5:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>x y.(x\<in>set(q s) \<and> y\<in>set(q s) \<and> fst(y)>fst(x))\<longrightarrow>(fst(y)\<ge>end(x))"
  using assms by (simp add:con_assms_def Q_lemmas Q_basic_lemmas)

lemma Q_gap_lemmas_6:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>x y.(x\<in>set(q s) \<and> y\<in>set(q s) \<and> fst(y)>fst(x))\<longrightarrow>(end(y)>end(x))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (smt (verit, best) diff_add_inverse diff_is_0_eq le_add1 le_neq_implies_less le_trans length_greater_0_conv list.size(3))

lemma Q_gap_lemmas_7:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>x y.(x\<in>set(q s) \<and> y\<in>set(q s) \<and> fst(y)\<ge>end(x))\<longrightarrow>(end(y)>fst(x))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (metis add_leD1 le_neq_implies_less less_add_same_cancel1 trans_less_add1)

lemma Q_gap_lemmas_8:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>x y.(x\<in>set(q s) \<and> y\<in>set(q s) \<and> fst(y)\<ge>end(x))\<longrightarrow>(fst(y)>fst(x))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (metis add_leD1 diff_add_0 diff_add_inverse diff_diff_cancel minus_nat.diff_0 nat_less_le)

lemma Q_gap_lemmas_9:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>x y.(x\<in>set(q s) \<and> y\<in>set(q s) \<and> fst(y)\<ge>end(x))\<longrightarrow>(end(y)>end(x))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (metis le_eq_less_or_eq less_add_same_cancel1 trans_less_add1)

lemma Q_gap_lemmas_10:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>x y.(x\<in>set(q s) \<and> y\<in>set(q s) \<and> end(y)>fst(x) \<and> fst(y)\<noteq>fst(x))\<longrightarrow>(fst(y)>fst(x))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (metis le_antisym less_or_eq_imp_le nat_neq_iff)

lemma Q_gap_lemmas_11:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>x y.(x\<in>set(q s) \<and> y\<in>set(q s) \<and> end(y)>fst(x) \<and> fst(y)\<noteq>fst(x))\<longrightarrow>(end(y)>end(x))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (smt (verit, ccfv_SIG) diff_add_inverse diff_is_0_eq le_antisym le_trans less_or_eq_imp_le nat_neq_iff)


lemma Q_gap_lemmas_12:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>x y.(x\<in>set(q s) \<and> y\<in>set(q s) \<and> end(y)>fst(x) \<and> fst(y)\<noteq>fst(x))\<longrightarrow>(fst(y)\<ge>end(x))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (metis le_antisym less_or_eq_imp_le nat_neq_iff)


lemma Q_gap_lemmas_13:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>x y.(x\<in>set(q s) \<and> y\<in>set(q s) \<and> end(y)>end(x))\<longrightarrow>(end(y)>fst(x))"
  using assms by (simp add:con_assms_def Q_lemmas Q_basic_lemmas)



lemma Q_gap_lemmas_14:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>x y.(x\<in>set(q s) \<and> y\<in>set(q s) \<and> end(y)>end(x) \<and> fst(y)\<noteq>fst(x))\<longrightarrow>(fst(y)\<ge>end(x))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (metis diff_diff_left diff_is_0_eq less_nat_zero_code linorder_neqE_nat zero_less_diff)


lemma Q_gap_lemmas_15:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>x y.(x\<in>set(q s) \<and> y\<in>set(q s) \<and> end(y)>end(x))\<longrightarrow>(fst(y)\<noteq>fst(x))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (metis fst_conv in_set_conv_nth nat_neq_iff old.prod.inject)

lemma Q_gap_lemmas_16_B:
  assumes "Q_structure s"
  and "length(q s) >0"
  and "x\<in>set(q s)" 
  and "y\<in>set(q s)" 
  and "end(y)>end(x)"
shows "fst(y)\<ge>end(x)"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas) 
  using Q_gap_lemmas_14 Q_gap_lemmas_15
  by (metis assms(1) assms(2) end_simp fst_conv snd_conv)


lemma Q_gap_lemmas_16:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>x y.(x\<in>set(q s) \<and> y\<in>set(q s) \<and> end(y)>end(x))\<longrightarrow>(fst(y)\<ge>end(x))"
  using Q_gap_lemmas_16_B assms by blast



lemma Q_gap_lemmas_17:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>x y.(x\<in>set(q s) \<and> y\<in>set(q s) \<and> end(y)>end(x))\<longrightarrow>(fst(y)>fst(x))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (metis Q_gap_lemmas_15 Q_gap_lemmas_10 add_lessD1 assms(1) assms(2) end_simp fst_conv snd_conv)





lemma Q_gap_lemmas_1_list:
  assumes "Q_structure s"
  and "length(q s) >0"
shows "\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> i\<noteq>j)\<longrightarrow>(fst(q s!i)>fst(q s!j) \<or>
                                                     fst(q s!i)<fst(q s!j))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas) 
  by (meson nat_neq_iff)


lemma Q_gap_lemmas_2_list:
  assumes "Q_structure s"
  and "length(q s) >0"
shows "\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> fst(q s!i)>fst(q s!j))\<longrightarrow>
                            (end(q s!i)>fst(q s!j))"
  using assms by (simp add:con_assms_def Q_lemmas Q_basic_lemmas) 


lemma Q_gap_lemmas_3_list:
  assumes "Q_structure s"
  and "length(q s) >0"
shows "\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> fst(q s!i)>fst(q s!j))\<longrightarrow>
                            (end(q s!i)>end(q s!j))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (metis Q_gap_lemmas_6 assms(1) end_simp length_pos_if_in_set nth_mem)


lemma Q_gap_lemmas_4_list:
  assumes "Q_structure s"
  and "length(q s) >0"
shows "\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> fst(q s!i)>fst(q s!j))\<longrightarrow>
                            (fst(q s!i)\<ge>end(q s!j))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (metis Q_gap_lemmas_2 assms(1) assms(2) prod.collapse)



lemma Q_gap_lemmas_5_list:
  assumes "Q_structure s"
  and "length(q s) >0"
shows "\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> fst(q s!i)\<ge>end(q s!j))\<longrightarrow>
                            (fst(q s!i)>fst(q s!j))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (metis Q_gap_lemmas_8 assms(1) end_simp length_pos_if_in_set nth_mem)



lemma Q_gap_lemmas_6_list:
  assumes "Q_structure s"
  and "length(q s) >0"
shows "\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> fst(q s!i)\<ge>end(q s!j))\<longrightarrow>
                            (end(q s!i)>fst(q s!j))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (metis Q_gap_lemmas_7 assms(1) end_simp length_pos_if_in_set nth_mem)


lemma Q_gap_lemmas_7_list:
  assumes "Q_structure s"
  and "length(q s) >0"
shows "\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> fst(q s!i)\<ge>end(q s!j))\<longrightarrow>
                            (end(q s!i)>end(q s!j))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (metis le_eq_less_or_eq less_add_same_cancel1 nth_mem surjective_pairing trans_less_add1)


lemma Q_gap_lemmas_8_list:
  assumes "Q_structure s"
  and "length(q s) >0"
shows "\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> end(q s!i)>fst(q s!j) \<and> i\<noteq>j)\<longrightarrow>
                            (fst(q s!i)>fst(q s!j))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas) 
  using Q_gap_lemmas_10
  by (metis assms(1) end_simp length_pos_if_in_set nth_mem)

lemma Q_gap_lemmas_9_list_B:
  assumes "Q_structure s"
  and "length(q s) >0"
  and "i<length(q s)" 
  and "j<length(q s)" 
  and "end(q s!i)>fst(q s!j)" 
  and "i\<noteq>j"
shows "end(q s!i)>end(q s!j)"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas) 
  by (metis Q_gap_lemmas_11 assms(1) end_simp length_pos_if_in_set nth_mem)


lemma Q_gap_lemmas_9_list:
  assumes "Q_structure s"
  and "length(q s) >0"
shows "\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> end(q s!i)>fst(q s!j) \<and> i\<noteq>j)\<longrightarrow>
                            (end(q s!i)>end(q s!j))"
  using assms Q_gap_lemmas_9_list_B by blast


lemma Q_gap_lemmas_10_list:
  assumes "Q_structure s"
  and "length(q s) >0"
shows "\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> end(q s!i)>fst(q s!j) \<and> i\<noteq>j)\<longrightarrow>
                            (fst(q s!i)\<ge>end(q s!j))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  using Q_gap_lemmas_12
  by (metis assms(1) end_simp length_pos_if_in_set nth_mem)



lemma Q_gap_lemmas_11_list:
  assumes "Q_structure s"
  and "length(q s) >0"
shows "\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> end(q s!i)>end(q s!j))\<longrightarrow>
                            (end(q s!i)>fst(q s!j))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (metis add_lessD1)


lemma Q_gap_lemmas_12_list:
  assumes "Q_structure s"
  and "length(q s) >0"
shows "\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> end(q s!i)>end(q s!j))\<longrightarrow>
                            (fst(q s!i)\<ge>end(q s!j))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  using Q_gap_lemmas_16 
  by (metis Q_gap_lemmas_2 assms(1) assms(2) end_simp)


lemma Q_gap_lemmas_13_list:
  assumes "Q_structure s"
  and "length(q s) >0"
shows "\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> end(q s!i)>end(q s!j))\<longrightarrow>
                            (fst(q s!i)>fst(q s!j))"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  using Q_gap_lemmas_17
  by (metis Q_gap_lemmas_2 assms(1) assms(2) end_simp)




  



(**********)
lemma ownB_lemma:
  assumes "length(q s) =2"
  and "Q_holds_bytes s"
  and "Q_has_no_overlaps s"
  and "Q_offsets_differ s"
  and "s' = (`q:= (tl(q s)) \<circ> (setownB [(fst(hd(q s)),(end(hd(q s)))) R])) s"
shows "Q_holds_bytes s' "
  using assms apply (simp add:Q_lemmas Q_basic_lemmas)
  apply (intro conjI impI) apply clarify apply safe
  apply simp
      apply simp
     apply auto[1]
  apply(case_tac "a<fst(hd(q s))", simp_all)
  defer
  apply(case_tac "fst(hd(q s))<a", simp_all)

  apply (smt Suc_1 head_q0 le_less_trans length_greater_0_conv list.set_sel(2) not_less nth_mem plus_1_eq_Suc prod.collapse zero_less_two)
  apply(case_tac "fst(hd(q s)) =fst(a,b)") 
  apply (metis (mono_tags, hide_lams) One_nat_def Suc_1 Suc_leI diff_Suc_1 diff_is_0_eq' hd_conv_nth in_set_conv_nth length_tl lessI list.sel(2) nat.simps(3) nth_tl zero_less_Suc)
  apply(simp add:fst_def) 
  apply (metis (no_types, lifting) One_nat_def Suc_1 add_diff_cancel_left' in_set_conv_nth length_tl less_one nat_neq_iff nth_tl plus_1_eq_Suc zero_less_two)
  apply (metis list.sel(2) list.set_sel(2)) 
  by (metis (no_types, lifting) hd_in_set le_add_diff_inverse2 length_0_conv list.set_sel(2) prod.collapse trans_le_add2 verit_comp_simplify1(3) zero_neq_numeral)

(*
lemma ownB_lemma2:
  assumes "Q_holds_bytes s"
  and "Q_structure s"
  and "\<forall>i.(i<n)\<longrightarrow>Data s i>0"
  and "q s\<noteq>[]"
  and "s' = (`q:= (tl(q s)) \<circ> (setownB [(fst(hd(q s)),(end(hd(q s)))) R]) \<circ> (`tempR := (hd(q s))) 
          \<circ> (transownT [Q R s])
          \<circ> (`numDeqs :=(numDeqs s+1))) s"
shows "Q_holds_bytes s'"
  using assms apply (simp add:Q_lemmas Q_basic_lemmas)
  apply(elim conjE impE) 
  apply(case_tac "ownT s=Q", simp_all)
   apply(case_tac "length(q s) =1", simp_all)
  apply (metis diff_Suc_1 length_pos_if_in_set length_tl less_numeral_extra(3))
   apply(case_tac "length(q s) =2", simp_all)
  apply (smt Suc_1 add_diff_cancel_left' fst_conv fst_def hd_conv_nth in_set_conv_nth le_less_trans length_tl less_2_cases_iff less_Suc0 nat_arith.rule0 not_less nth_tl plus_1_eq_Suc prod.collapse)
  apply clarify apply safe
  apply(case_tac "fst(hd(q s)) >a", simp add:fst_def snd_def)
  apply (smt fst_def hd_in_set le_imp_less_Suc le_less_trans list.set_sel(2) not_less_eq prod.collapse)
       defer
  apply(case_tac "fst(hd(q s))<a", simp add:fst_def snd_def)
  apply (meson list.set_sel(2))
  apply (meson list.set_sel(2))
  apply(case_tac "fst(hd(q s)) =fst(a,b)", simp add:fst_def snd_def) 
  apply (smt One_nat_def Suc_mono Suc_pred fst_conv fst_def hd_conv_nth in_set_conv_nth length_greater_0_conv length_tl less_antisym not_less_zero nth_tl zero_induct)
     apply(simp add:fst_def snd_def)
  apply (smt Suc_leI fst_def hd_in_set le_trans linorder_neqE_nat list.set_sel(2) not_less_eq_eq prod.collapse snd_def)
  apply(simp add:fst_def snd_def)
  apply (meson list.set_sel(2))
  apply (meson list.set_sel(2))
  apply clarsimp 
  apply (case_tac "a<fst(hd(q s))", simp_all add:fst_def snd_def)
  apply (case_tac "a>fst(hd(q s))", simp_all add:fst_def snd_def)
  apply (smt fst_def hd_in_set le_less_trans list.set_sel(2) not_less prod.collapse snd_def)
  by (smt One_nat_def Suc_mono Suc_pred fst_conv fst_def hd_conv_nth in_set_conv_nth length_greater_0_conv length_tl less_antisym not_less_zero nth_tl zero_induct)
  
lemma Q_type_1:
  assumes "q s=[(3,2),(5,2),(0,1)] \<and> N=10"
  shows "Q_basic_struct s"
  using assms apply(simp add:Q_basic_struct_def) 
  apply(intro conjI impI)
  apply(simp add:Q_boundness_def)
  apply(simp add:Q_gap_structure_def)
  using less_Suc_eq apply force
  apply(simp add:Q_offsets_differ_def)
  using less_Suc_eq apply fastforce
  apply(simp add:Q_has_no_overlaps_def)
  using less_Suc_eq apply force
  by(simp add:Q_has_no_uroboros_def) 

lemma Q_tail_props:
  shows "\<forall>i.(i<length(q s) \<and> i>0)\<longrightarrow>(((q s)!i) = (tl(q s)!(i-1)))"
  apply simp
  by (simp add: diff_less_mono nth_tl)

lemma Q_basic_preserved:
  assumes "Q_basic_struct s"
  and "s' = (`q:= (tl(q s))) s"
  shows "Q_basic_struct s'"
  using assms apply(simp add:Q_basic_struct_def)
  apply(intro conjI impI)
  apply(simp add:Q_basic_struct_def Q_boundness_def) 
  apply (metis list.sel(2) list.set_sel(2))
     apply(simp add:Q_basic_struct_def Q_gap_structure_def)
    defer
     apply(simp add:Q_offsets_differ_def)
  apply (metis One_nat_def Suc_eq_plus1 diff_Suc_1 length_tl less_diff_conv nth_tl)
    apply(simp add:Q_has_no_overlaps_def)
    apply (metis list.sel(2) list.set_sel(2))
  prefer 2 
   apply (metis One_nat_def assms(1) end_simp length_tl less_nat_zero_code list.size(3) tail_preserves_Q_basic_struct)
  using assms Q_tail_props apply (simp add:Q_has_no_uroboros_def Q_basic_struct_def)
  by (smt (z3) assms(1) empty_iff end_simp fst_conv in_set_butlastD list.set(1) tail_preserves_Q_basic_struct)
(*
lemma Q_basic_preserved2:
  assumes "Q_structure s"
  and "ownT s=Q"
  and "s' =((`q:= (tl(q s)))
          \<circ> (`pcR := Read) 
          \<circ> (`tempR := (hd(q s))) 
          \<circ> (transownT [Q R s])
          \<circ> (`numDeqs :=(numDeqs s+1))
          \<circ> (setownB [(fst(hd(q s)),(end(hd(q s)))) R]))  s"
  shows "Q_structure s'"
  using assms apply simp
  apply(simp add:Q_structure_def)                                        
  apply(intro conjI impI)
      apply(simp add:Q_basic_struct_def)
      apply(intro conjI impI)
  apply(simp add:Q_boundness_def)
  apply (metis list.sel(2) list.set_sel(2))
  apply(simp add:Q_gap_structure_def)
  apply (smt One_nat_def Q_tail_props Suc_diff_le Suc_leI Suc_mono Suc_pred length_greater_0_conv less_SucI list.sel(2))
  apply(simp add:Q_offsets_differ_def)
  apply (metis (no_types, lifting) Nitpick.size_list_simp(2) One_nat_def Suc_mono length_tl list.sel(2) nat.inject nth_tl)
  apply(simp add:Q_has_no_overlaps_def) 
  apply (metis (no_types, lifting) list.sel(2) list.set_sel(2))
  apply(simp add:Q_has_no_uroboros_def)
  apply (metis butlast_tl last_tl list.sel(2) list.set_sel(2))
  using ownB_lemma2 apply (simp add:Q_holds_bytes_def)
     apply clarify
  apply safe 
  apply simp_all apply(case_tac "fst(hd(q s))>a", simp_all)
       apply(simp add:Q_lemmas Q_basic_lemmas fst_def snd_def)
  apply (smt fst_def hd_in_set le_imp_less_Suc le_less_trans list.sel(2) list.set_sel(2) not_less_eq prod.collapse)
       defer
  apply(case_tac "fst(hd(q s))<a", simp_all)
  apply (metis list.sel(2) list.set_sel(2))
  apply (metis list.sel(2) list.set_sel(2))
     defer defer defer 
  apply(case_tac "fst(hd(q s)) =fst(a,b)", simp add:fst_def snd_def Q_lemmas Q_basic_lemmas) 
  apply (smt One_nat_def Suc_mono Suc_pred fst_conv fst_def hd_conv_nth in_set_conv_nth length_greater_0_conv length_tl less_antisym list.sel(2) not_less_zero nth_tl zero_induct)
  apply(simp add:Q_basic_struct_def Q_has_no_overlaps_def fst_def snd_def)
  apply clarify
  apply(simp add:Q_lemmas Q_basic_lemmas fst_def snd_def butlast_def)
  apply (smt fst_def hd_in_set le_less_trans linorder_neqE_nat list.sel(2) list.set_sel(2) not_less prod.collapse snd_def)
  (*finally Q_holds_bytes done*)
  apply(simp add:Q_reflects_writes_def)
  apply (simp add: nth_tl)
   apply(simp add:Q_elem_size_def)
  apply (simp add: nth_tl)
  apply(simp add:Q_reflects_ownD_def)
  using less_diff_conv by auto
  *)

*)

(*tempR used to be part of Q so:.....*)

 definition "tempR_boundness s \<equiv> (end (tempR s) \<le> N)" 

definition "tempR_offsets_differ s \<equiv> (\<forall>i.(i<length(q s))\<longrightarrow>(fst(q s!i)\<noteq>fst(tempR s)))"

definition "tempR_gap_structure s   \<equiv> (end(tempR s) = fst(hd(q s)))\<or> (fst(hd(q s)) =0)"

definition "tempR_has_no_uroboros s \<equiv> (fst (tempR s) \<noteq> end (last (q s)))"

definition "tempR_has_no_overlaps s \<equiv>(\<forall>i.(i<length(q s))\<longrightarrow>((fst(tempR s)<fst(q s!i)\<longrightarrow>end(tempR s)\<le>fst(q s!i))
                                                           \<and>(fst(tempR s)>fst(q s!i)\<longrightarrow>end(q s!i)\<le>fst(tempR s))))"

definition "tempR_basic_struct s \<equiv> tempR_boundness s \<and> (q s\<noteq>[]\<longrightarrow> (tempR_gap_structure s \<and> tempR_offsets_differ s
                              \<and> tempR_has_no_overlaps s \<and> tempR_has_no_uroboros s)) "


lemmas tempR_basic_lemmas = tempR_basic_struct_def  tempR_has_no_overlaps_def 
                            tempR_gap_structure_def tempR_has_no_uroboros_def
                            tempR_boundness_def     tempR_offsets_differ_def


definition "tempR_holds_bytes s     \<equiv> (\<forall>j.(fst(tempR s)\<le>j \<and> j<end(tempR s))\<longrightarrow>ownB s j=R)"

definition "tempR_reflects_writes s \<equiv> (data_index s (tempR s) = ((numDeqs s) -1))"

definition "tempR_elem_size s       \<equiv> (snd(tempR s) =Data s ((numDeqs s) -1))"


definition "tempR_structure s \<equiv>(tempR_basic_struct s \<and> 
                                      tempR_holds_bytes s \<and> tempR_reflects_writes s \<and> tempR_elem_size s)"


lemmas tempR_lemmas = tempR_holds_bytes_def tempR_reflects_writes_def 
                      tempR_elem_size_def   tempR_structure_def
                      


(*tempW will be part of Q so:.....*)
definition "tempW s \<equiv> (offset s, Data s (numEnqs s))"

 definition "tempW_boundness s \<equiv> (end (tempW s) \<le> N)" 

definition "tempW_offsets_differ s \<equiv> (\<forall>i.(i<length(q s))\<longrightarrow>(fst(q s!i)\<noteq>fst(tempW s)))"

definition "tempW_gap_structure s   \<equiv> (fst(tempW s) = end(last(q s)))\<or> (fst(tempW s) =0)"

definition "tempW_has_no_uroboros s \<equiv> (end((tempW s)) \<noteq> fst (hd (q s)))"

definition "tempW_has_no_overlaps s \<equiv>(\<forall>i.(i<length(q s))\<longrightarrow>((fst(tempW s)<fst(q s!i)\<longrightarrow>end(tempW s)<fst(q s!i))
                                                           \<and>(fst(tempW s)>fst(q s!i)\<longrightarrow>end(q s!i)\<le>fst(tempW s))))"

definition "tempW_basic_struct s \<equiv> tempW_boundness s \<and> (q s\<noteq>[]\<longrightarrow> (tempW_gap_structure s \<and> tempW_offsets_differ s
                              \<and> tempW_has_no_overlaps s \<and> tempW_has_no_uroboros s))"


lemmas tempW_basic_lemmas = tempW_basic_struct_def  tempW_has_no_overlaps_def 
                            tempW_gap_structure_def tempW_has_no_uroboros_def
                            tempW_boundness_def     tempW_offsets_differ_def
                            tempW_def


definition "tempW_holds_bytes s     \<equiv> (\<forall>j.(fst(tempW s)\<le>j \<and> j<end(tempW s))\<longrightarrow>ownB s j=W)"

definition "tempW_reflects_writes s \<equiv> (data_index s (offset s, Data s (numEnqs s)) = numEnqs s)"

definition "tempW_structure s \<equiv>(tempW_basic_struct s \<and> 
                                      tempW_holds_bytes s )"


lemmas tempW_lemmas = tempW_holds_bytes_def tempW_reflects_writes_def 
                      tempW_structure_def













(*Writer Thread Behaviour*)


fun rbW_step :: "PCW \<Rightarrow> rb_state \<Rightarrow> rb_state" where
  "rbW_step A1 s = ((`hW := (H s)) \<circ> (`tW := (T s)) \<circ> (`pcW := A2)) s "
| "rbW_step A2 s = (if grd1 s then ((`pcW := A3) \<circ> (transownT [Q W s]))
                     else if grd2 s then (`pcW := A4) 
                     else if grd3 s then (`pcW := A5) 
                     else (`pcW :=A8)) s"
| "rbW_step A3 s = ((`T := 0) \<circ> (`H := (Data s (numEnqs s))) \<circ> (`offset := 0) \<circ> (`pcW := Write) 
                        \<circ> setownB [(0,(Data s (numEnqs s))) W]) s" 
| "rbW_step A4 s = ((`H := ((hW s) + (Data s (numEnqs s)))) \<circ> (`offset := (hW s)) \<circ> (`pcW := Write)
                        \<circ> setownB [(hW s,hW s+Data s (numEnqs s)) W]) s"
| "rbW_step A5 s = (if grd4 s then (`pcW := A6)  
                     else if grd5 s then (`pcW := A7)
                     else (`pcW := A8)) s"
| "rbW_step A6 s = (`H := ((hW s) + (Data s (numEnqs s))) \<circ> (`offset := (hW s)) \<circ> (`pcW := Write)
                        \<circ> setownB [(hW s,hW s+Data s (numEnqs s)) W]) s"
| "rbW_step A7 s = ((`H := (Data s (numEnqs s))) \<circ> (`offset := 0) \<circ> (`pcW := Write)
                        \<circ> (setownB [(hW s,N) D])
                        \<circ> (setownB [(0,Data s (numEnqs s)) W])) s"
| "rbW_step A8 s = (if ((Data s (numEnqs s))>N) then ERRBTS s
                        else (ERROOM \<circ> (`tW := (T s))) s)"

| "rbW_step Write s = s"
| "rbW_step Enqueue s = s"| "rbW_step idleW s = s" | "rbW_step FinishedW s = s"| "rbW_step BTS s = s"| "rbW_step OOM s = s"



definition "B_acquire s s' \<equiv> s' = (`pcW := A1) s"

definition "Q_enqueue s s' \<equiv> s' = (`q:=(append (q s) [(offset s,Data s (numEnqs s))])
                     \<circ> `pcW := idleW
                     \<circ>  transownB [W Q]
                     \<circ> `numEnqs := (numEnqs s + 1)
                     \<circ>  transownT [W Q s]) s"

definition "B_write s s' \<equiv> s' = ((`B.write ((offset s), (Data s (numEnqs s))):= (numEnqs s))
                      \<circ> (transownD [(numWrites s) B]) \<circ> `pcW := Enqueue \<circ> (`numWrites := ((numWrites s )+1))) s"

definition cW_step :: "PCW \<Rightarrow> rb_state \<Rightarrow> rb_state \<Rightarrow> bool" where
 "cW_step pcw s s' \<equiv> 
    case pcw of
        idleW     \<Rightarrow>  if ((numEnqs s) < n) then B_acquire s s'
                          else s' = (`pcW := FinishedW ) s
      | Write     \<Rightarrow>  B_write s s'   
      | Enqueue   \<Rightarrow>  Q_enqueue s s'
      | OOM       \<Rightarrow>  if tW s \<noteq> T s then s' = (`pcW := idleW ) s else s = s'
      | FinishedW \<Rightarrow>  s = s'
      | BTS       \<Rightarrow>  s = s'
      | _         \<Rightarrow>  s' = rbW_step pcw s "


lemmas W_functs [simp] = B_acquire_def B_write_def Q_enqueue_def
(*---------Tailored assertions to Writer-------*)
definition "pre_acquire_inv s   \<equiv> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq> W)
                                \<and> (T s=H s \<longrightarrow> (\<forall>i.(i\<ge>0 \<and> i<N)\<longrightarrow>ownB s i=B) \<and> ownT s = Q \<and> q s= [] \<and> numDeqs s = numEnqs s)
                                \<and> (T s>H s \<longrightarrow> (\<forall>i.(i\<ge>H s \<and> i<T s)\<longrightarrow>ownB s i=B))
                                \<and> (T s<H s \<longrightarrow> (\<forall>i.((i\<ge>H s \<and> i<N) \<or> i<T s)\<longrightarrow>ownB s i=B))
                                \<and> (numWrites s=numEnqs s)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[]) 
                                \<and> (numEnqs s\<le>n)
                                \<and> (numEnqs s>0\<longleftrightarrow>H s>0)
                                \<and> (numEnqs s=0\<longleftrightarrow>H s=0)
"
definition "pre_A1_inv s        \<equiv> (T s=H s\<longrightarrow>((\<forall>i.(i\<ge>0 \<and> i<N)\<longrightarrow>ownB s i=B) \<and> ownT s =Q \<and> q s=[]))
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (T s>H s \<longrightarrow> (\<forall>i.(i\<ge>H s \<and> i<T s)\<longrightarrow>ownB s i=B))
                                \<and> (T s<H s \<longrightarrow> (\<forall>i.((i\<ge>H s \<and> i<N) \<or> i<T s)\<longrightarrow>ownB s i=B))
                                \<and> (numWrites s=numEnqs s)
                                \<and> (numEnqs s<n)
                                \<and> (numEnqs s>0\<longleftrightarrow>H s>0)
                                \<and> (numEnqs s=0\<longleftrightarrow>H s=0)
                                \<and> (T s = 0 \<and> H s = 0) = (numWrites s = 0)
                                " 
definition "pre_A2_inv s        \<equiv> (tW s=hW s\<longrightarrow>((\<forall>i.(i\<ge>0 \<and> i<N)\<longrightarrow>ownB s i=B) \<and> ownT s =Q \<and> q s=[] \<and> tW s=T s))
                                \<and> (tW s>hW s \<longrightarrow> ((\<forall>i.(i\<ge>hW s \<and> i<tW s)\<longrightarrow>ownB s i=B) \<and> (T s\<ge>tW s \<or> T s\<le>H s)))
                                \<and> (tW s<hW s \<longrightarrow> ((\<forall>i.((i\<ge>hW s \<and> i<N) \<or> i<tW s)\<longrightarrow>ownB s i=B) \<and> T s\<ge>tW s \<and> H s\<ge>T s))
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (numWrites s=numEnqs s)
                                \<and> (numEnqs s<n)
                                \<and> (H s=hW s)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[])
                                \<and> (numEnqs s>0\<longleftrightarrow>H s>0)
                                \<and> (numEnqs s=0\<longleftrightarrow>H s=0)
                                \<and> (T s = 0 \<and> H s = 0) = (numWrites s = 0)
                                " 
definition "pre_A3_inv s        \<equiv> ((\<forall>i.(i\<ge>0 \<and> i<N)\<longrightarrow>ownB s i=B))
                                \<and> (grd1 s)
                                \<and> (ownT s =W)
                                \<and> (numWrites s=numEnqs s)
                                \<and> (numEnqs s<n)
                                \<and> (H s=hW s) \<and> q s=[]
                                \<and> (numEnqs s=0\<longrightarrow>q s=[])
                                \<and> (numEnqs s>0\<longleftrightarrow>H s>0)
                                \<and> (numEnqs s=0\<longleftrightarrow>H s=0)
                                \<and> (T s=tW s)
                                \<and> (T s = 0 \<and> H s = 0) = (numWrites s = 0)
                                " 
definition "pre_A4_inv s        \<equiv> (\<forall>i.(i\<ge>hW s \<and> i<tW s)\<longrightarrow>ownB s i=B)
                                \<and> (grd2 s) \<and> (\<not>grd1 s)
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (numWrites s=numEnqs s) 
                                \<and> (numEnqs s<n)
                                \<and> (H s=hW s)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[])
                                \<and> (numEnqs s>0\<longleftrightarrow>H s>0)
                                \<and> (numEnqs s=0\<longleftrightarrow>H s=0)
                                \<and> (T s\<ge>tW s \<or> T s\<le>H s)
                                \<and> (T s = 0 \<and> H s = 0) = (numWrites s = 0)
                                " 
definition "pre_A5_inv s        \<equiv> (\<forall>i.((i\<ge>hW s \<and> i<N) \<or> i<tW s)\<longrightarrow>ownB s i=B)
                                \<and> (grd3 s) \<and> (\<not>grd1 s) \<and> (\<not>grd2 s)
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (numWrites s=numEnqs s)
                                \<and> (numEnqs s<n)
                                \<and> (H s=hW s)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[])
                                \<and> (numEnqs s>0\<longleftrightarrow>H s>0)
                                \<and> (numEnqs s=0\<longleftrightarrow>H s=0)
                                \<and> (T s\<ge>tW s \<and> T s\<le>H s)
                                \<and> (T s = 0 \<and> H s = 0) = (numWrites s = 0)
                                " 
definition "pre_A6_inv s        \<equiv> (\<forall>i.((i\<ge>hW s \<and> i<N) \<or> i<tW s)\<longrightarrow>ownB s i=B)
                                \<and> (grd4 s) \<and> (grd3 s) \<and> (\<not>grd1 s) \<and> (\<not>grd2 s)
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (numWrites s=numEnqs s) 
                                \<and> (numEnqs s<n)
                                \<and> (H s=hW s)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[])
                                \<and> (numEnqs s>0\<longleftrightarrow>H s>0)
                                \<and> (numEnqs s=0\<longleftrightarrow>H s=0)
                                \<and> (T s\<ge>tW s \<and> T s\<le>H s)
                                \<and> (T s = 0 \<and> H s = 0) = (numWrites s = 0)
                                " 
definition "pre_A7_inv s        \<equiv> (\<forall>i.((i\<ge>hW s \<and> i<N) \<or> i<tW s)\<longrightarrow>ownB s i=B)
                                \<and> (grd5 s) \<and> (grd3 s) \<and> (\<not>grd1 s) \<and> (\<not>grd2 s) \<and> (\<not>grd4 s)
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (numWrites s=numEnqs s) 
                                \<and> (numEnqs s<n) 
                                \<and> (H s=hW s)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[])
                                \<and> (numEnqs s>0\<longleftrightarrow>H s>0)
                                \<and> (numEnqs s=0\<longleftrightarrow>H s=0)
                                \<and> (T s\<ge>tW s \<and> T s\<le>H s)
                                \<and> (T s = 0 \<and> H s = 0) = (numWrites s = 0)
                                " 
definition "pre_A8_inv s        \<equiv> (tW s\<le>hW s \<longrightarrow>(\<forall>i.((i\<ge>hW s \<and> i<N) \<or> i<tW s)\<longrightarrow>ownB s i=B))
                                \<and> (tW s>hW s \<longrightarrow>(\<forall>i.(hW s \<le>i \<and> i<tW s)\<longrightarrow>ownB s i=B))
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (numWrites s=numEnqs s)
                                \<and> (no_space_for_word s) 
                                \<and> (numEnqs s<n)
                                \<and> (H s=hW s)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[])
                                \<and> (numEnqs s>0\<longleftrightarrow>H s>0)
                                \<and> (numEnqs s=0\<longleftrightarrow>H s=0)
                                \<and> (T s\<ge>tW s \<or> T s\<le>H s)
                                \<and> (T s = 0 \<and> H s = 0) = (numWrites s = 0)
"
definition "pre_write_inv s     \<equiv> (\<forall>i.(i\<ge>offset s \<and> i< ((offset s)+(Data s (numEnqs s))))\<longrightarrow>ownB s i=W)
                                \<and> ((tW s>hW s)\<longrightarrow>(\<forall>i.(i\<ge>((offset s)+(Data s (numEnqs s)))\<and>i<tW s)\<longrightarrow>ownB s i =B))
                                \<and> ((tW s<hW s \<and> offset s\<noteq>0)\<longrightarrow>(\<forall>i.((i\<ge>((offset s)+(Data s (numEnqs s))) \<and> i<N)\<or>i<tW s)\<longrightarrow>ownB s i =B))
                                \<and> ((tW s<hW s \<and> offset s=0)\<longrightarrow>((\<forall>i.(i\<ge>((offset s)+(Data s (numEnqs s))) \<and> i<tW s)\<longrightarrow>ownB s i =B) \<and> (\<forall>i.(i\<ge>hW s \<and> i<N)\<longrightarrow>ownB s i=D)))
                                \<and> (tW s=hW s\<longrightarrow>(ownT s=W \<and> q s=[]))
                                \<and> (numWrites s=numEnqs s)
                                \<and> (numEnqs s<n)
                                \<and> (tempW_structure s)
                                \<and> (ownD s(numWrites s) =W)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[]) 
                                \<and> (offset s=hW s \<or> offset s=0)
                                \<and> (H s=offset s + Data s (numEnqs s))
                                " 
definition "pre_enqueue_inv s   \<equiv> (\<forall>i.(i\<ge>offset s \<and> i< end(tempW s))\<longrightarrow>ownB s i=W)
                                \<and> (\<forall>i.(i<offset s \<or> (i\<ge> end(tempW s)\<and>i\<le>N))\<longrightarrow>ownB s i\<noteq>W)
                                \<and> ((tW s>hW s)\<longrightarrow>(\<forall>i.(i\<ge>end(tempW s)\<and>i<tW s)\<longrightarrow>ownB s i =B))
                                \<and> ((tW s<hW s \<and> offset s\<noteq>0)\<longrightarrow>(\<forall>i.((i\<ge>end(tempW s) \<and> i<N)\<or>i<tW s)\<longrightarrow>ownB s i =B))
                                \<and> ((tW s<hW s \<and> offset s=0)\<longrightarrow>((\<forall>i.(i\<ge>end(tempW s) \<and> i<tW s)\<longrightarrow>ownB s i =B) \<and> (\<forall>i.(i\<ge>hW s \<and> i<N)\<longrightarrow>ownB s i=D)))
                                \<and> (tW s=hW s\<longrightarrow>(ownT s=W \<and> q s=[]))
                                \<and> (numWrites s=numEnqs s +1)
                                \<and> (numEnqs s<n)
                                \<and> ((ownT s = W)\<longrightarrow>q s=[])
                                \<and> (tempW_structure s)
                                \<and> (tempW_reflects_writes s)
                                \<and> (ownD s(numEnqs s) =B)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[]) 
                                \<and> (offset s=hW s \<or> offset s=0)
                                \<and> (H s=offset s + Data s (numEnqs s))
                                " 
definition "pre_OOM_inv s       \<equiv> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (tW s>hW s \<longrightarrow> (\<forall>i.(i\<ge>tW s \<and> i<hW s)\<longrightarrow>ownB s i=B))
                                \<and> (tW s<hW s \<longrightarrow> (\<forall>i.((i\<ge>hW s \<and> i<N) \<or> i<tW s)\<longrightarrow>ownB s i=B))
                                \<and> (numWrites s=numEnqs s) 
                                \<and> (numEnqs s<n)
                                \<and> (H s=hW s)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[]) 
                                \<and> (numEnqs s>0\<longleftrightarrow>H s>0)
                                \<and> (numEnqs s=0\<longleftrightarrow>H s=0)
                                \<and> (T s = 0 \<and> H s = 0) = (numWrites s = 0)
                                " 
definition "pre_finished_inv s  \<equiv> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (numWrites s=numEnqs s)
                                \<and> (numEnqs s=n)
                                \<and> (H s>0)
                                " 
definition "pre_BTS_inv s       \<equiv> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (numWrites s=numEnqs s)
                                \<and> (numEnqs s<n)
                                \<and> (H s=hW s)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[]) 
                                \<and> (numEnqs s>0\<longleftrightarrow>H s>0)
                                \<and> (numEnqs s=0\<longleftrightarrow>H s=0)
                                \<and> (T s = 0 \<and> H s = 0) = (numWrites s = 0)
                                " 

lemmas writer_lemmas  = pre_A1_inv_def pre_A2_inv_def pre_A3_inv_def pre_A4_inv_def
                              pre_A5_inv_def pre_A6_inv_def pre_A7_inv_def pre_A8_inv_def
                              pre_BTS_inv_def pre_OOM_inv_def pre_acquire_inv_def
                              pre_finished_inv_def pre_enqueue_inv_def pre_write_inv_def
(***********************************************************************)


(*Reader Thread Behaviour*)

definition "B_release s s' \<equiv> s' = (`T := (end(tempR s)) 
                        \<circ> (`pcR := idleR) 
                        \<circ> (`tempR := (0,0))
                        \<circ> (transownB [R B]) 
                        \<circ> (if tR s\<noteq> fst(tempR s) then setownB [(tR s,N) B] else id) 
                        \<circ> transownT [R Q s]) s"

definition "B_read s s' \<equiv> s' = (((transownD [(data_index s (tempR s)) R]) 
                        \<circ> (`pcR := Release)) 
                        \<circ> (`numReads := (numReads s+1))  
                        \<circ> (`tR := (T s))) s"

definition "Q_dequeue s s' \<equiv>  s' = ((`q:= (tl(q s)))
                                          \<circ> (`pcR := Read)
                                          \<circ> (`tempR := (hd(q s)))
                                          \<circ> (transownT [Q R s])
                                          \<circ> (`numDeqs :=(numDeqs s+1))
                                          \<circ> (setownB [(off(hd(q s)),(end(hd(q s)))) R])) s"

definition cR_step :: "PCR \<Rightarrow> rb_state \<Rightarrow> rb_state \<Rightarrow> bool" where
 "cR_step pcr s s' \<equiv> 
    case pcr of
        idleR \<Rightarrow> if (q s=[]) then (s=s') else (Q_dequeue s s')
      | Read \<Rightarrow>  B_read s s' 
      | Release \<Rightarrow>  B_release s s'"


lemmas R_functs [simp] = B_release_def B_read_def Q_dequeue_def
(*---------Tailored assertions to Reader-------*)
definition "pre_dequeue_inv s \<equiv>  (tempR s = (0,0))
                              \<and> (numDeqs s \<le> n)
                              \<and> (numDeqs s \<ge> 0)
                              \<and> (numDeqs s = numReads s)
                              \<and> (numDeqs s \<le> numEnqs s)
                              \<and> (pcR s = idleR)
                              \<and> (q s\<noteq>[] \<longrightarrow> ownT s=Q)
                              \<and> (q s\<noteq>[] \<longrightarrow> H s>0)
                              \<and> ((T s\<noteq>fst(hd(q s))\<and>q s\<noteq>[])\<longrightarrow>(\<forall>x j.(x\<in>set(q s) \<and> j<N \<and> j\<ge>T s)\<longrightarrow>end(x)<j))
                              \<and> (q s\<noteq>[]\<longrightarrow>(\<forall>i.(fst(hd(q s))\<le>i \<and> i<end(hd(q s)))\<longrightarrow>ownB s i = Q))
                              \<and> (\<forall>i.(i<fst(tempR s) \<or> (i\<ge>end(tempR s)\<and> i\<le>N))\<longrightarrow>ownB s i \<noteq> R)

"

definition "pre_Read_inv s    \<equiv>  (snd(tempR s) = Data s (numReads s))
                              \<and> (numReads s=data_index s (tempR s))
                              \<and> (numDeqs s\<le>n) 
                              \<and> (numDeqs s\<ge>0) 
                              \<and> (numReads s+1=numDeqs s)
                              \<and> (numDeqs s\<ge>1)
                              \<and> (numEnqs s\<ge>numDeqs s) 
                              \<and> (pcR s=Read)
                              \<and> (ownT s = R)
                              \<and> (ownD s (numReads s) = B)
                              \<and> (tempR s\<noteq>(0,0))
                              \<and> (tempR_structure s)
                              \<and> (\<forall>i.(fst(tempR s)\<le>i \<and> i<end(tempR s))\<longrightarrow>ownB s i = R)
                              \<and> (\<forall>i.(i<fst(tempR s) \<or> (i\<ge>end(tempR s)\<and> i\<le>N))\<longrightarrow>ownB s i \<noteq> R)

                              \<and> (H s>0)
"

definition "pre_Release_inv s \<equiv> (snd(tempR s) = Data s (numReads s -1))
                              \<and> (data_index s (tempR s) = numReads s -1)
                              \<and> (q s\<noteq>[]\<longrightarrow>(numReads s=data_index s (hd(q s))))
                              \<and> (ownT s = R)
                              \<and> (numEnqs s\<ge>numDeqs s)
                              \<and> (ownD s (numReads s -1) = R)
                              \<and> (numDeqs s\<le>n \<and> numDeqs s\<ge>1)
                              \<and> (numDeqs s = numReads s)
                              \<and> (pcR s=Release)
                              \<and> (tR s=T s)
                              \<and> (tempR s\<noteq>(0,0))
                              \<and> (tempR_structure s)
                              \<and> (\<forall>i.(fst(tempR s)\<le>i \<and> i<end(tempR s))\<longrightarrow>ownB s i = R)
                              \<and> (\<forall>i.(i<fst(tempR s) \<or> (i\<ge>end(tempR s)\<and> i\<le>N))\<longrightarrow>ownB s i \<noteq> R)


                              \<and> (H s>0)
" 



lemmas reader_lemmas  = pre_Release_inv_def pre_Read_inv_def pre_dequeue_inv_def
(***********************************************************************)



lemma Q_structure_preserved1:
  assumes "Q_structure s"
  and "pre_dequeue_inv s"
  and "q s\<noteq>[]"
  and "Q_dequeue s s'"
  shows "Q_structure s'"
  using assms apply(simp add:Q_structure_def pre_dequeue_inv_def)
  apply (intro conjI impI)
  apply(simp add:Q_basic_struct_def)
  apply(intro conjI impI)
  apply(simp add:Q_boundness_def )
  apply (metis  list.set_sel(2))
  apply(simp add:Q_gap_structure_def) 
  apply (metis (no_types, hide_lams) One_nat_def Q_gap_structure_def end_simp length_tl tail_preserves_Q_gap_structure)
  apply(simp add:Q_offsets_differ_def)
  apply (metis (no_types, lifting) One_nat_def add.commute add_right_cancel length_tl less_diff_conv nth_tl plus_1_eq_Suc)
  apply(simp add:Q_has_no_overlaps_def)
  apply (metis (no_types, lifting) list.set_sel(2))
  apply(simp add:Q_has_no_uroboros_def)
  apply (metis butlast_tl last_tl list.sel(2) list.set_sel(2))
  apply(simp add:Q_reflects_writes_def) apply(simp add:Q_elem_size_def)
  apply (meson list.set_sel(2)) apply(simp add:Q_reflects_writes_def)
  apply (metis One_nat_def Suc_eq_plus1 add_Suc_right length_tl less_diff_conv nth_tl)
  apply(simp add:Q_reflects_ownD_def) apply(simp add:Q_elem_rel_def) 
  apply (metis (no_types, hide_lams) One_nat_def Q_structure_def Suc_eq_plus1_left add.commute assms(1) length_tl tail_preserves_Q_elem_size)
  apply(simp add:Q_reflects_ownD_def)
  by (metis Nat.add_0_right add_Suc add_Suc_right less_diff_conv)

lemma Q_structure_preserved2:
  assumes "Q_structure s"
  and "ownT s=R"
  and "pre_Read_inv s"
  and "B_read s s'"
  shows "Q_structure s'"
  using assms apply(simp add:Q_structure_def)
  apply(intro conjI impI) apply(simp add:Q_basic_struct_def) apply(intro conjI impI)
  apply(simp add:Q_boundness_def)
  apply(simp add:Q_gap_structure_def)
  apply(simp add:Q_offsets_differ_def)
  apply(simp add:Q_has_no_overlaps_def)
  apply(simp add:Q_has_no_uroboros_def)
  apply(simp add:Q_elem_size_def)
  apply(simp add:Q_holds_bytes_def)
  apply(simp add:Q_reflects_writes_def)
  apply(simp add:Q_elem_size_def)
  apply(simp add:Q_reflects_ownD_def)
  apply(simp add:Q_elem_rel_def)
  apply(simp add:Q_reflects_ownD_def)
  by(simp add:Q_structure_def pre_Read_inv_def)

lemma Q_structure_preserved3:
  assumes "Q_structure s"
  and "pre_Release_inv s"
  and "s' = (`T := (off(tempR s) +len(tempR s)) 
          \<circ> (`pcR := idleR) 
          \<circ> (`tempR := (0,0))
          \<circ> (transownB [R B]) 
          \<circ> (if tR s\<noteq> fst(tempR s) then setownB [(tR s,N) B] else id) 
          \<circ> transownT [R Q s]) s"
  shows "Q_structure s'"
  using assms 
  apply (simp add:Q_structure_def) 
  apply(intro conjI impI)
  apply(simp add:Q_basic_struct_def)
  apply(intro conjI impI) 
  apply(simp add:pre_Release_inv_def Q_boundness_def)
  apply(simp add:pre_Release_inv_def Q_gap_structure_def)
  apply(simp add:pre_Release_inv_def Q_offsets_differ_def)
  apply(simp add:pre_Release_inv_def Q_has_no_overlaps_def)
  apply(simp add:pre_Release_inv_def Q_has_no_uroboros_def)
  apply(simp add:pre_Release_inv_def Q_holds_bytes_def tempR_lemmas tempR_basic_lemmas)
  apply(simp add:pre_Release_inv_def Q_reflects_writes_def)
  apply(simp add:pre_Release_inv_def Q_elem_size_def)
  apply(simp add:pre_Release_inv_def Q_reflects_ownD_def)
  apply(simp add:pre_Release_inv_def Q_basic_lemmas)
  apply(simp add:pre_Release_inv_def Q_reflects_writes_def)
  apply(simp add:pre_Release_inv_def Q_elem_rel_def)
  apply(simp add:pre_Release_inv_def Q_reflects_ownD_def)
  apply(simp add:pre_Release_inv_def Q_basic_lemmas)
  apply(simp add:pre_Release_inv_def Q_reflects_writes_def)
  apply(simp add:pre_Release_inv_def Q_elem_rel_def)
  apply(simp add:pre_Release_inv_def Q_reflects_ownD_def)
  apply(simp add:pre_Release_inv_def Q_basic_lemmas)
  apply(simp add:pre_Release_inv_def Q_reflects_writes_def)
  apply(simp add:pre_Release_inv_def Q_elem_rel_def)
  apply(simp add:pre_Release_inv_def Q_reflects_ownD_def)
  apply(simp add:pre_Release_inv_def Q_basic_lemmas)
  apply(simp add:pre_Release_inv_def Q_reflects_writes_def)
  apply(simp add:pre_Release_inv_def Q_elem_rel_def)
  by(simp add:pre_Release_inv_def Q_reflects_ownD_def)

  





definition "inRange v \<equiv> 0 \<le> v \<and> v \<le> N"
definition "inRangeHT s \<equiv> inRange (H s) \<and> inRange (T s)"
definition "H0_T0 s \<equiv> H s = 0 \<longrightarrow> T s = 0"
definition "inRangeht s \<equiv> inRange (hW s) \<and> inRange (tW s)"
definition "basic_pointer_movement s \<equiv> inRangeHT s \<and> inRangeht s \<and> H0_T0 s "

lemmas basic_pointer_movement_lemmas [simp] = basic_pointer_movement_def inRangeHT_def inRangeht_def H0_T0_def inRange_def


definition "mainInv s \<equiv> \<forall> i. (i<numReads s \<longrightarrow> ownD s i=R) 
                           \<and> (numReads s \<le> i \<and> i < numWrites s \<longrightarrow> ownD s i = B) 
                           \<and> (numWrites s \<le> i \<and> i < n \<longrightarrow> ownD s i = W) "
definition "counter_bounds s \<equiv> numReads s \<le>n \<and> numWrites s\<le>n \<and> numEnqs s\<le>n \<and> numDeqs s \<le> n"
definition "counter_q_rel s \<equiv> (numEnqs s-numDeqs s=length(q s))\<and> numWrites s\<ge>numReads s \<and> numEnqs s\<ge>numDeqs s" 


(*new lemmas, take 2*)
definition "data_index_bouded s \<equiv> \<forall>i. (i\<le>N)\<longrightarrow>(\<forall>j.(j\<le>N)\<longrightarrow>data_index s (i,j)<n)"




lemmas invariant_lemmas [simp] = con_assms_def mainInv_def
                          counter_q_rel_def 
                          counter_bounds_def data_index_bouded_def
                          

definition "Q_ownB_rel s        \<equiv> \<forall>j.(ownB s j=Q \<and> j<N)\<longrightarrow>(\<exists>a b. ((a, b)\<in>set(q s)\<and> a\<le>j \<and> j<a+b))"

definition "ran_indices a b \<equiv> {i . a \<le> i \<and> i < b}"

definition "Q_indices s \<equiv> \<Union> {ran_indices a (a + b) | a b. (a, b) \<in> set(q s)}"

definition "Q_tail_indices s \<equiv> \<Union> {ran_indices a (a + b) | a b. (a, b) \<in> set(tl(q s))}"

lemma ran_ind_imp_Q_ind:
  "\<forall>i a b. (i\<in> ran_indices a b \<and> (a, b)\<in>set(q s))\<longrightarrow>i\<in>Q_indices s"
  apply(simp add:Q_indices_def ran_indices_def) 
  by (smt (z3) add.assoc add_lessD1 less_add_eq_less mem_Collect_eq)

lemma Q_ind_imp_tail_ind_1:
  "tl(q s)\<noteq>[] \<Longrightarrow> hd(q s) = (q s!0)"
  apply (simp add:hd_def) 
  by (metis Nil_tl hd_conv_nth hd_def)

lemma Q_ind_imp_tail_ind_2:
  "tl(q s)\<noteq> [] \<Longrightarrow>i\<in>Q_indices s\<Longrightarrow> \<exists>a b.((a,b)\<in>set(tl(q s))\<and>a\<le>i \<and> i<b)\<Longrightarrow>i\<in>Q_tail_indices s"
  apply(simp add:Q_indices_def ran_indices_def Q_tail_indices_def) 
  by (metis (no_types, lifting) leD leI le_iff_add mem_Collect_eq nat_add_left_cancel_less trans_le_add2)

lemma Q_ind_imp_tail_ind_3:
  "tl(q s)\<noteq> [] \<Longrightarrow>i\<in>Q_indices s\<Longrightarrow> s'=(s\<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
                   numDeqs := Suc (numDeqs s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr>)
 \<Longrightarrow>\<exists>a b.((a,b)\<in>set(tl(q s))\<and>a\<le>i \<and> i<b)\<Longrightarrow>i\<in>Q_indices s'"
  apply(simp add:Q_indices_def ran_indices_def Q_tail_indices_def) 
  by (metis (no_types, lifting) leD leI le_iff_add mem_Collect_eq nat_add_left_cancel_less trans_le_add2)



(*
[(1, 3), (4,1)]
ran_indices 1 4 = {1,2,3}
ran_indicies 4,5 = {4}
Q_indicies s = {1,2,3,4}
*)

definition "Q_owns_bytes s \<equiv> \<forall>i.(i\<in>Q_indices s)\<longleftrightarrow>(i\<le>N \<and> ownB s i=Q)"

definition "Q_tail_owns_bytes s \<equiv> \<forall>i.(i\<in>Q_tail_indices s)\<longleftrightarrow>(i\<le>N \<and> ownB s i=Q \<and> i\<notin>ran_indices (fst(hd(q s))) (end(hd(q s))))"



(*------------------------ Invariant ------------------------------------*)
definition inv  where
"inv   s \<equiv> basic_pointer_movement s 
               \<and> mainInv s
               \<and> counter_q_rel s
               \<and> counter_bounds s 
               \<and> Q_structure s
               \<and> data_index_bouded s
               \<and> (case_1 s \<or> case_2 s)
               \<and> Q_owns_bytes s
"

definition pre_W where
  "pre_W pcw s \<equiv> (case pcw of
      idleW \<Rightarrow> pre_acquire_inv s 
    | A1 \<Rightarrow> pre_A1_inv s 
    | A2 \<Rightarrow> pre_A2_inv s 
    | A3 \<Rightarrow> pre_A3_inv s 
    | A4 \<Rightarrow> pre_A4_inv s 
    | A5 \<Rightarrow> pre_A5_inv s 
    | A6 \<Rightarrow> pre_A6_inv s 
    | A7 \<Rightarrow> pre_A7_inv s 
    | A8 \<Rightarrow> pre_A8_inv s 
    | Write \<Rightarrow> pre_write_inv s 
    | OOM \<Rightarrow> pre_OOM_inv s 
    | BTS \<Rightarrow> pre_BTS_inv s 
    | Enqueue \<Rightarrow> pre_enqueue_inv s  
    | FinishedW \<Rightarrow> pre_finished_inv s)"

definition pre_R where
  "pre_R pcr s \<equiv>
  (case pcr of
     idleR \<Rightarrow> pre_dequeue_inv s 
    | Read \<Rightarrow> pre_Read_inv s  
    | Release \<Rightarrow> pre_Release_inv s)"


lemmas inv_simps =  inv_def cW_step_def cR_step_def init_def





lemma Q_not_empty:
  "q s \<noteq> [] \<Longrightarrow> \<forall>x.(x\<in>set(q s))\<longrightarrow>snd(x)>0 \<Longrightarrow> Q_indices s\<noteq>{}"
  apply (simp add: Q_indices_def ran_indices_def)
  apply (rule_tac exI [where x ="{i. fst(hd(q s)) \<le> i \<and> i < end(hd(q s))}"])
  apply safe defer apply(simp add:end_def)
  apply auto 
  apply (metis add.commute le_refl less_add_same_cancel2 list.set_sel(1) prod.exhaust_sel)
  apply (rule_tac exI [where x ="fst(hd(q s))"])
  apply (rule_tac exI [where x ="snd(hd(q s))"])
  by simp


lemma case_1_Q_struct:
  assumes "case_1 s"
  and "Q_structure s"
  and "Q_owns_bytes s"
shows "\<forall>i.(i>0 \<and> i<length(q s))\<longrightarrow>fst(q s!i) = end(q s!(i-1))"
  apply (cases "q s = []")
  apply simp 
  using assms apply (simp add:Q_lemmas Q_basic_lemmas case_1_def Q_owns_bytes_def Q_indices_def ran_indices_def) 
  apply clarify
  apply(subgoal_tac "\<forall>a b aa. (a,b)\<in>set(q s) \<and> (\<exists>b.(aa, b)\<in>set(q s)) \<longrightarrow> a<aa\<longrightarrow>a+b\<le>aa") prefer 2 
  apply blast
  apply(subgoal_tac "\<forall>a b. (a,b)\<in>set(q s)\<longrightarrow>(\<exists>i.(i<length(q s) \<and> (q s!i) = (a,b)))") prefer 2
  apply (metis in_set_conv_nth)
  apply(subgoal_tac "\<forall>i j.(i<length(q s)\<and>j<length(q s))\<longrightarrow>(\<exists>a b aa bb.((a,b)\<in>set(q s)\<and>(aa,bb)\<in>set(q s)))")
  prefer 2 
  apply (metis last_in_set surjective_pairing)
  apply(subgoal_tac "\<forall>i.(i<length(q s) \<and> i>0)\<longrightarrow>(fst(q s!i) = 0 \<or> fst(q s!i) = end(q s!(i-1)))")
  prefer 2 
  apply (metis (no_types, lifting) One_nat_def end_simp)
  apply(case_tac "ownB s 0 = Q") 
  apply (metis (no_types, lifting) F.distinct(11) F.distinct(19) F.distinct(23) F.distinct(3) bot_nat_0.not_eq_extremum head_q0 le_numeral_extra(3) length_greater_0_conv)
  apply(subgoal_tac "ownB s 0\<noteq>Q") prefer 2 apply blast
  (*trying to use the fact that ownB s 0\<noteq>Q and Q_gap_structure to show that all 
    Q entries start where the last left off, rather than any starting from 0*)
  apply(subgoal_tac "(\<exists>a b.((a,b)\<in>set(q s) \<and> a = 0))\<longrightarrow>ownB s 0=Q")
  prefer 2
  apply (metis (no_types, lifting) add_gr_0 mem_Collect_eq nat_le_linear)
  apply(subgoal_tac "ownB s 0\<noteq>Q\<longrightarrow>(\<nexists>a b.((a,b)\<in>set(q s) \<and> a = 0))")
  prefer 2 
  apply meson
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>a\<noteq>0") prefer 2
  apply metis
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>(\<exists>i.(i<length(q s) \<and> (a,b)=(q s!i)))") prefer 2
  apply metis
  apply(subgoal_tac "\<forall>a b i.((a,b)\<in>set(q s)\<and>(q s!i) = (a, b))\<longrightarrow>a=fst(q s!i)") prefer 2
  apply (metis fst_conv)
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow>fst(q s!i)\<noteq>0") prefer 2
  apply (metis nth_mem prod.collapse)
  apply(subgoal_tac "\<forall>i.(i<length(q s)\<and>i>0)\<longrightarrow>(fst(q s!i) =end(q s!(i-1)) \<or> fst(q s!i) =0)")
  prefer 2 
  apply (metis (no_types, hide_lams))
  apply(subgoal_tac "(\<forall>i.(i<length(q s))\<longrightarrow>fst(q s!i)\<noteq>0) \<and> (\<forall>i.(i<length(q s)\<and>i>0)\<longrightarrow>(fst(q s!i) =end(q s!(i-1)) \<or> fst(q s!i) =0))
                      \<longrightarrow>(\<forall>i.(i<length(q s)\<and>i>0)\<longrightarrow>(fst(q s!i) =end(q s!(i-1))))")
  prefer 2 
  apply (metis (no_types, hide_lams))
  by (metis (no_types, lifting))

lemma ran_indices_lem:
  "Q_structure s \<Longrightarrow> \<forall>i.(i<length(q s))\<longrightarrow> fst(q s!i) \<in> ran_indices (fst(q s ! i)) (fst(q s!i)+snd(q s!i))"
  apply (simp add: Q_lemmas Q_basic_lemmas ran_indices_def)
  by (metis bot_nat_0.not_eq_extremum length_0_conv length_pos_if_in_set nth_mem prod.exhaust_sel)

lemma ran_indices_lem2:
  "q s \<noteq> [] \<Longrightarrow> Q_structure s \<Longrightarrow> case_1 s \<Longrightarrow> \<forall>i.(i\<ge>end(last(q s)) \<and> i\<le>N)\<longrightarrow>ownB s i\<noteq>Q"
  apply (simp add: Q_lemmas Q_basic_lemmas ran_indices_def case_1_def) 
  by (metis F.distinct(11) F.distinct(19) F.distinct(23) F.distinct(3) le_eq_less_or_eq nat_neq_iff)
 

lemma ran_indices_lem3:              
  "q s \<noteq> [] \<Longrightarrow> Q_structure s \<Longrightarrow> case_1 s \<Longrightarrow> end(last(q s)) \<le> N \<Longrightarrow> ownB s (end(last(q s))) \<noteq>Q"
  apply (simp add: Q_lemmas Q_basic_lemmas ran_indices_def case_1_def) 
  by (smt (z3) F.distinct(11) F.distinct(19) F.distinct(23) F.distinct(3) last_in_set le_eq_less_or_eq less_eq_Suc_le not_less_eq_eq prod.collapse)

lemma ran_indices_lem4:
  "q s \<noteq> [] \<Longrightarrow> Q_structure s \<Longrightarrow> case_1 s \<Longrightarrow>  end(last(q s))\<le>N"
  by (simp add: Q_lemmas Q_basic_lemmas ran_indices_def case_1_def)

lemma ran_indices_lem5:
  "q s\<noteq>[] \<Longrightarrow>Q_structure s \<Longrightarrow> case_1 s \<Longrightarrow> Q_owns_bytes s \<Longrightarrow> \<forall>i.(i<length(q s)) \<longrightarrow> fst(q s!i)\<in>Q_indices s"
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  by (metis (mono_tags, lifting) mem_Collect_eq nth_mem prod.collapse ran_indices_def ran_indices_lem)


lemma case_1_Q_struct_inf:
  assumes "Q_structure s"
  and "case_1 s"
  and "Q_owns_bytes s"
shows  "\<forall>i<length (q s). fst (q s ! i) < end(q s!(length(q s)-1))"
  apply(case_tac "q s=[]")
  apply simp
  using assms apply(case_tac "length (q s) =1") 
  apply(simp add:Q_lemmas Q_basic_lemmas )
  apply (metis lessI nth_mem prod.collapse)
  apply safe[1]
  apply(subgoal_tac "\<forall>i.(i<N \<and> i\<ge>end(last(q s)))\<longrightarrow> ownB s i\<noteq>Q") prefer 2
  apply(simp add:case_1_def) 
  apply (metis assms(2) end_simp less_or_eq_imp_le ran_indices_lem2)
  apply(simp add:case_1_def)
  apply clarify
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow>ownB s (fst(q s!i)) = Q") prefer 2
  using ran_indices_lem [where s = s] 
   defer 
  apply(subgoal_tac "\<forall>i.(ownB s i =Q \<and> i\<le>N)\<longrightarrow>i<end(last(q s))") prefer 2
  apply (metis (no_types, lifting) assms(2) nat_le_linear nat_less_le ran_indices_lem2)
  apply(subgoal_tac "(\<forall>i.(i\<ge>end(last(q s)) \<and> i\<le>N)\<longrightarrow>ownB s i\<noteq>Q)\<longrightarrow>(\<forall>i.(ownB s i=Q \<and> i\<le>N)\<longrightarrow>i<end(last(q s)))") prefer 2
  apply(unfold Q_owns_bytes_def Q_indices_def ran_indices_def)[1]
  apply blast
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow>ownB s (fst(q s!i)) =Q") prefer 2 
  apply blast
  apply(subgoal_tac "\<forall>i.(ownB s i=Q \<and> i\<le>N)\<longrightarrow>i<end(last(q s))") prefer 2
  apply blast
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow>(\<exists>a b. (a,b)\<in>set(q s) \<and> a=fst(q s!i))") prefer 2
  apply (metis nth_mem prod.exhaust_sel)
  apply(unfold Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "\<nexists>j.(j<length(q s) \<and> ownB s (fst(q s!j))\<noteq>Q)") prefer 2
  apply metis
  apply(subgoal_tac "\<forall>i.(ownB s i = Q \<and> i\<le>N)\<longrightarrow>i<end(last(q s))") prefer 2
  apply meson
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow> fst(q s!i) \<in> {j. ownB s j = Q}") prefer 2
  apply (metis (mono_tags, lifting) mem_Collect_eq)
  apply(subgoal_tac "\<forall>i.(i<length(q s)) \<longrightarrow> end(q s!i)\<le>N") prefer 2
  apply (metis nth_mem)
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow>snd(q s!i)>0") prefer 2
  apply (metis nth_mem)
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow>fst(q s!i)<end(q s!i)") prefer 2
  apply (metis (no_types, lifting) end_simp less_add_same_cancel1)
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow>fst(q s!i)<N") prefer 2 
  apply (metis (no_types, lifting) F.distinct(23) add_leD1 end_simp nat_less_le)
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow> fst(q s!i) \<in> {j. j<N}") prefer 2 
  apply (metis mem_Collect_eq)
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow>fst(q s!i) \<in> {j. ownB s j = Q \<and> j<N}") prefer 2 
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply (metis (no_types, lifting) One_nat_def end_simp last_conv_nth less_imp_le_nat)
  apply clarify
  by (metis Q_owns_bytes_def assms(1) assms(2) ran_indices_lem5)

(*******************************************************************)


















(**********************Supporting lemmas for LOCAL W transitions*********************************)


lemma case_trans_A2_to_A3_1:
  shows "s'=(s\<lparr>ownT := W, pcW := A3\<rparr>) \<Longrightarrow> case_1 s 
            \<Longrightarrow> (i\<le>N)\<longrightarrow>ownB s' i = ownB s i"
  by (simp add:case_1_def cW_step_def)

lemma case_trans_A2_to_A3_2:
  shows "s'=(s\<lparr>ownT := W, pcW := A3\<rparr>) \<Longrightarrow> T s=H s\<Longrightarrow> case_1 s 
            \<Longrightarrow> case_1 s'"
  apply (simp add:case_1_def cW_step_def)
  apply clarify
  by (smt (z3) diff_is_0_eq le_trans less_irrefl_nat zero_less_diff)


lemma case_trans_A2_to_A4_1:
  shows "s'=(s\<lparr>pcW := A4\<rparr>) \<Longrightarrow> case_1 s 
            \<Longrightarrow> (i\<le>N)\<longrightarrow>ownB s' i = ownB s i"
  by (simp add:case_1_def cW_step_def)

lemma case_trans_A2_to_A4_2:
  shows "s'=(s\<lparr>pcW := A4\<rparr>) \<Longrightarrow> case_1 s 
            \<Longrightarrow> case_1 s'"
  by (simp add:case_1_def cW_step_def)

lemma case_trans_A2_to_A4_3:
  shows "s'=(s\<lparr>pcW := A4\<rparr>) \<Longrightarrow> case_2 s \<Longrightarrow> T s>H s
            \<Longrightarrow> case_2 s'"
  by (simp add:case_2_def cW_step_def)




lemma case_trans_A2_to_A5_1:
  shows "s'=(s\<lparr>pcW := A5\<rparr>) \<Longrightarrow> case_1 s 
            \<Longrightarrow> (i\<le>N)\<longrightarrow>ownB s' i = ownB s i"
  by (simp add:case_1_def cW_step_def)

lemma case_trans_A2_to_A5_2:
  shows "s'=(s\<lparr>pcW := A5\<rparr>) \<Longrightarrow> case_1 s 
            \<Longrightarrow> case_1 s'"
  by (simp add:case_1_def cW_step_def)

lemma case_trans_A2_to_A5_3:
  shows "s'=(s\<lparr>pcW := A5\<rparr>) \<Longrightarrow> case_2 s \<Longrightarrow> T s\<le>H s
            \<Longrightarrow> case_2 s'"
  by (simp add:case_2_def cW_step_def)







lemma case_trans_A2_to_A8_1:
  shows "s'=(s\<lparr>pcW := A8\<rparr>) \<Longrightarrow> case_1 s 
            \<Longrightarrow> (i\<le>N)\<longrightarrow>ownB s' i = ownB s i"
  by (simp add:case_1_def cW_step_def)


lemma case_trans_A2_to_A8_2:
  shows "s'=(s\<lparr>pcW := A8\<rparr>) \<Longrightarrow> case_1 s 
            \<Longrightarrow> case_1 s'"
  by (simp add:case_1_def cW_step_def)

lemma case_trans_A2_to_A8_3:
  shows "s'=(s\<lparr>pcW := A8\<rparr>) \<Longrightarrow> case_2 s \<Longrightarrow> T s\<le>H s
            \<Longrightarrow> case_2 s'"
  by (simp add:case_2_def cW_step_def)

lemma case_trans_A2_to_A8_4:
  shows "s'=(s\<lparr>pcW := A8\<rparr>) \<Longrightarrow> case_2 s \<Longrightarrow> T s>H s
            \<Longrightarrow> case_2 s'"
  by (simp add:case_2_def cW_step_def)

lemma case_trans_A3_1:
  shows "pre_A3_inv s \<Longrightarrow> case_2 s \<Longrightarrow> False"
  by (simp add:case_2_def pre_A3_inv_def)

lemma case_trans_A3_2:
  shows "pre_A3_inv s \<Longrightarrow>con_assms s\<Longrightarrow>inv s\<Longrightarrow> case_1 s"
  apply (simp add:pre_A3_inv_def con_assms_def basic_pointer_movement_def inv_def)
  apply(subgoal_tac "H s=T s") prefer 2
  apply simp apply clarify 
  apply(subgoal_tac "\<not>case_2 s") prefer 2
  apply (metis case_split_2 less_or_eq_imp_le)
  by blast

lemma case_trans_A3_to_write_1:
  shows "pre_A3_inv s \<Longrightarrow>s'=(s\<lparr>ownB := \<lambda>i. if i < Data s (numEnqs s) then W else ownB s i,
             pcW := Write, offset := 0, H := Data s (numEnqs s), T := 0\<rparr>)\<Longrightarrow>inv s\<Longrightarrow> H s'\<ge>T s'"
  by (simp add:pre_A3_inv_def inv_def)

lemma case_trans_A3_to_write_2:
  shows "pre_A3_inv s \<Longrightarrow>s'=(s\<lparr>ownB := \<lambda>i. if i < Data s (numEnqs s) then W else ownB s i,
             pcW := Write, offset := 0, H := Data s (numEnqs s), T := 0\<rparr>)\<Longrightarrow>inv s\<Longrightarrow> \<not>case_2 s'"
  by (simp add:pre_A3_inv_def inv_def case_2_def)

lemma case_trans_A3_to_write_3:
  shows "pre_A3_inv s \<Longrightarrow>s'=(s\<lparr>ownB := \<lambda>i. if i < Data s (numEnqs s) then W else ownB s i,
             pcW := Write, offset := 0, H := Data s (numEnqs s), T := 0\<rparr>)\<Longrightarrow>inv s\<Longrightarrow> con_assms s\<Longrightarrow> (i\<ge>T s' \<and> i<H s')\<longrightarrow>ownB s' i=W"
  by (simp add:pre_A3_inv_def inv_def case_1_def)

lemma case_trans_A3_to_write_4:
  shows "pre_A3_inv s \<Longrightarrow>s'=(s\<lparr>ownB := \<lambda>i. if i < Data s (numEnqs s) then W else ownB s i,
             pcW := Write, offset := 0, H := Data s (numEnqs s), T := 0\<rparr>)\<Longrightarrow>inv s\<Longrightarrow> con_assms s\<Longrightarrow> (i\<ge>H s'\<and> i<N)\<longrightarrow>ownB s' i=B"
  by (simp add:pre_A3_inv_def inv_def case_1_def)

lemma case_trans_A3_to_write_7:
  shows "pre_A3_inv s \<Longrightarrow>s'=(s\<lparr>ownB := \<lambda>i. if i < Data s (numEnqs s) then W else ownB s i,
             pcW := Write, offset := 0, H := Data s (numEnqs s), T := 0\<rparr>)\<Longrightarrow>inv s\<Longrightarrow> con_assms s\<Longrightarrow> case_1 s'"
  apply (simp add:pre_A3_inv_def inv_def case_1_def)
  apply (rule_tac exI [where x ="0"])
  apply (rule_tac exI [where x ="0"]) apply simp
  apply (subgoal_tac "Data s (numEnqs s)\<le>N")
  apply (metis case_split_2 le_refl)
  by blast


lemma case_trans_A4_1:
  shows "pre_A4_inv s \<Longrightarrow> T s\<ge>tW s\<Longrightarrow> case_1 s \<Longrightarrow> False"
  apply (simp add:case_1_def pre_A4_inv_def)
  by (metis diff_is_0_eq le_trans less_nat_zero_code)

lemma case_trans_A4_2:
  shows "pre_A4_inv s \<Longrightarrow> T s\<le>hW s\<Longrightarrow> case_2 s \<Longrightarrow> False"
  apply (simp add:case_2_def pre_A4_inv_def) 
  by (metis le_antisym less_irrefl_nat less_or_eq_imp_le)

lemma case_trans_A4_3:
  shows "pre_A4_inv s \<Longrightarrow> T s>hW s \<and> T s<tW s  \<Longrightarrow> False"
  by (simp add:case_2_def pre_A4_inv_def) 

lemma case_trans_A4_4:
  shows "pre_A4_inv s \<Longrightarrow> inv s\<Longrightarrow> T s\<ge>tW s\<Longrightarrow> case_2 s"
  apply (simp add: pre_A4_inv_def inv_def) using case_trans_A4_1 [where s=s]
  by (metis case_split_4 less_eqE trans_less_add1) 


lemma case_trans_A4_5:
  shows "pre_A4_inv s \<Longrightarrow> inv s\<Longrightarrow> T s\<le>hW s\<Longrightarrow> case_1 s"
  apply (simp add: pre_A4_inv_def inv_def) using case_trans_A4_2 [where s=s]
  by (metis RingBuffer_BD_latest_2.case_split) 


lemma case_trans_A4_to_write_1:
  shows "pre_A4_inv s \<Longrightarrow> T s\<ge>tW s  \<Longrightarrow> s'=(s\<lparr>ownB := \<lambda>i. if hW s \<le> i \<and> i < hW s + Data s (numEnqs s) then W else ownB s i, pcW := Write,
          offset := hW s, H := hW s + Data s (numEnqs s)\<rparr>) \<Longrightarrow> inv s \<Longrightarrow>
    (i<offset s')\<longrightarrow>ownB s i=ownB s' i"
  by (simp add:case_2_def pre_A4_inv_def inv_def) 

lemma case_trans_A4_to_write_2:
  shows "pre_A4_inv s \<Longrightarrow> T s\<ge>tW s  \<Longrightarrow> s'=(s\<lparr>ownB := \<lambda>i. if hW s \<le> i \<and> i < hW s + Data s (numEnqs s) then W else ownB s i, pcW := Write,
          offset := hW s, H := hW s + Data s (numEnqs s)\<rparr>) \<Longrightarrow> inv s \<Longrightarrow>
    (i\<ge>H s')\<longrightarrow>ownB s i=ownB s' i"
  by (simp add:case_2_def pre_A4_inv_def inv_def) 

lemma case_trans_A4_to_write_3:
  shows "pre_A4_inv s \<Longrightarrow> T s\<ge>tW s  \<Longrightarrow> s'=(s\<lparr>ownB := \<lambda>i. if hW s \<le> i \<and> i < hW s + Data s (numEnqs s) then W else ownB s i, pcW := Write,
          offset := hW s, H := hW s + Data s (numEnqs s)\<rparr>) \<Longrightarrow> inv s \<Longrightarrow>
    (hW s \<le>i \<and> i<H s')\<longrightarrow>W=ownB s' i"
  by (simp add:case_2_def pre_A4_inv_def inv_def) 

lemma case_trans_A4_to_write_4:
  shows "pre_A4_inv s \<Longrightarrow> T s\<ge>tW s  \<Longrightarrow> s'=(s\<lparr>ownB := \<lambda>i. if hW s \<le> i \<and> i < hW s + Data s (numEnqs s) then W else ownB s i, pcW := Write,
          offset := hW s, H := hW s + Data s (numEnqs s)\<rparr>) \<Longrightarrow> inv s \<Longrightarrow>
    T s'=T s"
  by (simp add:case_2_def pre_A4_inv_def inv_def) 

lemma case_trans_A4_to_write_5:
  shows "pre_A4_inv s \<Longrightarrow> T s\<ge>tW s  \<Longrightarrow> s'=(s\<lparr>ownB := \<lambda>i. if hW s \<le> i \<and> i < hW s + Data s (numEnqs s) then W else ownB s i, pcW := Write,
          offset := hW s, H := hW s + Data s (numEnqs s)\<rparr>) \<Longrightarrow> inv s \<Longrightarrow> con_assms s \<Longrightarrow>
    T s'> H s' \<and> H s<H s' \<and> T s=T s' \<and> offset s'=hW s \<and> Data s (numEnqs s) = Data s' (numEnqs s') \<and> H s'-H s=Data s (numEnqs s) \<and> tempR s=tempR s' \<and> q s=q s' \<and> ownT s=ownT s'"
  apply (simp add:case_2_def pre_A4_inv_def inv_def) 
  by (simp add: le_Suc_ex less_diff_conv) 


lemma case_trans_A4_to_write_6:
  shows "pre_A4_inv s \<Longrightarrow> T s\<ge>tW s  \<Longrightarrow> s'=(s\<lparr>ownB := \<lambda>i. if hW s \<le> i \<and> i < hW s + Data s (numEnqs s) then W else ownB s i, pcW := Write,
          offset := hW s, H := hW s + Data s (numEnqs s)\<rparr>) \<Longrightarrow>con_assms s \<Longrightarrow> inv s \<Longrightarrow>
    case_2 s"
  using case_trans_A4_4 [where s=s] 
  by blast

lemma case_trans_A4_to_write_7:
  shows "pre_A4_inv s \<Longrightarrow> T s\<ge>tW s  \<Longrightarrow> s'=(s\<lparr>ownB := \<lambda>i. if hW s \<le> i \<and> i < hW s + Data s (numEnqs s) then W else ownB s i, pcW := Write,
          offset := hW s, H := hW s + Data s (numEnqs s)\<rparr>) \<Longrightarrow>con_assms s \<Longrightarrow> inv s \<Longrightarrow>
    case_2 s'"
  apply(subgoal_tac "H s'<T s'") prefer 2 
  using case_trans_A4_to_write_5 [where s=s and s'=s']
  apply blast
  apply(subgoal_tac "H s<H s'") prefer 2 
  using case_trans_A4_to_write_5 [where s=s and s'=s']
  apply blast
  apply(subgoal_tac "T s=T s'") prefer 2 
  using case_trans_A4_to_write_5 [where s=s and s'=s']
  apply blast
  apply(subgoal_tac "q s=q s'") prefer 2 
  using case_trans_A4_to_write_5 [where s=s and s'=s']
  apply blast
  apply(subgoal_tac "ownT s=ownT s'") prefer 2 
  using case_trans_A4_to_write_5 [where s=s and s'=s']
  apply blast
  apply(subgoal_tac "Data s (numEnqs s) = Data s' (numEnqs s')") prefer 2 
  using case_trans_A4_to_write_5 [where s=s and s'=s']
   apply blast
  apply(subgoal_tac "H s'-H s=Data s (numEnqs s)") prefer 2 
  using case_trans_A4_to_write_5 [where s=s and s'=s']
  apply blast
  apply(subgoal_tac "\<forall>i.(i<offset s')\<longrightarrow>ownB s i=ownB s' i") prefer 2
  using case_trans_A4_to_write_1 [where s=s and s'=s']
  apply blast
  apply(subgoal_tac "\<forall>i.(hW s \<le>i \<and> i<H s')\<longrightarrow>W=ownB s' i") prefer 2
  using case_trans_A4_to_write_3 [where s=s and s'=s']
  apply blast
  apply(subgoal_tac "\<forall>i.(i\<ge>H s')\<longrightarrow>ownB s i=ownB s' i") prefer 2
  using case_trans_A4_to_write_2 [where s=s and s'=s']
  apply blast
  apply(subgoal_tac "offset s'=hW s") prefer 2
  using case_trans_A4_to_write_5 [where s=s and s'=s']
  apply blast
  apply(subgoal_tac "tempR s = tempR s'") prefer 2
  using case_trans_A4_to_write_5 [where s=s and s'=s']
  apply blast
  apply(unfold inv_def)[1]
  apply(subgoal_tac "case_2 s") prefer 2
  using case_trans_A4_to_write_6 [where s=s and s'=s']
  using RingBuffer_BD_latest_2.inv_def apply blast 
  apply(subgoal_tac "\<not>case_1 s") prefer 2
  using case_trans_A4_1 apply blast
  apply(unfold pre_A4_inv_def grd1_def grd2_def basic_pointer_movement_def)[1]
  apply(clarify) 
  apply(thin_tac "case_2 s")
  apply(thin_tac "\<not>case_1 s")
  apply(thin_tac "mainInv s")
   apply(unfold case_2_def)[1]
    (*apply instance*) apply clarify
  apply(rule_tac ?x = "a" in exI)
  apply(rule_tac ?x = "b" in exI) 
  apply(rule_tac exI [where x ="H s'"])
  apply(rule_tac exI [where x ="T s'"])
  apply(rule_tac ?x = "e" in exI)
  apply(rule_tac ?x = "f" in exI)
  apply (intro conjI impI)
  apply blast 
  apply meson
  apply (metis le_trans less_imp_le_nat)
  apply meson
  apply metis
  apply blast
  apply meson
  apply clarify
  apply(subgoal_tac "i<a\<longrightarrow>ownB s i=R") prefer 2
  apply (metis zero_le)
  apply(subgoal_tac "hW s = b") prefer 2
  apply (metis F.distinct(17) F.distinct(23) nat_le_linear nat_less_le zero_le)
  apply(subgoal_tac "(i<offset s')\<longrightarrow>ownB s i=ownB s' i") prefer 2
  using case_trans_A4_to_write_1 [where s=s and s'=s']
  apply metis
  apply (metis le_trans nat_less_le)
  apply(subgoal_tac "i\<ge>a \<and> i<b\<longrightarrow>ownB s i=Q") prefer 2
  apply (metis zero_le)
  apply(subgoal_tac "(i<offset s')\<longrightarrow>ownB s i=ownB s' i") prefer 2
  using case_trans_A4_to_write_1 [where s=s and s'=s']
  apply metis
  apply (metis le_trans nat_less_le)
  apply (metis le_eq_less_or_eq le_trans)
  apply(subgoal_tac "(i\<ge>H s')\<longrightarrow>ownB s i=ownB s' i") prefer 2
  using case_trans_A4_to_write_1 [where s=s and s'=s']
  apply metis
  apply (metis le_trans less_or_eq_imp_le)
  apply(subgoal_tac "(i\<ge>H s')\<longrightarrow>ownB s i=ownB s' i") prefer 2
  using case_trans_A4_to_write_1 [where s=s and s'=s']
  apply metis
  apply (metis le_trans less_or_eq_imp_le)
  apply(subgoal_tac "(i\<ge>H s')\<longrightarrow>ownB s i=ownB s' i") prefer 2
  using case_trans_A4_to_write_1 [where s=s and s'=s']
  apply metis
  apply (metis le_trans less_or_eq_imp_le)
  apply(subgoal_tac "(i\<ge>H s')\<longrightarrow>ownB s i=ownB s' i") prefer 2
  using case_trans_A4_to_write_1 [where s=s and s'=s']
  apply metis
  apply (metis le_trans less_or_eq_imp_le)
  apply(subgoal_tac "(i\<ge>H s')\<longrightarrow>ownB s i=ownB s' i") prefer 2
  using case_trans_A4_to_write_1 [where s=s and s'=s']
  apply metis
  apply (metis le_trans less_or_eq_imp_le)
  apply meson
  apply metis
  apply metis
  apply (metis gr_zeroI less_nat_zero_code)
  apply meson
  apply force
  apply (metis F.distinct(17) F.distinct(23) less_eq_nat.simps(1) nat_le_linear nat_less_le)
  apply(subgoal_tac "b=H s") prefer 2
  apply (metis F.distinct(17) F.distinct(23) less_eq_nat.simps(1) nat_le_linear nat_less_le)
  apply(subgoal_tac "H s'-H s=Data s (numEnqs s)") prefer 2
  apply meson
  apply metis
  apply metis
  apply metis
  apply metis
  apply metis
  apply metis
  apply metis
  apply metis
  apply metis
  apply metis
  apply metis
  apply metis
  by metis
 




lemma case_trans_A4_to_write_8:
  shows "pre_A4_inv s \<Longrightarrow> T s\<le>H s  \<Longrightarrow> s'=(s\<lparr>ownB := \<lambda>i. if hW s \<le> i \<and> i < hW s + Data s (numEnqs s) then W else ownB s i, pcW := Write,
          offset := hW s, H := hW s + Data s (numEnqs s)\<rparr>) \<Longrightarrow>con_assms s \<Longrightarrow> inv s \<Longrightarrow>
    case_1 s"
  using case_trans_A4_5 [where s=s] apply (simp add:case_1_def)
  by (simp add: pre_A4_inv_def)


lemma case_trans_A4_to_write_9:
  shows "pre_A4_inv s \<Longrightarrow> T s\<le>H s  \<Longrightarrow> s'=(s\<lparr>ownB := \<lambda>i. if hW s \<le> i \<and> i < hW s + Data s (numEnqs s) then W else ownB s i, pcW := Write,
          offset := hW s, H := hW s + Data s (numEnqs s)\<rparr>) \<Longrightarrow>con_assms s \<Longrightarrow> inv s \<Longrightarrow>
    case_1 s'"
  apply(simp add:inv_def)
  using case_trans_A4_to_write_8 [where s=s] 
  apply (meson case_split_2) apply(simp add:pre_A4_inv_def)
  apply(simp add:case_1_def)
  apply(intro conjI impI) prefer 2
   apply clarify
  apply(rule_tac ?x = "T s" in exI)
  apply(rule_tac ?x = b in exI) apply(intro conjI impI) prefer 2
  apply(rule_tac ?x = "hW s" in exI)
  apply(intro conjI impI)
  apply(linarith)
  apply(linarith)
  apply clarify apply(intro conjI impI) apply clarify
  apply linarith
  apply metis
  apply (metis le_neq_implies_less le_trans less_imp_le_nat)
  apply (metis le_eq_less_or_eq)
  apply blast
  apply (metis add_leE)
  apply blast
  apply blast
  apply blast
  apply (metis add_diff_cancel_left')
  apply meson
  apply meson
  apply (metis le_refl nat_less_le)
  apply (metis nat_less_le) 
  apply (metis le_refl nat_less_le)
  apply (metis le_refl nat_less_le)
  apply (metis le_refl nat_less_le)
  apply (metis le_refl nat_less_le)
  apply (metis le_refl nat_less_le)
  by (metis (no_types, lifting) add.commute add_lessD1 less_diff_conv less_eqE less_imp_add_positive not_add_less1)






lemma case_trans_A5_1:
  shows "pre_A5_inv s \<Longrightarrow> inv s\<Longrightarrow> case_1 s"
  apply (simp add: pre_A5_inv_def inv_def)
  by (metis RingBuffer_BD_latest_2.case_split) 

lemma case_trans_A5_2:
  shows "pre_A5_inv s \<Longrightarrow> inv s\<Longrightarrow> \<not>case_2 s"
  apply (simp add: pre_A5_inv_def inv_def)
  by (metis case_split_2)


lemma case_trans_A5_to_A6_1:
  shows "pre_A5_inv s  \<Longrightarrow> s'=(s\<lparr>pcW := A6\<rparr>) \<Longrightarrow>con_assms s \<Longrightarrow> inv s \<Longrightarrow>
    i\<le>N\<longrightarrow>ownB s i=ownB s' i"
  by(simp add:case_1_def pre_A5_inv_def inv_def)


lemma case_trans_A5_to_A6_2:
  shows "pre_A5_inv s  \<Longrightarrow> s'=(s\<lparr>pcW := A6\<rparr>) \<Longrightarrow>con_assms s \<Longrightarrow> inv s \<Longrightarrow>
    case_1 s' = case_1 s"
  by(simp add:case_1_def)

lemma case_trans_A5_to_A6_3:
  shows "pre_A5_inv s  \<Longrightarrow> s'=(s\<lparr>pcW := A6\<rparr>) \<Longrightarrow>con_assms s \<Longrightarrow> inv s \<Longrightarrow>
    case_1 s'"
  using case_trans_A5_to_A6_2 [where s=s and s'=s']
  using case_trans_A5_1 by blast


lemma case_trans_A5_to_A6_4:
  shows "pre_A5_inv s  \<Longrightarrow> s'=(s\<lparr>pcW := A7\<rparr>) \<Longrightarrow>con_assms s \<Longrightarrow> inv s \<Longrightarrow>
    i\<le>N\<longrightarrow>ownB s i=ownB s' i"
  by(simp add:case_1_def pre_A5_inv_def inv_def)

lemma case_trans_A5_to_A6_5:
  shows "pre_A5_inv s  \<Longrightarrow> s'=(s\<lparr>pcW := A7\<rparr>) \<Longrightarrow>con_assms s \<Longrightarrow> inv s \<Longrightarrow>
    case_1 s' = case_1 s"
  by(simp add:case_1_def)

lemma case_trans_A5_to_A6_6:
  shows "pre_A5_inv s  \<Longrightarrow> s'=(s\<lparr>pcW := A7\<rparr>) \<Longrightarrow>con_assms s \<Longrightarrow> inv s \<Longrightarrow>
    case_1 s'"
  using case_trans_A5_to_A6_5 [where s=s and s'=s']
  using case_trans_A5_1 by blast


lemma case_trans_A5_to_A6_7:
  shows "pre_A5_inv s  \<Longrightarrow> s'=(s\<lparr>pcW := A8\<rparr>) \<Longrightarrow>con_assms s \<Longrightarrow> inv s \<Longrightarrow>
    i\<le>N\<longrightarrow>ownB s i=ownB s' i"
  by(simp add:case_1_def pre_A5_inv_def inv_def)


lemma case_trans_A5_to_A6_8:
  shows "pre_A5_inv s  \<Longrightarrow> s'=(s\<lparr>pcW := A8\<rparr>) \<Longrightarrow>con_assms s \<Longrightarrow> inv s \<Longrightarrow>
    case_1 s' = case_1 s"
  by(simp add:case_1_def)


lemma case_trans_A5_to_A6_9:
  shows "pre_A5_inv s  \<Longrightarrow> s'=(s\<lparr>pcW := A8\<rparr>) \<Longrightarrow>con_assms s \<Longrightarrow> inv s \<Longrightarrow>
    case_1 s'"
  using case_trans_A5_to_A6_7 [where s=s and s'=s']
  by (metis case_trans_A2_to_A8_2 case_trans_A5_1)


lemma case_trans_A6_1:
  shows "pre_A6_inv s \<Longrightarrow> inv s\<Longrightarrow> case_1 s"
  apply (simp add: pre_A6_inv_def inv_def) 
  by (metis RingBuffer_BD_latest_2.case_split) 

lemma case_trans_A6_2:
  shows "pre_A6_inv s \<Longrightarrow> inv s\<Longrightarrow> case_2 s \<Longrightarrow> False"
  apply (simp add: pre_A6_inv_def inv_def)
  by (metis case_split_2)



lemma case_trans_A6_to_write_1:
  shows "pre_A6_inv s \<Longrightarrow> s' = s
    \<lparr>ownB := \<lambda>i. if hW s \<le> i \<and> i < hW s + Data s (numEnqs s) then W else ownB s i,
       pcW := Write, offset := hW s, H := hW s + Data s (numEnqs s)\<rparr>\<Longrightarrow>inv s\<Longrightarrow> H s'\<ge>T s'"
  by (simp add:pre_A6_inv_def inv_def)

lemma case_trans_A6_to_write_2:
  shows "pre_A6_inv s \<Longrightarrow> s' = s
    \<lparr>ownB := \<lambda>i. if hW s \<le> i \<and> i < hW s + Data s (numEnqs s) then W else ownB s i,
       pcW := Write, offset := hW s, H := hW s + Data s (numEnqs s)\<rparr>\<Longrightarrow>inv s\<Longrightarrow>con_assms s\<Longrightarrow> \<not>case_2 s'"
  by (simp add:pre_A6_inv_def inv_def case_2_def)

lemma case_trans_A6_to_write_3:
  shows "pre_A6_inv s \<Longrightarrow> s' = s
    \<lparr>ownB := \<lambda>i. if hW s \<le> i \<and> i < hW s + Data s (numEnqs s) then W else ownB s i,
       pcW := Write, offset := hW s, H := hW s + Data s (numEnqs s)\<rparr>\<Longrightarrow>inv s\<Longrightarrow> con_assms s\<Longrightarrow> (i\<ge>hW s' \<and> i<H s')\<longrightarrow>ownB s' i=W"
  by (simp add:pre_A6_inv_def inv_def case_1_def)

lemma case_trans_A6_to_write_4:
  shows "pre_A6_inv s \<Longrightarrow> s' = s
    \<lparr>ownB := \<lambda>i. if hW s \<le> i \<and> i < hW s + Data s (numEnqs s) then W else ownB s i,
       pcW := Write, offset := hW s, H := hW s + Data s (numEnqs s)\<rparr>\<Longrightarrow>inv s\<Longrightarrow> con_assms s\<Longrightarrow> (i\<ge>H s'\<and> i<N)\<longrightarrow>ownB s' i=B"
  by (simp add:pre_A6_inv_def inv_def case_1_def)

lemma case_trans_A6_to_write_7:
  shows "pre_A6_inv s \<Longrightarrow> s' = s
    \<lparr>ownB := \<lambda>i. if hW s \<le> i \<and> i < hW s + Data s (numEnqs s) then W else ownB s i,
       pcW := Write, offset := hW s, H := hW s + Data s (numEnqs s)\<rparr>\<Longrightarrow>inv s\<Longrightarrow> con_assms s\<Longrightarrow> case_1 s'"
  apply(subgoal_tac "\<not>case_2 s") prefer 2
  using case_trans_A6_to_write_2 [where s=s and s'=s']
  using case_trans_A6_2 apply blast
  apply (simp add:pre_A6_inv_def inv_def case_1_def)
  apply(intro conjI impI) 
  apply (metis (no_types, lifting) add_le_cancel_left le_add_diff_inverse le_antisym less_imp_le_nat nat_neq_iff)
  apply clarify
  apply (rule_tac exI [where x ="T s"]) 
  apply(rule_tac ?x = "b" in exI) apply (intro conjI impI)
  apply blast 
  apply(rule_tac ?x = "c" in exI)
  apply (intro conjI impI)
  apply linarith
  apply linarith 
  apply (metis le_trans nat_less_le)
  apply (metis le_trans nat_less_le)
  apply (metis le_trans nat_less_le)
  apply (metis F.distinct(17) F.distinct(23) le_refl nat_less_le nat_neq_iff)
  apply (metis)
  apply (metis le_trans nat_less_le)
  apply (metis le_neq_implies_less le_refl le_trans)
  apply (metis Nat.add_diff_assoc2 diff_self_eq_0 le_refl le_trans nat_less_le plus_nat.add_0)
  apply meson
  apply meson
  apply meson
  apply meson
  apply meson
  apply meson
  apply meson
  by meson



lemma case_trans_A7_1:
  shows "pre_A7_inv s \<Longrightarrow> inv s\<Longrightarrow> case_1 s"
  apply (simp add: pre_A7_inv_def inv_def) 
  by (metis RingBuffer_BD_latest_2.case_split) 

lemma case_trans_A7_2:
  shows "pre_A7_inv s \<Longrightarrow> inv s\<Longrightarrow> case_2 s \<Longrightarrow> False"
  apply (simp add: pre_A7_inv_def inv_def)
  by (metis case_split_2)

lemma case_trans_A7_to_write_1:
  shows "pre_A7_inv s \<Longrightarrow> s' = (s\<lparr>ownB :=
          \<lambda>i. if hW s \<le> i \<and> i < N then D
              else ownB (s\<lparr>ownB := \<lambda>i. if i < Data s (numEnqs s) then W else ownB s i\<rparr>) i,
          pcW := Write, offset := 0, H := Data s (numEnqs s)\<rparr>)\<Longrightarrow>inv s\<Longrightarrow> H s'<T s'"
  by (simp add:pre_A7_inv_def inv_def)

lemma case_trans_A7_to_write_2:
  shows "pre_A7_inv s \<Longrightarrow> s' = (s\<lparr>ownB :=
          \<lambda>i. if hW s \<le> i \<and> i < N then D
              else ownB (s\<lparr>ownB := \<lambda>i. if i < Data s (numEnqs s) then W else ownB s i\<rparr>) i,
          pcW := Write, offset := 0, H := Data s (numEnqs s)\<rparr>)\<Longrightarrow>inv s\<Longrightarrow>con_assms s\<Longrightarrow> \<not>case_1 s'"
  by (simp add:pre_A7_inv_def inv_def case_1_def)
  



lemma case_trans_A7_to_write_3:
  shows "pre_A7_inv s \<Longrightarrow> s' = (s\<lparr>ownB :=
          \<lambda>i. if hW s \<le> i \<and> i < N then D
              else ownB (s\<lparr>ownB := \<lambda>i. if i < Data s (numEnqs s) then W else ownB s i\<rparr>) i,
          pcW := Write, offset := 0, H := Data s (numEnqs s)\<rparr>)\<Longrightarrow>inv s\<Longrightarrow> con_assms s\<Longrightarrow> (i\<ge>0 \<and> i<H s')\<longrightarrow>ownB s' i=W"
  by (simp add:pre_A7_inv_def inv_def case_2_def)

lemma case_trans_A7_to_write_4:
  shows "pre_A7_inv s \<Longrightarrow> s' = (s\<lparr>ownB :=
          \<lambda>i. if hW s \<le> i \<and> i < N then D
              else ownB (s\<lparr>ownB := \<lambda>i. if i < Data s (numEnqs s) then W else ownB s i\<rparr>) i,
          pcW := Write, offset := 0, H := Data s (numEnqs s)\<rparr>)\<Longrightarrow>inv s\<Longrightarrow> con_assms s\<Longrightarrow> (i\<ge>hW s\<and> i<N)\<longrightarrow>ownB s' i=D"
  by (simp add:pre_A7_inv_def inv_def case_2_def)

lemma case_trans_A7_to_write_7:
  shows "pre_A7_inv s \<Longrightarrow> s' = (s\<lparr>ownB :=
          \<lambda>i. if hW s \<le> i \<and> i < N then D
              else ownB (s\<lparr>ownB := \<lambda>i. if i < Data s (numEnqs s) then W else ownB s i\<rparr>) i,
          pcW := Write, offset := 0, H := Data s (numEnqs s)\<rparr>)\<Longrightarrow>inv s\<Longrightarrow> con_assms s\<Longrightarrow> case_2 s'"
  apply(subgoal_tac "\<not>case_2 s") prefer 2
  using case_trans_A7_to_write_2 [where s=s and s'=s']
  using case_trans_A7_2 apply blast 
  apply (simp add:pre_A7_inv_def inv_def) apply(thin_tac "\<not>case_2 s") apply(simp add:case_1_def case_2_def)
  
  apply clarify
  apply(rule_tac ?x = "0" in exI) 
  apply(rule_tac ?x = "0" in exI) apply (intro conjI impI)
  apply blast 
  apply(rule_tac ?x = "Data s (numEnqs s)" in exI)
  apply (intro conjI impI)
  apply linarith
  apply(rule_tac ?x = "T s" in exI)
  apply (intro conjI impI) 
  apply linarith 
  apply(rule_tac ?x = "b" in exI) 
  apply (intro conjI impI) 
  apply linarith 
  apply(rule_tac ?x = "c" in exI) 
  apply (intro conjI impI) 
  apply linarith 
  apply (metis le_trans)
  apply blast
  apply blast
  apply blast  
  apply (metis le_antisym le_trans nat_less_le) 
  apply (metis le_antisym le_trans nat_less_le)
  apply (metis le_antisym le_trans nat_less_le)
  apply (metis le_trans nat_le_linear nat_less_le)
  apply blast
  apply fastforce
  apply blast  
  apply blast  
  apply metis
  apply blast
  apply blast
  apply blast 
  apply (metis diff_zero) 
  apply force
  apply fastforce
  apply meson
  apply meson 
  apply (metis zero_less_iff_neq_zero)
  apply force
  apply force
  apply force
  apply fastforce
  apply meson
  by (metis le_neq_implies_less)
  




lemma case_trans_Enqueue_to_idleW_case_1_1:
  shows "pre_enqueue_inv s \<Longrightarrow> inv s\<Longrightarrow> s'= (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s),
          ownB :=
            \<lambda>i. if ownB s i = W \<and> i \<le> N then Q else ownB (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s)\<rparr>) i,
          pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr>) \<Longrightarrow>case_1 s \<Longrightarrow> con_assms s
      \<Longrightarrow> H s\<ge>T s"
  apply (simp add: pre_enqueue_inv_def inv_def case_1_def)
  by (metis (no_types, lifting) le_trans) 

lemma case_trans_Enqueue_to_idleW_case_1_2:
  shows "pre_enqueue_inv s \<Longrightarrow> inv s\<Longrightarrow> s'= (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s),
          ownB :=
            \<lambda>i. if ownB s i = W \<and> i \<le> N then Q else ownB (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s)\<rparr>) i,
          pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr>) \<Longrightarrow>case_1 s \<Longrightarrow> con_assms s
      \<Longrightarrow> H s'\<ge>T s'"
  apply (simp add: pre_enqueue_inv_def inv_def case_1_def) 
  by (metis (no_types, lifting) le_trans)

lemma case_trans_Enqueue_to_idleW_case_1_3:
  shows "pre_enqueue_inv s \<Longrightarrow> inv s\<Longrightarrow> s'= (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s),
          ownB :=
            \<lambda>i. if ownB s i = W \<and> i \<le> N then Q else ownB (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s)\<rparr>) i,
          pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr>) \<Longrightarrow>case_1 s \<Longrightarrow> con_assms s
      \<Longrightarrow> i<offset s\<Longrightarrow>ownB s i=ownB s' i"
  by (simp add: pre_enqueue_inv_def inv_def case_1_def) 

lemma case_trans_Enqueue_to_idleW_case_1_4:
  shows "pre_enqueue_inv s \<Longrightarrow> inv s\<Longrightarrow> s'= (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s),
          ownB :=
            \<lambda>i. if ownB s i = W \<and> i \<le> N then Q else ownB (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s)\<rparr>) i,
          pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr>) \<Longrightarrow>case_1 s \<Longrightarrow> con_assms s
      \<Longrightarrow> i\<ge>H s'\<and> i\<le>N\<Longrightarrow>ownB s i=ownB s' i"
  apply (simp add: pre_enqueue_inv_def inv_def case_1_def)
  by (metis F.distinct(5) F.distinct(9) nat_less_le)

lemma case_trans_Enqueue_to_idleW_case_1_5:
  shows "pre_enqueue_inv s \<Longrightarrow> inv s\<Longrightarrow> s'= (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s),
          ownB :=
            \<lambda>i. if ownB s i = W \<and> i \<le> N then Q else ownB (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s)\<rparr>) i,
          pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr>) \<Longrightarrow>case_1 s \<Longrightarrow> con_assms s
      \<Longrightarrow> offset s \<le> i \<and> i < offset s + Data s (numEnqs s) \<Longrightarrow>Q=ownB s' i"
  by (simp add: pre_enqueue_inv_def inv_def case_1_def tempW_def) 





lemma case_trans_Enqueue_to_idleW_case_1_6:
  shows "pre_enqueue_inv s \<Longrightarrow> inv s\<Longrightarrow> q s = [] \<Longrightarrow> s'= (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s),
          ownB :=
            \<lambda>i. if ownB s i = W \<and> i \<le> N then Q else ownB (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s)\<rparr>) i,
          pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr>) \<Longrightarrow>case_1 s \<Longrightarrow> con_assms s
     \<Longrightarrow>case_1 s'"
  apply(simp add:inv_def)
  apply(subgoal_tac "\<not>case_2 s ") prefer 2
  apply (meson case_split_5) apply(thin_tac "\<not> case_2 s")
  apply (simp add: pre_enqueue_inv_def inv_def case_1_def tempW_def) 
  apply clarify apply simp
  apply(rule_tac ?x = "T s" in exI)
  apply(rule_tac ?x = "b" in exI) apply (intro conjI impI)
  apply meson
  apply(rule_tac ?x = "offset s + Data s (numEnqs s)" in exI)
  apply (intro conjI impI)
  apply (metis F.distinct(5))
  apply (metis (mono_tags, hide_lams) le_trans less_or_eq_imp_le linorder_neqE_nat) 
  apply (metis F.distinct(5)) 
  apply (metis F.distinct(1))
  apply (metis le_trans less_or_eq_imp_le)
  apply (metis Suc_leI not_less_eq_eq)
  apply blast
  apply (metis less_irrefl_nat)
  apply (metis less_irrefl_nat)
  apply meson
  apply meson 
  apply (metis (no_types, hide_lams) F.distinct(1) F.distinct(5) diff_diff_left diff_is_0_eq' linorder_neqE_nat nat_add_left_cancel_less nat_le_linear zero_less_diff)
  apply metis
  by (metis F.distinct(1) F.distinct(5) Suc_pred bot_nat_0.not_eq_extremum diff_0_eq_0 diff_Suc_Suc diff_diff_cancel diff_diff_left diff_is_0_eq diff_is_0_eq' diff_self_eq_0 le_refl less_nat_zero_code linorder_neqE_nat nat_add_left_cancel_less nat_le_linear not0_implies_Suc old.nat.inject zero_less_Suc zero_less_diff)

            
            





lemma case_trans_Write_to_Enqueue_case_1:
  shows "pre_write_inv s \<Longrightarrow> inv s\<Longrightarrow> s'=s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
       ownD :=
         \<lambda>i. if i = numWrites s then B
             else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i,
       data_index :=
         \<lambda>x. if (offset s, Data s (numEnqs s)) = x then numEnqs s
             else data_index
                   (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
                        ownD :=
                          \<lambda>i. if i = numWrites s then B
                              else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i\<rparr>)
                   x\<rparr> \<Longrightarrow>case_1 s \<Longrightarrow> con_assms s
     \<Longrightarrow>case_1 s'"
  by (simp add:pre_write_inv_def case_1_def)


lemma case_trans_Write_to_Enqueue_case_2:
  shows "pre_write_inv s \<Longrightarrow> inv s\<Longrightarrow> s'=s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
       ownD :=
         \<lambda>i. if i = numWrites s then B
             else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i,
       data_index :=
         \<lambda>x. if (offset s, Data s (numEnqs s)) = x then numEnqs s
             else data_index
                   (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
                        ownD :=
                          \<lambda>i. if i = numWrites s then B
                              else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i\<rparr>)
                   x\<rparr> \<Longrightarrow>case_2 s \<Longrightarrow> con_assms s
     \<Longrightarrow>case_2 s'"
  by (simp add:pre_write_inv_def case_2_def)

lemma case_trans_Write_to_Enqueue_case_3:
  shows "pre_write_inv s \<Longrightarrow> inv s\<Longrightarrow> s'=s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
       ownD :=
         \<lambda>i. if i = numWrites s then B
             else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i,
       data_index :=
         \<lambda>x. if (offset s, Data s (numEnqs s)) = x then numEnqs s
             else data_index
                   (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
                        ownD :=
                          \<lambda>i. if i = numWrites s then B
                              else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i\<rparr>)
                   x\<rparr> \<Longrightarrow>case_1 s \<or> case_2 s \<Longrightarrow> con_assms s
     \<Longrightarrow>case_1 s' \<or> case_2 s'"
  by (simp add:pre_write_inv_def case_1_def case_2_def)

lemma case_trans_Write_to_Enqueue_case_4:
  shows " s'=s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
       ownD :=
         \<lambda>i. if i = numWrites s then B
             else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i,
       data_index :=
         \<lambda>x. if (offset s, Data s (numEnqs s)) = x then numEnqs s
             else data_index
                   (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
                        ownD :=
                          \<lambda>i. if i = numWrites s then B
                              else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i\<rparr>)
                   x\<rparr> 
     \<Longrightarrow>\<forall>i::nat. ownB s i=ownB s' i \<and> T s = T s' \<and> H s = H s' \<and> offset s = offset s' \<and> tempR s=tempR s' \<and> q s=q s'"
  by simp 

(************************************* queue transition lemmas **************************************************)



lemma peculiar_1:
  assumes "Q_gap_structure s"
  and "Q_offsets_differ s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
  shows "fst(q s!1) = end(q s!0) \<or> fst(q s!1) =0"
  using assms apply(simp add:Q_gap_structure_def Q_offsets_differ_def Q_structure_def) 
  by (metis One_nat_def diff_add_zero length_greater_0_conv length_tl less_numeral_extra(1) plus_1_eq_Suc zero_less_diff)
  
lemma peculiar_2:
  assumes "Q_gap_structure s"
  and "Q_offsets_differ s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
  shows "(end(hd(q s)) = fst(hd(tl(q s)))\<and> fst(hd(tl(q s)))\<noteq>0) \<or> fst(hd(tl(q s))) =0"
  using assms apply(simp add:Q_gap_structure_def Q_offsets_differ_def Q_structure_def) 
  by (metis Nitpick.size_list_simp(2) One_nat_def diff_add_zero hd_conv_nth less_Suc_eq_0_disj not_gr_zero nth_tl plus_1_eq_Suc)
  
lemma peculiar_3:
  assumes "Q_structure s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "(end(hd(q s)) = fst(hd(tl(q s)))\<and> fst(hd(tl(q s)))\<noteq>0) \<or> fst(hd(tl(q s))) =0"
  using peculiar_1 peculiar_2 Q_structure_def Q_basic_struct_def 
proof -
  have "Q_basic_struct s"
by (metis (no_types) Nil_tl Q_structure_def assms(1) assms(3))
then show ?thesis
by (metis Nil_tl Q_basic_struct_def assms(3) peculiar_2)
qed

lemma peculiar_4:
  assumes "Q_offsets_differ s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "\<forall>i.(i<length(q s) \<and> i>0)\<longrightarrow>fst(q s!0) \<noteq> fst(q s!i)"
  using assms by (simp add:Q_offsets_differ_def) 

lemma peculiar_5:
  assumes "Q_offsets_differ s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "\<forall>i.(i<length(q s) \<and> i>0)\<longrightarrow>fst(hd(q s)) \<noteq> fst(q s!i)"
  using assms peculiar_4 
  by (simp add: peculiar_4 hd_conv_nth)

lemma peculiar_6:
  assumes "Q_offsets_differ s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "\<forall>i.(i<length(tl(q s)))\<longrightarrow>fst(hd(q s)) \<noteq> fst(tl(q s)!i)"
  using peculiar_4 peculiar_5 
  by (simp add: Q_head_relates_tail assms(1) assms(2) hd_conv_nth)

lemma peculiar_7:
  assumes "Q_offsets_differ s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "\<forall>i.(i<(length((q s))-1))\<longrightarrow>fst(hd(q s)) \<noteq> fst(tl(q s)!i)"
  using assms peculiar_6 
  by (simp add: peculiar_6)

lemma peculiar_8:
  assumes "Q_has_no_overlaps s"
  and "Q_has_no_uroboros s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "\<forall>x.(x\<in>set(q s) \<and> x\<noteq>hd(q s) \<and> fst(hd(q s))<fst(x))\<longrightarrow>end(hd(q s))\<le>fst(x)"
  using assms Q_has_no_overlaps_def Q_has_no_uroboros_def
  using hd_in_set by blast

lemma peculiar_9:
  assumes "Q_has_no_overlaps s"
  and "Q_has_no_uroboros s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "\<forall>x.(x\<in>set(tl(q s)) \<and> fst(hd(q s))<fst(x))\<longrightarrow>end(hd(q s))\<le>fst(x)"
  using peculiar_8 
  by (metis assms(1) assms(2) assms(3) assms(4) dual_order.irrefl list.set_sel(2))

lemma peculiar_10:
  assumes "Q_has_no_overlaps s"
  and "Q_has_no_uroboros s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "\<forall>i.(i<(length(q s)-1) \<and> fst(hd(q s))<fst(tl(q s)!i))\<longrightarrow>end(hd(q s))\<le>fst(tl(q s)!i)"
  by (metis assms(1) assms(2) assms(3) assms(4) length_tl nth_mem peculiar_9)

lemma peculiar_11:
  assumes "Q_has_no_overlaps s"
  and "Q_has_no_uroboros s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "\<forall>x.(x\<in>set(q s) \<and> x\<noteq>hd(q s) \<and> fst(hd(q s))>fst(x))\<longrightarrow>fst(hd(q s))\<ge>end(x)"
  using assms Q_has_no_overlaps_def Q_has_no_uroboros_def 
  using hd_in_set by blast

lemma peculiar_12:
  assumes "Q_has_no_overlaps s"
  and "Q_has_no_uroboros s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "\<forall>x.(x\<in>set(tl(q s)) \<and> fst(hd(q s))>fst(x))\<longrightarrow>fst(hd(q s))\<ge>end(x)"
  using assms Q_has_no_overlaps_def peculiar_11 
  by (metis list.set_sel(2))

lemma peculiar_13:
  assumes "Q_has_no_overlaps s"
  and "Q_has_no_uroboros s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "\<forall>i.(i<(length(q s)-1) \<and> fst(hd(q s))>fst(tl(q s)!i))\<longrightarrow>fst(hd(q s))\<ge>end(tl(q s)!i)"
  using assms peculiar_12 
  by (metis length_tl nth_mem)

lemma peculiar_14:
  assumes "Q_has_no_overlaps s"
  and "Q_has_no_uroboros s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "(\<forall>i.(i<(length(q s)-1) \<and> fst(hd(q s))>fst(tl(q s)!i))\<longrightarrow>fst(hd(q s))\<ge>end(tl(q s)!i))
      \<and>(\<forall>i.(i<(length(q s)-1) \<and> fst(hd(q s))<fst(tl(q s)!i))\<longrightarrow>end(hd(q s))\<le>fst(tl(q s)!i))"
  using peculiar_13 peculiar_10 
  using assms(1) assms(2) assms(3) assms(4) by blast

lemma peculiar_15:
  assumes "Q_has_no_overlaps s"
  and "Q_has_no_uroboros s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "\<forall>i<length (q s) - Suc 0.
       (fst (hd (q s)) < fst (tl (q s) ! i) \<longrightarrow>
        fst (hd (q s)) + snd (hd (q s)) \<le> fst (tl (q s) ! i)) \<and>
       (fst (tl (q s) ! i) < fst (hd (q s)) \<longrightarrow>
        fst (tl (q s) ! i) + snd (tl (q s) ! i) \<le> fst (hd (q s)))"
  using peculiar_14 
  by (metis One_nat_def assms(1) assms(2) assms(3) assms(4) end_simp)


lemma peculiar_16:
  assumes "Q_structure s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "\<forall>i<length (q s) - Suc 0.
       (fst (hd (q s)) < fst (tl (q s) ! i) \<longrightarrow>
        fst (hd (q s)) + snd (hd (q s)) \<le> fst (tl (q s) ! i)) \<and>
       (fst (tl (q s) ! i) < fst (hd (q s)) \<longrightarrow>
        fst (tl (q s) ! i) + snd (tl (q s) ! i) \<le> fst (hd (q s)))"
  using peculiar_15 Q_structure_def 
  using Q_basic_struct_def assms(1) assms(2) assms(3) by auto

lemma peculiar_17 :
  assumes "inv s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "\<forall>i<length (q s) - Suc 0.
       (fst (hd (q s)) < fst (tl (q s) ! i) \<longrightarrow>
        fst (hd (q s)) + snd (hd (q s)) \<le> fst (tl (q s) ! i)) \<and>
       (fst (tl (q s) ! i) < fst (hd (q s)) \<longrightarrow>
        fst (tl (q s) ! i) + snd (tl (q s) ! i) \<le> fst (hd (q s)))"
  using peculiar_16 inv_def Q_structure_def 
  using assms(1) assms(2) assms(3) by blast

lemma peculiar_18:
  assumes "Q_has_no_uroboros s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "fst (q s!0) \<noteq> end (last (q s))"
  using Q_has_no_uroboros_def 
  by (metis assms(1) assms(2) assms(3) butlast.simps(2) list.exhaust_sel list.set_intros(1) nth_Cons_0)

lemma peculiar_19:
  assumes "Q_structure s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "fst (q s!0) \<noteq> end (last (q s))"
  using Q_has_no_uroboros_def Q_structure_def peculiar_18 
  using Q_basic_struct_def assms(1) assms(2) assms(3) by blast

lemma peculiar_20:
  assumes "Q_structure s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "fst (hd(q s)) \<noteq> end (last (q s))"
  using peculiar_19
  by (metis assms(1) assms(2) assms(3) hd_conv_nth)

lemma peculiar_21:
  assumes "Q_structure s"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "fst (hd(q s)) \<noteq> end (last (tl(q s)))"
  using peculiar_20
  by (metis assms(1) assms(2) assms(3) last_tl)

lemma peculiar_22:
  assumes "Q_structure s"
  and "tempR_structure s"
  and "fst(tempR s) =0"
shows "\<forall>i.(i<length(q s)\<and> i>0)\<longrightarrow>fst(q s!i) = end(q s!(i-1))"
  using assms apply (simp add:Q_lemmas Q_basic_lemmas tempR_lemmas tempR_basic_lemmas)
  by (metis length_0_conv less_nat_zero_code)

lemma peculiar_23:
  assumes "Q_structure s"
  and "tempR_structure s"
  and "fst(tempR s) =0"
shows "\<forall>i.(i<length(q s))\<longrightarrow>fst(q s!i) >0"
  using assms apply (simp add:Q_lemmas Q_basic_lemmas tempR_lemmas tempR_basic_lemmas)
  by (metis length_0_conv less_nat_zero_code)

lemma peculiar_24:
  assumes "Q_structure s"
  and "tempR_structure s"
  and "fst(tempR s) =0"
  and "q s\<noteq>[]" and "tl(q s)\<noteq>[]"
shows "fst(q s!0) =end(tempR s)"
  using assms apply (simp add:Q_lemmas Q_basic_lemmas tempR_lemmas tempR_basic_lemmas)
  by (metis hd_conv_nth length_greater_0_conv zero_less_iff_neq_zero)

lemma peculiar_25:
  assumes "Q_offsets_differ s"
  and "Q_gap_structure s"
  and "fst(hd(q s)) =0"
  and "tl(q s)\<noteq>[]"
shows "\<forall>i.(i<length(q s)\<and>i>0)\<longrightarrow>fst(q s!i) = end(q s!(i-1))"
  using assms 
  by (metis Q_hd_zero_implies_structure)

lemma peculiar_26:
  assumes "Q_offsets_differ s"
  and "Q_gap_structure s"
  and "fst(hd(q s)) =0"
  and "tl(q s)\<noteq>[]"
shows "\<forall>i.(i<length(q s)\<and>i>0)\<longrightarrow>(q s!i) = (tl(q s)!(i-1))"
  using assms apply(simp add:Q_lemmas Q_basic_lemmas)
  by (metis Nitpick.size_list_simp(2) Suc_pred add_less_cancel_left list.sel(2) nth_tl plus_1_eq_Suc)


lemma peculiar_27:
  assumes "Q_offsets_differ s"
  and "Q_gap_structure s"
  and "fst(hd(q s)) =0"
  and "tl(q s)\<noteq>[]"
shows "\<forall>i.(i<length(q s)\<and>i>1)\<longrightarrow>fst(tl(q s)!(i-1)) = end(tl(q s)!(i-2))"
  using assms apply(simp add:Q_lemmas Q_basic_lemmas)
  by (smt (verit, ccfv_SIG) Nitpick.size_list_simp(2) Suc_diff_Suc add_less_cancel_left assms(1) assms(2) diff_less less_trans_Suc list.sel(2) nth_tl numeral_1_eq_Suc_0 numeral_2_eq_2 numerals(1) peculiar_26 peculiar_5 plus_1_eq_Suc zero_less_two)




lemma peculiar_28:
  assumes "Q_offsets_differ s"
  and "Q_gap_structure s"
  and "Q_has_no_uroboros s"
  and "fst(hd(q s)) =0"
  and "tl(q s)\<noteq>[]"
  and "butlast(tl(q s))\<noteq>[]"
shows "last(tl(q s)) =last(q s)"
  using assms 
  by (simp add: last_tl)



lemma peculiar_29:
  assumes "Q_offsets_differ s"
  and "Q_gap_structure s"
  and "Q_has_no_uroboros s"
  and "fst(hd(q s)) =0"
  and "tl(q s)\<noteq>[]"
  and "butlast(tl(q s))\<noteq>[]"
shows "\<forall>i.(i<length(butlast(tl(q s))))\<longrightarrow>(tl(q s)!i) = (q s!(i+1))"
  using assms 
  by (simp add: peculiar_26)

lemma peculiar_30:
  assumes "Q_offsets_differ s"
  and "Q_gap_structure s"
  and "Q_has_no_uroboros s"
  and "fst(hd(q s)) =0"
  and "tl(q s)\<noteq>[]"
  and "butlast(tl(q s))\<noteq>[]"
shows "end(last(q s)) = end(last(tl(q s)))"
  using assms 
  by (simp add: last_tl)


lemma peculiar_31:
  assumes "Q_offsets_differ s"
  and "Q_gap_structure s"
  and "Q_has_no_uroboros s"
  and "fst(hd(q s)) =0"
  and "tl(q s)\<noteq>[]"
  and "butlast(tl(q s))\<noteq>[]"
shows "\<forall>i.(i<(length(tl(q s))-1))\<longrightarrow>fst(tl(q s)!i) \<noteq>end(last(tl(q s)))"
  using assms peculiar_30 peculiar_29 apply simp
  unfolding Q_lemmas Q_basic_lemmas apply safe apply(subgoal_tac "last(tl(q s)) =(tl(q s)!(length(tl(q s))-1))")
  prefer 2 
  apply (simp add: last_conv_nth) apply simp
  by (metis One_nat_def Suc_eq_plus1 Suc_lessD assms(5) diff_Suc_eq_diff_pred in_set_conv_nth last_tl length_butlast length_tl less_diff_conv nth_butlast nth_tl prod.exhaust_sel)



lemma tail_preserves_struct:
  "Q_gap_structure s \<Longrightarrow> fst (q s ! 0) = 0 \<Longrightarrow>\<forall> i . i<length (q s) \<longrightarrow> snd(q s ! i) > 0 \<Longrightarrow>
  Q_offsets_differ s \<Longrightarrow> length(q s)>0 \<Longrightarrow>
\<forall> i . (i<length (q s) \<and> i>0)\<longrightarrow> fst(q s ! i) > fst (q s ! 0)"
  apply(simp add:Q_gap_structure_def Q_offsets_differ_def)
  by (metis gr_implies_not_zero not_gr_zero)


lemma queue_is_finite_set:
  assumes "con_assms s"
  and "Q_structure s"
shows "\<forall>a b.((a,b)\<in>set(q s))\<longleftrightarrow>(\<exists>i.(i<length(q s) \<and> (a, b) =(q s!i)))"
  using assms apply(simp add:Q_lemmas Q_basic_lemmas)
  by (metis in_set_conv_nth)
  

































(**********************Supporting lemmas for R trans*********************************)




lemma R_idle_to_nidle_lemma_case_1_1:
  "case_1 s\<Longrightarrow>con_assms s \<Longrightarrow> pcR s = idleR\<Longrightarrow>pre_R (pcR s) s
  \<Longrightarrow>s'=(s\<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
          numDeqs := Suc (numDeqs s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr>)
\<Longrightarrow>inv s
\<Longrightarrow>i<fst(hd(q s))\<longrightarrow>ownB s i=ownB s' i"
  by(simp add:case_1_def) 


lemma R_idle_to_nidle_lemma_case_1_2:
  "case_1 s\<Longrightarrow>con_assms s \<Longrightarrow> pcR s = idleR\<Longrightarrow>pre_R (pcR s) s
  \<Longrightarrow>s'=(s\<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
          numDeqs := Suc (numDeqs s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr>)
\<Longrightarrow>inv s
\<Longrightarrow>i>end(hd(q s))\<longrightarrow>ownB s i=ownB s' i"
  by(simp add:case_1_def) 



lemma R_idle_to_nidle_lemma_case_1_3:
  "case_1 s\<Longrightarrow>con_assms s \<Longrightarrow> pcR s = idleR\<Longrightarrow>pre_R (pcR s) s
  \<Longrightarrow>s'=(s\<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
          numDeqs := Suc (numDeqs s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr>)
\<Longrightarrow>inv s
\<Longrightarrow>fst(hd(q s))\<le>i \<and> i<end(hd(q s))\<longrightarrow>R=ownB s' i"
  by(simp add:case_1_def) 



lemma R_idle_to_nidle_lemma_case_1_4:
  "case_1 s\<Longrightarrow>con_assms s \<Longrightarrow> pcR s = idleR\<Longrightarrow>pre_R (pcR s) s
  \<Longrightarrow>s'=(s\<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
          numDeqs := Suc (numDeqs s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr>)
\<Longrightarrow>inv s
\<Longrightarrow>T s=T s'\<and>H s=H s'\<and>offset s=offset s'\<and>ownT s'=R"
  by(simp add:case_1_def) 


lemma sum_of_things:
  "q s!0 = (2,3) \<Longrightarrow> (length(q s) = 1)\<longrightarrow>\<Sum>{j. j=(snd(q s!0))} = 3"
  by simp 

lemma sum_of_things_2:
  "q s=[(0,1)] \<Longrightarrow> length(q s) = 1"
  by simp


lemma sum_of_things_3:
  " length(q s)>0 \<Longrightarrow> \<forall>i. i<length(q s) \<longrightarrow> snd(q s!i) =1\<Longrightarrow> (\<Sum>i::nat=0..length(q s)-1. 1) = length(q s)"
  by auto 

lemma sum_of_things_4:
  " length(q s)>1 \<Longrightarrow> \<forall>i. i<length(q s) \<longrightarrow> snd(q s!i) =1\<Longrightarrow> (\<Sum>i::nat=0..(length(q s)-1). snd(q s!i)) = length(q s)"
  by auto

lemma sum_of_things_5:
  "n>0\<Longrightarrow> (\<Sum>i::nat=0..n. k) = (\<Sum>i::nat=1..n. k) + k "
proof (induct n)
  show "0 = n \<Longrightarrow>
    0 < n \<Longrightarrow>
    (\<Sum>i = 0..n. k) = (\<Sum>i = 1..n. k) + k" by simp
next show "\<And>x. (x = n \<Longrightarrow>
          0 < n \<Longrightarrow>
          (\<Sum>i = 0..n. k) =
          (\<Sum>i = 1..n. k) + k) \<Longrightarrow>
         Suc x = n \<Longrightarrow>
         0 < n \<Longrightarrow>
         (\<Sum>i = 0..n. k) =
         (\<Sum>i = 1..n. k) + k" 
    by (metis add.commute add_diff_cancel_left' le_add1 plus_1_eq_Suc sum.atLeast0_atMost_Suc_shift sum.atLeastAtMost_shift_0)
qed



lemma sum_of_things_6:
  "length(q s) =n+2\<Longrightarrow> (\<Sum>i::nat=0..(length(q s)-1). 1) = (\<Sum>i::nat=1..(length(q s)-1). 1) + 1 "
  apply auto
proof (induct n)
  case 0
  then show ?case  
    by simp
next
  case (Suc x)
  then show ?case 
    by (metis add.commute add.right_neutral nat.distinct(1) not_gr_zero plus_1_eq_Suc sum_of_things_5)
qed


lemma sum_of_things_7:
  "length(q s) =n+2\<Longrightarrow> \<forall>i. (i<length(q s)) \<longrightarrow> snd(q s!i) =1\<Longrightarrow>
 (\<Sum>i::nat=0..(length(q s)-1). snd(q s!i)) = (\<Sum>i::nat=1..(length(q s)-1). snd(q s!i)) + snd(q s!0) "
  by auto


lemma sum_of_things_8:
  "length(q s) =n+2\<Longrightarrow>
 (\<Sum>i::nat=0..(length(q s)-1). snd(q s!i)) = (\<Sum>i::nat=1..(length(q s)-1). snd(q s!i)) + snd(q s!0) "
  apply auto
proof (induct n)
  case 0
  then show ?case 
    by auto
next 
  case (Suc x)
  then show ?case
    by (simp add: sum.atLeast_Suc_atMost)
qed


lemma sum_of_things_9:
  " length(q s)=n+2 \<Longrightarrow> \<forall>i. (i<length(q s) \<and> i>0) \<longrightarrow> snd(q s!i) =1\<Longrightarrow> 
(\<Sum>i::nat=0..(length(q s)-1). snd(q s!i)) = (\<Sum>i::nat=1..(length(q s)-1). snd(q s!i)) + snd(q s!0) "
  apply auto 
proof (induct n) case 0 then show ?case   by auto
next  case (Suc x) then show ?case  by (simp add: sum.atLeast_Suc_atMost)
qed  


lemma sum_of_things_10:
  " length(q s)\<ge>2 \<Longrightarrow> \<forall>i. (i<length(q s) \<and> i>0) \<longrightarrow> snd(q s!i) =1\<Longrightarrow> 
(\<Sum>i::nat=0..(length(q s)-1). snd(q s!i)) = (\<Sum>i::nat=1..(length(q s)-1). snd(q s!i)) + snd(q s!0) "
  apply auto
  by (metis add.commute sum.atLeast_Suc_atMost zero_le)

lemma sum_of_things_11:
  " length(q s) = n+2 \<Longrightarrow> \<forall>i. (i<length(q s) \<and> i>0) \<longrightarrow> snd(q s!i) =1\<Longrightarrow> 
(\<Sum>i::nat=0..(length(q s)-1). snd(q s!i)) = length(q s)-1 + snd(q s!0) "
  apply auto 
proof (induct n) case 0 then show ?case   by auto
next  case (Suc x) then show ?case by (simp add: sum.atLeast_Suc_atMost)
qed  


lemma sum_of_things_12:
  " length(q s) = n+2 \<Longrightarrow> \<forall>i. (i<length(q s) \<and> i>0) \<longrightarrow> snd(q s!i) =1\<Longrightarrow> 
(\<Sum>i::nat=1..(length(q s)-1). snd(q s!i)) = length(q s)-1  "
  by auto 

lemma sum_of_things_13:
  " \<forall>n.(n\<ge>0) \<longrightarrow>length(q s) = n+2 \<Longrightarrow> \<forall>i. (i<length(q s) \<and> i>0) \<longrightarrow> snd(q s!i) =1\<Longrightarrow> 
(\<Sum>i::nat=1..(length(q s)-1). snd(q s!i)) = length(q s)-1  "
  using sum_of_things_12 [where s=s] 
  by blast

lemma sum_of_things_14:
  " \<forall>k.(k\<ge>2)\<longrightarrow>length(q s) = k \<Longrightarrow> \<forall>i. (i<length(q s) \<and> i>0) \<longrightarrow> snd(q s!i) =1\<Longrightarrow> 
(\<Sum>i::nat=1..(length(q s)-1). snd(q s!i)) = length(q s)-1  "
  using sum_of_things_13 [where s=s]
  using le_add2 by blast







lemma R_idle_to_nidle_lemma_case_1_5_1:
  "inv s \<Longrightarrow>q s\<noteq>[]
\<Longrightarrow>\<forall>a b aa bb.((a,b)\<in>set(q s) \<and> (aa,bb)\<in>set(q s) \<and> a<aa)\<longrightarrow>a+b\<le>aa"
  apply simp
  by(simp add:inv_def Q_lemmas Q_basic_lemmas)

lemma R_idle_to_nidle_lemma_case_1_5_2:
  "inv s \<Longrightarrow>q s\<noteq>[]
\<Longrightarrow>\<forall>a b aa bb.((a,b)\<in>set(q s) \<and> (aa,bb)\<in>set(q s) \<and> a+b\<le>aa)\<longrightarrow>a+b<aa+bb"
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  by (metis less_add_same_cancel1 nat_less_le trans_less_add1)


lemma R_idle_to_nidle_lemma_case_1_5:
  "case_1 s\<Longrightarrow>con_assms s \<Longrightarrow> pcR s = idleR\<Longrightarrow>pre_R (pcR s) s
  \<Longrightarrow>s'=(s\<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
          numDeqs := Suc (numDeqs s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr>)
\<Longrightarrow>inv s \<Longrightarrow>q s\<noteq>[]
\<Longrightarrow>case_1 s'"
  apply(simp add:case_1_def inv_def) 
  apply(clarify) apply(intro conjI impI)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(subgoal_tac "fst (last (q s)) + snd (last (q s))\<le>N") prefer 2
  apply linarith
  apply(subgoal_tac "q s\<noteq>[]\<longrightarrow>hd(q s) \<in>set(q s)") prefer 2 
  apply (metis list.set_sel(1))
  apply(subgoal_tac "q s\<noteq>[]") prefer 2 
  apply blast
  apply (metis diff_is_0_eq less_nat_zero_code prod.collapse zero_less_diff)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(rule_tac ?x = "T s" in exI)
  apply(rule_tac ?x = "end(hd(q s))" in exI)
  apply(intro conjI impI)
  apply (metis cancel_comm_monoid_add_class.diff_cancel end_simp le_0_eq le_neq_implies_less length_0_conv trans_le_add1)
  apply(rule_tac ?x = "fst (last (q s)) + snd (last (q s))" in exI)
  apply(simp add:pre_R_def  pre_dequeue_inv_def) 
  apply(intro conjI impI) 
  apply(subgoal_tac "last(q s) \<in>set(q s) \<and> hd(q s)\<in>set(q s)") prefer 2 
  apply (metis last_in_set list.set_sel(1))
  defer
  apply (metis (no_types, lifting) F.distinct(19) F.distinct(3) diff_is_0_eq le_0_eq le_neq_implies_less length_0_conv nat_le_linear)
  apply (metis (no_types, hide_lams) F.distinct(3)) 
  defer
  apply (metis le_neq_implies_less le_refl)
  apply (metis diff_add_inverse eq_imp_le le_neq_implies_less) 
  apply (subgoal_tac "((fst (hd (q s)) + snd (hd (q s)) < fst (last (q s)) + snd (last (q s))) \<longrightarrow> (Suc 0 < length (q s))) \<and>
   ((Suc 0 < length (q s)\<longrightarrow>fst (hd (q s)) + snd (hd (q s)) < fst (last (q s)) + snd (last (q s))))")
  apply blast defer
  apply(subgoal_tac "hd(q s) = (q s!0)") prefer 2 
  apply (metis hd_conv_nth)
  apply(subgoal_tac "hd(tl(q s)) = (q s!1)") prefer 2
  apply (metis (no_types, lifting) One_nat_def diff_add_inverse2 hd_conv_nth last_conv_nth length_greater_0_conv length_tl less_diff_conv list.size(3) nth_tl)
  apply(case_tac "fst(q s!0) = 0") 
  apply(subgoal_tac "fst(hd(q s)) = 0") prefer 2
  apply presburger
  apply(subgoal_tac "i<length(q s) \<and> j<length(q s) \<and> i\<noteq>j \<longrightarrow> fst(q s!i) \<noteq>fst(q s!j)") prefer 2 
  apply (metis (no_types, lifting))
  apply(subgoal_tac "i<(length(q s))\<and>i>0\<and> fst(q s!0) = 0\<longrightarrow> fst(q s!(i-1)) + snd(q s!(i-1)) = fst(q s!i)") prefer 2
  apply (metis (no_types, lifting) One_nat_def length_greater_0_conv)
  apply(case_tac "length(q s) > 1") 
  apply(subgoal_tac "fst(q s!0) = 0\<longrightarrow> fst(q s!(0)) + snd(q s!(0)) = fst(q s!1)") prefer 2
  apply (metis (no_types, lifting) One_nat_def diff_Suc_1 length_greater_0_conv less_one)
  apply presburger
  apply (metis diff_self_eq_0 last_conv_nth length_0_conv less_nat_zero_code less_one nat_neq_iff)
  apply(subgoal_tac "fst(hd(q s))>0") prefer 2 
  using gr0I apply presburger
  apply(subgoal_tac "ownB s 0 \<noteq> Q") prefer 2 
  apply (metis F.distinct(19) gr0I le_numeral_extra(3))
  apply(subgoal_tac " \<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) = (i \<le> N \<and> ownB s i = Q)") prefer 2 
  apply blast
  apply(subgoal_tac "0\<le>N") prefer 2
  apply blast
  apply(subgoal_tac "(\<nexists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> 0 \<in> x)")
  prefer 2
  apply presburger
  apply(subgoal_tac "\<nexists>a b. (a,b) \<in> set(q s) \<and> a=0") prefer 2 
  apply (metis (no_types, lifting) bot_nat_0.extremum mem_Collect_eq plus_nat.add_0)
  apply(subgoal_tac "i<length(q s) \<longrightarrow> (q s!i) \<in> set(q s)") prefer 2 
  apply (metis nth_mem)
  apply(subgoal_tac "(sta,wlength)\<in>set(q s) \<longrightarrow> (\<exists>i.(i<length(q s) \<and> (sta,wlength) = q s!i))") prefer 2
  apply (metis in_set_conv_nth)
  apply(subgoal_tac "\<forall>sta wlength. (sta,wlength)\<in>set(q s) \<longrightarrow> sta\<noteq>0") prefer 2 
  apply metis
  apply(subgoal_tac "i<length(q s) \<longrightarrow>fst(q s!i)\<noteq>0") prefer 2
  apply (metis prod.collapse)
  apply(subgoal_tac "i<(length(q s))\<and>i>0\<longrightarrow> fst(q s!(i-1)) + snd(q s!(i-1)) = fst(q s!i)") prefer 2
  apply (metis (no_types, lifting) One_nat_def)
  apply(case_tac "length(q s)>1") 
  apply (metis (no_types, lifting) One_nat_def diff_Suc_1 less_one nth_mem prod.collapse)
  apply(case_tac "length(q s) = 0")
  apply fastforce
  apply(subgoal_tac "length(q s) = 1") prefer 2
  apply linarith
  apply(subgoal_tac "length(tl(q s)) = 0") prefer 2
  apply (metis diff_self_eq_0 length_tl)
  apply (metis diff_self_eq_0 last_conv_nth le_neq_implies_less less_irrefl_nat not_one_le_zero)
  apply(case_tac "length(q s) \<le>1")
  apply (metis bot_nat_0.extremum_uniqueI diff_add_inverse2 diff_is_0_eq' head_q0 last_conv_nth le_neq_implies_less length_greater_0_conv less_diff_conv less_numeral_extra(3))
  apply (metis (no_types, lifting) One_nat_def diff_is_0_eq last_tl le_Suc_eq le_neq_implies_less length_tl list.size(3))
  apply (metis (no_types, lifting) diff_add_inverse diff_is_0_eq' le_0_eq le_eq_less_or_eq length_0_conv linorder_neqE_nat list.set_sel(1) nat_less_le not_add_less1 prod.collapse)
  apply (metis diff_add_inverse diff_is_0_eq' le_eq_less_or_eq less_nat_zero_code list.set_sel(1) prod.collapse)                       
  apply(subgoal_tac "(\<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a < aa \<longrightarrow> a + b \<le> aa)") prefer 2
  apply presburger
  apply(subgoal_tac "(\<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a + b > aa \<longrightarrow>a \<ge> aa )") prefer 2
  apply (metis (no_types, hide_lams) diff_is_0_eq' linorder_neqE_nat nat_le_linear zero_less_diff)
  apply(subgoal_tac "(\<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a + b > aa \<longrightarrow>a \<ge> aa )") prefer 2
  apply (metis (no_types, hide_lams) diff_is_0_eq' linorder_neqE_nat nat_le_linear zero_less_diff)
  apply(subgoal_tac "(\<forall>a b aa bb . ((a, b) \<in> set (q s) \<and>  (aa, bb) \<in> set (q s)) \<longrightarrow> a + b \<ge> aa + bb \<longrightarrow>a \<ge> aa )") prefer 2
  apply (metis (no_types, lifting) less_add_same_cancel1 nat_le_iff_add trans_less_add1)
  apply(subgoal_tac "(\<forall>a b aa bb . ((a, b) \<in> set (q s) \<and>  (aa, bb) \<in> set (q s)) \<longrightarrow> a <  aa \<longrightarrow> a + b \<le> aa + bb)") prefer 2
  apply (meson trans_le_add1)
  apply(case_tac "hd(q s) \<noteq> last(q s)")
  apply(subgoal_tac "fst(hd(q s)) < fst(last(q s))")
  apply (metis (no_types, lifting) prod.collapse)
  apply(subgoal_tac "i<length(q s) \<and> j<length(q s) \<and> i\<noteq>j \<longrightarrow> fst(q s!i)\<noteq>fst(q s!j)")
  prefer 2 
  apply presburger
  apply(subgoal_tac "ownB s (fst(q s!0)) = Q") prefer 2 
  apply (metis (no_types, lifting) head_q0 le_eq_less_or_eq length_greater_0_conv)
  apply(subgoal_tac "ownB s (fst(last(q s))) = Q") prefer 2
  apply (metis (no_types, lifting) less_add_same_cancel1 prod.collapse)
  apply(subgoal_tac "\<forall>i.(ownB s i=Q \<and> i\<le>N)\<longrightarrow>i\<ge>fst(q s!0)") prefer 2 
  apply (metis F.distinct(19) hd_conv_nth less_Suc_eq_le not_less_eq)
  apply(subgoal_tac "hd(q s) = (q s!0) \<and> last(q s) = (q s!(length(q s)-1))") prefer 2
  apply (metis hd_conv_nth last_conv_nth) 
  apply (metis (no_types, lifting) diff_less length_pos_if_in_set less_one nat_less_le prod.collapse)
  using le_eq_less_or_eq apply presburger
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) = (i \<le> N \<and> ownB s i = Q)")
  prefer 2 
  apply blast
  apply(subgoal_tac "hd(q s) \<in>set(q s)") prefer 2
  apply (metis hd_in_set)
  apply(case_tac "hd(q s) = last(q s)") 
  apply (metis Suc_diff_le Suc_leI Suc_neq_Zero diff_is_0_eq le_trans)
  apply(subgoal_tac "i\<ge>H s \<and> i\<le>N \<longrightarrow> ownB s i \<noteq>Q") prefer 2
  apply (metis F.distinct(19) F.distinct(23) le_eq_less_or_eq)
  apply(subgoal_tac "i\<ge>fst(q s!0) \<and> i<fst(q s!0) + snd(q s!0)\<longrightarrow> ownB s i = Q") prefer 2
  apply (metis (no_types, lifting) head_q0 length_greater_0_conv)
  defer (*SMT*)
  apply(intro conjI impI)
  apply(subgoal_tac "hd(q s) = (q s!0) \<and> last(q s) = (q s!(length(q s)-1))") prefer 2 
  apply (meson hd_conv_nth last_conv_nth)
  apply (metis (no_types, lifting) One_nat_def Suc_lessI diff_self_eq_0 length_greater_0_conv less_not_refl2)
  apply(subgoal_tac "hd(q s)\<in> set(q s) \<and> last(q s) \<in>set(q s)") prefer 2 
  apply (metis last_in_set list.set_sel(1))
  apply(subgoal_tac "(a,b)\<in>set(q s)\<longrightarrow>b>0") prefer 2 
  apply blast
  apply(subgoal_tac "fst(hd(q s)) < fst(last(q s))") 
  apply (metis (no_types, lifting) linorder_neqE_nat nat_less_le prod.collapse trans_less_add1)
  apply(subgoal_tac "i<fst(hd(q s)) \<longrightarrow> ownB s i \<noteq>Q") prefer 2
  apply (metis F.distinct(19) le_eq_less_or_eq)
  apply(subgoal_tac "\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> i\<noteq>j)\<longrightarrow>fst(q s!i)\<noteq>fst(q s!j)") prefer 2
  apply presburger
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} 
   \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) = (i \<le> N \<and> ownB s i = Q)") prefer 2
  apply blast
  apply(subgoal_tac "\<forall>a b i.((a,b)\<in>set(q s) \<and> a\<le>i \<and> i<a+b) \<longrightarrow>ownB s i = Q") prefer 2 
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s)) \<longrightarrow>ownB s a = Q") prefer 2 
  apply (metis le_eq_less_or_eq less_add_same_cancel1)
  apply(subgoal_tac "i<length(q s) \<longrightarrow> (\<exists>a b.((a,b)\<in>set(q s) \<and> (a,b) = (q s!i)))") prefer 2
  apply (metis nth_mem prod.collapse)
  apply(subgoal_tac "i<length(q s) \<longrightarrow> ownB s (fst(q s!i)) = Q") prefer 2
  apply (metis fst_eqD)
  apply(subgoal_tac "hd(q s) = (q s!0) \<and> last(q s) = (q s!(length(q s)-1))") prefer 2
  apply (metis hd_conv_nth last_conv_nth)
  defer (*SMT*)
  apply(subgoal_tac "\<forall>a b i.((a,b)\<in>set(q s) \<and> a\<le>i \<and> i<a+b) \<longrightarrow> ownB s i = Q") prefer 2 
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply(subgoal_tac "hd(q s) \<in> set (q s)") prefer 2
  apply blast
  apply(subgoal_tac "\<forall>i.( fst(hd(q s))\<le>i \<and> i<fst(hd(q s))+snd(hd(q s))) \<longrightarrow> ownB s i = Q") prefer 2 
  apply presburger
  apply(subgoal_tac "\<forall>i.(ownB s i\<noteq>Q \<and> i>fst(hd(q s))) \<longrightarrow> i\<ge>end(last(q s))") prefer 2 
  apply (metis (no_types, lifting) end_simp le_eq_less_or_eq nat_le_linear)
  apply(subgoal_tac "end(last(q s))\<le>H s") prefer 2 
  apply (metis end_simp)
  apply (metis (no_types, lifting) F.distinct(19) add_lessD1 le_add_diff_inverse less_imp_le_nat nat_neq_iff)
  apply(subgoal_tac "hd(q s)\<noteq>last(q s)") prefer 2 
  apply (metis (no_types, lifting) One_nat_def Suc_lessD diff_less less_one zero_less_diff)
  apply(subgoal_tac "(\<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a < aa \<longrightarrow> a + b \<le> aa)") prefer 2
  apply blast
  apply(subgoal_tac "(\<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a + b > aa \<longrightarrow>a \<ge> aa )") prefer 2
  apply (metis (no_types, hide_lams) diff_is_0_eq' linorder_neqE_nat nat_le_linear zero_less_diff)
  apply(subgoal_tac "(\<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a + b > aa \<longrightarrow>a \<ge> aa )") prefer 2
  apply (metis (no_types, hide_lams) diff_is_0_eq' linorder_neqE_nat nat_le_linear zero_less_diff)
  apply(subgoal_tac "(\<forall>a b aa bb . ((a, b) \<in> set (q s) \<and>  (aa, bb) \<in> set (q s)) \<longrightarrow> a + b \<ge> aa + bb \<longrightarrow>a \<ge> aa )") prefer 2
  apply (metis (no_types, lifting) less_add_same_cancel1 nat_le_iff_add trans_less_add1)
  apply(subgoal_tac "(\<forall>a b aa bb . ((a, b) \<in> set (q s) \<and>  (aa, bb) \<in> set (q s)) \<longrightarrow> a <  aa \<longrightarrow> a + b \<le> aa + bb)") prefer 2
  apply (metis (no_types, lifting) trans_le_add1)
  by (metis (no_types, lifting) Suc_lessD diff_less less_one nat_less_le prod.collapse)

  
lemma R_idle_to_nidle_lemma_case_1_6_1_supp:
  "case_2 s\<Longrightarrow>q s\<noteq>[] \<Longrightarrow> fst(hd(q s)) = T s
\<Longrightarrow>H s = fst(last(q s))+snd(last(q s)) \<longrightarrow> (\<nexists>j.(j\<le>N \<and> ownB s j = W))"
  apply(simp add:case_2_def ) 
  apply(clarify) 
  by (metis F.distinct(5) F.distinct(7) F.distinct(9) diff_is_0_eq less_nat_zero_code linorder_neqE_nat zero_less_diff)

lemma R_idle_to_nidle_lemma_case_1_6_1_supp_2:
  "case_2 s\<Longrightarrow>q s\<noteq>[] \<Longrightarrow> fst(hd(q s)) = T s
\<Longrightarrow>H s \<noteq> fst(last(q s))+snd(last(q s)) \<longrightarrow> (H s =offset s + Data s (numEnqs s))"
  apply(simp add:case_2_def ) 
  apply(clarify) 
  by (metis le_add_diff_inverse le_neq_implies_less)
  
lemma pec_prelim_1:
" \<forall>i.  (i \<le> N \<and> ownB s i = Q) \<longrightarrow> (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) 
  \<Longrightarrow> 0\<le>N \<and> ownB s 0=Q \<Longrightarrow> (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s))\<and> 0\<in>x)"
  by (metis (no_types, lifting) mem_Collect_eq)


lemma pec_prelim_2:
" \<forall>i.  (i \<le> N \<and> ownB s i = Q) \<longrightarrow> (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) 
  \<Longrightarrow> 0\<le>N \<and> ownB s 0=Q \<Longrightarrow> (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s))\<and> 0\<in>x) \<Longrightarrow> \<exists>a b.((a,b)\<in>set(q s) \<and> a=0)"
  by fastforce




lemma pec_prelim_3:
" \<forall>i.  (i \<le> N \<and> ownB s i = Q) \<longrightarrow> (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) 
\<Longrightarrow> ownB s (fst(hd(q s)) + snd(hd(q s))) = Q \<and> (fst(hd(q s)) + snd(hd(q s)))\<le>N  
\<Longrightarrow> (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s))\<and> fst(hd(q s)) + snd(hd(q s))\<in>x) 
\<Longrightarrow> \<exists>a b.((a,b)\<in>set(q s) \<and> a\<le>fst(hd(q s)) + snd(hd(q s)) \<and> fst(hd(q s)) + snd(hd(q s))<a+b)" 
  by blast


lemma pec_prelim_4:
"Q_structure s \<Longrightarrow> length(q s)>1
\<Longrightarrow>
\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> i\<noteq>j \<and> fst(q s!j)<fst(q s!i))\<longrightarrow>fst(q s!j) + snd(q s!j) < fst(q s!i)+ snd(q s!i)"
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply clarify 
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow>(q s!i)\<in>set(q s)") prefer 2 
  apply (meson nth_mem)
  apply(subgoal_tac "\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> i\<noteq>j)\<longrightarrow>fst(q s!i)\<noteq>fst(q s!j)") prefer 2
  apply (metis less_nat_zero_code list.size(3))
  apply(subgoal_tac "(\<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a < aa \<longrightarrow> a + b \<le> aa)") prefer 2 
  apply (metis less_nat_zero_code list.size(3))
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s)) \<longrightarrow> b>0") prefer 2 
  apply (metis less_nat_zero_code list.size(3))
  apply(subgoal_tac "\<forall>a b aa ba. ((a, b) \<in> set (q s) \<and>  (aa, ba) \<in> set (q s) \<and> a < aa) \<longrightarrow> a + b < aa+ba") prefer 2
  apply (metis Nat.add_diff_assoc2 add_gr_0 zero_less_diff)
  apply(subgoal_tac "(i<length(q s) \<and> j<length(q s) \<and> i\<noteq>j \<and> fst(q s!j)<fst(q s!i)) 
\<longrightarrow> ((q s!i)\<in>set(q s) \<and> (q s!j)\<in>set(q s) \<and> fst(q s!j)<fst(q s!i))") prefer 2 
  apply presburger
  apply(subgoal_tac "(\<exists>a b aa ba.((a, b) \<in> set (q s) \<and>  (aa, ba) \<in> set (q s) \<and> a < aa) \<and> (q s!i) = (aa, ba) \<and> (q s!j) =(a,b))") prefer 2 
  apply (metis prod.collapse)
  apply(clarify)
  apply(subgoal_tac "a+b<aa+ba") prefer 2
  apply presburger
  apply(subgoal_tac "fst(q s!i) = aa") prefer 2
  apply (metis fst_conv)
  apply(subgoal_tac "fst(q s!j) = a") prefer 2
  apply (metis fst_conv)
  apply(subgoal_tac "snd(q s!j) = b") prefer 2
  apply (metis snd_conv)
  apply(subgoal_tac "snd(q s!i) = ba") prefer 2
  apply (metis snd_conv)
  by meson

lemma pec_prelim_5:
"Q_structure s \<Longrightarrow> length(q s)>1
\<Longrightarrow>
\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> i\<noteq>j )\<longrightarrow>fst(q s!j) + snd(q s!j) \<noteq> fst(q s!i)+ snd(q s!i)"
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply clarify apply(case_tac "fst(q s!i)<fst(q s!j)") 
  using pec_prelim_4 [where s=s]
  apply (metis diff_add_inverse diff_is_0_eq less_nat_zero_code list.size(3) nth_mem prod.collapse)
  using pec_prelim_4 [where s=s]
  apply(subgoal_tac "fst(q s!i)>fst(q s!j)") 
  apply (metis diff_add_inverse diff_is_0_eq less_nat_zero_code list.size(3) nth_mem prod.collapse)
  by (metis less_nat_zero_code linorder_neqE_nat list.size(3))


lemma pec_prelim_6:
"Q_structure s \<Longrightarrow> length(q s)>2
\<Longrightarrow>
\<forall>i j.(i<length(q s) \<and> j<length(q s) \<and> i\<noteq>j )\<longrightarrow>fst(q s!j) + snd(q s!j) \<noteq> fst(q s!i)+ snd(q s!i)"
  using pec_prelim_5 [where s=s]
  by (metis add_lessD1 nat_1_add_1)


lemma pec_prelim_7:
"Q_structure s \<Longrightarrow> length(q s)>2
\<Longrightarrow> fst(q s!1) = 0 \<Longrightarrow>
\<forall>i.(i<length(q s) \<and> i>1)\<longrightarrow>fst(q s!0) + snd(q s!0) \<noteq> fst(q s!i)"
  using pec_prelim_6 [where s=s] Q_lemmas Q_basic_lemmas
  by (smt (verit, ccfv_threshold) add.commute add_lessD1 add_less_same_cancel2 canonically_ordered_monoid_add_class.lessE diff_add_inverse end_simp linorder_neqE_nat list.size(3) not_add_less2)

lemma pec_prelim_8:
"Q_structure s \<Longrightarrow> 
\<forall>a b aa bb.((a,b)\<in>set(q s) \<and> (aa,bb)\<in>set(q s) \<and> a+b<aa+bb)\<longrightarrow>a+b\<le>aa"
  using Q_lemmas Q_basic_lemmas 
  by (smt (verit) Q_gap_lemmas_14 Q_gap_lemmas_15 end_simp fst_eqD length_pos_if_in_set snd_eqD)




  


lemma pec_prelim_9:
"(\<forall>a b. (a, b) \<in> set (q s) \<longrightarrow> a + b \<le> N) \<and>
    (\<forall>i. i < length (q s) \<and> 0 < i \<longrightarrow> fst (q s ! (i - Suc 0)) + snd (q s ! (i - Suc 0)) = fst (q s ! i) \<or> fst (q s ! i) = 0) \<and>
    (\<forall>i j. i < length (q s) \<and> j < length (q s) \<and> i \<noteq> j \<longrightarrow> fst (q s ! i) \<noteq> fst (q s ! j)) \<and>
    (\<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a < aa \<longrightarrow> a + b \<le> aa) \<and>
    (\<forall>a. (\<exists>b. (a, b) \<in> set (q s)) \<longrightarrow> a \<noteq> fst (last (q s)) + snd (last (q s))) \<and>
    (\<forall>a b. (a, b) \<in> set (q s) \<longrightarrow> 0 < b) \<and>
    (\<forall>i<length (q s). data_index s (q s ! i) = numDeqs s + i) \<and>
    (\<forall>i<length (q s). snd (q s ! i) = Data s (numDeqs s + i)) \<and>
    (\<forall>i<length (q s). ownD s (i + numDeqs s) = B) \<and> (\<forall>i\<le>N. \<forall>j\<le>N. data_index s (i, j) < n)
\<Longrightarrow> Q_structure s"
  by (simp add:Q_lemmas Q_basic_lemmas)

lemma pec_prelim_10:
"(\<forall>a b. (a, b) \<in> set (q s) \<longrightarrow> a + b \<le> N) \<and>
    (\<forall>i. i < length (q s) \<and> 0 < i \<longrightarrow> fst (q s ! (i - Suc 0)) + snd (q s ! (i - Suc 0)) = fst (q s ! i) \<or> fst (q s ! i) = 0) \<and>
    (\<forall>i j. i < length (q s) \<and> j < length (q s) \<and> i \<noteq> j \<longrightarrow> fst (q s ! i) \<noteq> fst (q s ! j)) \<and>
    (\<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a < aa \<longrightarrow> a + b \<le> aa) \<and>
    (\<forall>a. (\<exists>b. (a, b) \<in> set (q s)) \<longrightarrow> a \<noteq> fst (last (q s)) + snd (last (q s))) \<and>
    (\<forall>a b. (a, b) \<in> set (q s) \<longrightarrow> 0 < b) \<and>
    (\<forall>i<length (q s). data_index s (q s ! i) = numDeqs s + i) \<and>
    (\<forall>i<length (q s). snd (q s ! i) = Data s (numDeqs s + i)) \<and>
    (\<forall>i<length (q s). ownD s (i + numDeqs s) = B)
\<Longrightarrow> Q_structure s"
  by (simp add:Q_lemmas Q_basic_lemmas)



lemma pec_prelim_11:
"Q_structure s \<Longrightarrow> 
length(q s)>2 \<Longrightarrow> 
i<length(q s) \<Longrightarrow> 
j<length(q s)\<Longrightarrow> 
fst(q s!i) = 0 \<Longrightarrow>
i\<noteq>0 \<Longrightarrow> 
fst(q s!j) = fst(q s!0)+snd(q s!0) \<Longrightarrow>
j=1"
  apply(simp add: Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "Q_structure s") prefer 2 using pec_prelim_10 [where s=s]
  apply auto[1]
  apply (subgoal_tac "fst(q s!j)\<noteq>0") prefer 2 
  apply (metis add_is_0 bot_nat_0.not_eq_extremum length_0_conv not_numeral_less_zero nth_mem prod.collapse) 
  apply(subgoal_tac "\<forall>i.(i<length(q s) \<and> i>1)\<longrightarrow>fst(q s!0) + snd(q s!0) \<noteq> fst(q s!i)")
  prefer 2 using pec_prelim_7 [where s=s] 
  apply (metis One_nat_def Suc_1 Suc_lessD diff_is_0_eq' le_numeral_extra(4) less_numeral_extra(1) list.size(3) nat_neq_iff)
  apply(subgoal_tac "j\<noteq>i") prefer 2 
  apply blast
  apply(subgoal_tac "\<forall>i.(i<length(q s) \<and> fst(q s!0) + snd(q s!0) =fst(q s!i))\<longrightarrow>i\<le>1")
  prefer 2 
  apply (meson less_Suc_eq_le not_less_eq)
  apply(subgoal_tac "(i<length(q s) \<and> fst(q s!0) + snd(q s!0) =fst(q s!i))\<longrightarrow>i=1")
  prefer 2 
  apply presburger
  by (metis Suc_diff_1 bot_nat_0.not_eq_extremum diff_add_inverse diff_is_0_eq' diff_self_eq_0 length_0_conv nth_mem surjective_pairing)




lemma R_idle_to_nidle_lemma_case_1_6_1:
  "case_2 s\<Longrightarrow>con_assms s \<Longrightarrow> pcR s = idleR\<Longrightarrow>pre_R (pcR s) s
  \<Longrightarrow>s'=(s\<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
          numDeqs := Suc (numDeqs s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr>)
\<Longrightarrow>inv s \<Longrightarrow>q s\<noteq>[] \<Longrightarrow> fst(hd(q s)) = T s \<Longrightarrow> H s = fst(last(q s))+snd(last(q s))
\<Longrightarrow>case_2 s'"
  apply(subgoal_tac "T s\<noteq>0") prefer 2
  apply(simp add:case_2_def) 
  apply(subgoal_tac "Q_structure s") prefer 2 
  apply (metis RingBuffer_BD_latest_2.inv_def)
  apply (metis gr0I less_nat_zero_code)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "Q_structure s") prefer 2 using pec_prelim_9 [where s=s]
  apply blast
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:pre_R_def pre_dequeue_inv_def)
  apply(simp add:case_2_def ) 
  apply(clarify) 
  apply(intro conjI impI)
  apply (metis (no_types, lifting) le_antisym less_or_eq_imp_le list.set_sel(1) nat_neq_iff prod.collapse)
  apply(rule_tac ?x = "0" in exI)
  apply(rule_tac ?x = "H s" in exI)
  apply(intro conjI impI)  
  apply blast
  apply(rule_tac ?x = "H s" in exI)
  apply(intro conjI impI) 
  apply fastforce  
  apply(rule_tac ?x = "T s" in exI)
  apply(intro conjI impI) 
  apply(subgoal_tac "H s < T s") prefer 2
  apply linarith
  apply linarith
  apply(rule_tac ?x = "fst(hd(q s)) + snd(hd(q s))" in exI)
  apply(intro conjI impI)
  apply linarith
  apply(rule_tac ?x = "f" in exI)
  apply(intro conjI impI)  
  apply (metis (no_types, lifting) F.distinct(21) le_eq_less_or_eq linorder_neqE_nat)
  apply linarith 
  apply metis 
  apply (metis Suc_leI le_less_Suc_eq le_trans less_or_eq_imp_le not_less_eq not_less_eq_eq)
  apply (metis le_antisym less_irrefl_nat less_or_eq_imp_le)
  apply (metis Suc_leI not_less_eq_eq)
  apply (metis trans_less_add1)
  apply (metis diff_is_0_eq' le_add1 le_less_Suc_eq le_trans not_less_eq zero_less_diff)
  apply clarify
  apply(intro conjI impI)
  apply(subgoal_tac "ownB s i = Q") prefer 2 
  apply metis
  apply(subgoal_tac "j\<ge>f \<and> j\<le>N \<longrightarrow> ownB s j \<noteq>Q") prefer 2 
  apply (metis F.distinct(21) F.distinct(23) le_neq_implies_less)
  apply(subgoal_tac " T s + snd (hd (q s)) \<le>N") prefer 2 
  apply linarith
  apply(subgoal_tac " T s + snd (hd (q s)) \<le>f") prefer 2 
  apply (metis (no_types, lifting) F.distinct(21) le_eq_less_or_eq linorder_neqE_nat)
  apply(subgoal_tac "i < T s + snd (hd (q s))") prefer 2
  apply meson
  apply linarith
  apply metis
  apply metis
  apply fastforce
  apply fastforce
  apply fastforce
  using add_gr_0 apply presburger
  apply meson
  apply linarith
  apply force
  apply force
  apply force
  apply force
  apply force
  using diff_add_inverse apply presburger
  apply(intro iffI) prefer 2 
  apply (metis bot_nat_0.not_eq_extremum)
  apply(subgoal_tac "H s>0") prefer 2 
  using add_gr_0 apply presburger
  apply(subgoal_tac " \<forall>i.  (i \<le> N \<and> ownB s i = Q) \<longrightarrow> (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) ") prefer 2
  apply presburger
  apply(subgoal_tac "ownB s 0 = Q \<and> 0\<le>N") prefer 2
  apply (metis gr_zeroI zero_le)
  apply(subgoal_tac "(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> 0 \<in> x)") prefer 2        
  using pec_prelim_1 [where s=s]
  apply presburger  
  apply(subgoal_tac "\<exists>a b.((a,b)\<in>set(q s) \<and> a=0)") prefer 2 using pec_prelim_2 [where s=s]
  apply presburger
  apply(subgoal_tac "hd(q s) \<in> set(q s)") prefer 2
  apply (metis list.set_sel(1))
  apply(subgoal_tac "hd(q s) = q s!0") prefer 2
  apply (metis hd_conv_nth)
  apply(subgoal_tac "\<exists>j.(j<length(q s) \<and> fst(q s!j) = 0)") prefer 2 
  apply (metis (no_types, lifting) fst_eqD in_set_conv_nth)
  apply(subgoal_tac "fst(q s!j) = 0 \<longrightarrow> j\<noteq>0") prefer 2
  apply metis
  apply(subgoal_tac "length(q s)\<ge>2") prefer 2
  apply (metis (no_types, hide_lams) diff_is_0_eq length_0_conv less_2_cases_iff less_Suc0 neq0_conv zero_less_diff)
  apply linarith
  defer
  apply(subgoal_tac "ownB s (f) \<noteq> Q") prefer 2 
  apply (metis F.distinct(21) F.distinct(23) eq_imp_le le_neq_implies_less)
  apply(subgoal_tac "length(q s) > 1") prefer 2 
  apply (metis (no_types, lifting) One_nat_def Suc_lessI diff_Suc_1 hd_conv_nth last_conv_nth length_greater_0_conv not_add_less1)
  apply(subgoal_tac " \<forall>i.  (i \<le> N \<and> ownB s i = Q) \<longrightarrow> (\<exists>x. (\<exists>a b. x = {j. a \<le> j \<and> j < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) ") prefer 2
  apply presburger
  apply(subgoal_tac "\<forall>star b.((star,b)\<in>set(q s))\<longrightarrow>(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> star \<in> x)") prefer 2
  apply (metis (no_types, lifting) diff_add_inverse le_refl mem_Collect_eq zero_less_diff)
  apply(subgoal_tac "\<forall>star b.((star,b)\<in>set(q s))\<longrightarrow> (star \<le> N \<and> ownB s star = Q)")
  prefer 2 
  apply presburger
  apply(subgoal_tac "ownB s 0 = Q") prefer 2
  apply (metis bot_nat_0.extremum bot_nat_0.not_eq_extremum)
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>(\<exists>i.(i<length(q s) \<and> (a,b) = (q s!i)))") prefer 2 
  apply (metis in_set_conv_nth)
  apply(subgoal_tac "fst(q s!1) = fst(q s!0)+snd(q s!0) \<longrightarrow> ownB s f = Q") prefer 2 
  apply (metis hd_conv_nth nth_mem prod.collapse)
  apply(subgoal_tac "fst(q s!1) = fst(tl(q s)!0)") prefer 2
  apply (metis (no_types, lifting) One_nat_def Suc_leI diff_is_0_eq diffs0_imp_equal length_0_conv length_greater_0_conv length_tl less_not_refl3 nth_tl)
  apply(subgoal_tac "fst(q s!1) = fst(hd(tl(q s)))") prefer 2 
  apply (metis diff_is_0_eq' hd_conv_nth length_tl list.size(3) zero_less_diff)
  apply (metis (no_types, lifting) One_nat_def diff_Suc_1 zero_less_Suc)
  apply(subgoal_tac "tl(q s)\<noteq>[]")
  apply (metis last_tl)
  defer
  apply (metis bot_nat_0.not_eq_extremum)
  apply (metis add_cancel_right_right hd_in_set less_SucE less_add_Suc1 prod.exhaust_sel)
  apply (metis add_eq_self_zero list.set_sel(1) prod.collapse)
  apply(subgoal_tac " \<forall>i.  (i \<le> N \<and> ownB s i = Q) \<longrightarrow> (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) ") prefer 2
  apply presburger
  apply(subgoal_tac "ownB s (fst (hd (q s)) + snd (hd (q s))) = Q") prefer 2
  apply (metis le_add1 le_less_Suc_eq not_less_eq)
  apply(subgoal_tac "length(q s)>1") prefer 2 
  apply (metis (no_types, lifting) One_nat_def Suc_lessI diff_Suc_1 hd_conv_nth last_conv_nth length_greater_0_conv not_add_less1)
  apply(subgoal_tac "(hd (tl (q s))) = (q s!1) ") prefer 2
  apply (metis (no_types, lifting) One_nat_def hd_conv_nth length_tl lessI list.size(3) not_less_eq nth_tl zero_less_diff)
  apply(subgoal_tac "(hd (q s)) = (q s!0) ") prefer 2
  apply (metis hd_conv_nth)
  defer
  apply(subgoal_tac "ownB s 0 = Q") prefer 2
  apply (metis gr_zeroI zero_le)
  apply(subgoal_tac " \<forall>i.  (i \<le> N \<and> ownB s i = Q) \<longrightarrow> (\<exists>x. (\<exists>a b. x = {j. a \<le> j \<and> j < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) ") prefer 2
  apply presburger
  apply(subgoal_tac "\<forall>star b.((star,b)\<in>set(q s))\<longrightarrow>(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> star \<in> x)") prefer 2
  apply (metis (no_types, lifting) diff_add_inverse le_refl mem_Collect_eq zero_less_diff)
  apply(subgoal_tac "(\<exists>x. (\<exists>a b. x = {j. a \<le> j \<and> j < a + b} \<and> (a, b) \<in> set (q s)) \<and> 0 \<in> x)") prefer 2 
  using bot_nat_0.extremum apply presburger
  apply(subgoal_tac "\<exists>a b.((a,b)\<in>set(q s) \<and> a=0)") prefer 2 
  using \<open>\<lbrakk>\<forall>i. i \<le> N \<and> ownB s i = Q \<longrightarrow> (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x); 0 \<le> N \<and> ownB s 0 = Q; \<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> 0 \<in> x\<rbrakk> \<Longrightarrow> \<exists>a b. (a, b) \<in> set (q s) \<and> a = 0\<close> apply presburger
  apply(subgoal_tac "fst(hd(q s)) \<noteq> 0") prefer 2
  apply linarith
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>(\<exists>i.(i<length(q s) \<and> (a,b) = (q s!i)))") prefer 2 
  apply (metis in_set_conv_nth)
  apply(subgoal_tac "fst(q s!k) = 0 \<longrightarrow> k\<noteq>0") prefer 2 
  apply (metis hd_conv_nth)
  apply(subgoal_tac "length(q s)>1") prefer 2 
  apply (metis (no_types, lifting) One_nat_def Suc_lessI diff_Suc_1 hd_conv_nth last_conv_nth length_pos_if_in_set not_add_less1)
  apply (metis Suc_diff_Suc Zero_not_Suc length_0_conv length_tl)
  apply(subgoal_tac "\<not>(fst (hd (tl (q s))) \<noteq> fst (hd (q s)) + snd (hd (q s)))") 
  apply meson
  apply(subgoal_tac "fst (hd (tl (q s))) \<noteq> 0") 
  apply (metis (no_types, lifting) One_nat_def diff_Suc_1 less_one)
  apply(subgoal_tac "ownB s (fst (hd (q s)) + snd (hd (q s))) = Q") prefer 2 
  apply blast
  apply(subgoal_tac " \<forall>i.  (i \<le> N \<and> ownB s i = Q) \<longrightarrow> (\<exists>x. (\<exists>a b. x = {j. a \<le> j \<and> j < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) ") prefer 2
  apply presburger
  apply(subgoal_tac "fst (hd (q s)) + snd (hd (q s))\<le>N \<and> ownB s (fst (hd (q s)) + snd (hd (q s))) = Q")
  prefer 2 
  apply (metis Suc_le_lessD not_less_eq_eq)
  apply(subgoal_tac " (\<exists>x. (\<exists>a b. x = {j. a \<le> j \<and> j < a + b} \<and> (a, b) \<in> set (q s)) \<and> (fst (hd (q s)) + snd (hd (q s))) \<in> x) ") prefer 2
  apply presburger
  apply(subgoal_tac "\<exists>a b.((a,b)\<in>set(q s) \<and> a \<le> fst (hd (q s)) + snd (hd (q s)) \<and> fst (hd (q s)) + snd (hd (q s))<a+b)") prefer 2
  using pec_prelim_3 [where s=s] 
  apply presburger
  apply(subgoal_tac "ownB s 0 = Q \<and> 0\<le>N") prefer 2 
  apply (metis bot_nat_0.not_eq_extremum zero_le)
  apply clarify
  apply(subgoal_tac "ab+bb>fst(hd(q s)) + snd(hd(q s))") prefer 2
  apply meson
  apply(subgoal_tac "(fst(hd(q s)),snd(hd(q s))) \<in>set (q s)") prefer 2 
  apply (metis hd_in_set prod.collapse)
  apply(subgoal_tac "Q_structure s") prefer 2 
  apply blast
  apply(subgoal_tac "ab\<ge> fst(hd(q s)) + snd(hd(q s))") prefer 2
  using pec_prelim_8 [where s=s] 
  apply (metis (no_types, lifting))
  apply(subgoal_tac "fst(hd(q s)) > 0") prefer 2
  apply linarith
  apply(subgoal_tac "ab> 0") prefer 2
  apply linarith
  apply(subgoal_tac "\<exists>a b.((a,b)\<in>set(q s) \<and> a \<le> 0 \<and> 0<a+b)") prefer 2
  using pec_prelim_3 [where s=s] 
  apply (metis (no_types, lifting) \<open>\<lbrakk>\<forall>i. i \<le> N \<and> ownB s i = Q \<longrightarrow> (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x); 0 \<le> N \<and> ownB s 0 = Q\<rbrakk> \<Longrightarrow> \<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> 0 \<in> x\<close> mem_Collect_eq)
  apply(clarify)
  apply(subgoal_tac "(aa,ba)\<noteq>(hd(q s))") prefer 2
  apply (metis Pair_inject less_irrefl_nat prod.collapse)
  apply(subgoal_tac "(0,bc)\<noteq>(hd(q s))") prefer 2 
  apply (metis fst_conv)
  apply(subgoal_tac "(aa,ba)\<noteq>(0,bc)") prefer 2 
  apply (metis (no_types, lifting) \<open>Q_structure s \<Longrightarrow> \<forall>a b aa bb. (a, b) \<in> set (q s) \<and> (aa, bb) \<in> set (q s) \<and> a + b < aa + bb \<longrightarrow> a + b \<le> aa\<close> add_eq_0_iff_both_eq_0 le_zero_eq prod.inject)
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>(\<exists>i.(i<length(q s) \<and> (q s!i) = (a,b)))") prefer 2
  apply (metis in_set_conv_nth)
  apply(subgoal_tac "\<exists>i.(i<length(q s) \<and> (aa,ba) =(q s!i))") prefer 2
  apply metis
  apply(subgoal_tac "\<exists>i.(i<length(q s) \<and> (0,bc) =(q s!i))") prefer 2
  apply metis
  apply(subgoal_tac "(hd(q s)) = (q s!0)") prefer 2
  apply force
  apply(subgoal_tac "(aa,ba) =(q s!second) \<and> (0,bc) =(q s!third)\<longrightarrow> second\<noteq>third") prefer 2
  apply metis
  apply(subgoal_tac "(aa,ba) =(q s!second) \<and> (0,bc) =(q s!third) \<longrightarrow> second\<noteq>0 \<and> third\<noteq>0") prefer 2
  apply metis
  apply (subgoal_tac "length(q s) > 2") prefer 2 
  apply (metis Suc_1 Suc_lessI less_2_cases_iff)
  apply(subgoal_tac "fst(hd(tl(q s))) = 0 \<longrightarrow> False") 
  apply fastforce
  apply(subgoal_tac "Q_structure s") prefer 2 
  apply meson
  apply(subgoal_tac "\<exists>ass.(ass <length(q s) \<and> (q s!ass) = (0,bc) \<and> fst(q s!ass) = 0)") prefer 2 
  apply (metis prod.collapse prod.inject)
  apply(subgoal_tac "\<exists>a b.((a,b)\<in>set(q s) \<and> a = fst(hd(q s)) + snd(hd(q s)))") prefer 2
  apply (metis le_antisym)
  apply clarify 
  apply(subgoal_tac "\<exists>tru.(tru<length(q s) \<and> (fst (hd (q s)) + snd (hd (q s)), bd) =(q s!tru))")
  prefer 2 
  apply metis
  apply clarify
  apply(subgoal_tac "ass<length(q s)") prefer 2 
  apply blast
  apply(subgoal_tac "tru<length(q s)") prefer 2 
  apply blast
  apply(subgoal_tac "ass\<noteq>0") prefer 2 
  apply metis
  apply(subgoal_tac " fst(q s!ass) = 0") prefer 2 
  apply meson
  apply(subgoal_tac "fst(q s!tru) = fst(q s!0)+snd(q s!0) ") prefer 2 
  apply (metis prod.collapse prod.inject)
  apply(subgoal_tac "tru = 1") 
  apply (metis add_is_0)
  using pec_prelim_11 [where s=s and i=ass and j=tru] 
  proof -
  fix a :: nat and b :: nat and c :: nat and d :: nat and e :: nat and f :: nat and x :: "nat set" and aa :: nat and ba :: nat and ab :: nat and bb :: nat and ac :: nat and bc :: nat and i :: nat and ia :: nat and assa :: nat and ad :: nat and bd :: nat and trua :: nat
  assume a1: "Q_structure s"
  assume a2: "2 < length (q s)"
  assume a3: "assa < length (q s)"
  assume a4: "fst (q s ! assa) = 0"
  assume a5: "trua < length (q s)"
  assume a6: "assa \<noteq> 0"
  assume "fst (q s ! trua) = fst (q s ! 0) + snd (q s ! 0)"
  then show "trua = 1"
    using a6 a5 a4 a3 a2 a1 by (meson pec_prelim_11)
  next
  qed



lemma str_pec_1:
  "Q_structure s \<Longrightarrow> fst(hd(q s)) = 0 \<Longrightarrow> length(q s)>1
\<Longrightarrow> (i>0 \<and> i<length(q s))\<longrightarrow>fst(q s!i)\<ge>fst(q s!0)+snd(q s!0)"
  apply(simp add:Q_lemmas Q_basic_lemmas)
  by (metis hd_conv_nth le_add2 le_add_same_cancel2 le_eq_less_or_eq less_nat_zero_code list.size(3) nth_mem prod.collapse)

lemma str_pec_2:
  "Q_structure s \<Longrightarrow> fst(hd(q s)) = 0 \<Longrightarrow> length(q s)>1 \<Longrightarrow> k=(length(q s) -1)
\<Longrightarrow> fst(q s!k)\<ge>fst(q s!0)+snd(q s!0)"
  apply(simp add:Q_lemmas Q_basic_lemmas) 
  apply(subgoal_tac "k>0") prefer 2 
  apply linarith
  apply(subgoal_tac "k<length(q s)") prefer 2 
   apply linarith
  apply(subgoal_tac "(k>0 \<and> k<length(q s))\<longrightarrow>fst(q s!k)\<ge>fst(q s!0)+snd(q s!0)")
  using str_pec_1 [where s=s and i=k] 
  apply meson
  apply(subgoal_tac "(k>0 \<and> k<length(q s))") prefer 2 
  apply blast
  by (metis hd_conv_nth less_nat_zero_code list.size(3) nat_neq_iff nth_mem prod.collapse)

lemma str_pec_3:
  "Q_structure s \<Longrightarrow> fst(hd(q s)) = 0 \<Longrightarrow> length(q s)>1 
\<Longrightarrow> fst(q s!(length(q s) -1))\<ge>fst(q s!0)+snd(q s!0)"
  apply(simp add:Q_lemmas Q_basic_lemmas) 
  apply(subgoal_tac "fst(hd(q s)) = fst(q s!0)") prefer 2
  apply (metis Suc_lessD head_q0)
  by (metis diff_less lessI less_nat_zero_code list.size(3) nat_neq_iff nth_mem prod.collapse zero_less_diff)
  

lemma str_pec_4:
  "Q_structure s \<Longrightarrow> fst(hd(q s)) = 0 \<Longrightarrow> length(q s)>1 
\<Longrightarrow> fst(last(q s))\<ge>fst(hd(q s))+snd(hd(q s))"
  apply(subgoal_tac "fst(q s!(length(q s) -1))\<ge>fst(q s!0)+snd(q s!0)") prefer 2
  using str_pec_3 [where s=s]
  apply blast
  apply(simp add:Q_lemmas Q_basic_lemmas) 
  apply(subgoal_tac "hd(q s) = q s!0") prefer 2
  apply (metis Suc_lessD head_q0)
  apply(subgoal_tac "last(q s) = q s!(length(q s) -1)") prefer 2
  apply (metis last_conv_nth less_nat_zero_code list.size(3))
  by (metis One_nat_def plus_nat.add_0)
  

lemma str_pec_5:
  "Q_structure s \<Longrightarrow> fst(hd(q s)) = 0 \<Longrightarrow> length(q s)>1 
\<Longrightarrow> snd(last(q s))+fst(last(q s))>fst(hd(q s))+snd(hd(q s))"
  apply(subgoal_tac "fst(last(q s))\<ge>fst(hd(q s))+snd(hd(q s))") prefer 2
  using str_pec_4 [where s=s]
  apply blast 
  apply(simp add:Q_lemmas Q_basic_lemmas) apply(subgoal_tac "snd(last(q s))>0") prefer 2 
  apply (metis last_in_set less_nat_zero_code list.size(3) prod.collapse)
  apply(subgoal_tac "hd(q s) = q s!0") prefer 2
  apply (metis Suc_lessD head_q0)
  apply(subgoal_tac "last(q s) = q s!(length(q s) -1)") prefer 2
  apply (metis last_conv_nth less_nat_zero_code list.size(3)) 
  by linarith


lemma R_idle_to_nidle_lemma_case_1_6_2:
  "case_2 s\<Longrightarrow>con_assms s \<Longrightarrow> pcR s = idleR\<Longrightarrow>pre_R (pcR s) s
  \<Longrightarrow>s'=(s\<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
          numDeqs := Suc (numDeqs s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr>)
\<Longrightarrow>inv s \<Longrightarrow>q s\<noteq>[] \<Longrightarrow> fst(hd(q s)) \<noteq> T s \<Longrightarrow> H s \<noteq> fst(last(q s))+snd(last(q s))
\<Longrightarrow>case_2 s'"
  apply(subgoal_tac "T s\<noteq>0") prefer 2
  apply(simp add:case_2_def) 
  apply(subgoal_tac "Q_structure s") prefer 2 
  apply (metis RingBuffer_BD_latest_2.inv_def)
  apply (metis gr0I less_nat_zero_code)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "Q_structure s") prefer 2 using pec_prelim_9 [where s=s]
  apply blast
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:pre_R_def pre_dequeue_inv_def)
  apply(simp add:case_2_def ) 
  apply(clarify) 
  apply(intro conjI impI)
  apply (metis (no_types, lifting) le_antisym less_or_eq_imp_le list.set_sel(1) nat_neq_iff prod.collapse)
  apply(rule_tac ?x = "fst (hd (q s))+snd(hd(q s))" in exI)
  apply(rule_tac ?x = "fst (last (q s)) + snd (last (q s))" in exI)
  apply(intro conjI impI)
  apply (metis (no_types, lifting) F.distinct(3) bot_nat_0.not_eq_extremum diff_diff_cancel diff_is_0_eq diff_is_0_eq' eq_imp_le le_antisym linorder_neqE_nat zero_less_diff)
  apply(rule_tac ?x = "H s" in exI)
  apply(intro conjI impI) 
  apply (metis le_neq_implies_less)
  apply(rule_tac ?x = "T s" in exI)
  apply(intro conjI impI) 
  apply linarith
  apply(rule_tac ?x = "T s" in exI)
  apply(intro conjI impI) 
  apply linarith
  apply(rule_tac ?x = "T s" in exI)
  apply(intro conjI impI) 
  apply linarith
  apply linarith 
  apply (metis bot_nat_0.extremum le_neq_implies_less)
  apply (metis Suc_leI le_add1 le_neq_implies_less le_trans not_less_eq_eq) 
  apply (metis (no_types, lifting) F.distinct(3) le_neq_implies_less)
  apply (metis (no_types, hide_lams) F.distinct(19))
  apply (metis le_neq_implies_less)
  apply (metis Suc_diff_Suc Zero_not_Suc diff_is_0_eq')
  apply (metis (no_types, hide_lams) F.distinct(21) nat_less_le)
  apply blast
  apply blast
  apply fastforce
  apply fastforce
  apply blast
  apply blast
  apply blast 
  apply (metis nat_less_le)
  apply (metis nat_less_le)
  apply (metis le_neq_implies_less)
  apply (metis add_cancel_right_left le_neq_implies_less)
  apply (metis le_neq_implies_less)
  apply (metis le_neq_implies_less)
  defer 
  apply fastforce
  defer defer 
  apply force
  apply (metis add_cancel_right_left le_neq_implies_less list.set_sel(1) prod.collapse)
  apply (metis add_cancel_right_left le_neq_implies_less list.set_sel(1) prod.collapse)
  apply(intro iffI)
  prefer 2 
  apply(subgoal_tac "hd(q s) = q s!0") prefer 2
  apply (metis hd_conv_nth)
  apply(subgoal_tac "last(q s) = q s!(length(q s) -1 ) ") prefer 2 
  apply (metis last_conv_nth)
  apply(subgoal_tac "last(q s) \<noteq> hd(q s) \<longrightarrow> length(q s)>1") prefer 2 
  apply (metis One_nat_def)
  using str_pec_5 [where s=s] 
  apply (metis (no_types, hide_lams) One_nat_def add.commute nat_less_le)
  apply(subgoal_tac "fst (hd (q s)) + snd (hd (q s)) < fst (last (q s)) + snd (last (q s))") prefer 2
  apply force
  apply(subgoal_tac "hd(q s) = q s!0") prefer 2
  apply (metis hd_conv_nth)
  apply(subgoal_tac "last(q s) = q s!(length(q s) -1 ) ") prefer 2 
  apply (metis last_conv_nth)
  apply (metis (no_types, lifting) One_nat_def Suc_lessI diff_self_eq_0 length_greater_0_conv less_not_refl2)
  apply(subgoal_tac "hd(q s) = q s!0") prefer 2
  apply (metis hd_conv_nth)
  apply(subgoal_tac "hd(tl(q s)) = q s!1") prefer 2
  apply (metis (no_types, lifting) One_nat_def hd_conv_nth last_conv_nth length_greater_0_conv length_tl list.size(3) nat_neq_iff nth_tl)
  apply(subgoal_tac "fst(q s!0) = 0") prefer 2 
  apply (metis le_neq_implies_less)
  apply(subgoal_tac "fst (hd (q s)) + snd (hd (q s)) = fst(q s!0) + snd(q s!0)") prefer 2 
  apply presburger
  apply(subgoal_tac "i < length (q s) \<and> j < length (q s) \<and> i \<noteq> j \<longrightarrow> fst (q s ! i) \<noteq> fst (q s ! j)") prefer 2
  apply (metis (no_types, lifting))
  apply(subgoal_tac "length(q s)>1") prefer 2 
  apply (metis (no_types, lifting) One_nat_def Suc_lessI diff_add_inverse last_conv_nth length_greater_0_conv nat_neq_iff plus_1_eq_Suc)
  apply(subgoal_tac "fst(q s!0) \<noteq> fst(q s!1)") prefer 2 
  apply (metis (no_types, hide_lams) bot_nat_0.not_eq_extremum length_greater_0_conv less_one)
  apply (metis (no_types, hide_lams) Suc_diff_1 diff_self_eq_0 less_one)
  apply(subgoal_tac "last(q s) = q s!(length(q s)-1)") prefer 2 
  apply (metis last_conv_nth)
  apply(subgoal_tac "length(tl(q s)) = length(q s)-1") prefer 2
  apply (metis length_tl)
  apply(subgoal_tac "last(tl(q s)) = (tl(q s)!(length(tl(q s)) -1))") prefer 2 
  apply (metis (no_types, lifting) hd_conv_nth last_conv_nth length_0_conv less_not_refl2)
  apply(subgoal_tac "last(tl(q s)) = (tl(q s)!(length(q s) -2))") prefer 2 
  apply (metis Suc_1 diff_Suc_eq_diff_pred)
  by (metis (no_types, hide_lams) hd_conv_nth last_tl length_0_conv nat_less_le)








lemma R_idle_to_nidle_lemma_case_1_6_3:
  "case_2 s\<Longrightarrow>con_assms s \<Longrightarrow> pcR s = idleR\<Longrightarrow>pre_R (pcR s) s
  \<Longrightarrow>s'=(s\<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
          numDeqs := Suc (numDeqs s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr>)
\<Longrightarrow>inv s \<Longrightarrow>q s\<noteq>[] \<Longrightarrow> fst(hd(q s)) = T s \<Longrightarrow> H s \<noteq> fst(last(q s))+snd(last(q s))
\<Longrightarrow>case_2 s'"
  apply(subgoal_tac "T s\<noteq>0") prefer 2
  apply(simp add:case_2_def) 
  apply(subgoal_tac "Q_structure s") prefer 2 
  apply (metis RingBuffer_BD_latest_2.inv_def)
  apply (metis gr0I less_nat_zero_code)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "Q_structure s") prefer 2 using pec_prelim_9 [where s=s]
  apply blast
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:pre_R_def pre_dequeue_inv_def)
  apply(simp add:case_2_def ) 
  apply(clarify) 
  apply(intro conjI impI)
  apply (metis (no_types, lifting) le_antisym less_or_eq_imp_le list.set_sel(1) nat_neq_iff prod.collapse)
  apply(rule_tac ?x = "0" in exI)
  apply(rule_tac ?x = "offset s" in exI)
  apply(intro conjI impI)  
  apply blast
  apply(rule_tac ?x = "H s" in exI)
  apply(intro conjI impI) 
  apply (metis nat_less_le)
  apply(rule_tac ?x = "T s" in exI)
  apply(intro conjI impI) 
  apply(subgoal_tac "H s < T s") prefer 2
  apply linarith
  apply linarith
  apply(rule_tac ?x = "fst(hd(q s)) + snd(hd(q s))" in exI)
  apply(intro conjI impI)
  apply linarith
  apply(rule_tac ?x = "f" in exI)
  apply(intro conjI impI)  
  apply (metis (no_types, lifting) F.distinct(21) le_eq_less_or_eq linorder_neqE_nat)
  apply linarith 
  apply metis 
  apply (metis Suc_leI le_less_Suc_eq le_trans less_or_eq_imp_le not_less_eq not_less_eq_eq) 
  apply (metis F.distinct(3) bot_nat_0.not_eq_extremum le_neq_implies_less)
  apply (metis Suc_leI not_less_eq_eq)
  apply (metis trans_less_add1)
  apply (metis diff_is_0_eq' le_add1 le_less_Suc_eq le_trans not_less_eq zero_less_diff)
  apply clarify
  apply(intro conjI impI)
  apply(subgoal_tac "ownB s i = Q") prefer 2 
  apply metis
  apply(subgoal_tac "j\<ge>f \<and> j\<le>N \<longrightarrow> ownB s j \<noteq>Q") prefer 2 
  apply (metis F.distinct(21) F.distinct(23) le_neq_implies_less)
  apply(subgoal_tac " T s + snd (hd (q s)) \<le>N") prefer 2 
  apply linarith
  apply(subgoal_tac " T s + snd (hd (q s)) \<le>f") prefer 2 
  apply (metis (no_types, lifting) F.distinct(21) le_eq_less_or_eq linorder_neqE_nat)
  apply(subgoal_tac "i < T s + snd (hd (q s))") prefer 2
  apply meson
  apply linarith
  apply metis
  apply metis
  apply fastforce
  apply fastforce
  apply fastforce
  using add_gr_0 apply presburger
  apply meson
  apply linarith
  apply force 
  apply (metis nat_less_le)
  apply force
  apply force
  apply force
  using diff_add_inverse apply presburger
  apply(intro iffI) prefer 2 
  apply(subgoal_tac "(fst(q s!1) = fst(q s!0)+snd(q s!0)) \<or> fst(q s!1) =0") prefer 2 
  apply (metis (no_types, lifting) One_nat_def diff_Suc_1 less_one)
  apply(subgoal_tac "(q s!0) =hd(q s)") prefer 2
  apply (metis hd_conv_nth)
  apply(subgoal_tac "(q s!1) =hd(tl(q s))") prefer 2
  apply (metis (no_types, lifting) One_nat_def hd_conv_nth length_tl lessI list.size(3) not_less_eq nth_tl zero_less_diff)
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)") prefer 2
  apply presburger
  apply(subgoal_tac "(q s!1)\<in>set(q s)") prefer 2 
  apply (metis One_nat_def nth_mem)
  apply(subgoal_tac "(q s!1) = (sta,leng) \<longrightarrow> (sta,leng)\<in>set(q s)") prefer 2 
  apply metis
  apply(case_tac "fst(q s!1) = 0") prefer 2 
  apply (metis (no_types, lifting) F.distinct(21) le_eq_less_or_eq linorder_neqE_nat prod.collapse)
  apply(subgoal_tac "0<offset s") 
  apply meson
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)") prefer 2
  apply presburger
  apply(subgoal_tac "\<forall>i. (\<exists>x. ( x = {i. fst(hd(tl(q s))) \<le> i \<and> i < fst(hd(tl(q s))) + snd(hd(tl(q s)))} ) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)") prefer 2
  apply(subgoal_tac "(fst(hd(tl(q s))),snd(hd(tl(q s))))\<in>set(q s)") prefer 2 
  apply (metis prod.collapse)
  apply (metis (no_types, lifting) mem_Collect_eq) defer (*the isar*)
  apply(case_tac "0<offset s") 
  apply(subgoal_tac "\<exists>i.(fst(q s!i) =0 \<and> i<length(q s))") 
  apply (metis Suc_lessI hd_conv_nth length_greater_0_conv less_Suc0)
  apply(subgoal_tac "ownB s 0 = Q") prefer 2 
  apply (metis gr_zeroI zero_le)
  apply(subgoal_tac "\<forall>i. (i \<le> N \<and> ownB s i = Q)\<longrightarrow> (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) ")
  prefer 2 
  apply presburger
  apply(subgoal_tac "(0 \<le> N \<and> ownB s 0 = Q)") prefer 2
  apply blast
  apply(subgoal_tac "(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> 0 \<in> x)") prefer 2
  apply presburger
  apply(subgoal_tac "\<exists>sta leng.((sta,leng)\<in>set(q s) \<and> sta=0)") prefer 2 
  apply (metis gr_implies_not_zero mem_Collect_eq nat_less_le)
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(q s) \<longrightarrow>(\<exists>i.(i<length(q s) \<and> q s!i=(a,b)))") prefer 2 
  apply (metis in_set_conv_nth)
  apply clarify
  apply(subgoal_tac "k<length(q s) \<and> (q s!k) = (0,leng) \<longrightarrow> k\<noteq>0") prefer 2
  apply (metis fst_conv hd_conv_nth)
  apply (metis fst_eqD)
  apply(subgoal_tac "fst (hd (q s)) + snd (hd (q s)) < f") prefer 2 
  apply meson
  apply(subgoal_tac "i\<ge>fst (hd (q s)) + snd (hd (q s)) \<and> i<f \<longrightarrow> ownB s i=Q") prefer 2 
  apply (metis add_leD1 le_eq_less_or_eq)
  apply(subgoal_tac "\<forall>i. (i \<le> N \<and> ownB s i = Q)\<longrightarrow> (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) ")
  prefer 2 
  apply presburger
  apply(subgoal_tac "fst (hd (q s)) + snd (hd (q s))\<le>N \<and> ownB s (fst (hd (q s)) + snd (hd (q s))) = Q") prefer 2
  apply (metis Suc_le_lessD le_add1 le_neq_implies_less not_less_eq_eq)
  apply(subgoal_tac "\<exists>a b.((a,b)\<in>set(q s) \<and> a\<le>fst (hd (q s)) + snd (hd (q s)) \<and> fst (hd (q s)) + snd (hd (q s))<a+b)")
  prefer 2 
  using pec_prelim_3 [where s=s ]
  apply presburger apply clarify
  apply(subgoal_tac "\<exists>i.(i<length(q s) \<and> q s!i = (aa,ba))") prefer 2 
  apply (metis in_set_conv_nth)
  apply(subgoal_tac "aa\<noteq>fst(hd(q s))") prefer 2 
  apply (metis (no_types, lifting) fst_eqD hd_conv_nth length_pos_if_in_set nat_neq_iff snd_eqD)
  apply clarify
  apply(subgoal_tac "ia\<noteq>0") prefer 2 
  apply (metis fst_eqD hd_conv_nth)
  apply linarith
  apply(subgoal_tac "hd(q s) = q s!0") prefer 2 
  apply (metis hd_conv_nth)
  apply(subgoal_tac "hd(tl(q s)) = q s!1") prefer 2 
  apply (metis (no_types, lifting) One_nat_def diff_is_0_eq' hd_conv_nth last_conv_nth le_add1 le_add_diff_inverse2 le_less_Suc_eq le_trans length_greater_0_conv length_tl less_or_eq_imp_le list.size(3) not_less_eq nth_tl)
  apply(subgoal_tac "fst(hd(tl(q s))) = fst(q s!1)") prefer 2
  apply presburger
  apply(case_tac "b=0")
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)")
  prefer 2 
  apply presburger
  apply(subgoal_tac "ownB s 0\<noteq>Q") prefer 2 
  apply (metis F.distinct(3))
  apply(subgoal_tac "i<fst(q s!0) \<longrightarrow> ownB s i\<noteq>Q") prefer 2 
  apply (metis (no_types, hide_lams) F.distinct(19) bot_nat_0.extremum diff_is_0_eq' linorder_neqE_nat nat_le_linear zero_less_diff)
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>(\<exists>x.(x = {i. a\<le>i \<and> i < a + b} \<and> a\<in>x))") prefer 2
  apply (metis Nat.add_0_right le_refl mem_Collect_eq nat_add_left_cancel_less)
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s)) \<longrightarrow> ownB s a = Q") prefer 2 
  apply (metis (no_types, lifting))
  apply(subgoal_tac "length(q s)>1") prefer 2 
  apply (metis One_nat_def Suc_lessI diff_Suc_1 last_conv_nth length_greater_0_conv nat_neq_iff)
  apply(subgoal_tac "\<nexists>a b.((a,b)\<in>set(q s) \<and> a=0)") prefer 2
  apply metis
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(q s) \<longrightarrow>(\<exists>i.(i<length(q s) \<and> q s!i = (a,b)))")
  prefer 2 
  apply (metis in_set_conv_nth)
  apply(subgoal_tac "fst(q s!1)\<noteq>0") prefer 2
  apply (metis nth_mem prod.collapse)
  apply (metis (no_types, lifting) One_nat_def diff_Suc_1 less_one)
  apply(subgoal_tac "\<forall>i.  (i \<le> N \<and> ownB s i = Q)\<longrightarrow>(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) ")
  prefer 2 
  apply presburger
  apply(subgoal_tac "ownB s 0 = Q \<and> 0\<le>N") prefer 2
  apply (metis gr_zeroI zero_le)
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)")
  prefer 2 
  apply presburger
  apply(subgoal_tac "(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> 0 \<in> x)") prefer 2 
  apply presburger
  apply(subgoal_tac "\<exists>a b.((a,b)\<in>set(q s) \<and> a=0)") prefer 2
  using pec_prelim_2 [where s=s] 
  apply presburger
  apply clarify
  apply(subgoal_tac "ownB s (fst (hd (q s)) + snd (hd (q s))) = Q \<and> fst (hd (q s)) + snd (hd (q s))\<le>N") prefer 2 
  apply (metis Suc_le_lessD le_add1 le_less_Suc_eq not_less_eq_eq)
  apply(subgoal_tac "(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> fst (hd (q s)) + snd (hd (q s)) \<in> x)") prefer 2 
  apply presburger
  apply(subgoal_tac "\<exists>a b.(a\<le>fst (hd (q s)) + snd (hd (q s)) \<and> fst (hd (q s)) + snd (hd (q s))<a+b \<and> (a,b)\<in>set(q s))") prefer 2
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply clarify
  apply(subgoal_tac "\<exists>ass. (ass<length(q s) \<and> q s!ass = (0,ba))") prefer 2 
  apply (metis in_set_conv_nth) 
  apply(subgoal_tac "\<exists>tru. (tru<length(q s) \<and> q s!tru = (ad,bd))") prefer 2 
  apply (metis in_set_conv_nth)
  apply(clarify)
  apply(subgoal_tac "ad = fst(hd(q s))+snd(hd(q s))") prefer 2
  apply (metis (no_types, lifting) hd_in_set le_antisym pec_prelim_8 prod.collapse)
  apply(subgoal_tac "ad\<noteq>0") prefer 2
  apply linarith
  apply(subgoal_tac "ass\<noteq>tru") prefer 2
  apply (metis fst_conv)
  apply(subgoal_tac "ass\<noteq>0") prefer 2 
  apply (metis fst_conv)
  apply(subgoal_tac "tru\<noteq>0") prefer 2
  apply (metis fst_conv less_irrefl_nat snd_conv)
  apply(subgoal_tac "length(q s)>2") prefer 2
  using Nat.lessE Suc_1 Suc_diff_1 Suc_lessI bot_nat_0.not_eq_extremum apply linarith
  apply(subgoal_tac "Q_structure s") prefer 2 apply presburger 
  apply(subgoal_tac "fst(q s!ass) = 0") prefer 2
  apply (metis prod.collapse prod.inject)
  apply(subgoal_tac "fst(q s!tru) = fst(q s!0) + snd(q s!0)") prefer 2 
  apply (metis prod.collapse prod.inject)
  apply(subgoal_tac "ass<length(q s) \<and> tru<length(q s)") prefer 2 
  apply blast
  apply(subgoal_tac "tru=1") prefer 2   
  defer (*another ISAR*) using pec_prelim_11 [where s=s and i=ass and j=tru]
  apply metis
  apply(subgoal_tac "length(q s)>1") prefer 2 
  apply (metis (no_types, lifting) One_nat_def Suc_lessI add_leD1 diff_Suc_1 hd_conv_nth last_conv_nth le_antisym le_neq_implies_less length_greater_0_conv less_or_eq_imp_le)
  apply(subgoal_tac "ownB s (fst(hd(q s))+snd(hd(q s))) \<noteq>Q") prefer 2 
  apply (metis F.distinct(21) F.distinct(23) eq_imp_le le_neq_implies_less)
  apply(subgoal_tac "\<forall>i.  (i \<le> N \<and> ownB s i = Q)\<longrightarrow>(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) ")
  prefer 2 
  apply presburger
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)")
  prefer 2 
  apply presburger
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>(\<exists>x.(x = {i. a\<le>i \<and> i < a + b} \<and> a\<in>x))") prefer 2
  apply (metis Nat.add_0_right le_refl mem_Collect_eq nat_add_left_cancel_less)
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s)) \<longrightarrow> ownB s a = Q") prefer 2 
  apply (metis (no_types, lifting))
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(tl(q s))\<longrightarrow>(a,b)\<in>set(q s)") prefer 2
  apply (metis list.set_sel(2))
  apply(subgoal_tac "hd(tl(q s))\<in>set(tl(q s))") prefer 2 
  apply (metis diff_is_0_eq' hd_in_set length_tl list.size(3) zero_less_diff)
  apply(subgoal_tac "hd(tl(q s)) \<in>set (q s)") prefer 2
  apply (metis list.set_sel(2))
  apply(subgoal_tac "ownB s (fst(hd(tl(q s)))) = Q") prefer 2 
  apply (metis prod.collapse)
  apply(subgoal_tac "ownB s (fst(hd(q s))+snd(hd(q s))) \<noteq>Q") prefer 2
  apply blast
  apply(subgoal_tac "hd(q s) = q s!0") prefer 2
  apply (metis hd_conv_nth)
  apply(subgoal_tac "hd(tl(q s)) = q s!1") prefer 2 
  apply (metis One_nat_def hd_conv_nth length_greater_0_conv length_pos_if_in_set nth_tl)
  apply(subgoal_tac "fst(hd(tl(q s)))\<noteq>fst(hd(q s))+snd(hd(q s))") prefer 2
  apply metis
  apply (metis (no_types, lifting) One_nat_def diff_Suc_1 less_one)
  apply(subgoal_tac "fst(last(q s)) + snd(last(q s)) = offset s") prefer 2
  apply (metis nat_less_le)
  apply(subgoal_tac "0<b") prefer 2 
  apply (metis bot_nat_0.not_eq_extremum)
  apply(subgoal_tac "\<forall>i.  (i \<le> N \<and> ownB s i = Q)\<longrightarrow>(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) ")
  prefer 2 
  apply presburger
  apply(subgoal_tac "ownB s 0 = Q \<and> 0\<le>N") prefer 2
  apply (metis gr_zeroI zero_le)
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)")
  prefer 2 
  apply presburger
  apply(subgoal_tac "(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> 0 \<in> x)") prefer 2 
  apply presburger
  apply(subgoal_tac "\<exists>a b.((a,b)\<in>set(q s) \<and> a=0)") prefer 2
  using pec_prelim_2 [where s=s] 
  apply presburger
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>(\<exists>i.(i<length(q s) \<and> (a,b) = q s!i))") prefer 2
  apply (metis in_set_conv_nth)
  apply(subgoal_tac "length(q s)>1") prefer 2
  apply (metis One_nat_def Suc_lessI add_leD1 diff_Suc_1 hd_conv_nth last_conv_nth le_antisym length_pos_if_in_set less_or_eq_imp_le nat_neq_iff)
  apply(subgoal_tac "last(q s) = q s!(length(q s)-1)") prefer 2
  apply (metis last_conv_nth)
  apply(subgoal_tac "length(tl(q s)) = length(q s)-1") prefer 2 
  apply (metis length_tl)
  apply(subgoal_tac "last(tl(q s)) = q s!(length(q s)-1)") prefer 2
  apply (metis F.distinct(11) last_tl list.size(3) zero_less_diff)
  apply metis
  apply(subgoal_tac "offset s = b") prefer 2
  apply (metis le_neq_implies_less)
  apply(subgoal_tac "\<forall>i.  (i \<le> N \<and> ownB s i = Q)\<longrightarrow>(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) ")
  prefer 2 
  apply presburger
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)")
  prefer 2 
  apply presburger
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>(\<exists>x.(x = {i. a\<le>i \<and> i < a + b} \<and> a\<in>x))") prefer 2
  apply (metis Nat.add_0_right le_refl mem_Collect_eq nat_add_left_cancel_less)
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s)) \<longrightarrow> ownB s a = Q") prefer 2 
  apply (metis (no_types, lifting))
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(tl(q s))\<longrightarrow>(a,b)\<in>set(q s)") prefer 2
  apply (metis list.set_sel(2))
  apply(subgoal_tac "ownB s (fst (hd (q s)) + snd (hd (q s))) = Q \<and> fst (hd (q s)) + snd (hd (q s))\<le>N") prefer 2 
  apply (metis Suc_le_lessD le_add1 le_less_Suc_eq not_less_eq_eq)
  apply(subgoal_tac "(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> fst (hd (q s)) + snd (hd (q s)) \<in> x)") prefer 2 
  apply presburger
  apply(subgoal_tac "\<exists>a b.(a\<le>fst (hd (q s)) + snd (hd (q s)) \<and> fst (hd (q s)) + snd (hd (q s))<a+b \<and> (a,b)\<in>set(q s))") prefer 2
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply clarify
  apply(subgoal_tac "\<exists>tru. (tru<length(q s) \<and> q s!tru = (ab,bb))") prefer 2 
  apply (metis (no_types, lifting) in_set_conv_nth)
  apply(clarify)
  apply(subgoal_tac "tru\<noteq>0") prefer 2 
  apply (metis fst_conv hd_conv_nth less_irrefl_nat snd_conv) apply(subgoal_tac "length(q s)>1") 
  prefer 2 
  apply linarith
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(tl(q s))\<longrightarrow>(a,b)\<in>set(q s)") prefer 2
  apply meson
  apply(subgoal_tac "last(q s) = last(tl(q s))") prefer 2
  apply (metis diff_is_0_eq' last_tl length_tl list.size(3) zero_less_diff)
  apply (metis nat_less_le)
  apply (metis diff_add_inverse diff_is_0_eq' le_less_Suc_eq linorder_neqE_nat list.set_sel(1) not_add_less1 not_less_eq prod.collapse)
  apply (metis add_eq_self_zero list.set_sel(1) prod.collapse)
  proof -
  fix a :: nat and b :: nat and c :: nat and d :: nat and e :: nat and f :: nat and x :: "nat set" and aa :: nat and ba :: nat and ab :: nat and bb :: nat and xa :: "nat set" and ac :: nat and bc :: nat and ad :: nat and bd :: nat and assa :: nat and trua :: nat
  assume a1: "Q_structure s"
  assume a2: "assa < length (q s)"
  assume a3: "trua < length (q s)"
  assume a4: "assa \<noteq> 0"
  assume a5: "2 < length (q s)"
  assume a6: "fst (q s ! assa) = 0"
  assume "fst (q s ! trua) = fst (q s ! 0) + snd (q s ! 0)"
  then show "trua = 1"
  using a6 a5 a4 a3 a2 a1 by (metis (no_types) pec_prelim_11)
  next
  show " \<And>a b c d e f.
       pcR s = idleR \<Longrightarrow> s' = s
       \<lparr>ownB := \<lambda>i. if T s \<le> i \<and> i < T s + snd (hd (q s)) then R else ownB s i, numDeqs := Suc (numReads s), ownT := R,
          tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr> \<Longrightarrow>  q s \<noteq> [] \<Longrightarrow>  fst (hd (q s)) = T s \<Longrightarrow> H s \<noteq> fst (last (q s)) + snd (last (q s)) \<Longrightarrow> 0 < T s \<Longrightarrow> Q_structure s \<Longrightarrow> 0 < n \<Longrightarrow> tempR s = (0, 0) \<Longrightarrow> H s \<le> N \<Longrightarrow> 0 \<le> b \<Longrightarrow> n < N \<Longrightarrow>  numDeqs s = numReads s \<Longrightarrow> T s \<le> N \<Longrightarrow>   b \<le> H s \<Longrightarrow>  numEnqs s \<le> n \<Longrightarrow> ownT s = Q \<Longrightarrow> hW s \<le> N \<Longrightarrow>   H s < T s \<Longrightarrow> numReads s \<le> numEnqs s \<Longrightarrow> \<forall>i<n. Data s i \<le> N \<and> 0 < Data s i \<Longrightarrow> \<forall>i. T s \<le> i \<and> i < T s + snd (hd (q s)) \<longrightarrow> ownB s i = Q \<Longrightarrow> \<forall>i. (i < fst (tempR s) \<longrightarrow> ownB s i \<noteq> R) \<and> (fst (tempR s) + snd (tempR s) \<le> i \<and> i \<le> N \<longrightarrow> ownB s i \<noteq> R) \<Longrightarrow>
       tW s \<le> N \<Longrightarrow>  T s \<le> e \<Longrightarrow>  0 < H s \<Longrightarrow> e \<le> f \<Longrightarrow> \<forall>i. (i < numReads s \<longrightarrow> ownD s i = R) \<and>
           (numReads s \<le> i \<and> i < numWrites s \<longrightarrow> ownD s i = B) \<and> (numWrites s \<le> i \<and> i < n \<longrightarrow> ownD s i = W) \<Longrightarrow>
       f \<le> N \<Longrightarrow>  numEnqs s - numReads s = length (q s) \<Longrightarrow> \<forall>i<0. ownB s i = R \<Longrightarrow> numReads s \<le> numWrites s \<Longrightarrow>\<forall>i. 0 \<le> i \<and> i < b \<longrightarrow> ownB s i = Q \<Longrightarrow> numWrites s \<le> n \<Longrightarrow> \<forall>i. b \<le> i \<and> i < H s \<longrightarrow> ownB s i = W \<Longrightarrow>\<forall>a b. (a, b) \<in> set (q s) \<longrightarrow> a + b \<le> N \<Longrightarrow> \<forall>i. H s \<le> i \<and> i < T s \<longrightarrow> ownB s i = B \<Longrightarrow> \<forall>i. i < length (q s) \<and> 0 < i \<longrightarrow>
           fst (q s ! (i - Suc 0)) + snd (q s ! (i - Suc 0)) = fst (q s ! i) \<or> fst (q s ! i) = 0 \<Longrightarrow>
       \<forall>i. T s \<le> i \<and> i < e \<longrightarrow> ownB s i = R \<Longrightarrow>\<forall>i j. i < length (q s) \<and> j < length (q s) \<and> i \<noteq> j \<longrightarrow> fst (q s ! i) \<noteq> fst (q s ! j) \<Longrightarrow>\<forall>i. e \<le> i \<and> i < f \<longrightarrow> ownB s i = Q \<Longrightarrow> \<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a < aa \<longrightarrow> a + b \<le> aa \<Longrightarrow>\<forall>i. f \<le> i \<and> i < N \<longrightarrow> ownB s i = D \<Longrightarrow>\<forall>a. (\<exists>b. (a, b) \<in> set (q s)) \<longrightarrow> a \<noteq> fst (last (q s)) + snd (last (q s)) \<Longrightarrow> ownB s N = F.None \<Longrightarrow> \<forall>a b. (a, b) \<in> set (q s) \<longrightarrow> 0 < b \<Longrightarrow> 0 < 0 \<longrightarrow> e = T s \<Longrightarrow> \<forall>i<length (q s). data_index s (q s ! i) = numReads s + i \<Longrightarrow>
       T s < e \<longrightarrow> 0 = 0 \<Longrightarrow>\<forall>i<length (q s). snd (q s ! i) = Data s (numReads s + i) \<Longrightarrow>e < f \<longrightarrow> 0 = 0 \<Longrightarrow> \<forall>i<length (q s). ownD s (i + numReads s) = B \<Longrightarrow> 0 < H s \<Longrightarrow>\<forall>i\<le>N. \<forall>j\<le>N. data_index s (i, j) < n \<Longrightarrow>\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) = (i \<le> N \<and> ownB s i = Q) \<Longrightarrow>
       b < H s \<longrightarrow> offset s = b \<Longrightarrow>b < H s \<longrightarrow> Data s (numEnqs s) = H s - b \<Longrightarrow> T s < e \<longrightarrow> T s = 0 \<Longrightarrow>\<not> T s < e \<Longrightarrow> e < f \<or> 0 < b \<Longrightarrow> e < f \<longrightarrow> T s = e \<Longrightarrow> f = e \<and> 0 < b \<longrightarrow> T s = 0 \<Longrightarrow>0 < b \<longrightarrow> fst (last (q s)) + snd (last (q s)) = b \<Longrightarrow>b = 0 \<and> e < f \<longrightarrow> fst (last (q s)) + snd (last (q s)) = f \<Longrightarrow>\<not> N < T s + snd (hd (q s)) \<Longrightarrow>Suc 0 < length (q s) \<Longrightarrow>fst (q s ! 1) = fst (q s ! 0) + snd (q s ! 0) \<or> fst (q s ! 1) = 0 \<Longrightarrow>q s ! 0 = hd (q s) \<Longrightarrow> q s ! 1 = hd (tl (q s)) \<Longrightarrow>\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> i \<le> N \<and> ownB s i = Q \<Longrightarrow>
       q s ! 1 \<in> set (q s) \<Longrightarrow> q s ! 1 = (sta, leng) \<longrightarrow> (sta, leng) \<in> set (q s) \<Longrightarrow>fst (q s ! 1) = 0 \<Longrightarrow> \<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> i \<le> N \<and> ownB s i = Q \<Longrightarrow>
       \<forall>i. (\<exists>x. x = {i. fst (hd (tl (q s))) \<le> i \<and> i < fst (hd (tl (q s))) + snd (hd (tl (q s)))} \<and> i \<in> x) \<longrightarrow>
           i \<le> N \<and> ownB s i = Q \<Longrightarrow>0 < offset s"
  proof -
  fix a :: nat and b :: nat and c :: nat and d :: nat and e :: nat and f :: nat
  assume a1: "H s \<noteq> fst (last (q s)) + snd (last (q s))"
  assume "0 < n"
  assume a2: "0 \<le> b"
  assume a3: "b \<le> H s"
  assume "H s < T s"
  assume "T s \<le> e"
  assume a4: "0 < H s"
  assume a5: "\<forall>i. b \<le> i \<and> i < H s \<longrightarrow> ownB s i = W"
  assume a6: "\<forall>a b. (a, b) \<in> set (q s) \<longrightarrow> 0 < b"
  assume a7: "b < H s \<longrightarrow> offset s = b"
  assume "\<not> T s < e"
  assume "e < f \<or> 0 < b"
  assume a8: "0 < b \<longrightarrow> fst (last (q s)) + snd (last (q s)) = b"
  assume a9: "q s ! 1 = hd (tl (q s))"
  assume a10: "q s ! 1 \<in> set (q s)"
  assume a11: "fst (q s ! 1) = 0"
  assume a12: "\<forall>i. (\<exists>x. x = {i. fst (hd (tl (q s))) \<le> i \<and> i < fst (hd (tl (q s))) + snd (hd (tl (q s)))} \<and> i \<in> x) \<longrightarrow> i \<le> N \<and> ownB s i = Q"
  have "\<not> (0::nat) \<le> 0 \<or> fst (hd (tl (q s))) \<le> 0 \<and> 0 < fst (hd (tl (q s))) + snd (hd (tl (q s)))"
  using a11 a10 a9 a6 by (metis (no_types) plus_nat.add_0 prod.collapse)
  then have "0 \<noteq> b"
  using a12 a5 a4 by force
  then show "0 < offset s"
  using a8 a7 a3 a2 a1 by (metis nat_less_le)
  qed
  qed
  
  








lemma R_idle_to_nidle_lemma_case_1_6_4:
  "case_2 s\<Longrightarrow>con_assms s \<Longrightarrow> pcR s = idleR\<Longrightarrow>pre_R (pcR s) s
  \<Longrightarrow>s'=(s\<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
          numDeqs := Suc (numDeqs s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr>)
\<Longrightarrow>inv s \<Longrightarrow>q s\<noteq>[] \<Longrightarrow> fst(hd(q s)) \<noteq> T s \<Longrightarrow> H s = fst(last(q s))+snd(last(q s))
\<Longrightarrow>case_2 s'"
  apply(subgoal_tac "T s\<noteq>0") prefer 2
  apply(simp add:case_2_def) 
  apply(subgoal_tac "Q_structure s") prefer 2 
  apply (metis RingBuffer_BD_latest_2.inv_def)
  apply (metis gr0I less_nat_zero_code)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "Q_structure s") prefer 2 using pec_prelim_9 [where s=s]
  apply blast
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:pre_R_def pre_dequeue_inv_def)
  apply(simp add:case_2_def ) 
  apply(clarify) 
  apply(intro conjI impI)
  apply (metis (no_types, lifting) le_antisym less_or_eq_imp_le list.set_sel(1) nat_neq_iff prod.collapse)
  apply(rule_tac ?x = "fst (hd (q s))+snd(hd(q s))" in exI)
  apply(rule_tac ?x = "H s" in exI)
  apply(intro conjI impI) defer
  apply(rule_tac ?x = "H s" in exI)
  apply(intro conjI impI) 
  apply (metis le_neq_implies_less)
  apply(rule_tac ?x = "T s" in exI)
  apply(intro conjI impI) 
  apply linarith
  apply(rule_tac ?x = "T s" in exI)
  apply(intro conjI impI) 
  apply linarith
  apply(rule_tac ?x = "T s" in exI)
  apply(intro conjI impI) 
  apply linarith
  apply linarith 
  apply (metis bot_nat_0.extremum le_neq_implies_less)
  apply (metis Suc_leI le_add1 le_neq_implies_less le_trans not_less_eq_eq) 
  apply (metis (no_types, lifting) F.distinct(3) le_neq_implies_less)
  apply (metis (no_types, hide_lams) F.distinct(19))
  apply (metis le_neq_implies_less)
  apply (metis Suc_diff_Suc Zero_not_Suc diff_is_0_eq')
  apply (metis (no_types, hide_lams) F.distinct(21) nat_less_le)
  apply blast
  apply blast
  apply fastforce
  apply fastforce
  using add_gr_0 apply presburger
  apply blast 
  apply presburger
  apply (metis nat_less_le)
  apply (metis nat_less_le)
  apply (metis le_neq_implies_less)
  apply (metis add_cancel_right_left le_neq_implies_less)
  apply (metis le_neq_implies_less)
  apply (metis le_neq_implies_less) 
  defer 
  apply fastforce
  apply(subgoal_tac "fst(hd(q s)) = 0") prefer 2 
  apply (metis le_neq_implies_less)
  apply(subgoal_tac "fst (hd (tl (q s))) = fst(q s!1)") prefer 2 
  apply (metis One_nat_def hd_conv_nth last_conv_nth length_greater_0_conv length_tl list.size(3) nat_neq_iff nth_tl)
  apply(subgoal_tac "fst(hd(q s)) = fst(q s!0)") prefer 2
  apply (metis hd_conv_nth)
  apply(subgoal_tac "fst (hd (tl (q s))) = fst(q s!1)") prefer 2
  apply linarith
  apply(subgoal_tac "hd (q s) = q s!0") prefer 2
  apply (metis hd_conv_nth)
  apply(subgoal_tac "hd (tl(q s)) = q s!1") prefer 2
  apply (metis One_nat_def hd_conv_nth last_conv_nth length_greater_0_conv length_tl list.size(3) nat_neq_iff nth_tl)
  defer defer
  apply force
  apply (metis add_cancel_right_left le_neq_implies_less list.set_sel(1) prod.collapse)
  apply (metis add_cancel_right_left le_neq_implies_less list.set_sel(1) prod.collapse)
  apply(subgoal_tac "\<forall>i.(ownB s i = Q \<and> i\<le>N) \<longrightarrow> i<H s") prefer 2 
  apply (metis F.distinct(19) F.distinct(21) F.distinct(23) le_neq_implies_less less_or_eq_imp_le linorder_neqE_nat)
  apply(subgoal_tac "\<forall>i.(fst(hd(q s))\<le>i \<and> i<fst(hd(q s))+snd(hd(q s))) \<longrightarrow> ownB s i = Q") prefer 2
  apply meson
  apply (metis (no_types, hide_lams) bot_nat_0.not_eq_extremum diff_diff_cancel diff_is_0_eq diff_self_eq_0 zero_less_diff)
  apply(intro iffI)
  apply(case_tac "T s < T s") 
  apply force apply(subgoal_tac "\<not>T s < T s \<and> ((T s < T s \<or> fst (hd (q s)) + snd (hd (q s)) < H s)) \<longrightarrow> H s > fst (hd (q s)) + snd (hd (q s))") prefer 2
  apply blast
  apply(subgoal_tac "H s > fst (hd (q s)) + snd (hd (q s))") prefer 2
  apply force
  apply(subgoal_tac "\<forall>i.  (i \<le> N \<and> ownB s i = Q)\<longrightarrow>(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) ")
  prefer 2 
  apply presburger
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)")
  prefer 2 
  apply presburger
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>(\<exists>x.(x = {i. a\<le>i \<and> i < a + b} \<and> a\<in>x))") prefer 2
  apply (metis Nat.add_0_right le_refl mem_Collect_eq nat_add_left_cancel_less)
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s)) \<longrightarrow> ownB s a = Q") prefer 2 
  apply (metis (no_types, lifting))
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(tl(q s))\<longrightarrow>(a,b)\<in>set(q s)") prefer 2
  apply (metis list.set_sel(2))
  apply(subgoal_tac "fst (hd (q s)) + snd(hd(q s)) \<le>N") prefer 2 
  apply (metis (no_types, lifting) Suc_le_lessD bot_nat_0.extremum le_neq_implies_less not_less_eq_eq)
  apply(subgoal_tac "ownB s (fst (hd (q s)) + snd(hd(q s))) = Q") prefer 2 
  apply (metis le_add1 le_neq_implies_less)
  apply(subgoal_tac "(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> fst (hd (q s)) + snd (hd (q s)) \<in> x)") prefer 2
  apply presburger
  apply(subgoal_tac "\<exists>a b.(a\<le>fst (hd (q s)) + snd (hd (q s)) \<and> fst (hd (q s)) + snd (hd (q s))<a+b \<and> (a,b)\<in>set(q s))") prefer 2
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply clarify
  apply(subgoal_tac "\<exists>tru. (tru<length(q s) \<and> q s!tru = (ab,bb))") prefer 2 
  apply (metis (no_types, lifting) in_set_conv_nth)
  apply(clarify)
  apply(subgoal_tac "tru\<noteq>0") prefer 2 
  apply (metis fst_conv hd_conv_nth less_irrefl_nat snd_conv) apply(subgoal_tac "length(q s)>1") 
  prefer 2 
  apply linarith
  apply(subgoal_tac "hd(q s) = q s!0") prefer 2
  apply (metis hd_conv_nth)
  apply(subgoal_tac "last(q s) = q s!(length(q s) -1 ) ") prefer 2 
  apply (metis last_conv_nth)
  apply(subgoal_tac "last(q s) \<noteq> hd(q s) \<longrightarrow> length(q s)>1") prefer 2 
  apply (metis One_nat_def)
  using str_pec_5 [where s=s] 
  apply (metis (no_types, hide_lams) One_nat_def add.commute nat_less_le)
  apply(subgoal_tac "fst (hd (q s)) + snd (hd (q s)) < H s") prefer 2 
  apply (metis (no_types, hide_lams) One_nat_def add.commute le_neq_implies_less str_pec_5)
  apply force
  apply(subgoal_tac "hd(q s) = q s!0") prefer 2
  apply (metis hd_conv_nth)
  apply(subgoal_tac "last(q s) = q s!(length(q s) -1 ) ") prefer 2 
  apply (metis last_conv_nth)
  apply(subgoal_tac "hd(q s) = q s!0") prefer 2
  apply (metis hd_conv_nth)
  apply(subgoal_tac "hd(tl(q s)) = q s!1") prefer 2
  apply (metis (no_types, lifting) One_nat_def hd_conv_nth last_conv_nth length_greater_0_conv length_tl list.size(3) nat_neq_iff nth_tl)
  apply(subgoal_tac "fst(q s!0) = 0") prefer 2 
  apply (metis le_neq_implies_less)
  apply(subgoal_tac "fst (hd (q s)) + snd (hd (q s)) = fst(q s!0) + snd(q s!0)") prefer 2 
  apply presburger
  apply(subgoal_tac "i < length (q s) \<and> j < length (q s) \<and> i \<noteq> j \<longrightarrow> fst (q s ! i) \<noteq> fst (q s ! j)") prefer 2
  apply (metis (no_types, lifting))
  apply(subgoal_tac "length(q s)>1") prefer 2 
  apply (metis (no_types, lifting) One_nat_def Suc_lessI diff_add_inverse last_conv_nth length_greater_0_conv nat_neq_iff plus_1_eq_Suc)
  apply(subgoal_tac "fst(q s!0) \<noteq> fst(q s!1)") prefer 2 
  apply (metis (no_types, hide_lams) bot_nat_0.not_eq_extremum length_greater_0_conv less_one)
  apply (metis (no_types, hide_lams) Suc_diff_1 diff_self_eq_0 less_one)
  apply(subgoal_tac "last(q s) = q s!(length(q s)-1)") prefer 2 
  apply (metis last_conv_nth)
  apply(subgoal_tac "length(tl(q s)) = length(q s)-1") prefer 2
  apply (metis length_tl)
  apply(subgoal_tac "last(tl(q s)) = (tl(q s)!(length(tl(q s)) -1))") prefer 2 
  apply (metis (no_types, lifting) hd_conv_nth last_conv_nth length_0_conv less_not_refl2)
  apply(subgoal_tac "last(tl(q s)) = (tl(q s)!(length(q s) -2))") prefer 2 
  apply (metis Suc_1 diff_Suc_eq_diff_pred)
  by (metis (no_types, hide_lams) hd_conv_nth last_tl length_0_conv nat_less_le)




lemma R_idle_to_nidle_lemma_case_1_6:
  "case_2 s\<Longrightarrow>con_assms s \<Longrightarrow> pcR s = idleR\<Longrightarrow>pre_R (pcR s) s
  \<Longrightarrow>s'=(s\<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
          numDeqs := Suc (numDeqs s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr>)
\<Longrightarrow>inv s \<Longrightarrow>q s\<noteq>[]
\<Longrightarrow>case_2 s'"
  apply (case_tac "fst(hd(q s)) = T s") 
  apply (case_tac[!] "H s = fst(last(q s))+snd(last(q s))") 
  using R_idle_to_nidle_lemma_case_1_6_1 [where s=s and s'=s'] 
  apply blast 
  using R_idle_to_nidle_lemma_case_1_6_3 [where s=s and s'=s']
  apply blast 
  using R_idle_to_nidle_lemma_case_1_6_4 [where s=s and s'=s'] 
  apply blast
  using R_idle_to_nidle_lemma_case_1_6_2 [where s=s and s'=s'] 
  by blast
    






lemma strange_things_1:
  "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) 
\<longrightarrow> (i \<le> N \<and> ownB s i = Q)
\<Longrightarrow>
\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (tl(q s))) \<and> (i \<in> x)) 
\<longrightarrow> (i \<le> N \<and> ownB s i = Q)"
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(tl(q s))\<longrightarrow> (a,b)\<in>set(q s)") prefer 2
  apply (metis list.sel(2) list.set_sel(2))
  by blast

lemma strange_things_2:
  "Q_structure s
\<Longrightarrow> ((a,b)\<in>set((q s)) \<and> (a,b)\<noteq>hd(q s)) \<longrightarrow> a\<noteq>fst(hd(q s))
" apply(case_tac "q s=[]") 
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(q s) \<longrightarrow> (\<exists>i.(i<length(q s) \<and> q s!i = (a,b)))") prefer 2
  apply (meson in_set_conv_nth)
  apply(subgoal_tac "hd(q s) = q s!0") prefer 2 
  using hd_conv_nth apply auto[1]
  by (metis fst_conv length_pos_if_in_set)

lemma strange_things_3:
  "Q_structure s
\<Longrightarrow> (a,b)\<in>set((q s)) \<longrightarrow> (\<exists>i.(i<length(q s) \<and> q s!i = (a,b)))
" apply(case_tac "q s=[]") 
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(q s) \<longrightarrow> (\<exists>i.(i<length(q s) \<and> q s!i = (a,b)))") prefer 2
  apply (meson in_set_conv_nth)
  apply(subgoal_tac "hd(q s) = q s!0") prefer 2 
  using hd_conv_nth apply auto[1]
  by (metis)

lemma strange_things_4:
  "Q_structure s
\<Longrightarrow> ((a,b)\<in>set(q s)) \<Longrightarrow> \<exists>j.(j<length(q s) \<and> q s!j =(a,b))" 
  apply(case_tac "q s=[]") 
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "fst(q s!0) = fst(hd(q s))") prefer 2 
  apply (metis hd_conv_nth) 
  by (meson in_set_conv_nth)
  

lemma strange_things_5:
  "Q_structure s
\<Longrightarrow> ((a,b)\<in>set(q s)) \<Longrightarrow> (a,b)\<noteq>hd(q s) \<Longrightarrow> \<exists>j.(j<length(q s) \<and> q s!j =(a,b) \<and> j>0)" 
  apply(case_tac "q s=[]") 
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "fst(q s!0) = fst(hd(q s))") prefer 2 
  apply (metis hd_conv_nth) 
  by (metis bot_nat_0.not_eq_extremum hd_conv_nth in_set_conv_nth)

lemma strange_things_6:
  "Q_structure s
\<Longrightarrow> ((a,b)\<in>set(q s)) \<Longrightarrow> (a,b)\<noteq>hd(q s) \<Longrightarrow> a\<noteq>fst(hd(q s))" 
  apply(case_tac "q s=[]") 
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "fst(q s!0) = fst(hd(q s))") prefer 2 
  apply (metis hd_conv_nth) 
  by (metis fst_conv hd_conv_nth in_set_conv_nth length_pos_if_in_set) 


lemma strange_things_7_1:
  " Q_structure s
\<Longrightarrow> \<forall>y x.(x \<in>set(q s) \<and> y\<in>set(q s) \<and> fst(x)>fst(y))\<longrightarrow>fst(x)\<ge>end(y)
"
  apply(case_tac "q s=[]") 
  apply(simp add:Q_lemmas Q_basic_lemmas)
  by(simp add:Q_lemmas Q_basic_lemmas)

lemma strange_things_7_2:
  " Q_structure s
\<Longrightarrow> \<forall>a b aa bb.((a,b) \<in>set(q s) \<and> (aa,bb)\<in>set(q s) \<and> a>aa)\<longrightarrow>a\<ge>aa+bb
"
  apply(case_tac "q s=[]") 
  apply(simp add:Q_lemmas Q_basic_lemmas)
  using strange_things_7_1 fst_def end_def 
  by (metis old.prod.inject surjective_pairing)
  

lemma strange_things_7_3:
  " Q_structure s
\<Longrightarrow> \<forall>a b aa bb.((a,b) \<in>set(q s) \<and> (aa,bb)\<in>set(q s) \<and> a\<noteq>aa)\<longrightarrow>(a>aa \<or> a<aa)
"
  apply(case_tac "q s=[]") 
  apply(simp add:Q_lemmas Q_basic_lemmas)
  using strange_things_7_1 fst_def end_def
  using nat_neq_iff by blast


lemma strange_things_7_5:
  " Q_structure s 
\<Longrightarrow> \<forall>x.(x \<in>set(tl(q s)))\<longrightarrow>(fst(x)\<noteq>fst(hd(q s)))
" apply clarify 
  apply(case_tac "q s=[]") 
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply (simp add:Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "(\<forall>i j. i < length (q s) \<and> j < length (q s) \<and> i \<noteq> j \<longrightarrow> fst (q s ! i) \<noteq> fst (q s ! j))")
  prefer 2 
  apply (metis less_nat_zero_code list.size(3)) apply clarify
  apply(subgoal_tac "\<nexists>i.(i<length(q s) \<and> i>0 \<and> (fst (hd (q s)), b) = q s!i)") prefer 2 
  apply (metis fst_conv gr_implies_not_zero hd_conv_nth length_greater_0_conv)
  apply(subgoal_tac "\<forall>i j.(fst (q s ! i) = fst (q s ! j))\<longrightarrow> (i=j\<or>i \<ge> length (q s) \<or> j \<ge>  length (q s))") prefer 2 
  apply (meson bot_nat_0.not_eq_extremum diff_is_0_eq zero_less_diff) 
  apply(case_tac "tl(q s) = []") 
  apply (metis length_greater_0_conv length_pos_if_in_set)
  apply clarsimp
  apply(subgoal_tac "(fst (hd (q s)), b) \<in> set (tl (q s))") prefer 2 
  apply blast
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set((q s)) \<longrightarrow> (\<exists>i.(i<length(q s) \<and> q s!i = (a, b)))") prefer 2 
  apply (meson in_set_conv_nth)
  apply(subgoal_tac "length(q s) -1 = length(tl(q s))") prefer 2 
  apply (metis length_tl)
  apply(subgoal_tac "hd(q s) = q s !0") prefer 2 
  apply (meson Q_ind_imp_tail_ind_1)
  apply(subgoal_tac "\<forall>i.(i<length(tl(q s)))\<longrightarrow>tl(q s)!i = q s!(i+1)") prefer 2 
  apply (metis Suc_eq_plus1 nth_tl)
  by (smt (z3) One_nat_def diff_Suc_less gr_implies_not0 in_set_conv_nth length_greater_0_conv lessI less_trans_Suc nth_tl)

lemma strange_things_7_almost_there_1:
  " Q_structure s
\<Longrightarrow> q s\<noteq>[]
\<Longrightarrow> tl(q s)\<noteq>[]
\<Longrightarrow>\<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a + b > aa \<longrightarrow>a \<ge> aa "
  apply(simp add:Q_lemmas Q_basic_lemmas) 
  by (metis le_antisym le_eq_less_or_eq nat_neq_iff)

lemma strange_things_7_almost_there_2:
  " Q_structure s
\<Longrightarrow> q s\<noteq>[]
\<Longrightarrow> tl(q s)\<noteq>[]
\<Longrightarrow>\<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a \<ge> aa \<and> a\<noteq>aa \<longrightarrow> a>aa"
  by(simp add:Q_lemmas Q_basic_lemmas) 


lemma strange_things_7_almost_there_3:
  " Q_structure s
\<Longrightarrow> q s\<noteq>[]
\<Longrightarrow> tl(q s)\<noteq>[]
\<Longrightarrow>\<forall>a b aa ba. (a, b) \<in> set (q s) \<and> (aa, ba) \<in> set (q s) \<longrightarrow> a>aa \<longrightarrow> a\<ge>aa+ba"
  by (meson strange_things_7_2)

lemma strange_things_7_almost_there_4:
  " Q_structure s
\<Longrightarrow> q s\<noteq>[]
\<Longrightarrow> tl(q s)\<noteq>[]
\<Longrightarrow>\<forall>a b aa ba. (a, b) \<in> set (q s) \<and> (aa, ba) \<in> set (q s) \<longrightarrow> a\<ge>aa+ba \<longrightarrow> a+b>aa+ba"
  apply(simp add:Q_lemmas Q_basic_lemmas) 
  by (metis le_eq_less_or_eq less_add_same_cancel1 trans_less_add1)

lemma strange_things_7:
  " Q_structure s
\<Longrightarrow> i \<in> {i. fst(hd(q s)) \<le>i \<and> i<fst(hd(q s)) + snd(hd(q s))}
\<Longrightarrow>\<forall>a b.(a,b)\<in>set(tl(q s))\<longrightarrow> (a\<ge>fst(hd(q s)) + snd(hd(q s)) \<or> a+b\<le>fst(hd(q s)))
\<Longrightarrow> \<forall>a b.(a,b)\<in>set(tl(q s)) \<longrightarrow> i \<notin> {i. a \<le>i \<and> i<a+b}
"
  apply(simp add:Q_lemmas Q_basic_lemmas)
  by (meson Suc_leI le_trans not_less_eq_eq)


lemma strange_things_8_1_1:
  "Q_structure s \<Longrightarrow>
\<forall>a b.(a,b)\<in>set(tl(q s)) \<longrightarrow> (\<exists>i. (i<length(q s) \<and> i>0 \<and> (q s!i) = (a,b)))"
  by (metis list.sel(2) list.set_sel(2) strange_things_5 strange_things_7_5)


lemma strange_things_8_1_2:
  "Q_structure s \<Longrightarrow>
\<forall>i.(i<length(q s) \<and> i>0)\<longrightarrow> q s!i\<noteq>q s!0"
  by (metis Q_basic_struct_def Q_lemmas(4) Q_offsets_differ_def gr_implies_not0 length_0_conv length_greater_0_conv)

lemma strange_things_8_1_3:
  "Q_structure s \<Longrightarrow>
\<forall>i.(i<length(q s) \<and> i>0)\<longrightarrow> (fst(q s!i)>fst(q s!0) \<or> fst(q s!i)<fst(q s!0))" 
  using Q_gap_lemmas_1_list less_trans by blast


lemma strange_things_8_1_4_1:
  "Q_structure s \<Longrightarrow>
\<forall>a b.((a,b)\<in>set(q s) \<and> (a,b)\<noteq>hd(q s) \<and> a<fst(hd(q s)))\<longrightarrow> a+b\<le>fst(hd(q s))" 
  by (metis Q_gap_lemmas_2 eq_fst_iff head_q0 length_pos_if_in_set strange_things_7_2)

lemma strange_things_8_1_4_2:
  "Q_structure s \<Longrightarrow>
\<forall>i.(i<length(q s) \<and> i>0)\<longrightarrow> (fst(q s!i)\<noteq>fst(q s!0))" 
  apply(clarify)
  by (metis nat_neq_iff strange_things_8_1_3)

lemma strange_things_8_1_4_3:
  "Q_structure s \<Longrightarrow>
\<forall>i.(i<length(q s) \<and> i>0\<and>fst(q s!i)>fst(q s!0))\<longrightarrow> fst(q s!i)\<ge>end(q s!0)" 
  by (meson Q_gap_lemmas_4_list less_trans)


lemma strange_things_8_1_4_4:
  "Q_structure s \<Longrightarrow> case_1 s \<or> case_2 s \<Longrightarrow> Q_owns_bytes s \<Longrightarrow>
\<forall>i.(i<length(q s) \<and> i>0 \<and> fst(q s!i)<fst(q s!0)) \<longrightarrow> end(q s!i)<fst(q s!0)" 
  apply(simp add:Q_lemmas Q_basic_lemmas) apply(clarify)
  apply(subgoal_tac "(fst(q s!i), snd(q s!i)) \<in>set(q s)") prefer 2 
  apply (metis nth_mem prod.collapse)
  apply(subgoal_tac "(fst(q s!0), snd(q s!0)) \<in>set(q s)") prefer 2 
  apply (metis length_pos_if_in_set nth_mem prod.exhaust_sel)
  apply(subgoal_tac "fst (q s ! i) + snd (q s ! i) \<le> fst (q s ! 0)") prefer 2
  apply (metis less_asym' list.size(3))
  apply(subgoal_tac "fst (q s ! i) + snd (q s ! i) \<noteq> fst (q s ! 0)") 
  apply linarith
  apply(case_tac "i=length(q s)-1") 
  apply (metis last_conv_nth less_nat_zero_code list.size(3))
  apply(subgoal_tac "fst(q s!(i+1)) = end(q s!i) \<or> fst(q s!(i+1)) = 0") prefer 2 
  apply (smt (z3) Nat.add_0_right One_nat_def add_Suc_right add_diff_cancel_right' add_gr_0 end_simp list.size(3) nat_neq_iff not_less_eq)
  apply(case_tac "fst(q s!(i+1)) = end(q s!i)") apply simp 
  apply (metis One_nat_def Suc_mono diff_add_inverse less_zeroE list.size(3) not_gr0 not_less_less_Suc_eq plus_1_eq_Suc)
  apply(case_tac "case_1 s", simp_all)
  apply(simp add:case_1_def) 
  apply(clarify)
  apply(subgoal_tac "b = fst(q s!0)") prefer 2 
  apply (metis head_q0 length_greater_0_conv less_nat_zero_code list.size(3))
  apply(subgoal_tac "snd(q s!i)>0") prefer 2 
  apply linarith
  apply(subgoal_tac "b>0") prefer 2 
  apply linarith
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(subgoal_tac "(q s!i)\<in>set(q s)") prefer 2 
  apply (metis in_set_conv_nth)
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) = (i \<le> N \<and> ownB s i = Q)")
  prefer 2
  apply fastforce
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)")
  prefer 2 
  apply presburger
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)")
  prefer 2
  apply meson
  apply(subgoal_tac "(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) = q s!i))") prefer 2
  apply (metis prod.exhaust_sel)
  apply(clarify)
  apply(subgoal_tac "fst(q s!i)>fst(q s!0)") 
  apply linarith
  apply(subgoal_tac "fst(q s!i)\<noteq>fst(q s!0)") prefer 2 
  apply linarith
  apply(subgoal_tac "\<forall>i.(\<exists>x.( x = {i. a \<le> i \<and> i < a + ba} )\<and> i\<in>x)\<longrightarrow>ownB s i = Q") prefer 2
  apply metis
  apply(subgoal_tac "ba>0") prefer 2 
  apply (metis less_nat_zero_code list.size(3))
  apply(subgoal_tac "a\<in>{i. a \<le> i \<and> i < a + ba}") prefer 2
  apply (metis le_eq_less_or_eq less_add_same_cancel1 mem_Collect_eq)
  apply(subgoal_tac "ownB s a = Q") prefer 2 
  apply presburger
  apply (metis F.distinct(11) F.distinct(19) fst_eqD leI linorder_neqE_nat)
  apply(subgoal_tac "case_2 s") prefer 2 
  apply fastforce
  apply(thin_tac "\<not>case_1 s")
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:case_2_def)
  apply clarify
  apply(subgoal_tac "f>e \<or> a<b") prefer 2 
  apply (metis less_nat_zero_code list.size(3))
  apply(subgoal_tac "e= fst(hd(q s)) \<or> a = fst(hd(q s))") prefer 2 
  apply (metis le_eq_less_or_eq)
  apply(case_tac "a = fst(hd(q s))")
  apply(subgoal_tac "(q s!i)\<in>set(q s)") prefer 2 
  apply (metis in_set_conv_nth)
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) = (i \<le> N \<and> ownB s i = Q)")
  prefer 2
  apply fastforce
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)")
  prefer 2 
  apply presburger
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)")
  prefer 2
  apply meson
  apply(subgoal_tac "(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) = q s!i))") prefer 2
  apply (metis prod.exhaust_sel)
  apply(clarify)
  apply(subgoal_tac "fst(q s!i)>fst(q s!0)") 
  apply linarith
  apply(subgoal_tac "fst(q s!i)\<noteq>fst(q s!0)") prefer 2 
  apply linarith
  apply(subgoal_tac "\<forall>i.(\<exists>x.( x = {i. aa \<le> i \<and> i < aa + ba} )\<and> i\<in>x)\<longrightarrow>ownB s i = Q") prefer 2 sledgehammer
  apply metis
  apply(subgoal_tac "ba>0") prefer 2 
  apply (metis less_nat_zero_code list.size(3))
  apply(subgoal_tac "aa\<in>{i. aa \<le> i \<and> i < aa + ba}") prefer 2
  apply (metis le_eq_less_or_eq less_add_same_cancel1 mem_Collect_eq)
  apply(subgoal_tac "ownB s aa = Q") prefer 2 
  apply metis 
  apply (metis F.distinct(11) fst_conv hd_conv_nth)
  apply(subgoal_tac "e = fst (hd (q s))") prefer 2 
  apply force
  apply(subgoal_tac "b = end(last(q s)) \<or> f = end(last(q s))") prefer 2 
  apply (metis end_simp nat_less_le)
  apply(case_tac "f = end(last(q s))") 
  apply(subgoal_tac "(q s!i)\<in>set(q s)") prefer 2 
  apply (metis in_set_conv_nth)
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) = (i \<le> N \<and> ownB s i = Q)")
  prefer 2
  apply fastforce
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)")
  prefer 2 
  apply presburger
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)")
  prefer 2
  apply meson
  apply(subgoal_tac "(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) = q s!i))") prefer 2
  apply (metis prod.exhaust_sel)
  apply(clarify)
  apply(subgoal_tac "fst(q s!i)>fst(q s!0)") 
  apply linarith
  apply(subgoal_tac "fst(q s!i)\<noteq>fst(q s!0)") prefer 2 
  apply linarith
  apply(subgoal_tac "\<forall>i.(\<exists>x.( x = {i. aa \<le> i \<and> i < aa + ba} )\<and> i\<in>x)\<longrightarrow>ownB s i = Q") prefer 2 sledgehammer
  apply metis
  apply(subgoal_tac "ba>0") prefer 2 
  apply (metis less_nat_zero_code list.size(3))
  apply(subgoal_tac "aa\<in>{i. aa \<le> i \<and> i < aa + ba}") prefer 2
  apply (metis le_eq_less_or_eq less_add_same_cancel1 mem_Collect_eq)
  apply(subgoal_tac "ownB s aa = Q") prefer 2 
  apply metis 
  apply(subgoal_tac "a=b") prefer 2 
  apply (metis (no_types, lifting) end_simp less_trans nat_less_le)
  apply(subgoal_tac "\<forall>i.(i<fst(q s!0))\<longrightarrow>ownB s i\<noteq>Q") prefer 2 
  apply (metis F.distinct(11) F.distinct(19) F.distinct(3) hd_conv_nth leI)
  apply (metis fst_eqD)
  apply(subgoal_tac "f>e \<and> b>a") prefer 2 
  apply (metis end_simp nat_less_le)
  apply(subgoal_tac "fst(q s!i)<fst(hd(q s))") prefer 2 
  apply (metis hd_conv_nth)
  apply(subgoal_tac "(q s!i)\<in>set(q s)") prefer 2 
  apply (metis in_set_conv_nth)
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) = (i \<le> N \<and> ownB s i = Q)")
  prefer 2
  apply fastforce
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)")
  prefer 2 
  apply presburger
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> (i \<le> N \<and> ownB s i = Q)")
  prefer 2
  apply meson
  apply(subgoal_tac "(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) = q s!i))") prefer 2
  apply (metis prod.exhaust_sel)
  apply(clarify)
  apply(subgoal_tac "fst(q s!i)>fst(q s!0)") 
  apply linarith
  apply(subgoal_tac "fst(q s!i)\<noteq>fst(q s!0)") prefer 2 
  apply linarith
  apply(subgoal_tac "\<forall>i.(\<exists>x.( x = {i. aa \<le> i \<and> i < aa + ba} )\<and> i\<in>x)\<longrightarrow>ownB s i = Q") prefer 2 sledgehammer
  apply metis
  apply(subgoal_tac "ba>0") prefer 2 
  apply (metis)
  apply(subgoal_tac "aa\<in>{i. aa \<le> i \<and> i < aa + ba}") prefer 2
  apply (metis le_eq_less_or_eq less_add_same_cancel1 mem_Collect_eq)
  apply(subgoal_tac "ownB s aa = Q") prefer 2 
  apply metis 
  apply(subgoal_tac "\<forall>i.(i<fst(q s!0) \<and> i\<ge>end(last(q s)))\<longrightarrow>ownB s i\<noteq>Q") prefer 2 
  apply (metis F.distinct(11) F.distinct(19) F.distinct(3) hd_conv_nth leI)
  apply(subgoal_tac "fst(q s!i)<end(last(q s))") prefer 2 
  apply (metis fst_eqD leI)
  apply(subgoal_tac "\<forall>i.(i\<in>{j. j\<le>aa \<and> j<aa+ba})\<longrightarrow>ownB s i = Q") prefer 2 
  apply (metis fst_eqD leI le_trans less_eq_nat.simps(1) mem_Collect_eq)
  apply(subgoal_tac "aa\<le>aa+ba \<and> aa+ba\<le>end(last(q s))") prefer 2
  apply (metis fst_eqD leI le_eq_less_or_eq mem_Collect_eq snd_conv)  
  apply(subgoal_tac "fst(q s!i)<aa+ba") prefer 2 
  apply (metis fst_conv snd_conv)
  apply(subgoal_tac "fst(q s!i)<end(last(q s))") prefer 2 
  apply fastforce
  apply(subgoal_tac "end(last(q s)) < fst(q s!0)") prefer 2 
  apply (metis (no_types, hide_lams) fst_conv head_q0 le_imp_less_Suc le_trans not_less_eq order.strict_trans snd_conv)
  by (metis eq_fst_iff not_le snd_conv)




lemma strange_things_8_1_4:
  "Q_structure s \<Longrightarrow>case_1 s \<or> case_2 s \<Longrightarrow> Q_owns_bytes s \<Longrightarrow>
\<forall>i.(i<length(q s) \<and> i>0)\<longrightarrow> ((fst(q s!i)>fst(q s!0) \<and> fst(q s!i)\<ge>end(q s!0)) \<or> (fst(q s!i)<fst(q s!0)) \<and> end(q s!i)<fst(q s!0))" 
  apply(simp) 
  apply(subgoal_tac "\<forall>i.(i<length(q s) \<and> i>0\<and>fst(q s!i)>fst(q s!0))\<longrightarrow> fst(q s!i)\<ge>end(q s!0)") prefer 2 
  using strange_things_8_1_4_3 apply blast
  apply(subgoal_tac "\<forall>i.(i<length(q s) \<and> i>0 \<and> fst(q s!i)<fst(q s!0)) \<longrightarrow> end(q s!i)<fst(q s!0)") prefer 2 
  using strange_things_8_1_4_4 apply blast
  by (metis end_simp nat_neq_iff strange_things_8_1_4_2)



lemma strange_things_8_1_5:
  "Q_structure s \<Longrightarrow> case_1 s \<or> case_2 s \<Longrightarrow> Q_owns_bytes s \<Longrightarrow>
\<forall>i.(i<length(q s) \<and> i>0)\<longrightarrow> ((fst(q s!i)>fst(q s!0) \<longrightarrow> fst(q s!i)\<ge>end(q s!0)) \<and> (fst(q s!i)<fst(q s!0)) \<longrightarrow> end(q s!i)<fst(q s!0))" 
  apply(simp) 
  apply(subgoal_tac "\<forall>i.(i<length(q s) \<and> i>0\<and>fst(q s!i)>fst(q s!0))\<longrightarrow> fst(q s!i)\<ge>end(q s!0)") prefer 2 
  using strange_things_8_1_4_3 apply blast
  apply(subgoal_tac "\<forall>i.(i<length(q s) \<and> i>0 \<and> fst(q s!i)<fst(q s!0)) \<longrightarrow> end(q s!i)<fst(q s!0)") prefer 2 
  using strange_things_8_1_4_4 apply blast 
  by simp


lemma strange_things_8_1:
  " Q_structure s \<Longrightarrow> case_1 s \<or> case_2 s \<Longrightarrow> Q_owns_bytes s 
\<Longrightarrow>\<forall>a b.(a,b)\<in>set(tl(q s))\<longrightarrow> (a\<ge>fst(hd(q s)) + snd(hd(q s)) \<or> a+b<fst(hd(q s)))"
  apply clarify 
  apply(case_tac "q s=[]") 
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(case_tac "tl(q s)=[]") 
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply (simp add:Q_lemmas Q_basic_lemmas)apply(subgoal_tac "Q_structure s") prefer 2 
  using pec_prelim_9 [where s=s] 
  apply (simp add: pec_prelim_10)
  apply(subgoal_tac "hd(q s) = q s!0") prefer 2 
  using Q_ind_imp_tail_ind_1 apply auto[1]
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(tl(q s)) \<longrightarrow> (a,b)\<in>set(q s)") prefer 2
  apply (meson list.set_sel(2))
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s) \<and> (a,b)\<noteq>hd(q s)) \<longrightarrow> (\<exists>i.(i<length(q s) \<and> i>0 \<and> (a,b) = q s!i))") prefer 2
  apply (metis gr0I in_set_conv_nth)
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(tl(q s)) \<longrightarrow> a>fst(hd(q s)) \<or> a<fst(hd(q s))") prefer 2
  using strange_things_7_3 [where s=s] pec_prelim_10 [where s=s] strange_things_7_5 [where s=s]  
   apply clarsimp 
  apply (meson nat_neq_iff)
  apply(subgoal_tac "hd(q s) = q s!0") prefer 2 
  apply linarith
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set((q s)) \<longrightarrow> (\<exists>i.(i<length(q s) \<and> q s!i = (a, b)))") prefer 2 
  apply (meson in_set_conv_nth)
  apply(subgoal_tac "length(q s) -1 = length(tl(q s))") prefer 2 
  apply (metis length_tl)
  apply(subgoal_tac "hd(q s) = q s !0") prefer 2 
  apply (meson Q_ind_imp_tail_ind_1)
  apply(subgoal_tac "\<forall>i.(i<length(tl(q s)))\<longrightarrow>tl(q s)!i = q s!(i+1)") prefer 2 
   apply (metis Suc_eq_plus1 nth_tl) apply clarsimp 
  apply(subgoal_tac "\<exists>i.(i<length(q s) \<and> i>0 \<and> (a,b)\<in>set(q s))") prefer 2 
  apply (metis \<open>Q_structure s \<Longrightarrow> \<forall>x. x \<in> set (tl (q s)) \<longrightarrow> fst x \<noteq> fst (hd (q s))\<close>)
  apply(subgoal_tac "fst (q s ! 0)\<le>a") 
   apply (metis add_cancel_right_right le_imp_less_Suc length_pos_if_in_set less_SucE nth_mem surjective_pairing)
  apply(subgoal_tac "fst(q s!0) < a")  
  apply linarith
  apply clarsimp
  apply (thin_tac "\<forall>i<length (q s). snd (q s ! i) = Data s (numDeqs s + i)")
  apply (thin_tac "\<forall>i<length (q s). data_index s (q s ! i) = numDeqs s + i")
  apply (thin_tac "\<forall>i j. i < length (q s) \<and> j < length (q s) \<and> i \<noteq> j \<longrightarrow> fst (q s ! i) \<noteq> fst (q s ! j)")
  apply(thin_tac "\<forall>i. i < length (q s) \<and> 0 < i \<longrightarrow>
           fst (q s ! (i - Suc 0)) + snd (q s ! (i - Suc 0)) = fst (q s ! i) \<or> fst (q s ! i) = 0 ")
  apply (thin_tac "\<forall>a. (\<exists>b. (a, b) \<in> set (tl (q s))) \<longrightarrow> fst (q s ! 0) < a \<or> a < fst (q s ! 0)")
  apply (subgoal_tac "(a,b)\<in>set(q s)") prefer 2 
  apply meson
  apply(case_tac "(a,b)= last(q s)")
  apply (metis Q_gap_lemmas_2 Suc_le_lessD \<open>Q_structure s \<Longrightarrow> \<forall>x. x \<in> set (tl (q s)) \<longrightarrow> fst x \<noteq> fst (hd (q s))\<close> fst_conv le_neq_implies_less length_greater_0_conv not_less_eq_eq prod.collapse snd_conv)
  apply(subgoal_tac " a + b \<noteq> fst (q s ! 0)")
  apply (metis \<open>Q_structure s \<Longrightarrow> \<forall>x. x \<in> set (tl (q s)) \<longrightarrow> fst x \<noteq> fst (hd (q s))\<close> fst_conv hd_in_set le_neq_implies_less linorder_neqE_nat prod.collapse)
  apply(subgoal_tac "a + b > fst (q s ! 0)") 
  apply linarith
  apply(subgoal_tac "(a,b) \<noteq> last(q s)") prefer 2
  apply blast
  apply(subgoal_tac "(a,b) \<noteq> last(tl(q s))") prefer 2 
   apply (metis last_tl)
  apply(subgoal_tac "last(q s) = q s!(length(q s) -1)") prefer 2
  apply (meson last_conv_nth)
  apply(subgoal_tac "(a,b)\<noteq> q s!(length(q s) -1)") prefer 2 
   apply metis
  apply(subgoal_tac "(a,b)\<noteq> q s!0") prefer 2 
  apply (metis \<open>Q_structure s \<Longrightarrow> \<forall>x. x \<in> set (tl (q s)) \<longrightarrow> fst x \<noteq> fst (hd (q s))\<close>)
  apply(subgoal_tac "\<exists>k.((a,b) = q s!k \<and> k>0 \<and> k<length(q s)-1)") prefer 2 
  apply (metis Suc_diff_1 length_greater_0_conv not_less_less_Suc_eq)
  apply clarify 
  apply(case_tac "fst(q s!k) <fst(q s!0)") prefer 2 
  apply (metis fst_conv less_add_same_cancel1 linorder_neqE_nat)
  apply(subgoal_tac "fst(q s!k) < fst(q s!0)") prefer 2 
  apply blast
  apply(subgoal_tac "fst(q s!k) +snd(q s!k) \<le> fst(q s!0)") prefer 2 
  apply (metis hd_in_set prod.collapse)
  apply(subgoal_tac "a+b \<le> fst(q s!0)") prefer 2 
  apply (metis fst_conv snd_conv)
  by (metis end_simp fst_conv snd_conv strange_things_8_1_4_4)



lemma strange_things_8:
  "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) 
\<longrightarrow> (i \<le> N \<and> ownB s i = Q)
\<Longrightarrow>
\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (tl(q s))) \<and> (i \<in> x)) 
\<longrightarrow> (i \<le> N \<and> ownB s i = Q)
\<Longrightarrow> Q_structure s
\<Longrightarrow>\<forall>a b.(a,b)\<in>set(tl(q s))\<longrightarrow> (a\<ge>fst(hd(q s)) + snd(hd(q s)) \<or> a+b<fst(hd(q s)))
\<Longrightarrow> i \<in> {i. fst(hd(q s)) \<le>i \<and> i<fst(hd(q s)) + snd(hd(q s))}
\<Longrightarrow> \<forall>a b.(a,b)\<in>set(tl(q s)) \<longrightarrow> i \<notin> {i. a \<le>i \<and> i<a+b}
"
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(tl(q s))) \<longrightarrow> (a,b)\<in>set(q s)") prefer 2
  apply (metis list.sel(2) list.set_sel(2))
  apply clarify 
  by (meson Suc_leI le_trans less_or_eq_imp_le not_less_eq_eq)
  
  

lemma strange_things_9:
  "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) 
\<longrightarrow> (i \<le> N \<and> ownB s i = Q)

\<Longrightarrow> Q_structure s
\<Longrightarrow>\<forall>a b.(a,b)\<in>set(tl(q s))\<longrightarrow> (a\<ge>fst(hd(q s)) + snd(hd(q s)) \<or> a+b\<le>fst(hd(q s)))
\<Longrightarrow> i \<in> {i. fst(hd(q s)) \<le>i \<and> i<fst(hd(q s)) + snd(hd(q s))}
\<Longrightarrow> \<forall>a b.(a,b)\<in>set(tl(q s)) \<longrightarrow> i \<notin> {i. a \<le>i \<and> i<a+b}\<Longrightarrow>
\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (tl(q s))) \<and> (i \<in> x)) 
\<longrightarrow> (i \<le> N \<and> ownB s i = Q)
"
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(tl(q s))) \<longrightarrow> (a,b)\<in>set(q s)") prefer 2
  apply (metis list.sel(2) list.set_sel(2))
  apply clarify 
  by (metis (mono_tags, lifting) mem_Collect_eq)
  

lemma strange_things_10:
  "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) 
\<longrightarrow> (i \<le> N \<and> ownB s i = Q)
\<Longrightarrow> Q_structure s
\<Longrightarrow>
\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (tl(q s))) \<and> (i \<in> x)) 
\<longrightarrow> (i \<le> N \<and> ownB s i = Q)
"
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(tl(q s))) \<longrightarrow> (a,b)\<in>set(q s)") prefer 2
  apply (metis list.sel(2) list.set_sel(2))
  apply clarify 
  by (metis (mono_tags, lifting) mem_Collect_eq)

lemma strange_things_11_1:
  "Q_structure s
\<Longrightarrow> (i\<le>N \<and> ownB s i = Q)\<longrightarrow>
((\<exists>a b. i\<in> {i. a \<le> i \<and> i < a + b} \<and> ((a, b) \<in> set ([hd(q s)]))) \<or> 
     (i\<in> {i. fst(hd(q s)) \<le> i \<and> i < fst(hd(q s))+snd(hd(q s))}))
\<Longrightarrow>\<forall>i.
 ((\<exists>a b. i\<in> {i. a \<le> i \<and> i < a + b} \<and> ((a, b) \<in> set (tl(q s)))))
\<longrightarrow>((\<exists>a b. i \<in> {i. a \<le> i \<and> i < a + b} \<and> ((a, b) \<in> set ((q s)))) )

"
  by (metis list.sel(2) list.set_sel(2))

lemma strange_things_11_2:
  "Q_structure s
\<Longrightarrow> (i\<le>N \<and> ownB s i = Q)\<longrightarrow>
((\<exists>a b. i\<in> {i. a \<le> i \<and> i < a + b} \<and> ((a, b) \<in> set ([hd(q s)]))) \<or> 
     (i\<in> {i. fst(hd(q s)) \<le> i \<and> i < fst(hd(q s))+snd(hd(q s))}))
\<Longrightarrow> q s\<noteq>[]
\<Longrightarrow>\<forall>i.
 ((\<exists>a b. i\<in> {i. a \<le> i \<and> i < a + b} \<and> ((a, b) \<in> set ([hd(q s)]))))
\<longrightarrow>((\<exists>a b. i \<in> {i. a \<le> i \<and> i < a + b} \<and> ((a, b) \<in> set ((q s)))) )

" 
  by (metis ex_in_conv hd_in_set set_ConsD set_empty)

lemma strange_things_11_3:
  "Q_structure s
\<Longrightarrow> (i\<le>N \<and> ownB s i = Q)\<longrightarrow>
((\<exists>a b. i\<in> {i. a \<le> i \<and> i < a + b} \<and> ((a, b) \<in> set (tl(q s)))) \<or> 
     (i\<in> {i. fst(hd(q s)) \<le> i \<and> i < fst(hd(q s))+snd(hd(q s))}))
\<Longrightarrow>(i \<le> N \<and> ownB s i = Q) \<longrightarrow>
(\<exists>x. (((\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> ((a, b) \<in> set (tl(q s)))) \<and> i \<in> x) \<or> 
     (x = {i. fst(hd(q s)) \<le> i \<and> i < fst(hd(q s))+snd(hd(q s))} \<and> i\<in>x)))"
  by blast


lemma strange_things_11_4:
  "Q_structure s
\<Longrightarrow>(i \<le> N \<and> ownB s i = Q) \<longrightarrow>
(\<exists>x. (((\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> ((a, b) \<in> set (tl(q s)))) \<and> i \<in> x) \<or> 
     (x = {i. fst(hd(q s)) \<le> i \<and> i < fst(hd(q s))+snd(hd(q s))} \<and> i\<in>x)))
\<Longrightarrow> q s\<noteq>[]
\<Longrightarrow> (i\<le>N \<and> ownB s i = Q)\<longrightarrow>
(\<exists>a b. i\<in> {i. a \<le> i \<and> i < a + b} \<and> ((a, b) \<in> set ((q s))))"
  using list.set_sel(2) by fastforce


lemma strange_things_11_5:
  "Q_structure s
\<Longrightarrow> (i\<le>N \<and> ownB s i = Q)\<longrightarrow>
(\<exists>a b. i\<in> {i. a \<le> i \<and> i < a + b} \<and> ((a, b) \<in> set ((q s))))
\<Longrightarrow> q s\<noteq>[]
\<Longrightarrow>(i \<le> N \<and> ownB s i = Q) \<longrightarrow>
(\<exists>x. (((\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> ((a, b) \<in> set (tl(q s)))) \<and> i \<in> x) \<or> 
     (x = {i. fst(hd(q s)) \<le> i \<and> i < fst(hd(q s))+snd(hd(q s))} \<and> i\<in>x)))" 
  by (metis (no_types, lifting) fst_conv list.collapse mem_Collect_eq set_ConsD snd_conv)


lemma strange_things_11_6:
  "Q_structure s
\<Longrightarrow> (i\<le>N \<and> ownB s i = Q)\<longrightarrow>
(\<exists>a b. i\<in> {i. a \<le> i \<and> i < a + b} \<and> ((a, b) \<in> set ((q s))))
\<Longrightarrow> q s\<noteq>[]
\<Longrightarrow> fst(hd(q s)) \<le> i \<longrightarrow> \<not>i < fst(hd(q s))+snd(hd(q s))
\<Longrightarrow>(i \<le> N \<and> ownB s i = Q) \<longrightarrow>
(\<exists>x. (((\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> ((a, b) \<in> set (tl(q s)))) \<and> i \<in> x)))" 
  by (metis (no_types, lifting) fst_conv list.collapse mem_Collect_eq set_ConsD snd_conv)




lemma strange_things_11:
  " Q_structure s
\<Longrightarrow> \<forall>i. (i \<le> N \<and> ownB s i = Q) \<longrightarrow>
(\<exists>x. (((\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> ((a, b) \<in> set (q s))) \<and> i \<in> x)))
\<Longrightarrow> q s\<noteq>[]
\<Longrightarrow>fst(hd(q s))\<le>i\<longrightarrow>\<not>i<fst(hd(q s))+snd(hd(q s))
\<Longrightarrow> (i \<le> N \<and> ownB s i = Q) \<Longrightarrow>
(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (tl (q s))) \<and> i \<in> x)"
  using strange_things_11_6 [where s=s and i=i] 
  by fastforce

lemma strange_things_12:
  " Q_structure s
\<Longrightarrow> \<forall>i. (i \<le> N \<and> ownB s i = Q) \<longrightarrow>
(\<exists>x. (((\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> ((a, b) \<in> set (q s))) \<and> i \<in> x)))
\<Longrightarrow> q s\<noteq>[]
\<Longrightarrow> \<forall>i. (i \<le> N \<and> ownB s i = Q \<and> (fst(hd(q s))\<le>i\<longrightarrow>\<not>i<fst(hd(q s))+snd(hd(q s))) ) \<longrightarrow>
(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (tl (q s))) \<and> i \<in> x)"
  using strange_things_11 [where s=s and i=i] 
  by (simp add: strange_things_11)


lemma R_idle_to_nidle_lemma_case_1_7:
  "con_assms s \<Longrightarrow> pcR s = idleR\<Longrightarrow>pre_R (pcR s) s
  \<Longrightarrow>s'=(s\<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
          numDeqs := Suc (numDeqs s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr>)
\<Longrightarrow>inv s \<Longrightarrow>q s\<noteq>[]
\<Longrightarrow>Q_owns_bytes s'"
  apply(simp add:pre_R_def pre_dequeue_inv_def inv_def)
  apply(simp add: Q_owns_bytes_def )
  apply(simp add:Q_lemmas Q_basic_lemmas) apply(subgoal_tac "Q_structure s") prefer 2 
  using pec_prelim_9 [where s=s] apply presburger
  apply(intro allI conjI)
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(tl(q s))\<longrightarrow> (a\<ge>fst(hd(q s)) + snd(hd(q s)) \<or> a+b<fst(hd(q s)))")
  apply(simp add:Q_indices_def ran_indices_def)
  using strange_things_8 [where s=s and i=i] apply clarsimp 
  (*SMT*)
  defer using strange_things_8_1 [where s=s]   (*Sorry*)
  apply (simp add: pec_prelim_9) 
  using Q_owns_bytes_def apply auto[1]
  
  apply clarify
  apply(intro iffI)
  apply(simp add:Q_indices_def ran_indices_def)  
  defer 
  apply(simp add:Q_indices_def ran_indices_def)
    apply clarify
  apply(subgoal_tac "(i \<le> N \<and> ownB s i = Q)") prefer 2 
     apply fastforce
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> i \<le> N \<and> ownB s i = Q") prefer 2 
  apply presburger
  apply(subgoal_tac "Q_structure s") prefer 2 apply presburger
  apply(subgoal_tac "\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (tl (q s))) \<and> i \<in> x")
  using strange_things_11 [where s=s and i=i]  
     apply blast
  using strange_things_11 [where s=s and i=i]  
    defer
    apply simp
  apply safe[1] apply clarsimp 
  using Suc_leI le_trans less_or_eq_imp_le not_less_eq_eq
proof -
  fix ia :: nat and a :: nat and b :: nat
assume a1: "(a, b) \<in> set (tl (q s))"
  assume a2: "ia < a + b"
assume a3: "a \<le> ia"
assume a4: "ia < fst (hd (q s)) + snd (hd (q s))"
assume a5: "fst (hd (q s)) \<le> ia"
assume a6: "\<forall>a b. (a, b) \<in> set (tl (q s)) \<longrightarrow> fst (hd (q s)) + snd (hd (q s)) \<le> a \<or> a + b < fst (hd (q s))"
  have f7: "\<not> Suc ia \<le> fst (hd (q s))"
    using a5 by simp
  have "\<not> Suc ia \<le> a"
    using a3 by (metis (full_types) not_less_eq_eq)
  then show False
    using f7 a6 a4 a2 a1 by (meson Suc_leI le_trans less_or_eq_imp_le)
next 
  fix ia :: nat and a :: nat and b :: nat
assume a1: "(a, b) \<in> set (tl (q s))"
  assume a2: "ia < a + b"
assume a3: "a \<le> ia"
assume a4: "ia < fst (hd (q s)) + snd (hd (q s))"
assume a5: "fst (hd (q s)) \<le> ia"
assume a6: "\<forall>a b. (a, b) \<in> set (tl (q s)) \<longrightarrow> fst (hd (q s)) + snd (hd (q s)) \<le> a \<or> a + b < fst (hd (q s))"
  have f7: "\<not> Suc ia \<le> fst (hd (q s))"
    using a5 by simp
  have "\<not> Suc ia \<le> a"
    using a3 by (metis (full_types) not_less_eq_eq)
  then show False
    using f7 a6 a4 a2 a1 by (meson Suc_leI le_trans less_or_eq_imp_le)
next
  fix ia :: nat and a :: nat and b :: nat
assume a1: "(a, b) \<in> set (tl (q s))"
  assume a2: "ia < a + b"
assume a3: "a \<le> ia"
assume a4: "ia < fst (hd (q s)) + snd (hd (q s))"
assume a5: "fst (hd (q s)) \<le> ia"
assume a6: "\<forall>a b. (a, b) \<in> set (tl (q s)) \<longrightarrow> fst (hd (q s)) + snd (hd (q s)) \<le> a \<or> a + b < fst (hd (q s))"
  have f7: "\<not> Suc ia \<le> fst (hd (q s))"
    using a5 by simp
  have "\<not> Suc ia \<le> a"
    using a3 by (metis (full_types) not_less_eq_eq)
  then show False
    using f7 a6 a4 a2 a1 by (meson Suc_leI le_trans less_or_eq_imp_le)
next 
  fix ia :: nat and a :: nat and b :: nat
assume a1: "(a, b) \<in> set (tl (q s))"
  assume a2: "ia < a + b"
assume a3: "a \<le> ia"
assume a4: "ia < fst (hd (q s)) + snd (hd (q s))"
assume a5: "fst (hd (q s)) \<le> ia"
assume a6: "\<forall>a b. (a, b) \<in> set (tl (q s)) \<longrightarrow> fst (hd (q s)) + snd (hd (q s)) \<le> a \<or> a + b < fst (hd (q s))"
  have f7: "\<not> Suc ia \<le> fst (hd (q s))"
    using a5 by simp
  have "\<not> Suc ia \<le> a"
    using a3 by (metis (full_types) not_less_eq_eq)
  then show False
    using f7 a6 a4 a2 a1 by (meson Suc_leI le_trans less_or_eq_imp_le)

next show "\<And>i. pcR s = idleR \<Longrightarrow>  s' = s   \<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
            numDeqs := Suc (numReads s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr> \<Longrightarrow>  q s \<noteq> [] \<Longrightarrow>  Q_structure s \<Longrightarrow>   0 < n \<Longrightarrow>   tempR s = (0, 0) \<Longrightarrow>   H s \<le> N \<Longrightarrow>    n < N \<Longrightarrow>    numDeqs s = numReads s \<Longrightarrow>   T s \<le> N \<Longrightarrow>    numEnqs s \<le> n \<Longrightarrow>   ownT s = Q \<Longrightarrow>  hW s \<le> N \<Longrightarrow>   numReads s \<le> numEnqs s \<Longrightarrow>  \<forall>i<n. Data s i \<le> N \<and> 0 < Data s i \<Longrightarrow>  0 < H s \<Longrightarrow>  tW s \<le> N \<Longrightarrow> T s \<noteq> fst (hd (q s)) \<longrightarrow> (\<forall>a b j. (a, b) \<in> set (q s) \<and> j < N \<and> T s \<le> j \<longrightarrow> a + b < j) \<Longrightarrow> \<forall>i. (i < numReads s \<longrightarrow> ownD s i = R) \<and>
             (numReads s \<le> i \<and> i < numWrites s \<longrightarrow> ownD s i = B) \<and> (numWrites s \<le> i \<and> i < n \<longrightarrow> ownD s i = W) \<Longrightarrow>
         \<forall>i. fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) \<longrightarrow> ownB s i = Q \<Longrightarrow>    \<forall>i\<le>N. ownB s i \<noteq> R \<Longrightarrow>  numEnqs s - numReads s = length (q s) \<Longrightarrow>   numReads s \<le> numWrites s \<Longrightarrow>numWrites s \<le> n \<Longrightarrow>\<forall>a b. (a, b) \<in> set (q s) \<longrightarrow> a + b \<le> N \<Longrightarrow>  \<forall>i. i < length (q s) \<and> 0 < i \<longrightarrow>fst (q s ! (i - Suc 0)) + snd (q s ! (i - Suc 0)) = fst (q s ! i) \<or> fst (q s ! i) = 0 \<Longrightarrow>  \<forall>i j. i < length (q s) \<and> j < length (q s) \<and> i \<noteq> j \<longrightarrow> fst (q s ! i) \<noteq> fst (q s ! j) \<Longrightarrow>  \<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a < aa \<longrightarrow> a + b \<le> aa \<Longrightarrow>  \<forall>a. (\<exists>b. (a, b) \<in> set (q s)) \<longrightarrow> a \<noteq> fst (last (q s)) + snd (last (q s)) \<Longrightarrow> \<forall>a b. (a, b) \<in> set (q s) \<longrightarrow> 0 < b \<Longrightarrow> \<forall>i<length (q s). data_index s (q s ! i) = numReads s + i \<Longrightarrow> \<forall>i<length (q s). snd (q s ! i) = Data s (numReads s + i) \<Longrightarrow> \<forall>i<length (q s). ownD s (i + numReads s) = B \<Longrightarrow>  \<forall>i\<le>N. \<forall>j\<le>N. data_index s (i, j) < n \<Longrightarrow> case_1 s \<or> case_2 s \<Longrightarrow> \<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) = (i \<le> N \<and> ownB s i = Q) \<Longrightarrow>
         fst (hd (q s)) \<le> i \<longrightarrow> \<not> i < fst (hd (q s)) + snd (hd (q s)) \<Longrightarrow> i \<le> N \<Longrightarrow> ownB s i = Q \<Longrightarrow>i \<le> N \<and> ownB s i = Q \<Longrightarrow> \<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) \<longrightarrow> i \<le> N \<and> ownB s i = Q \<Longrightarrow>
         Q_structure s \<Longrightarrow> (\<And>m n. m < n \<Longrightarrow> Suc m \<le> n) \<Longrightarrow>(\<And>i j k. i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> i \<le> k) \<Longrightarrow> (\<And>m n. m < n \<or> m = n \<Longrightarrow> m \<le> n) \<Longrightarrow>(\<And>m n. (\<not> m \<le> n) = (Suc n \<le> m)) \<Longrightarrow>\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (tl (q s))) \<and> i \<in> x"
    apply(case_tac "q s=[]") 
     apply blast
    apply(subgoal_tac " \<forall>i. i \<le> N \<and> ownB s i = Q \<longrightarrow> (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x)") prefer 2 
     apply presburger
    apply(subgoal_tac "Q_structure s") prefer 2 apply presburger 
    apply(subgoal_tac "q s\<noteq>[]") prefer 2 apply presburger 
    apply(subgoal_tac "fst (hd (q s)) \<le> i \<longrightarrow> \<not> i < fst (hd (q s)) + snd (hd (q s))") prefer 2 
    apply meson
    using strange_things_12 [where s=s] 
    by blast
next show "\<And>i. pcR s = idleR \<Longrightarrow>  s' = s \<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
            numDeqs := Suc (numReads s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr> \<Longrightarrow>  q s \<noteq> [] \<Longrightarrow>
         Q_structure s \<Longrightarrow>  0 < n \<Longrightarrow> tempR s = (0, 0) \<Longrightarrow>   H s \<le> N \<Longrightarrow>   n < N \<Longrightarrow>numDeqs s = numReads s \<Longrightarrow>
         T s \<le> N \<Longrightarrow> numEnqs s \<le> n \<Longrightarrow> ownT s = Q \<Longrightarrow>   hW s \<le> N \<Longrightarrow>   numReads s \<le> numEnqs s \<Longrightarrow>    \<forall>i<n. Data s i \<le> N \<and> 0 < Data s i \<Longrightarrow>
         0 < H s \<Longrightarrow> tW s \<le> N \<Longrightarrow>  T s \<noteq> fst (hd (q s)) \<longrightarrow> (\<forall>a b j. (a, b) \<in> set (q s) \<and> j < N \<and> T s \<le> j \<longrightarrow> a + b < j) \<Longrightarrow>
         \<forall>i. (i < numReads s \<longrightarrow> ownD s i = R) \<and> (numReads s \<le> i \<and> i < numWrites s \<longrightarrow> ownD s i = B) \<and> (numWrites s \<le> i \<and> i < n \<longrightarrow> ownD s i = W) \<Longrightarrow>
         \<forall>i. fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) \<longrightarrow> ownB s i = Q \<Longrightarrow> \<forall>i\<le>N. ownB s i \<noteq> R \<Longrightarrow>
         numEnqs s - numReads s = length (q s) \<Longrightarrow>  numReads s \<le> numWrites s \<Longrightarrow>  numWrites s \<le> n \<Longrightarrow>  \<forall>a b. (a, b) \<in> set (q s) \<longrightarrow> a + b \<le> N \<Longrightarrow>    \<forall>i. i < length (q s) \<and> 0 < i \<longrightarrow>
             fst (q s ! (i - Suc 0)) + snd (q s ! (i - Suc 0)) = fst (q s ! i) \<or> fst (q s ! i) = 0 \<Longrightarrow>  \<forall>i j. i < length (q s) \<and> j < length (q s) \<and> i \<noteq> j \<longrightarrow> fst (q s ! i) \<noteq> fst (q s ! j) \<Longrightarrow> \<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a < aa \<longrightarrow> a + b \<le> aa \<Longrightarrow>  \<forall>a. (\<exists>b. (a, b) \<in> set (q s)) \<longrightarrow> a \<noteq> fst (last (q s)) + snd (last (q s)) \<Longrightarrow>  \<forall>a b. (a, b) \<in> set (q s) \<longrightarrow> 0 < b \<Longrightarrow>   \<forall>i<length (q s). data_index s (q s ! i) = numReads s + i \<Longrightarrow> \<forall>i<length (q s). snd (q s ! i) = Data s (numReads s + i) \<Longrightarrow>  \<forall>i<length (q s). ownD s (i + numReads s) = B \<Longrightarrow>  \<forall>i\<le>N. \<forall>j\<le>N. data_index s (i, j) < n \<Longrightarrow>  case_1 s \<or> case_2 s \<Longrightarrow>  \<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) = (i \<le> N \<and> ownB s i = Q) \<Longrightarrow>
         fst (hd (q s)) \<le> i \<longrightarrow> \<not> i < fst (hd (q s)) + snd (hd (q s)) \<Longrightarrow>  \<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (tl (q s))) \<and> i \<in> x \<Longrightarrow>   (\<And>m n. m < n \<Longrightarrow> Suc m \<le> n) \<Longrightarrow> (\<And>i j k. i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> i \<le> k) \<Longrightarrow>   (\<And>m n. m < n \<or> m = n \<Longrightarrow> m \<le> n) \<Longrightarrow> (\<And>m n. (\<not> m \<le> n) = (Suc n \<le> m)) \<Longrightarrow> i \<le> N \<and> ownB s i = Q" 

  proof -
    fix i :: nat
    assume a1: "q s \<noteq> []"
    assume a2: "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) = (i \<le> N \<and> ownB s i = Q)"
    assume a3: "\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (tl (q s))) \<and> i \<in> x"
    have "\<forall>n. ((\<exists>N. n \<in> N \<and> (\<exists>n na. (n, na) \<in> set (q s) \<and> {nb. n \<le> nb \<and> nb < n + na} = N)) \<or> Q \<noteq> ownB s n \<or> \<not> n \<le> N) \<and> (Q = ownB s n \<and> n \<le> N \<or> (\<forall>N. n \<notin> N \<or> (\<forall>n na. (n, na) \<notin> set (q s) \<or> {nb. n \<le> nb \<and> nb < n + na} \<noteq> N)))"
      using a2 by (metis (full_types))
    then show "i \<le> N \<and> ownB s i = Q"
      using a3 a1 by (metis (no_types) list.set_sel(2))
  qed
qed



lemma R_read_to_release_lemma_1:
  "con_assms s \<Longrightarrow> pcR s = Read\<Longrightarrow>pre_Read_inv s
  \<Longrightarrow>s'=(s\<lparr>tR := T s, numReads := Suc (data_index s (tempR s)),
          pcR := Release,
          ownD :=
            \<lambda>i. if i = data_index s (tempR s) then R
                 else ownD
                       (s\<lparr>tR := T s,
                            numReads := Suc (data_index s (tempR s)),
                            pcR := Release\<rparr>)
                       i\<rparr>)
\<Longrightarrow>inv s 
\<Longrightarrow>i>0\<longrightarrow>ownB s' i = ownB s i \<and> T s = T s' \<and> H s = H s' \<and>
  tempR s = tempR s' \<and> offset s = offset s' \<and> Data s (numEnqs s) = Data s' (numEnqs s')
  \<and> q s = q s' \<and> ownT s = ownT s'"
  by simp


lemma R_read_to_release_lemma_case_1:
  "con_assms s \<Longrightarrow> pcR s = Read\<Longrightarrow>pre_Read_inv s
  \<Longrightarrow>s'=(s\<lparr>tR := T s, numReads := Suc (data_index s (tempR s)),
          pcR := Release,
          ownD :=
            \<lambda>i. if i = data_index s (tempR s) then R
                 else ownD
                       (s\<lparr>tR := T s,
                            numReads := Suc (data_index s (tempR s)),
                            pcR := Release\<rparr>)
                       i\<rparr>)
\<Longrightarrow>inv s 
\<Longrightarrow>case_1 s
\<Longrightarrow>case_1 s'"
  by(simp add:case_1_def)

lemma R_read_to_release_lemma_case_2:
  "con_assms s \<Longrightarrow> pcR s = Read\<Longrightarrow>pre_Read_inv s
  \<Longrightarrow>s'=(s\<lparr>tR := T s, numReads := Suc (data_index s (tempR s)),
          pcR := Release,
          ownD :=
            \<lambda>i. if i = data_index s (tempR s) then R
                 else ownD
                       (s\<lparr>tR := T s,
                            numReads := Suc (data_index s (tempR s)),
                            pcR := Release\<rparr>)
                       i\<rparr>)
\<Longrightarrow>inv s 
\<Longrightarrow>case_2 s
\<Longrightarrow>case_2 s'"
  by(simp add:case_2_def)

lemma R_read_to_release_lemma_2:
  "con_assms s \<Longrightarrow> pcR s = Read\<Longrightarrow>pre_Read_inv s
  \<Longrightarrow>s'=(s\<lparr>tR := T s, numReads := Suc (data_index s (tempR s)),
          pcR := Release,
          ownD :=
            \<lambda>i. if i = data_index s (tempR s) then R
                 else ownD
                       (s\<lparr>tR := T s,
                            numReads := Suc (data_index s (tempR s)),
                            pcR := Release\<rparr>)
                       i\<rparr>)
\<Longrightarrow>inv s 
\<Longrightarrow>Q_owns_bytes s
\<Longrightarrow>Q_owns_bytes s'"
  by(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)

lemma T_modification_rule:
  "s'=(s\<lparr>T := fst (tempR s) + Data s (numReads s - Suc 0)\<rparr>) \<Longrightarrow> T s' = fst (tempR s) + Data s (numReads s - Suc 0)"
  by simp

lemma T_modification_rule_2:
  "s'=(s\<lparr>ownT := Q,
          ownB :=
            \<lambda>i. if (if T s \<le> i \<and> i < N then B else ownB (s\<lparr>ownT := Q\<rparr>) i) = R \<and> i \<le> N then B
                else ownB (setownB [(tR s, N) B] (s\<lparr>ownT := Q\<rparr>)) i,
          tempR := (0, 0), pcR := idleR, T := fst (tempR s) + Data s (numReads s - Suc 0)\<rparr>) \<Longrightarrow> T s' = fst (tempR s) + Data s (numReads s - Suc 0)"
  by simp

lemma T_push:
  " T s = fst (tempR s) \<Longrightarrow>s'=s \<lparr>ownT := Q,
          ownB :=
            \<lambda>i. if ownB s i = R \<and> i \<le> N then B
                else ownB ((if T s \<noteq> fst (tempR s) then setownB [(tR s, N) B] else id) (s\<lparr>ownT := Q\<rparr>)) i,
          tempR := (0, 0), pcR := idleR, T := fst (tempR s) + Data s (numReads s - Suc 0)\<rparr> \<Longrightarrow>
T s' = fst (tempR s) + Data s (numReads s - Suc 0)"
  by simp

lemma T_push_2 :
  " T s = fst (tempR s) \<Longrightarrow>s'=(s\<lparr>ownT := Q, ownB := \<lambda>i. if ownB s i = R \<and> i \<le> N then B else ownB (id (s\<lparr>ownT := Q\<rparr>)) i, tempR := (0, 0), pcR := idleR,
          T := fst (tempR s) + Data s (numReads s - Suc 0)\<rparr>) \<Longrightarrow>
T s' = fst (tempR s) + Data s (numReads s - Suc 0)"
  by simp

lemma R_release_to_idle_lemma_1:
  "con_assms s \<Longrightarrow> pcR s = Release \<Longrightarrow> pre_Release_inv s
  \<Longrightarrow> s'=s \<lparr>ownT := Q,
          ownB :=
            \<lambda>i. if ownB s i = R \<and> i \<le> N then B
                else ownB ((if T s \<noteq> fst (tempR s) then setownB [(tR s, N) B] else id) (s\<lparr>ownT := Q\<rparr>)) i,
          tempR := (0, 0), pcR := idleR, T := fst (tempR s) + Data s (numReads s - Suc 0)\<rparr>
\<Longrightarrow>inv s \<Longrightarrow> T s = fst (tempR s)
\<Longrightarrow>case_1 s
\<Longrightarrow>case_1 s'"
  apply (simp add:inv_def)       
  apply(simp add:pre_Release_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(subgoal_tac "T s' = fst (tempR s) + Data s (numReads s - Suc 0)") prefer 2 
  using T_push [where s =s and s'=s'] 
  apply fastforce
  apply(simp add:case_1_def)
  apply clarify 
  apply(rule_tac ?x = "b" in exI)
  apply(rule_tac ?x = "b" in exI) 
  apply(intro conjI impI)
  apply fastforce 
  apply(rule_tac ?x = "c" in exI) 
  apply(intro conjI impI) 
  apply blast
  apply blast 
  apply (metis (no_types, lifting) le_trans less_or_eq_imp_le linorder_neqE_nat)
  apply (metis Suc_leI not_less_eq_eq)
  apply (metis F.distinct(11)) 
  apply (metis F.distinct(1)) 
  apply metis    
  apply meson
  apply (metis le_add_diff_inverse)
  apply meson
  apply meson
  apply fastforce
  apply blast
  apply blast
  apply meson
  by meson



lemma R_release_nequal_case_2:
  "con_assms s \<Longrightarrow> pcR s = Release \<Longrightarrow> pre_Release_inv s
\<Longrightarrow>inv s \<Longrightarrow> T s \<noteq> fst (tempR s)
\<Longrightarrow>case_2 s"
  apply (simp add:inv_def)       
  apply(simp add:pre_Release_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) 
  apply(simp add:case_1_def)
  apply(subgoal_tac "H s>T s") prefer 2 
  apply metis
  apply(simp add:case_2_def)
  by metis


lemma R_release_nequal_case_2_2:
  "con_assms s \<Longrightarrow> pcR s = Release \<Longrightarrow> pre_Release_inv s
\<Longrightarrow>inv s \<Longrightarrow> T s \<noteq> fst (tempR s) \<Longrightarrow> s' = s
    \<lparr>ownT := Q,
       ownB :=
         \<lambda>i. if (if T s \<le> i \<and> i < N then B else ownB (s\<lparr>ownT := Q\<rparr>) i) = R \<and> i \<le> N then B
             else ownB ((if T s \<noteq> fst (tempR s) then setownB [(tR s, N) B] else id) (s\<lparr>ownT := Q\<rparr>)) i,
       tempR := (0, 0), pcR := idleR, T := fst (tempR s) + Data s (numReads s - Suc 0)\<rparr>
\<Longrightarrow>case_1 s'"
  apply(subgoal_tac "case_2 s") prefer 2 using  R_release_nequal_case_2 [where s=s]
  apply blast
  apply (simp add:inv_def)
  apply(simp add:pre_Release_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(subgoal_tac "H s < T s") prefer 2 
  apply(simp add:case_2_def)
  apply meson
  apply(simp add:case_2_def case_1_def)
  apply clarify
  apply(rule_tac ?x = "a" in exI)
  apply(rule_tac ?x = "a" in exI)
  apply(intro conjI impI)
  apply blast
  apply(rule_tac ?x = "b" in exI)
  apply(intro conjI impI)
  apply blast
  apply blast
  apply (metis add_cancel_left_left le_trans less_or_eq_imp_le)
  apply (metis le_antisym less_irrefl_nat less_or_eq_imp_le)
  apply (metis F.distinct(11) F.distinct(21) gr0_conv_Suc nat.discI nat_less_le)
  apply (metis F.distinct(1))
  apply (metis nat_le_linear nat_less_le)
  apply meson
  apply (metis add_cancel_right_left)
  apply fastforce
  apply meson
  apply force
  apply blast
  apply (metis add_cancel_left_left diff_self_eq_0 le_neq_implies_less)
  apply (metis le_neq_implies_less)
  by meson


lemma R_release_nequal_case_1_1:
  "con_assms s \<Longrightarrow> pcR s = Release \<Longrightarrow> pre_Release_inv s
\<Longrightarrow>inv s \<Longrightarrow> T s = fst (tempR s) \<Longrightarrow> s'=(s\<lparr>ownT := Q, ownB := \<lambda>i. if ownB s i = R \<and> i \<le> N then B else ownB (id (s\<lparr>ownT := Q\<rparr>)) i, tempR := (0, 0), pcR := idleR,
          T := fst (tempR s) + Data s (numReads s - Suc 0)\<rparr>) \<Longrightarrow> case_1 s
\<Longrightarrow>case_1 s'"
  apply (simp add:inv_def)       
  apply(simp add:pre_Release_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(subgoal_tac "T s' = fst (tempR s) + Data s (numReads s - Suc 0)") prefer 2 
  using T_push_2 [where s=s and s'=s']
  apply fastforce
  apply(simp add:case_1_def) 
  apply clarify 
  apply(rule_tac ?x = "b" in exI)
  apply(rule_tac ?x = "b" in exI) 
  apply(intro conjI impI)
  apply fastforce 
  apply(rule_tac ?x = "c" in exI) 
  apply(intro conjI impI) 
  apply blast
  apply blast
  apply (metis diff_commute diff_diff_cancel diff_is_0_eq' less_nat_zero_code linorder_neqE_nat nat_le_linear zero_less_diff)
  apply (metis le_imp_less_Suc not_less_eq)
  apply (metis F.distinct(11))
  apply (metis F.distinct(1))
  apply metis
  apply blast
  apply (metis le_add_diff_inverse)
  apply meson
  apply fastforce
  apply fastforce
  apply force
  apply blast
  apply meson
  by fastforce



lemma R_release_equal_case_2_3:
  "con_assms s \<Longrightarrow> pcR s = Release \<Longrightarrow> pre_Release_inv s
\<Longrightarrow>inv s \<Longrightarrow> T s = fst (tempR s) \<Longrightarrow> s'=(s\<lparr>ownT := Q, ownB := \<lambda>i. if ownB s i = R \<and> i \<le> N then B else ownB (id (s\<lparr>ownT := Q\<rparr>)) i, tempR := (0, 0), pcR := idleR,
          T := fst (tempR s) + Data s (numReads s - Suc 0)\<rparr>) \<Longrightarrow> case_2 s
\<Longrightarrow>case_2 s'"
  apply (simp add:inv_def)       
  apply(simp add:pre_Release_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(subgoal_tac "T s' = fst (tempR s) + Data s (numReads s - Suc 0)") prefer 2 
  using T_push_2 [where s =s and s'=s'] 
  apply fastforce apply(simp_all)
  apply(simp add:case_2_def)
  apply clarify 
  apply(rule_tac ?x = "0" in exI)
  apply(rule_tac ?x = "b" in exI) 
  apply(intro conjI impI)
  apply fastforce 
  apply(rule_tac ?x = "H s" in exI) 
  apply(intro conjI impI) 
  apply fastforce
  apply(rule_tac ?x = "e" in exI)
  apply(intro conjI impI) 
  apply (metis le_add_diff_inverse trans_less_add1)
  apply(rule_tac ?x = "e" in exI)
  apply(intro conjI impI) 
  apply fastforce
  apply(rule_tac ?x = "f" in exI)
  apply(intro conjI impI) 
  apply fastforce
  apply blast
  apply blast
  apply (metis F.distinct(11) less_nat_zero_code)
  apply (metis F.distinct(1))
  apply (metis (mono_tags, hide_lams) diff_is_0_eq' le_trans linorder_neqE_nat nat_le_linear zero_less_diff)
  apply (metis le_imp_less_Suc not_less_eq)
  apply (metis F.distinct(11))
  apply (metis F.distinct(15))
  apply fastforce
  apply blast
  apply blast
  apply blast
  apply blast
  apply (metis gr_implies_not_zero le_add_diff_inverse)
  apply blast
  apply meson
  apply meson
  apply blast
  apply fastforce
  apply blast
  apply (metis less_nat_zero_code)
  apply meson
  apply (metis less_nat_zero_code)
  apply (metis less_nat_zero_code)
  by (metis less_nat_zero_code)



  




lemma Q_continues_to_own_through_release:
  "Q_owns_bytes s \<Longrightarrow> inv s \<Longrightarrow> cR_step (pcR s) s s' \<Longrightarrow> pcR s = Release 
  \<Longrightarrow> pre_Release_inv s
  \<Longrightarrow> Q_owns_bytes s'"
  apply simp
  apply(simp add:Q_lemmas Q_basic_lemmas inv_def pre_Release_inv_def)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:cR_step_def)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply metis
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s") 
  by (metis F.distinct(21) nat_less_le)



lemma Q_structure_continues_to_own_through_release:
  "Q_structure s \<Longrightarrow> inv s \<Longrightarrow> cR_step (pcR s) s s' \<Longrightarrow> pcR s = Release 
  \<Longrightarrow> pre_Release_inv s
  \<Longrightarrow> Q_structure s'"
  apply simp
  apply(simp add:Q_lemmas Q_basic_lemmas inv_def pre_Release_inv_def)
  by(simp add:cR_step_def)




(************************************Local R_step shows inv  *********************************************)


lemma R_local_release_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcR s = Release"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "inv s'"
  using assms apply simp 
  apply(subgoal_tac "Q_owns_bytes s") prefer 2
  using inv_def
  apply blast
  apply(subgoal_tac "inv s") prefer 2 
  apply blast
  apply(subgoal_tac "cR_step (pcR s) s s'") prefer 2
  apply metis
  apply(subgoal_tac "pcR s = Release ") prefer 2
   apply metis 
  apply(subgoal_tac "pre_Release_inv s") prefer 2 
  apply(simp add:pre_R_def)
  apply(subgoal_tac "Q_owns_bytes s'") prefer 2
  using Q_continues_to_own_through_release [where s=s and s'=s'] 
  apply blast
  apply(subgoal_tac "Q_structure s") prefer 2 using inv_def
  apply blast
  apply(subgoal_tac "Q_structure s'") prefer 2 
  using Q_structure_continues_to_own_through_release [where s=s and s'=s']
  apply blast
(*prelimiaries go here*)
  apply(simp add:inv_def)
  apply(subgoal_tac "inv s") prefer 2 
  using assms(1) apply linarith
  apply(simp add:pre_R_def)
  apply(subgoal_tac "B_release s s'") prefer 2 using B_release_def [where s=s and s'=s']
  apply (metis PCR.simps(7) cR_step_def) 
  apply(subgoal_tac "ownT s = R") prefer 2 using pre_Release_inv_def [where s=s] 
  apply presburger
  apply(subgoal_tac "Q_structure s'")
  using Q_structure_preserved3 [where s=s and s'=s']  prefer 2 
  apply (metis \<open>B_release s s' \<equiv> s' = (`T := end (tempR s) \<circ> `pcR := idleR \<circ> `tempR := (0, 0) \<circ> transownB [R B] \<circ> (if tR s \<noteq> fst (tempR s) then setownB [(tR s, N) B] else id) \<circ> transownT [R Q s]) s\<close> end_simp len_def off_def)
  apply(simp add:pre_Release_inv_def)
  apply(intro conjI impI) apply(simp add:tempR_lemmas tempR_basic_lemmas) prefer 2
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply(case_tac "T s \<noteq> fst (tempR s)", simp_all)
  apply(subgoal_tac "T s \<noteq> fst (tempR s)") prefer 2 
  apply blast
  apply(subgoal_tac "pre_R Release s") prefer 2 using assms 
  apply presburger
  apply(simp add:pre_R_def)
  apply(subgoal_tac "pre_Release_inv s") prefer 2
  apply blast
  apply(subgoal_tac "case_2 s") prefer 2
  using R_release_nequal_case_2 [where s=s]
  using assms(2) apply fastforce
  apply(simp_all)
  apply(subgoal_tac "case_1 s'") prefer 2 using R_release_nequal_case_2_2 [where s'=s' and s=s] 
  using assms(2) apply blast
  apply presburger
  apply(case_tac "case_1 s", simp_all)
  apply(case_tac[!] "T s = fst(tempR s)") apply(simp_all)
  apply(subgoal_tac "case_1 s'") 
  using R_release_nequal_case_1_1 [where s=s and s'=s'] 
  apply presburger
  apply(subgoal_tac "pre_R (pcR s) s") prefer 2 
  using assms(4) apply blast
  apply(simp add:pre_R_def) apply(subgoal_tac "pre_Release_inv s") prefer 2 
  apply blast
  using R_release_nequal_case_1_1 [where s=s and s'=s']
  using assms(2) apply presburger
  apply(subgoal_tac "case_2 s'")
  using R_release_equal_case_2_3 [where s=s and s'=s']
  apply presburger
  apply(subgoal_tac "pre_R (pcR s) s") prefer 2 
  using assms(4) apply blast
  apply(simp add:pre_R_def) apply(subgoal_tac "pre_Release_inv s") prefer 2 
  apply blast
  using R_release_equal_case_2_3 [where s=s and s'=s']
  using assms(2) by presburger



lemma R_local_idle_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcR s = idleR"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "inv s'"
  using assms apply simp
  apply(simp add:pre_R_def cR_step_def)
  apply(case_tac "q s=[]")  apply(case_tac "pcR s'") apply (simp,simp,simp)
  apply(subgoal_tac "Q_structure s'") prefer 2 
  using Q_structure_preserved1 [where s=s and s'=s'] inv_def
  apply meson 
  apply (simp add: RingBuffer_BD_latest_2.inv_def)  apply simp
  apply(simp add:pre_dequeue_inv_def)
  apply(subgoal_tac "s'=(s\<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
          numDeqs := Suc (numDeqs s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr>)
") prefer 2 
  apply presburger
  apply(subgoal_tac "Q_owns_bytes s'") prefer 2
  using R_idle_to_nidle_lemma_case_1_7 [where s=s and s'=s'] assms
  apply fastforce
  apply(simp add:inv_def)
  apply(clarify)
  apply(intro conjI impI)
  apply (metis add.right_neutral add_Suc_right diff_diff_left)
  apply (metis diff_is_0_eq length_0_conv not_less_eq_eq)
  apply (metis diff_is_0_eq' le_trans length_0_conv not_less_eq_eq)
  apply(case_tac "case_1 s") apply simp 
  apply(subgoal_tac "case_1 s'\<longrightarrow>case_1 s' \<or> case_2 s'") prefer 2
  apply linarith
  apply(subgoal_tac "case_1 s'") 
  apply blast
  apply simp 
  using R_idle_to_nidle_lemma_case_1_5 [where s=s and s'=s'] 
  using assms(1) assms(2) assms(4) 
  apply presburger
  apply(subgoal_tac "case_2 s") prefer 2
  apply blast
  apply(thin_tac "\<not>case_1 s") apply simp 
  using R_idle_to_nidle_lemma_case_1_6 [where s=s and s'=s'] 
  using assms(1) assms(2) assms(4) by presburger



lemma R_local_read_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcR s = Read"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "inv s'"
  using assms apply simp
  apply(simp add:inv_def)
  apply(simp add:pre_R_def)
  apply(subgoal_tac "B_read s s'") prefer 2 using B_read_def [where s=s and s'=s'] 
   apply (metis PCR.simps(9) cR_step_def)
  apply(subgoal_tac "ownT s = R") prefer 2 using pre_Read_inv_def [where s=s] 
  apply presburger
  apply(subgoal_tac "Q_structure s'")
  using Q_structure_preserved2 [where s=s and s'=s']  prefer 2
  apply blast
  apply(simp add:pre_Read_inv_def)
  apply(intro conjI impI)
  apply (metis F.distinct(5) le_antisym le_eq_less_or_eq not_less_eq_eq)
  apply (metis F.distinct(5) Suc_leI le_eq_less_or_eq not_less_eq_eq)
   apply(case_tac "case_1 s")
    apply(subgoal_tac "case_1 s'")
     apply fastforce
  apply(subgoal_tac "pre_Read_inv s") prefer 2
  apply (metis PCR.simps(9) assms(4) pre_R_def)
  using R_read_to_release_lemma_case_1 [where s=s and s'=s']
  using assms(1) assms(2) apply fastforce
  apply(subgoal_tac "case_2 s") prefer 2
    apply blast
   apply(thin_tac "\<not>case_1 s") 
  apply(subgoal_tac "case_2 s'")
  apply force
  using R_read_to_release_lemma_case_2 [where s=s and s'=s']
  apply (metis PCR.simps(9) assms(1) assms(2) assms(4) pre_R_def)
  using R_read_to_release_lemma_2 [where s=s and s'=s']
  by (metis PCR.simps(9) assms(1) assms(2) assms(4) pre_R_def)


lemma R_step_preserves_inv:
  assumes "inv s"
  and "con_assms s"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "inv s'"
  using assms apply(case_tac "pcR s") 
  using R_local_release_lemma [where s=s and s'=s'] apply blast       
  using R_local_idle_lemma [where s=s and s'=s'] apply blast         
  using R_local_read_lemma [where s=s and s'=s'] by blast         









(*******************************LOCAL W_step shows inv s'*************************************)


lemma W_inv_A1_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A1"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"    
shows "inv s'"
  using assms apply(simp add:inv_def pre_W_def cW_step_def pre_A1_inv_def)
  apply (intro conjI impI)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s")
  apply(simp add:case_1_def)
  apply(simp add:case_2_def)
  by(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)




lemma W_inv_A2_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A2"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"    
shows "inv s'"
  using assms apply(simp add:inv_def pre_W_def cW_step_def pre_A2_inv_def)
  apply(case_tac "tW s = hW s", simp_all)
  apply(intro conjI impI)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply (elim conjE disjE)
  apply(case_tac "case_1 s'") 
  using case_trans_A2_to_A3_2 [where s=s]
  apply blast 
  using \<open>\<And>s'. \<lbrakk>s' = s\<lparr>ownT := W, pcW := A3\<rparr>; T s = H s; case_1 s\<rbrakk> \<Longrightarrow> case_1 s'\<close> apply presburger
  apply (metis case_split_2 le_refl)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(case_tac "hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s", simp_all)
  apply(intro conjI impI)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply (elim conjE disjE)
  apply(subgoal_tac "\<not>case_1 s") prefer 2
  apply (metis case_split_4 less_eqE trans_less_add1)
  apply meson
  apply(subgoal_tac "case_2 s'")
  apply blast apply simp
  using  case_trans_A2_to_A4_3 [where s=s]
  apply (meson case_split_2 not_less)
  apply (metis case_trans_A2_to_A4_2)
  apply (metis case_split_2)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(case_tac "tW s < hW s", simp_all)
  apply(intro conjI impI)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply (metis case_split_2 case_trans_A2_to_A5_2)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(intro conjI impI)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply (elim conjE disjE)
  apply (metis case_split_4 less_eqE linorder_neqE_nat trans_less_add1)
  apply (metis case_split_2 case_trans_A2_to_A8_4 linear nat_less_le)
  apply (metis case_trans_A2_to_A8_2)
  apply (metis case_split_2)
  by(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)



lemma W_inv_A3_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A3"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"    
shows "inv s'"
  using assms apply(simp add:inv_def pre_W_def cW_step_def pre_A3_inv_def)
  apply(intro conjI impI)
  apply(simp add:Q_lemmas Q_basic_lemmas) defer
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def) 
  apply(subgoal_tac "case_1 s") prefer 2 
  apply (metis RingBuffer_BD_latest_2.case_split le_refl)
  apply(subgoal_tac "\<not>case_2 s'") prefer 2 
  using case_trans_A3_to_write_2 [where s=s and s'=s'] 
  apply (simp add: assms(1) pre_A3_inv_def)
  apply simp
  using case_trans_A3_to_write_7 [where s=s]
  by (simp add: assms(1) pre_A3_inv_def)


lemma W_inv_A4_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A4"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"    
shows "inv s'"
  using assms apply(simp add:inv_def pre_W_def cW_step_def)
  apply(intro conjI impI)  apply(simp add:inv_def pre_W_def cW_step_def pre_A4_inv_def)
  apply (simp add: less_diff_conv)  apply(simp add:inv_def pre_W_def cW_step_def pre_A4_inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas) defer  apply(simp add:inv_def pre_W_def cW_step_def pre_A4_inv_def)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)  
  apply (metis (no_types, lifting) F.distinct(19) add.commute add_lessD1 canonically_ordered_monoid_add_class.lessE less_diff_conv) 
  apply(case_tac "T s\<ge>tW s")
  apply(subgoal_tac "case_2 s'") prefer 2 
  using case_trans_A4_to_write_7 [where s=s and s'=s'] 
  apply (simp add: assms(1) assms(2) pre_A4_inv_def)
  apply meson 
  using case_trans_A4_to_write_9 [where s=s and s'=s'] 
  using assms(1) pre_A4_inv_def by auto



lemma W_inv_A5_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A5"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"    
shows "inv s'"
  using assms apply(simp add:inv_def pre_W_def cW_step_def pre_A5_inv_def)
  apply(case_tac "Data s (numEnqs s) \<le> N - hW s", simp_all) defer
  apply(case_tac "Data s (numEnqs s) < tW s", simp_all) defer defer
  apply(intro conjI impI) apply(simp add:Q_lemmas Q_basic_lemmas)
  prefer 2 
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def) defer
  apply(intro conjI impI) apply(simp add:Q_lemmas Q_basic_lemmas)
  prefer 2 
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def) defer
  apply(intro conjI impI) apply(simp add:Q_lemmas Q_basic_lemmas)
  prefer 2 
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def) defer
  using case_trans_A5_to_A6_3 [where s=s and s'=s'] 
  apply (metis PCW.simps(187) assms(1) assms(2) assms(4) pre_W_def)
  using case_trans_A5_to_A6_6 [where s=s and s'=s']
  apply (simp add: assms(1) pre_A5_inv_def)
  using case_trans_A5_to_A6_9 [where s=s and s'=s']
  by (metis case_split_2 case_trans_A2_to_A8_2)



lemma W_inv_A6_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A6"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"    
shows "inv s'"
  using assms apply(simp add:inv_def pre_W_def cW_step_def pre_A6_inv_def)
  apply(intro conjI impI)
  apply (metis Nat.le_diff_conv2 add.commute)
  apply(simp add:Q_lemmas Q_basic_lemmas) prefer 2
   apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def) prefer 2 
  using case_trans_A6_to_write_7 [where s=s and s'=s']
  apply (metis (no_types, lifting) PCW.simps(188) assms(1) assms(2) assms(4) pre_W_def)
  by (smt (z3) F.distinct(19) diff_add_inverse le_diff_iff le_neq_implies_less le_trans less_imp_add_positive less_or_eq_imp_le not_add_less1)



lemma W_inv_A7_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A7"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"    
shows "inv s'"
  using assms apply(simp add:inv_def pre_W_def cW_step_def pre_A7_inv_def)
  apply(intro conjI impI)
  apply(simp add:Q_lemmas Q_basic_lemmas) prefer 2
   apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def) 
  using case_trans_A7_to_write_7 [where s=s and s'=s'] 
  by (metis (no_types, lifting) PCW.simps(189) assms(1) assms(2) assms(4) pre_W_def)
  




lemma W_inv_A8_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A8"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"    
shows "inv s'"
  using assms apply(simp add:inv_def pre_W_def cW_step_def pre_A8_inv_def)
  apply(intro conjI impI)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(case_tac "N < Data s (numEnqs s)", simp_all)
  apply (metis leD)
  apply (metis leD)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_def) 
  apply(simp add:case_2_def)
  by(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)


lemma W_inv_Enqueue_lemma_prelim_1:
  "inv s \<Longrightarrow> con_assms s \<Longrightarrow> pcW s = Enqueue \<Longrightarrow> pre_W (pcW s) s \<Longrightarrow> cW_step (pcW s) s s'
  \<Longrightarrow> q s= []
\<Longrightarrow> Q_structure s'"
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac " q s' = [(offset s, Data s (numDeqs s))]")
  prefer 2 apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply (metis le_antisym)
  apply(intro conjI impI)
  apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) 
  apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis gr0I)
  apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  by (metis le_antisym)

lemma W_inv_Enqueue_lemma_prelim_2:
  "con_assms s \<Longrightarrow> pcW s = Enqueue \<Longrightarrow> cW_step (pcW s) s s'
  \<Longrightarrow> ownT s \<noteq> W
\<Longrightarrow> q s @ [(offset s, Data s (numEnqs s))] = q s'"
  apply simp
  by(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)

lemma W_inv_Enqueue_lemma_prelim_3:
  "inv s \<Longrightarrow> con_assms s \<Longrightarrow> pcW s = Enqueue \<Longrightarrow> pre_W (pcW s) s \<Longrightarrow> cW_step (pcW s) s s'
  \<Longrightarrow> ownT s \<noteq> W \<Longrightarrow> q s = []
\<Longrightarrow> Q_structure s'"
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac " q s' = [(offset s, Data s (numDeqs s))]")
  prefer 2 apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply (metis le_antisym)
  apply(intro conjI impI)
  apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) 
  apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis gr0I)
  apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  by (metis le_antisym)

lemma W_inv_Enqueue_lemma_prelim_4:
  "\<forall>a b. (a, b) \<in> set (q s) \<longrightarrow> a + b \<le> N \<Longrightarrow> offset s + Data s (numEnqs s)\<le>N
\<Longrightarrow>q s @ [(offset s, Data s (numEnqs s))] = q s'
\<Longrightarrow> \<forall>a b. (a, b) \<in> set (q s') \<longrightarrow> a + b \<le> N"
  by (metis old.prod.inject rotate1.simps(2) set_ConsD set_rotate1)


lemma W_inv_Enqueue_lemma_prelim_5:
  "length(q s)>0\<Longrightarrow>\<forall>i. i < length (q s) \<and> 0 < i \<longrightarrow>
        fst (q s ! (i - Suc 0)) + snd (q s ! (i - Suc 0)) = fst (q s ! i) \<or> fst (q s ! i) = 0 \<Longrightarrow>
offset s = fst(last(q s)) + snd(last(q s)) \<or> offset s = 0
\<Longrightarrow>q s @ [(offset s, Data s (numEnqs s))] = q s'
\<Longrightarrow> \<forall>i. i < length (q s') \<and> 0 < i \<longrightarrow>
        fst (q s' ! (i - Suc 0)) + snd (q s' ! (i - Suc 0)) = fst (q s' ! i) \<or> fst (q s' ! i) = 0"
  apply (subgoal_tac "last(q s) = q s!(length(q s)-1)") prefer 2 
  using last_conv_nth apply blast
  by (smt (z3) One_nat_def Suc_diff_1 Suc_less_eq fst_conv length_append_singleton less_antisym nth_append nth_append_length)

lemma W_inv_Enqueue_lemma_prelim_6:
  "length(q s)>0\<Longrightarrow>\<forall>i j. i < length (q s) \<and> j < length (q s) \<and> i \<noteq> j \<longrightarrow> fst (q s ! i) \<noteq> fst (q s ! j) \<Longrightarrow>
\<forall>i.(i<length(q s))\<longrightarrow>offset s \<noteq> fst(q s!i)
\<Longrightarrow>q s @ [(offset s, Data s (numEnqs s))] = q s'
\<Longrightarrow> \<forall>i j. i < length (q s') \<and> j < length (q s') \<and> i \<noteq> j \<longrightarrow> fst (q s' ! i) \<noteq> fst (q s' ! j)"
  by (smt (z3) butlast_snoc diff_diff_cancel diff_less_mono2 fstI le_eq_less_or_eq length_butlast less_one linorder_neqE_nat nth_append nth_append_length zero_less_diff zero_less_one)
  
lemma W_inv_Enqueue_lemma_prelim_7:
  "q s\<noteq>[]\<Longrightarrow>\<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a < aa \<longrightarrow> a + b \<le> aa \<Longrightarrow>
\<forall>a b. (a, b) \<in> set (q s)  \<longrightarrow> ((offset s> a \<longrightarrow> a+b\<le>offset s) \<and> (offset s< a \<longrightarrow> offset s + Data s (numEnqs s) \<le>a))
\<Longrightarrow>q s @ [(offset s, Data s (numEnqs s))] = q s'
\<Longrightarrow> \<forall>a b aa. (a, b) \<in> set (q s') \<and> (\<exists>b. (aa, b) \<in> set (q s')) \<longrightarrow> a < aa \<longrightarrow> a + b \<le> aa" 
  by (metis nat_neq_iff old.prod.inject rotate1.simps(2) set_ConsD set_rotate1)
  
lemma pec_1:
  "q s\<noteq>[] \<Longrightarrow>(\<forall>i<length (q s).
        (offset s < fst (q s ! i) \<longrightarrow> offset s + Data s (numEnqs s) < fst (q s ! i)) \<and>
        (fst (q s ! i) < offset s \<longrightarrow> fst (q s ! i) + snd (q s ! i) \<le> offset s)) \<Longrightarrow>
\<forall>a b. (a, b) \<in> set (q s)  \<longrightarrow> ((offset s> a \<longrightarrow> a+b\<le>offset s) \<and> (offset s< a \<longrightarrow> offset s + Data s (numEnqs s) \<le>a))
"
  by (metis fst_conv in_set_conv_nth less_or_eq_imp_le snd_conv)

lemma pec_2:
  "q s\<noteq>[] \<Longrightarrow>(\<forall>i<length (q s).
        (offset s < fst (q s ! i) \<longrightarrow> offset s + Data s (numEnqs s) < fst (q s ! i)) \<and>
        (fst (q s ! i) < offset s \<longrightarrow> fst (q s ! i) + snd(q s!i) \<le> offset s)) \<Longrightarrow>
Data s (numEnqs s)>0\<Longrightarrow>
\<forall>a. (\<exists>b. (a, b) \<in> set (q s))\<longrightarrow>offset s + Data s (numEnqs s) \<noteq> a"
  by (metis fst_conv in_set_conv_nth less_add_same_cancel1 less_irrefl_nat)
  



lemma W_inv_Enqueue_lemma_prelim_8:
  "q s\<noteq>[]\<Longrightarrow>\<forall>a. (\<exists>b. (a, b) \<in> set (q s)) \<longrightarrow> a \<noteq> fst (last (q s)) + snd (last (q s)) \<Longrightarrow>
    \<forall>a. (\<exists>b. (a, b) \<in> set (q s))  \<longrightarrow>offset s + Data s (numEnqs s) \<noteq> a \<Longrightarrow> Data s (numEnqs s)>0
\<Longrightarrow>q s @ [(offset s, Data s (numEnqs s))] = q s'
\<Longrightarrow> \<forall>a. (\<exists>b. (a, b) \<in> set (q s')) \<longrightarrow> a \<noteq> fst (last (q s')) + snd (last (q s'))" 
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>(\<exists>i. (i<length(q s) \<and> (q s!i) = (a,b)))") prefer 2
  apply (simp add: in_set_conv_nth)
  apply(subgoal_tac "\<forall>i.(i<length(q s')-1)\<longrightarrow> q s!i = q s'!i") prefer 2
  apply (metis length_append_singleton nat_diff_split_asm nth_append plus_1_eq_Suc)
  apply(subgoal_tac "i=length(q s')-1 \<longrightarrow> q s'!i = (offset s, Data s (numEnqs s))") prefer 2
  apply (metis Nil_is_append_conv last_conv_nth last_snoc)
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow>offset s + Data s (numEnqs s) \<noteq> fst(q s!i)") prefer 2
  apply (metis nth_mem prod.exhaust_sel)
  apply(subgoal_tac "\<forall>i.(i<length(q s')-1)\<longrightarrow>offset s + Data s (numEnqs s) \<noteq> fst(q s'!i)") prefer 2
  apply (metis diff_Suc_1 length_append_singleton)
  apply(subgoal_tac "fst (last (q s')) + snd (last (q s')) = offset s + Data s (numEnqs s)") prefer 2 
  apply (metis fst_conv last_snoc snd_conv)
  apply(subgoal_tac "\<forall>i.(i<length(q s'))\<longrightarrow>offset s + Data s (numEnqs s) \<noteq> fst(q s'!i)") prefer 2
  apply (metis One_nat_def Suc_pred add_eq_self_zero append_is_Nil_conv bot_nat_0.not_eq_extremum last_conv_nth last_snoc length_greater_0_conv less_SucE snd_conv)
  apply(subgoal_tac "\<forall>i.(i<length(q s'))\<longrightarrow>fst (last (q s')) + snd (last (q s')) \<noteq> fst(q s'!i)") prefer 2
  apply presburger
  by (metis fst_conv in_set_conv_nth)

lemma W_inv_Enqueue_lemma_prelim_9:
  "q s\<noteq>[]\<Longrightarrow>\<forall>a b. (a, b) \<in> set (q s) \<longrightarrow> 0 < b \<Longrightarrow>
    0< Data s (numEnqs s) 
\<Longrightarrow>q s @ [(offset s, Data s (numEnqs s))] = q s'
\<Longrightarrow> \<forall>a b. (a, b) \<in> set (q s') \<longrightarrow> 0 < b" 
  apply(subgoal_tac "\<forall>i.(i<length(q s')-1)\<longrightarrow> q s!i = q s'!i") prefer 2
  apply (metis length_append_singleton nat_diff_split_asm nth_append plus_1_eq_Suc)
  apply(subgoal_tac "i=length(q s')-1 \<longrightarrow> q s'!i = (offset s, Data s (numEnqs s))") prefer 2
  apply (metis Nil_is_append_conv last_conv_nth last_snoc)
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow>0< snd(q s!i)") prefer 2
  apply (metis nth_mem prod.exhaust_sel)
  apply(subgoal_tac "\<forall>i.(i<length(q s')-1)\<longrightarrow>0< snd(q s'!i)") prefer 2
  apply (metis diff_Suc_1 length_append_singleton)
  apply(subgoal_tac "last(q s') = (offset s, Data s (numEnqs s))") prefer 2 
  apply (metis fst_conv last_snoc snd_conv)
  apply(subgoal_tac "snd(last(q s')) = Data s (numEnqs s)") prefer 2 
  apply (metis snd_conv)
  apply(subgoal_tac "\<forall>i.(i<length(q s'))\<longrightarrow>0< snd(q s'!i)") prefer 2
  apply (metis One_nat_def Suc_pred add_eq_self_zero append_is_Nil_conv bot_nat_0.not_eq_extremum last_conv_nth last_snoc length_greater_0_conv less_SucE snd_conv)
  by (metis in_set_conv_nth snd_conv)
  

lemma W_inv_Enqueue_lemma_prelim_10:
  "q s\<noteq>[]\<Longrightarrow>\<forall>i<length (q s). data_index s (q s ! i) = numDeqs s + i \<Longrightarrow>
    data_index s ((offset s, Data s (numEnqs s))) = numEnqs s
\<Longrightarrow> q s @ [(offset s, Data s (numEnqs s))] = q s'
\<Longrightarrow> numDeqs s = numDeqs s'
\<Longrightarrow> length(q s) = numEnqs s - numDeqs s
\<Longrightarrow> data_index s = data_index s'
\<Longrightarrow> numEnqs s +1 = numEnqs s'
\<Longrightarrow> Data s = Data s'
\<Longrightarrow> offset s= offset s'
\<Longrightarrow> \<forall>i<length (q s'). data_index s' (q s' ! i) = numDeqs s' + i" 
  apply(subgoal_tac "\<forall>i.(i<length(q s')-1)\<longrightarrow> q s!i = q s'!i") prefer 2
  apply (metis length_append_singleton nat_diff_split_asm nth_append plus_1_eq_Suc)
  apply(subgoal_tac "\<forall>i<length (q s). data_index s' (q s' ! i) = numDeqs s' + i") prefer 2 
  apply (metis nth_append)
  apply(subgoal_tac "data_index s ((offset s, Data s (numEnqs s' -1))) = numEnqs s' -1") prefer 2
  apply (metis add_implies_diff)
  apply(subgoal_tac "data_index s' ((offset s, Data s (numEnqs s' -1))) = numEnqs s' -1") prefer 2
  apply metis
  apply(subgoal_tac "data_index s' ((offset s', Data s' (numEnqs s' -1))) = numEnqs s' -1") prefer 2
  apply presburger
  apply(subgoal_tac "\<forall>i<length (q s')-1. data_index s' (q s' ! i) = numDeqs s' + i") prefer 2
  apply (metis add.commute append.left_neutral append_Cons length_append length_tl list.sel(3))
  apply(subgoal_tac "(q s' ! (length (q s')-1 )) = (offset s, Data s (numEnqs s))") prefer 2 
  apply (metis append_is_Nil_conv last_conv_nth last_snoc)
  apply(subgoal_tac "(q s' ! (length (q s')-1 )) = (offset s', Data s' (numEnqs s' -1))") prefer 2
  apply (metis add.commute diff_add_inverse)
  apply(subgoal_tac "numDeqs s + length (q s) = data_index s' (offset s', Data s' (numEnqs s' -1))") prefer 2
  apply (metis diff_is_0_eq' le_add_diff_inverse length_0_conv nat_le_linear)
  apply(subgoal_tac "length (q s') -1  = length(q s)") prefer 2
  apply (metis add.comm_neutral add_implies_diff length_0_conv length_append length_tl less_one linordered_semidom_class.add_diff_inverse list.sel(3) not_Cons_self2)
  apply(subgoal_tac "numDeqs s + length (q s') -1 = data_index s' (offset s', Data s' (numEnqs s' -1))") prefer 2
  apply (metis Nat.add_diff_assoc diff_is_0_eq' length_0_conv nat_le_linear)
  by (metis Nat.lessE diff_Suc_1)


lemma pec_3:
  "inv s \<Longrightarrow> cW_step (pcW s) s s' \<Longrightarrow> pcW s = Enqueue \<Longrightarrow> pre_W (pcW s) s \<Longrightarrow> con_assms s 
\<Longrightarrow> length(q s) = numEnqs s - numDeqs s
"
  by(simp add:cW_step_def pre_W_def inv_def )


lemma pec_4:
  "cW_step (pcW s) s s' \<Longrightarrow> pcW s = Enqueue \<Longrightarrow> pre_W (pcW s) s \<Longrightarrow> con_assms s \<Longrightarrow> 
     numDeqs s = numDeqs s' 
  \<and> data_index s = data_index s' 
  \<and> numEnqs s +1 = numEnqs s'
  \<and> Data s = Data s'
  \<and> offset s= offset s'
  \<and> ownD s = ownD s'
"
  by(simp add:cW_step_def )




lemma W_inv_Enqueue_lemma_prelim_11:
  "q s\<noteq>[]\<Longrightarrow> \<forall>i<length (q s). snd (q s ! i) = Data s (numDeqs s + i) \<Longrightarrow>
q s @ [(offset s, Data s (numEnqs s))] = q s'
\<Longrightarrow> numDeqs s = numDeqs s'
\<Longrightarrow> length(q s) = numEnqs s - numDeqs s
\<Longrightarrow> data_index s = data_index s'
\<Longrightarrow> numEnqs s +1 = numEnqs s'
\<Longrightarrow> Data s = Data s'
\<Longrightarrow> offset s= offset s'
\<Longrightarrow>  \<forall>i<length (q s'). snd (q s' ! i) = Data s' (numDeqs s' + i)"
  apply(subgoal_tac "snd(offset s, Data s (numEnqs s)) = Data s (numEnqs s)") prefer 2
  apply simp
  apply(subgoal_tac "\<forall>i.(i<length(q s')-1)\<longrightarrow> q s!i = q s'!i") prefer 2
  apply (metis length_append_singleton nat_diff_split_asm nth_append plus_1_eq_Suc)
  apply(subgoal_tac "\<forall>i<length (q s). snd(q s' ! i) = Data s' (numDeqs s' + i)") prefer 2 
  apply (metis nth_append)
  apply(subgoal_tac "snd ((offset s, Data s (numEnqs s' -1))) = Data s(numEnqs s' -1)") prefer 2
  apply (metis add_implies_diff)
  apply(subgoal_tac "snd((offset s', Data s' (numEnqs s' -1))) = Data s' (numEnqs s' -1)") prefer 2
  apply metis
  apply(subgoal_tac "\<forall>i<length (q s')-1. snd (q s' ! i) = Data s' (numDeqs s' + i)") prefer 2
  apply (metis add.commute append.left_neutral append_Cons length_append length_tl list.sel(3))
  apply(subgoal_tac "(q s' ! (length (q s')-1 )) = (offset s, Data s (numEnqs s))") prefer 2 
  apply (metis append_is_Nil_conv last_conv_nth last_snoc)
  apply(subgoal_tac "(q s' ! (length (q s')-1 )) = (offset s', Data s' (numEnqs s' -1))") prefer 2
  apply (metis add.commute diff_add_inverse) 
  apply(subgoal_tac "length (q s') -1  = length(q s)") prefer 2
  apply (metis add.comm_neutral add_implies_diff length_0_conv length_append length_tl less_one linordered_semidom_class.add_diff_inverse list.sel(3) not_Cons_self2)
  by (metis Nat.lessE add.commute diff_Suc_1 le_add_diff_inverse2 length_greater_0_conv less_or_eq_imp_le zero_less_diff)

lemma W_inv_Enqueue_lemma_prelim_12:
  "length(q s)>0\<Longrightarrow>\<forall>i<length (q s). ownD s (i + numDeqs s) = B
\<Longrightarrow>q s @ [(offset s, Data s (numEnqs s))] = q s'
\<Longrightarrow>ownD s = ownD s'
\<Longrightarrow>numDeqs s = numDeqs s'
\<Longrightarrow>length(q s) = numEnqs s - numDeqs s
\<Longrightarrow>ownD s (numEnqs s) = B
\<Longrightarrow> \<forall>i<length (q s'). ownD s' (i + numDeqs s') = B"
  apply(subgoal_tac "length(q s)+1 = length(q s')") prefer 2 
  apply (metis Suc_eq_plus1 length_append_singleton)
  apply(subgoal_tac " \<forall>i<length (q s')-1 . ownD s (i + numDeqs s) = B")
  prefer 2 
  apply simp
  apply(subgoal_tac " \<forall>i<length (q s')-1 . ownD s' (i + numDeqs s') = B")
  prefer 2 
  apply simp
  apply(subgoal_tac "ownD s' (length (q s')-1 + numDeqs s') = B") 
  apply (smt (z3) add.commute add_diff_cancel_left' discrete le_eq_less_or_eq less_diff_conv)
  apply(subgoal_tac "length (q s')-1 + numDeqs s' = numEnqs s") prefer 2 
  apply linarith
  by presburger


lemma W_inv_Enqueue_lemma_prelim_13:
  "inv s \<Longrightarrow> con_assms s \<Longrightarrow> pcW s = Enqueue \<Longrightarrow> pre_W (pcW s) s \<Longrightarrow> cW_step (pcW s) s s'
  \<Longrightarrow> ownT s \<noteq> W
\<Longrightarrow> Q_structure s'"
  apply(subgoal_tac "numDeqs s = numDeqs s' \<and> ownD s = ownD s' \<and> data_index s = data_index s' \<and> numEnqs s +1 = numEnqs s'\<and>  Data s = Data s'\<and> offset s= offset s'") 
   prefer 2 using pec_4 [where s=s and s'=s']
   apply blast
  apply(subgoal_tac "length(q s) = numEnqs s - numDeqs s") prefer 2
  using pec_3 apply blast
  apply(subgoal_tac "q s @ [(offset s, Data s (numEnqs s))] = q s'") prefer 2
  using W_inv_Enqueue_lemma_prelim_2 [where s=s and s'=s'] 
   apply linarith
  apply(case_tac "q s=[]")
  using W_inv_Enqueue_lemma_prelim_3 [where s=s and s'=s'] 
  apply blast
  apply(simp add:Q_structure_def)
  apply(intro conjI impI)
  apply(simp add:Q_basic_struct_def)
  apply(intro conjI impI)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas cW_step_def)
  apply(simp add:pre_W_def pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  using W_inv_Enqueue_lemma_prelim_4 [where s=s and s'=s'] 
  apply presburger
  apply(simp add:Q_gap_structure_def)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas cW_step_def)
  apply(simp add:pre_W_def pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  apply(subgoal_tac "\<forall>i. i < length (q s) \<and> 0 < i \<longrightarrow>
        fst (q s ! (i - Suc 0)) + snd (q s ! (i - Suc 0)) = fst (q s ! i) \<or> fst (q s ! i) = 0 \<Longrightarrow>
        offset s = fst(last(q s)) + snd(last(q s)) \<or> offset s = 0") prefer 2 
  apply presburger
  apply(subgoal_tac "q s @ [(offset s, Data s (numEnqs s))] = q s'") prefer 2 
  apply presburger
  apply(subgoal_tac "length(q s) > 0") prefer 2 
  apply blast
  using W_inv_Enqueue_lemma_prelim_5 [where s=s and s'=s']
  apply presburger
  apply(simp add:Q_offsets_differ_def)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas cW_step_def)
  apply(simp add:pre_W_def pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  apply(subgoal_tac "length(q s) > 0") prefer 2 
  apply blast
  apply(subgoal_tac "\<forall>i j. i < length (q s) \<and> j < length (q s) \<and> i \<noteq> j \<longrightarrow> fst (q s ! i) \<noteq> fst (q s ! j)") prefer 2 
  apply presburger
  apply(subgoal_tac "\<forall>i<length (q s). offset s \<noteq> fst (q s ! i)") prefer 2
  apply metis
  using W_inv_Enqueue_lemma_prelim_6 [where s=s and s'=s']
  apply presburger
  apply(simp add:Q_has_no_overlaps_def)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas cW_step_def)
  apply(simp add:pre_W_def pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  apply(subgoal_tac "\<forall>a b. (a, b) \<in> set (q s)  \<longrightarrow> ((offset s> a \<longrightarrow> a+b\<le>offset s) \<and> (offset s< a \<longrightarrow> offset s + Data s (numEnqs s) \<le>a))")
  prefer 2 using pec_1 [where s=s] 
  apply presburger
  using W_inv_Enqueue_lemma_prelim_7 [where s=s and s'=s']
  apply presburger
  apply(simp add: Q_has_no_uroboros_def)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas cW_step_def)
  apply(simp add:pre_W_def pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  apply(subgoal_tac "\<forall>a. (\<exists>b. (a, b) \<in> set (q s))\<longrightarrow>offset s + Data s (numEnqs s) \<noteq> a") prefer 2
  using pec_2 [where s=s] 
  apply presburger
  using W_inv_Enqueue_lemma_prelim_8 [where s=s and s'=s'] 
  apply presburger
  apply(simp add: Q_elem_size_def)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas cW_step_def)
  apply(simp add:pre_W_def pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  using W_inv_Enqueue_lemma_prelim_9 [where s=s and s'=s']
  apply presburger
  apply(simp add: Q_reflects_writes_def)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas cW_step_def)
  apply(simp add:pre_W_def pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  apply(subgoal_tac "data_index s ((offset s, Data s (numEnqs s))) = numEnqs s") prefer 2
  apply presburger
  using W_inv_Enqueue_lemma_prelim_10 [where s=s and s'=s']
  apply (metis (no_types, lifting) Suc_eq_plus1)
  apply(simp add:Q_elem_rel_def)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas cW_step_def)
  apply(simp add:pre_W_def pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  using W_inv_Enqueue_lemma_prelim_11 [where s=s and s'=s'] 
  apply (metis (no_types, lifting) Suc_eq_plus1)
  apply(simp add:Q_reflects_ownD_def)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas cW_step_def)
  apply(simp add:pre_W_def pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  apply(subgoal_tac "ownD s (numEnqs s) = B") prefer 2
  apply presburger
  using W_inv_Enqueue_lemma_prelim_12 [where s=s and s'=s']
  by (metis (no_types, lifting) length_greater_0_conv)
 
lemma pec_5:
  "cW_step (pcW s) s s' \<Longrightarrow> pcW s = Enqueue \<Longrightarrow> pre_W (pcW s) s 
\<Longrightarrow> H s = H s' \<and> T s = T s'
"
  by(simp add:cW_step_def pre_W_def inv_def )

lemma W_inv_Enqueue_cases_split_1:
  "case_1 s \<Longrightarrow>  pcW s = Enqueue \<Longrightarrow>pre_W (pcW s) s \<Longrightarrow> cW_step (pcW s) s s'
\<Longrightarrow> \<not>case_2 s'"    
  apply(subgoal_tac "H s = H s' \<and> T s = T s'") prefer 2 using pec_5 apply blast
  apply(simp add:case_1_def) apply(simp add:case_2_def)
  by (metis dual_order.strict_iff_order less_trans)

lemma W_inv_Enqueue_cases_split_2:
  "case_2 s \<Longrightarrow>  pcW s = Enqueue \<Longrightarrow>pre_W (pcW s) s \<Longrightarrow> cW_step (pcW s) s s'
\<Longrightarrow> \<not>case_1 s'"    
  apply(subgoal_tac "H s = H s' \<and> T s = T s'") prefer 2 using pec_5 apply blast
  apply(simp add:case_1_def) apply(simp add:case_2_def) 
  by (metis leD le_trans)





lemma W_inv_Enqueue_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = Enqueue"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"    
shows "inv s'"
  apply(subgoal_tac "H s = H s' \<and> T s = T s'") prefer 2 
  using pec_5
  using assms(1) assms(2) assms(3) assms(4) assms(5) apply blast
  using assms apply(simp add:inv_def pre_W_def cW_step_def pre_enqueue_inv_def)
  apply(intro conjI impI)
  apply (metis Suc_diff_le length_0_conv)
  defer
  defer 
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:tempW_def)
  apply(case_tac "case_1 s") apply simp apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:case_1_def) apply clarify apply(intro conjI impI)
  apply (metis F.distinct(5) diff_is_0_eq' less_nat_zero_code linorder_neqE_nat nat_le_linear zero_less_diff)
  apply (metis (mono_tags, hide_lams) F.distinct(5) F.distinct(9) le_antisym less_Suc_eq_le minus_nat.diff_0 not_less_eq plus_nat.add_0)
  apply(subgoal_tac "i<N \<and> ownB s i=W\<longrightarrow>offset s\<le>i \<and> i<offset s + Data s (numEnqs s)") prefer 2
  apply (metis nat_less_le)
  apply(subgoal_tac "i>N \<and> ownB s i=W\<longrightarrow>i>offset s + Data s (numEnqs s)")
  apply (metis (no_types, lifting) diff_is_0_eq le_eq_less_or_eq linorder_neqE_nat zero_less_diff)
  apply(subgoal_tac "end(tempW s)\<le>N", unfold tempW_def)[1] prefer 2
  apply (metis end_simp fst_conv snd_conv) 
  apply (metis (no_types, lifting) less_trans_Suc nat_less_le nat_neq_iff not_less_eq_eq)
  apply(subgoal_tac "case_2 s") apply simp apply(thin_tac "\<not>case_1 s")[1]
  prefer 2 apply blast apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:case_2_def) apply clarify 
  using Suc_diff_le apply presburger
  defer defer
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply clarify
  apply(intro conjI impI)
  apply(rule_tac ?x = "{i. offset s \<le> i \<and> i < offset s + Data s (numEnqs s)}" in exI)
  apply (intro conjI impI)
  apply metis
  apply(case_tac "case_1 s") apply(simp)
  apply(simp add:case_1_def) apply clarify apply(intro conjI impI)
  apply (metis F.distinct(5) diff_is_0_eq' less_nat_zero_code linorder_neqE_nat nat_le_linear zero_less_diff)
  apply (metis (no_types, lifting) Suc_le_lessD fst_conv not_less_eq_eq snd_conv tempW_def)
  apply(subgoal_tac "case_2 s") apply simp apply(thin_tac "\<not>case_1 s")[1]
  prefer 2 apply blast apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:case_2_def) apply clarify 
  apply (intro conjI impI)
  apply (metis le_eq_less_or_eq nat_le_linear)
  apply(subgoal_tac "i\<ge>H s\<and>i<T s\<longrightarrow>ownB s i=B") prefer 2
  apply metis
  apply(subgoal_tac "i\<ge>T s\<and>i<e\<longrightarrow>ownB s i=R") prefer 2
  apply metis
  apply(subgoal_tac "i\<ge>e\<and>i<f\<longrightarrow>ownB s i=Q") prefer 2
  apply metis
  apply(subgoal_tac "i\<ge>f\<and>i<N\<longrightarrow>ownB s i=D") prefer 2
  apply metis
  apply(subgoal_tac "i\<ge>H s\<and>i<N\<longrightarrow>ownB s i\<noteq>W") prefer 2 
  apply (metis F.distinct(1) F.distinct(3) F.distinct(5) F.distinct(7) diff_is_0_eq neq0_conv zero_less_diff)
  apply (metis (no_types, lifting) diff_is_0_eq gr0I zero_less_diff)
  apply(clarsimp)
  apply(intro iffI)
  apply clarify apply simp
  apply(case_tac "(a, b) \<in> set (q s)") apply simp 
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply(subgoal_tac "(i\<le>N \<and> ownB s i\<noteq>Q)\<longrightarrow>(\<nexists>a b. ((a,b)\<in>set(q s)\<and> a\<le>i \<and> i<a+b))")
  prefer 2 
  apply (metis fst_eqD snd_eqD tempW_def)
  apply(subgoal_tac "a = offset s \<and> b = Data s (numEnqs s)") prefer 2
  apply meson
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply clarify apply simp
  apply(subgoal_tac "ownB s i=Q \<and> i\<le>N\<longleftrightarrow>(\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x)")
  prefer 2 
  apply presburger
  apply simp 
  apply metis
  apply clarify
  apply(case_tac "ownT s = W", simp_all)
  apply(subgoal_tac "Q_structure s'") 
  apply presburger
  using W_inv_Enqueue_lemma_prelim_1 [where s=s and s'=s'] assms 
  apply fastforce
  prefer 2
  apply(subgoal_tac "Q_structure s'") 
  apply presburger
  using W_inv_Enqueue_lemma_prelim_13 [where s=s and s'=s'] assms 
  apply fastforce
  apply(case_tac "case_1 s", simp_all) prefer 2 apply(simp add:case_2_def)
  prefer 2
  apply(case_tac "case_1 s", simp_all)
  apply(subgoal_tac "\<not>case_2 s'") prefer 2 using W_inv_Enqueue_cases_split_1 [where s=s and s'=s'] assms
  apply fastforce
  prefer 2
  apply(subgoal_tac "\<not>case_1 s'") prefer 2 using W_inv_Enqueue_cases_split_2 [where s=s and s'=s'] assms
  apply fastforce
  apply(simp_all)
  apply(thin_tac "\<not>case_1 s") 
  apply(subgoal_tac "case_2 s'") 
  apply presburger
  apply(thin_tac "\<not> case_1(s\<lparr>numEnqs := Suc (numEnqs s),ownB := \<lambda>i. if ownB s i = W \<and> i \<le> N then Q
                   else ownB ((if ownT s = W then ownT_update (\<lambda>_. Q) else (\<lambda>s. s\<lparr>ownT := ownT s\<rparr>)) s\<lparr>numEnqs := Suc (numEnqs s)\<rparr>)i, pcW := idleW, q := q s @ [(offset s, Data s (numEnqs s))]\<rparr>)")
  defer
  apply(subgoal_tac "case_1 s'") 
  apply presburger
  apply(thin_tac "\<not> case_2 (s\<lparr>numEnqs := Suc (numEnqs s),ownB := \<lambda>i. if ownB s i = W \<and> i \<le> N then Q
                   else ownB ((if ownT s = W then ownT_update (\<lambda>_. Q) else (\<lambda>s. s\<lparr>ownT := ownT s\<rparr>)) s\<lparr>numEnqs := Suc (numEnqs s)\<rparr>)  i,  pcW := idleW, q := q s @ [(offset s, Data s (numEnqs s))]\<rparr>)")
  defer
  apply(subgoal_tac "case_1 s'")
  apply presburger
  defer                         (*start case2 to case2*)
  apply(simp add:case_2_def)
  apply clarify
  apply(intro conjI impI) 
  using F.distinct(9) apply presburger
  apply(rule_tac ?x = "a" in exI)
  apply(rule_tac ?x = "offset s + Data s (numEnqs s)" in exI)
  apply(intro conjI impI)
  apply linarith
  apply(rule_tac ?x = "offset s + Data s (numEnqs s)" in exI)
  apply(intro conjI impI)
  apply linarith
  apply(rule_tac ?x = "T s" in exI)
  apply(intro conjI impI)
  apply linarith
  apply(rule_tac ?x = "e" in exI)
  apply(intro conjI impI)
  apply linarith
  apply(rule_tac ?x = "f" in exI)
  apply(intro conjI impI)
  apply linarith
  apply linarith
  apply (metis F.distinct(1))
  apply (metis (mono_tags, hide_lams) le_eq_less_or_eq le_trans nat_le_linear)
  apply (metis Suc_diff_Suc Zero_not_Suc diff_is_0_eq')
  apply (metis F.distinct(5))
  apply (metis F.distinct(1))
  apply (metis (mono_tags, hide_lams))
  apply (metis F.distinct(7))
  apply blast
  apply meson
  apply meson
  apply meson
  apply blast
  apply meson
  apply meson
  apply force
  apply force
  apply force
  apply force
  apply force
  apply force
  apply (metis (mono_tags, hide_lams) F.distinct(1) F.distinct(13) add_diff_cancel_left' eq_imp_le fst_eqD linorder_neqE_nat snd_eqD tempW_def zero_less_diff)
  apply (metis hd_append2)
  apply (metis fst_eqD hd_append le_neq_implies_less less_irrefl_nat list.sel(1))
  apply force
  apply (metis add_is_0)
  apply force
  apply fastforce
  (*start case1 to case1 and ownT \<noteq>W *)
  apply(case_tac "q s=[]")
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:case_1_def)
   apply(clarify)
  apply(rule_tac ?x = "T s" in exI)
  apply(rule_tac ?x = "b" in exI)
  apply(intro conjI impI)
  apply linarith
  apply(rule_tac ?x = "offset s + Data s (numEnqs s)" in exI)
  apply(intro conjI impI) 
  apply linarith
  apply linarith
  apply (metis F.distinct(5))
  apply (metis F.distinct(1))
  apply (metis le_trans less_eq_Suc_le less_or_eq_imp_le not_less_eq_eq)
  apply (metis le_imp_less_Suc not_less_eq)
  apply (metis)
  apply blast
  apply blast
  apply fastforce
  apply fastforce
  apply fastforce
  apply fastforce
  apply (metis F.distinct(1) F.distinct(5) Nat.add_0_right le_eq_less_or_eq nat_add_left_cancel_less nat_le_linear)
  apply (metis fst_eqD hd_append2 list.sel(1) nat_less_le self_append_conv2)
  apply blast
  apply meson
  apply (metis le_neq_implies_less)
  apply (metis le_neq_implies_less)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:case_1_def)
  apply(clarify)
  apply(rule_tac ?x = "T s" in exI)
  apply(rule_tac ?x = "fst (hd (q s))" in exI)
  apply(intro conjI impI)
  apply blast
  apply(rule_tac ?x = "offset s + Data s (numEnqs s)" in exI)
  apply(intro conjI impI) 
  apply linarith
  apply linarith
  apply (metis F.distinct(5))
  apply (metis F.distinct(1))
  apply (smt (z3) le_eq_less_or_eq le_trans linorder_neqE_nat)
  apply (metis le_trans less_eq_Suc_le less_or_eq_imp_le not_less_eq_eq)
  apply (metis le_imp_less_Suc not_less_eq)
  apply (metis)
  apply blast
  apply fastforce
  apply fastforce
  apply fastforce
  apply fastforce
  apply linarith
  apply fastforce
  apply (metis F.distinct(1) F.distinct(5) Nat.add_0_right le_eq_less_or_eq nat_add_left_cancel_less nat_le_linear)
  apply metis
  apply force
  apply meson
  (*start case1 to case1 and ownT =W *)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:case_1_def)
  apply(clarify)
  apply(rule_tac ?x = "T s" in exI)
  apply(rule_tac ?x = "b" in exI)
  apply(intro conjI impI)
  apply blast
  apply(rule_tac ?x = "offset s + Data s (numEnqs s)" in exI)
  apply(intro conjI impI) 
  apply linarith
  apply blast
  apply (metis F.distinct(5))
  apply (metis F.distinct(1))
  apply (metis le_neq_implies_less le_trans less_imp_le_nat)
  apply (metis le_imp_less_Suc not_less_eq)
  apply (metis F.distinct(5))
  apply metis
  apply metis
  apply fastforce
  apply force
  apply metis
  apply meson
  apply (metis (mono_tags, hide_lams) F.distinct(5) Nat.add_0_right le_refl less_nat_zero_code linorder_neqE_nat nat_add_left_cancel_less)
  apply (metis nat_less_le)
  by blast



lemma W_inv_idleW_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = idleW"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"    
shows "inv s'"
  using assms apply(simp add:inv_def pre_W_def cW_step_def pre_acquire_inv_def)
  apply(intro conjI impI)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply (metis leD)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_def) 
  apply(simp add:case_2_def)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_def) 
  apply(subgoal_tac "case_2 (s\<lparr>pcW := FinishedW\<rparr>)")
  apply blast apply simp apply(thin_tac "\<not> case_1 s ") 
  apply(simp add:case_2_def)
  prefer 2 
  apply(case_tac "numEnqs s < n", simp_all)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply clarify
  apply(rule_tac ?x = "a" in exI)
  apply(rule_tac ?x = "b" in exI)
  apply(intro conjI impI) apply metis
  apply(rule_tac ?x = "H s" in exI)
  apply(intro conjI impI) 
  apply blast
  apply(rule_tac ?x = "T s" in exI)
  apply(intro conjI impI) 
  apply blast
  apply(rule_tac ?x = "e" in exI)
  apply(intro conjI impI) 
  apply blast
  apply(rule_tac ?x = "f" in exI)
  apply(intro conjI impI) 
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast 
  apply meson
  apply metis
  apply meson
  apply meson
  apply meson
  apply meson
  apply meson
  apply meson
  apply meson
  apply meson
  apply meson
  apply meson
  by meson



lemma W_inv_OOM_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = OOM"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"    
shows "inv s'"
  using assms apply(simp add:inv_def pre_W_def cW_step_def pre_OOM_inv_def)
  apply(intro conjI impI)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_def)
  apply(simp add:case_2_def)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  by(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)





lemma W_inv_FinishedW_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = FinishedW"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"    
shows "inv s'"
  using assms by(simp add:inv_def pre_W_def cW_step_def pre_OOM_inv_def)



lemma W_inv_Write_lemma_prelim_1:
  "pcW s = Write\<Longrightarrow>cW_step (pcW s) s s'
\<Longrightarrow>q s=q s' \<and> numDeqs s = numDeqs s'"
  apply simp 
  by(simp add:cW_step_def)


lemma W_inv_Write_lemma_prelim_2:
  "pcW s = Write\<Longrightarrow>cW_step (pcW s) s s'
\<Longrightarrow>\<forall>a b. ((a,b)\<noteq>(offset s, Data s (numEnqs s)))\<longrightarrow> data_index s' (a,b) = data_index s (a,b)"
  apply simp 
  by(simp add:cW_step_def)

lemma W_inv_Write_lemma_prelim_3:
  "pcW s = Write\<Longrightarrow>cW_step (pcW s) s s'
\<Longrightarrow>\<forall>i. i<length(q s) \<longrightarrow> ((q s ! i)\<noteq>(offset s, Data s (numEnqs s)))\<longrightarrow> data_index s' ((q s ! i)) = data_index s ((q s ! i))"
  apply simp 
  by(simp add:cW_step_def)


lemma W_inv_Write_lemma_prelim_4:
  "pcW s = Write\<Longrightarrow>cW_step (pcW s) s s'\<Longrightarrow>pre_write_inv s
\<Longrightarrow>\<forall>i<length (q s). data_index s' (q s ! i) = data_index s (q s ! i)"
  apply simp 
  apply(simp add:cW_step_def pre_write_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  by (metis fst_conv less_nat_zero_code list.size(3))

lemma W_inv_Write_lemma_prelim_5:
  "pcW s = Write\<Longrightarrow>cW_step (pcW s) s s'\<Longrightarrow>pre_write_inv s \<Longrightarrow> inv s
\<Longrightarrow>\<forall>i<length (q s). Data s (numDeqs s + i) = snd(q s ! i)"
  apply simp 
  apply(simp add:cW_step_def pre_write_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) 
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas) 
  by (metis length_0_conv less_nat_zero_code)

lemma W_inv_Write_lemma_prelim_6:
  "pcW s = Write\<Longrightarrow>cW_step (pcW s) s s'\<Longrightarrow>pre_write_inv s \<Longrightarrow> inv s
\<Longrightarrow>\<forall>i<length (q s). Data s (numDeqs s + i) = Data s' (numDeqs s' + i)"
  apply simp 
  by(simp add:cW_step_def pre_write_inv_def)

lemma W_inv_Write_lemma_prelim_7:
  "pcW s = Write\<Longrightarrow>cW_step (pcW s) s s'\<Longrightarrow>pre_write_inv s \<Longrightarrow> inv s
\<Longrightarrow>\<forall>i<length (q s). snd(q s ! i) = snd(q s' ! i)"
  apply simp 
  using W_inv_Write_lemma_prelim_1 by auto

lemma W_inv_Write_lemma_prelim_8:
  "pcW s = Write\<Longrightarrow>cW_step (pcW s) s s'\<Longrightarrow>pre_write_inv s \<Longrightarrow> inv s
\<Longrightarrow>\<forall>i<length (q s'). Data s' (numDeqs s' + i) = snd(q s' ! i)"
  apply simp 
  using W_inv_Write_lemma_prelim_1 W_inv_Write_lemma_prelim_5 W_inv_Write_lemma_prelim_6 by presburger
  
lemma W_inv_Write_lemma_prelim_9:
  "pcW s = Write\<Longrightarrow>cW_step (pcW s) s s'\<Longrightarrow>pre_write_inv s \<Longrightarrow> inv s
\<Longrightarrow>\<forall>i<length (q s). ownD s (numDeqs s + i) = B"
  apply simp 
  apply(simp add:cW_step_def pre_write_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) 
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  by (metis add.commute less_nat_zero_code list.size(3))
  
lemma W_inv_Write_lemma_prelim_10:
  "pcW s = Write\<Longrightarrow>cW_step (pcW s) s s'\<Longrightarrow>pre_write_inv s \<Longrightarrow> inv s
\<Longrightarrow>\<forall>i<length (q s'). ownD s' (numDeqs s' + i) = B"
  apply simp 
  apply(simp add:cW_step_def pre_write_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) 
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  by (metis add.commute less_nat_zero_code list.size(3))

lemma W_inv_Write_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = Write"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"    
shows "inv s'"
  using assms apply simp
  apply(subgoal_tac "case_1 s \<or> case_2 s") prefer 2 using inv_def pre_W_def
  apply blast
  apply(subgoal_tac "pre_write_inv s") prefer 2 using inv_def pre_W_def assms
  apply (metis PCW.simps(195))
  apply(simp add:pre_W_def cW_step_def)
  apply(simp add:inv_def)
  apply(intro conjI impI) 
  apply (simp add: pre_write_inv_def) defer
  apply (simp add: pre_write_inv_def) defer defer defer 
  apply(subgoal_tac "case_1 s' \<or> case_2 s'")
  apply meson using case_trans_Write_to_Enqueue_case_3 [where s=s and s'=s']
  using assms(1) assms(2) apply blast
   apply(simp add:Q_indices_def ran_indices_def Q_owns_bytes_def)
  apply(subgoal_tac "q s= q s'") prefer 2 using W_inv_Write_lemma_prelim_1 [where s=s and s'=s'] 
  using assms(5) apply blast
  apply(unfold Q_lemmas Q_basic_lemmas)
  apply(intro conjI impI)
  apply presburger
  apply (metis (no_types, lifting))
  apply force
  apply presburger
  apply metis
  apply presburger
  apply(subgoal_tac "numDeqs s = numDeqs s'") prefer 2
  using case_trans_Write_to_Enqueue_case_3 [where s=s and s'=s'] using assms(1) assms(2) 

  using \<open>\<lbrakk>pcW s = Write; cW_step (pcW s) s s'\<rbrakk> \<Longrightarrow> q s = q s' \<and> numDeqs s = numDeqs s'\<close> assms(5) apply fastforce
  apply(subgoal_tac "data_index(s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
             ownD :=
               \<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i,
             data_index :=\<lambda>x. if (offset s, Data s (numEnqs s)) = x then numEnqs s else data_index  (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
                              ownD :=\<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i\<rparr>) x\<rparr>) = data_index s'") prefer 2
  
  apply meson
  apply(subgoal_tac "(\<forall>i. (i<length(q s')) \<longrightarrow> data_index s' (q s' ! i) =
       numDeqs s' + i) \<longrightarrow> (\<forall>i<length (q (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
                ownD := \<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i,
                data_index := \<lambda>x. if (offset s, Data s (numEnqs s)) = x then numEnqs s else data_index (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
                                 ownD := \<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i\<rparr>) x\<rparr>)).
       data_index (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
             ownD :=  \<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i,
             data_index :=  \<lambda>x. if (offset s, Data s (numEnqs s)) = x then numEnqs s  else data_index (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
                              ownD := \<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i\<rparr>) x\<rparr>)  (q (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
                ownD := \<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i,
                data_index := \<lambda>x. if (offset s, Data s (numEnqs s)) = x then numEnqs s  else data_index
                            (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue, ownD := \<lambda>i. if i = numWrites s then B  else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i\<rparr>)  x\<rparr>) !  i) =
       numDeqs (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
             ownD := \<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i,
             data_index := \<lambda>x. if (offset s, Data s (numEnqs s)) = x then numEnqs s else data_index (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue, ownD :=
                                \<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i\<rparr>) x\<rparr>) + i) ") prefer 2 
  apply force
  apply(subgoal_tac "(\<forall>i. (i<length (q s')) \<longrightarrow> data_index s' (q s' ! i) = numDeqs s' + i)") 
  apply meson
  apply(subgoal_tac "q s'\<noteq>[]") prefer 2
  apply meson
  apply(subgoal_tac "length(q s)= length(q s')") prefer 2 
     apply presburger
    apply(subgoal_tac "\<forall>i<length (q s). data_index s' (q s ! i) = numDeqs s' + i")
  apply presburger
  apply(subgoal_tac "\<forall>i<length (q s). data_index s' (q s ! i) = data_index s (q s!i)")
  apply metis
  apply(subgoal_tac "\<forall>a b. ((a,b)\<noteq>(offset s, Data s (numEnqs s)))\<longrightarrow> data_index s' (a,b) = data_index s (a,b)")
     prefer 2 
  using W_inv_Write_lemma_prelim_2 [where s=s and s'=s']
  using assms(5) apply fastforce
  apply(subgoal_tac "\<forall>i. i<length(q s) \<longrightarrow> ((q s ! i)\<noteq>(offset s, Data s (numEnqs s)))\<longrightarrow> data_index s' ((q s ! i)) = data_index s ((q s ! i))")
  prefer 2 using W_inv_Write_lemma_prelim_3 [where s=s and s'=s']
  using assms(5) apply fastforce 
  using W_inv_Write_lemma_prelim_4 [where s=s and s'=s']
  using assms(5) apply fastforce
  using W_inv_Write_lemma_prelim_8 [where s=s and s'=s']
  using assms(1) assms(5) apply presburger
  using W_inv_Write_lemma_prelim_10 [where s=s and s'=s']
  using assms(1) assms(5) 
  by (metis add.commute)




lemma W_inv_BTS_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = BTS"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"    
shows "inv s'"
  using assms by(simp add:inv_def pre_W_def cW_step_def pre_OOM_inv_def)




lemma local_pre_W_inv: 
  assumes "con_assms s"
  and "pcw = pcW s"
  and "pre_W pcw s"
  and "inv s"
  and "cW_step pcw s s'"
shows "inv s'"
  using assms apply(case_tac "pcW s") 
  using W_inv_A1_lemma [where s=s and s'=s'] apply blast
  using W_inv_A2_lemma [where s=s and s'=s'] apply blast
  using W_inv_A3_lemma [where s=s and s'=s'] apply blast
  using W_inv_A4_lemma [where s=s and s'=s'] apply blast
  using W_inv_A5_lemma [where s=s and s'=s'] apply blast
  using W_inv_A6_lemma [where s=s and s'=s'] apply blast 
  using W_inv_A7_lemma [where s=s and s'=s'] apply blast
  using W_inv_A8_lemma [where s=s and s'=s'] apply blast 
  using W_inv_Enqueue_lemma [where s=s and s'=s'] apply blast             
  using W_inv_idleW_lemma [where s=s and s'=s'] apply blast 
  using W_inv_OOM_lemma [where s=s and s'=s'] apply blast    
  using W_inv_FinishedW_lemma [where s=s and s'=s'] apply blast 
  using W_inv_Write_lemma [where s=s and s'=s'] apply blast 
  using W_inv_BTS_lemma [where s=s and s'=s'] by blast   



























(*******************************LOCAL W_step shows preW*************************************)


lemma W_local_A1_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A1"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_W (pcW s') s'"
  using assms apply simp
  by(simp add:inv_def pre_W_def cW_step_def pre_A1_inv_def pre_A2_inv_def)

lemma W_local_A2_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A2"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_W (pcW s') s'"
  using assms apply simp
  apply(simp add:inv_def pre_W_def cW_step_def pre_A2_inv_def pre_A3_inv_def)
  apply(case_tac "tW s = hW s") apply simp_all 
  apply(case_tac "hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s") 
  apply(simp_all add: pre_A4_inv_def)
  apply metis
  apply(case_tac "tW s < hW s", simp_all) 
  apply(simp add:pre_A5_inv_def) 
  apply(simp add:pre_A8_inv_def)
  by metis




lemma W_local_A3_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A3"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_W (pcW s') s'"
  using assms apply simp
  apply(simp add:inv_def pre_W_def cW_step_def pre_A3_inv_def pre_write_inv_def)
  by(simp add:tempW_lemmas tempW_basic_lemmas)



lemma W_local_A4_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A4"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_W (pcW s') s'"
  using assms apply simp
  apply(simp add:inv_def pre_W_def cW_step_def pre_A4_inv_def pre_write_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(intro conjI impI)
  apply (simp add: less_diff_conv)
  apply(case_tac "case_1 s") apply(subgoal_tac "\<not>case_2 s") apply simp 
  apply(thin_tac "\<not> case_2 s")
  apply(simp add:case_1_def) 
  apply(subgoal_tac "hW s = fst (last (q s)) + snd (last (q s))") 
  apply blast
  apply (metis cancel_comm_monoid_add_class.diff_cancel le_eq_less_or_eq length_0_conv less_nat_zero_code)
  apply (metis case_split_5)
  apply(subgoal_tac "case_2 s") apply simp 
  apply(thin_tac "\<not>case_1 s") 
  apply(simp add:case_2_def) 
  apply (metis (no_types, lifting) add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq diff_zero le_trans length_greater_0_conv nat_less_le)
  apply (metis)
  apply(simp add:Q_lemmas Q_basic_lemmas tempW_lemmas tempW_basic_lemmas)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(case_tac "case_1 s") apply(subgoal_tac "\<not>case_2 s") apply simp
  apply(thin_tac "\<not> case_2 s")
  apply(simp add:case_1_def)
  apply (metis (no_types, hide_lams) diff_is_0_eq' le_eq_less_or_eq length_pos_if_in_set nth_mem prod.exhaust_sel zero_less_diff)
  apply (metis case_split_5)
  apply(subgoal_tac "case_2 s") apply simp 
  apply(thin_tac "\<not>case_1 s") 
  apply(simp add:case_2_def)
  apply clarify 
  apply(subgoal_tac "ownB s (H s) \<noteq> Q") prefer 2 
  apply (metis F.distinct(19) le_refl)
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) = (i \<le> N \<and> ownB s i = Q)") prefer 2
  apply blast
  apply(subgoal_tac "i<length(q s) \<longrightarrow> snd(q s!i) > 0") prefer 2
  apply (metis nth_mem prod.collapse)
  apply(subgoal_tac "hW s = end(last(q s))") prefer 2 
  apply (metis add.commute add_diff_inverse_nat diff_is_0_eq' end_simp le_eq_less_or_eq le_trans minus_nat.diff_0 nat_less_le)
  apply (metis end_simp nth_mem prod.collapse)
  apply metis
  apply(simp add:Q_lemmas Q_basic_lemmas) (*doable*)
  defer 
  apply(case_tac "case_1 s") apply(subgoal_tac "\<not>case_2 s") apply simp 
  apply(thin_tac "\<not> case_2 s")
  apply(simp add:case_1_def)
  apply(simp add:Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply (metis (no_types, lifting) add_leD1 cancel_comm_monoid_add_class.diff_cancel le_eq_less_or_eq le_zero_eq length_0_conv)
  apply (metis case_split_5)
  apply(subgoal_tac "case_2 s") apply simp 
  apply(thin_tac "\<not>case_1 s") 
  apply(simp add:case_2_def)
  apply(simp add:Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply(clarify)
  apply(case_tac "fst(hd(q s)) = 0") 
  apply (metis add_is_0)
  apply(subgoal_tac "fst(hd(q s)) = e") prefer 2
  apply (metis (no_types, lifting) add_diff_cancel_right' add_lessD1 cancel_comm_monoid_add_class.diff_cancel le_neq_implies_less length_greater_0_conv not_add_less1 ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
  apply(subgoal_tac "hW s<T s") prefer 2
  apply blast
  apply(subgoal_tac " hW s + Data s (numEnqs s) = hW s") prefer 2
  apply (metis add.commute diff_add less_diff_conv nat_less_le trans_less_add2)
  apply(subgoal_tac "T s \<le> fst(hd(q s))") prefer 2
  apply meson
  apply(subgoal_tac "d> Data s (numEnqs s) + hW s ") prefer 2 
  apply (metis add.commute less_add_same_cancel2)
  apply(subgoal_tac "d=e") prefer 2 
  apply (metis less_add_same_cancel1)
  apply (metis not_add_less2)
  apply blast
  apply(clarify)
  apply(intro conjI impI)
  apply(case_tac "case_1 s") apply(subgoal_tac "\<not>case_2 s") apply simp 
  apply(thin_tac "\<not> case_2 s")
  apply(simp add:case_1_def)
  apply(simp add:Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply(subgoal_tac "\<forall>j. j<length(q s) \<longrightarrow> hW s > fst(q s!j)")
  apply (metis Suc_lessD less_natE not_add_less1)
  apply(subgoal_tac "\<forall> a b j. ((a,b)\<in>set(q s) \<and> a\<le>j \<and> j<a+b) \<longrightarrow> ownB s (j) = Q") prefer 2
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply(clarify) 
  apply(subgoal_tac "\<forall>i.(ownB s i=Q \<and> i\<le>N) \<longrightarrow> i<fst (last (q s)) + snd (last (q s))") prefer 2 
  apply (metis (no_types, lifting) F.distinct(19) F.distinct(23) le_eq_less_or_eq linorder_neqE_nat)
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow> ownB s (fst(q s!0)) = Q") prefer 2
  apply (metis (no_types, lifting) hd_conv_nth le_eq_less_or_eq)
  
  apply(subgoal_tac "fst (last (q s)) + snd (last (q s))\<le>hW s") prefer 2
  apply blast
  apply(subgoal_tac "fst(q s!j) + snd(q s!j) \<le>N") prefer 2 
  apply (metis nth_mem prod.collapse)
  apply(subgoal_tac "fst(q s!j) \<le>N") prefer 2 
  apply (metis add_leD1)
  apply (metis (no_types, lifting) le_eq_less_or_eq less_add_same_cancel1 nth_mem prod.collapse)
  apply (metis case_split_5)
  apply(simp add:Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply(case_tac "case_1 s") apply(subgoal_tac "\<not>case_2 s") apply simp 
  apply (metis case_split_5)
  apply(simp add:case_2_def)
  apply(thin_tac "\<not> case_1 s")
  apply clarify
  apply(case_tac "H s \<ge> T s") 
  apply (metis le_imp_less_Suc less_or_eq_imp_le not_less_eq)
  apply(subgoal_tac "H s < T s ") prefer 2
  apply metis
  apply(thin_tac "\<not> T s \<le> H s")
  apply(subgoal_tac "\<forall>i.(hW s \<le>i \<and> i<hW s + Data s (numEnqs s)) \<longrightarrow> ownB s i = B") prefer 2 
  apply (metis (no_types, lifting) Suc_lessD add.commute less_diff_conv less_trans_Suc)
  apply(case_tac "e=f") 
  apply(subgoal_tac "\<forall>i.(ownB s i = Q \<and> i\<le>N)\<longrightarrow>i<b") prefer 2
  apply (metis (no_types, hide_lams) F.distinct(11) F.distinct(19) F.distinct(21) F.distinct(23) F.distinct(3) Suc_pred bot_nat_0.not_eq_extremum diff_Suc_Suc diff_diff_cancel diff_is_0_eq old.nat.inject zero_less_Suc zero_less_diff)
  apply(subgoal_tac "\<forall>a b j.((a,b)\<in>set(q s) \<and> a\<le>j \<and> j<a+b)\<longrightarrow>ownB s j = Q") prefer 2 
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply(subgoal_tac "\<forall>i. i<length(q s) \<longrightarrow> (q s!i) \<in> set(q s)") prefer 2 
  apply (metis nth_mem)
  apply(subgoal_tac "fst(q s!i)< fst(q s!i) + snd(q s!i)") prefer 2 
  apply (metis less_add_same_cancel1 prod.collapse) 
  apply(subgoal_tac "\<forall>a b. (a,b)\<in>set(q s) \<longrightarrow> ownB s (a) = Q") prefer 2
  apply (metis (no_types, hide_lams) Nat.add_0_right le_refl nat_add_left_cancel_less)
  apply(subgoal_tac "\<forall>i. (i<length(q s)) \<longrightarrow> (\<exists>a b. ((a,b)\<in>set(q s) \<and> a=fst(q s!i) \<and> b = snd(q s!i)))") prefer 2
  apply (metis prod.collapse)
  apply(subgoal_tac "\<forall>i. i<length(q s) \<longrightarrow> ownB s (fst(q s!i)) = Q") prefer 2 
  apply (metis (no_types, hide_lams))
  apply(subgoal_tac "\<forall>i.(i<length(q s) \<and> fst(q s!i) < N)\<longrightarrow> fst(q s!i)<b") prefer 2 
  apply (metis less_imp_le_nat)
  apply(subgoal_tac "fst(q s!i) + snd(q s!i)\<le>N") prefer 2 
  apply (metis less_add_same_cancel1 prod.collapse)
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow> fst(q s!i)<b") prefer 2 
  apply (metis (no_types, lifting) add_leD1)
  apply (metis (no_types, lifting) add_lessD1 le_imp_less_Suc less_imp_add_positive not_less_eq)
  apply(case_tac "fst(q s!i) < hW s") 
  apply linarith
  apply(subgoal_tac "\<forall>a b j.((a,b)\<in>set(q s) \<and> a\<le>j \<and> j<a+b)\<longrightarrow>ownB s j = Q") prefer 2 
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply(subgoal_tac "\<forall>i. i<length(q s) \<longrightarrow> (q s!i) \<in> set(q s)") prefer 2 
  apply (metis nth_mem)
  apply(subgoal_tac "fst(q s!i)< fst(q s!i) + snd(q s!i)") prefer 2 
  apply (metis less_add_same_cancel1 prod.collapse) 
  apply(subgoal_tac "\<forall>a b. (a,b)\<in>set(q s) \<longrightarrow> ownB s (a) = Q") prefer 2
  apply (metis (no_types, hide_lams) Nat.add_0_right le_refl nat_add_left_cancel_less)
  apply(subgoal_tac "\<forall>i. (i<length(q s)) \<longrightarrow> (\<exists>a b. ((a,b)\<in>set(q s) \<and> a=fst(q s!i) \<and> b = snd(q s!i)))") prefer 2
  apply (metis prod.collapse)
  apply(subgoal_tac "\<forall>i. i<length(q s) \<longrightarrow> ownB s (fst(q s!i)) = Q") prefer 2 
  apply (metis (no_types, hide_lams))
  apply(subgoal_tac "fst(q s!i) + snd(q s!i)\<le>N") prefer 2 
  apply (metis less_add_same_cancel1 prod.collapse)
  apply(subgoal_tac "fst(q s!i) \<ge>e") 
  apply (metis (no_types, lifting) F.distinct(19) add.commute less_diff_conv less_or_eq_imp_le linorder_neqE_nat)
  apply (metis (no_types, hide_lams) F.distinct(11) F.distinct(19) bot_nat_0.not_eq_extremum diff_is_0_eq diff_self_eq_0 zero_less_diff)
  apply(simp add:Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_def)
  apply clarify 
  apply(subgoal_tac "\<forall>a b j.((a,b)\<in>set(q s) \<and> a\<le>j \<and> j<a+b)\<longrightarrow>ownB s j = Q") prefer 2 
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply(subgoal_tac "\<forall>i. i<length(q s) \<longrightarrow> (q s!i) \<in> set(q s)") prefer 2 
  apply (metis nth_mem)
  apply(subgoal_tac "fst(q s!i)< fst(q s!i) + snd(q s!i)") prefer 2 
  apply (metis less_add_same_cancel1 prod.collapse) 
  apply(subgoal_tac "\<forall>a b. (a,b)\<in>set(q s) \<longrightarrow> ownB s (a) = Q") prefer 2
  apply (metis (no_types, hide_lams) Nat.add_0_right le_refl nat_add_left_cancel_less)
  apply(subgoal_tac "\<forall>i. (i<length(q s)) \<longrightarrow> (\<exists>a b. ((a,b)\<in>set(q s) \<and> a=fst(q s!i) \<and> b = snd(q s!i)))") prefer 2
  apply (metis prod.collapse)
  apply(subgoal_tac "\<forall>a b j.((a,b)\<in>set(q s) \<and> a\<le>j \<and> j\<le>a+b-1)\<longrightarrow>ownB s j = Q") prefer 2 
  apply (metis Suc_diff_1 add_gr_0 le_imp_less_Suc)
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>a+b\<le>hW s")
  apply (metis (no_types, lifting) less_or_eq_imp_le)
  apply(subgoal_tac "\<forall>i.(ownB s i = Q \<and> i\<le>N) \<longrightarrow> i<fst (last (q s)) + snd (last (q s))") prefer 2 
  apply (metis (no_types, lifting) F.distinct(19) F.distinct(23) le_eq_less_or_eq linorder_neqE_nat)
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>a+b\<le>N") prefer 2 
  apply blast
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>b>0") prefer 2
  apply blast
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s) \<and> a\<le>a+b-1 \<and> a+b-1\<le>a+b-1)\<longrightarrow>ownB s (a+b-1) = Q") prefer 2 
  apply (metis Suc_diff_1 add_gr_0 le_imp_less_Suc)
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>a\<le>a+b-1 \<and> a+b-1\<le>a+b-1") prefer 2 
  apply (metis Suc_diff_1 add_gr_0 le_eq_less_or_eq less_Suc_eq_le less_add_same_cancel1)
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>ownB s (a+b-1) = Q") prefer 2 
  apply (metis (no_types, lifting))
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>a+b-1 <fst (last (q s)) + snd (last (q s))") prefer 2 
  apply (metis diff_le_self le_trans)
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>a+b-1 <a+b") prefer 2 
  apply (metis Suc_pred' add_gr_0 lessI)
  apply(subgoal_tac "hW s\<ge>fst (last (q s)) + snd (last (q s))") prefer 2
  apply blast
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>a+b-1 <hW s") prefer 2 
  apply (metis (no_types, lifting) eq_imp_le le_neq_implies_less)
  apply (metis (no_types, lifting) Suc_leI Suc_pred' add_gr_0)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply(clarify)
  apply(case_tac "e=f") 
  apply(subgoal_tac "\<forall>i.(ownB s i = Q \<and> i\<le>N)\<longrightarrow>i<b") prefer 2
  apply (metis (no_types, hide_lams) F.distinct(11) F.distinct(19) F.distinct(21) F.distinct(23) F.distinct(3) Suc_pred bot_nat_0.not_eq_extremum diff_Suc_Suc diff_diff_cancel diff_is_0_eq old.nat.inject zero_less_Suc zero_less_diff)
  apply(subgoal_tac "\<forall>a b j.((a,b)\<in>set(q s) \<and> a\<le>j \<and> j<a+b)\<longrightarrow>ownB s j = Q") prefer 2 
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply(subgoal_tac "\<forall>a b j.((a,b)\<in>set(q s) \<and> a\<le>j \<and> j\<le>a+b-1)\<longrightarrow>ownB s j = Q") prefer 2 
  apply (metis Suc_diff_1 add_gr_0 le_imp_less_Suc)
  apply(subgoal_tac "\<forall>i. i<length(q s) \<longrightarrow> (q s!i) \<in> set(q s)") prefer 2 
  apply (metis nth_mem)
  apply(subgoal_tac "fst(q s!i)< fst(q s!i) + snd(q s!i)") prefer 2 
  apply (metis less_add_same_cancel1 prod.collapse) 
  apply(subgoal_tac "\<forall>a b. (a,b)\<in>set(q s) \<longrightarrow> b>0") prefer 2 
  apply blast
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>a\<le>a+b-1 \<and> a+b-1\<le>a+b") prefer 2 
  apply (metis Suc_diff_1 add_gr_0 diff_le_self less_Suc_eq_le less_add_same_cancel1)
  apply(subgoal_tac "\<forall>a b. (a,b)\<in>set(q s) \<longrightarrow> ownB s (a+b-1) = Q") prefer 2
  apply (metis (no_types, hide_lams) Nat.add_0_right le_refl nat_add_left_cancel_less)
  apply(subgoal_tac "\<forall>i. (i<length(q s)) \<longrightarrow> (\<exists>a b. ((a,b)\<in>set(q s) \<and> a=fst(q s!i) \<and> b = snd(q s!i)))") prefer 2
  apply (metis prod.collapse)
  apply(subgoal_tac "\<forall>i. i<length(q s) \<longrightarrow> ownB s (fst(q s!i)+snd(q s!i)-1) = Q") prefer 2 
  apply (metis (no_types, lifting))
  apply(subgoal_tac "\<forall>i.(i<length(q s) \<and> fst(q s!i)+snd(q s!i)-1 \<le> N)\<longrightarrow> fst(q s!i)+snd(q s!i)-1<b") prefer 2 
  apply (metis (no_types, lifting))
  apply(subgoal_tac "fst(q s!i) + snd(q s!i)\<le>N") prefer 2 
  apply (metis less_add_same_cancel1 prod.collapse)
  apply(subgoal_tac "fst(q s!i) + snd(q s!i)-1\<le>N") prefer 2 
  apply linarith
  apply(subgoal_tac "i<length(q s)") prefer 2 
  apply blast
  apply(subgoal_tac "fst(q s!i)+snd(q s!i)-1<b") prefer 2 
  apply (metis (no_types, lifting))
  apply (metis Suc_leI diff_Suc_1 le_trans less_natE)
  apply(case_tac "fst(q s!i) > hW s") 
  apply linarith
  apply(subgoal_tac "\<forall>a b j.((a,b)\<in>set(q s) \<and> a\<le>j \<and> j<a+b)\<longrightarrow>ownB s j = Q") prefer 2 
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply(subgoal_tac "\<forall>a b j.((a,b)\<in>set(q s) \<and> a\<le>j \<and> j\<le>a+b-1)\<longrightarrow>ownB s j = Q") prefer 2 
  apply (metis Suc_pred' add_gr_0 le_imp_less_Suc)
  apply(subgoal_tac "\<forall>i. i<length(q s) \<longrightarrow> (q s!i) \<in> set(q s)") prefer 2 
  apply (metis nth_mem)
  apply(subgoal_tac "fst(q s!i)< fst(q s!i) + snd(q s!i)") prefer 2 
  apply (metis less_add_same_cancel1 prod.collapse) 
  apply(subgoal_tac "\<forall>a b. (a,b)\<in>set(q s) \<longrightarrow> ownB s (a) = Q") prefer 2
  apply (metis (no_types, hide_lams) Nat.add_0_right le_refl nat_add_left_cancel_less)
  apply(subgoal_tac "\<forall>a b. (a,b)\<in>set(q s) \<longrightarrow> b>0") prefer 2
  apply meson
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s))\<longrightarrow>a\<le>a+b-1\<and> a+b-1\<le>a+b-1") prefer 2  
  apply (metis Suc_diff_1 add_gr_0 le_eq_less_or_eq less_Suc_eq_le less_add_same_cancel1)
  apply(subgoal_tac "\<forall>a b j.((a,b)\<in>set(q s))\<longrightarrow>ownB s (a+b-1) = Q") prefer 2 
  apply (metis (no_types, lifting))
  apply(subgoal_tac "\<forall>i. (i<length(q s)) \<longrightarrow> (\<exists>a b. ((a,b)\<in>set(q s) \<and> a=fst(q s!i) \<and> b = snd(q s!i)))") prefer 2
  apply (metis prod.collapse)
  apply(subgoal_tac "\<forall>i. i<length(q s) \<longrightarrow> ownB s (fst(q s!i)+snd(q s!i)-1) = Q") prefer 2 
  apply (metis (no_types, hide_lams))
  apply(subgoal_tac "fst(q s!i) + snd(q s!i)\<le>N") prefer 2 
  apply (metis less_add_same_cancel1 prod.collapse) 
  apply(subgoal_tac "fst(q s!i) < hW s") prefer 2 
  apply blast
  by (metis (no_types, hide_lams) F.distinct(19) diff_is_0_eq' less_nat_zero_code linorder_neqE_nat nat_le_linear zero_less_diff)



    


lemma W_local_A5_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A5"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_W (pcW s') s'"
  using assms apply simp
  apply(simp add:inv_def pre_W_def cW_step_def pre_A5_inv_def pre_write_inv_def)
  apply(case_tac "Data s (numEnqs s) \<le> N - hW s", simp_all)
  apply(simp_all add: pre_A6_inv_def)
  apply(case_tac "Data s (numEnqs s) < tW s", simp_all)
  apply(simp_all add: pre_A7_inv_def)  
  by(simp_all add: pre_A8_inv_def)


lemma W_local_A6_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A6"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_W (pcW s') s'"
  using assms apply simp
  apply(simp add:cW_step_def pre_W_def)
  apply(simp add:inv_def pre_A6_inv_def)
  apply(subgoal_tac "H s\<ge>T s") prefer 2 
  apply meson apply(subgoal_tac "\<not>case_2 s") prefer 2
  apply (metis case_split_2)
  apply(subgoal_tac "case_1 s") prefer 2
  apply blast
  apply(thin_tac "\<not>case_2 s") 
  apply(simp add:pre_write_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(intro conjI impI)
  apply (metis Nat.le_diff_conv2 add.commute)
  apply(simp add:case_1_def)
  apply (metis cancel_comm_monoid_add_class.diff_cancel le_eq_less_or_eq le_zero_eq length_0_conv)
  apply (metis (no_types, hide_lams) F.distinct(19) Q_owns_bytes_def diff_self_eq_0 le_eq_less_or_eq less_nat_zero_code ran_indices_lem5)
  apply(simp add:case_1_def)
  defer
  apply(simp add:case_1_def)
  apply (metis (no_types, lifting) cancel_comm_monoid_add_class.diff_cancel le_eq_less_or_eq le_zero_eq length_0_conv trans_le_add1)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply(subgoal_tac "hW s = H s") prefer 2 
  apply presburger
  apply(clarify)
  apply(intro conjI impI)
  apply(subgoal_tac "\<forall>i.(ownB s i = Q \<and> i\<le>N)\<longrightarrow>i<fst (last (q s)) + snd (last (q s))") prefer 2 
  apply (metis (no_types, lifting) F.distinct(19) F.distinct(23) le_eq_less_or_eq linorder_neqE_nat)
  apply(subgoal_tac "\<forall>a b j.((a,b)\<in>set(q s)\<and>a \<le> j \<and> j<a+b ) \<longrightarrow> ownB s j = Q") prefer 2
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(q s) \<longrightarrow> ownB s (a) = Q") prefer 2 
  apply (metis (no_types, hide_lams) Nat.add_0_right le_refl nat_add_left_cancel_less)
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(q s) \<longrightarrow> a<N") prefer 2 
  apply (metis F.distinct(23) add_leD1 nat_less_le)
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(q s) \<longrightarrow> a<hW s")
  apply (metis (no_types, lifting) le_eq_less_or_eq nth_mem prod.collapse)
  apply (metis le_neq_implies_less less_or_eq_imp_le)
  apply(subgoal_tac "\<forall>i.(ownB s i = Q \<and> i\<le>N)\<longrightarrow>i<fst (last (q s)) + snd (last (q s))") prefer 2 
  apply (metis (no_types, lifting) F.distinct(19) F.distinct(23) le_eq_less_or_eq linorder_neqE_nat)
  apply(subgoal_tac "\<forall>a b j.((a,b)\<in>set(q s)\<and>a \<le> j \<and> j<a+b ) \<longrightarrow> ownB s j = Q") prefer 2
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(q s)\<longrightarrow>a \<le> a+b-1 \<and> a+b-1<a+b") prefer 2 
  apply (metis Suc_diff_1 add_gr_0 diff_less less_Suc_eq_le less_add_same_cancel1 less_one)
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(q s) \<longrightarrow> ownB s (a+b-1) = Q") prefer 2
  apply (metis (no_types, lifting))
  apply(subgoal_tac "\<exists>a b.((a,b)\<in>set(q s) \<and> a=fst(q s!i) \<and> b=Data s (numDeqs s + i))") prefer 2
  apply (metis nth_mem prod.collapse)
  by (metis (no_types, hide_lams) diff_is_0_eq' linorder_neqE_nat nat_le_linear zero_less_diff)




lemma W_local_A7_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A7"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_W (pcW s') s'"
  using assms apply simp
  apply(simp add:cW_step_def pre_W_def)
  apply(simp add:inv_def pre_A7_inv_def)
  apply(subgoal_tac "H s\<ge>T s") prefer 2 
  apply meson apply(subgoal_tac "\<not>case_2 s") prefer 2
  apply (metis case_split_2)
  apply(subgoal_tac "case_1 s") prefer 2
  apply blast
  apply(thin_tac "\<not>case_2 s") 
  apply(simp add:pre_write_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(intro conjI impI)
  apply (metis (no_types, hide_lams) F.distinct(19) Q_owns_bytes_def bot_nat_0.not_eq_extremum less_nat_zero_code ran_indices_lem5)
  apply(simp add:case_1_def) 
  defer
  apply(simp add:case_1_def)
  apply (metis F.distinct(19) cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq le_neq_implies_less le_zero_eq length_0_conv)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply(subgoal_tac "hW s = H s") prefer 2 
  apply presburger
  apply(clarify)
  apply(subgoal_tac "\<forall>i.(ownB s i = Q \<and> i\<le>N)\<longrightarrow>i\<ge>fst (hd (q s))") prefer 2 
  apply (metis (no_types, hide_lams) F.distinct(11) F.distinct(19) diff_is_0_eq' linorder_neqE_nat nat_le_linear zero_less_diff)
  apply(subgoal_tac "\<forall>a b j.((a,b)\<in>set(q s)\<and>a \<le> j \<and> j<a+b ) \<longrightarrow> ownB s j = Q") prefer 2
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(q s) \<longrightarrow> ownB s (a) = Q") prefer 2 
  apply (metis (no_types, hide_lams) Nat.add_0_right le_refl nat_add_left_cancel_less)
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(q s) \<longrightarrow> a<N") prefer 2 
  apply (metis F.distinct(23) add_leD1 nat_less_le)
  apply(subgoal_tac "\<forall>i.(i\<le>Data s (numEnqs s))\<longrightarrow>ownB s i = B") prefer 2 
  apply (metis add_lessD1 nat_le_iff_add)
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(q s) \<longrightarrow> a>Data s (numEnqs s)") prefer 2
  apply (metis F.distinct(19) Suc_le_lessD not_less_eq_eq)
  by (metis nth_mem prod.collapse)
   
   



lemma W_local_A8_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A8"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_W (pcW s') s'"
  using assms apply simp
  apply(simp add:cW_step_def pre_W_def)
  apply(simp add:inv_def pre_A8_inv_def)
  apply(case_tac "N < Data s (numEnqs s)") 
  apply (metis leD) apply(intro conjI impI) 
  apply linarith apply(simp add:pre_OOM_inv_def) apply(intro conjI impI)
  defer 
  apply(case_tac "case_1 s") apply simp  apply(simp add:case_1_def)
  apply metis
  apply meson apply(case_tac "case_1 s") apply simp  apply(simp add:case_1_def)
  apply metis
  apply(simp add:case_2_def)
  by (metis le_antisym less_or_eq_imp_le)





lemma W_local_Enqueue_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = Enqueue"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_W (pcW s') s'"
  using assms apply simp
  apply(simp add:cW_step_def pre_W_def)
  apply(simp add:inv_def pre_enqueue_inv_def)
  apply(intro conjI impI) 
  apply(simp add:pre_acquire_inv_def) apply(intro conjI impI)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_def) 
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis F.distinct(5) eq_imp_le less_add_same_cancel1)
  apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) 
  apply clarify
  apply(intro conjI impI)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_def) apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_def)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_def) apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_def)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_def)
  apply (metis add_cancel_left_left less_imp_le_nat old.prod.inject prod.collapse tempW_def)
  apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_def)
  apply(simp add:pre_acquire_inv_def)
  apply(intro conjI impI) 
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis F.distinct(5) le_eq_less_or_eq less_add_same_cancel1)
  apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_def)
  apply (metis F.distinct(5) le_eq_less_or_eq less_add_same_cancel1)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis F.distinct(5) le_eq_less_or_eq less_add_same_cancel1)
  apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_def)
  apply (metis F.distinct(5) le_eq_less_or_eq less_add_same_cancel1)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis F.distinct(5) le_eq_less_or_eq less_add_same_cancel1)
  apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_def)
  by (metis Suc_diff_Suc Zero_not_Suc diff_is_0_eq' less_or_eq_imp_le)



lemma W_local_idleW_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = idleW"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_W (pcW s') s'"
  using assms apply simp
  apply(simp add:cW_step_def pre_W_def)
  apply(simp add:inv_def pre_acquire_inv_def) 
  apply(case_tac " numEnqs s < n", simp_all)
  apply(simp add: pre_A1_inv_def) 
  apply blast
  by(simp add: pre_finished_inv_def) 



lemma W_local_OOM_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = OOM"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_W (pcW s') s'"
  using assms apply simp
  apply(simp add:cW_step_def pre_W_def)
  apply(simp add:inv_def pre_OOM_inv_def)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(simp add:inv_def pre_acquire_inv_def)
  apply(case_tac "case_1 s") apply(simp ) apply(simp add:case_1_def)
  apply(intro conjI impI) 
  apply (metis eq_imp_le less_imp_le_nat linorder_neqE_nat)
  apply (metis le_neq_implies_less le_refl)
  apply (metis diff_self_eq_0 le_neq_implies_less le_refl le_zero_eq length_0_conv) 
  apply (metis le_refl length_0_conv nat_less_le ordered_cancel_comm_monoid_diff_class.le_imp_diff_is_add plus_nat.add_0)
  apply (metis diff_self_eq_0 le_antisym le_refl nat_less_le zero_less_diff)
  apply metis
  apply(simp add:case_2_def)
  apply(intro conjI impI) 
  apply (metis)
  apply (metis)
  apply (metis)
  apply (metis)
  apply metis 
  apply (metis le_antisym nat_less_le)
  apply(simp add:pre_OOM_inv_def)
  by blast



lemma W_local_FinishedW_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = FinishedW"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_W (pcW s') s'"
  using assms apply simp
  by(simp add:cW_step_def pre_W_def)




lemma W_local_Write_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = Write"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_W (pcW s') s'"
  using assms apply simp
  apply(simp add:pre_W_def cW_step_def)
  apply(simp add:inv_def pre_write_inv_def)
  apply(simp add:pre_enqueue_inv_def)
  apply(intro conjI impI)
  apply clarify
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) apply clarify
  apply(intro conjI impI)
  apply(subgoal_tac "i<T s\<longrightarrow>ownB s i=B") prefer 2
  apply metis
  apply(subgoal_tac "T s\<le>i \<and> i<b\<longrightarrow>ownB s i = R") prefer 2 
  apply metis
  apply(subgoal_tac "b\<le>i \<and> i<c\<longrightarrow>ownB s i = Q") prefer 2 
  apply metis
  apply (metis (mono_tags, lifting) F.distinct(1) F.distinct(3) F.distinct(5) Suc_le_lessD le_eq_less_or_eq not_less_eq_eq trans_less_add1)
  apply(subgoal_tac "end(tempW s)\<le>i \<and> i<N\<longrightarrow> ownB s i = B") prefer 2
  apply metis
  apply (metis F.distinct(5) F.distinct(9) le_neq_implies_less)
  apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(clarify)
  apply(intro conjI impI) 
  apply (metis F.distinct(1) F.distinct(3) eq_imp_le linorder_neqE_nat nat_less_le trans_less_add1)
  apply (metis F.distinct(1) F.distinct(3) F.distinct(5) F.distinct(7) F.distinct(9) le_neq_implies_less less_or_eq_imp_le linorder_neqE_nat)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) 
  apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_def) 
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(case_tac "case_1 s") apply(simp add:case_1_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) 
  apply(subgoal_tac "case_2 s") prefer 2 
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(case_tac "case_1 s") apply(simp add:case_1_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) 
  apply(subgoal_tac "case_2 s") prefer 2 
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(case_tac "case_1 s") apply(simp add:case_1_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) 
  apply (metis le_antisym le_trans less_nat_zero_code)
  apply(subgoal_tac "case_2 s") prefer 2 
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  by(simp add:tempW_lemmas tempW_basic_lemmas)





lemma W_local_BTS_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = BTS"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_W (pcW s') s'"
  using assms apply simp
  by(simp add:cW_step_def pre_W_def)



lemma local_pre_W_pre: 
  assumes "con_assms s"
  and "pcw = pcW s"
  and "pre_W pcw s"
  and "inv s"
  and "cW_step pcw s s'"
shows "pre_W (pcW s') s'"
  using assms apply(case_tac "pcW s") 
  using W_local_A1_lemma [where s=s and s'=s'] apply blast 
  using W_local_A2_lemma [where s=s and s'=s'] apply blast 
  using W_local_A3_lemma [where s=s and s'=s'] apply blast  
  using W_local_A4_lemma [where s=s and s'=s'] apply blast   
  using W_local_A5_lemma [where s=s and s'=s'] apply blast  
  using W_local_A6_lemma [where s=s and s'=s'] apply blast    
  using W_local_A7_lemma [where s=s and s'=s'] apply blast     
  using W_local_A8_lemma [where s=s and s'=s'] apply blast       
  using W_local_Enqueue_lemma [where s=s and s'=s'] apply blast  
  using W_local_idleW_lemma [where s=s and s'=s'] apply blast    
  using W_local_OOM_lemma [where s=s and s'=s'] apply blast         
  using W_local_FinishedW_lemma [where s=s and s'=s'] apply blast   
  using W_local_Write_lemma [where s=s and s'=s'] apply blast   
  using W_local_BTS_lemma [where s=s and s'=s'] by blast       




























































































(*******************************Local R pre post lemmas*************************************)
lemma R_local_release_pre_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcR s = Release"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_R (pcR s') s'"
  using assms apply(simp add:pre_R_def) apply clarify
  apply(subgoal_tac "ownT s' \<noteq> R") prefer 2 
  apply(simp add:pre_dequeue_inv_def)
  apply(simp add:cR_step_def)
  apply(subgoal_tac "ownT s = R") prefer 2 
  apply(simp add:pre_Release_inv_def)
  apply(simp add:cR_step_def)
  apply(case_tac "tR s = fst(tempR s)") apply simp_all
  apply(simp add:pre_dequeue_inv_def)
   apply(intro conjI impI)
  apply(simp add:pre_Release_inv_def)
  apply(simp add:pre_Release_inv_def)
  apply(simp add:pre_Release_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "hd(q s)\<in>set(q s)") prefer 2 
  apply (metis hd_in_set)
  apply(subgoal_tac "fst(q s!0) = 0") prefer 2 
  apply (metis hd_conv_nth)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(case_tac "case_1 s ") apply simp apply(simp add:case_1_def)
  apply (metis diff_self_eq_0 le_neq_implies_less length_pos_if_in_set less_nat_zero_code)
  apply(simp) apply(thin_tac "\<not> case_1 s") apply(simp add:case_2_def)
  apply(clarify)
  apply(subgoal_tac "e=f") prefer 2
  apply (metis gr_implies_not0 le_neq_implies_less)
  apply(subgoal_tac "(i<N \<and> ownB s i = Q )\<longrightarrow> i<ba") prefer 2 
  apply (metis (mono_tags, hide_lams) F.distinct(11) F.distinct(19) F.distinct(21) F.distinct(3) diff_is_0_eq neq0_conv zero_less_diff)
  apply(subgoal_tac "aa=0") prefer 2
  apply (metis gr_implies_not0)
  apply(subgoal_tac "a+b\<le>ba")
  apply (metis (no_types, lifting) Suc_le_eq le_add1 le_trans not_less_eq_eq)
  apply(subgoal_tac "(a\<le>i \<and> i<a+b) \<longrightarrow> (ownB s i = Q)") prefer 2
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply(subgoal_tac "a = i\<longrightarrow> ownB s i = Q") prefer 2
  apply (metis le_refl less_add_same_cancel1)
  apply(subgoal_tac "fst(tempR s) = T s \<longrightarrow> ownB s (T s) =R") prefer 2
  apply (metis gr_implies_not0 le_refl)
  apply(subgoal_tac "T s > ba") prefer 2
  apply (metis le0 less_nat_zero_code nat_neq_iff)
  apply(subgoal_tac "a=i\<longrightarrow>i<ba") prefer 2 
  apply (metis (no_types, lifting) F.distinct(23) le_add1 le_neq_implies_less le_trans)
  apply(subgoal_tac "a+b-1 = i \<longrightarrow>ownB s i=Q") prefer 2
  apply (metis Suc_diff_1 add_gr_0 lessI less_Suc_eq_le less_add_same_cancel1)
  apply(subgoal_tac "\<nexists>i.(i\<ge>ba \<and> ownB s i = Q \<and> i\<le>N)") prefer 2 
  apply (metis (no_types, hide_lams) F.distinct(11) F.distinct(19) F.distinct(21) F.distinct(23) F.distinct(3) bot_nat_0.not_eq_extremum diff_diff_cancel diff_is_0_eq diff_self_eq_0 zero_less_diff)
  apply(subgoal_tac "a=i \<and> ownB s i = Q \<longrightarrow> i<ba") prefer 2
  apply meson
  defer defer
  apply(simp add:pre_dequeue_inv_def)
  apply(intro conjI impI)
  apply(simp add:pre_Release_inv_def)
  apply(simp add:pre_Release_inv_def)
  apply(simp add:pre_Release_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "fst(hd(q s)) = 0") prefer 2 
  apply blast
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_def)
  apply metis
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis head_q0 length_greater_0_conv)
  prefer 3 
  apply(simp add:inv_def)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_def pre_Release_inv_def)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_Release_inv_def tempR_lemmas tempR_basic_lemmas) 
  apply(simp add:Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply(clarify) apply(intro conjI impI)
  apply (metis (no_types, lifting) bot_nat_0.extremum_uniqueI diff_self_eq_0 le_neq_implies_less length_0_conv)
  apply(subgoal_tac "hd(q s) \<in> set(q s)") prefer 2
  apply (metis hd_in_set)
  apply(subgoal_tac "i\<le>N") prefer 2
  apply (metis (no_types, lifting) le_trans less_or_eq_imp_le prod.collapse)
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) = (i \<le> N \<and> ownB s i = Q)") prefer 2 apply blast
  apply(subgoal_tac "\<forall>a b i.((a,b)\<in>set(q s) \<and> i\<ge>a \<and> i<a+b) \<longrightarrow> ownB s i=Q") prefer 2 
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply (metis (no_types, lifting) prod.collapse)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply(simp add:case_1_def pre_Release_inv_def)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_Release_inv_def tempR_lemmas tempR_basic_lemmas) 
  apply(simp add:Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply(clarify) apply(intro conjI impI) 
  apply(subgoal_tac "\<forall>i. (\<exists>x. (\<exists>a b. x = {i. a \<le> i \<and> i < a + b} \<and> (a, b) \<in> set (q s)) \<and> i \<in> x) = (i \<le> N \<and> ownB s i = Q)") prefer 2 apply blast
  apply(subgoal_tac "hd(q s) \<in> set(q s)") prefer 2
  apply (metis hd_in_set)
  apply(subgoal_tac "a = 0") prefer 2 
  apply (metis less_nat_zero_code)
  apply(case_tac "fst(hd(q s)) = e") 
  apply (metis gr_implies_not0)
  apply(subgoal_tac "fst(hd(q s)) = 0") prefer 2
  apply metis
  apply(subgoal_tac "b\<le>H s") prefer 2
  apply fastforce
  apply(subgoal_tac "H s< T s") prefer 2
  apply fastforce
  apply(subgoal_tac "b< T s") prefer 2
  apply (metis le0 le_refl less_nat_zero_code nat_neq_iff)
  apply(subgoal_tac "i\<ge>end(hd(q s))") 
  apply (metis Suc_leI end_simp not_less_eq_eq)
  apply(subgoal_tac "e = f") prefer 2 
  apply (metis le_neq_implies_less)
  apply(subgoal_tac "\<forall>a b i.((a,b)\<in>set(q s) \<and> i\<ge>a \<and> i<a+b) \<longrightarrow> ownB s i=Q") prefer 2 
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply(subgoal_tac "i\<ge>T s") prefer 2
  apply (metis less_Suc_eq_le not_less_eq)
  apply(subgoal_tac "\<forall>i.(i\<ge>a \<and> i<end(hd(q s))) \<longrightarrow> ownB s i = Q")
  prefer 2 
  apply (metis (no_types, lifting) end_simp prod.collapse)
  apply (metis F.distinct(11) less_Suc_eq_le not_less_eq)
  apply(subgoal_tac "\<forall>a b i.((a,b)\<in>set(q s) \<and> i\<ge>a \<and> i<a+b) \<longrightarrow> ownB s i=Q") prefer 2 
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply (metis (no_types, lifting) list.set_sel(1) prod.collapse)
  apply(simp add:inv_def)
  apply(case_tac "case_1 s") apply simp 
  apply(simp add:case_1_def pre_Release_inv_def)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_Release_inv_def tempR_lemmas tempR_basic_lemmas) 
  apply(simp add:Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply metis
  apply(simp add:case_2_def pre_Release_inv_def) apply(thin_tac "\<not>case_1 s")
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_Release_inv_def tempR_lemmas tempR_basic_lemmas) 
  apply(simp add:Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply(clarify)
  apply(intro conjI impI)
  apply(subgoal_tac "\<forall>a b i.((a,b)\<in>set(q s) \<and> i\<ge>a \<and> i<a+b) \<longrightarrow> ownB s i=Q") prefer 2 
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply (metis (no_types, hide_lams) F.distinct(21) less_imp_Suc_add list.set_sel(1) nat.distinct(1) nat_less_le prod.exhaust_sel)
  apply (metis head_q0 length_greater_0_conv)
  apply(subgoal_tac "\<forall>a b i.((a,b)\<in>set(q s) \<and> i\<ge>a \<and> i<a+b) \<longrightarrow> ownB s i=Q") prefer 2 
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply (metis (no_types, lifting) list.set_sel(1) prod.collapse)
  apply(subgoal_tac "\<forall>a b i.((a,b)\<in>set(q s) \<and> i\<ge>a \<and> i<a+b) \<longrightarrow> ownB s i=Q") prefer 2 
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply(subgoal_tac "aa=0") prefer 2
  apply blast
  apply(subgoal_tac "\<forall>a b.((a,b)\<in>set(q s)) \<longrightarrow> a+b\<le>N") prefer 2
  apply meson
  apply(subgoal_tac "\<forall>a b i.((a,b)\<in>set(q s) \<and> i\<ge>a \<and> i<a+b) \<longrightarrow> ownB s i=Q") prefer 2 
  apply (metis (no_types, lifting) mem_Collect_eq)
  apply(subgoal_tac "\<forall>j.(a\<le>j \<and> j<b+a) \<longrightarrow> ownB s j = Q") prefer 2
  apply (metis add.commute)
  by (metis (no_types, hide_lams) Suc_eq_plus1 add_diff_inverse_nat add_leD1 diff_add_inverse2 diff_le_self less_eq_Suc_le zero_less_diff)




lemma R_local_idle_pre_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcR s = idleR"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_R (pcR s') s'"
  using assms apply(simp add:pre_R_def) apply clarify
  apply(case_tac "q s=[]") 
  using cR_step_def apply auto[1] apply(subgoal_tac "ownT s = Q") prefer 2 
  apply(simp add:pre_dequeue_inv_def)
  apply(simp add:cR_step_def)
  apply(simp add:pre_Read_inv_def)
  apply(intro conjI impI)
  apply(simp add:inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_dequeue_inv_def)
  apply (metis add_cancel_right_right head_q0 length_greater_0_conv)
  apply(simp add:inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_dequeue_inv_def)
  apply (metis add_cancel_right_right head_q0 length_greater_0_conv)
  apply(simp add:inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_dequeue_inv_def)
  apply (metis diff_is_0_eq' le_trans length_0_conv not_less_eq_eq)
  apply(simp add:inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_dequeue_inv_def)
  apply(simp add:inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_dequeue_inv_def)
  apply (metis diff_is_0_eq' length_0_conv not_less_eq_eq)
  apply(simp add:inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_dequeue_inv_def)
  apply (metis length_greater_0_conv plus_nat.add_0)
  apply(simp add:inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_dequeue_inv_def)
  apply (metis hd_in_set less_nat_zero_code)
  apply(simp add:inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_dequeue_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply(intro conjI impI) 
  apply(subgoal_tac "(\<forall>i. i < length (q s) \<and> 0 < i \<longrightarrow>
         fst (q s ! (i - Suc 0)) + snd (q s ! (i - Suc 0)) = fst (q s ! i) \<or> fst (q s ! i) = 0)") prefer 2
  apply presburger
  apply(subgoal_tac "fst(hd(q s)) = fst(q s!0)") prefer 2
  apply (metis Q_ind_imp_tail_ind_1)
  apply(subgoal_tac "fst(hd(tl(q s))) = fst(q s!1)") prefer 2 
  apply (metis One_nat_def hd_conv_nth length_greater_0_conv nth_tl)
  apply (metis (no_types, lifting) One_nat_def Q_ind_imp_tail_ind_1 diff_Suc_1 length_greater_0_conv length_tl less_one zero_less_diff)
  apply(subgoal_tac "fst(hd(q s)) = fst(q s!0)") prefer 2
  apply (metis Q_ind_imp_tail_ind_1)
  apply(subgoal_tac "fst(hd(tl(q s))) = fst(q s!1)") prefer 2 
  apply (metis One_nat_def hd_conv_nth length_greater_0_conv nth_tl)
  apply (metis (no_types, lifting) One_nat_def Suc_eq_plus1 Suc_neq_Zero length_greater_0_conv length_tl less_diff_conv nth_tl)
  apply(subgoal_tac "fst(hd(q s)) = fst(q s!0)") prefer 2
  apply (metis Q_ind_imp_tail_ind_1)
  apply(subgoal_tac "fst(hd(tl(q s))) = fst(q s!1)") prefer 2 
  apply (metis One_nat_def hd_conv_nth length_greater_0_conv nth_tl)
  apply(subgoal_tac "i<length(q s) - Suc 0 \<longrightarrow> (tl (q s) ! i )\<in>set (q s)") prefer 2
  apply (metis One_nat_def length_tl list.set_sel(2) nth_mem)
  apply(subgoal_tac "(hd (q s))\<in>set (q s)") prefer 2
  apply (metis hd_in_set)
  apply simp apply clarify
  apply (intro conjI impI) apply(subgoal_tac "snd(hd(q s)) = snd(q s!0)") prefer 2 
  apply (metis Q_ind_imp_tail_ind_1) apply simp 
  apply(subgoal_tac "\<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a < aa \<longrightarrow> a + b \<le> aa") prefer 2
  apply blast
  apply(subgoal_tac "\<forall>i.(i<length(q s) -1)\<longrightarrow>(tl(q s)!i)\<in>set(q s)") prefer 2
  apply (metis length_tl list.set_sel(2) nth_mem)
  apply(subgoal_tac "tl(q s)!ia \<in>set(q s)") prefer 2
  apply (metis One_nat_def)
  apply(subgoal_tac "fst(tl(q s)!ia) >fst(hd(q s))") prefer 2
  apply presburger
  apply (metis (no_types, lifting) list.set_sel(1) prod.collapse)
  apply(subgoal_tac "\<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a < aa \<longrightarrow> a + b \<le> aa") prefer 2
  apply blast
  apply(subgoal_tac "\<forall>i.(i<length(q s) -1)\<longrightarrow>(tl(q s)!i)\<in>set(q s)") prefer 2
  apply (metis length_tl list.set_sel(2) nth_mem)
  apply(subgoal_tac "tl(q s)!ia \<in>set(q s)") prefer 2
  apply (metis One_nat_def)
  apply(subgoal_tac "fst(tl(q s)!ia) <fst(hd(q s))") prefer 2
  apply presburger
  apply (metis (no_types, lifting) list.set_sel(1) prod.collapse)
  apply(subgoal_tac "hd(q s)\<in>set(q s)") prefer 2 
  apply (metis hd_in_set)
  apply(subgoal_tac "last (tl (q s))\<in>set(q s)") prefer 2
  apply (metis last_in_set last_tl) 
  apply (metis fst_conv last_tl surj_pair)
  apply (metis Nat.add_0_right hd_conv_nth length_greater_0_conv)
  apply (metis add_cancel_right_right head_q0 length_greater_0_conv) defer
  apply(simp add:inv_def)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_def) 
  apply (metis bot_nat_0.extremum_uniqueI bot_nat_0.not_eq_extremum diff_is_0_eq' length_greater_0_conv)
  apply(simp) apply(thin_tac "\<not> case_1 s") apply(simp add:case_2_def)
  apply meson
  apply(simp add:inv_def)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(subgoal_tac "hd(q s)\<in>set(q s)") prefer 2 
  apply (metis hd_in_set) 
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_def)
  apply(simp add:pre_dequeue_inv_def)
  apply (metis F.distinct(13) bot_nat_0.extremum_uniqueI diff_self_eq_0 le_neq_implies_less length_0_conv)
  apply simp apply(thin_tac "\<not>case_1 s")  apply(simp add:case_2_def)
  apply(simp add:pre_dequeue_inv_def)
  by (metis diff_self_eq_0 fst_conv le0 le_trans length_greater_0_conv nat_less_le plus_nat.add_0 snd_conv)




lemma R_local_read_pre_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcR s = Read"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_R (pcR s') s'"
  using assms apply(simp add:pre_R_def) apply clarify
  apply(simp add:cR_step_def)
  apply(simp add:pre_Release_inv_def)
  apply(intro conjI impI)
  apply(simp add:pre_Read_inv_def)
  apply(simp add:pre_Read_inv_def)
  apply(simp add:inv_def) apply(simp add:Q_lemmas Q_basic_lemmas) apply(subgoal_tac "hd(q s)\<in>set(q s)")
  prefer 2 
  apply (meson list.set_sel(1))
  apply (metis Nat.add_0_right hd_conv_nth length_pos_if_in_set)
  apply(simp add:pre_Read_inv_def)
  apply(simp add:pre_Read_inv_def)
  apply(simp add:pre_Read_inv_def)
  apply(simp add:pre_Read_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply(intro conjI impI)
  apply(simp add:pre_Read_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(simp add:pre_Read_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(subgoal_tac "snd (tempR s) = Data s (numDeqs s - Suc 0)") prefer 2
  apply blast
  apply metis
  apply(simp add:pre_Read_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(simp add:pre_Read_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(subgoal_tac "snd (tempR s) = Data s (numDeqs s - Suc 0)") prefer 2
  apply blast 
  apply force
  apply(simp add:pre_Read_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(simp add:pre_Read_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(simp add:pre_Read_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(simp add:pre_Read_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(simp add:pre_Read_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(simp add:pre_Read_inv_def tempR_lemmas tempR_basic_lemmas)
  apply(simp add:pre_Read_inv_def tempR_lemmas tempR_basic_lemmas)
  by(simp add:pre_Read_inv_def tempR_lemmas tempR_basic_lemmas)


lemma R_local_pre_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_R (pcR s') s'"
  using assms apply(case_tac "pcR s") 
  using R_local_release_pre_lemma [where s=s and s'=s'] apply blast           (*done*)
  using R_local_idle_pre_lemma [where s=s and s'=s'] apply blast           (*done*)
  using R_local_read_pre_lemma [where s=s and s'=s'] by blast           (*done*)


























































(*******************************GLOBAL W_step shows preR*************************************)


lemma pcR_doesnt_change_with_W:
  assumes "inv s"
  and "con_assms s"
  and "pre_R (pcR s) s"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pcR s'=pcR s"
 using assms apply simp
  apply(case_tac "pcW s ", simp add:cW_step_def)
  apply(simp add:cW_step_def)
  apply(simp add:cW_step_def)
  apply(simp add:cW_step_def)
  apply(simp add:cW_step_def)
  apply(simp add:cW_step_def)
  apply(simp add:cW_step_def)
  apply(simp add:cW_step_def)
  apply(simp add:cW_step_def)
  apply(simp add:cW_step_def) apply(cases "numEnqs s < n") 
  apply(simp add:B_acquire_def) apply(simp add:B_acquire_def) 
  apply(simp add:cW_step_def) apply(cases "tW s \<noteq> T s") 
  apply(simp add:cW_step_def) 
  apply(simp add:cW_step_def) 
  apply(simp add:cW_step_def) 
  apply(simp add:cW_step_def) 
  by(simp add:cW_step_def) 


lemma supporting_strange:
  "\<forall>i<(length (q s)).
       (fst (tempR s) < fst ((q s @ [(offset s, Data s (numEnqs s))]) ! i) \<longrightarrow>
        fst (tempR s) + snd (tempR s) \<le> fst ((q s @ [(offset s, Data s (numEnqs s))]) ! i)) \<and>
       (fst ((q s @ [(offset s, Data s (numEnqs s))]) ! i) < fst (tempR s) \<longrightarrow>
        fst ((q s @ [(offset s, Data s (numEnqs s))]) ! i) +
        snd ((q s @ [(offset s, Data s (numEnqs s))]) ! i)
        \<le> fst (tempR s)) \<Longrightarrow> 
       (fst (tempR s) < fst ((offset s, Data s (numEnqs s))) \<longrightarrow>
        fst (tempR s) + snd (tempR s) \<le> fst ((offset s, Data s (numEnqs s)))) \<and>
       (fst ((offset s, Data s (numEnqs s))) < fst (tempR s) \<longrightarrow>
        fst ((offset s, Data s (numEnqs s))) +
        snd ((offset s, Data s (numEnqs s)))
        \<le> fst (tempR s))
\<Longrightarrow>
 \<forall>i<Suc (length (q s)).
       (fst (tempR s) < fst ((q s @ [(offset s, Data s (numEnqs s))]) ! i) \<longrightarrow>
        fst (tempR s) + snd (tempR s) \<le> fst ((q s @ [(offset s, Data s (numEnqs s))]) ! i)) \<and>
       (fst ((q s @ [(offset s, Data s (numEnqs s))]) ! i) < fst (tempR s) \<longrightarrow>
        fst ((q s @ [(offset s, Data s (numEnqs s))]) ! i) +
        snd ((q s @ [(offset s, Data s (numEnqs s))]) ! i)
        \<le> fst (tempR s))"
  by (metis less_SucE nth_append_length)



lemma preRead_doesnt_change_with_W:
  assumes "inv s"
  and "con_assms s"
  and "pre_Read_inv s"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_Read_inv s'"
  using assms apply simp
  apply(simp add:pre_Read_inv_def) 
  apply(intro conjI impI)
  apply(simp add:pre_W_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply(cases "pcW s", simp_all)
  apply(simp_all add:cW_step_def)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(simp add:pre_W_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply(cases "pcW s", simp_all)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(simp add:pre_write_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:inv_def)
  apply (metis F.distinct(1) eq_imp_le fst_eqD less_add_same_cancel1 snd_eqD)
  apply(cases "pcW s", simp_all)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all)
  apply metis
  apply(case_tac "tW s = hW s \<and> Data s (numEnqs s) \<le> N", simp_all)
  apply metis
  apply(case_tac " hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s", simp_all, metis)
  apply(case_tac "tW s < hW s", simp_all, metis, metis, metis, metis)
  apply(case_tac " Data s (numEnqs s) \<le> N - hW s", simp_all, metis)
  apply(case_tac " Data s (numEnqs s) < tW s", simp_all, metis, metis, metis, metis, metis, metis)
  apply(case_tac "numEnqs s < n", simp_all, metis, metis)
  apply(cases "tW s \<noteq> T s", simp_all, metis, metis, metis, metis, metis)
  apply(case_tac "pcW s", simp_all add:cW_step_def)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)  
  apply(cases "pcW s", simp_all) 
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply metis
  apply(case_tac " tW s = hW s \<and> Data s (numEnqs s) \<le> N", simp_all) 
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply metis
  apply(case_tac "hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s", simp_all)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply metis
  apply(case_tac "tW s < hW s", simp_all)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply metis
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply metis
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply(intro conjI impI)
  apply metis
  apply (metis (no_types, lifting))
  apply(simp add:pre_W_def pre_A3_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply(intro conjI impI)
  apply metis
  apply (metis (no_types, lifting))
  apply(simp add:pre_W_def pre_A4_inv_def)
  apply (metis (no_types, lifting) F.distinct(13) Suc_lessD add.commute less_diff_conv less_trans_Suc)
  apply(case_tac " Data s (numEnqs s) \<le> N - hW s", simp_all)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply(simp add:pre_W_def pre_A5_inv_def)
  apply metis
  apply(case_tac "Data s (numEnqs s) < tW s", simp_all)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply(simp add:pre_W_def pre_A5_inv_def)
  apply metis
  apply(simp add:pre_W_def pre_A5_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply metis
  apply(simp add:pre_W_def pre_A6_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply(intro conjI impI)
  apply metis
  apply (metis (no_types, lifting))
  apply (metis (mono_tags, hide_lams) F.distinct(13) le_trans less_or_eq_imp_le nat_neq_iff)
  apply(simp add:pre_W_def pre_A7_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply(intro conjI impI)
  apply metis
  apply (metis (no_types, lifting))
  apply(clarify)
  apply(intro conjI impI)
  apply (metis F.distinct(13) Suc_lessD less_trans_Suc)
  apply (metis (mono_tags, hide_lams) F.distinct(13) le_trans less_or_eq_imp_le linorder_neqE_nat)
  apply(case_tac "N < Data s (numEnqs s)", simp_all)
  apply(simp add:pre_W_def pre_A8_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply metis
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply metis
  apply(simp add:pre_W_def pre_A8_inv_def)  defer
  apply(cases "numEnqs s < n", simp_all)
  apply(simp add:pre_W_def pre_acquire_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply metis
  apply(simp add:pre_W_def pre_acquire_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply metis
  apply(simp add:pre_W_def pre_OOM_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply metis
  apply metis
  apply(simp add:pre_W_def pre_write_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply (metis (no_types, lifting) F.distinct(1) Nat.add_0_right eq_imp_le fst_eqD nat_add_left_cancel_less snd_eqD)
  defer
  defer
  defer 
  apply(simp add:pre_W_def pre_enqueue_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply(intro conjI impI)
  apply(simp add: tempW_def)
  apply(case_tac "q s\<noteq>[]") 
  apply (metis (no_types, hide_lams) hd_append2)
  apply(subgoal_tac "q s=[]") prefer 2 
  apply force
  apply(subgoal_tac "tempR s \<noteq>(0,0)") prefer 2 
  apply blast
  apply(case_tac "offset s = 0")
  apply (metis append_Nil fst_conv list.sel(1))
  apply(simp add:inv_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply clarify 
  apply(subgoal_tac "c=b") prefer 2 
  apply (metis le_neq_implies_less)
  apply(subgoal_tac "end(tempR s) = b") prefer 2 
  apply (metis end_simp le_add_diff_inverse)
  apply(subgoal_tac "offset s = hW s") prefer 2
  apply meson 
  apply(subgoal_tac "i\<ge>c \<and> i<H s \<longrightarrow>ownB s i = W") prefer 2
  apply metis
  apply(subgoal_tac "H s\<le>N") prefer 2 
  apply metis
  apply(subgoal_tac "(i<c \<or> i\<ge>H s \<and> i\<le>N) \<longrightarrow>ownB s i\<noteq>W") prefer 2 
  apply (metis F.distinct(1) F.distinct(5) bot_nat_0.not_eq_extremum diff_is_0_eq zero_less_diff)
  apply (metis F.distinct(1) add_leD1 end_simp le_eq_less_or_eq linorder_neqE_nat nat_less_le)  
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s") 
  apply clarify 
  apply (metis eq_imp_le le_add1 le_neq_implies_less plus_nat.add_0)
  apply(simp add: tempW_def)
  apply(case_tac "q s=[]")
  apply (metis (no_types, lifting) F.distinct(1) Nat.add_0_right Suc_le_lessD Suc_lessD Suc_pred add_lessD1 fst_eqD le_add_diff_inverse less_Suc0 less_Suc_eq_le less_add_same_cancel1 list.size(3) nat_add_left_cancel_le nth_Cons_0 self_append_conv2)
  apply(subgoal_tac "q s\<noteq>[]") prefer 2 
  apply blast
  apply(subgoal_tac "\<forall>i<length (q s). fst ((q s) ! i) \<noteq> fst (tempR s)") prefer 2
  apply presburger
  apply(subgoal_tac "fst((offset s, Data s (numEnqs s))) \<noteq> fst(tempR s)") 
  apply (metis less_SucE nth_append nth_append_length)
  apply(subgoal_tac "offset s \<noteq> fst(tempR s)") prefer 2 
  apply (metis (no_types, lifting) F.distinct(1) Suc_le_lessD Suc_lessD Suc_pred add_lessD1 le_add_diff_inverse le_refl less_add_same_cancel1)
  apply(case_tac "case_1 s", simp_all) 
  apply(subgoal_tac "Data s (numReads s) = snd(tempR s)") prefer 2 
  apply presburger
  apply(subgoal_tac "Data s (numDeqs s - Suc 0) = snd(tempR s)") prefer 2
  apply presburger 
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "\<forall>i<length (q s).
       (fst (tempR s) < fst ((q s ) ! i) \<longrightarrow>
        fst (tempR s) + Data s (numDeqs s - Suc 0) \<le> fst ((q s ) ! i)) \<and>
       (fst ((q s) ! i) < fst (tempR s) \<longrightarrow>
        fst ((q s) ! i) + snd ((q s ) ! i)
        \<le> fst (tempR s))")
       prefer 2 
  apply (metis (no_types, lifting) gr_implies_not0 length_0_conv)
  apply(subgoal_tac "(fst (tempR s) < fst(offset s, Data s (numEnqs s)) \<longrightarrow>
        fst (tempR s) + Data s (numDeqs s - Suc 0) \<le> fst(offset s, Data s (numEnqs s))) \<and>
       (fst(offset s, Data s (numEnqs s)) < fst (tempR s) \<longrightarrow>
        fst(offset s, Data s (numEnqs s)) +
        snd(offset s, Data s (numEnqs s))
        \<le> fst (tempR s))") 
  apply(subgoal_tac "((q s @ [(offset s, Data s (numEnqs s))]) ! length (q s)) = (offset s, Data s (numEnqs s))") prefer 2 
  apply (metis nth_append_length)
  apply(subgoal_tac "\<forall>i<(length (q s)).
       (fst (tempR s) < fst ((q s @ [(offset s, Data s (numEnqs s))]) ! i) \<longrightarrow>
        fst (tempR s) + snd (tempR s) \<le> fst ((q s @ [(offset s, Data s (numEnqs s))]) ! i)) \<and>
       (fst ((q s @ [(offset s, Data s (numEnqs s))]) ! i) < fst (tempR s) \<longrightarrow>
        fst ((q s @ [(offset s, Data s (numEnqs s))]) ! i) +
        snd ((q s @ [(offset s, Data s (numEnqs s))]) ! i)
        \<le> fst (tempR s))") prefer 2 
  apply (metis (no_types, hide_lams) nth_append)
  using supporting_strange [where s=s] 
  apply presburger
  apply(intro conjI impI)
  apply (metis (no_types, lifting) Nat.add_0_right fst_eqD le_eq_less_or_eq less_add_same_cancel1 less_nat_zero_code nat_neq_iff snd_eqD tempW_def)
  apply(simp add:inv_def)
  apply(case_tac "case_1 s", simp_all) apply (simp add:case_1_def)
  apply(clarify)
  apply (metis (no_types, lifting) F.distinct(1) diff_is_0_eq le_refl less_imp_le_nat not_gr0 prod.collapse prod.inject tempW_def zero_less_diff)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s") 
  apply clarify
  apply (metis less_or_eq_imp_le zero_less_iff_neq_zero)
  apply(simp add: tempW_def)
  apply(subgoal_tac "fst((offset s, Data s (numEnqs s))) + snd((offset s, Data s (numEnqs s)))  \<noteq> fst(tempR s)")
  apply (metis fst_eqD snd_eqD)
  apply(subgoal_tac "offset s \<noteq> fst(tempR s)") prefer 2 
  apply (metis (no_types, lifting) F.distinct(1) Suc_le_lessD Suc_lessD Suc_pred add_lessD1 le_add_diff_inverse le_refl less_add_same_cancel1)
  apply(simp add:inv_def)
  apply(case_tac "case_1 s", simp_all)
  apply(simp add:case_1_def)
  apply(clarify)
  apply linarith
  apply(simp add:case_2_def) apply (thin_tac "\<not>case_1 s") 
  apply(clarify)
  apply (metis add_gr_0 nat_neq_iff)
  apply(case_tac "pcW s", simp_all add:inv_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply(simp add:pre_W_def pre_A3_inv_def)
  apply(simp add:case_2_def)
  apply(simp add:pre_W_def pre_A3_inv_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply(simp add:pre_W_def pre_A4_inv_def)
  apply (metis (no_types, lifting) le_add_diff_inverse le_eq_less_or_eq less_trans_Suc not_less_eq_eq)
  apply(simp add:case_2_def) apply(thin_tac "\<not> case_1 s")
  apply(simp add:pre_W_def pre_A4_inv_def) 
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply(clarify)
  apply(subgoal_tac "fst(tempR s) = 0 \<or> fst(tempR s) = T s") prefer 2
  apply meson
  apply(case_tac "fst(tempR s) = T s")
  apply(subgoal_tac "hW s = b") prefer 2 
  apply (metis le_imp_less_Suc le_refl le_trans not_less_less_Suc_eq)
  apply(subgoal_tac "T s > hW s + Data s (numEnqs s)") prefer 2 
  apply(subgoal_tac "ownB s (T s) = R") prefer 2
  apply (metis gr_implies_not0 le_refl)
  apply(subgoal_tac "tW s = T s") prefer 2
  apply (metis (no_types, lifting) add.commute le_trans less_diff_conv nat_less_le)
  apply(subgoal_tac "Data s (numEnqs s) < (tW s - hW s)") prefer 2 
  apply fastforce
  apply (metis add.commute less_diff_conv)
  apply (metis Suc_leI le_trans less_or_eq_imp_le not_less_eq_eq)
  apply(subgoal_tac "fst(tempR s) = 0") prefer 2
  apply fastforce
  apply(subgoal_tac "end(tempR s) = a") prefer 2 
  apply (metis add_cancel_left_left end_simp)
  apply(subgoal_tac "hW s\<ge>a") prefer 2 
  apply (metis le_trans)
  apply (metis Suc_leI end_simp le_trans not_less_eq_eq)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply(simp add:pre_W_def pre_A6_inv_def) 
  apply (metis le_add_diff_inverse le_trans less_or_eq_imp_le)
  apply(simp add:case_2_def)
  apply(simp add:pre_W_def pre_A6_inv_def)
  apply (metis Suc_leI not_less_eq_eq)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply(simp add:pre_W_def pre_A7_inv_def) 
  apply clarify
  apply(intro conjI impI)
  apply linarith
  apply (metis le_add_diff_inverse le_trans less_or_eq_imp_le)
  apply(simp add:case_2_def)
  apply(simp add:pre_W_def pre_A7_inv_def)
  apply clarify
  apply(intro conjI impI)
  apply linarith
  apply (metis Suc_leI not_less_eq_eq)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  prefer 2
  apply(case_tac "pcW s", simp_all)
  apply(simp add:pre_W_def pre_A3_inv_def)
  apply(simp add:pre_W_def pre_A4_inv_def)
  apply(simp add:pre_W_def pre_A6_inv_def)
  apply(simp add:pre_W_def pre_A7_inv_def)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "pcW s ", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  by(case_tac "tW s \<noteq> T s", simp_all)
  



lemma preIdleR_doesnt_change_with_W:
  assumes "inv s"
  and "con_assms s"
  and "pre_dequeue_inv s"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_dequeue_inv s'"
  using assms apply simp
  apply(simp add:pre_dequeue_inv_def) 
  apply(intro conjI impI)
  apply(simp add:pre_W_def)
  apply(cases "pcW s", simp_all add:cW_step_def  B_acquire_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:cW_step_def  B_acquire_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:cW_step_def  B_acquire_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:cW_step_def  B_acquire_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:cW_step_def  B_acquire_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:cW_step_def  B_acquire_def pre_W_def)
  apply(cases "tW s = hW s \<and> Data s (numEnqs s) \<le> N", simp_all)
  apply(cases "ownT s = Q", simp_all)
  apply(simp add:pre_A2_inv_def)
  apply(cases "hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s", simp_all)
  apply(cases "tW s < hW s", simp_all)
  apply(cases "Data s (numEnqs s) \<le> N - hW s", simp_all)
  apply(cases "Data s (numEnqs s) < tW s", simp_all)
  apply(cases "N < Data s (numEnqs s)", simp_all)
  apply(cases "ownT s = W", simp_all add:pre_enqueue_inv_def inv_def)
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_def)
  apply (metis nat_less_le)
  apply simp apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis nat_less_le)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:cW_step_def  B_acquire_def)
  apply(cases "tW s = hW s \<and> Data s (numEnqs s) \<le> N", simp_all)
  apply(cases "ownT s = W", simp_all add:pre_enqueue_inv_def inv_def)
  apply(cases "ownT s = W", simp_all add:pre_A2_inv_def inv_def)
  apply(cases "hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s", simp_all)
  apply(cases "tW s < hW s", simp_all)
  apply(simp add:pre_A3_inv_def)
  apply(simp add:pre_A4_inv_def)
  apply(simp add:pre_A5_inv_def)
  apply(simp add:pre_A6_inv_def)
  apply(simp add:pre_A7_inv_def)
  apply(simp add:pre_A8_inv_def)
  apply(cases "N < Data s (numEnqs s)", simp_all)
  apply(simp add:pre_acquire_inv_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all) defer
  apply(cases "pcW s", simp_all add:cW_step_def  B_acquire_def)
  apply(cases "tW s = hW s \<and> Data s (numEnqs s) \<le> N", simp_all add:pre_enqueue_inv_def inv_def)
  apply(cases "ownT s = W", simp_all add:pre_A2_inv_def inv_def)
  apply(cases "hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s", simp_all)
  apply(cases "tW s < hW s", simp_all)
  apply(simp add:pre_A3_inv_def)
  apply(simp add:pre_A4_inv_def)
  apply (metis (no_types, lifting) F.distinct(19) add.commute add_lessD1 less_diff_conv less_imp_add_positive)
  apply(simp add:pre_A5_inv_def)
  apply(cases "Data s (numEnqs s) \<le> N - hW s", simp_all)
  apply(cases "Data s (numEnqs s) < tW s", simp_all)
  apply(simp add:pre_A6_inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply clarify
  apply(subgoal_tac "offset s = hW s") prefer 2
  apply (metis (no_types, lifting) F.distinct(19) F.distinct(23) add_lessD1 diff_is_0_eq' le_0_eq le_eq_less_or_eq length_0_conv nat_le_iff_add)
  apply (metis (no_types, lifting) F.distinct(19) add_lessD1 diff_self_eq_0 le_0_eq le_add_diff_inverse le_neq_implies_less length_0_conv)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s") 
  apply (metis Suc_leI not_less_eq_eq)
  apply(simp add:pre_A7_inv_def) 
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply clarify
  apply (metis (no_types, lifting) F.distinct(19) F.distinct(23) add_lessD1 diff_is_0_eq' le_0_eq le_eq_less_or_eq length_0_conv nat_le_iff_add)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s") 
  apply (metis Suc_leI not_less_eq_eq)
  apply(simp add:pre_A8_inv_def)
  apply(cases "N < Data s (numEnqs s)", simp_all)
  apply(cases "ownT s = W", simp_all)
  apply (metis fst_conv le_trans nat_less_le snd_conv tempW_def)
  apply(simp add:Q_lemmas Q_basic_lemmas Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply(case_tac "case_1 s", simp_all)
  apply(simp add:case_1_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(case_tac "q s=[]")
  apply(subgoal_tac "fst(hd (q s @ [(offset s, Data s (numEnqs s))])) = offset s") prefer 2
  apply (metis append_self_conv2 list.sel(1) old.prod.inject prod.collapse)
  apply(subgoal_tac "snd(hd (q s @ [(offset s, Data s (numEnqs s))])) = Data s (numEnqs s)") prefer 2
  apply (metis append_self_conv2 list.sel(1) old.prod.inject prod.collapse)
  apply (metis le_trans less_imp_le_nat)
  apply(subgoal_tac "fst(hd (q s @ [(offset s, Data s (numEnqs s))])) = fst(hd(q s))") prefer 2
  apply (metis (no_types, lifting) hd_append2)
  apply(subgoal_tac "snd(hd (q s @ [(offset s, Data s (numEnqs s))])) = snd(hd(q s))") prefer 2
  apply (metis (no_types, lifting) hd_append2)
  apply presburger
  apply(simp add:case_2_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(case_tac "q s=[]")
  apply(subgoal_tac "fst(hd (q s @ [(offset s, Data s (numEnqs s))])) = offset s") prefer 2
  apply (metis append_self_conv2 list.sel(1) old.prod.inject prod.collapse)
  apply(subgoal_tac "snd(hd (q s @ [(offset s, Data s (numEnqs s))])) = Data s (numEnqs s)") prefer 2
  apply (metis append_self_conv2 list.sel(1) old.prod.inject prod.collapse)
  apply (metis le_trans less_imp_le_nat)
  apply(subgoal_tac "fst(hd (q s @ [(offset s, Data s (numEnqs s))])) = fst(hd(q s))") prefer 2
  apply (metis (no_types, lifting) hd_append2)
  apply(subgoal_tac "snd(hd (q s @ [(offset s, Data s (numEnqs s))])) = snd(hd(q s))") prefer 2
  apply (metis (no_types, lifting) hd_append2)
  apply presburger
  apply(case_tac "numEnqs s< n", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "pcW s", simp_all)
  apply(case_tac "numEnqs s< n", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "pcW s", simp_all)
  apply(case_tac "tW s = hW s \<and> Data s (numEnqs s) \<le> N", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(case_tac " hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s ", simp_all)
  apply(case_tac "tW s < hW s", simp_all)
  apply(simp add:Q_lemmas Q_basic_lemmas Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply (simp add: pre_A3_inv_def)
  apply(case_tac " Data s (numEnqs s) \<le> N - hW s", simp_all)
  apply(case_tac "Data s (numEnqs s) < tW s", simp_all)
  apply(case_tac "N < Data s (numEnqs s)", simp_all)
  apply(case_tac "ownT s = W", simp_all)
  apply(simp add:Q_lemmas Q_basic_lemmas Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply(simp add:pre_enqueue_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply clarify
  apply (metis (no_types, hide_lams) Nat.add_0_right diff_is_0_eq le_refl nat_add_left_cancel_less nat_neq_iff zero_less_diff)
  apply(simp add:case_2_def) 
  apply(simp add:Q_lemmas Q_basic_lemmas Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply(simp add:pre_enqueue_inv_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply clarify
  apply (metis (no_types, hide_lams) diff_self_eq_0 fst_eqD hd_append le_zero_eq length_0_conv less_add_same_cancel1 less_or_eq_imp_le list.sel(1) nat_less_le snd_eqD tempW_def)
  apply(simp add:case_2_def) 
  apply(subgoal_tac "\<forall>a b j.
       ((a, b) \<in> set (q s)) \<and> j < N \<and> T s \<le> j \<longrightarrow>
       a + b < j") prefer 2
  apply (metis (no_types, lifting) hd_append length_greater_0_conv length_pos_if_in_set)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(subgoal_tac "offset s + Data s (numEnqs s)<T s") prefer 2 
  apply force
  apply(subgoal_tac "\<forall> j. T s \<le> j \<longrightarrow>
       offset s + Data s (numEnqs s) < j") prefer 2 
  apply (metis (mono_tags, hide_lams) diff_is_0_eq le_trans nat_less_le zero_less_diff)
  apply (metis (no_types, lifting))
  apply(case_tac "numEnqs s < n", simp_all)
  by(case_tac "tW s \<noteq> T s", simp_all)
  







lemma preRelease_doesnt_change_with_W:
  assumes "inv s"
  and "con_assms s"
  and "pre_Release_inv s"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_Release_inv s'"
  using assms apply simp
  apply(simp add:pre_Release_inv_def) 
  apply(intro conjI impI)
  apply(simp add:cW_step_def)
  apply(cases "pcW s", simp_all) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(simp_all add:cW_step_def)
  apply(cases "pcW s", simp_all) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(simp add:pre_W_def pre_write_inv_def)
  apply (metis F.distinct(1) fst_eqD less_add_same_cancel1 nat_le_linear snd_eqD)
  apply(cases "pcW s", simp_all) 
  apply(cases "tW s = hW s \<and> Data s (numEnqs s) \<le> N", simp_all)
  apply(cases "hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s", simp_all)
  apply(cases "tW s < hW s", simp_all)
  apply(case_tac "Data s (numEnqs s) \<le> N - hW s", simp_all)
  apply(case_tac "Data s (numEnqs s) < tW s", simp_all)
  apply(case_tac "N < Data s (numEnqs s)", simp_all)
  apply(simp add:pre_W_def pre_enqueue_inv_def)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply (metis Nat.le_imp_diff_is_add hd_append length_0_conv list.sel(1) plus_nat.add_0 tempW_reflects_writes_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(simp add:pre_W_def pre_write_inv_def)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis fst_eqD head_q0 length_greater_0_conv)
  apply(cases "pcW s", simp_all) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(simp add:pre_W_def pre_write_inv_def)
  apply (metis F.distinct(1))
  apply(cases "pcW s", simp_all) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all) 
  apply(simp add:pre_W_def pre_A3_inv_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all) defer
  apply(cases "pcW s", simp_all) 
  apply(simp add:pre_W_def pre_A3_inv_def)
  apply(simp add:pre_W_def pre_A4_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply (metis (no_types, lifting) F.distinct(13) Suc_lessD add.commute less_diff_conv less_trans_Suc) 
  apply(simp add:pre_W_def pre_A6_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply (metis (mono_tags, hide_lams) F.distinct(13) le_antisym le_trans less_or_eq_imp_le nat_neq_iff)
  apply(simp add:pre_W_def pre_A7_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply (metis (no_types, hide_lams) F.distinct(13) Suc_lessD less_trans_Suc)  
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all) 
  apply(simp add:pre_W_def pre_A3_inv_def)
  apply(simp add:pre_W_def pre_A4_inv_def)
  apply(simp add:pre_W_def pre_A6_inv_def)
  apply(simp add:pre_W_def pre_A7_inv_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)     (*tempR doesnt change:*)
  apply(cases "pcW s", simp_all) 
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply metis
  apply(case_tac " tW s = hW s \<and> Data s (numEnqs s) \<le> N", simp_all) 
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply metis
  apply(case_tac "hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s", simp_all)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply metis
  apply(case_tac "tW s < hW s", simp_all)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply metis
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply metis
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply(intro conjI impI)
  apply metis
  apply (metis (no_types, lifting))
  apply(simp add:pre_W_def pre_A3_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply(intro conjI impI)
  apply metis
  apply (metis (no_types, lifting))
  apply(simp add:pre_W_def pre_A4_inv_def)
  apply (metis (no_types, lifting) F.distinct(13) Suc_lessD add.commute less_diff_conv less_trans_Suc)
  apply(case_tac " Data s (numEnqs s) \<le> N - hW s", simp_all)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply(simp add:pre_W_def pre_A5_inv_def)
  apply metis
  apply(case_tac "Data s (numEnqs s) < tW s", simp_all)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply(simp add:pre_W_def pre_A5_inv_def)
  apply metis
  apply(simp add:pre_W_def pre_A5_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply metis
  apply(simp add:pre_W_def pre_A6_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply(intro conjI impI)
  apply metis
  apply (metis (no_types, lifting))
  apply (metis (mono_tags, hide_lams) F.distinct(13) le_trans less_or_eq_imp_le nat_neq_iff)
  apply(simp add:pre_W_def pre_A7_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas) 
  apply(intro conjI impI)
  apply metis
  apply (metis (no_types, lifting))
  apply(clarify)
  apply(intro conjI impI)
  apply (metis F.distinct(13) Suc_lessD less_trans_Suc)
  apply (metis (mono_tags, hide_lams) F.distinct(13) le_trans less_or_eq_imp_le linorder_neqE_nat)
  apply(case_tac "N < Data s (numEnqs s)", simp_all)
  apply(simp add:pre_W_def pre_A8_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply metis
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply metis
  apply(simp add:pre_W_def pre_A8_inv_def)  defer
  apply(cases "numEnqs s < n", simp_all)
  apply(simp add:pre_W_def pre_acquire_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply metis
  apply(simp add:pre_W_def pre_acquire_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply metis
  apply(simp add:pre_W_def pre_OOM_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply metis
  apply metis
  apply(simp add:pre_W_def pre_write_inv_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply (metis (no_types, lifting) F.distinct(1) Nat.add_0_right eq_imp_le fst_eqD nat_add_left_cancel_less snd_eqD)
  apply(simp add:pre_W_def pre_enqueue_inv_def)   
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply(intro conjI impI)
  (*solved trivially by case ownership observation*)
  apply(simp add: tempW_def)
  apply(case_tac "q s\<noteq>[]") 
  apply (metis (no_types, hide_lams) hd_append2)
  apply(subgoal_tac "q s=[]") prefer 2 
  apply force
  apply(subgoal_tac "tempR s \<noteq>(0,0)") prefer 2 
  apply blast
  apply(case_tac "offset s = 0")
  apply (metis append_Nil fst_conv list.sel(1))
  apply(simp add:inv_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply clarify 
  apply(subgoal_tac "c=b") prefer 2 
  apply (metis le_neq_implies_less)
  apply(subgoal_tac "end(tempR s) = b") prefer 2 
  apply (metis end_simp le_add_diff_inverse)
  apply(subgoal_tac "offset s = hW s") prefer 2
  apply meson 
  apply(subgoal_tac "i\<ge>c \<and> i<H s \<longrightarrow>ownB s i = W") prefer 2
  apply metis
  apply(subgoal_tac "H s\<le>N") prefer 2 
  apply metis
  apply(subgoal_tac "(i<c \<or> i\<ge>H s \<and> i\<le>N) \<longrightarrow>ownB s i\<noteq>W") prefer 2 
  apply (metis F.distinct(1) F.distinct(5) bot_nat_0.not_eq_extremum diff_is_0_eq zero_less_diff)
  apply (metis F.distinct(1) add_leD1 end_simp le_eq_less_or_eq linorder_neqE_nat nat_less_le)  
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s") 
  apply clarify 
  apply (metis eq_imp_le le_add1 le_neq_implies_less plus_nat.add_0)
  apply(simp add: tempW_def)
  apply(case_tac "q s=[]")
  apply (metis (no_types, lifting) F.distinct(1) Nat.add_0_right Suc_le_lessD Suc_lessD Suc_pred add_lessD1 fst_eqD le_add_diff_inverse less_Suc0 less_Suc_eq_le less_add_same_cancel1 list.size(3) nat_add_left_cancel_le nth_Cons_0 self_append_conv2)
  apply(subgoal_tac "q s\<noteq>[]") prefer 2 
  apply blast
  apply(subgoal_tac "\<forall>i<length (q s). fst ((q s) ! i) \<noteq> fst (tempR s)") prefer 2
  apply presburger
  apply(subgoal_tac "fst((offset s, Data s (numEnqs s))) \<noteq> fst(tempR s)") 
  apply (metis less_SucE nth_append nth_append_length)
  apply(subgoal_tac "offset s \<noteq> fst(tempR s)") prefer 2 
  apply (metis (no_types, lifting) F.distinct(1) Suc_le_lessD Suc_lessD Suc_pred add_lessD1 le_add_diff_inverse le_refl less_add_same_cancel1)
  apply(case_tac "case_1 s", simp_all) 
  apply(subgoal_tac "\<forall>i<length (q s).
       (fst (tempR s) < fst ((q s ) ! i) \<longrightarrow>
        fst (tempR s) + Data s (numReads s - Suc 0) \<le> fst ((q s ) ! i)) \<and>
       (fst ((q s) ! i) < fst (tempR s) \<longrightarrow>
        fst ((q s) ! i) + snd ((q s ) ! i)
        \<le> fst (tempR s))")
  prefer 2 
  apply (metis (no_types, lifting) gr_implies_not0 length_0_conv)
  apply(subgoal_tac "(fst (tempR s) < fst(offset s, Data s (numEnqs s)) \<longrightarrow>
        fst (tempR s) + Data s (numReads s - Suc 0) \<le> fst(offset s, Data s (numEnqs s))) \<and>
       (fst(offset s, Data s (numEnqs s)) < fst (tempR s) \<longrightarrow>
        end(offset s, Data s (numEnqs s))
        \<le> fst (tempR s))")
  apply (smt (z3) end_simp less_SucE nth_append nth_append_length)
  apply(intro conjI impI)
  apply (metis (no_types, lifting) Nat.add_0_right fst_eqD le_eq_less_or_eq less_add_same_cancel1 less_nat_zero_code nat_neq_iff snd_eqD tempW_def)
  apply(simp add:inv_def)
  apply(case_tac "case_1 s", simp_all) apply (simp add:case_1_def)
  apply(clarify)
  apply (metis (no_types, lifting) F.distinct(1) diff_is_0_eq le_refl less_imp_le_nat not_gr0 prod.collapse prod.inject tempW_def zero_less_diff)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s") 
  apply clarify
  apply (metis less_or_eq_imp_le zero_less_iff_neq_zero)
  apply(simp add: tempW_def)
  apply(subgoal_tac "end((offset s, Data s (numEnqs s))) \<noteq> fst(tempR s)") 
  apply (metis end_simp fst_conv snd_conv)
  apply(subgoal_tac "offset s \<noteq> fst(tempR s)") prefer 2 
  apply (metis (no_types, lifting) F.distinct(1) Suc_le_lessD Suc_lessD Suc_pred add_lessD1 le_add_diff_inverse le_refl less_add_same_cancel1)
  apply(simp add:inv_def)
  apply(case_tac "case_1 s", simp_all)
  apply(simp add:case_1_def)
  apply(clarify)
  apply linarith
  apply(simp add:case_2_def) apply (thin_tac "\<not>case_1 s") 
  apply(clarify)
  by (metis add_gr_0 nat_neq_iff)




lemma GLOBAL_W_step_shows_preR:
  assumes "inv s"
  and "con_assms s"
  and "pre_R (pcR s) s"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_R (pcR s') s'"
  using assms apply simp
  apply(subgoal_tac "pcR s' = pcR s") prefer 2
  using pcR_doesnt_change_with_W [where s=s and s'=s']
  apply simp
  apply(simp add:pre_R_def) apply(case_tac "pcR s") apply simp_all
  using preRelease_doesnt_change_with_W [where s=s and s'=s'] apply simp    
  using preIdleR_doesnt_change_with_W [where s=s and s'=s'] apply simp     
  using preRead_doesnt_change_with_W [where s=s and s'=s'] 
  by simp




















(*******************************GLOBAL R_step shows preW*************************************)

lemma pcW_doesnt_change_with_R:
  assumes "inv s"
  and "con_assms s"
  and "pre_R (pcR s) s"
  and "pre_W (pcW s) s"
  and "cR_step (pcR s) s s'"
shows "pcW s'=pcW s"
 using assms apply simp
  apply(case_tac "pcR s ", simp_all add:cR_step_def)
  by(case_tac "q s=[]", simp_all)


lemma ownB_by_W_doesnt_change_after_release:
  "inv s \<Longrightarrow> con_assms s \<Longrightarrow> pre_Release_inv s \<Longrightarrow> cR_step Release s s'
  \<Longrightarrow>ownB s i = W \<and> i\<le>N \<Longrightarrow> ownB s' i = W \<and> i\<le>N"
  apply(simp add:inv_def)
  apply(simp add:cR_step_def)
  apply(simp add:pre_Release_inv_def)
  apply(case_tac "T s \<noteq> fst (tempR s)") 
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_def)
  apply metis
  apply simp apply(simp add:case_2_def)
  apply (metis F.distinct(7) nat_less_le) 
  apply(case_tac "case_1 s") apply simp by(simp add:case_1_def)
  
lemma ownB_not_by_W_doesnt_change_after_release:
  "inv s \<Longrightarrow> con_assms s \<Longrightarrow> pre_Release_inv s \<Longrightarrow> cR_step Release s s'
  \<Longrightarrow>ownB s i \<noteq> W \<and> i\<le>N \<Longrightarrow> ownB s' i \<noteq> W \<and> i\<le>N"
  apply(simp add:inv_def)
  by(simp add:cR_step_def)


lemma ownB_by_W_doesnt_change_after_read:
  "inv s \<Longrightarrow> con_assms s \<Longrightarrow> pre_Read_inv s \<Longrightarrow> cR_step Read s s'
  \<Longrightarrow>ownB s i = W \<and> i\<le>N \<Longrightarrow> ownB s' i = W \<and> i\<le>N"
  apply(simp add:inv_def)
  by(simp add:cR_step_def)


lemma ownB_not_by_W_doesnt_change_after_read:
  "inv s \<Longrightarrow> con_assms s \<Longrightarrow> pre_Read_inv s \<Longrightarrow> cR_step Read s s'
  \<Longrightarrow>ownB s i \<noteq> W \<and> i\<le>N \<Longrightarrow> ownB s' i \<noteq> W \<and> i\<le>N"
  apply(simp add:inv_def)
  by(simp add:cR_step_def)


lemma ownB_by_W_doesnt_change_after_dequeue:
  "inv s \<Longrightarrow> con_assms s \<Longrightarrow> pre_dequeue_inv s \<Longrightarrow> cR_step idleR s s'
  \<Longrightarrow>ownB s i = W \<and> i\<le>N \<Longrightarrow> ownB s' i = W \<and> i\<le>N"
  apply(simp add:inv_def)
  apply(simp add:cR_step_def)
  apply(simp add:pre_dequeue_inv_def)
  apply(case_tac "q s=[]")
  apply presburger
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_def) 
  apply (metis (no_types, hide_lams) F.distinct(3))
  apply simp apply(simp add:case_2_def)
  by (metis (no_types, hide_lams) F.distinct(3))


lemma ownB_not_by_W_doesnt_change_after_dequeue:
  "inv s \<Longrightarrow> con_assms s \<Longrightarrow> pre_dequeue_inv s \<Longrightarrow> cR_step idleR s s'
  \<Longrightarrow>ownB s i \<noteq> W \<and> i\<le>N \<Longrightarrow> ownB s' i \<noteq> W \<and> i\<le>N"
  apply(simp add:inv_def)
  apply(simp add:cR_step_def)
  apply(simp add:pre_dequeue_inv_def)
  apply(case_tac "q s=[]")
  apply presburger
  apply(case_tac "case_1 s") apply simp by(simp add:case_1_def) 

lemma ownB_by_W_doesnt_change_with_R:
  "inv s \<Longrightarrow> con_assms s  \<Longrightarrow> cR_step (pcR s) s s' \<Longrightarrow> pcR s = Release \<longrightarrow> pre_Release_inv s \<Longrightarrow>
     pcR s = Read \<longrightarrow> pre_Read_inv s \<Longrightarrow> pcR s = idleR \<longrightarrow> pre_dequeue_inv s
  \<Longrightarrow>ownB s i = W \<and> i\<le>N \<Longrightarrow> ownB s' i = W \<and> i\<le>N"
  apply(case_tac "pcR s ") apply simp_all
  using ownB_by_W_doesnt_change_after_release [where s=s and s'=s' and i=i]
  apply auto[1] 
  using ownB_by_W_doesnt_change_after_dequeue [where s=s and s'=s' and i=i]
  apply auto[1]
  using ownB_by_W_doesnt_change_after_read [where s=s and s'=s' and i=i]
  by auto[1]

lemma ownB_not_by_W_doesnt_change_with_R:
  "inv s \<Longrightarrow> con_assms s  \<Longrightarrow> cR_step (pcR s) s s' \<Longrightarrow> pcR s = Release \<longrightarrow> pre_Release_inv s \<Longrightarrow>
     pcR s = Read \<longrightarrow> pre_Read_inv s \<Longrightarrow> pcR s = idleR \<longrightarrow> pre_dequeue_inv s
  \<Longrightarrow>ownB s i \<noteq> W \<and> i\<le>N \<Longrightarrow> ownB s' i \<noteq> W \<and> i\<le>N"
  apply(case_tac "pcR s ") apply simp_all
  using ownB_not_by_W_doesnt_change_after_release [where s=s and s'=s' and i=i]
  apply auto[1] 
  using ownB_not_by_W_doesnt_change_after_dequeue [where s=s and s'=s' and i=i]
  apply auto[1]
  using ownB_not_by_W_doesnt_change_after_read [where s=s and s'=s' and i=i]
  by auto[1]


lemma ownB_by_B_doesnt_change_after_release:
  "inv s \<Longrightarrow> con_assms s \<Longrightarrow> pre_Release_inv s \<Longrightarrow> cR_step Release s s'
  \<Longrightarrow>ownB s i = B \<and> i\<le>N \<Longrightarrow> ownB s' i = B \<and> i\<le>N"
  apply(simp add:inv_def)
  by(simp add:cR_step_def)


lemma ownB_by_B_doesnt_change_after_read:
  "inv s \<Longrightarrow> con_assms s \<Longrightarrow> pre_Read_inv s \<Longrightarrow> cR_step Read s s'
  \<Longrightarrow>ownB s i = B \<and> i\<le>N \<Longrightarrow> ownB s' i = B \<and> i\<le>N"
  apply(simp add:inv_def)
  by(simp add:cR_step_def)


lemma ownB_by_B_doesnt_change_after_dequeue:
  "inv s \<Longrightarrow> con_assms s \<Longrightarrow> pre_dequeue_inv s \<Longrightarrow> cR_step idleR s s'
  \<Longrightarrow>ownB s i = B \<and> i\<le>N \<Longrightarrow> ownB s' i = B \<and> i\<le>N"
  apply(simp add:inv_def)
  apply(simp add:cR_step_def)
  apply(simp add:pre_dequeue_inv_def)
  apply(case_tac "q s=[]")
  apply presburger
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_def)
  apply (metis (no_types, hide_lams) F.distinct(19))
  apply(case_tac "q s=[]", simp_all)
  by force

lemma ownB_by_B_doesnt_change_with_R:
  "inv s \<Longrightarrow> con_assms s  \<Longrightarrow> cR_step (pcR s) s s' \<Longrightarrow> pcR s = Release \<longrightarrow> pre_Release_inv s \<Longrightarrow>
     pcR s = Read \<longrightarrow> pre_Read_inv s \<Longrightarrow> pcR s = idleR \<longrightarrow> pre_dequeue_inv s
  \<Longrightarrow>ownB s i = B \<and> i\<le>N \<Longrightarrow> ownB s' i = B \<and> i\<le>N"
  apply(case_tac "pcR s ") apply simp_all
  using ownB_by_B_doesnt_change_after_release [where s=s and s'=s' and i=i]
  apply auto[1] 
  using ownB_by_B_doesnt_change_after_dequeue [where s=s and s'=s' and i=i]
  apply auto[1]
  using ownB_by_B_doesnt_change_after_read [where s=s and s'=s' and i=i]
  by auto[1]



lemma ownB_by_D_doesnt_change_after_release:
  "inv s \<Longrightarrow> con_assms s \<Longrightarrow> pre_Release_inv s \<Longrightarrow> cR_step Release s s' \<Longrightarrow>tR s = fst(tempR s)
  \<Longrightarrow>ownB s i = D \<and> i\<le>N \<Longrightarrow> ownB s' i = D \<and> i\<le>N"
  apply(simp add:inv_def)
  by(simp add:cR_step_def)
  

lemma ownB_by_D_doesnt_change_after_read:
  "inv s \<Longrightarrow> con_assms s \<Longrightarrow> pre_Read_inv s \<Longrightarrow> cR_step Read s s'
  \<Longrightarrow>ownB s i = D \<and> i\<le>N \<Longrightarrow> ownB s' i = D \<and> i\<le>N"
  apply(simp add:inv_def)
  by(simp add:cR_step_def)



lemma ownB_by_D_doesnt_change_after_dequeue:
  "inv s \<Longrightarrow> con_assms s \<Longrightarrow> pre_dequeue_inv s \<Longrightarrow> cR_step idleR s s'
  \<Longrightarrow>ownB s i = D \<and> i\<le>N \<Longrightarrow> ownB s' i = D \<and> i\<le>N"
  apply(simp add:inv_def)
  apply(simp add:cR_step_def)
  apply(simp add:pre_dequeue_inv_def)
  apply(case_tac "q s=[]", simp_all) 
  by force


lemma W_items_dont_change_with_R:
  "cR_step (pcR s) s s' 
  \<Longrightarrow>offset s = offset s' \<and> Data s (numEnqs s) = Data s' (numEnqs s') \<and> numEnqs s = numEnqs s' "
  apply(case_tac "pcR s ") apply simp_all apply(simp_all add:cR_step_def)
  by(cases "q s=[]", simp_all) 

lemma W_items_dont_change_with_R_2:
  "cR_step (pcR s) s s' 
  \<Longrightarrow>tempW s = tempW s' \<and> tW s = tW s' \<and> hW s = hW s' \<and> data_index s = data_index s'"
  apply(case_tac "pcR s ") apply simp_all apply(simp_all add:cR_step_def tempW_def)
  by(cases "q s=[]", simp_all) 

lemma W_items_dont_change_with_R_3:
  "cR_step (pcR s) s s' 
  \<Longrightarrow>numWrites s=numWrites s' \<and> H s= H s'"
  apply(case_tac "pcR s ") apply simp_all apply(simp_all add:cR_step_def tempW_def)
  by(cases "q s=[]", simp_all) 

lemma ownB_by_D_relation_with_R:
  "inv s \<Longrightarrow>con_assms s  \<Longrightarrow> pre_Read_inv s \<Longrightarrow> pre_enqueue_inv s \<Longrightarrow>  
offset s \<noteq> fst(tempR s)"
  apply (simp add:inv_def pre_Read_inv_def pre_enqueue_inv_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply(clarify)
  apply(case_tac "q s=[]")
  apply(subgoal_tac "b=c") prefer 2
  apply (metis nat_less_le) apply(unfold tempW_lemmas tempW_basic_lemmas)
  apply(subgoal_tac "offset s = c") prefer 2
  apply (metis F.distinct(1) F.distinct(5) fst_conv le_iff_add less_or_eq_imp_le nat_less_le snd_conv)
  apply(subgoal_tac "offset s = b") prefer 2 
  apply force
  apply(subgoal_tac "fst(tempR s )\<ge>T s") prefer 2 
  apply linarith apply(unfold tempR_lemmas tempR_basic_lemmas)
  apply(subgoal_tac "snd( tempR s )>0")
  apply metis
  apply metis
  apply(subgoal_tac "b<c") prefer 2 
  apply (metis diff_self_eq_0 le_zero_eq length_0_conv nat_less_le)
  apply(subgoal_tac "offset s = c") prefer 2
  apply (metis F.distinct(1) F.distinct(5) fst_conv le_iff_add less_or_eq_imp_le nat_less_le snd_conv)
  apply(subgoal_tac "snd(tempR s)>0") 
  apply (metis end_simp)
  apply (metis end_simp)
  apply simp
  apply(simp add:case_2_def)
  apply clarify
  apply(case_tac "q s=[]")
  apply(subgoal_tac "d = fst(tempR s)") prefer 2 
  apply (metis F.distinct(1) Nat.add_0_right le0 less_nat_zero_code nat_add_left_cancel_less)
  apply(subgoal_tac "fst(tempW s) = b") prefer 2 
  apply (metis F.distinct(1) diff_is_0_eq le0 nat_neq_iff zero_less_diff)
  apply(subgoal_tac "snd(tempW s) > 0") prefer 2
  apply (metis snd_eqD tempW_def)
  apply (metis fst_eqD le_neq_implies_less tempW_def)
  by (metis F.distinct(1) add_gr_0 le0)


lemma R_doesnt_change_q_read_release:
  "inv s \<Longrightarrow> cR_step (pcR s) s s' \<Longrightarrow> pcR s\<noteq>idleR \<Longrightarrow> q s=q s'"
  apply(simp add:inv_def cR_step_def)
  by(case_tac "pcR s", simp_all)

lemma R_changes_q_dequeue:
  "inv s \<Longrightarrow> cR_step (pcR s) s s' \<Longrightarrow> pcR s=idleR \<Longrightarrow>q s\<noteq>[] \<Longrightarrow> tl(q s)=q s'"
  by(simp add:inv_def cR_step_def)

lemma strange_but_Q_1:
  "q s\<noteq>[] \<Longrightarrow> hd(q s) = q s!0"
  by (simp add: hd_conv_nth)

lemma strange_but_Q_2:
  "length(q s)>1 \<Longrightarrow>hd(tl(q s)) = tl(q s)!0"
  by (metis One_nat_def hd_conv_nth length_tl less_nat_zero_code list.size(3) zero_less_diff)

lemma strange_but_Q_3:
  "length(q s)>1 \<Longrightarrow>tl(q s)\<noteq>[]"
  by (metis Nitpick.size_list_simp(2) One_nat_def less_numeral_extra(4) not_one_less_zero)

lemma strange_but_Q_4:
  "length(q s)>1 \<Longrightarrow>hd(tl(q s)) = q s!1"
  by (simp add: nth_tl strange_but_Q_2)

lemma R_doesnt_change_ownD_release_dequeue:
  "cR_step (pcR s) s s'\<Longrightarrow> pcR s\<noteq>Read \<Longrightarrow>
  ownD s= ownD s'"
  apply(simp add: cR_step_def) 
  apply(case_tac "pcR s", simp_all)
  by(case_tac "q s=[]", simp_all)

lemma R_doesnt_change_ownD_read_except:
  "cR_step (pcR s) s s'\<Longrightarrow> pcR s=Read \<Longrightarrow> 
  i\<ge>0 \<and> i\<noteq> data_index s (tempR s) \<longrightarrow> ownD s i= ownD s' i"
  by(simp add: cR_step_def) 

lemma Q_empty_R_step_result:
  "cR_step (pcR s) s s' \<Longrightarrow> q s=[] \<Longrightarrow> pcR s=idleR \<Longrightarrow>
q s'=[]"
  by (simp add:cR_step_def)

lemma Q_W_relation_through_R_1:
  "cR_step (pcR s) s s' \<Longrightarrow> q s'\<noteq>[] \<Longrightarrow> q s\<noteq>[] \<Longrightarrow> pcR s = idleR \<Longrightarrow>
\<forall>i<length (q s).
       (offset s < fst (q s ! i) \<longrightarrow> offset s + Data s (numEnqs s) < fst (q s ! i)) \<and>
       (fst (q s ! i) < offset s \<longrightarrow> fst (q s ! i) + snd (q s ! i) \<le> offset s)
\<Longrightarrow>
\<forall>i<length (q s').
       (offset s' < fst (q s' ! i) \<longrightarrow> offset s' + Data s' (numEnqs s') < fst (q s' ! i)) \<and>
       (fst (q s' ! i) < offset s' \<longrightarrow> fst (q s' ! i) + snd (q s' ! i) \<le> offset s')"
  apply(simp add:cR_step_def)
  by (simp add: length_greater_0_conv nth_tl)

lemma Q_W_relation_through_R_2:
  "cR_step (pcR s) s s'  \<Longrightarrow> pcR s = Read \<Longrightarrow>
\<forall>i<length (q s).
       (offset s < fst (q s ! i) \<longrightarrow> offset s + Data s (numEnqs s) < fst (q s ! i)) \<and>
       (fst (q s ! i) < offset s \<longrightarrow> fst (q s ! i) + snd (q s ! i) \<le> offset s)
\<Longrightarrow>
\<forall>i<length (q s').
       (offset s' < fst (q s' ! i) \<longrightarrow> offset s' + Data s' (numEnqs s') < fst (q s' ! i)) \<and>
       (fst (q s' ! i) < offset s' \<longrightarrow> fst (q s' ! i) + snd (q s' ! i) \<le> offset s')"
  by(simp add:cR_step_def)


lemma Q_W_relation_through_R_3:
  "cR_step (pcR s) s s' \<Longrightarrow> pcR s = Release \<Longrightarrow>
\<forall>i<length (q s).
       (offset s < fst (q s ! i) \<longrightarrow> offset s + Data s (numEnqs s) < fst (q s ! i)) \<and>
       (fst (q s ! i) < offset s \<longrightarrow> fst (q s ! i) + snd (q s ! i) \<le> offset s)
\<Longrightarrow>
\<forall>i<length (q s').
       (offset s' < fst (q s' ! i) \<longrightarrow> offset s' + Data s' (numEnqs s') < fst (q s' ! i)) \<and>
       (fst (q s' ! i) < offset s' \<longrightarrow> fst (q s' ! i) + snd (q s' ! i) \<le> offset s')"
  by(simp add:cR_step_def) 




lemma pre_write_doesnt_change_with_R:
  assumes "inv s"
  and "con_assms s"
  and "pre_write_inv s"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_write_inv s'"
  using assms apply simp
  apply(simp add:pre_write_inv_def)
  apply(subgoal_tac "end(tempW s )\<le>N") prefer 2 apply(simp_all add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:pre_R_def)
  apply(intro conjI impI)
  apply(case_tac[!] "pcR s")
  apply simp_all apply(subgoal_tac "\<forall>i. offset s \<le> i \<and> i < fst (tempW s) + snd (tempW s) \<longrightarrow> ownB s i = W") prefer 2 
  apply (metis fst_eqD snd_eqD tempW_def)
  apply(subgoal_tac "hW s = hW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(1) PCR.distinct(3) assms(2) apply presburger
  apply(subgoal_tac "tW s = tW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(1) PCR.distinct(3) assms(2) apply presburger
  using ownB_by_W_doesnt_change_after_release [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis W_items_dont_change_with_R assms(2) le_trans less_or_eq_imp_le)
  using ownB_by_W_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply (metis PCR.distinct(1) PCR.distinct(5) W_items_dont_change_with_R assms(2) le_trans less_or_eq_imp_le)
  using ownB_by_W_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis PCR.distinct(3) PCR.distinct(5) W_items_dont_change_with_R assms(2) le_trans less_or_eq_imp_le)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(1) PCR.distinct(3) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis RingBuffer_BD_latest_2.inv_def basic_pointer_movement_def inRange_def inRangeht_def)
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (smt (z3) PCR.distinct(1) PCR.distinct(3) W_items_dont_change_with_R assms(2) le_trans less_or_eq_imp_le)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(1) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis RingBuffer_BD_latest_2.inv_def basic_pointer_movement_def inRange_def inRangeht_def)
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (smt (z3) PCR.distinct(1) PCR.distinct(5) W_items_dont_change_with_R assms(2) le_trans less_or_eq_imp_le)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(3) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis RingBuffer_BD_latest_2.inv_def basic_pointer_movement_def inRange_def inRangeht_def)
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply (smt (z3) PCR.distinct(3) PCR.distinct(5) W_items_dont_change_with_R assms(2) le_trans less_or_eq_imp_le)
  apply clarify   
  apply(intro conjI impI)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(1) PCR.distinct(3) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:inv_def) 
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s']
  apply (metis PCR.distinct(1) PCR.distinct(3) W_items_dont_change_with_R assms(1) assms(2) less_or_eq_imp_le)
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (smt (z3) PCR.distinct(1) PCR.distinct(3) W_items_dont_change_with_R assms(2) le_add_same_cancel1 le_trans less_or_eq_imp_le not_gr_zero)
  apply clarify
  apply(intro conjI impI)        
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(1) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:inv_def) 
  apply (metis assms(1) assms(2) less_or_eq_imp_le ownB_by_B_doesnt_change_after_dequeue prod.inject tempW_def)
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply (metis PCR.distinct(1) PCR.distinct(5) add_leD1 assms(2) fst_conv less_le_not_le order_trans tempW_def)
  apply clarify
  apply(intro conjI impI)        
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(3) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:inv_def) 
  apply (metis assms(1) assms(2) less_or_eq_imp_le ownB_by_B_doesnt_change_after_read prod.inject tempW_def)
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis PCR.distinct(3) PCR.distinct(5) add_leD1 assms(2) fst_conv less_le_not_le order_trans tempW_def)
  apply clarify       
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(1) PCR.distinct(3) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:inv_def) 
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (smt (z3) PCR.distinct(1) PCR.distinct(3) W_items_dont_change_with_R assms(2) le_trans less_or_eq_imp_le)
  apply clarify       
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(1) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:inv_def) 
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply (smt (z3) PCR.distinct(1) PCR.distinct(5) W_items_dont_change_with_R assms(2) le_trans less_or_eq_imp_le)
  apply clarify
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(3) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:inv_def) 
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (smt (z3) PCR.distinct(3) PCR.distinct(5) W_items_dont_change_with_R assms(2) le_trans less_or_eq_imp_le)
  apply(case_tac "tR s = fst(tempR s)")
  using ownB_by_D_doesnt_change_after_release [where s=s and s'=s'] 
  apply (metis W_items_dont_change_with_R \<open>cR_step (pcR s) s s' \<Longrightarrow> tempW s = tempW s' \<and> tW s = tW s' \<and> hW s = hW s' \<and> data_index s = data_index s'\<close> assms(2) nat_less_le)
  apply (simp add:inv_def)
  apply(case_tac "case_1 s", simp_all)
  apply(simp add: case_1_def) 
  apply (metis (no_types, hide_lams) F.distinct(25) F.distinct(7) \<open>cR_step (pcR s) s s' \<Longrightarrow> tempW s = tempW s' \<and> tW s = tW s' \<and> hW s = hW s' \<and> data_index s = data_index s'\<close> le0 le_refl nat_less_le nat_neq_iff prod.inject tempW_def)
  apply(thin_tac "\<not>case_1 s")
  apply(simp add:pre_Release_inv_def)
  apply(subgoal_tac "T s\<noteq>fst(tempR s)") prefer 2 
  apply blast
  apply(simp add:case_2_def)
  apply clarify
  apply(subgoal_tac "fst(tempR s) = T s \<or> fst(tempR s) = 0") prefer 2 
  apply meson
  apply(subgoal_tac "fst(tempR s) = 0") prefer 2 
  apply presburger
  apply(subgoal_tac "ownB s (fst(tempR s)) = R") prefer 2
  apply metis
  apply(subgoal_tac "ownB s (offset s) = W") prefer 2 
  apply (metis Nat.add_0_right le_refl nat_add_left_cancel_less)
  apply (metis F.distinct(1) W_items_dont_change_with_R)
  using ownB_by_D_doesnt_change_after_dequeue [where s=s and s'=s'] 
  using W_items_dont_change_with_R \<open>cR_step (pcR s) s s' \<Longrightarrow> tempW s = tempW s' \<and> tW s = tW s' \<and> hW s = hW s' \<and> data_index s = data_index s'\<close> assms(2) less_or_eq_imp_le 
  apply presburger
  using ownB_by_D_doesnt_change_after_read [where s=s and s'=s'] 
  using W_items_dont_change_with_R \<open>cR_step (pcR s) s s' \<Longrightarrow> tempW s = tempW s' \<and> tW s = tW s' \<and> hW s = hW s' \<and> data_index s = data_index s'\<close> assms(2) less_or_eq_imp_le 
  apply presburger
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(1) PCR.distinct(3) assms(2) apply presburger
  apply (simp add: pre_Release_inv_def) 
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(1) PCR.distinct(5) assms(2) apply presburger
  apply (simp add: pre_dequeue_inv_def inv_def Q_lemmas Q_basic_lemmas cR_step_def) 
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(3) PCR.distinct(5) assms(2) apply presburger
  apply(simp add: pre_Read_inv_def) 
  apply(simp add:cR_step_def)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(simp add:cR_step_def)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(case_tac "q s=[]", simp_all)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(case_tac "q s=[]", simp_all)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(case_tac "q s=[]", simp_all)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(simp add:cR_step_def)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply (metis last_tl)
  apply (metis last_tl)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(simp add:cR_step_def)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis assms(5))
  apply(subgoal_tac "(\<forall>i<length (q s). fst (q s ! i) \<noteq> offset s)") prefer 2 
  apply presburger
  apply(subgoal_tac "(\<forall>i<length (tl(q s)). fst (tl(q s) ! i) \<noteq> offset s)") prefer 2
  apply (metis Suc_diff_Suc diff_Suc_eq_diff_pred diff_add_0 length_tl linordered_semidom_class.add_diff_inverse nat.discI nth_tl)
  apply(subgoal_tac "length(q s) - Suc 0 = length(tl(q s))") prefer 2 
  apply (metis One_nat_def length_tl)
  apply presburger
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis assms(5))
  apply(subgoal_tac "(\<forall>i<length (q s). fst (q s ! i) \<noteq> offset s)") prefer 2 
  apply presburger
  apply(subgoal_tac "(\<forall>i<length (tl(q s)). fst (tl(q s) ! i) \<noteq> offset s)") prefer 2                  
  apply (metis Suc_diff_Suc diff_Suc_eq_diff_pred diff_add_0 length_tl linordered_semidom_class.add_diff_inverse nat.discI nth_tl)
  apply (metis One_nat_def length_tl)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis assms(5))
  apply(subgoal_tac "(\<forall>i<length (q s). fst (q s ! i) \<noteq> offset s)") prefer 2 
  apply (metis length_0_conv less_nat_zero_code)
  apply(subgoal_tac "offset s' = offset s") prefer 2
  apply (metis fst_conv tempW_def)
  apply(subgoal_tac "q s= q s'") 
  apply metis
  using R_doesnt_change_q_read_release [where s=s and s'=s']
  apply (metis PCR.distinct(5) assms(5))                
  using Q_W_relation_through_R_3 [where s=s and s'=s'] 
  apply (simp add: \<open>\<lbrakk>RingBuffer_BD_latest_2.inv s; cR_step (pcR s) s s'; pcR s \<noteq> idleR\<rbrakk> \<Longrightarrow> q s = q s'\<close>)
  apply(subgoal_tac "q s\<noteq>[]") prefer 2 
  apply (metis Q_empty_R_step_result)
  using Q_W_relation_through_R_1 [where s=s and s'=s']
  apply presburger       
  using Q_W_relation_through_R_2 [where s=s and s'=s']
  apply (simp add: \<open>\<lbrakk>RingBuffer_BD_latest_2.inv s; cR_step (pcR s) s s'; pcR s \<noteq> idleR\<rbrakk> \<Longrightarrow> q s = q s'\<close>)
  apply(subgoal_tac "q s=q s'") prefer 2 
  using R_doesnt_change_q_read_release [where s=s and s'=s']
  using PCR.distinct(1) apply presburger
  apply(subgoal_tac "offset s + Data s (numEnqs s) \<noteq> fst (hd (q s))") prefer 2 
  apply metis
  apply(subgoal_tac "tempW s=tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis)
  apply (metis W_items_dont_change_with_R)
  apply(subgoal_tac "offset s + Data s (numEnqs s) \<noteq> fst (hd (q s))") prefer 2   
  using cR_step_def apply force
  apply(subgoal_tac "i<length(q s)\<longrightarrow>offset s + Data s (numEnqs s) \<noteq> fst(q s ! i)") prefer 2 
  apply (metis diff_add_zero length_0_conv less_irrefl_nat less_nat_zero_code linordered_semidom_class.add_diff_inverse)
  apply(subgoal_tac "q s\<noteq>[]") prefer 2 
  using PCR.simps(8) cR_step_def apply force
  apply(subgoal_tac "fst(hd(q s')) = fst(hd(tl(q s)))") prefer 2 
  using R_changes_q_dequeue apply presburger
  apply(subgoal_tac "tempW s=tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(1) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "offset s' = offset s") prefer 2
  apply (metis fst_conv tempW_def)
  apply(subgoal_tac "fst(hd(tl(q s))) = fst(q s!1)") prefer 2
  using strange_but_Q_4 [where s=s] fst_def 
  apply (metis R_changes_q_dequeue length_greater_0_conv length_tl zero_less_diff)
  apply (metis R_changes_q_dequeue cancel_comm_monoid_add_class.diff_cancel le_iff_add length_0_conv length_tl less_one linorder_neqE_nat nat_less_le snd_conv tempW_def)
  apply(subgoal_tac "q s=q s'") prefer 2 
  using R_doesnt_change_q_read_release [where s=s and s'=s']
  using PCR.distinct(5) apply presburger
  apply(subgoal_tac "offset s + Data s (numEnqs s) \<noteq> fst (hd (q s))") prefer 2 
  apply metis
  apply(subgoal_tac "tempW s=tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis)
  apply (metis W_items_dont_change_with_R)
  apply clarify
  using W_items_dont_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using ownB_by_W_doesnt_change_with_R [where s=s and s'=s' and i=j]
  apply (metis \<open>\<And>i. \<lbrakk>RingBuffer_BD_latest_2.inv s; con_assms s; pre_Release_inv s; cR_step Release s s'; ownB s i = W \<and> i \<le> N\<rbrakk> \<Longrightarrow> ownB s' i = W \<and> i \<le> N\<close> assms(1) assms(2) le_trans less_imp_le_nat)
  apply clarify
  using W_items_dont_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using ownB_by_W_doesnt_change_with_R [where s=s and s'=s' and i=j]
  apply (metis PCR.distinct(1) PCR.distinct(5) \<open>\<And>i. \<lbrakk>RingBuffer_BD_latest_2.inv s; con_assms s; cR_step (pcR s) s s'; pcR s = Release \<longrightarrow> pre_Release_inv s; pcR s = Read \<longrightarrow> pre_Read_inv s; pcR s = idleR \<longrightarrow> pre_dequeue_inv s; ownB s i = W \<and> i \<le> N\<rbrakk> \<Longrightarrow> ownB s' i = W \<and> i \<le> N\<close> assms(2) le_trans less_imp_le_nat)
  using W_items_dont_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using ownB_by_W_doesnt_change_with_R [where s=s and s'=s' and i=j]
  apply (metis PCR.distinct(3) PCR.distinct(5) \<open>\<And>i. \<lbrakk>RingBuffer_BD_latest_2.inv s; con_assms s; cR_step (pcR s) s s'; pcR s = Release \<longrightarrow> pre_Release_inv s; pcR s = Read \<longrightarrow> pre_Read_inv s; pcR s = idleR \<longrightarrow> pre_dequeue_inv s; ownB s i = W \<and> i \<le> N\<rbrakk> \<Longrightarrow> ownB s' i = W \<and> i \<le> N\<close> assms(2) le_trans less_imp_le_nat)
  apply(subgoal_tac "numWrites s= numWrites s'") prefer 2
  apply (metis W_items_dont_change_with_R_3 assms(5))
  using R_doesnt_change_ownD_release_dequeue [where s=s and s'=s']
  apply (metis PCR.distinct(3))
  apply(subgoal_tac "numWrites s= numWrites s'") prefer 2
  apply (metis W_items_dont_change_with_R_3 assms(5))
  using R_doesnt_change_ownD_release_dequeue [where s=s and s'=s']
  apply (metis PCR.distinct(5))
  apply(subgoal_tac "numWrites s= numWrites s'") prefer 2
  apply (metis W_items_dont_change_with_R_3 assms(5))
  apply(subgoal_tac "numWrites s \<noteq> data_index s (tempR s) ") prefer 2 
  apply(simp add:pre_Read_inv_def)
  using R_doesnt_change_ownD_read_except [where s=s and s'=s']
  apply (metis less_eq_nat.simps(1))
  apply(subgoal_tac "q s=q s'") prefer 2
  using R_doesnt_change_q_read_release [where s=s and s'=s']
  using PCR.distinct(1) apply presburger
  apply (metis W_items_dont_change_with_R)
  apply(simp add:inv_def pre_dequeue_inv_def)
  apply(subgoal_tac "numEnqs s= 0") prefer 2
  using W_items_dont_change_with_R apply presburger
  apply(subgoal_tac "numDeqs s = 0") prefer 2
  apply (metis less_nat_zero_code nat_less_le)
  apply(subgoal_tac "q s=[]") prefer 2
  apply meson
  apply(simp add:cR_step_def) 
  apply(subgoal_tac "q s=q s'") prefer 2
  using R_doesnt_change_q_read_release [where s=s and s'=s']
  using PCR.distinct(5) apply presburger
  apply (metis W_items_dont_change_with_R)
  using W_items_dont_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply metis
  using W_items_dont_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply metis
  using W_items_dont_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply metis
  using W_items_dont_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using W_items_dont_change_with_R_3 [where s=s and s'=s']
  apply (metis)
  using W_items_dont_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using W_items_dont_change_with_R_3 [where s=s and s'=s']
  apply (metis)
  using W_items_dont_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using W_items_dont_change_with_R_3 [where s=s and s'=s']
  by (metis)



lemma pre_enqueue_doesnt_change_with_R:
  assumes "inv s"
  and "con_assms s"
  and "pre_enqueue_inv s"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_enqueue_inv s'"
  using assms apply simp
  apply(simp add:pre_enqueue_inv_def)
  apply(subgoal_tac "end(tempW s )\<le>N") prefer 2 apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:pre_R_def)
  apply(intro conjI impI)
  apply(case_tac[!] "pcR s")
  apply simp_all apply(subgoal_tac "\<forall>i. offset s \<le> i \<and> i < fst (tempW s) + snd (tempW s) \<longrightarrow> ownB s i = W") prefer 2
  apply metis   apply(subgoal_tac "\<forall>i. offset s > i \<or> i \<ge> fst (tempW s) + snd (tempW s) \<and> i\<le>N \<longrightarrow> ownB s i \<noteq> W") prefer 2
  apply metis
  apply(subgoal_tac "hW s = hW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(1) PCR.distinct(3) assms(2) apply presburger
  apply(subgoal_tac "tW s = tW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(1) PCR.distinct(3) assms(2) apply presburger
  using ownB_by_W_doesnt_change_after_release [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply (metis PCR.distinct(1) PCR.distinct(3) W_items_dont_change_with_R assms(2) end_simp le_trans less_or_eq_imp_le)
  using ownB_by_W_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply (metis PCR.distinct(1) PCR.distinct(5) W_items_dont_change_with_R assms(2) le_trans less_or_eq_imp_le)
  using ownB_by_W_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis PCR.distinct(3) PCR.distinct(5) W_items_dont_change_with_R assms(2) le_trans less_or_eq_imp_le)
  apply clarify
  apply (intro conjI impI)
  using ownB_not_by_W_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis PCR.distinct(1) PCR.distinct(3) add_leD1 assms(2) fst_conv less_le_not_le order_trans tempW_def)
  using ownB_not_by_W_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis PCR.distinct(1) PCR.distinct(3) add_leD1 assms(2) fst_conv less_le_not_le order_trans tempW_def)
  using ownB_not_by_W_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply clarify
  apply (intro conjI impI)
  using ownB_not_by_W_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis PCR.distinct(1) PCR.distinct(5) add_leD1 assms(2) fst_conv le_imp_less_Suc nat_le_linear not_less_eq order_trans tempW_def)
  using ownB_not_by_W_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis PCR.distinct(1) PCR.distinct(5) add_leD1 assms(2) fst_conv le_imp_less_Suc nat_le_linear not_less_eq order_trans tempW_def)
  apply clarify
  apply (intro conjI impI) 
  apply(subgoal_tac "i<offset s \<longrightarrow>ownB s i\<noteq>W") prefer 2 
  apply presburger
  apply(subgoal_tac "offset s = offset s'") prefer 2 
  using PCR.distinct(3) PCR.distinct(5) W_items_dont_change_with_R assms(2) apply presburger
  using ownB_not_by_W_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis PCR.distinct(3) PCR.distinct(5) add_leD1 assms(2) fst_conv less_le_not_le order_trans tempW_def)
  using ownB_not_by_W_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(3) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(1) PCR.distinct(3) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis RingBuffer_BD_latest_2.inv_def basic_pointer_movement_def inRange_def inRangeht_def)
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply (metis PCR.distinct(1) PCR.distinct(3) assms(2) le_trans less_or_eq_imp_le)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(1) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis RingBuffer_BD_latest_2.inv_def basic_pointer_movement_def inRange_def inRangeht_def)
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis PCR.distinct(1) PCR.distinct(5) assms(2) le_trans less_or_eq_imp_le)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(3) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis RingBuffer_BD_latest_2.inv_def basic_pointer_movement_def inRange_def inRangeht_def)
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply (metis PCR.distinct(3) PCR.distinct(5) assms(2) le_trans less_or_eq_imp_le)
  apply clarify
  apply(intro conjI impI)        
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(1) PCR.distinct(3) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:inv_def)
  apply (metis assms(1) assms(2) less_or_eq_imp_le ownB_by_B_doesnt_change_after_release prod.inject tempW_def)
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply (metis PCR.distinct(1) PCR.distinct(3) add_leD1 assms(2) fst_conv less_le_not_le order_trans tempW_def)
  apply clarify
  apply(intro conjI impI)        
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(1) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:inv_def) 
  apply (metis assms(1) assms(2) less_or_eq_imp_le ownB_by_B_doesnt_change_after_dequeue prod.inject tempW_def)
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply (metis PCR.distinct(1) PCR.distinct(5) add_leD1 assms(2) fst_conv less_le_not_le order_trans tempW_def)
  apply clarify
  apply(intro conjI impI)        
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(3) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:inv_def) 
  apply (metis assms(1) assms(2) less_or_eq_imp_le ownB_by_B_doesnt_change_after_read prod.inject tempW_def)
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis PCR.distinct(3) PCR.distinct(5) add_leD1 assms(2) fst_conv less_le_not_le order_trans tempW_def)
  apply clarify       
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(1) PCR.distinct(3) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:inv_def) 
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply (metis PCR.distinct(1) PCR.distinct(3) add_leD1 assms(2) fst_conv less_le_not_le order_trans tempW_def)
  apply clarify       
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(1) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:inv_def) 
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply (metis PCR.distinct(1) PCR.distinct(5) add_leD1 assms(2) fst_conv less_le_not_le order_trans tempW_def)
  apply clarify
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(3) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:inv_def) 
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis PCR.distinct(3) PCR.distinct(5) add_leD1 assms(2) fst_conv less_le_not_le order_trans tempW_def)
  apply(case_tac "tR s = fst(tempR s)")
  using ownB_by_D_doesnt_change_after_release [where s=s and s'=s'] 
  apply (metis W_items_dont_change_with_R \<open>cR_step (pcR s) s s' \<Longrightarrow> tempW s = tempW s' \<and> tW s = tW s' \<and> hW s = hW s' \<and> data_index s = data_index s'\<close> assms(2) nat_less_le)
  apply (simp add:inv_def)
  apply(case_tac "case_1 s", simp_all)
  apply(simp add: case_1_def)
  apply (metis F.distinct(15) F.distinct(21) F.distinct(25) F.distinct(7) W_items_dont_change_with_R \<open>cR_step (pcR s) s s' \<Longrightarrow> tempW s = tempW s' \<and> tW s = tW s' \<and> hW s = hW s' \<and> data_index s = data_index s'\<close> less_eq_Suc_le not_less_eq_eq)
  apply(thin_tac "\<not>case_1 s")
  apply(simp add:pre_Release_inv_def)
  apply(subgoal_tac "T s\<noteq>fst(tempR s)") prefer 2 
  apply blast
  apply(simp add:case_2_def)
  apply clarify
  apply(subgoal_tac "fst(tempR s) = T s \<or> fst(tempR s) = 0") prefer 2 
  apply meson
  apply(subgoal_tac "fst(tempR s) = 0") prefer 2 
  apply presburger
  apply(subgoal_tac "ownB s (fst(tempR s)) = R") prefer 2
  apply metis
  apply(subgoal_tac "ownB s (offset s) = W") prefer 2 
  apply (metis \<open>cR_step (pcR s) s s' \<Longrightarrow> tempW s = tempW s' \<and> tW s = tW s' \<and> hW s = hW s' \<and> data_index s = data_index s'\<close> fst_eqD nat_le_iff_add plus_nat.add_0 snd_eqD tempW_def)
  apply (metis F.distinct(1) W_items_dont_change_with_R)
  using ownB_by_D_doesnt_change_after_dequeue [where s=s and s'=s'] 
  using W_items_dont_change_with_R \<open>cR_step (pcR s) s s' \<Longrightarrow> tempW s = tempW s' \<and> tW s = tW s' \<and> hW s = hW s' \<and> data_index s = data_index s'\<close> assms(2) less_or_eq_imp_le 
  apply presburger
  using ownB_by_D_doesnt_change_after_read [where s=s and s'=s'] 
  using W_items_dont_change_with_R \<open>cR_step (pcR s) s s' \<Longrightarrow> tempW s = tempW s' \<and> tW s = tW s' \<and> hW s = hW s' \<and> data_index s = data_index s'\<close> assms(2) less_or_eq_imp_le 
  apply presburger
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(1) PCR.distinct(3) assms(2) apply presburger
  apply (simp add: pre_Release_inv_def) 
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(1) PCR.distinct(5) assms(2) apply presburger
  apply (simp add: pre_dequeue_inv_def inv_def Q_lemmas Q_basic_lemmas cR_step_def) 
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(3) PCR.distinct(5) assms(2) apply presburger
  apply(simp add: pre_Read_inv_def) 
  apply(simp add:cR_step_def)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(simp add:cR_step_def)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(case_tac "q s=[]", simp_all)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(case_tac "q s=[]", simp_all)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(simp add:cR_step_def)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(simp add:cR_step_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(intro conjI impI)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(1) PCR.distinct(3) assms(2) apply presburger 
  apply (metis fst_conv snd_conv tempW_def)
  apply (metis PCR.distinct(1) R_doesnt_change_q_read_release W_items_dont_change_with_R)
  apply (metis PCR.distinct(1) R_doesnt_change_q_read_release W_items_dont_change_with_R)
  apply (metis (no_types, lifting) PCR.distinct(1) R_doesnt_change_q_read_release W_items_dont_change_with_R assms(1) assms(5))
  apply (metis PCR.distinct(1) R_doesnt_change_q_read_release W_items_dont_change_with_R) 
  apply (metis W_items_dont_change_with_R \<open>\<And>i. \<lbrakk>RingBuffer_BD_latest_2.inv s; con_assms s; pre_Release_inv s; cR_step Release s s'; ownB s i = W \<and> i \<le> N\<rbrakk> \<Longrightarrow> ownB s' i = W \<and> i \<le> N\<close> assms(2) le_trans less_imp_le_nat)
  prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(intro conjI impI)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(1) PCR.distinct(3) assms(2) apply presburger 
  apply (metis fst_conv snd_conv tempW_def) 
  apply (metis PCR.distinct(5) R_doesnt_change_q_read_release W_items_dont_change_with_R)
  apply (metis PCR.distinct(5) R_doesnt_change_q_read_release W_items_dont_change_with_R)
  apply (metis (no_types, lifting) PCR.distinct(5) R_doesnt_change_q_read_release W_items_dont_change_with_R assms(1) assms(5))
  apply (metis PCR.distinct(5) R_doesnt_change_q_read_release W_items_dont_change_with_R)
  apply (metis PCR.distinct(3) PCR.distinct(5) W_items_dont_change_with_R \<open>\<And>i. \<lbrakk>RingBuffer_BD_latest_2.inv s; con_assms s; cR_step (pcR s) s s'; pcR s = Release \<longrightarrow> pre_Release_inv s; pcR s = Read \<longrightarrow> pre_Read_inv s; pcR s = idleR \<longrightarrow> pre_dequeue_inv s; ownB s i = W \<and> i \<le> N\<rbrakk> \<Longrightarrow> ownB s' i = W \<and> i \<le> N\<close> \<open>\<And>i. \<lbrakk>RingBuffer_BD_latest_2.inv s; con_assms s; cR_step (pcR s) s s'; pcR s = Release \<longrightarrow> pre_Release_inv s; pcR s = Read \<longrightarrow> pre_Read_inv s; pcR s = idleR \<longrightarrow> pre_dequeue_inv s; ownB s i \<noteq> W \<and> i \<le> N\<rbrakk> \<Longrightarrow> ownB s' i \<noteq> W \<and> i \<le> N\<close> assms(2) le_trans less_imp_le_nat)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)   
  apply(intro conjI impI) apply(simp add:pre_dequeue_inv_def)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply presburger               
  apply (metis fst_conv snd_conv tempW_def) 
  apply(case_tac "length(q s)>1", simp_all)
  apply(subgoal_tac "last(q s) = last(tl(q s))") prefer 2 
  apply (metis R_changes_q_dequeue last_tl)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply presburger    
  apply(subgoal_tac "q s\<noteq>[]") prefer 2
  apply (metis length_0_conv less_nat_zero_code)
  apply (simp add: R_changes_q_dequeue W_items_dont_change_with_R)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply presburger    
  apply(subgoal_tac "length(q s) = 1 \<longrightarrow> tl(q s) = []") prefer 2 
  apply (metis cancel_comm_monoid_add_class.diff_cancel length_greater_0_conv length_tl not_gr0)
  apply(case_tac "q s=[]") prefer 2 
  apply (metis One_nat_def R_changes_q_dequeue Suc_lessI length_greater_0_conv)
  apply(simp add:pre_dequeue_inv_def)
  apply(subgoal_tac "q s= []") prefer 2
  apply blast
  apply(subgoal_tac "q s'=[]") prefer 2
  using Q_empty_R_step_result [where s=s and s'=s'] 
  apply presburger
  apply linarith
  apply(subgoal_tac "q s\<noteq>[]") prefer 2
  using \<open>\<lbrakk>cR_step (pcR s) s s'; q s = []; pcR s = idleR\<rbrakk> \<Longrightarrow> q s' = []\<close> apply presburger
  apply(subgoal_tac "q s'= tl(q s)") prefer 2
  using R_changes_q_dequeue apply presburger
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply presburger  
  apply (metis in_set_conv_nth list.set_sel(2) prod.inject tempW_def)
  using Q_W_relation_through_R_1 [where s=s and s'=s']
  using \<open>\<lbrakk>cR_step (pcR s) s s'; q s = []; pcR s = idleR\<rbrakk> \<Longrightarrow> q s' = []\<close> apply presburger
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply presburger  
  apply(subgoal_tac "q s'= tl(q s)") prefer 2
  using R_changes_q_dequeue 
  using \<open>\<lbrakk>cR_step (pcR s) s s'; q s = []; pcR s = idleR\<rbrakk> \<Longrightarrow> q s' = []\<close> apply presburger
  apply(subgoal_tac "offset s = offset s' \<and>  numEnqs s = numEnqs s'") prefer 2
  using W_items_dont_change_with_R [where s=s and s'=s']
  apply presburger
  apply (metis Nat.add_0_right \<open>\<lbrakk>cR_step (pcR s) s s'; q s = []; pcR s = idleR\<rbrakk> \<Longrightarrow> q s' = []\<close> \<open>cR_step (pcR s) s s' \<Longrightarrow> offset s = offset s' \<and> Data s (numEnqs s) = Data s' (numEnqs s') \<and> numEnqs s = numEnqs s'\<close> hd_in_set in_set_conv_nth less_not_refl list.set_sel(2) nat_add_left_cancel_less)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply presburger  
  apply(subgoal_tac "offset s = offset s'") prefer 2
  using \<open>cR_step (pcR s) s s' \<Longrightarrow> offset s = offset s' \<and> Data s (numEnqs s) = Data s' (numEnqs s') \<and> numEnqs s = numEnqs s'\<close> apply presburger
  apply(subgoal_tac "Data s' (numEnqs s') = Data s (numEnqs s)") prefer 2 
  apply (metis \<open>cR_step (pcR s) s s' \<Longrightarrow> offset s = offset s' \<and> Data s (numEnqs s) = Data s' (numEnqs s') \<and> numEnqs s = numEnqs s'\<close>)
  apply(subgoal_tac "\<forall>j. offset s \<le> j \<and> j < offset s + Data s (numEnqs s) \<longrightarrow> ownB s j = W") prefer 2 
  apply presburger
  apply(clarify)  
  using ownB_by_W_doesnt_change_after_dequeue [where s=s and s'=s' and i=j]
  apply (metis PCR.distinct(1) PCR.distinct(5) \<open>\<And>i. \<lbrakk>RingBuffer_BD_latest_2.inv s; con_assms s; cR_step (pcR s) s s'; pcR s = Release \<longrightarrow> pre_Release_inv s; pcR s = Read \<longrightarrow> pre_Read_inv s; pcR s = idleR \<longrightarrow> pre_dequeue_inv s; ownB s i = W \<and> i \<le> N\<rbrakk> \<Longrightarrow> ownB s' i = W \<and> i \<le> N\<close> assms(2) le_trans less_or_eq_imp_le)
  apply(simp add:tempW_reflects_writes_def)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(1) PCR.distinct(3) assms(2) apply presburger
  apply(simp add: pre_Read_inv_def)
  apply(subgoal_tac "data_index s (offset s, Data s (numEnqs s)) = numEnqs s") prefer 2
  apply meson
  apply(subgoal_tac "data_index s = data_index s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(1) PCR.distinct(3) assms(2) apply presburger
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis W_items_dont_change_with_R)
  apply(simp add:tempW_reflects_writes_def)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(1) PCR.distinct(5) assms(2) apply presburger
  apply(simp add: pre_Read_inv_def)
  apply(subgoal_tac "data_index s (offset s, Data s (numEnqs s)) = numEnqs s") prefer 2
  apply meson
  apply(subgoal_tac "data_index s = data_index s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(1) PCR.distinct(5) assms(2) apply presburger
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis W_items_dont_change_with_R)
  apply(simp add:tempW_reflects_writes_def)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using PCR.distinct(3) PCR.distinct(5) assms(2) apply presburger
  apply(simp add: pre_Read_inv_def)
  apply(subgoal_tac "data_index s (offset s, Data s (numEnqs s)) = numEnqs s") prefer 2
  apply meson
  apply(subgoal_tac "data_index s = data_index s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply (metis)
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis W_items_dont_change_with_R)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(case_tac "q s=[]", simp_all)
  apply(simp add:cR_step_def)
  apply(simp add:pre_Read_inv_def)
  apply(simp add:cR_step_def)
  apply(case_tac " tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac " ownT s = R", simp_all)
  apply(case_tac " ownT s = R", simp_all)
  apply(simp add:cR_step_def)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac " ownT s = Q", simp_all)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(case_tac "q s=[]", simp_all)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(simp add:cR_step_def)
  apply(case_tac "q s=[]", simp_all)
  by(simp add:cR_step_def)








lemma pre_A1_doesnt_change_with_R:
  assumes "inv s"
  and "con_assms s"
  and "pre_A1_inv s"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_A1_inv s'"
  using assms apply simp
  apply(simp add:pre_A1_inv_def) 
  apply(intro conjI impI)
  apply(simp add:cR_step_def)
  apply(cases "pcR s", simp_all) 
  apply(cases " tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all) 
  apply(simp add:pre_R_def pre_Release_inv_def inv_def) 
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_def) apply metis
  apply(simp) apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis (no_types, hide_lams) diff_is_0_eq le0 nat_neq_iff zero_less_diff)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def)
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_def) 
  apply (metis Nat.add_diff_assoc diff_diff_left diff_is_0_eq' linorder_neqE_nat nat_le_linear zero_less_diff)
  apply(simp) apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis not_add_less1)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac " ownT s = Q ", simp_all)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def)
  apply(cases "pcR s", simp_all)
  apply(simp add:cR_step_def)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all) 
  apply(simp add:pre_R_def pre_Release_inv_def inv_def)
  apply(case_tac "ownT s = R", simp_all) 
  apply(simp add:pre_R_def pre_Release_inv_def inv_def)
  apply(simp add:pre_R_def pre_dequeue_inv_def inv_def)
  apply(simp add:cR_step_def)
  apply(case_tac "q s = []", simp_all)
  apply(simp add:pre_R_def pre_Read_inv_def inv_def cR_step_def)
  apply(simp add:pre_R_def pre_Read_inv_def inv_def cR_step_def)
  apply(cases "pcR s", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all) 
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_def) apply metis
  apply(simp) apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis diff_self_eq_0 le_antisym le_neq_implies_less length_greater_0_conv less_imp_Suc_add nat.distinct(1) plus_nat.add_0)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "ownT s = R", simp_all) 
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_def) 
  apply (metis bot_nat_0.extremum_uniqueI diff_self_eq_0 le_add_diff_inverse le_antisym length_0_conv)
  apply(simp) apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis not_add_less1)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac " ownT s = Q ", simp_all)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(cases "pcR s", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(cases "pcR s", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(cases "pcR s", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all) 
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_def) apply metis
  apply(simp) apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis add_cancel_right_left le_refl)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "ownT s = R", simp_all) 
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_def) 
  apply (metis le_add_diff_inverse le_eq_less_or_eq)
  apply(simp) apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis (no_types, hide_lams) le_add_diff_inverse le_trans less_or_eq_imp_le linorder_neqE_nat nat_less_le)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac " ownT s = Q ", simp_all)
  apply(simp add:pre_R_def pre_dequeue_inv_def inv_def)
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_def)
  apply (metis le_antisym nat_less_le)
  apply(simp) apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis (no_types, lifting) F.distinct(19))
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_def) 
  apply (metis F.distinct(13) F.distinct(17) le_eq_less_or_eq)
  apply(simp) apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply(simp add:pre_R_def pre_dequeue_inv_def inv_def)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(cases "pcR s", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all) 
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_def) 
  apply (metis le_add_diff_inverse le_eq_less_or_eq)
  apply(simp) apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis (no_types, hide_lams) le_add_diff_inverse le_trans less_or_eq_imp_le linorder_neqE_nat nat_less_le)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "ownT s = R", simp_all) 
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply (metis le_eq_less_or_eq nat_le_linear)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac " ownT s = Q ", simp_all)
  apply(simp add:pre_R_def pre_dequeue_inv_def inv_def)
  apply (metis (no_types, hide_lams) F.distinct(19))
  apply(simp add:pre_R_def pre_dequeue_inv_def inv_def)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(cases "pcR s", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(cases "pcR s", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(cases "pcR s", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(cases "pcR s", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(cases "pcR s", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all) 
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "ownT s = R", simp_all) 
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  by(case_tac "q s = []", simp_all)



lemma pre_A2_doesnt_change_with_R:
  assumes "inv s"
  and "con_assms s"
  and "pre_A2_inv s"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_A2_inv s'"
  using assms apply simp
  apply(simp add:pre_A2_inv_def) 
  apply(intro conjI impI)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac[!] "pcR s", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all) 
  apply(case_tac "ownT s = R", simp_all) 
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "ownT s = Q", simp_all) 
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all) 
  apply(case_tac "ownT s = R", simp_all) 
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "ownT s = Q", simp_all) 
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all) 
  apply(case_tac "ownT s = R", simp_all) 
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "ownT s = Q", simp_all) 
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def) 
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "ownT s = Q", simp_all) 
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "ownT s = Q", simp_all) 
  apply(simp_all add:pre_R_def pre_dequeue_inv_def inv_def cR_step_def) 
  apply (metis (no_types, hide_lams) F.distinct(19))
  apply(case_tac "T s \<noteq> fst (tempR s)", simp_all)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply metis
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis add_cancel_right_left le_trans)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis (no_types, lifting) F.distinct(13) eq_imp_le less_imp_le_nat linorder_neqE_nat trans_le_add1)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq trans_le_add1)
  apply(case_tac "q s = []", simp_all)
  apply metis
  apply metis
  apply metis
  apply(case_tac "T s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq trans_le_add1)
  apply(case_tac "T s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq trans_le_add1)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "T s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq trans_le_add1)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis le_add_diff_inverse le_eq_less_or_eq)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "T s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply blast
  by(simp_all add:pre_R_def pre_Read_inv_def inv_def cR_step_def)





lemma pre_A3_doesnt_change_with_R:
  assumes "inv s"
  and "con_assms s"
  and "pre_A3_inv s"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_A3_inv s'"
  using assms apply simp
  apply(simp add:pre_A3_inv_def) 
  apply(intro conjI impI)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac[!] "pcR s", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  by(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)




lemma pre_A4_doesnt_change_with_R:
  assumes "inv s"
  and "con_assms s"
  and "pre_A4_inv s"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_A4_inv s'"
  using assms apply simp
  apply(simp add:pre_A4_inv_def) 
  apply(intro conjI impI)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac[!] "pcR s", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(simp_all add:pre_R_def pre_dequeue_inv_def inv_def cR_step_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis (no_types, hide_lams) F.distinct(19))
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis add_cancel_right_left le_trans)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis F.distinct(13) eq_imp_le less_imp_le_nat linorder_neqE_nat trans_le_add1)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq trans_le_add1)
  apply(case_tac "q s=[]", simp_all)
  apply metis+
  apply(case_tac "q s=[]", simp_all)
  by metis+
  



lemma pre_A5_doesnt_change_with_R:
  assumes "inv s"
  and "con_assms s"
  and "pre_A5_inv s"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_A5_inv s'"
  using assms apply simp
  apply(simp add:pre_A5_inv_def) 
  apply(intro conjI impI)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac[!] "pcR s", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(simp_all add:pre_R_def pre_dequeue_inv_def inv_def cR_step_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis (no_types, hide_lams) F.distinct(19))
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis add_cancel_right_left le_trans)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis F.distinct(13) eq_imp_le less_imp_le_nat linorder_neqE_nat trans_le_add1)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq trans_le_add1)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis le_add_diff_inverse le_trans)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq)
  apply(case_tac "q s=[]", simp_all)
  by(case_tac "q s=[]", simp_all)
  



lemma pre_A6_doesnt_change_with_R:
  assumes "inv s"
  and "con_assms s"
  and "pre_A6_inv s"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_A6_inv s'"
  using assms apply simp
  apply(simp add:pre_A6_inv_def) 
  apply(intro conjI impI)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac[!] "pcR s", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(simp_all add:pre_R_def pre_dequeue_inv_def inv_def cR_step_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis (no_types, hide_lams) F.distinct(19))
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis add_cancel_right_left le_trans)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "T s \<noteq> fst (tempR s)", simp_all)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis F.distinct(13) eq_imp_le less_imp_le_nat linorder_neqE_nat trans_le_add1)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq trans_le_add1)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis le_add_diff_inverse le_trans)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq)
  apply(case_tac "q s=[]", simp_all)
  by(case_tac "q s=[]", simp_all)






lemma pre_A7_doesnt_change_with_R:
  assumes "inv s"
  and "con_assms s"
  and "pre_A7_inv s"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_A7_inv s'"
  using assms apply simp
  apply(simp add:pre_A7_inv_def) 
  apply(intro conjI impI)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac[!] "pcR s", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(simp_all add:pre_R_def pre_dequeue_inv_def inv_def cR_step_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis (no_types, hide_lams) F.distinct(19))
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis add_cancel_right_left le_trans)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "T s \<noteq> fst (tempR s)", simp_all)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis F.distinct(13) eq_imp_le less_imp_le_nat linorder_neqE_nat trans_le_add1)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq trans_le_add1)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis le_add_diff_inverse le_trans)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq)
  apply(case_tac "q s=[]", simp_all)
  by(case_tac "q s=[]", simp_all)





lemma pre_A8_doesnt_change_with_R:
  assumes "inv s"
  and "con_assms s"
  and "pre_A8_inv s"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_A8_inv s'"
  using assms apply simp
  apply(simp add:pre_A8_inv_def) 
  apply(intro conjI impI)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac[!] "pcR s", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(simp_all add:pre_R_def pre_dequeue_inv_def inv_def cR_step_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis (no_types, hide_lams) F.distinct(19))
  apply(case_tac "q s=[]", simp_all) 
  apply (metis (no_types, lifting) F.distinct(19))
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all) 
  apply metis
  apply metis
  apply(case_tac "ownT s = R", simp_all)
  apply metis
  apply metis
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all) 
  apply(case_tac "ownT s =R", simp_all) 
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all) 
  apply(case_tac "ownT s =R", simp_all) 
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all) 
  apply(case_tac "ownT s =R", simp_all) 
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all) 
  apply(case_tac "ownT s =R", simp_all) 
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "ownT s =R", simp_all) 
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis add_cancel_right_left le_trans)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis le_add_diff_inverse le_eq_less_or_eq)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq trans_le_add1)
  apply(case_tac "q s=[]", simp_all) 
  apply metis+
  apply(case_tac "q s=[]", simp_all)
  by metis+





lemma pre_acquire_doesnt_change_with_R:
  assumes "inv s"
  and "con_assms s"
  and "pre_acquire_inv s"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_acquire_inv s'"
  using assms apply simp
  apply(simp add:pre_acquire_inv_def) 
  apply(intro conjI impI)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac[!] "pcR s", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply metis
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis eq_imp_le less_imp_le_nat linorder_neqE_nat plus_nat.add_0)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis diff_is_0_eq' linorder_neqE_nat nat_le_linear zero_less_diff)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis eq_imp_le less_imp_le_nat linorder_neqE_nat plus_nat.add_0)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all) 
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis diff_is_0_eq' linorder_neqE_nat nat_le_linear zero_less_diff)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis add_cancel_right_left diff_add_inverse2 le_0_eq le_antisym length_0_conv nat_less_le)
  apply(case_tac "ownT s = R", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis bot_nat_0.extremum_uniqueI diff_self_eq_0 le_add_diff_inverse le_antisym length_0_conv)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis not_add_less1)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis bot_nat_0.extremum_uniqueI diff_self_eq_0 le_add_diff_inverse le_antisym length_0_conv)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s") 
  apply (metis add_cancel_left_left diff_is_0_eq' le_neq_implies_less length_greater_0_conv zero_less_diff)
  apply(case_tac "ownT s =R", simp_all) 
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def) 
  apply (metis le_add_diff_inverse le_imp_less_Suc length_greater_0_conv nat_less_le not_less_eq zero_less_diff)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis not_add_less1)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis bot_nat_0.extremum_uniqueI diff_self_eq_0 le_add_diff_inverse le_antisym length_0_conv)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis less_or_eq_imp_le plus_nat.add_0)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis le_add_diff_inverse le_eq_less_or_eq)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis le_add_diff_inverse le_trans less_nat_zero_code less_or_eq_imp_le nat_less_le nat_neq_iff)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(simp add:pre_dequeue_inv_def)
  apply (metis (mono_tags, hide_lams) F.distinct(19))
  apply(simp add:pre_dequeue_inv_def)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply (metis le_add_diff_inverse le_eq_less_or_eq)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply (metis plus_nat.add_0)
  apply (metis le_add_diff_inverse le_trans less_nat_zero_code less_or_eq_imp_le nat_less_le nat_neq_iff)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(simp add:pre_dequeue_inv_def)
  apply (metis (mono_tags, hide_lams) F.distinct(19))
  apply(simp add:pre_dequeue_inv_def)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  by(case_tac "q s=[]", simp_all)



lemma pre_OOM_doesnt_change_with_R:
  assumes "inv s"
  and "con_assms s"
  and "pre_OOM_inv s"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_OOM_inv s'"
  using assms apply simp
  apply(simp add:pre_OOM_inv_def) 
  apply(intro conjI impI)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac[!] "pcR s", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(simp_all add:pre_R_def pre_dequeue_inv_def inv_def cR_step_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all) 
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all) 
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_def)
  apply(case_tac "ownT s =R", simp_all)
  apply(simp add:case_2_def) apply(thin_tac "\<not>case_1 s")
  apply(case_tac "ownT s =R", simp_all)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "q s=[]", simp_all) 
  apply (metis (no_types, lifting) F.distinct(19))
  apply(case_tac "q s=[]", simp_all) 
  apply(case_tac "q s=[]", simp_all) 
  apply(case_tac "q s=[]", simp_all) 
  apply(case_tac "T s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "q s=[]", simp_all) 
  apply(case_tac "q s=[]", simp_all) 
  apply(case_tac "q s=[]", simp_all) 
  apply(case_tac "q s=[]", simp_all) 
  apply blast
  by(simp_all add:pre_R_def pre_Read_inv_def inv_def cR_step_def)
  




lemma pre_finished_doesnt_change_with_R:
  assumes "inv s"
  and "con_assms s"
  and "pre_finished_inv s"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_finished_inv s'"
  using assms apply simp
  apply(simp add:pre_finished_inv_def) 
  apply(intro conjI impI)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac[!] "pcR s", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  by(case_tac "q s=[]", simp_all)






lemma pre_BTS_doesnt_change_with_R:
  assumes "inv s"
  and "con_assms s"
  and "pre_BTS_inv s"
  and "pre_R (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "pre_BTS_inv s'"
  using assms apply simp
  apply(simp add:pre_BTS_inv_def) 
  apply(intro conjI impI)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac[!] "pcR s", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(simp_all add:pre_R_def pre_dequeue_inv_def inv_def cR_step_def)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(simp_all add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "q s=[]", simp_all)
  apply blast
  by(simp_all add:pre_R_def pre_Read_inv_def inv_def cR_step_def)
 



(*******************************GLOBAL R_step preserves preW*************************************)



lemma GLOBAL_R_step_shows_preW:
  assumes "inv s"
  and "con_assms s"
  and "pre_R (pcR s) s"
  and "pre_W (pcW s) s"
  and "cR_step (pcR s) s s'"
shows "pre_W (pcW s') s'"
  using assms apply simp
  apply(subgoal_tac "pcW s' = pcW s") prefer 2
  using pcW_doesnt_change_with_R [where s=s and s'=s']
  apply simp
  apply(simp add:pre_W_def) apply(case_tac "pcW s") apply simp_all
  using pre_A1_doesnt_change_with_R [where s=s and s'=s'] apply simp
  using pre_A2_doesnt_change_with_R [where s=s and s'=s'] apply simp
  using pre_A3_doesnt_change_with_R [where s=s and s'=s'] apply simp
  using pre_A4_doesnt_change_with_R [where s=s and s'=s'] apply simp
  using pre_A5_doesnt_change_with_R [where s=s and s'=s'] apply simp
  using pre_A6_doesnt_change_with_R [where s=s and s'=s'] apply simp
  using pre_A7_doesnt_change_with_R [where s=s and s'=s'] apply simp
  using pre_A8_doesnt_change_with_R [where s=s and s'=s'] apply simp
  using pre_enqueue_doesnt_change_with_R [where s=s and s'=s'] apply simp 
  using pre_acquire_doesnt_change_with_R [where s=s and s'=s'] apply simp
  using pre_OOM_doesnt_change_with_R [where s=s and s'=s'] apply simp
  using pre_finished_doesnt_change_with_R [where s=s and s'=s'] apply simp
  using pre_write_doesnt_change_with_R [where s=s and s'=s'] apply simp  
  using pre_BTS_doesnt_change_with_R [where s=s and s'=s'] by simp


















































(*(*

(*------------------------showing progress----------------------*)
(*
lemma tries_are_bounded:
  assumes "con_assms s"
  and "cW_step pcw s s'"
  and "inv pcw pcr s"
shows "tries s'\<le>N"
  using assms
  apply (simp_all add:cW_step_def)
  using less_le_trans apply auto[1]
  apply (case_tac "pcw", simp_all)
  using less_imp_le_nat apply blast
  using less_imp_le_nat apply blast
  using less_imp_le_nat apply blast
  using less_imp_le_nat apply blast
  using less_imp_le_nat apply blast
  using less_imp_le_nat apply blast
  using less_imp_le_nat apply blast
  using less_imp_le_nat apply blast
  apply(case_tac "numEnqs s < n", simp_all add:less_imp_le)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  using Suc_leI apply blast
  by (meson less_imp_le_nat)


lemma when_W_moves_prog_less:
  assumes "con_assms s"
  and "inv (pcW s) (pcR s) s"
  and "cW_step (pcW s) s s'"
shows "lex_prog s s'"
proof - 
  from assms(1) have sp1: "numEnqs s \<le> n \<and> numDeqs s \<le> n"
    using con_assms_def by auto
  from assms show ?thesis
  apply (simp_all add:cW_step_def inv_def  progress_lemmas tries_left_def)
  apply(case_tac "pcW s", simp_all)
  apply(case_tac[!] "pcR s", simp_all)
  apply (simp_all add: diff_less_mono2)
  apply (case_tac[!] "tW s = T s", simp_all add:cW_step_def)
  apply(case_tac[1-6] "numEnqs s < n", simp_all)
  using diff_less_mono2 by auto
qed

lemma W_counter_implies_notown:
  assumes "con_assms s"
  and "mainInv s"
shows "\<forall>i.(i<numEnqs s)\<longrightarrow>ownD s i \<in> {R,B}"
  using assms
  apply (simp_all add:inv_def)
  by (meson le_less_linear)


lemma least_prog_W_implies:
  assumes "con_assms s"
  and "inv (pcW s) pcr s"
  and "cW_step (pcW s) s s'"
  and "inv (pcW s') pcr s'"
  and "lex_prog s s'"
shows "end_W_prog s'=True\<longrightarrow>end_W_prog s \<or> ((\<forall>i.(i<n)\<longrightarrow>ownD s' i\<noteq>W) \<and> (pcW s=idleW) \<and> numEnqs s=n)"
  using assms W_counter_implies_notown
  apply (simp_all add: end_W_prog_def progress_lemmas tries_left_def cW_step_def inv_def)
  apply (case_tac "pcW s", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "pcr", simp_all)
  apply (metis F.distinct(1) F.distinct(5) le_less_linear)
  apply (metis F.distinct(1) F.distinct(5) le_less_linear)
  apply (metis F.distinct(1) F.distinct(5) le_less_linear)
  by(case_tac "tW s \<noteq> T s", simp_all)


lemma when_R_moves_prog_less:
  assumes "con_assms s"
  and "inv (pcW s) (pcR s) s"
  and "cR_step (pcR s) s s'"
shows "lex_prog s s'"
  using assms apply (simp_all add:inv_def cR_step_def progress_lemmas)
  apply(case_tac "pcR s", simp_all add:tries_left_def)
  apply(case_tac[!] "pcW s", simp_all)
                      apply(case_tac[!] "q s=[]", simp_all add: Let_def)
                      apply clarify
oops
  apply(case_tac " T s < fst (hd (q s)) + snd (hd (q s))", simp_all)
  apply(case_tac " T s < fst (hd (q s)) + snd (hd (q s))", simp_all)
  apply (metis (no_types, lifting) add_less_mono diff_less_mono2 diff_self_eq_0 length_greater_0_conv lessI less_le_trans mult_2 nat_add_left_cancel_less nat_less_le)
  apply (metis (no_types, lifting) add_less_mono diff_less_mono2 diff_self_eq_0 length_greater_0_conv lessI less_le_trans mult_2 nat_add_left_cancel_less nat_less_le)
  apply(case_tac " T s < fst (hd (q s)) + snd (hd (q s))", simp_all)
  apply (metis diff_less_mono2 length_greater_0_conv lessI zero_less_diff)
  apply (metis diff_less_mono2 diff_self_eq_0 le_eq_less_or_eq length_0_conv lessI)
  oops




lemma least_prog_R_implies:
  assumes "con_assms s"
  and "inv (pcW s) (pcR s) s"
  and "cR_step (pcR s) s s'"
  and "inv (pcW s) (pcR s) s'"
  and "lex_prog s s'"
shows "end_R_prog s'=True\<longrightarrow>(end_R_prog s \<or> ((\<forall>i.(i<n)\<longrightarrow>ownD s' i=R) \<and> pcR s=Release))\<and>end_W_prog s"
  using assms apply (simp_all add: end_R_prog_def end_W_prog_def tries_left_def cR_step_def inv_def)
  apply(case_tac "pcR s", simp_all)
  by(case_tac "q s=[]", simp_all add:Let_def)


lemma initial_progress:
  assumes  "cR_step (pcR s) s s' \<or> cW_step (pcW s) s s'"
  and "inv (pcW s) (pcR s) s"
  and "init s'"
  and "con_assms s"
shows "lex_prog s s'\<longrightarrow>s=s'"
  using assms apply(simp_all add:cR_step_def cW_step_def init_def progress_lemmas tries_left_def inv_def)
  apply(case_tac "pcR s", simp_all)
  apply(case_tac "pcW s", simp_all)
  apply (metis add.commute add_less_mono diff_less less_le_trans less_nat_zero_code mult.commute mult_2_right nat_le_iff_add order_less_irrefl zero_less_iff_neq_zero)
  apply (metis add.commute add_cancel_right_left add_cancel_right_right add_is_0 diff_less diff_zero le_iff_add length_0_conv length_greater_0_conv less_add_eq_less less_irrefl_nat less_le_trans mult.commute mult_2_right nat_diff_split zero_less_iff_neq_zero)
  apply (metis (no_types, hide_lams) add.commute diff_less le_iff_add le_less_trans less_eq_nat.simps(1) less_le_trans mult.commute mult_2_right order_less_irrefl trans_less_add2)
  apply (metis add.commute add_strict_mono diff_less le_iff_add less_le_trans less_nat_zero_code less_not_refl mult.commute mult_2_right zero_less_iff_neq_zero)
  apply (metis add_is_0 diff_diff_cancel diff_le_self nat_0_less_mult_iff nat_less_le not_le zero_less_diff zero_less_numeral)
  apply (metis add.commute diff_less le0 le_less_trans less_le_trans mult.commute mult_2_right nat_le_iff_add order_less_irrefl trans_less_add2)
  apply (metis add.commute diff_less le_iff_add le_less_trans less_eq_nat.simps(1) less_le_trans less_not_refl mult.commute mult_2_right trans_less_add2)
  apply (metis add.commute diff_less le0 le_less_trans less_le_trans less_not_refl mult.commute mult_2_right nat_le_iff_add trans_less_add1)
  apply (metis add.commute add_cancel_right_right diff_less gr_implies_not0 le0 le_iff_add le_less_trans le_neq_implies_less less_add_eq_less less_le_trans mult.commute mult_2_right order_less_irrefl zero_le)
  apply (metis add_is_0 diff_diff_cancel diff_self_eq_0 nat_0_less_mult_iff nat_less_le zero_less_diff zero_less_numeral)
  apply (metis add.commute diff_less le_iff_add le_less_trans less_le_trans mult.commute mult_2_right order_less_irrefl trans_less_add2 zero_le)
  apply (metis diff_add_zero diff_diff_cancel less_numeral_extra(3) mult_2)
  apply (metis add.commute diff_less le_iff_add less_le_trans mult.commute mult_2_right order_less_irrefl)
  apply (metis add.commute diff_less le_iff_add less_le_trans less_not_refl mult.commute mult_2_right)
  apply (simp add: leD)
  by (simp add: leD)
  



(*--------------------------------------------------------------*)



(*--------------lexicographical progress------------------------------*)
definition "ltpcW i j \<equiv> 
(i \<noteq> j \<and>
(i=FinishedW)
\<or>(i \<in> {Enqueue, OOM, BTS} \<and> j\<noteq>FinishedW)
\<or> (i \<in> {A8, Write} \<and> j \<notin> {Enqueue, OOM, BTS, FinishedW})
\<or> (i \<in> {A6, A7} \<and> j \<in> {idleW, A1, A2, A3, A4, A5})
\<or> (i \<in> {A3, A4, A5} \<and> j \<in> {idleW, A1, A2})
\<or> (i = A2 \<and> j \<in> {idleW, A1})
\<or> (i = A1 \<and> j = idleW)) 
"

definition "ltpcR i j \<equiv> 
i = idleR \<and> j =Release \<or> i=Release \<and> j=Read \<or> i=Read \<and> j=idleR"

definition "state_pv s \<equiv> (2*n - numEnqs s - numDeqs s)"
definition "tries_left s \<equiv> N-tries s"

definition "lex_prog s s' \<equiv> s = s' \<or> 
(state_pv s' < state_pv s 
\<or> (state_pv s' = state_pv s \<and> tries_left s' < tries_left s)
\<or> (state_pv s' = state_pv s \<and> tries_left s' = tries_left s \<and> ltpcR (pcR s') (pcR s)) 
\<or> (state_pv s' = state_pv s \<and> tries_left s' = tries_left s \<and> ltpcW (pcW s') (pcW s)))"

lemmas progress_lemmas = ltpcW_def ltpcR_def state_pv_def lex_prog_def 

definition "end_W_prog s \<equiv> ((n-numEnqs s)=0) \<and> tries_left s=N \<and> pcW s=FinishedW" 
definition "end_R_prog s \<equiv> end_W_prog s\<and> pcR s=idleR \<and> numDeqs s=numEnqs s"
definition "start_state_prog s\<equiv> state_pv s=2*n \<and> pcR s=idleR \<and> pcW s=idleW \<and> tries_left s=N"
*)
(*a
\<and> right_to_addresses s
               \<and> no_ownB s
               \<and> H_T_ownB s
               \<and> Buff_entries_transfer_numDeqs s*)*)*)
*)