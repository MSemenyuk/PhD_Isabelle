theory check_up
imports Main HOL.List
begin 

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
                                  \<and>(length(q s)\<le>c-b)
                                  \<and>(c>b\<longrightarrow>length(q s)>0)
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
  and "k<N"  (*this allows H=T\<noteq>N*)
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
                                  \<and>(length(q s)\<le>(f-e+b-a))
                                  \<and>((f>e\<or>b>a)\<longrightarrow>length(q s)>0)
                                  \<and>(f>e\<longrightarrow>fst(hd(q s)) =e)
                                  \<and>((f=e\<and>b>a)\<longrightarrow>fst(hd(q s)) =a)
                                  \<and>(b>a\<longrightarrow>fst(last(q s))+snd(last(q s)) =b)
                                  \<and>((b=a\<and>f>e)\<longrightarrow>fst(last(q s))+snd(last(q s)) =f)
                                \<comment>\<open>describe ownT using ownB\<close>
                                  \<and>((a>0\<or>e>d)\<longleftrightarrow>ownT s = R)
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




  




lemma sum_of_things:
  "q s!0 = (2,3) \<Longrightarrow> (length(q s) = 1)\<longrightarrow>\<Sum>{j. j=(snd(q s!0))} = 3"
  by simp 

lemma sum_of_things_2:
  "q s=[(0,1)] \<Longrightarrow> length(q s) = 1"
  by simp

lemma sum_of_things_3:
  "length(q s) =2\<Longrightarrow> {i. i<length(q s)} = {0,1}"
  by auto


theorem sum_of_things_4:
  "2 * (\<Sum>i::nat=0..n. i) = n * (n + 1)"
    (is "?P n" is "?S n = _")
 proof (induct n)
   case 0
   then show ?case 
     by (simp add: "0.hyps") 
 next
   case (Suc x)
   then show ?case 
     by (simp add: gauss_sum_nat)
  qed

  
  
lemma sum_of_things_5:
  " length(q s)>0 ==> (\<Sum>i::nat=0..length(q s)-1. 1) = length(q s)"
  by auto 











definition "Q_indices s \<equiv> \<Union> {{i . a \<le> i \<and> i < b} | a b. (a, b) \<in> set(q s)}"

lemma sum_of_things_3:
  "length(q s) =2\<Longrightarrow> \<forall>i.(i<length(q s)) \<longrightarrow> snd(q s!i) = 1 
\<Longrightarrow> (\<Sum> {j. j\<in>{i. (i<length(q s) \<and> i\<ge>1)}} ) = 1"
  apply auto

  sledgehammer
  sorry

















