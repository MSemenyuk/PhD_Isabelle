theory RingBuffer_BD_latest_3
imports Main HOL.List
begin 

(*-------------------------------------------------------------------
      W_step_side                           R_step_side
LOCAL preserves inv    (done)         LOCAL preserves inv    (done)
LOCAL shows preW       (done)         LOCAL shows preR       (done) 
GLOBAL preserves preR  (done)         GLOBAL preserves preW  (done)  
---------------------------------------------------------------------*)


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



definition "case_1_pred a b c d s  \<equiv> 0\<le>a \<and> a\<le>b \<and> b\<le>c \<and> c\<le>d \<and> d\<le>N 
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
"
definition "case_1 s  \<equiv> \<exists>a b c d. case_1_pred a b c d s"

lemmas case_1_lemmas = case_1_def case_1_pred_def

lemma can_a_equal_d:
  assumes "\<forall>i.(i<N)\<longrightarrow>ownB s i=B"
  and "ownT s=Q"
  and "H s=k"
  and "T s=k"
  and "k<N"  
  and "q s=[]"
  and "ownB s N=None"
  shows "case_1 s"
  using assms apply (simp add:case_1_lemmas)
  apply (rule_tac exI [where x ="k"])
  apply (rule_tac exI [where x ="k"])
  apply simp
  apply (rule_tac exI [where x ="k"])
  by simp

definition "case_2_pred a b c d e f s \<equiv>
0\<le>a \<and> a\<le>b \<and> b\<le>c \<and> c<d \<and> d\<le>e \<and> e\<le>f \<and> f\<le>N
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
                                  \<and>(ownT s\<noteq>W)"

definition "case_2 s  \<equiv> \<exists>a b c d e f. case_2_pred a b c d e f s"

lemmas case_2_lemmas = case_2_def case_2_pred_def


lemma case_split:
  shows "H s\<ge>T s\<Longrightarrow> (case_1 s \<or> case_2 s) \<Longrightarrow> case_1 s"
  apply (simp add:case_1_lemmas case_2_lemmas) apply clarify
  by linarith


lemma case_split_2:
  shows "H s\<ge>T s\<Longrightarrow> (case_1 s \<or> case_2 s) \<Longrightarrow>\<not> case_2 s"
  by (simp add:case_1_lemmas case_2_lemmas) 

lemma case_split_3:
  shows "H s<T s\<Longrightarrow> (case_1 s \<or> case_2 s) \<Longrightarrow> case_2 s"
  apply (simp add:case_1_lemmas case_2_lemmas) apply clarify
  by linarith


lemma case_split_4:
  shows "H s<T s\<Longrightarrow> (case_1 s \<or> case_2 s) \<Longrightarrow>\<not> case_1 s"
  by (simp add:case_1_lemmas case_2_lemmas)


lemma case_split_5:
  shows "(case_1 s \<and> case_2 s) \<Longrightarrow>False"
  apply (case_tac "H s\<ge>T s") 
  apply (metis case_split_2)
  using case_split_4 not_le_imp_less by blast







definition  "end x \<equiv> fst x + snd x"

lemmas end_simp [simp] = end_def 

definition "Q_boundness qs \<equiv> 
     \<forall>x. (x \<in> set qs) \<longrightarrow> end x \<le> N" 


definition "Q_offsets_differ qs \<equiv> 
  \<forall>i j. i<length qs \<and> j<length qs \<and> i\<noteq>j \<longrightarrow> fst(qs !i) \<noteq> fst(qs!j) "

definition "Q_gap_structure qs   \<equiv> 
          (\<forall>i. (i < length qs \<and> i > 0) \<longrightarrow>((end( qs!(i-1)) = fst( qs !i))\<or> (fst( qs !i) =0)))"

definition "Q_has_no_uroboros  qs \<equiv>
(\<forall>x. x \<in> set ( qs)\<longrightarrow> fst x \<noteq> end (last ( qs)))"

(*I would call this Q elements ordered *)
definition "Q_has_no_overlaps qs \<equiv>
(\<forall> x y. (x \<in> set qs \<and> y \<in> set qs) \<longrightarrow> (fst(x) < fst(y) \<longrightarrow> end x \<le> fst y))"
(*Q has no overlaps looks like this this *)
definition "pairtoset x \<equiv>
{k | k. fst x \<le> k \<and> k < end x}"

definition "Q_has_no_overlaps_2 qs \<equiv>
(\<forall> x y. x \<in> set qs \<and> y \<in> set qs \<and> x \<noteq> y \<longrightarrow> pairtoset x \<inter> pairtoset y = {})"




definition "Q_elem_size qs       \<equiv> \<forall>x.(x\<in>set(qs))\<longrightarrow>snd(x)>0"

definition "Q_basic_struct qs \<equiv> Q_boundness qs \<and> Q_gap_structure qs \<and> Q_offsets_differ qs
                              \<and> Q_has_no_overlaps qs \<and> Q_has_no_uroboros qs \<and> Q_elem_size qs"


lemmas Q_basic_lemmas = Q_basic_struct_def  Q_has_no_overlaps_def 
                        Q_gap_structure_def Q_has_no_uroboros_def
                        Q_boundness_def     Q_offsets_differ_def
                        Q_elem_size_def

lemma Q_boundness_list:
"Q_boundness qs \<Longrightarrow> \<forall>i.(i<length qs) \<longrightarrow> end(qs !i)\<le>N"
  by (simp add: Q_boundness_def)

lemma proof_no_overlaps2:
"Q_offsets_differ qs \<Longrightarrow> x\<in>set qs \<Longrightarrow> y\<in>set qs \<Longrightarrow> x \<noteq> y \<Longrightarrow> fst(x)\<noteq>fst(y)"
  using  Q_offsets_differ_def 
  by (metis in_set_conv_nth)

lemma proof_no_overlaps:
  assumes "Q_gap_structure (q s)"
  and "Q_offsets_differ (q s)"
  and "Q_has_no_overlaps (q s)"
shows "\<forall>x y.(x\<in>set(q s)\<and>y\<in>set(q s)\<and>fst(x)\<noteq>fst(y))\<longrightarrow>
  (\<forall>j.(fst(x)\<le>j \<and> j<end(x))\<longrightarrow>(j<fst(y)\<or>j\<ge>end(y)))"
  using assms apply (simp add:Q_basic_lemmas) 
  apply safe 
  by (smt (verit, best) bot_nat_0.not_eq_extremum diff_is_0_eq le_trans linorder_neqE_nat zero_less_diff)


lemma tail_preserves_Q_boundness:
  assumes "Q_boundness qs"
shows "Q_boundness (tl qs)"
  using assms  apply (simp add:Q_boundness_def)
  by (metis Nil_tl list.set_sel(2))

lemma tail_preserves_Q_offsets_differ:
  assumes "Q_offsets_differ qs"
shows "Q_offsets_differ (tl qs)"
  using assms  apply (simp add:Q_offsets_differ_def) 
  by (simp add: less_diff_conv nth_tl)

lemma tail_preserves_Q_gap_structure:
  assumes "Q_gap_structure qs"
shows "Q_gap_structure (tl qs)"
  using assms  apply (simp add:Q_gap_structure_def) 
  by (smt (verit) One_nat_def Suc_pred add_diff_cancel_left' length_tl less_Suc_eq less_diff_conv not_less_eq nth_tl plus_1_eq_Suc)

lemma tail_preserves_Q_has_no_uroboros:
  assumes "Q_has_no_uroboros qs"
shows "Q_has_no_uroboros (tl qs)"
  using assms  apply (simp add:Q_has_no_uroboros_def) 
  by (metis last_tl length_pos_if_in_set less_nat_zero_code list.sel(2) list.set_sel(2) list.size(3))

lemma tail_preserves_Q_has_no_overlaps:
  assumes "Q_has_no_overlaps qs"
shows "Q_has_no_overlaps (tl qs)"
  using assms  apply (simp add:Q_has_no_overlaps_def) 
  by (metis list.sel(2) list.set_sel(2))

lemma tail_preserves_Q_elem_size_2:
  assumes "Q_elem_size qs"
shows "Q_elem_size (tl qs)"
  using assms  using Q_elem_size_def 
  by (metis list.sel(2) list.set_sel(2))

lemma tail_preserves_Q_basic_struct:
  assumes "Q_basic_struct qs"
shows "Q_basic_struct (tl qs)"
  using assms  apply (simp add:Q_basic_struct_def)
  by (simp add: tail_preserves_Q_boundness tail_preserves_Q_elem_size_2 tail_preserves_Q_gap_structure tail_preserves_Q_has_no_overlaps tail_preserves_Q_has_no_uroboros tail_preserves_Q_offsets_differ)
  





definition "tempR_bounded tr     \<equiv> end tr\<le>N"
definition "Q_no_overlap_tempR qs tr\<equiv> (\<forall>x. (x \<in> set qs)\<longrightarrow>
                  ((fst tr <fst(x)\<and>end tr\<le> fst(x))
                  \<or>(fst(x)<fst tr\<and>end(x)<fst tr)))"
definition "Q_relates_tempR qs tr   \<equiv> (end tr = fst(hd qs)) \<or> (fst(hd qs) = 0)"
lemmas tmepR_extra_lemmas [simp] = tempR_bounded_def Q_no_overlap_tempR_def Q_relates_tempR_def






definition "Q_holds_bytes s     \<equiv> (\<forall>x.(x\<in>set(q s))\<longrightarrow>(\<forall>j.(fst(x)\<le>j \<and> j<end(x))\<longrightarrow>ownB s j=Q))"
definition "Q_reflects_writes s \<equiv> (\<forall>i.(i<length(q s))\<longrightarrow>data_index s (q s!i) = ((numDeqs s) +i))"

definition "Q_elem_rel s        \<equiv> (\<forall>i.(i<length(q s))\<longrightarrow>snd(q s!i) =Data s ((numDeqs s) +i))"

definition "Q_reflects_ownD s   \<equiv> (\<forall>i.(i<length(q s))\<longrightarrow>ownD s (i+(numDeqs s)) =B)"


lemma Q_holds_bytes_index: 
"Q_holds_bytes s \<Longrightarrow> i<length(q s) \<Longrightarrow>fst(q s!i)\<le>j \<Longrightarrow> j<end(q s!i) \<Longrightarrow>ownB s j=Q"
  using Q_holds_bytes_def nth_mem by blast



lemma tail_preserves_Q_holds_bytes:
  assumes "Q_holds_bytes s"
  and "x\<in>set(tl(q s))"
  and "fst(x)\<le>j" "j<end(x)"
shows "ownB s j=Q"
  using assms  apply (simp add:Q_holds_bytes_def) 
  apply(case_tac "tl(q s)\<noteq>[]") prefer 2
  apply force
  by (metis list.sel(2) list.set_sel(2) prod.collapse)

lemma tail_preserves_Q_reflects_writes:
  assumes "Q_reflects_writes s"
  and "i<length(tl(q s))"
shows "data_index s ((tl(q s))!i) = ((numDeqs s) +i +1)"
  using assms  apply (simp add:Q_reflects_writes_def)
  by (simp add: nth_tl)

lemma tail_preserves_Q_elem_size:
  assumes "Q_elem_rel s"
  and "i<length(tl(q s))"
shows "snd(tl(q s)!i) =Data s ((numDeqs s) +i +1)"
  using assms  apply (simp add:Q_elem_size_def)
  by (simp add: Q_elem_rel_def nth_tl)

lemma tail_preserves_Q_reflects_ownD:
  assumes "Q_reflects_ownD s"
  and "i<length(tl(q s))"
shows "ownD s (i+(numDeqs s) +1) =B"
  using assms  apply (simp add:Q_reflects_ownD_def) 
  by (metis One_nat_def Suc_eq_plus1 add.assoc less_diff_conv plus_1_eq_Suc)

lemma Q_head_relates_tail:
  assumes "Q_offsets_differ qs"
  and "i<length(tl qs)"
  shows "fst(qs!0)\<noteq> fst((tl qs)!i)"
  using assms apply (simp add:Q_offsets_differ_def)
  by (metis One_nat_def Suc_pred length_tl less_Suc_eq_0_disj not_less_eq nth_tl zero_less_diff)
  
lemma Q_hd_zero_implies_structure:
  assumes "Q_offsets_differ qs "
  and "Q_gap_structure qs"
  and "fst(hd qs) =0"
  and "i<length(qs)" "i>0"
shows "end(qs!(i-1)) =fst(qs!i)"
  using assms apply(simp add:Q_basic_lemmas) 
  by (metis drop0 hd_drop_conv_nth less_Suc_eq_0_disj less_imp_Suc_add not_gr_zero)

lemma data_index_preserved_lemma:
  assumes "Q_reflects_writes s"
  and "length(q s)>0"
  shows "data_index s(q s!0) = numDeqs s"
  using assms by (simp add:Q_reflects_writes_def)

definition "Q_structure s \<equiv> Q_basic_struct (q s) \<and> 
                                      \<comment> \<open>Q_holds_bytes s \<and>\<close>
                                      Q_reflects_writes s \<and> 
                                      Q_elem_rel s \<and> 
                                      Q_reflects_ownD s"

lemma Q_structure_nempty:
  "q s=[] \<Longrightarrow> Q_structure s"
  by (simp add: Q_basic_struct_def Q_boundness_def Q_elem_rel_def Q_elem_size_def Q_gap_structure_def Q_has_no_overlaps_def Q_has_no_uroboros_def Q_offsets_differ_def Q_reflects_ownD_def Q_reflects_writes_def Q_structure_def)



lemmas Q_lemmas = Q_holds_bytes_def Q_reflects_writes_def Q_reflects_ownD_def
                  Q_structure_def Q_relates_tempR_def Q_elem_rel_def
                  Q_elem_size_def Q_no_overlap_tempR_def



lemma head_q0:
  assumes "length qs>0"
  shows "hd qs = (qs!0)"
  using assms apply (simp add:Q_reflects_writes_def)
  by (simp add: hd_conv_nth)



lemma Q_gap_lemmas_4:
  assumes "Q_structure s"
  and "x\<in>set(q s)" "y\<in>set(q s)" "fst(y)>fst(x)"
  shows "end(y)>fst(x)"
  using assms by (simp add:con_assms_def Q_lemmas Q_basic_lemmas)


lemma Q_gap_lemmas_15:
  assumes "Q_structure s" 
  and "x\<in>set(q s)" "y\<in>set(q s)" "end(y)>end(x)"
  shows "fst(y)\<noteq>fst(x)"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (metis fst_conv in_set_conv_nth nat_neq_iff old.prod.inject)

lemma Q_gap_lemmas_14:
  assumes "Q_structure s"
  and "x\<in>set(q s)" "y\<in>set(q s)" "end(y)>end(x)" 
shows "fst(y)\<ge>end(x)"
proof - 
  from assms Q_gap_lemmas_15 have c1: "fst(y)\<noteq>fst(x)"
    by blast
  from this assms show ?thesis apply simp 
    apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas) 
    by (metis (mono_tags, lifting) leD not_less_iff_gr_or_eq prod.collapse trans_le_add1)
qed










lemma Q_gap_lemmas_1_list:
  assumes "Q_structure s"
  and "i<length(q s)" "j<length(q s)" "i\<noteq>j"
shows "fst(q s!i) \<noteq> fst(q s!j)"
  using assms by (simp add:con_assms_def Q_lemmas Q_basic_lemmas) 

lemma Q_gap_lemmas_2:
  assumes "Q_structure s"
  and "length(q s) >0"
  shows "\<forall>i.(i<length(q s))\<longrightarrow>(q s!i)\<in>set(q s)"
  using assms by (simp add:con_assms_def)


lemma Q_gap_lemmas_2_list:
  assumes "Q_structure s"
  and "i<length(q s)" "j<length(q s)" "fst(q s!i)>fst(q s!j)"
shows "end(q s!i)>fst(q s!j)"
  using assms by (simp add:con_assms_def Q_lemmas Q_basic_lemmas) 



lemma Q_gap_lemmas_4_list:
  assumes "Q_structure s"
  and "i<length(q s)" "j<length(q s)" "fst(q s!i)>fst(q s!j)"
shows "fst(q s!i)\<ge>end(q s!j)"
  using assms apply (simp add:con_assms_def Q_lemmas Q_basic_lemmas)
  by (metis nth_mem prod.collapse)




(*tempR used to be part of Q so:.....*)

 definition "tempR_boundness tr \<equiv> (end (tr) \<le> N)" 

definition "tempR_offsets_differ qs tr \<equiv> (\<forall>i.(i<length(qs))\<longrightarrow>(fst(qs!i)\<noteq>fst(tr)))"

definition "tempR_gap_structure qs tr  \<equiv> (end(tr) = fst(hd(qs)))\<or> (fst(hd(qs)) =0)"

definition "tempR_has_no_uroboros qs tr \<equiv> (fst (tr) \<noteq> end (last (qs)))"

definition "tempR_has_no_overlaps qs tr \<equiv>(\<forall>i.(i<length(qs))\<longrightarrow>((fst(tr)<fst(qs!i)\<longrightarrow>end(tr)\<le>fst(qs!i))
                                                           \<and>(fst(tr)>fst(qs!i)\<longrightarrow>end(qs!i)\<le>fst(tr))))"

definition "tempR_basic_struct qs tr \<equiv> tempR_boundness tr \<and> (qs\<noteq>[]\<longrightarrow> (tempR_gap_structure qs tr \<and> tempR_offsets_differ qs tr
                              \<and> tempR_has_no_overlaps qs tr \<and> tempR_has_no_uroboros qs tr)) "


lemmas tempR_basic_lemmas = tempR_basic_struct_def  tempR_has_no_overlaps_def 
                            tempR_gap_structure_def tempR_has_no_uroboros_def
                            tempR_boundness_def     tempR_offsets_differ_def


definition "tempR_holds_bytes s     \<equiv> (\<forall>j.(fst(tempR s)\<le>j \<and> j<end(tempR s))\<longrightarrow>ownB s j=R)"

definition "tempR_reflects_writes s \<equiv> (data_index s (tempR s) = ((numDeqs s) -1))"

definition "tempR_elem_size s       \<equiv> (snd(tempR s) =Data s ((numDeqs s) -1))"


definition "tempR_structure s \<equiv>(tempR_basic_struct (q s) (tempR s) \<and> 
                                      tempR_holds_bytes s \<and> tempR_reflects_writes s \<and> tempR_elem_size s)"


lemmas tempR_lemmas = tempR_holds_bytes_def tempR_reflects_writes_def 
                      tempR_elem_size_def   tempR_structure_def
                      


(*tempW will be part of Q so:.....*)
definition "tempW s \<equiv> (offset s, Data s (numEnqs s))"

 definition "tempW_boundness tw \<equiv> (end ( tw) \<le> N)" 

definition "tempW_offsets_differ qs tw \<equiv> (\<forall>i.(i<length(qs))\<longrightarrow>(fst(qs!i)\<noteq>fst(tw)))"

definition "tempW_gap_structure qs tw  \<equiv> (fst(tw) = end(last(qs)))\<or> (fst(tw) =0)"

definition "tempW_has_no_uroboros qs tw \<equiv> (end((tw)) \<noteq> fst (hd (qs)))"

definition "tempW_has_no_overlaps qs tw \<equiv>(\<forall>i.(i<length(qs))\<longrightarrow>((fst(tw)<fst(qs!i)\<longrightarrow>end(tw)<fst(qs!i))
                                                           \<and>(fst(tw)>fst(qs!i)\<longrightarrow>end(qs!i)\<le>fst(tw))))"

definition "tempW_basic_struct qs tw \<equiv> tempW_boundness tw \<and> (qs\<noteq>[]\<longrightarrow> (tempW_gap_structure qs tw \<and> tempW_offsets_differ qs tw
                              \<and> tempW_has_no_overlaps qs tw \<and> tempW_has_no_uroboros qs tw))"


lemmas tempW_basic_lemmas = tempW_basic_struct_def  tempW_has_no_overlaps_def 
                            tempW_gap_structure_def tempW_has_no_uroboros_def
                            tempW_boundness_def     tempW_offsets_differ_def
                            tempW_def


definition "tempW_holds_bytes s     \<equiv> (\<forall>j.(fst(tempW s)\<le>j \<and> j<end(tempW s))\<longrightarrow>ownB s j=W)"

definition "tempW_reflects_writes s \<equiv> (data_index s (offset s, Data s (numEnqs s)) = numEnqs s)"

definition "tempW_structure s \<equiv>(tempW_basic_struct (q s) (tempW s) \<and> 
                                      tempW_holds_bytes s )"


lemmas tempW_lemmas = tempW_holds_bytes_def tempW_reflects_writes_def 
                      tempW_structure_def













(*Writer Thread Behaviour*)

definition "B_acquire s s' \<equiv> s' = (`pcW := A1) s"

definition "trans_A3 s = ((`T := 0) \<circ> (`H := (Data s (numEnqs s))) 
                        \<circ> (`offset := 0) \<circ> (`pcW := Write) 
                        \<circ> setownB [(0,(Data s (numEnqs s))) W]) s"

definition "trans_A4 s = ((`H := ((hW s) + (Data s (numEnqs s)))) \<circ> (`offset := (hW s)) \<circ> (`pcW := Write)
                        \<circ> setownB [(hW s,hW s+Data s (numEnqs s)) W]) s"

definition "trans_A6 s = ((`H := ((hW s) + (Data s (numEnqs s)))) \<circ> (`offset := (hW s)) \<circ> (`pcW := Write)
                        \<circ> setownB [(hW s,hW s+Data s (numEnqs s)) W]) s"

definition "trans_A7 s = ((`H := (Data s (numEnqs s))) \<circ> (`offset := 0) 
                        \<circ> (`pcW := Write) \<circ> (setownB [(hW s,N) D])
                        \<circ> (setownB [(0,Data s (numEnqs s)) W])) s"

fun rbW_step :: "PCW \<Rightarrow> rb_state \<Rightarrow> rb_state" where
  "rbW_step A1 s = ((`hW := (H s)) \<circ> (`tW := (T s)) \<circ> (`pcW := A2)) s "
| "rbW_step A2 s = (if grd1 s then ((`pcW := A3) \<circ> (transownT [Q W s]))
                     else if grd2 s then (`pcW := A4) 
                     else if grd3 s then (`pcW := A5) 
                     else (`pcW :=A8)) s"
| "rbW_step A3 s = trans_A3 s" 
| "rbW_step A4 s = trans_A4 s"
| "rbW_step A5 s = (if grd4 s then (`pcW := A6)  
                     else if grd5 s then (`pcW := A7)
                     else (`pcW := A8)) s"
| "rbW_step A6 s = trans_A6 s"
| "rbW_step A7 s = trans_A7 s"
| "rbW_step A8 s = (if ((Data s (numEnqs s))>N) then ERRBTS s
                        else (ERROOM \<circ> (`tW := (T s))) s)"

| "rbW_step Write s = s"
| "rbW_step Enqueue s = s"| "rbW_step idleW s = s" | "rbW_step FinishedW s = s"| "rbW_step BTS s = s"| "rbW_step OOM s = s"



definition "Q_enqueue s s' \<equiv> s' = (`q:=(append (q s) [(offset s,Data s (numEnqs s))])
                     \<circ> `pcW := idleW
                     \<circ>  transownB [W Q]
                     \<circ> `numEnqs := (numEnqs s + 1)
                     \<circ>  transownT [W Q s]) s"

definition "B_write s s' \<equiv> s' = ((`B.write ((offset s), (Data s (numEnqs s))):= (numEnqs s))
                     \<circ> (transownD [(numWrites s) B]) 
                     \<circ> `pcW := Enqueue 
                     \<circ> (`numWrites := ((numWrites s )+1))) s"

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
  and "Q_dequeue s s'"
  shows "Q_structure s'"
  using assms apply(simp add:Q_structure_def pre_dequeue_inv_def split:if_splits)
  apply(simp add:Q_reflects_writes_def Q_reflects_ownD_def Q_elem_rel_def) 
  apply (smt (verit, del_insts) One_nat_def Q_structure_def add.assoc add.commute assms(1) length_tl less_diff_conv plus_1_eq_Suc tail_preserves_Q_basic_struct tail_preserves_Q_elem_size tail_preserves_Q_reflects_writes)
  by(simp add:Q_reflects_writes_def Q_reflects_ownD_def Q_elem_rel_def) 

lemma Q_structure_preserved2:
  assumes "Q_structure s"
  and "pre_Read_inv s"
  and "B_read s s'"
  shows "Q_structure s'"
  using assms apply(simp add:Q_structure_def)
  by(simp_all add:Q_reflects_writes_def Q_elem_rel_def Q_reflects_ownD_def pre_Read_inv_def) 

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
  by(simp add:pre_Release_inv_def Q_reflects_writes_def Q_elem_rel_def Q_reflects_ownD_def)

  








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

definition "data_index_bouded s \<equiv> \<forall>i. (i\<le>N)\<longrightarrow>(\<forall>j.(j\<le>N)\<longrightarrow>data_index s (i,j)<n)"

lemmas invariant_lemmas [simp] = con_assms_def mainInv_def
                          counter_q_rel_def 
                          counter_bounds_def data_index_bouded_def
                          
definition "ran_indices a b \<equiv> {i . a \<le> i \<and> i < b}"

definition "Q_indices qs \<equiv> \<Union> {ran_indices a (a + b) | a b. (a, b) \<in> set qs}"

definition "Q_owns_bytes s \<equiv> \<forall>i.(i\<in>Q_indices (q s))\<longleftrightarrow>(i\<le>N \<and> ownB s i=Q)"

lemma Q_ind_imp_tail_ind_1:
  "tl qs \<noteq> [] \<Longrightarrow> hd qs = qs!0"
  apply (simp add:hd_def) 
  by (metis Nil_tl hd_conv_nth hd_def)

lemma ran_indices_lem:
  "Q_basic_struct qs \<Longrightarrow> 
    i<length qs \<Longrightarrow> fst(qs!i) \<in> ran_indices (fst(qs ! i)) (end (qs!i))"
  apply (simp add: Q_lemmas Q_basic_lemmas ran_indices_def)
  by (metis nth_mem prod.collapse)


lemma ran_indices_lem5:
  "Q_basic_struct qs \<Longrightarrow> i<length qs \<Longrightarrow> fst(qs!i)\<in>Q_indices qs"
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  by (metis (full_types) end_simp nth_mem prod.collapse ran_indices_def ran_indices_lem)











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


(*******************************************************************)


















(**********************Supporting lemmas for LOCAL W transitions*********************************)


lemma case_trans_A2_to_A3_2:
  shows "s'=(s\<lparr>ownT := W, pcW := A3\<rparr>) \<Longrightarrow> T s=H s\<Longrightarrow> case_1 s 
            \<Longrightarrow> case_1 s'"
  apply (simp add:case_1_lemmas cW_step_def)
  apply clarify 
  by (smt (z3) diff_is_0_eq le_trans less_irrefl_nat zero_less_diff)


lemma case_trans_A2_to_A4_1:
  shows "s'=(s\<lparr>pcW := A4\<rparr>) \<Longrightarrow> case_1 s 
            \<Longrightarrow> (i\<le>N)\<longrightarrow>ownB s' i = ownB s i"
  by (simp add:case_1_lemmas cW_step_def)

lemma case_trans_A2_to_A4_2:
  shows "s'=(s\<lparr>pcW := A4\<rparr>) \<Longrightarrow> case_1 s 
            \<Longrightarrow> case_1 s'"
  by (simp add:case_1_lemmas cW_step_def)

lemma case_trans_A2_to_A4_3:
  shows "s'=(s\<lparr>pcW := A4\<rparr>) \<Longrightarrow> case_2 s \<Longrightarrow> T s>H s
            \<Longrightarrow> case_2 s'"
  by (simp add:case_2_lemmas cW_step_def)

lemma case_trans_A2_to_A5_1:
  shows "s'=(s\<lparr>pcW := A5\<rparr>) \<Longrightarrow> case_1 s 
            \<Longrightarrow> (i\<le>N)\<longrightarrow>ownB s' i = ownB s i"
  by (simp add:case_1_lemmas cW_step_def)

lemma case_trans_A2_to_A5_2:
  shows "s'=(s\<lparr>pcW := A5\<rparr>) \<Longrightarrow> case_1 s 
            \<Longrightarrow> case_1 s'"
  by (simp add:case_1_lemmas cW_step_def)

lemma case_trans_A2_to_A5_3:
  shows "s'=(s\<lparr>pcW := A5\<rparr>) \<Longrightarrow> case_2 s \<Longrightarrow> T s\<le>H s
            \<Longrightarrow> case_2 s'"
  by (simp add:case_2_lemmas cW_step_def)

lemma case_trans_A2_to_A8_1:
  shows "s'=(s\<lparr>pcW := A8\<rparr>) \<Longrightarrow> case_1 s 
            \<Longrightarrow> (i\<le>N)\<longrightarrow>ownB s' i = ownB s i"
  by (simp add:case_1_lemmas cW_step_def)


lemma case_trans_A2_to_A8_2:
  shows "s'=(s\<lparr>pcW := A8\<rparr>) \<Longrightarrow> case_1 s 
            \<Longrightarrow> case_1 s'"
  by (simp add:case_1_lemmas cW_step_def)

lemma case_trans_A2_to_A8_3:
  shows "s'=(s\<lparr>pcW := A8\<rparr>) \<Longrightarrow> case_2 s \<Longrightarrow> T s\<le>H s
            \<Longrightarrow> case_2 s'"
  by (simp add:case_2_lemmas cW_step_def)

lemma case_trans_A2_to_A8_4:
  shows "s'=(s\<lparr>pcW := A8\<rparr>) \<Longrightarrow> case_2 s \<Longrightarrow> T s>H s
            \<Longrightarrow> case_2 s'"
  by (simp add:case_2_lemmas cW_step_def)

lemma case_trans_A3_1:
  shows "pre_A3_inv s \<Longrightarrow> case_2 s \<Longrightarrow> False"
  by (simp add:case_2_lemmas pre_A3_inv_def)

lemma case_trans_A3_2:
  shows "pre_A3_inv s \<Longrightarrow>con_assms s\<Longrightarrow>inv s\<Longrightarrow> case_1 s"
  apply (simp add:pre_A3_inv_def con_assms_def basic_pointer_movement_def inv_def)
  apply(subgoal_tac "H s=T s") prefer 2
  apply simp apply clarify 
  apply(subgoal_tac "\<not>case_2 s") prefer 2
  apply (metis case_split_2 less_or_eq_imp_le)
  by blast




lemma case_trans_A3_to_write_1:
  shows "pre_A3_inv s \<Longrightarrow> s' = trans_A3 s \<Longrightarrow> inv s\<Longrightarrow> H s'\<ge>T s'"
  by (simp add:pre_A3_inv_def trans_A3_def inv_def)

lemma case_trans_A3_to_write_2:
  shows "pre_A3_inv s \<Longrightarrow> s' = trans_A3 s \<Longrightarrow> inv s\<Longrightarrow> \<not>case_2 s'"
  by (simp add:pre_A3_inv_def inv_def case_2_pred_def trans_A3_def case_2_lemmas)

lemma case_trans_A3_to_write_3:
  shows "s' = trans_A3 s \<Longrightarrow> 
         i\<ge>T s' \<Longrightarrow> i<H s' \<Longrightarrow> ownB s' i=W"
  by (simp add:pre_A3_inv_def inv_def trans_A3_def case_1_lemmas)

lemma case_trans_A3_to_write_4:
  shows "pre_A3_inv s \<Longrightarrow> s' = trans_A3 s \<Longrightarrow> i\<ge>H s' \<Longrightarrow> i<N  \<Longrightarrow> ownB s' i=B"
  by (simp add:pre_A3_inv_def inv_def trans_A3_def case_1_lemmas)

lemma case_trans_A3_to_write_7:
  shows "pre_A3_inv s \<Longrightarrow> s' = trans_A3 s \<Longrightarrow> inv s\<Longrightarrow> con_assms s\<Longrightarrow> case_1 s'"
  apply (simp add:pre_A3_inv_def inv_def trans_A3_def case_1_lemmas) 
  apply (rule_tac exI [where x ="0"]) 
  apply (rule_tac exI [where x ="0"]) apply simp  
  by (metis case_split_2 less_or_eq_imp_le)



lemma case_trans_A4_1:
  shows "pre_A4_inv s \<Longrightarrow> T s\<ge>tW s\<Longrightarrow> case_1 s \<Longrightarrow> False"
  apply (simp add:case_1_lemmas pre_A4_inv_def)
  by (metis diff_is_0_eq le_trans less_nat_zero_code)

lemma case_trans_A4_2:
  shows "pre_A4_inv s \<Longrightarrow> T s\<le>hW s\<Longrightarrow> case_2 s \<Longrightarrow> False"
  apply (simp add:case_2_lemmas pre_A4_inv_def) 
  by (metis le_antisym less_irrefl_nat less_or_eq_imp_le)

lemma case_trans_A4_3:
  shows "pre_A4_inv s \<Longrightarrow> T s>hW s \<Longrightarrow> T s<tW s  \<Longrightarrow> False"
  by (simp add:case_2_lemmas pre_A4_inv_def) 

lemma case_trans_A4_4:
  shows "pre_A4_inv s \<Longrightarrow> inv s\<Longrightarrow> T s\<ge>tW s \<Longrightarrow> case_2 s"
  using RingBuffer_BD_latest_3.inv_def case_trans_A4_1 by blast

lemma case_trans_A4_5:
  shows "pre_A4_inv s \<Longrightarrow> inv s\<Longrightarrow> T s\<le>hW s\<Longrightarrow> case_1 s"
  apply (simp add: pre_A4_inv_def inv_def) using case_trans_A4_2 [where s=s]
  by (metis RingBuffer_BD_latest_3.case_split)




lemma case_trans_A4_to_write_3:
  shows "s' = trans_A4 s \<Longrightarrow>  hW s \<le>i \<Longrightarrow> i<H s' \<Longrightarrow> W=ownB s' i"
  by (simp add:case_2_lemmas pre_A4_inv_def inv_def trans_A4_def) 



lemma case_trans_A4_to_write_7:
  assumes a1: "pre_A4_inv s" and 
          a2: "T s\<ge>tW s" and 
          a3: "s' = trans_A4 s " and 
          a4: "con_assms s" and 
          a5: "inv s"
  shows "case_2 s'"
proof - 
  have c0: "H s<H s'" using a1 a3 a4 by (simp add: pre_A4_inv_def trans_A4_def) 
  have c1: "H s'<T s'" 
    using a1 a2 a3 unfolding pre_A4_inv_def trans_A4_def 
    using less_diff_conv less_le_trans by auto  
  have c2: "T s=T s'"  using a3 by (simp add: trans_A4_def) 
  have c3: "q s=q s'"  using a3 by (simp add: trans_A4_def) 
  have c4: "ownT s=ownT s'" using a3 by (simp add: trans_A4_def) 
  have c5: "Data s (numEnqs s) = Data s' (numEnqs s')"  using a3 by (simp add: trans_A4_def) 
  have c6: "H s'-H s=Data s (numEnqs s)"  using a1 a3 by (simp add: pre_A4_inv_def trans_A4_def)
  have c7: "offset s'=hW s" using a3 by (simp add: trans_A4_def) 
  have c8: "tempR s = tempR s'"  using a3 by (simp add: trans_A4_def) 
  have c9: "\<forall> i. i\<ge>H s' \<longrightarrow> ownB s i=ownB s' i" using a3 by (simp add: trans_A4_def) 
  have c10: "\<forall> i. i<offset s' \<longrightarrow> ownB s i=ownB s' i" using a3 by (simp add: trans_A4_def)     
  have "case_2 s"  by (simp add: a1 a2 a5 case_trans_A4_4)
  from this show ?thesis
    apply (simp add: case_2_def) apply clarify 
  proof - 
    fix a b c d e f
    assume ea: "case_2_pred a b c d e f s" 
      from ea have "\<forall> i. 0 \<le> i \<and> i < a \<longrightarrow> ownB s i = R" unfolding case_2_pred_def by metis
      from this a1 a3 c7 have ea1: "\<And>i. 0 \<le> i \<and> i < a \<longrightarrow> ownB s' i = R" 
        unfolding case_2_pred_def pre_A4_inv_def 
        by (metis F.distinct(13) c10 gr_implies_not0 grd2_def leI le_less_trans less_or_eq_imp_le)
      from ea a1 a3 c7 have ea2: "\<And>i. a \<le> i \<and> i < b \<longrightarrow> ownB s' i = Q"
        unfolding case_2_pred_def pre_A4_inv_def 
        by (metis c10 less_le_trans)      
      from ea a1 a3 c7 c10 have ea3: "\<And>i. b \<le> i \<and> i < H s' \<longrightarrow> ownB s' i = W"
        unfolding case_2_pred_def pre_A4_inv_def 
        by (metis case_trans_A4_to_write_3 leI)
      from ea a1 c7 have ea4: "offset s' = b"
        unfolding case_2_pred_def pre_A4_inv_def 
        by (metis le_neq_implies_less le_trans less_imp_le order_refl)
      from ea a1 c5 c6 have ea5: "Data s' (numEnqs s') = H s' - b"
        unfolding case_2_pred_def pre_A4_inv_def 
        by (metis c7 ea4)        
      show "\<exists>a b c d e f. case_2_pred a b c d e f s'"
    using ea apply(rule_tac ?x = "a" in exI)
    apply(rule_tac ?x = "b" in exI)
    apply(rule_tac exI [where x ="H s'"])
    apply(rule_tac exI [where x ="T s'"])
    apply(rule_tac ?x = "e" in exI)
    apply(rule_tac ?x = "f" in exI) 
    unfolding case_2_pred_def 
    using c0 c1 c2 c3 c4  c8 c9 ea1 ea2 ea3 ea4 ea5 
    by (smt (z3) le_eq_less_or_eq le_less_trans)
qed 
qed




lemma case_trans_A4_to_write_8:
  shows "pre_A4_inv s \<Longrightarrow> T s\<le>H s  \<Longrightarrow> con_assms s \<Longrightarrow> inv s \<Longrightarrow>
    case_1 s"
  using case_trans_A4_5 [where s=s] apply (simp add:case_1_lemmas)
  by (simp add: pre_A4_inv_def)


lemma case_trans_A4_to_write_9:
  assumes a1: "pre_A4_inv s" and 
          a2: "T s\<le>H s " and 
          a3: "s' = trans_A4 s " and 
          a4: "con_assms s" and 
          a5: "inv s"
        shows "case_1 s'"
proof - 
  have c0: "H s<H s'" using a1 a3 a4 by (simp add: pre_A4_inv_def trans_A4_def) 
  have c1: "T s=T s'"  using a3 by (simp add: trans_A4_def) 
  have c2: "T s'\<le>H s" 
  using a1 a2 a3 c1 unfolding pre_A4_inv_def trans_A4_def 
  using less_diff_conv less_le_trans by linarith 
  have c3: "q s=q s'"  using a3 by (simp add: trans_A4_def) 
  have c4: "ownT s=ownT s'" using a3 by (simp add: trans_A4_def) 
  have c5: "Data s (numEnqs s) = Data s' (numEnqs s')"  using a3 by (simp add: trans_A4_def) 
  have c6: "H s'-H s=Data s (numEnqs s)"  using a1 a3 by (simp add: pre_A4_inv_def trans_A4_def)
  have c7: "offset s'=hW s" using a3 by (simp add: trans_A4_def) 
  have c8: "tempR s = tempR s'"  using a3 by (simp add: trans_A4_def) 
  have c9: "\<forall> i. i\<ge>H s' \<longrightarrow> ownB s i=ownB s' i" using a3 by (simp add: trans_A4_def) 
  have c10: "\<forall> i. i<offset s' \<longrightarrow> ownB s i=ownB s' i" using a3 by (simp add: trans_A4_def) 
  have "case_1 s"  
    using a1 a2 a4 a5 case_trans_A4_to_write_8 by blast
  from this show ?thesis 
    apply (simp add: case_1_def) apply clarify 
  proof-
    fix a b c d
    assume ea: "case_1_pred a b c d s"
    from ea have ea1: "\<And>i.  0 \<le> i \<and> i < T s \<longrightarrow> ownB s i = B" unfolding case_1_pred_def by metis 
    from ea a1 c7 have ea4: "offset s' = c"
        unfolding case_1_pred_def pre_A4_inv_def 
        by (metis le_refl le_trans nat_less_le)
    from this a1 a3 c7 ea1 have ea2: "\<And>i. 0 \<le> i \<and> i < T s' \<longrightarrow> ownB s' i = B" 
        unfolding case_1_pred_def pre_A4_inv_def 
        by (metis c1 c10 c2 less_le_trans)
     from ea have ea3: "\<And>i.  a \<le> i \<and> i < b \<longrightarrow> ownB s i = R" unfolding case_1_pred_def 
       by presburger
    from this a1 a3 c7 ea3 have ea4: "\<And>i. a \<le> i \<and> i < b \<longrightarrow> ownB s' i = R" 
        unfolding case_1_pred_def pre_A4_inv_def 
        by (smt (verit) F.distinct(13) c10 c6 c9 dual_order.strict_trans1 grd2_def less_diff_iff not_less not_less_iff_gr_or_eq)
     from ea have ea5: "\<And>i.  b \<le> i \<and> i < c \<longrightarrow> ownB s i = Q" unfolding case_1_pred_def 
       by presburger
     from this a1 a3 c7 ea5 have ea6: "\<And>i. b \<le> i \<and> i < c \<longrightarrow> ownB s' i = Q" 
        unfolding case_1_pred_def pre_A4_inv_def 
        by (smt (verit) F.distinct(19) c10 c6 c9 dual_order.strict_trans1 grd2_def leI less_diff_iff not_less_iff_gr_or_eq)
     from ea have ea7: "\<And>i.  c \<le> i \<and> i < H s \<longrightarrow> ownB s i = W" unfolding case_1_pred_def 
       by presburger
     from this a1 a3 c7 ea7 have ea8: "\<And>i. c \<le> i \<and> i < H s' \<longrightarrow> ownB s' i = W" 
        unfolding case_1_pred_def pre_A4_inv_def 
        using case_trans_A4_to_write_3 
        by (metis c10 leI) 

    show "\<exists>a b c d. case_1_pred a b c d s'"
    using ea apply(rule_tac ?x = "T s'" in exI)
    apply(rule_tac ?x = "b" in exI)
    apply(rule_tac exI [where x ="c"])
    apply(rule_tac exI [where x ="H s'"])
    unfolding case_1_pred_def 
    apply (intro conjI impI; elim conjE)
    apply blast
    apply (simp add: c1) 
    apply fastforce
    apply (metis c0 less_le less_trans)
    defer 
    using ea2 apply blast
    using c1 ea4 apply presburger
    using ea6 apply fastforce
    using ea8 apply fastforce
    apply (metis c0 c9 le_trans less_le)
    apply (smt (verit, best) F.distinct(27) a1 c6 c9 grd2_def leI le_add_diff_inverse2 less_diff_conv less_trans pre_A4_inv_def)
    apply meson
    apply blast
    apply (smt (verit) a1 c7 less_le_trans order.order_iff_strict pre_A4_inv_def)
    apply (smt (verit, best) a1 c5 c6 le_trans not_less not_less_iff_gr_or_eq pre_A4_inv_def)
    apply (metis c1 c8 c3 c4)+
    apply (smt (verit, best) a1 c4 pre_A4_inv_def)
    by (smt (z3) F.distinct(27) a1 c6 grd2_def le_add_diff_inverse2 le_less_trans less_diff_conv nat_le_linear pre_A4_inv_def)
qed 
qed


lemma case_trans_A5_1:
  shows "pre_A5_inv s \<Longrightarrow> inv s\<Longrightarrow> case_1 s"
  apply (simp add: pre_A5_inv_def inv_def)
  by (metis RingBuffer_BD_latest_3.case_split) 



lemma case_trans_A5_to_A6_2:
  shows " s'=(s\<lparr>pcW := A6\<rparr>)  \<Longrightarrow> 
    case_1 s' = case_1 s"
  by(simp add:case_1_lemmas)

lemma case_trans_A5_to_A6_3:
  shows "pre_A5_inv s  \<Longrightarrow> s'=(s\<lparr>pcW := A6\<rparr>)  \<Longrightarrow> inv s \<Longrightarrow>
    case_1 s'"
  using case_trans_A5_1 
  using case_trans_A5_to_A6_2 by blast 



lemma case_trans_A5_to_A6_5:
  shows "s'=(s\<lparr>pcW := A7\<rparr>) \<Longrightarrow>
    case_1 s' = case_1 s"
  by(simp add:case_1_lemmas)

lemma case_trans_A5_to_A6_6:
  shows "pre_A5_inv s  \<Longrightarrow> s'=(s\<lparr>pcW := A7\<rparr>) \<Longrightarrow>con_assms s \<Longrightarrow> inv s \<Longrightarrow>
    case_1 s'"
  using case_trans_A5_to_A6_5 [where s=s and s'=s']
  using case_trans_A5_1 by blast


(*
lemma case_trans_A5_to_A6_7:
  shows "s'=(s\<lparr>pcW := A8\<rparr>)   \<Longrightarrow>
    i\<le>N \<Longrightarrow> ownB s i=ownB s' i"
  by(simp add:case_1_lemmas pre_A5_inv_def inv_def)
*)


lemma case_trans_A5_to_A6_9:
  shows "pre_A5_inv s  \<Longrightarrow> s'=(s\<lparr>pcW := A8\<rparr>) \<Longrightarrow>con_assms s \<Longrightarrow> inv s \<Longrightarrow>
    case_1 s'"
  by (metis case_trans_A2_to_A8_2 case_trans_A5_1)


lemma case_trans_A6_2:
  shows "pre_A6_inv s \<Longrightarrow> inv s\<Longrightarrow> case_2 s \<Longrightarrow> False"
  apply (simp add: pre_A6_inv_def inv_def)
  by (metis case_split_2)


(*
lemma case_trans_A6_to_write_1:
  shows "pre_A6_inv s \<Longrightarrow> s' = s
    \<lparr>ownB := \<lambda>i. if hW s \<le> i \<and> i < hW s + Data s (numEnqs s) then W else ownB s i,
       pcW := Write, offset := hW s, H := hW s + Data s (numEnqs s)\<rparr>\<Longrightarrow>inv s\<Longrightarrow> H s'\<ge>T s'"
  by (simp add:pre_A6_inv_def inv_def)
*)
(*
lemma case_trans_A6_to_write_2:
  shows "pre_A6_inv s \<Longrightarrow> s' = s
    \<lparr>ownB := \<lambda>i. if hW s \<le> i \<and> i < hW s + Data s (numEnqs s) then W else ownB s i,
       pcW := Write, offset := hW s, H := hW s + Data s (numEnqs s)\<rparr>\<Longrightarrow>inv s\<Longrightarrow>con_assms s\<Longrightarrow> \<not>case_2 s'" 
  using case_split_2 case_trans_A6_to_write_1 by auto
*)


lemma case_trans_A6_to_write_7:
  "pre_A6_inv s \<Longrightarrow> s' = trans_A6 s \<Longrightarrow>inv s\<Longrightarrow> con_assms s\<Longrightarrow> case_1 s'"
  apply(subgoal_tac "\<not>case_2 s") prefer 2
  using case_trans_A6_2 apply blast
  apply (simp add:pre_A6_inv_def inv_def case_1_lemmas trans_A6_def)
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

 


lemma case_trans_A7_2:
  shows "pre_A7_inv s \<Longrightarrow>  case_2 s \<Longrightarrow> False"
  apply (simp add: pre_A7_inv_def inv_def)
  by (metis case_split_2)

lemma case_trans_A7_to_write_2:
  shows "pre_A7_inv s \<Longrightarrow> s' = trans_A7 s \<Longrightarrow>  \<not>case_1 s'"
  by (simp add:pre_A7_inv_def inv_def trans_A7_def case_1_lemmas)
  

lemma case_trans_A7_to_write_7:
  shows "pre_A7_inv s \<Longrightarrow> s' = trans_A7 s \<Longrightarrow>inv s\<Longrightarrow> con_assms s\<Longrightarrow> case_2 s'"
  apply(subgoal_tac "\<not>case_2 s") prefer 2
  using case_trans_A7_to_write_2 [where s=s and s'=s']
  using case_trans_A7_2 apply blast 
  apply (simp add:pre_A7_inv_def trans_A7_def inv_def) 
  apply(thin_tac "\<not>case_2 s") 
  apply(simp add:case_1_lemmas case_2_lemmas)
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
  by (simp add:pre_write_inv_def case_1_lemmas case_2_lemmas)





(**********************Supporting lemmas for R trans*********************************)

lemma R_idle_to_nidle_lemma_case_1_5:
  assumes 
   a1: "case_1 s"  and 
   a2: " con_assms s" and 
   a3: "pcR s = idleR" and
   a4: " pre_R (pcR s) s " and
   a5: " s'=(s\<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
          numDeqs := Suc (numDeqs s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr>)"and
   a6: "inv s" and 
   a7: "q s\<noteq>[]"
 shows "case_1 s'"
  using assms apply (simp add: case_1_def) apply(simp add:case_1_lemmas inv_def) 
  apply(clarify) apply(intro conjI impI)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(subgoal_tac "fst (last (q s)) + snd (last (q s))\<le>N") prefer 2
  apply linarith
  apply(subgoal_tac "q s\<noteq>[]\<longrightarrow>hd(q s) \<in>set(q s)") prefer 2 
  apply (metis list.set_sel(1))
  using a7 apply (metis diff_is_0_eq less_nat_zero_code prod.collapse zero_less_diff)
   apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(rule_tac ?x = "T s" in exI)
  apply(rule_tac ?x = "end(hd(q s))" in exI)
  apply(intro conjI impI)
  apply (metis cancel_comm_monoid_add_class.diff_cancel end_simp le_0_eq le_neq_implies_less length_0_conv trans_le_add1)
  apply(rule_tac ?x = "fst (last (q s)) + snd (last (q s))" in exI)
  apply(simp add:pre_R_def  pre_dequeue_inv_def) 
  apply(intro conjI impI) 
  defer
  apply (metis (no_types, lifting) F.distinct(19) F.distinct(3) diff_is_0_eq le_0_eq le_neq_implies_less length_0_conv nat_le_linear)
  apply (metis (no_types, hide_lams) F.distinct(3)) 
  defer
  apply (metis le_neq_implies_less le_refl)
  apply (metis diff_add_inverse eq_imp_le le_neq_implies_less) 
 defer
  apply(subgoal_tac "hd(q s) = (q s!0)") prefer 2 
  apply (metis hd_conv_nth)
  apply(subgoal_tac "hd(tl(q s)) = (q s!1)") prefer 2
  apply (metis (no_types, lifting) One_nat_def diff_add_inverse2 hd_conv_nth last_conv_nth length_greater_0_conv length_tl less_diff_conv list.size(3) nth_tl)
  apply(case_tac "fst(q s!0) = 0") 
  apply (metis (no_types, hide_lams) Nat.add_0_right add.commute diff_add_inverse2 diff_is_0_eq last_conv_nth lessI not_less plus_1_eq_Suc trans_le_add1)
  apply(subgoal_tac "ownB s 0 \<noteq> Q") prefer 2 
  apply (metis F.distinct(19) gr0I le_numeral_extra(3))
  apply(subgoal_tac "\<nexists>a b. (a,b) \<in> set(q s) \<and> a=0") prefer 2 
  apply (metis (no_types, lifting) bot_nat_0.extremum mem_Collect_eq plus_nat.add_0)
  apply (metis (no_types, lifting) One_nat_def Suc_lessI diff_Suc_1 last_conv_nth length_greater_0_conv less_le less_one nth_mem prod.collapse)
  apply (metis (no_types, hide_lams) Nitpick.size_list_simp(2) hd_conv_nth last_conv_nth last_tl length_tl less_not_refl)
  apply (metis (no_types, lifting) diff_add_inverse diff_is_0_eq' le_0_eq le_eq_less_or_eq length_0_conv linorder_neqE_nat list.set_sel(1) nat_less_le not_add_less1 prod.collapse)
  apply (metis diff_add_inverse diff_is_0_eq' le_eq_less_or_eq less_nat_zero_code list.set_sel(1) prod.collapse)                       
  apply (metis (no_types, hide_lams) F.distinct(19) F.distinct(3) le_eq_less_or_eq not_less)
  using le_eq_less_or_eq 
  apply (metis (no_types, lifting) F.distinct(19) add_lessD1 le_add_diff_inverse less_imp_le_nat nat_neq_iff)
  apply (subgoal_tac "((fst (hd (q s)) + snd (hd (q s)) < fst (last (q s)) + snd (last (q s))) \<longrightarrow> (Suc 0 < length (q s))) \<and>
   ((Suc 0 < length (q s)\<longrightarrow>fst (hd (q s)) + snd (hd (q s)) < fst (last (q s)) + snd (last (q s))))")
   apply blast  
  apply(intro conjI impI)
  apply (metis (no_types, lifting) One_nat_def Suc_eq_plus1 Suc_lessI add.commute diff_add_zero hd_conv_nth last_conv_nth length_greater_0_conv less_not_refl2)
  apply(subgoal_tac "hd(q s)\<in> set(q s) \<and> last(q s) \<in>set(q s)") prefer 2 
  apply (metis last_in_set list.set_sel(1))
  apply(subgoal_tac "fst(hd(q s)) < fst(last(q s))") 
  apply (metis (no_types, lifting) linorder_neqE_nat nat_less_le prod.collapse trans_less_add1)
  apply(subgoal_tac "hd(q s) = (q s!0) \<and> last(q s) = (q s!(length(q s)-1))") prefer 2
  apply (metis hd_conv_nth last_conv_nth)
  apply(subgoal_tac "(\<forall>a b aa. (a, b) \<in> set (q s) \<and> (\<exists>b. (aa, b) \<in> set (q s)) \<longrightarrow> a + b > aa \<longrightarrow>a \<ge> aa )") prefer 2
  apply (metis (no_types, hide_lams) diff_is_0_eq' linorder_neqE_nat nat_le_linear zero_less_diff)
  by (metis (no_types, lifting) One_nat_def diff_is_0_eq diff_less leD length_pos_if_in_set less_one linorder_neqE_nat prod.collapse)



(*
lemma R_idle_to_nidle_lemma_case_1_5:
  assumes 
   a1: "case_1 s"  and 
   a2: " con_assms s" and 
   a3: "pcR s = idleR" and
   a4: " pre_R (pcR s) s " and
   a5: " s'=(s\<lparr>ownB := \<lambda>i. if fst (hd (q s)) \<le> i \<and> i < fst (hd (q s)) + snd (hd (q s)) then R else ownB s i,
          numDeqs := Suc (numDeqs s), ownT := R, tempR := hd (q s), pcR := Read, q := tl (q s)\<rparr>)"and
   a6: "inv s" and 
   a7: "q s\<noteq>[]"
 shows "case_1 s'"
  using assms apply(simp add:case_1_lemmas inv_def) 
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
  defer
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
  defer 
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
*)

  
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
  by metis

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
  by (smt (z3) add_lessD1 diff_add_inverse end_simp less_imp_add_positive list.size(3) nat_neq_iff not_add_less2)
  
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
  apply(simp add:case_2_lemmas) 
  apply(subgoal_tac "Q_structure s") prefer 2 
  apply (metis RingBuffer_BD_latest_3.inv_def)
  apply (metis gr0I less_nat_zero_code)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "Q_structure s") prefer 2 using pec_prelim_9 [where s=s]
  apply blast
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:pre_R_def pre_dequeue_inv_def)
  apply(simp add:case_2_lemmas ) 
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
  apply (metis (no_types, lifting) F.distinct(21) le_eq_less_or_eq le_less_trans)
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
  apply(subgoal_tac "ownB s 0 = Q \<and> 0\<le>N") prefer 2
  apply (metis gr_zeroI zero_le)
  apply(subgoal_tac "\<exists>a b.((a,b)\<in>set(q s) \<and> a=0)") prefer 2 using pec_prelim_2 [where s=s]
  apply presburger
  apply(subgoal_tac "hd(q s) \<in> set(q s)") prefer 2
  apply (metis list.set_sel(1))
  apply(subgoal_tac "hd(q s) = q s!0") prefer 2
  apply (metis hd_conv_nth)
  apply(subgoal_tac "\<exists>j.(j<length(q s) \<and> fst(q s!j) = 0)") prefer 2 
  apply (metis (no_types, lifting) fst_eqD in_set_conv_nth)
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
  apply(subgoal_tac "ownB s (fst (hd (q s)) + snd (hd (q s))) = Q") prefer 2
  apply (metis le_add1 le_less_Suc_eq not_less_eq)
  apply(subgoal_tac "length(q s)>1") prefer 2 
  apply (metis (no_types, lifting) One_nat_def Suc_lessI diff_Suc_1 hd_conv_nth last_conv_nth length_greater_0_conv not_add_less1)
  apply(subgoal_tac "(hd (tl (q s))) = (q s!1) ") prefer 2
  apply (metis (no_types, lifting) One_nat_def hd_conv_nth length_tl lessI list.size(3) not_less_eq nth_tl zero_less_diff)
  defer
  apply(subgoal_tac "ownB s 0 = Q") prefer 2
  apply (metis gr_zeroI zero_le)
  apply(subgoal_tac "(\<exists>x. (\<exists>a b. x = {j. a \<le> j \<and> j < a + b} \<and> (a, b) \<in> set (q s)) \<and> 0 \<in> x)") prefer 2 
  using bot_nat_0.extremum apply presburger
  apply (metis head_q0 last_conv_nth length_pos_if_in_set length_tl list.size(3) not_add_less1)
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
  apply(subgoal_tac "(fst(hd(q s)),snd(hd(q s))) \<in>set (q s)") prefer 2 
  apply (metis hd_in_set prod.collapse)
  apply(subgoal_tac "Q_structure s") prefer 2 
  apply blast
  apply(subgoal_tac "ab\<ge> fst(hd(q s)) + snd(hd(q s))") prefer 2
  using pec_prelim_8 [where s=s] 
  apply (metis (no_types, lifting))
  apply(subgoal_tac "\<exists>a b.((a,b)\<in>set(q s) \<and> a \<le> 0 \<and> 0<a+b)") prefer 2
  using pec_prelim_3 [where s=s] 
  apply (metis (no_types, lifting) mem_Collect_eq)
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
  apply (subgoal_tac "length(q s) > 2") prefer 2 
  apply (metis Suc_lessI hd_conv_nth less_Suc_eq less_one nat_1_add_1 plus_1_eq_Suc)
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
  apply (metis hd_conv_nth)
  apply(subgoal_tac "fst(q s!tru) = fst(q s!0)+snd(q s!0) ") prefer 2 
  apply (metis fst_conv hd_conv_nth)
  apply(subgoal_tac "tru = 1") 
  apply (metis fst_conv)
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
  apply(simp add:case_2_lemmas) 
  apply(subgoal_tac "Q_structure s") prefer 2 
  apply (metis RingBuffer_BD_latest_3.inv_def)
  apply (metis gr0I less_nat_zero_code)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "Q_structure s") prefer 2 using pec_prelim_9 [where s=s]
  apply blast
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:pre_R_def pre_dequeue_inv_def)
  apply(simp add:case_2_lemmas ) 
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
  apply(simp add:case_2_lemmas) 
  apply(subgoal_tac "Q_structure s") prefer 2 
  apply (metis RingBuffer_BD_latest_3.inv_def)
  apply (metis gr0I less_nat_zero_code)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "Q_structure s") prefer 2 using pec_prelim_9 [where s=s]
  apply blast
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:pre_R_def pre_dequeue_inv_def)
  apply(simp add:case_2_lemmas ) 
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
  apply (metis (no_types, lifting) mem_Collect_eq) defer 
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
  defer using pec_prelim_11 [where s=s and i=ass and j=tru]
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
  apply(simp add:case_2_lemmas) 
  apply(subgoal_tac "Q_structure s") prefer 2 
  apply (metis RingBuffer_BD_latest_3.inv_def)
  apply (metis gr0I less_nat_zero_code)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "Q_structure s") prefer 2 using pec_prelim_9 [where s=s]
  apply blast
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:pre_R_def pre_dequeue_inv_def)
  apply(simp add:case_2_lemmas ) 
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
  using le_neq_implies_less apply presburger
  apply(case_tac "i=length(q s)-1") 
  apply (metis last_conv_nth less_nat_zero_code list.size(3))
  apply(subgoal_tac "fst(q s!(i+1)) = end(q s!i) \<or> fst(q s!(i+1)) = 0") prefer 2 
  apply (smt (z3) Nat.add_0_right One_nat_def add_Suc_right add_diff_cancel_right' add_gr_0 end_simp list.size(3) nat_neq_iff not_less_eq)
  apply(case_tac "fst(q s!(i+1)) = end(q s!i)") apply simp 
  apply (metis One_nat_def Suc_mono diff_add_inverse less_zeroE list.size(3) not_gr0 not_less_less_Suc_eq plus_1_eq_Suc)
  apply(case_tac "case_1 s", simp_all)
  apply(simp add:case_1_lemmas) 
  apply(clarify)
  apply(subgoal_tac "b = fst(q s!0)") prefer 2 
  apply (metis head_q0 length_greater_0_conv less_nat_zero_code list.size(3))
  apply(subgoal_tac "snd(q s!i)>0") prefer 2
  apply metis
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
  apply metis
  apply (metis F.distinct(11) F.distinct(19) fst_eqD leI linorder_neqE_nat)
  apply(subgoal_tac "case_2 s") prefer 2 
  apply fastforce
  apply(thin_tac "\<not>case_1 s")
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:case_2_lemmas)
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
  apply(subgoal_tac "\<forall>i.(\<exists>x.( x = {i. aa \<le> i \<and> i < aa + ba} )\<and> i\<in>x)\<longrightarrow>ownB s i = Q") prefer 2 
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
  apply(subgoal_tac "\<forall>i.(\<exists>x.( x = {i. aa \<le> i \<and> i < aa + ba} )\<and> i\<in>x)\<longrightarrow>ownB s i = Q") prefer 2 
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
  apply(subgoal_tac "\<forall>i.(\<exists>x.( x = {i. aa \<le> i \<and> i < aa + ba} )\<and> i\<in>x)\<longrightarrow>ownB s i = Q") prefer 2
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
  defer using strange_things_8_1 [where s=s]
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
  by(simp add:case_1_lemmas)

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
  by(simp add:case_2_lemmas)

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
  apply(simp add:case_1_lemmas)
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
  apply(simp add:case_1_lemmas)
  apply(subgoal_tac "H s>T s") prefer 2 
  apply metis
  apply(simp add:case_2_lemmas)
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
  apply(simp add:case_2_lemmas)
  apply meson
  apply(simp add:case_2_lemmas case_1_lemmas)
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
  apply(simp add:case_1_lemmas) 
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
  apply(simp add:case_2_lemmas)
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply metis
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s") 
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
  apply (simp add: RingBuffer_BD_latest_3.inv_def)  apply simp
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
  apply(simp add:case_1_lemmas)
  apply(simp add:case_2_lemmas)
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
  using assms apply(simp add:inv_def pre_W_def cW_step_def trans_A3_def pre_A3_inv_def)
  apply(intro conjI impI)
  apply(simp add:Q_lemmas Q_basic_lemmas) defer
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def) 
  apply(subgoal_tac "case_1 s") prefer 2 
  apply (metis RingBuffer_BD_latest_3.case_split le_refl)
  apply(subgoal_tac "\<not>case_2 s'") prefer 2 
  using case_trans_A3_to_write_2 [where s=s and s'=s'] 
  apply (simp add: assms(1) pre_A3_inv_def trans_A3_def)
  apply simp
  using case_trans_A3_to_write_7 [where s=s]
  by (simp add: assms(1) pre_A3_inv_def trans_A3_def)


lemma W_inv_A4_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A4"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"    
shows "inv s'"
  using assms apply(simp add:inv_def pre_W_def cW_step_def trans_A4_def)
  apply(intro conjI impI)  apply(simp add:inv_def pre_W_def cW_step_def pre_A4_inv_def trans_A4_def)
  apply (simp add: less_diff_conv)  apply(simp add:inv_def pre_W_def cW_step_def pre_A4_inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas) defer  apply(simp add:inv_def pre_W_def cW_step_def pre_A4_inv_def)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)  
  apply (metis (no_types, lifting) F.distinct(19) add.commute add_lessD1 canonically_ordered_monoid_add_class.lessE less_diff_conv) 
  apply(case_tac "T s\<ge>tW s")
  apply(subgoal_tac "case_2 s'") prefer 2 
  using case_trans_A4_to_write_7 [where s=s and s'=s'] 
  apply (simp add: assms(1) assms(2) pre_A4_inv_def trans_A4_def)
  apply meson 
  using case_trans_A4_to_write_9 [where s=s and s'=s'] 
  using assms(1) pre_A4_inv_def trans_A4_def by auto



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
  using assms apply(simp add:inv_def pre_W_def cW_step_def pre_A6_inv_def trans_A6_def)
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
  using assms apply(simp add:inv_def pre_W_def cW_step_def pre_A7_inv_def trans_A7_def)
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
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_lemmas) 
  apply(simp add:case_2_lemmas)
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
  apply(simp add:case_1_lemmas) apply(simp add:case_2_lemmas)
  by (metis dual_order.strict_iff_order less_trans)

lemma W_inv_Enqueue_cases_split_2:
  "case_2 s \<Longrightarrow>  pcW s = Enqueue \<Longrightarrow>pre_W (pcW s) s \<Longrightarrow> cW_step (pcW s) s s'
\<Longrightarrow> \<not>case_1 s'"    
  apply(subgoal_tac "H s = H s' \<and> T s = T s'") prefer 2 using pec_5 apply blast
  apply(simp add:case_1_lemmas) apply(simp add:case_2_lemmas) 
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
  apply(simp add:case_1_lemmas) apply clarify apply(intro conjI impI)
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
  apply(simp add:case_2_lemmas) apply clarify 
  using Suc_diff_le apply presburger
  defer defer
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply clarify
  apply(intro conjI impI)
  apply(rule_tac ?x = "{i. offset s \<le> i \<and> i < offset s + Data s (numEnqs s)}" in exI)
  apply (intro conjI impI)
  apply metis
  apply(case_tac "case_1 s") apply(simp)
  apply(simp add:case_1_lemmas) apply clarify apply(intro conjI impI)
  apply (metis F.distinct(5) diff_is_0_eq' less_nat_zero_code linorder_neqE_nat nat_le_linear zero_less_diff)
  apply (metis (no_types, lifting) Suc_le_lessD fst_conv not_less_eq_eq snd_conv tempW_def)
  apply(subgoal_tac "case_2 s") apply simp apply(thin_tac "\<not>case_1 s")[1]
  prefer 2 apply blast apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:case_2_lemmas) apply clarify 
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
  apply(case_tac "case_1 s", simp_all) prefer 2 apply(simp add:case_2_lemmas)
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
  defer                      
  apply(simp add:case_2_lemmas)
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
  apply(case_tac "q s=[]")
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:case_1_lemmas)
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
  apply(simp add:case_1_lemmas)
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
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:case_1_lemmas)
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
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_lemmas) 
  apply(simp add:case_2_lemmas)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_lemmas) 
  apply(subgoal_tac "case_2 (s\<lparr>pcW := FinishedW\<rparr>)")
  apply blast apply simp apply(thin_tac "\<not> case_1 s ") 
  apply(simp add:case_2_lemmas)
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
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_lemmas)
  apply(simp add:case_2_lemmas)
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
  by(simp add:inv_def Q_lemmas Q_basic_lemmas) 

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
  apply(subgoal_tac "data_index(s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue, ownD := \<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i,
             data_index :=\<lambda>x. if (offset s, Data s (numEnqs s)) = x then numEnqs s else data_index  (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue, ownD :=\<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i\<rparr>) x\<rparr>) = data_index s'") prefer 2
  apply meson
  apply(subgoal_tac "(\<forall>i. (i<length(q s')) \<longrightarrow> data_index s' (q s' ! i) =  numDeqs s' + i) \<longrightarrow> (\<forall>i<length (q (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,  ownD := \<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i,
                data_index := \<lambda>x. if (offset s, Data s (numEnqs s)) = x then numEnqs s else data_index (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue, ownD := \<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i\<rparr>) x\<rparr>)). data_index (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue, ownD :=  \<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i,
             data_index :=  \<lambda>x. if (offset s, Data s (numEnqs s)) = x then numEnqs s  else data_index (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,   ownD := \<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i\<rparr>) x\<rparr>)  (q (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
                ownD := \<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i,  data_index := \<lambda>x. if (offset s, Data s (numEnqs s)) = x then numEnqs s  else data_index (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue, ownD := \<lambda>i. if i = numWrites s then B  else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i\<rparr>)  x\<rparr>) !  i) =
           numDeqs (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,    ownD := \<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i,  data_index := \<lambda>x. if (offset s, Data s (numEnqs s)) = x then numEnqs s else data_index (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue, ownD :=   \<lambda>i. if i = numWrites s then B else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i\<rparr>) x\<rparr>) + i) ") prefer 2 
  apply force
  apply(subgoal_tac "(\<forall>i. (i<length (q s')) \<longrightarrow> data_index s' (q s' ! i) = numDeqs s' + i)") 
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
  using assms(1) assms(5) 
  apply (metis less_nat_zero_code list.size(3)) 
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
  apply(simp add:inv_def pre_W_def cW_step_def trans_A3_def pre_A3_inv_def pre_write_inv_def)
  by(simp add:tempW_lemmas tempW_basic_lemmas)



lemma W_local_A4_lemma:
  assumes "inv s"
  and "con_assms s"
  and "pcW s = A4"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pre_W (pcW s') s'"
  using assms apply simp
  apply(simp add:inv_def pre_W_def cW_step_def trans_A4_def pre_A4_inv_def pre_write_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(intro conjI impI)
  apply (simp add: less_diff_conv)
  apply(case_tac "case_1 s") apply(subgoal_tac "\<not>case_2 s") apply simp 
  apply(thin_tac "\<not> case_2 s")
  apply(simp add:case_1_lemmas) 
  apply(subgoal_tac "hW s = fst (last (q s)) + snd (last (q s))") 
  apply blast
  apply (metis cancel_comm_monoid_add_class.diff_cancel le_eq_less_or_eq length_0_conv less_nat_zero_code)
  apply (metis case_split_5)
  apply(subgoal_tac "case_2 s") apply simp 
  apply(thin_tac "\<not>case_1 s") 
  apply(simp add:case_2_lemmas) 
  apply (metis (no_types, lifting) add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq diff_zero le_trans length_greater_0_conv nat_less_le)
  apply (metis)
  apply(simp add:Q_lemmas Q_basic_lemmas tempW_lemmas tempW_basic_lemmas)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(case_tac "case_1 s") apply(subgoal_tac "\<not>case_2 s") apply simp
  apply(thin_tac "\<not> case_2 s")
  apply(simp add:case_1_lemmas)
  apply (metis (no_types, hide_lams) diff_is_0_eq' le_eq_less_or_eq length_pos_if_in_set nth_mem prod.exhaust_sel zero_less_diff)
  apply (metis case_split_5)
  apply(subgoal_tac "case_2 s") apply simp 
  apply(thin_tac "\<not>case_1 s") 
  apply(simp add:case_2_lemmas)
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
  apply(simp add:Q_lemmas Q_basic_lemmas)
  defer 
  apply(case_tac "case_1 s") apply(subgoal_tac "\<not>case_2 s") apply simp 
  apply(thin_tac "\<not> case_2 s")
  apply(simp add:case_1_lemmas)
  apply(simp add:Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply (metis (no_types, lifting) add_leD1 cancel_comm_monoid_add_class.diff_cancel le_eq_less_or_eq le_zero_eq length_0_conv)
  apply (metis case_split_5)
  apply(subgoal_tac "case_2 s") apply simp 
  apply(thin_tac "\<not>case_1 s") 
  apply(simp add:case_2_lemmas)
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
  apply(simp add:case_1_lemmas)
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
  apply(simp add:case_2_lemmas)
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
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_lemmas)
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
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(simp add:cW_step_def pre_W_def trans_A6_def)
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
  apply(simp add:case_1_lemmas)
  apply (metis cancel_comm_monoid_add_class.diff_cancel le_eq_less_or_eq le_zero_eq length_0_conv) 
  apply (metis F.distinct(19) Q_owns_bytes_def Q_structure_def bot_nat_0.extremum_uniqueI cancel_comm_monoid_add_class.diff_cancel less_or_eq_imp_le nat_less_le ran_indices_lem5)
  apply(simp add:case_1_lemmas)
  defer
  apply(simp add:case_1_lemmas)
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
  apply(simp add:cW_step_def pre_W_def trans_A7_def)
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
  apply (metis F.distinct(19) Q_owns_bytes_def Q_structure_def less_nat_zero_code not_gr0 ran_indices_lem5)
  apply(simp add:case_1_lemmas) 
  defer
  apply(simp add:case_1_lemmas)
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
  apply(case_tac "case_1 s") apply simp  apply(simp add:case_1_lemmas)
  apply metis
  apply meson apply(case_tac "case_1 s") apply simp  apply(simp add:case_1_lemmas)
  apply metis
  apply(simp add:case_2_lemmas)
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
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_lemmas) 
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis F.distinct(5) eq_imp_le less_add_same_cancel1)
  apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_lemmas)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) 
  apply clarify
  apply(intro conjI impI)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_lemmas) apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_lemmas)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_lemmas) apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_lemmas)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_lemmas)
  apply (metis add_cancel_left_left less_imp_le_nat old.prod.inject prod.collapse tempW_def)
  apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_lemmas)
  apply(simp add:pre_acquire_inv_def)
  apply(intro conjI impI) 
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_lemmas)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis F.distinct(5) le_eq_less_or_eq less_add_same_cancel1)
  apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_lemmas)
  apply (metis F.distinct(5) le_eq_less_or_eq less_add_same_cancel1)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_lemmas)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis F.distinct(5) le_eq_less_or_eq less_add_same_cancel1)
  apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_lemmas)
  apply (metis F.distinct(5) le_eq_less_or_eq less_add_same_cancel1)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_lemmas)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis F.distinct(5) le_eq_less_or_eq less_add_same_cancel1)
  apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_lemmas)
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
  apply(case_tac "case_1 s") apply(simp ) apply(simp add:case_1_lemmas)
  apply(intro conjI impI) 
  apply (metis eq_imp_le less_imp_le_nat linorder_neqE_nat)
  apply (metis le_neq_implies_less le_refl)
  apply (metis diff_self_eq_0 le_neq_implies_less le_refl le_zero_eq length_0_conv) 
  apply (metis le_refl length_0_conv nat_less_le ordered_cancel_comm_monoid_diff_class.le_imp_diff_is_add plus_nat.add_0)
  apply (metis diff_self_eq_0 le_antisym le_refl nat_less_le zero_less_diff)
  apply metis
  apply(simp add:case_2_lemmas)
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
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_lemmas)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_lemmas)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_lemmas)
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
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_lemmas)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(clarify)
  apply(intro conjI impI) 
  apply (metis F.distinct(1) F.distinct(3) eq_imp_le linorder_neqE_nat nat_less_le trans_less_add1)
  apply (metis F.distinct(1) F.distinct(3) F.distinct(5) F.distinct(7) F.distinct(9) le_neq_implies_less less_or_eq_imp_le linorder_neqE_nat)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_lemmas)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) 
  apply(subgoal_tac "case_2 s") prefer 2
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_lemmas) 
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(case_tac "case_1 s") apply(simp add:case_1_lemmas)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) 
  apply(subgoal_tac "case_2 s") prefer 2 
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_lemmas)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(case_tac "case_1 s") apply(simp add:case_1_lemmas)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) 
  apply(subgoal_tac "case_2 s") prefer 2 
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_lemmas)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(case_tac "case_1 s") apply(simp add:case_1_lemmas)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) 
  apply (metis le_antisym le_trans less_nat_zero_code)
  apply(subgoal_tac "case_2 s") prefer 2 
  apply blast apply(simp) apply(thin_tac "\<not>case_1 s") apply(simp add:case_2_lemmas)
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
  apply(case_tac "case_1 s ") apply simp apply(simp add:case_1_lemmas)
  apply (metis diff_self_eq_0 le_neq_implies_less length_pos_if_in_set less_nat_zero_code)
  apply(simp) apply(thin_tac "\<not> case_1 s") apply(simp add:case_2_lemmas)
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
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_lemmas)
  apply metis
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis head_q0 length_greater_0_conv)
  prefer 3 
  apply(simp add:inv_def)
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_lemmas pre_Release_inv_def)
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
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply(simp add:case_1_lemmas pre_Release_inv_def)
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
  apply(simp add:case_1_lemmas pre_Release_inv_def)
  apply(simp add:inv_def Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_Release_inv_def tempR_lemmas tempR_basic_lemmas) 
  apply(simp add:Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply metis
  apply(simp add:case_2_lemmas pre_Release_inv_def) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s") apply(simp) apply(simp add:case_1_lemmas) 
  apply (metis bot_nat_0.extremum_uniqueI bot_nat_0.not_eq_extremum diff_is_0_eq' length_greater_0_conv)
  apply(simp) apply(thin_tac "\<not> case_1 s") apply(simp add:case_2_lemmas)
  apply meson
  apply(simp add:inv_def)
  apply(simp add:Q_owns_bytes_def Q_indices_def ran_indices_def)
  apply(subgoal_tac "hd(q s)\<in>set(q s)") prefer 2 
  apply (metis hd_in_set) 
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_lemmas)
  apply(simp add:pre_dequeue_inv_def)
  apply (metis F.distinct(13) bot_nat_0.extremum_uniqueI diff_self_eq_0 le_neq_implies_less length_0_conv)
  apply simp apply(thin_tac "\<not>case_1 s")  apply(simp add:case_2_lemmas)
  apply(simp add:pre_dequeue_inv_def)
  by (metis fst_conv le0 le_trans nat_less_le plus_nat.add_0 snd_conv)

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
  using R_local_release_pre_lemma [where s=s and s'=s'] apply blast       
  using R_local_idle_pre_lemma [where s=s and s'=s'] apply blast      
  using R_local_read_pre_lemma [where s=s and s'=s'] by blast      









(*******************************GLOBAL W_step shows preR*************************************)


lemma pcR_doesnt_change_with_W:
  assumes "inv s"
  and "con_assms s"
  and "pre_R (pcR s) s"
  and "pre_W (pcW s) s"
  and "cW_step (pcW s) s s'"
shows "pcR s'=pcR s"
 using assms apply simp
  apply(case_tac "pcW s ", simp add:cW_step_def trans_A3_def)
  apply(simp add:cW_step_def)
  apply(simp add:cW_step_def trans_A3_def)
  apply(simp add:cW_step_def trans_A4_def)
  apply(simp add:cW_step_def)
  apply(simp add:cW_step_def trans_A6_def)
  apply(simp add:cW_step_def trans_A7_def)
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
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(simp add:pre_W_def)
  apply(simp add:tempR_lemmas tempR_basic_lemmas)
  apply(cases "pcW s", simp_all)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all )
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all )
  apply(simp add:pre_write_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:inv_def)
  apply (metis F.distinct(1) eq_imp_le fst_eqD less_add_same_cancel1 snd_eqD)
  apply(cases "pcW s", simp_all)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(cases "numEnqs s<n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all)
  apply metis
  apply(case_tac "tW s = hW s \<and> Data s (numEnqs s) \<le> N", simp_all)
  apply metis
  apply(case_tac " hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s", simp_all, metis)
  apply(case_tac "tW s < hW s", simp_all,metis, metis)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def, metis, metis)
  apply(case_tac " Data s (numEnqs s) \<le> N - hW s", simp_all, metis)
  apply(case_tac " Data s (numEnqs s) < tW s", simp_all, metis, metis, metis, metis, metis, metis)
  apply(case_tac "numEnqs s < n", simp_all, metis, metis)
  apply(cases "tW s \<noteq> T s", simp_all, metis, metis, metis, metis, metis)
  apply(case_tac "pcW s", simp_all add:cW_step_def)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
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
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
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
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s") 
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
  apply(case_tac "case_1 s", simp_all) apply (simp add:case_1_lemmas)
  apply(clarify)
  apply (metis (no_types, lifting) F.distinct(1) diff_is_0_eq le_refl less_imp_le_nat not_gr0 prod.collapse prod.inject tempW_def zero_less_diff)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s") 
  apply clarify
  apply (metis less_or_eq_imp_le zero_less_iff_neq_zero)
  apply(simp add: tempW_def)
  apply(subgoal_tac "fst((offset s, Data s (numEnqs s))) + snd((offset s, Data s (numEnqs s)))  \<noteq> fst(tempR s)")
  apply (metis fst_eqD snd_eqD)
  apply(subgoal_tac "offset s \<noteq> fst(tempR s)") prefer 2 
  apply (metis (no_types, lifting) F.distinct(1) Suc_le_lessD Suc_lessD Suc_pred add_lessD1 le_add_diff_inverse le_refl less_add_same_cancel1)
  apply(simp add:inv_def)
  apply(case_tac "case_1 s", simp_all)
  apply(simp add:case_1_lemmas)
  apply(clarify)
  apply linarith
  apply(simp add:case_2_lemmas) apply (thin_tac "\<not>case_1 s") 
  apply(clarify)
  apply (metis add_gr_0 nat_neq_iff)
  apply(case_tac "pcW s", simp_all add:inv_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply(simp add:pre_W_def pre_A3_inv_def)
  apply(simp add:case_2_lemmas)
  apply(simp add:pre_W_def pre_A3_inv_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply(simp add:pre_W_def pre_A4_inv_def)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply (metis (no_types, lifting) le_add_diff_inverse le_eq_less_or_eq less_trans_Suc not_less_eq_eq)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not> case_1 s")
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply(simp add:pre_W_def pre_A6_inv_def) 
  apply (metis le_add_diff_inverse le_trans less_or_eq_imp_le)
  apply(simp add:case_2_lemmas)
  apply(simp add:pre_W_def pre_A6_inv_def)
  apply (metis Suc_leI not_less_eq_eq)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply(simp add:pre_W_def pre_A7_inv_def) 
  apply clarify
  apply(intro conjI impI)
  apply linarith
  apply (metis le_add_diff_inverse le_trans less_or_eq_imp_le)
  apply(simp add:case_2_lemmas)
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
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(simp add:pre_W_def pre_A6_inv_def)
  apply(simp add:pre_W_def pre_A7_inv_def)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "pcW s ", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
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
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(cases "pcW s", simp_all add:cW_step_def  B_acquire_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:cW_step_def  B_acquire_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(cases "pcW s", simp_all add:cW_step_def  B_acquire_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:cW_step_def  B_acquire_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:cW_step_def  B_acquire_def pre_W_def)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:cW_step_def  B_acquire_def pre_W_def)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:cW_step_def  B_acquire_def pre_W_def)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "tW s = hW s \<and> Data s (numEnqs s) \<le> N", simp_all)
  apply(cases "ownT s = Q", simp_all) 
  apply(simp add:pre_A2_inv_def)
  apply(cases "hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s", simp_all)
  apply(cases "tW s < hW s", simp_all) 
  apply(case_tac "T s = hW s", simp_all)
  apply(cases "ownT s = Q", simp_all) 
  using pre_A2_inv_def apply auto[1]
  apply(cases "hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s", simp_all)
  apply(cases "tW s < hW s", simp_all) 
  apply(cases "tW s = hW s \<and> Data s (numEnqs s) \<le> N", simp_all)
  apply(cases "ownT s = Q", simp_all) 
  using pre_A2_inv_def apply auto[1]
  apply(cases "tW s = hW s \<and> Data s n \<le> N", simp_all)
  apply(cases "hW s < tW s \<and> Data s n < tW s - hW s", simp_all) 
  apply(cases "tW s < hW s", simp_all) 
  apply(cases "Data s (numEnqs s) \<le> N - hW s", simp_all)
  apply(cases "Data s (numEnqs s) < tW s", simp_all)
  apply(cases "N < Data s (numEnqs s)", simp_all)
  apply(cases "ownT s = W", simp_all add:pre_enqueue_inv_def inv_def)
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_lemmas)
  apply (metis nat_less_le)
  apply simp apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis nat_less_le)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:cW_step_def  B_acquire_def)
  apply(cases "tW s = hW s \<and> Data s (numEnqs s) \<le> N", simp_all)
  apply(cases "ownT s = W", simp_all add:pre_enqueue_inv_def inv_def)
  apply(cases "ownT s = W", simp_all add:pre_A2_inv_def inv_def)
  apply(cases "hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s", simp_all)
  apply(cases "tW s < hW s", simp_all)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
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
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(simp add:pre_A3_inv_def)
  apply(simp add:pre_A4_inv_def)
  apply (metis (no_types, lifting) F.distinct(19) add.commute add_lessD1 less_diff_conv less_imp_add_positive)
  apply(simp add:pre_A5_inv_def)
  apply(cases "Data s (numEnqs s) \<le> N - hW s", simp_all)
  apply(cases "Data s (numEnqs s) < tW s", simp_all)
  apply(simp add:pre_A6_inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply clarify
  apply(subgoal_tac "offset s = hW s") prefer 2
  apply (metis (no_types, lifting) F.distinct(19) F.distinct(23) add_lessD1 diff_is_0_eq' le_0_eq le_eq_less_or_eq length_0_conv nat_le_iff_add)
  apply (metis (no_types, lifting) F.distinct(19) add_lessD1 diff_self_eq_0 le_0_eq le_add_diff_inverse le_neq_implies_less length_0_conv)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s") 
  apply (metis Suc_leI not_less_eq_eq)
  apply(simp add:pre_A7_inv_def) 
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply clarify
  apply (metis (no_types, lifting) F.distinct(19) F.distinct(23) add_lessD1 diff_is_0_eq' le_0_eq le_eq_less_or_eq length_0_conv nat_le_iff_add)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s") 
  apply (metis Suc_leI not_less_eq_eq)
  apply(simp add:pre_A8_inv_def)
  apply(cases "N < Data s (numEnqs s)", simp_all)
  apply(cases "ownT s = W", simp_all)
  apply (metis fst_conv le_trans nat_less_le snd_conv tempW_def)
  apply(simp add:Q_lemmas Q_basic_lemmas Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply(case_tac "case_1 s", simp_all)
  apply(simp add:case_1_lemmas)
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
  apply(simp add:case_2_lemmas)
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
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply(case_tac "numEnqs s< n", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(case_tac "pcW s", simp_all)
  apply(case_tac "tW s = hW s \<and> Data s (numEnqs s) \<le> N", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(case_tac " hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s ", simp_all)
  apply(case_tac "tW s < hW s", simp_all)
  apply(simp add:Q_lemmas Q_basic_lemmas Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply(simp_all add:cW_step_def trans_A3_def trans_A4_def trans_A6_def trans_A7_def)
  apply (simp add: pre_A3_inv_def)
  apply(case_tac " Data s (numEnqs s) \<le> N - hW s", simp_all)
  apply(case_tac "Data s (numEnqs s) < tW s", simp_all)
  apply(case_tac "N < Data s (numEnqs s)", simp_all)
  apply(case_tac "ownT s = W", simp_all)
  apply(simp add:Q_lemmas Q_basic_lemmas Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply(simp add:pre_enqueue_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply clarify
  apply (metis (no_types, hide_lams) Nat.add_0_right diff_is_0_eq le_refl nat_add_left_cancel_less nat_neq_iff zero_less_diff)
  apply(simp add:case_2_lemmas) 
  apply(simp add:Q_lemmas Q_basic_lemmas Q_indices_def Q_owns_bytes_def ran_indices_def)
  apply(simp add:pre_enqueue_inv_def)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply clarify
  apply (metis (no_types, hide_lams) diff_self_eq_0 fst_eqD hd_append le_zero_eq length_0_conv less_add_same_cancel1 less_or_eq_imp_le list.sel(1) nat_less_le snd_eqD tempW_def)
  apply(simp add:case_2_lemmas) 
  apply(subgoal_tac "\<forall>a b j. ((a, b) \<in> set (q s)) \<and> j < N \<and> T s \<le> j \<longrightarrow> a + b < j") prefer 2
  apply (metis (no_types, lifting) hd_append length_greater_0_conv length_pos_if_in_set)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(subgoal_tac "offset s + Data s (numEnqs s)<T s") prefer 2 
  apply force
  apply(subgoal_tac "\<forall> j. T s \<le> j \<longrightarrow> offset s + Data s (numEnqs s) < j") prefer 2 
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
  apply(cases "pcW s", simp_all add:trans_A3_def trans_A4_def trans_A6_def trans_A7_def) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(simp_all add:cW_step_def)
  apply(cases "pcW s", simp_all add:trans_A3_def trans_A4_def trans_A6_def trans_A7_def) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(simp add:pre_W_def pre_write_inv_def)
  apply (metis F.distinct(1) fst_eqD less_add_same_cancel1 nat_le_linear snd_eqD)
  apply(cases "pcW s", simp_all add:trans_A3_def trans_A4_def trans_A6_def trans_A7_def) 
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
  apply(cases "pcW s", simp_all add:trans_A3_def trans_A4_def trans_A6_def trans_A7_def) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:trans_A3_def trans_A4_def trans_A6_def trans_A7_def) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:trans_A3_def trans_A4_def trans_A6_def trans_A7_def) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(simp add:pre_W_def pre_write_inv_def)
  apply (metis F.distinct(1))
  apply(cases "pcW s", simp_all add:trans_A3_def trans_A4_def trans_A6_def trans_A7_def) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:trans_A3_def trans_A4_def trans_A6_def trans_A7_def) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:trans_A3_def trans_A4_def trans_A6_def trans_A7_def) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:trans_A3_def trans_A4_def trans_A6_def trans_A7_def) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:trans_A3_def trans_A4_def trans_A6_def trans_A7_def) 
  apply(simp add:pre_W_def pre_A3_inv_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:trans_A3_def trans_A4_def trans_A6_def trans_A7_def) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all) defer
  apply(cases "pcW s", simp_all add:trans_A3_def trans_A4_def trans_A6_def trans_A7_def) 
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
  apply(cases "pcW s", simp_all add:trans_A3_def trans_A4_def trans_A6_def trans_A7_def) 
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)
  apply(cases "pcW s", simp_all add:trans_A3_def trans_A4_def trans_A6_def trans_A7_def) 
  apply(simp add:pre_W_def pre_A3_inv_def)
  apply(simp add:pre_W_def pre_A4_inv_def)
  apply(simp add:pre_W_def pre_A6_inv_def)
  apply(simp add:pre_W_def pre_A7_inv_def)
  apply(cases "numEnqs s < n", simp_all)
  apply(cases "tW s \<noteq> T s", simp_all)    
  apply(cases "pcW s", simp_all add:trans_A3_def trans_A4_def trans_A6_def trans_A7_def) 
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
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
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s") 
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
  apply(case_tac "case_1 s", simp_all) apply (simp add:case_1_lemmas)
  apply(clarify)
  apply (metis (no_types, lifting) F.distinct(1) diff_is_0_eq le_refl less_imp_le_nat not_gr0 prod.collapse prod.inject tempW_def zero_less_diff)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s") 
  apply clarify
  apply (metis less_or_eq_imp_le zero_less_iff_neq_zero)
  apply(simp add: tempW_def)
  apply(subgoal_tac "end((offset s, Data s (numEnqs s))) \<noteq> fst(tempR s)") 
  apply (metis end_simp fst_conv snd_conv)
  apply(subgoal_tac "offset s \<noteq> fst(tempR s)") prefer 2 
  apply (metis (no_types, lifting) F.distinct(1) Suc_le_lessD Suc_lessD Suc_pred add_lessD1 le_add_diff_inverse le_refl less_add_same_cancel1)
  apply(simp add:inv_def)
  apply(case_tac "case_1 s", simp_all)
  apply(simp add:case_1_lemmas)
  apply(clarify)
  apply linarith
  apply(simp add:case_2_lemmas) apply (thin_tac "\<not>case_1 s") 
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
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_lemmas)
  apply metis
  apply simp apply(simp add:case_2_lemmas)
  apply (metis F.distinct(7) nat_less_le) 
  apply(case_tac "case_1 s") apply simp by(simp add:case_1_lemmas)
  
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
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_lemmas) 
  apply (metis (no_types, hide_lams) F.distinct(3))
  apply simp apply(simp add:case_2_lemmas)
  by (metis (no_types, hide_lams) F.distinct(3))


lemma ownB_not_by_W_doesnt_change_after_dequeue:
  "inv s \<Longrightarrow> con_assms s \<Longrightarrow> pre_dequeue_inv s \<Longrightarrow> cR_step idleR s s'
  \<Longrightarrow>ownB s i \<noteq> W \<and> i\<le>N \<Longrightarrow> ownB s' i \<noteq> W \<and> i\<le>N"
  apply(simp add:inv_def)
  apply(simp add:cR_step_def)
  apply(simp add:pre_dequeue_inv_def)
  apply(case_tac "q s=[]")
  apply presburger
  apply(case_tac "case_1 s") apply simp by(simp add:case_1_lemmas) 

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
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_lemmas)
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
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
  apply(simp add:case_2_lemmas)
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

lemma strange_but_Q_2:
  "length(q s)>1 \<Longrightarrow>hd(tl(q s)) = tl(q s)!0"
  by (metis One_nat_def hd_conv_nth length_tl less_nat_zero_code list.size(3) zero_less_diff)

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
  apply (metis RingBuffer_BD_latest_3.inv_def basic_pointer_movement_def inRange_def inRangeht_def)
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (smt (z3) PCR.distinct(1) PCR.distinct(3) W_items_dont_change_with_R assms(2) le_trans less_or_eq_imp_le)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(1) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis RingBuffer_BD_latest_3.inv_def basic_pointer_movement_def inRange_def inRangeht_def)
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (smt (z3) PCR.distinct(1) PCR.distinct(5) W_items_dont_change_with_R assms(2) le_trans less_or_eq_imp_le)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(3) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis RingBuffer_BD_latest_3.inv_def basic_pointer_movement_def inRange_def inRangeht_def)
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
  apply(simp add: case_1_lemmas) 
  apply (metis (no_types, hide_lams) F.distinct(25) F.distinct(7) \<open>cR_step (pcR s) s s' \<Longrightarrow> tempW s = tempW s' \<and> tW s = tW s' \<and> hW s = hW s' \<and> data_index s = data_index s'\<close> le0 le_refl nat_less_le nat_neq_iff prod.inject tempW_def)
  apply(thin_tac "\<not>case_1 s")
  apply(simp add:pre_Release_inv_def)
  apply(subgoal_tac "T s\<noteq>fst(tempR s)") prefer 2 
  apply blast
  apply(simp add:case_2_lemmas)
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
  apply (simp add: \<open>\<lbrakk>RingBuffer_BD_latest_3.inv s; cR_step (pcR s) s s'; pcR s \<noteq> idleR\<rbrakk> \<Longrightarrow> q s = q s'\<close>)
  apply(subgoal_tac "q s\<noteq>[]") prefer 2 
  apply (metis Q_empty_R_step_result)
  using Q_W_relation_through_R_1 [where s=s and s'=s']
  apply presburger       
  using Q_W_relation_through_R_2 [where s=s and s'=s']
  apply (simp add: \<open>\<lbrakk>RingBuffer_BD_latest_3.inv s; cR_step (pcR s) s s'; pcR s \<noteq> idleR\<rbrakk> \<Longrightarrow> q s = q s'\<close>)
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
  apply (metis \<open>\<And>i. \<lbrakk>RingBuffer_BD_latest_3.inv s; con_assms s; pre_Release_inv s; cR_step Release s s'; ownB s i = W \<and> i \<le> N\<rbrakk> \<Longrightarrow> ownB s' i = W \<and> i \<le> N\<close> assms(1) assms(2) le_trans less_imp_le_nat)
  apply clarify
  using W_items_dont_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using ownB_by_W_doesnt_change_with_R [where s=s and s'=s' and i=j]
  apply (metis PCR.distinct(1) PCR.distinct(5) \<open>\<And>i. \<lbrakk>RingBuffer_BD_latest_3.inv s; con_assms s; cR_step (pcR s) s s'; pcR s = Release \<longrightarrow> pre_Release_inv s; pcR s = Read \<longrightarrow> pre_Read_inv s; pcR s = idleR \<longrightarrow> pre_dequeue_inv s; ownB s i = W \<and> i \<le> N\<rbrakk> \<Longrightarrow> ownB s' i = W \<and> i \<le> N\<close> assms(2) le_trans less_imp_le_nat)
  using W_items_dont_change_with_R [where s=s and s'=s']
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  using ownB_by_W_doesnt_change_with_R [where s=s and s'=s' and i=j]
  apply (metis PCR.distinct(3) PCR.distinct(5) \<open>\<And>i. \<lbrakk>RingBuffer_BD_latest_3.inv s; con_assms s; cR_step (pcR s) s s'; pcR s = Release \<longrightarrow> pre_Release_inv s; pcR s = Read \<longrightarrow> pre_Read_inv s; pcR s = idleR \<longrightarrow> pre_dequeue_inv s; ownB s i = W \<and> i \<le> N\<rbrakk> \<Longrightarrow> ownB s' i = W \<and> i \<le> N\<close> assms(2) le_trans less_imp_le_nat)
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
  apply (metis RingBuffer_BD_latest_3.inv_def basic_pointer_movement_def inRange_def inRangeht_def)
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  apply (metis PCR.distinct(1) PCR.distinct(3) assms(2) le_trans less_or_eq_imp_le)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(1) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis RingBuffer_BD_latest_3.inv_def basic_pointer_movement_def inRange_def inRangeht_def)
  using ownB_by_B_doesnt_change_with_R [where s=s and s'=s'] 
  using W_items_dont_change_with_R_2 [where s=s and s'=s'] 
  apply (metis PCR.distinct(1) PCR.distinct(5) assms(2) le_trans less_or_eq_imp_le)
  apply(subgoal_tac "hW s = hW s' \<and> tW s = tW s' \<and> tempW s = tempW s'") prefer 2
  using W_items_dont_change_with_R_2 [where s=s and s'=s']
  using PCR.distinct(3) PCR.distinct(5) assms(2) apply presburger
  apply(subgoal_tac "tW s \<le>N") prefer 2
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis RingBuffer_BD_latest_3.inv_def basic_pointer_movement_def inRange_def inRangeht_def)
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
  apply(simp add: case_1_lemmas)
  apply (metis F.distinct(15) F.distinct(21) F.distinct(25) F.distinct(7) W_items_dont_change_with_R \<open>cR_step (pcR s) s s' \<Longrightarrow> tempW s = tempW s' \<and> tW s = tW s' \<and> hW s = hW s' \<and> data_index s = data_index s'\<close> less_eq_Suc_le not_less_eq_eq)
  apply(thin_tac "\<not>case_1 s")
  apply(simp add:pre_Release_inv_def)
  apply(subgoal_tac "T s\<noteq>fst(tempR s)") prefer 2 
  apply blast
  apply(simp add:case_2_lemmas)
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
  apply (metis W_items_dont_change_with_R \<open>\<And>i. \<lbrakk>RingBuffer_BD_latest_3.inv s; con_assms s; pre_Release_inv s; cR_step Release s s'; ownB s i = W \<and> i \<le> N\<rbrakk> \<Longrightarrow> ownB s' i = W \<and> i \<le> N\<close> assms(2) le_trans less_imp_le_nat)
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
  apply (metis PCR.distinct(3) PCR.distinct(5) W_items_dont_change_with_R \<open>\<And>i. \<lbrakk>RingBuffer_BD_latest_3.inv s; con_assms s; cR_step (pcR s) s s'; pcR s = Release \<longrightarrow> pre_Release_inv s; pcR s = Read \<longrightarrow> pre_Read_inv s; pcR s = idleR \<longrightarrow> pre_dequeue_inv s; ownB s i = W \<and> i \<le> N\<rbrakk> \<Longrightarrow> ownB s' i = W \<and> i \<le> N\<close> \<open>\<And>i. \<lbrakk>RingBuffer_BD_latest_3.inv s; con_assms s; cR_step (pcR s) s s'; pcR s = Release \<longrightarrow> pre_Release_inv s; pcR s = Read \<longrightarrow> pre_Read_inv s; pcR s = idleR \<longrightarrow> pre_dequeue_inv s; ownB s i \<noteq> W \<and> i \<le> N\<rbrakk> \<Longrightarrow> ownB s' i \<noteq> W \<and> i \<le> N\<close> assms(2) le_trans less_imp_le_nat)
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
  apply (metis PCR.distinct(1) PCR.distinct(5) \<open>\<And>i. \<lbrakk>RingBuffer_BD_latest_3.inv s; con_assms s; cR_step (pcR s) s s'; pcR s = Release \<longrightarrow> pre_Release_inv s; pcR s = Read \<longrightarrow> pre_Read_inv s; pcR s = idleR \<longrightarrow> pre_dequeue_inv s; ownB s i = W \<and> i \<le> N\<rbrakk> \<Longrightarrow> ownB s' i = W \<and> i \<le> N\<close> assms(2) le_trans less_or_eq_imp_le)
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
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_lemmas) apply metis
  apply(simp) apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis (no_types, hide_lams) diff_is_0_eq le0 nat_neq_iff zero_less_diff)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def)
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_lemmas) 
  apply (metis Nat.add_diff_assoc diff_diff_left diff_is_0_eq' linorder_neqE_nat nat_le_linear zero_less_diff)
  apply(simp) apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_lemmas) apply metis
  apply(simp) apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis diff_self_eq_0 le_antisym le_neq_implies_less length_greater_0_conv less_imp_Suc_add nat.distinct(1) plus_nat.add_0)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "ownT s = R", simp_all) 
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_lemmas) 
  apply (metis bot_nat_0.extremum_uniqueI diff_self_eq_0 le_add_diff_inverse le_antisym length_0_conv)
  apply(simp) apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_lemmas) apply metis
  apply(simp) apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis add_cancel_right_left le_refl)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "ownT s = R", simp_all) 
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_lemmas) 
  apply (metis le_add_diff_inverse le_eq_less_or_eq)
  apply(simp) apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis (no_types, hide_lams) le_add_diff_inverse le_trans less_or_eq_imp_le linorder_neqE_nat nat_less_le)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac " ownT s = Q ", simp_all)
  apply(simp add:pre_R_def pre_dequeue_inv_def inv_def)
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_lemmas)
  apply (metis le_antisym nat_less_le)
  apply(simp) apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis (no_types, lifting) F.distinct(19))
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_lemmas) 
  apply (metis F.distinct(13) F.distinct(17) le_eq_less_or_eq)
  apply(simp) apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply(simp add:pre_R_def pre_dequeue_inv_def inv_def)
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(cases "pcR s", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all) 
  apply(simp add:pre_R_def pre_Release_inv_def inv_def cR_step_def)
  apply(case_tac "case_1 s") apply simp apply(simp add:case_1_lemmas) 
  apply (metis le_add_diff_inverse le_eq_less_or_eq)
  apply(simp) apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply metis
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis add_cancel_right_left le_trans)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis (no_types, lifting) F.distinct(13) eq_imp_le less_imp_le_nat linorder_neqE_nat trans_le_add1)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq trans_le_add1)
  apply(case_tac "q s = []", simp_all)
  apply metis
  apply metis
  apply metis
  apply(case_tac "T s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq trans_le_add1)
  apply(case_tac "T s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq trans_le_add1)
  apply(case_tac "q s = []", simp_all)
  apply(case_tac "T s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq trans_le_add1)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis le_add_diff_inverse le_eq_less_or_eq)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis add_cancel_right_left le_trans)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis F.distinct(13) eq_imp_le less_imp_le_nat linorder_neqE_nat trans_le_add1)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis add_cancel_right_left le_trans)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis F.distinct(13) eq_imp_le less_imp_le_nat linorder_neqE_nat trans_le_add1)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq trans_le_add1)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis le_add_diff_inverse le_trans)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis add_cancel_right_left le_trans)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "T s \<noteq> fst (tempR s)", simp_all)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis F.distinct(13) eq_imp_le less_imp_le_nat linorder_neqE_nat trans_le_add1)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq trans_le_add1)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis le_add_diff_inverse le_trans)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis add_cancel_right_left le_trans)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "T s \<noteq> fst (tempR s)", simp_all)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis F.distinct(13) eq_imp_le less_imp_le_nat linorder_neqE_nat trans_le_add1)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis Suc_leI not_less_eq_eq trans_le_add1)
  apply(simp add:tempR_lemmas tempR_basic_lemmas Q_lemmas Q_basic_lemmas)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis le_add_diff_inverse le_trans)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis (no_types, lifting) F.distinct(19))
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis add_cancel_right_left le_trans)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis le_add_diff_inverse le_eq_less_or_eq)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply metis
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis eq_imp_le less_imp_le_nat linorder_neqE_nat plus_nat.add_0)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis diff_is_0_eq' linorder_neqE_nat nat_le_linear zero_less_diff)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis eq_imp_le less_imp_le_nat linorder_neqE_nat plus_nat.add_0)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all) 
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis diff_is_0_eq' linorder_neqE_nat nat_le_linear zero_less_diff)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis add_cancel_right_left diff_add_inverse2 le_0_eq le_antisym length_0_conv nat_less_le)
  apply(case_tac "ownT s = R", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis bot_nat_0.extremum_uniqueI diff_self_eq_0 le_add_diff_inverse le_antisym length_0_conv)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis not_add_less1)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s =R", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis bot_nat_0.extremum_uniqueI diff_self_eq_0 le_add_diff_inverse le_antisym length_0_conv)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s") 
  apply (metis add_cancel_left_left diff_is_0_eq' le_neq_implies_less length_greater_0_conv zero_less_diff)
  apply(case_tac "ownT s =R", simp_all) 
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas) 
  apply (metis le_add_diff_inverse le_imp_less_Suc length_greater_0_conv nat_less_le not_less_eq zero_less_diff)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis not_add_less1)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis bot_nat_0.extremum_uniqueI diff_self_eq_0 le_add_diff_inverse le_antisym length_0_conv)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis less_or_eq_imp_le plus_nat.add_0)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis le_add_diff_inverse le_eq_less_or_eq)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
  apply (metis le_add_diff_inverse le_trans less_nat_zero_code less_or_eq_imp_le nat_less_le nat_neq_iff)
  apply(case_tac "q s=[]", simp_all)
  apply(case_tac "ownT s = Q", simp_all)
  apply(simp add:pre_dequeue_inv_def)
  apply (metis (mono_tags, hide_lams) F.distinct(19))
  apply(simp add:pre_dequeue_inv_def)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply (metis le_add_diff_inverse le_eq_less_or_eq)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all) 
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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
  apply(case_tac "case_1 s", simp_all) apply(simp add:case_1_lemmas)
  apply(case_tac "ownT s =R", simp_all)
  apply(simp add:case_2_lemmas) apply(thin_tac "\<not>case_1 s")
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


