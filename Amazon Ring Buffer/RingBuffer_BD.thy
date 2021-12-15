theory RingBuffer_BD
imports Main HOL.List
begin 

datatype PCW =
  A1 | A2 | A3 | A4 | A5 | A6 | A7 | A8
| Enqueue | idleW | OOM | FinishedW |  Write | BTS

datatype PCR =
 Release | idleR | Read

datatype F = W | R | Q | B
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
  "transfer_ownB a b \<equiv> (\<lambda>s. s \<lparr> ownB := \<lambda> i. if (ownB s i = a) then b else (ownB s) i\<rparr>)"

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
                        \<and> (\<forall>i. (i\<le>N) \<longrightarrow>  ownB s i = B)
                        \<and> (ownT s = Q)
                        \<and> (tempR s = (0,0))
                        \<and> (\<forall>i. (i\<le>N)\<longrightarrow>(\<forall>j.(j\<le>N)\<longrightarrow>data_index s (i,j) <n))"
(***********************************************************************)



(*   State of the queue   *)
(*   What Q should look like   *)

definition  "end x \<equiv> fst x + snd x"

lemmas end_simp [simp] = end_def 

definition "Q_boundness s \<equiv> (\<forall>x. (x \<in> set (q s)) \<longrightarrow> end x \<le> N)" 

definition "Q_offsets_differ s \<equiv> (\<forall>i j.(i<length(q s)\<and> j<length(q s)\<and> i\<noteq>j)\<longrightarrow>(fst(q s!i)\<noteq>fst(q s!j)))"

definition "Q_gap_structure s   \<equiv> 
          (\<forall>i. (i < length(q s) \<and> i > 0) \<longrightarrow>((end(q s!(i-1)) = fst(q s!i))\<or> (fst(q s!i) =0)))"

definition "Q_has_no_uroboros s \<equiv>
(\<forall>x. x \<in> set (butlast (q s)) \<longrightarrow> fst x \<noteq> end (last (q s)))"

definition "Q_has_no_overlaps s \<equiv>
(\<forall> x y. (x \<in> set (q s) \<and> y \<in> set (q s)) \<longrightarrow> (fst(x) < fst(y) \<longrightarrow> end x \<le> fst y))"

definition "Q_basic_struct s \<equiv> Q_boundness s \<and> Q_gap_structure s \<and> Q_offsets_differ s
                              \<and> Q_has_no_overlaps s \<and> Q_has_no_uroboros s "


lemmas Q_basic_lemmas = Q_basic_struct_def  Q_has_no_overlaps_def 
                        Q_gap_structure_def Q_has_no_uroboros_def
                        Q_boundness_def     Q_offsets_differ_def

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
shows "(\<forall>x. x \<in> set (butlast (tl(q s))) \<longrightarrow> fst x \<noteq> end (last (tl(q s))))"
  using assms  apply (simp add:Q_has_no_uroboros_def) 
  by (metis butlast_tl last_tl list.sel(2) list.set_sel(2))

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
       (\<forall>x. x \<in> set (butlast (tl(q s))) \<longrightarrow> fst x \<noteq> end (last (tl(q s)))) \<and>
       (\<forall> x y. (fst(x) < fst(y) \<and> x \<in> set (tl(q s)) \<and> y \<in> set (tl(q s))) \<longrightarrow> (end x \<le> fst y))"
  using assms  apply (simp add:Q_basic_lemmas)
  apply(intro conjI impI)
  apply (metis list.sel(2) list.set_sel(2))
  using tail_preserves_Q_offsets_differ apply (metis One_nat_def Q_basic_struct_def assms(1) length_tl)
  using tail_preserves_Q_gap_structure apply (metis One_nat_def Q_basic_struct_def assms(1) end_simp length_tl)
  using tail_preserves_Q_has_no_uroboros  apply (metis Q_basic_struct_def assms(1) end_simp old.prod.inject prod.collapse)
  by (metis list.sel(2) list.set_sel(2))












(*have the idea of "can fit between T-N or not"*)
definition "T_is_outside_Q s    \<equiv> (\<forall>i.(i<length(q s) \<and> q s\<noteq>[])\<longrightarrow>(end(q s!i)<T s))"

definition "tempR_describes_T s \<equiv> ((fst(tempR s) =0) \<longrightarrow> (T s=0 \<or> T_is_outside_Q s))
                                 \<and>((fst(tempR s) >0) \<longrightarrow> (T s=fst(tempR s)))"

definition "Q_describes_T s     \<equiv> ((fst(hd(q s)) =0) \<longrightarrow> (T s=0 \<or> T_is_outside_Q s))
                                 \<and>((fst(hd(q s)) >0) \<longrightarrow> (T s=fst(hd(q s))))"



(*have the idea of "can we describe ownB s i=R"*)

definition "R_owns_no_bytes s   \<equiv> (\<forall>i.(i\<ge>0)\<longrightarrow>ownB s i\<noteq>R)"

definition "tempR_describes_ownB s \<equiv> (\<forall>i.(i<fst(tempR s))\<longrightarrow>ownB s i\<noteq>R)
                                    \<and>(\<forall>i.(i\<ge>end(tempR s))\<longrightarrow>ownB s i\<noteq>R)
                                    \<and>(\<forall>i.(fst(tempR s)\<le>i \<and> i<end(tempR s))\<longrightarrow>ownB s i=R)"







definition "tempR_bounded s     \<equiv> end(tempR s)\<le>N"
definition "Q_no_overlap_tempR s\<equiv> (\<forall>x. (x \<in> set (q s))\<longrightarrow>
                  ((fst(tempR s)<fst(x)\<and>end(tempR s)\<le> fst(x))
                  \<or>(fst(x)<fst(tempR s)\<and>end(x)<fst(tempR s))))"
definition "Q_relates_tempR s   \<equiv> (end(tempR s) = fst(hd (q s))) \<or> (fst(hd(q s)) = 0)"
lemmas tmepR_extra_lemmas [simp] = tempR_bounded_def Q_no_overlap_tempR_def Q_relates_tempR_def


(*   Relating Q to other variables   *)

definition "Q_bytes s     \<equiv> {i  . \<exists> k l. (k, l) \<in> set(q s) \<and> k \<le> i \<and> i < k+l}"

definition "Q_bytes_inv s \<equiv> \<forall> i. i \<in> Q_bytes s \<longleftrightarrow>  ownB s i = Q"
  q s = <(0,2),(2,3)>
  
N 7
definition "Q_holds_bytes s     \<equiv> q s\<noteq>[]\<longrightarrow>(\<forall>i.(i\<in>set(q s))\<longrightarrow>(\<forall>j.(fst(i)\<le>j \<and> j<end(i))\<longrightarrow>ownB s j=Q))"

definition "Q_reflects_writes s \<equiv> (\<forall>i.(i<length(q s))\<longrightarrow>data_index s (q s!i) = ((numDeqs s) +i))"

definition "Q_elem_size s       \<equiv> (\<forall>i.(i<length(q s))\<longrightarrow>snd(q s!i) =Data s ((numDeqs s) +i))"

definition "Q_reflects_ownD s   \<equiv> (\<forall>i.(i<length(q s))\<longrightarrow>ownD s (i+(numDeqs s)) =B)"


lemma "ownB s i \<noteq> Q \<Longrightarrow> i \<notin> Q_bytes s"



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
  assumes "Q_elem_size s"
  and "(tl(q s))\<noteq>[]"
shows "(\<forall>i.(i<length(tl(q s)))\<longrightarrow>snd((tl(q s))!i) =Data s ((numDeqs s) +i +1))"
  using assms  apply (simp add:Q_elem_size_def)
  by (simp add: nth_tl)

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
                                      Q_holds_bytes s \<and> Q_reflects_writes s \<and> Q_elem_size s \<and> 
                                      Q_reflects_ownD s )"


 
lemmas Q_lemmas = Q_holds_bytes_def Q_reflects_writes_def Q_reflects_ownD_def
                  Q_structure_def Q_relates_tempR_def
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

(*standard def of pos_of_H*)

definition "H_inside_Q s     \<equiv> H s=end(last(q s))"

definition "H_outside_Q s    \<equiv> (T s>end(last(q s))\<longrightarrow>(H s>0 \<and> H s\<ge>end(last(q s)) \<and> H s<T s))
                             \<and> (T s<end(last(q s))\<longrightarrow>((H s>end(last(q s))\<and>H s<N) \<or> (H s<T s \<and> H s>0)))"

definition "H_inside_R s     \<equiv> H s=end(tempR s)"

definition "H_outside_R s    \<equiv> (T s>end(tempR s)\<longrightarrow>(H s>0 \<and> H s\<ge>end(tempR s) \<and> H s<T s))
                             \<and> (T s<end(tempR s)\<longrightarrow>((H s>end(tempR s)\<and>H s<N) \<or> (H s<T s \<and> H s>0)))"

definition "H_position_inv s \<equiv> q s\<noteq>[]\<longrightarrow> (H s > 0 \<and> (H_outside_Q s \<or> H_inside_Q s))"

definition "H_position_R s   \<equiv> q s=[]\<longrightarrow> (H s > 0 \<and> (H_outside_R s \<or> H_inside_R s))"

definition "H_position_W s   \<equiv> H s = end(tempW s)"
















(*OwnB wrt Tail, Q, Reader pcR*)


definition "Tail_and_ownB_idleR s       \<equiv> (q s\<noteq>[]\<and>end(last(q s))<T s \<and> T s>0) \<longrightarrow> (\<forall>i.(T s\<le>i \<and> i<N)\<longrightarrow>ownB s i=Q)"

definition "Tail_and_ownB_not_idleR_1 s \<equiv> T s\<noteq>fst(tempR s) \<longrightarrow> (\<forall>i.(T s\<le>i \<and> i<N)\<longrightarrow>ownB s i=Q)"

definition "Tail_and_ownB_not_idleR_2 s \<equiv> (T s=fst(tempR s)\<and>q s\<noteq>[]\<and>end(last(q s))<T s)\<longrightarrow>
                                                          (\<forall>i.(end(tempR s)\<le>i \<and> i<N)\<longrightarrow>ownB s i=Q)"

lemmas Tail_ownB_rel = Tail_and_ownB_idleR_def Tail_and_ownB_not_idleR_1_def Tail_and_ownB_not_idleR_2_def




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
                        \<circ> (setownB [(hW s,N) W])
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
                                \<and> (T s=H s \<longrightarrow> (\<forall>i.(i\<ge>0 \<and> i\<le>N)\<longrightarrow>ownB s i=B) \<and> ownT s = Q \<and> q s= [] \<and> numDeqs s = numEnqs s)
                                \<and> (T s>H s \<longrightarrow> (\<forall>i.(i\<ge>H s \<and> i<T s)\<longrightarrow>ownB s i=B))
                                \<and> (T s<H s \<longrightarrow> (\<forall>i.((i\<ge>H s \<and> i\<le>N) \<or> i<T s)\<longrightarrow>ownB s i=B))
                                \<and> (numWrites s=numEnqs s)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[]) 
                                \<and> (numEnqs s\<le>n)
                                \<and> (q s\<noteq>[]\<longrightarrow>H_inside_Q s)
"
definition "pre_A1_inv s        \<equiv> (T s=H s\<longrightarrow>((\<forall>i.(i\<ge>0 \<and> i\<le>N)\<longrightarrow>ownB s i=B) \<and> ownT s =Q \<and> q s=[]))
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (T s>H s \<longrightarrow> (\<forall>i.(i\<ge>H s \<and> i<T s)\<longrightarrow>ownB s i=B))
                                \<and> (T s<H s \<longrightarrow> (\<forall>i.((i\<ge>H s \<and> i\<le>N) \<or> i<T s)\<longrightarrow>ownB s i=B))
                                \<and> (numWrites s=numEnqs s)
                                \<and> (numEnqs s<n)
                                \<and> (q s\<noteq>[]\<longrightarrow>H_inside_Q s)
                                " 
definition "pre_A2_inv s        \<equiv> (tW s=hW s\<longrightarrow>((\<forall>i.(i\<ge>0 \<and> i\<le>N)\<longrightarrow>ownB s i=B) \<and> ownT s =Q \<and> q s=[]))
                                \<and> (tW s>hW s \<longrightarrow> (\<forall>i.(i\<ge>hW s \<and> i<tW s)\<longrightarrow>ownB s i=B))
                                \<and> (tW s<hW s \<longrightarrow> (\<forall>i.((i\<ge>hW s \<and> i\<le>N) \<or> i<tW s)\<longrightarrow>ownB s i=B))
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (numWrites s=numEnqs s)
                                \<and> (numEnqs s<n)
                                \<and> (H s=hW s)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[])
                                \<and> (q s\<noteq>[]\<longrightarrow>H_inside_Q s)
                                " 
definition "pre_A3_inv s        \<equiv> ((\<forall>i.(i\<ge>0 \<and> i\<le>N)\<longrightarrow>ownB s i=B))
                                \<and> (grd1 s)
                                \<and> (ownT s =W)
                                \<and> (numWrites s=numEnqs s)
                                \<and> (numEnqs s<n)
                                \<and> (H s=hW s) \<and> q s=[]
                                \<and> (numEnqs s=0\<longrightarrow>q s=[])
                                " 
definition "pre_A4_inv s        \<equiv> (\<forall>i.(i\<ge>hW s \<and> i<tW s)\<longrightarrow>ownB s i=B)
                                \<and> (grd2 s) \<and> (\<not>grd1 s)
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (numWrites s=numEnqs s) 
                                \<and> (numEnqs s<n)
                                \<and> (H s=hW s)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[]) 
                                \<and> (q s\<noteq>[]\<longrightarrow>H_inside_Q s)
                                " 
definition "pre_A5_inv s        \<equiv> (\<forall>i.((i\<ge>hW s \<and> i<N) \<or> i<tW s)\<longrightarrow>ownB s i=B)
                                \<and> (grd3 s) \<and> (\<not>grd1 s) \<and> (\<not>grd2 s)
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (numWrites s=numEnqs s)
                                \<and> (numEnqs s<n)
                                \<and> (H s=hW s)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[]) 
                                \<and> (q s\<noteq>[]\<longrightarrow>H_inside_Q s)
                                " 
definition "pre_A6_inv s        \<equiv> (\<forall>i.((i\<ge>hW s \<and> i<N) \<or> i<tW s)\<longrightarrow>ownB s i=B)
                                \<and> (grd4 s) \<and> (grd3 s) \<and> (\<not>grd1 s) \<and> (\<not>grd2 s)
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (numWrites s=numEnqs s) 
                                \<and> (numEnqs s<n)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[]) 
                                \<and> (q s\<noteq>[]\<longrightarrow>H_inside_Q s)
                                " 
definition "pre_A7_inv s        \<equiv> (\<forall>i.((i\<ge>hW s \<and> i<N) \<or> i<tW s)\<longrightarrow>ownB s i=B)
                                \<and> (grd5 s) \<and> (grd3 s) \<and> (\<not>grd1 s) \<and> (\<not>grd2 s) \<and> (\<not>grd4 s)
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (numWrites s=numEnqs s) 
                                \<and> (numEnqs s<n) 
                                \<and> (H s=hW s)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[]) 
                                \<and> (q s\<noteq>[]\<longrightarrow>H_inside_Q s)
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
                                \<and> (q s\<noteq>[]\<longrightarrow>H_inside_Q s)
"
definition "pre_write_inv s     \<equiv> (\<forall>i.(i\<ge>offset s \<and> i< ((offset s)+(Data s (numEnqs s))))\<longrightarrow>ownB s i=W)
                                \<and> ((tW s>hW s)\<longrightarrow>(\<forall>i.(i\<ge>((offset s)+(Data s (numEnqs s)))\<and>i<tW s)\<longrightarrow>ownB s i =B))
                                \<and> ((tW s<hW s \<and> offset s\<noteq>0)\<longrightarrow>(\<forall>i.((i\<ge>((offset s)+(Data s (numEnqs s))) \<and> i\<le>N)\<or>i<tW s)\<longrightarrow>ownB s i =B))
                                \<and> ((tW s<hW s \<and> offset s=0)\<longrightarrow>((\<forall>i.(i\<ge>((offset s)+(Data s (numEnqs s))) \<and> i<tW s)\<longrightarrow>ownB s i =B) \<and> (\<forall>i.(i\<ge>hW s \<and> i<N)\<longrightarrow>ownB s i=W)))
                                \<and> (tW s=hW s\<longrightarrow>(ownT s=W \<and> q s=[]))
                                \<and> (numWrites s=numEnqs s)
                                \<and> (numEnqs s<n)
                                \<and> (tempW_structure s)
                                \<and> (ownD s(numWrites s) =W)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[]) 
                                \<and> (offset s=hW s \<or> offset s=0)
                                \<and> (H_position_W s)
                                " 
definition "pre_enqueue_inv s   \<equiv> (\<forall>i.(i\<ge>offset s \<and> i< end(tempW s))\<longrightarrow>ownB s i=W)
                                \<and> ((tW s>hW s)\<longrightarrow>(\<forall>i.(i\<ge>end(tempW s)\<and>i<tW s)\<longrightarrow>ownB s i =B))
                                \<and> ((tW s<hW s \<and> offset s\<noteq>0)\<longrightarrow>(\<forall>i.((i\<ge>end(tempW s) \<and> i\<le>N)\<or>i<tW s)\<longrightarrow>ownB s i =B))
                                \<and> ((tW s<hW s \<and> offset s=0)\<longrightarrow>((\<forall>i.(i\<ge>end(tempW s) \<and> i<tW s)\<longrightarrow>ownB s i =B) \<and> (\<forall>i.(i\<ge>hW s \<and> i<N)\<longrightarrow>ownB s i=W)))
                                \<and> (tW s=hW s\<longrightarrow>(ownT s=W \<and> q s=[]))
                                \<and> (numWrites s=numEnqs s +1)
                                \<and> (numEnqs s<n)
                                \<and> ((ownT s = W)\<longrightarrow>q s=[])
                                \<and> (tempW_structure s)
                                \<and> (tempW_reflects_writes s)
                                \<and> (ownD s(numEnqs s) =B)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[]) 
                                \<and> (offset s=hW s \<or> offset s=0)
                                \<and> (H_position_W s)
                                " 
definition "pre_OOM_inv s       \<equiv> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (tW s>hW s \<longrightarrow> (\<forall>i.(i\<ge>tW s \<and> i<hW s)\<longrightarrow>ownB s i=B))
                                \<and> (tW s<hW s \<longrightarrow> (\<forall>i.((i\<ge>hW s \<and> i\<le>N) \<or> i<tW s)\<longrightarrow>ownB s i=B))
                                \<and> (numWrites s=numEnqs s) 
                                \<and> (numEnqs s<n)
                                \<and> (H s=hW s)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[]) 
                                " 
definition "pre_finished_inv s  \<equiv> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (numWrites s=numEnqs s)
                                \<and> (numEnqs s=n)
                                " 
definition "pre_BTS_inv s       \<equiv> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> (ownT s \<noteq>W)
                                \<and> (numWrites s=numEnqs s)
                                \<and> (numEnqs s<n)
                                \<and> (H s=hW s)
                                \<and> (numEnqs s=0\<longrightarrow>q s=[]) 
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
                              \<and> (q s\<noteq>[] \<longrightarrow>Q_describes_T s)
                              \<and> (R_owns_no_bytes s)
                              \<and> (Tail_and_ownB_idleR s)
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



                              \<and> (tempR_describes_T s)
                              \<and> (tempR_describes_ownB s)
                              \<and> (H s>0)
                              \<and> (Tail_and_ownB_not_idleR_1 s)
                              \<and> (Tail_and_ownB_not_idleR_2 s)

                              \<and> (T s\<noteq>fst(tempR s)\<longrightarrow>(\<forall>x j.(x\<in>set(q s) \<and> j<N \<and> j\<ge>T s)\<longrightarrow>end(x)<j))
                              \<and> (T s\<noteq>fst(tempR s)\<longrightarrow>end(tempR s)<T s)
                              \<and> (H_position_R s)
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



                              \<and> (tempR_describes_T s)
                              \<and> (tempR_describes_ownB s)
                              \<and> (H s>0)
                              \<and> (Tail_and_ownB_not_idleR_1 s)
                              \<and> (Tail_and_ownB_not_idleR_2 s)
                              
                              \<and> (tR s\<noteq>fst(tempR s)\<longrightarrow>(\<forall>x j.(x\<in>set(q s) \<and> j<N \<and> j\<ge>tR s)\<longrightarrow>end(x)<j))
                              \<and> (tR s\<noteq>fst(tempR s)\<longrightarrow>end(tempR s)<tR s)
                              \<and> (H_position_R s)
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
  apply(simp add:Q_boundness_def Q_describes_T_def)
  apply (metis  list.set_sel(2))
  apply(simp add:Q_gap_structure_def)
  using Q_basic_preserved2 Q_tail_props
  apply (smt (verit, ccfv_SIG) One_nat_def Suc_less_eq2 diff_Suc_1 diff_commute gr_implies_not0 not_less_less_Suc_eq zero_less_Suc zero_less_diff)
  apply(simp add:Q_offsets_differ_def)
  apply (metis (no_types, lifting) One_nat_def add.commute add_right_cancel length_tl less_diff_conv nth_tl plus_1_eq_Suc)
  apply(simp add:Q_has_no_overlaps_def)
  using Q_basic_preserved2
  apply (metis (no_types, lifting) list.set_sel(2))
  apply(simp add:Q_has_no_uroboros_def)
  apply (metis butlast_tl last_tl list.sel(2) list.set_sel(2))
  using ownB_lemma2
  apply (smt (z3) Q_basic_preserved2 Q_dequeue_def Q_holds_bytes_def Q_structure_def assms(4) end_simp len_def off_def)
  apply(simp add:Q_reflects_writes_def) 
  using Q_basic_preserved2 
  apply (metis (no_types, lifting) One_nat_def Suc_eq_plus1 add_Suc_right length_tl less_diff_conv nth_tl)
  apply(simp add:Q_elem_size_def) 
  using Q_basic_preserved2
  apply (metis One_nat_def Suc_eq_plus1 add_Suc_right length_tl less_diff_conv nth_tl)
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
apply(simp add:Q_holds_bytes_def)
apply(simp add:Q_reflects_writes_def)
apply(simp add:Q_elem_size_def)
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
  apply (metis (no_types, lifting) F.distinct(7) less_Suc_eq not_less_eq)
  apply(simp add:pre_Release_inv_def Q_reflects_writes_def)
  apply(simp add:pre_Release_inv_def Q_elem_size_def)
  apply(simp add:pre_Release_inv_def Q_reflects_ownD_def)
  apply(simp add:pre_Release_inv_def Q_basic_lemmas)
  apply(simp add:pre_Release_inv_def Q_holds_bytes_def)
  apply(simp add:pre_Release_inv_def Q_reflects_writes_def)
  apply(simp add:pre_Release_inv_def Q_elem_size_def)
  apply(simp add:pre_Release_inv_def Q_reflects_ownD_def)
  apply(simp add:pre_Release_inv_def Q_basic_lemmas)
  apply(simp add:pre_Release_inv_def Q_holds_bytes_def)
  apply(simp add:pre_Release_inv_def Q_reflects_writes_def)
  apply(simp add:pre_Release_inv_def Q_elem_size_def)
  apply(simp add:pre_Release_inv_def Q_reflects_ownD_def)
  apply(simp add:pre_Release_inv_def Q_basic_lemmas)
  apply(simp add:pre_Release_inv_def Q_holds_bytes_def)
  apply(simp add:pre_Release_inv_def Q_reflects_writes_def)
  apply(simp add:pre_Release_inv_def Q_elem_size_def)
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
                          



(*------------------------ Invariant ------------------------------------*)
definition inv  where
"inv   s \<equiv> basic_pointer_movement s 
               \<and> mainInv s
               \<and> counter_q_rel s
               \<and> counter_bounds s 
               \<and> Q_structure s
               \<and> data_index_bouded s
               \<and> H_position_inv s
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



lemma local_pre_W: 
  assumes "con_assms s"
  and "pcw = pcW s"
  and "pre_W pcw s"
  and "inv s"
  and "cW_step pcw s s'"
shows "pre_W (pcW s') s'"
  using assms apply (simp add:inv_def)
  apply(simp add:pre_W_def)
  apply(case_tac "pcW s", simp_all add:cW_step_def)
  apply(simp add:pre_A1_inv_def pre_A2_inv_def)
  apply(intro conjI impI)
  apply (metis length_greater_0_conv less_numeral_extra(3) zero_diff)
  apply(simp add:H_inside_Q_def)   
  apply(case_tac "tW s = hW s", simp_all)
  apply(case_tac "Data s (numEnqs s) \<le> N ", simp_all)
  apply(case_tac " ownT s = Q", simp_all add:H_inside_Q_def)
  apply(simp add:pre_A2_inv_def pre_A8_inv_def)
  apply(simp add:pre_A2_inv_def pre_A3_inv_def)
  apply(simp add:pre_A2_inv_def pre_A3_inv_def)
  apply(simp add:pre_A2_inv_def pre_A8_inv_def)
  apply(case_tac "hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s", simp_all)
  apply(simp add:pre_A2_inv_def pre_A4_inv_def H_inside_Q_def H_position_inv_def)
  apply metis
  apply(case_tac "tW s < hW s", simp_all)
  apply(simp add:pre_A2_inv_def pre_A5_inv_def)
  apply(simp add:H_inside_Q_def)   
  apply(simp add:pre_A2_inv_def pre_A4_inv_def H_inside_Q_def H_position_inv_def)
  apply metis
  apply(simp add:pre_A2_inv_def pre_A8_inv_def)
  apply(simp add:H_inside_Q_def)   
  apply(simp add:pre_A2_inv_def pre_A4_inv_def H_inside_Q_def H_position_inv_def)
  apply metis






  apply(simp add:pre_A3_inv_def pre_write_inv_def)
  apply(simp add:tempW_structure_def)
  apply(intro conjI impI)
  apply(simp add:tempW_basic_struct_def tempW_boundness_def tempW_def)
  apply(simp add:tempW_holds_bytes_def tempW_def Q_lemmas Q_basic_lemmas)
  apply(simp add:tempW_holds_bytes_def tempW_def Q_lemmas Q_basic_lemmas H_position_W_def)
  apply(simp add:pre_A4_inv_def pre_write_inv_def)
  apply(simp add:tempW_structure_def)
  apply(intro conjI impI)
  apply(simp add:tempW_basic_struct_def tempW_boundness_def tempW_def)
  apply(intro conjI impI)
  apply (simp add: less_diff_conv) 
  apply(simp add:tempW_gap_structure_def)
               apply clarify apply(simp add:H_inside_Q_def H_position_inv_def)
  apply (simp add: surjective tempW_def update_convs(1) update_convs(5))
  apply(simp add:tempW_offsets_differ_def tempW_def Q_lemmas Q_basic_lemmas)
  apply(simp add:H_position_inv_def H_inside_Q_def) 
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow>Data s (numDeqs s + i)>0") prefer 2
  apply (metis (no_types, lifting) add.commute less_diff_conv less_imp_add_positive trans_less_add1)
  apply(subgoal_tac "hW s = end(last(q s))") prefer 2 
  apply (metis end_simp)
  apply(subgoal_tac "last(q s) = (q s!(length(q s) -1))") prefer 2 
  apply (metis last_conv_nth)
  apply(subgoal_tac "fst(q s!(length(q s)-1)) < end(last(q s))") prefer 2
  apply (metis Nat.add_0_right Suc_diff_1 length_greater_0_conv lessI nat_add_left_cancel_less)
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow>end(last(q s))\<noteq>fst(q s!i)")
  apply metis
  apply(subgoal_tac "(\<forall>a b.((a, b)\<in>set(butlast(q s)))\<longrightarrow>a\<noteq>end(last(q s)))\<and> (fst(last(q s))\<noteq>end(last(q s)))") prefer 2 
  apply(intro conjI impI)
  apply metis
  apply (metis nat_less_le) 
  apply(subgoal_tac "\<forall>a b.((a, b)\<in>set(q s))\<longrightarrow>(\<exists>i.(i<length(q s)\<and>(q s!i) =(a, b)))") prefer 2
  apply (metis in_set_conv_nth)
  apply(subgoal_tac "\<forall>i.(i<length(q s)-1)\<longrightarrow>fst(q s!i)\<noteq>end(last(q s))") prefer 2 
  apply (metis length_butlast nth_butlast nth_mem surjective_pairing)
  apply (metis Suc_diff_1 length_greater_0_conv not_less_less_Suc_eq)
  apply(simp add:tempW_has_no_overlaps_def Q_lemmas Q_basic_lemmas) 
  apply(clarify)
  apply(intro conjI impI)
  apply(simp add:H_position_inv_def H_inside_Q_def)
  apply(case_tac "fst(hd(q s))>end(last(q s))")
  apply(subgoal_tac "Data s (numEnqs s) < tW s-hW s") prefer 2 
  apply presburger
  apply(subgoal_tac "fst(hd(q s))>end(last(q s))\<longrightarrow>end(tempW s)< fst(hd(q s))") sledgehammer




  apply(simp add:tempW_def Q_lemmas Q_basic_lemmas)
  apply clarify
  apply(simp add:tempW_holds_bytes_def tempW_def Q_lemmas Q_basic_lemmas)
  apply(simp add:tempW_offsets_differ_def tempW_def Q_lemmas Q_basic_lemmas)
  apply(simp add:H_position_def) apply clarify
  apply(subgoal_tac "\<forall>i.(i\<in>set(butlast(q s)))\<longrightarrow>end(last(q s))\<noteq>fst(i)") prefer 2
              apply (metis end_simp prod.collapse)
  apply(subgoal_tac "last(q s) = (q s!(length(q s)-1))") prefer 2
  apply (metis last_conv_nth)
  apply(subgoal_tac "snd(q s!(length(q s)-1)) =Data s (numDeqs s + (length(q s)-1))") prefer 2
  apply (meson diff_less length_greater_0_conv less_one)
  apply(subgoal_tac "Data s (numDeqs s + (length(q s)-1))>0") prefer 2 
  apply (metis (no_types, lifting) Nat.add_0_right bot_nat_0.extremum diff_less gr0I last_in_set length_greater_0_conv less_one prod.collapse)
  apply(subgoal_tac "end(last(q s))>fst(last(q s))") prefer 2
  apply (metis end_simp less_add_same_cancel1) apply simp 
  apply(subgoal_tac "numDeqs s + length (q s) - Suc 0 = numEnqs s -1") prefer 2
  apply (metis One_nat_def le_add_diff_inverse)
  sledgehammer



             apply(simp add:pre_A4_inv_def pre_write_inv_def)
  apply(simp add:tempW_structure_def)
  apply(intro conjI impI)
  apply(simp add:tempW_basic_struct_def tempW_boundness_def tempW_def)
  apply(intro conjI impI)
  apply (simp add: less_diff_conv)
  apply(simp add:tempW_gap_structure_def tempW_boundness_def tempW_def)
  apply(case_tac "hW s\<noteq>0") prefer 2 
  apply fastforce apply simp                
  sledgehammer
           apply(simp add:tempW_holds_bytes_def tempW_def Q_lemmas Q_basic_lemmas)
  
                
  defer defer
  apply(case_tac "Data s (numEnqs s) \<le> N - hW s", simp_all)
  apply(simp add:pre_A5_inv_def pre_A6_inv_def)
  apply(case_tac "Data s (numEnqs s) < tW s", simp_all)
  apply(simp add:pre_A5_inv_def pre_A7_inv_def)
  apply(simp add:pre_A5_inv_def pre_A8_inv_def)  defer defer
  apply(case_tac " N < Data s (numEnqs s)", simp_all) 
  apply(simp add:pre_A8_inv_def pre_BTS_inv_def) defer
  apply(case_tac "ownT s = W", simp_all) defer defer
  apply(case_tac "numEnqs s < n", simp_all)
  apply(simp add:pre_acquire_inv_def pre_A1_inv_def)
  apply(simp add:pre_acquire_inv_def pre_finished_inv_def)
  apply(case_tac "tW s \<noteq> T s", simp_all) defer
  apply(simp add:pre_write_inv_def pre_enqueue_inv_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas) defer
  sorry



(*writer side enqueue------------------------*)
lemma enqueue_preserves_Q_n_n:
  assumes "q s\<noteq>[]"
  and "Q_structure s"
  and "Q_enqueue s s'"
  and "numDeqs s<numEnqs s"
  and "length(q s) = numEnqs s-numDeqs s"
  and "pre_enqueue_inv s"
  and "ownD s(numEnqs s) =B"
  and "ownT s \<noteq>W"
  and "numWrites s\<ge>numReads s"
shows "Q_structure s'"
  using assms apply (simp)
  apply (case_tac "ownT s = W", simp_all)
  apply(simp add:Q_structure_def) apply(intro conjI impI)
  apply(simp add:Q_basic_lemmas) apply(intro conjI impI)
  apply(simp add:pre_enqueue_inv_def) 
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:pre_enqueue_inv_def) 
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(subgoal_tac "\<forall>i. i < length (q s) \<and> 0 < i \<longrightarrow>
        fst ((q s @ [(offset s, Data s (numEnqs s))]) ! (i - Suc 0)) +
        snd ((q s @ [(offset s, Data s (numEnqs s))]) ! (i - Suc 0)) =
        fst ((q s @ [(offset s, Data s (numEnqs s))]) ! i) \<or>
        fst ((q s @ [(offset s, Data s (numEnqs s))]) ! i) = 0") prefer 2 apply clarify 
  apply (smt (z3) Suc_lessD Suc_pred nat_neq_iff nth_append)
  apply(subgoal_tac "fst(tempW s) =end(last(q s)) \<or> fst(tempW s) =0")
  prefer 2 
  apply (metis end_simp fst_conv tempW_def)
  apply(subgoal_tac "last(q s) =(q s!(length(q s)-1))") prefer 2
  apply (metis last_conv_nth)
  apply clarify
  apply(subgoal_tac "offset s =0\<longrightarrow>(\<forall>i.(i<length(q s))\<longrightarrow>fst(q s!i)\<noteq>0)") prefer 2
  apply metis
  apply(subgoal_tac "(\<exists>i.(i<length(q s)\<and>fst(q s!i) =0))\<longrightarrow>offset s\<noteq>0") prefer 2
  apply blast
  apply(case_tac "offset s=0")
  apply (metis (no_types, lifting) One_nat_def diff_Suc_less end_simp less_antisym nat_neq_iff nth_append nth_append_length tempW_def)
  apply (metis (no_types, lifting) One_nat_def diff_Suc_less end_simp less_antisym nat_neq_iff nth_append nth_append_length tempW_def)
  apply(simp add:pre_enqueue_inv_def) 
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply (metis (no_types, lifting) less_antisym nth_append nth_append_length prod.collapse prod.inject)
  apply(simp add:pre_enqueue_inv_def) 
  apply(simp add:tempW_lemmas tempW_basic_lemmas)  apply clarify
  apply(case_tac "a = offset s \<and> b = Data s (numEnqs s)", simp_all)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply (metis (no_types, lifting) fst_eqD in_set_conv_nth less_imp_le_nat)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(case_tac "aa = offset s \<and> ba = Data s (numEnqs s)", simp_all)
  apply (metis (no_types, lifting) fst_conv in_set_conv_nth snd_conv)
  apply (metis (no_types, hide_lams))
  apply(simp add:pre_enqueue_inv_def) 
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply (metis (no_types, lifting) fst_eqD in_set_conv_nth nat_neq_iff not_add_less1)
  apply(simp add:pre_enqueue_inv_def) 
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_enqueue_inv_def) 
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(subgoal_tac "\<forall>i<length (q s).
       data_index s ((q s) ! i) = numDeqs s + i") prefer 2
  apply presburger
  apply(subgoal_tac "
       data_index s ((offset s, Data s (numEnqs s))) = numDeqs s + length (q s)")
   apply (simp add: nth_append)
  apply (metis le_add_diff_inverse less_SucE less_imp_le_nat)
  apply (metis le_add_diff_inverse less_imp_le_nat)
  apply(simp add:pre_enqueue_inv_def) 
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply (metis (no_types, lifting) le_add_diff_inverse less_SucE less_imp_le_nat nth_append nth_append_length snd_eqD)
  apply(simp add:pre_enqueue_inv_def) 
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  by (metis le_add_diff_inverse2 less_SucE less_imp_le_nat)


lemma enqueue_preserves_Q_n_o:
  assumes "q s\<noteq>[]
  \<and> Q_structure s
  \<and> Q_enqueue s s'
  \<and> numDeqs s<numEnqs s
  \<and> numWrites s\<ge>numReads s
  \<and> length(q s) = numEnqs s-numDeqs s
  \<and> pre_enqueue_inv s
  \<and> ownD s(numEnqs s) =B
  \<and> ownT s =W"
  shows "Q_structure s'"
  using assms apply (simp)
  apply (case_tac "ownT s = W", simp_all)
  apply(simp add:Q_structure_def)
  apply(intro conjI impI)
  apply(simp add:Q_basic_lemmas)
  apply(intro conjI impI) apply(simp add:pre_enqueue_inv_def)
  apply blast
  apply(simp add:pre_enqueue_inv_def)
  apply blast
  apply(simp add:pre_enqueue_inv_def)
  apply blast
  apply(simp add:pre_enqueue_inv_def)
  apply(simp add:pre_enqueue_inv_def)
  apply(simp add:pre_enqueue_inv_def)
  apply meson
  apply(simp add:pre_enqueue_inv_def)
  apply blast
  apply(simp add:pre_enqueue_inv_def)
  apply blast
  apply(simp add:pre_enqueue_inv_def)
  by blast


lemma enqueue_preserves_Q_e_o:
  assumes "q s=[]
  \<and> Q_structure s
  \<and> Q_enqueue s s'
  \<and> numDeqs s=numEnqs s
  \<and> length(q s) = numEnqs s-numDeqs s
  \<and> pre_enqueue_inv s
  \<and> numWrites s\<ge>numReads s
  \<and> ownD s(numEnqs s) =B
  \<and> ownT s =W"
  shows "Q_structure s'"
  using assms apply simp
  apply(case_tac "ownT s = W", simp_all)
  apply(simp add:Q_structure_def) apply(intro conjI impI)
  apply(simp add:Q_basic_lemmas) apply(intro conjI impI)
  apply(simp add:pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  apply(simp add:pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  apply (metis gr0I)
  apply(simp add:pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  apply(simp add:Q_holds_bytes_def)
  apply(simp add:pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  apply(simp add:Q_reflects_writes_def)
  apply(simp add:pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  apply(simp add:Q_elem_size_def)
  apply(simp add:pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  by(simp add:Q_reflects_ownD_def)


lemma enqueue_preserves_Q_e_n:
  assumes "q s=[]
  \<and> Q_structure s
  \<and> Q_enqueue s s'
  \<and> numDeqs s=numEnqs s
  \<and> length(q s) = numEnqs s-numDeqs s
  \<and> pre_enqueue_inv s
  \<and> numWrites s\<ge>numReads s
  \<and> ownD s(numEnqs s) =B
  \<and> ownT s \<noteq>W"
  shows "Q_structure s'"
  using assms apply simp
  apply(case_tac "ownT s = W", simp_all)
  apply(simp add:Q_structure_def) apply(intro conjI impI)
  apply(simp add:Q_basic_lemmas) apply(intro conjI impI)
  apply(simp add:pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  apply(simp add:pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  apply (metis gr0I)
  apply(simp add:pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  apply(simp add:Q_holds_bytes_def)
  apply(simp add:pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  apply(simp add:Q_reflects_writes_def)
  apply(simp add:pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  apply(simp add:Q_elem_size_def)
  apply(simp add:pre_enqueue_inv_def tempW_lemmas tempW_basic_lemmas)
  by(simp add:Q_reflects_ownD_def)


lemma enqueue_preserves_Q:
  assumes "Q_structure s
  \<and> Q_enqueue s s'
  \<and> length(q s) = numEnqs s-numDeqs s
  \<and> pre_enqueue_inv s
  \<and> numWrites s\<ge>numReads s
  \<and> numEnqs s\<ge>numDeqs s
  \<and> ownD s(numEnqs s) =B"
  shows "Q_structure s'"
  using assms apply simp
  apply(case_tac "q s=[]")
   apply(case_tac[!] "ownT s = W", simp_all) 
     defer defer defer
(*4*)
  apply(subgoal_tac "q s\<noteq>[]
  \<and> Q_structure s
  \<and> Q_enqueue s s'
  \<and> numDeqs s<numEnqs s
  \<and> length(q s) = numEnqs s-numDeqs s
  \<and> pre_enqueue_inv s
  \<and> numWrites s\<ge>numReads s
  \<and> ownD s(numEnqs s) =B
  \<and> ownT s \<noteq>W") using enqueue_preserves_Q_n_n 
  apply presburger
  apply (metis assms length_greater_0_conv zero_less_diff) defer defer
(*3*)
  apply(subgoal_tac "q s\<noteq>[]
  \<and> Q_structure s
  \<and> Q_enqueue s s'
  \<and> numDeqs s<numEnqs s
  \<and> length(q s) = numEnqs s-numDeqs s
  \<and> pre_enqueue_inv s
  \<and> numWrites s\<ge>numReads s
  \<and> ownD s(numEnqs s) =B
  \<and> ownT s =W") prefer 2 
  apply (metis assms length_greater_0_conv zero_less_diff) using enqueue_preserves_Q_n_o
proof -
assume a1: "Q_structure s \<and> s' = s \<lparr>ownT := Q, numEnqs := Suc (numEnqs s), ownB := \<lambda>i. if ownB s i = W then Q else ownB ((if ownT s = W then ownT_update (\<lambda>_. Q) else (\<lambda>s. s\<lparr>ownT := ownT s\<rparr>)) s \<lparr>numEnqs := Suc (numEnqs s)\<rparr>) i, pcW := idleW, q := q s @ [(offset s, Data s (numEnqs s))]\<rparr> \<and> length (q s) = numEnqs s - numDeqs s \<and> pre_enqueue_inv s \<and> numReads s \<le> numWrites s \<and> numDeqs s \<le> numEnqs s \<and> ownD s (numEnqs s) = B"
assume "q s \<noteq> []"
  assume a2: "ownT s = W"
  assume a3: "q s \<noteq> [] \<and> Q_structure s \<and> Q_enqueue s s' \<and> numDeqs s < numEnqs s \<and> length (q s) = numEnqs s - numDeqs s \<and> pre_enqueue_inv s \<and> numReads s \<le> numWrites s \<and> ownD s (numEnqs s) = B \<and> ownT s = W"
  have "\<forall>r. W \<noteq> ownT s \<or> B \<noteq> ownD s (numEnqs s) \<or> \<not> pre_enqueue_inv s \<or> Q_structure r \<or> \<not> numReads s \<le> numWrites s \<or> \<not> numDeqs s < numEnqs s \<or> \<not> Q_enqueue s r \<or> \<not> Q_structure s \<or> [] = q s"
    using a1 by (smt (z3) enqueue_preserves_Q_n_o)
  then have "Q_structure (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s), ownB := \<lambda>n. if ownB s n = W then Q else ownB ((if ownT s = W then ownT_update (\<lambda>f. Q) else (\<lambda>r. r\<lparr>ownT := ownT r\<rparr>)) s \<lparr>numEnqs := Suc (numEnqs s)\<rparr>) n, pcW := idleW, q := q s @ [(offset s, Data s (numEnqs s))]\<rparr>)"
    using a3 a1 by (metis (full_types))
  then show "Q_structure (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s), ownB := \<lambda>n. if ownB s n = W then Q else ownB (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s)\<rparr>) n, pcW := idleW, q := q s @ [(offset s, Data s (numEnqs s))]\<rparr>)"
    using a2 by presburger
next
  show "Q_structure s \<and>
    s' = s
    \<lparr>numEnqs := Suc (numEnqs s),
       ownB :=
         \<lambda>i. if ownB s i = W then Q
             else ownB
                   ((if ownT s = W then ownT_update (\<lambda>_. Q) else (\<lambda>s. s\<lparr>ownT := ownT s\<rparr>))
                     s
                    \<lparr>numEnqs := Suc (numEnqs s)\<rparr>)
                   i,
       pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr> \<and>
    numEnqs s \<le> numDeqs s \<and>
    pre_enqueue_inv s \<and>
    numReads s \<le> numWrites s \<and> numDeqs s \<le> numEnqs s \<and> ownD s (numEnqs s) = B \<Longrightarrow>
    q s = [] \<Longrightarrow>
    ownT s \<noteq> W \<Longrightarrow>
    (\<And>s s'.
        q s \<noteq> [] \<and>
        Q_structure s \<and>
        Q_enqueue s s' \<and>
        numDeqs s < numEnqs s \<and>
        numReads s \<le> numWrites s \<and>
        length (q s) = numEnqs s - numDeqs s \<and>
        pre_enqueue_inv s \<and> ownD s (numEnqs s) = B \<and> ownT s = W \<Longrightarrow>
        Q_structure s') \<Longrightarrow>
    Q_structure
     (s\<lparr>numEnqs := Suc (numEnqs s),
          ownB :=
            \<lambda>i. if ownB s i = W then Q
                else ownB (s\<lparr>ownT := ownT s, numEnqs := Suc (numEnqs s)\<rparr>) i,
          pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr>)"
(*2*)
  apply(subgoal_tac "q s=[]
  \<and> Q_structure s
  \<and> Q_enqueue s s'
  \<and> numEnqs s = numDeqs s
  \<and> length(q s) = numEnqs s-numDeqs s
  \<and> pre_enqueue_inv s
  \<and> numWrites s\<ge>numReads s
  \<and> ownD s(numEnqs s) =B
  \<and> ownT s \<noteq>W") prefer 2 
    apply(subgoal_tac "q s=[]") prefer 2 apply blast
    apply(subgoal_tac "ownT s \<noteq>W") prefer 2 apply blast
    apply(subgoal_tac "ownD s(numEnqs s) =B") prefer 2 apply blast
    apply(subgoal_tac "pre_enqueue_inv s") prefer 2 apply blast
    apply(subgoal_tac "length(q s) = numEnqs s-numDeqs s") prefer 2 using assms apply blast 
    apply(subgoal_tac "Q_structure s") prefer 2 apply blast
    apply(subgoal_tac "Q_enqueue s s'") prefer 2 using assms apply blast
    apply(subgoal_tac "q s=[]\<longrightarrow>length(q s) = 0") prefer 2 
    apply blast
    apply(subgoal_tac "numEnqs s = numDeqs s") 
    apply blast
    apply(subgoal_tac "q s\<noteq>[]\<longrightarrow>length(q s)\<ge>0") prefer 2 
    apply blast
    apply(subgoal_tac "q s=[]\<longrightarrow>length(q s) =0") prefer 2
    apply blast 
    apply(subgoal_tac "length(q s)\<ge>0") prefer 2
    apply blast
    apply(subgoal_tac "numEnqs s \<ge>0") prefer 2
    apply blast
    apply(subgoal_tac "numDeqs s \<ge>0") prefer 2
    apply blast
    apply(subgoal_tac "(length(q s) = numEnqs s-numDeqs s \<and> length(q s)\<ge>0 \<and> 
                      numEnqs s\<ge>0 \<and> numDeqs s\<ge>0 \<and> length(q s) = 0)\<longrightarrow>numEnqs s-numDeqs s=0") prefer 2
    apply presburger 
    using dual_order.antisym apply blast
    using enqueue_preserves_Q_e_n 
  proof -
    assume a1: "Q_structure s \<and> s' = s \<lparr>numEnqs := Suc (numEnqs s), ownB := \<lambda>i. if ownB s i = W then Q else ownB ((if ownT s = W then ownT_update (\<lambda>_. Q) else (\<lambda>s. s\<lparr>ownT := ownT s\<rparr>)) s \<lparr>numEnqs := Suc (numEnqs s)\<rparr>) i, pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr> \<and> numEnqs s \<le> numDeqs s \<and> pre_enqueue_inv s \<and> numReads s \<le> numWrites s \<and> numDeqs s \<le> numEnqs s \<and> ownD s (numEnqs s) = B"
    assume "q s = []"
    assume a2: "ownT s \<noteq> W"
    assume a3: "q s = [] \<and> Q_structure s \<and> Q_enqueue s s' \<and> numEnqs s = numDeqs s \<and> length (q s) = numEnqs s - numDeqs s \<and> pre_enqueue_inv s \<and> numReads s \<le> numWrites s \<and> ownD s (numEnqs s) = B \<and> ownT s \<noteq> W"
    then have "\<forall>r. numDeqs s - numDeqs s \<noteq> length (q s) \<or> B \<noteq> ownD s (numEnqs s) \<or> Q_structure r \<or> \<not> Q_enqueue s r \<or> [] \<noteq> q s"
      by (metis (full_types) enqueue_preserves_Q_e_n)
    then have "Q_structure (s\<lparr>numEnqs := Suc (numEnqs s), ownB := \<lambda>n. if ownB s n = W then Q else ownB ((if ownT s = W then ownT_update (\<lambda>f. Q) else (\<lambda>r. r\<lparr>ownT := ownT r\<rparr>)) s \<lparr>numEnqs := Suc (numEnqs s)\<rparr>) n, pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr>)"
      using a3 a1 by (metis (full_types))
    then show ?thesis
      using a2 by presburger
  qed
next 
(*1*)
  show "Q_structure s \<and>
    s' = s
    \<lparr>ownT := Q, numEnqs := Suc (numEnqs s),
       ownB :=
         \<lambda>i. if ownB s i = W then Q
             else ownB
                   ((if ownT s = W then ownT_update (\<lambda>_. Q) else (\<lambda>s. s\<lparr>ownT := ownT s\<rparr>))
                     s
                    \<lparr>numEnqs := Suc (numEnqs s)\<rparr>)
                   i,
       pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr> \<and>
    numEnqs s \<le> numDeqs s \<and>
    pre_enqueue_inv s \<and>
    numReads s \<le> numWrites s \<and> numDeqs s \<le> numEnqs s \<and> ownD s (numEnqs s) = B \<Longrightarrow>
    q s = [] \<Longrightarrow>
    ownT s = W \<Longrightarrow>
    (\<And>s s'.
        q s \<noteq> [] \<and>
        Q_structure s \<and>
        Q_enqueue s s' \<and>
        numDeqs s < numEnqs s \<and>
        numReads s \<le> numWrites s \<and>
        length (q s) = numEnqs s - numDeqs s \<and>
        pre_enqueue_inv s \<and> ownD s (numEnqs s) = B \<and> ownT s = W \<Longrightarrow>
        Q_structure s') \<Longrightarrow>
    Q_structure
     (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s),
          ownB :=
            \<lambda>i. if ownB s i = W then Q
                else ownB (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s)\<rparr>) i,
          pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr>)"
  apply(subgoal_tac "q s=[]
  \<and> Q_structure s
  \<and> Q_enqueue s s'
  \<and> numDeqs s=numEnqs s
  \<and> length(q s) = numEnqs s-numDeqs s
  \<and> pre_enqueue_inv s
  \<and> ownD s(numEnqs s) =B
  \<and> ownT s =W") prefer 2 
    using assms verit_la_disequality apply blast using enqueue_preserves_Q_e_o
proof -
assume a1: "Q_structure s \<and> s' = s \<lparr>ownT := Q, numEnqs := Suc (numEnqs s), ownB := \<lambda>i. if ownB s i = W then Q else ownB ((if ownT s = W then ownT_update (\<lambda>_. Q) else (\<lambda>s. s\<lparr>ownT := ownT s\<rparr>)) s \<lparr>numEnqs := Suc (numEnqs s)\<rparr>) i, pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr> \<and> numEnqs s \<le> numDeqs s \<and> pre_enqueue_inv s \<and> numReads s \<le> numWrites s \<and> numDeqs s \<le> numEnqs s \<and> ownD s (numEnqs s) = B"
  assume "q s = []"
assume a2: "ownT s = W"
assume a3: "q s = [] \<and> Q_structure s \<and> Q_enqueue s s' \<and> numDeqs s = numEnqs s \<and> length (q s) = numEnqs s - numDeqs s \<and> pre_enqueue_inv s \<and> ownD s (numEnqs s) = B \<and> ownT s = W"
then have "\<forall>r. B \<noteq> ownD s (numEnqs s) \<or> Q_structure r \<or> \<not> Q_enqueue s r"
using a1 enqueue_preserves_Q_e_o by blast
  then have "Q_structure (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s), ownB := \<lambda>n. if ownB s n = W then Q else ownB ((if ownT s = W then ownT_update (\<lambda>f. Q) else (\<lambda>r. r\<lparr>ownT := ownT r\<rparr>)) s \<lparr>numEnqs := Suc (numEnqs s)\<rparr>) n, pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr>)"
using a3 a1 by (metis (full_types))
  then show ?thesis
    using a2 by presburger
qed
qed




(*----------enqueue end-----------------------*)

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


lemma data_index_reduce: "data_index
                   (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
                        ownD :=
                          \<lambda>i. if i = numWrites s then B
                              else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>)
                                    i\<rparr>) = data_index s"
  by simp

lemma data_index_reduce2: "
s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
          ownD :=
            \<lambda>i. if i = numWrites s then B
                else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i,
          data_index :=
            \<lambda>x. if (offset s, Data s (numEnqs s)) = x then numEnqs s
                else data_index
                      (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
                           ownD :=
                             \<lambda>i. if i = numWrites s then B
                                 else ownD
                                       (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>)
                                       i\<rparr>) x \<rparr>=
s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue,
          ownD :=
            \<lambda>i. if i = numWrites s then B
                else ownD (s\<lparr>numWrites := Suc (numWrites s), pcW := Enqueue\<rparr>) i,
          data_index :=
            \<lambda>x. if (offset s, Data s (numEnqs s)) = x then numEnqs s
                else data_index s x\<rparr>

"
  using data_index_reduce apply simp 
  by (metis data_index_reduce)

lemma write_doesnt_change_Q_struct:
  assumes "con_assms s"
  and "pcw = Write"
  and "pre_write_inv s"
  and "Q_structure s"
  and "numEnqs s - numDeqs s = length (q s)"
  and "(\<forall>i. (i < numReads s \<longrightarrow> ownD s i = R) \<and>
            (numReads s \<le> i \<and> i < numWrites s \<longrightarrow> ownD s i = B) \<and> 
            (numWrites s \<le> i \<and> i < n \<longrightarrow> ownD s i = W))"
  and " numReads s \<le> numWrites s \<and> numReads s \<le> n \<and> numWrites s \<le> n" 
  and "B_write s s'"
  and "tempW_structure s"
shows "Q_structure s'"
  using assms apply(simp add:pre_write_inv_def con_assms_def)
  apply(simp add:Q_structure_def)
  apply(intro conjI impI)
  apply(simp add:Q_basic_lemmas)
  apply(simp add:Q_holds_bytes_def) defer
  apply(simp add:Q_elem_size_def)
  apply(simp add:Q_reflects_ownD_def)
  apply(simp add:Q_reflects_writes_def)
  apply(simp add:tempW_lemmas tempW_basic_lemmas)
  by (metis fst_conv)



  
  
  sorry


lemma inv_holds_for_W: 
  assumes "con_assms s"
  and "pcw = pcW s"
  and "pre_W pcw s"
  and "inv s"
  and "cW_step pcw s s'"
shows "inv s'"
  using assms apply(simp add:inv_def)
  apply(intro conjI impI)
  apply(simp add:Q_lemmas Q_basic_lemmas cW_step_def)
  apply(case_tac "pcW s", simp_all)
  apply (metis (no_types, hide_lams) F.distinct(3) PCW.simps(185) pre_A3_inv_def pre_W_def)
  apply(simp add:pre_W_def pre_A4_inv_def)
  apply (simp add: le_add_diff_inverse2 less_diff_conv)
  apply(simp add:pre_W_def pre_A6_inv_def)
  apply (metis Nat.le_diff_conv2 add.commute)
  apply(simp add:pre_W_def pre_A7_inv_def)
  apply(case_tac "numEnqs s<n", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(simp add:pre_W_def pre_A7_inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas cW_step_def)
  apply(case_tac "pcW s", simp_all)
  apply(case_tac "numEnqs s<n", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(simp add:pre_W_def pre_A7_inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas cW_step_def)
  apply(case_tac "pcW s", simp_all)
  apply(case_tac "numEnqs s<n", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(simp add:pre_W_def pre_A7_inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas cW_step_def)
  apply(case_tac "pcW s", simp_all)
  apply(case_tac "numEnqs s<n", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(simp add:pre_W_def pre_A7_inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas cW_step_def) (*11*)
  apply(case_tac "pcW s", simp_all)
  apply(case_tac "tW s = hW s \<and> Data s (numEnqs s) \<le> N", simp_all)
  apply(case_tac "ownT s = Q", simp_all)   
  apply(case_tac "hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s", simp_all)
  apply(case_tac "tW s < hW s", simp_all)
  apply (metis pre_A4_inv_def)
  apply(case_tac "Data s (numEnqs s) \<le> N - hW s", simp_all)
  apply(case_tac "Data s (numEnqs s) < tW s", simp_all) 
  apply (simp add: pre_A6_inv_def)   
  apply (simp add: pre_A7_inv_def)   
  apply (simp add: pre_A8_inv_def)   
  apply(case_tac "N < Data s (numEnqs s)", simp_all)
  apply(case_tac "ownT s = W", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac " tW s \<noteq> T s", simp_all) (*10*)
  apply(simp add:pre_W_def pre_A7_inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas cW_step_def)
  apply(case_tac "pcW s", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac " tW s \<noteq> T s", simp_all)
  apply(simp add:pre_W_def pre_A7_inv_def)  (*9*)
  apply(simp add:Q_lemmas Q_basic_lemmas cW_step_def)
  apply(case_tac "pcW s", simp_all)
  apply(case_tac "ownT s = W", simp_all)
  using Suc_diff_le apply presburger
  using Suc_diff_le apply presburger
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac " tW s \<noteq> T s", simp_all)  (*8*)
  apply(simp add:pre_W_def pre_A7_inv_def)
  apply(simp add:cW_step_def)
  apply(case_tac "pcW s", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac " tW s \<noteq> T s", simp_all)  (*7*)
  apply(simp add:pre_W_def pre_A7_inv_def)
  apply(simp add:cW_step_def)
  apply(case_tac "pcW s", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac " tW s \<noteq> T s", simp_all)  (*6*)
  apply(simp add:pre_W_def pre_write_inv_def)
  apply(simp add:cW_step_def)
  apply(case_tac "pcW s", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac " tW s \<noteq> T s", simp_all)  (*5*)
  apply(simp add:pre_W_def cW_step_def) apply(case_tac "pcW s", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(simp add:pre_write_inv_def)        (*4*)
  apply(simp add:pre_W_def pre_write_inv_def)
  apply(simp add:cW_step_def)
  apply(case_tac "pcW s", simp_all)
  apply(case_tac "ownT s = W", simp_all)
  apply(simp add:pre_enqueue_inv_def)  
  apply(simp add:pre_enqueue_inv_def)  
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac " tW s \<noteq> T s", simp_all)  (*3*)
  apply(simp add:pre_W_def pre_write_inv_def)
  apply(simp add:cW_step_def)
  apply(case_tac "pcW s", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac " tW s \<noteq> T s", simp_all)  (*2*)
   defer
  apply(simp add:cW_step_def)
  apply(simp add:pre_W_def) apply(case_tac "pcW s", simp_all)
  apply(case_tac "numEnqs s < n", simp_all)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  using pre_write_inv_def apply auto[1]    (*1*)
  apply(simp add:cW_step_def)
  apply(case_tac "pcW s", simp_all)
  apply(simp add:pre_W_def pre_A1_inv_def)
  apply(subgoal_tac "Q_structure s=Q_structure s'")
  apply meson apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_W_def pre_A2_inv_def)
  apply(case_tac "tW s = hW s", simp_all)
  apply(subgoal_tac "Q_structure s=Q_structure s'")
  apply meson apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(case_tac "hW s < tW s \<and> Data s (numEnqs s) < tW s - hW s", simp_all)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(case_tac " tW s < hW s", simp_all)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_W_def pre_A3_inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply (metis F.distinct(3))
  apply(simp add:pre_W_def pre_A4_inv_def)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply (metis (no_types, lifting) F.distinct(11) Suc_lessD add.commute less_diff_conv less_trans_Suc)
  apply(case_tac "Data s (numEnqs s) \<le> N - hW s", simp_all)
  apply(simp add:pre_W_def pre_A5_inv_def)  
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_W_def pre_A6_inv_def)  
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply (metis F.distinct(11) le_trans less_eq_Suc_le)
  apply(simp add:pre_W_def pre_A7_inv_def)  
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply (metis (no_types, hide_lams) F.distinct(11) less_Suc_eq less_trans_Suc not_less_eq)
  apply(case_tac "N < Data s (numEnqs s)", simp_all)
  apply(simp add:pre_W_def pre_A8_inv_def) 
  apply (metis leD)
  apply(simp add:pre_W_def pre_A8_inv_def) 
  apply(simp add:Q_lemmas Q_basic_lemmas)
  defer
  apply(case_tac "numEnqs s < n", simp_all) 
  apply(simp add:pre_W_def pre_acquire_inv_def) 
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(simp add:pre_W_def pre_acquire_inv_def) 
  apply(simp add:Q_lemmas Q_basic_lemmas)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  apply(simp add:pre_W_def pre_OOM_inv_def) 
    apply(simp add:Q_lemmas Q_basic_lemmas)       (*this case is concerning pre_write *)
  apply(simp add:pre_W_def pre_write_inv_def)
 
  apply(subgoal_tac "con_assms s
  \<and> pcw = Write
  \<and> pre_write_inv s
  \<and> Q_structure s
  \<and> numEnqs s - numDeqs s = length (q s)
  \<and> (\<forall>i. (i < numReads s \<longrightarrow> ownD s i = R) \<and>
            (numReads s \<le> i \<and> i < numWrites s \<longrightarrow> ownD s i = B) \<and> 
            (numWrites s \<le> i \<and> i < n \<longrightarrow> ownD s i = W))
  \<and> numReads s \<le> numWrites s \<and> numReads s \<le> n \<and> numWrites s \<le> n
  \<and> B_write s s'
  \<and> tempW_structure s")  
  using write_doesnt_change_Q_struct
  apply (metis (no_types, lifting))
  apply (intro conjI impI)
  using assms(1) apply blast
  using assms(1) apply blast
  apply (metis (mono_tags, hide_lams) PCW.simps(195) assms(3) pre_W_def)
  apply meson
  apply fastforce
  apply presburger
  using less_imp_le_nat apply presburger
  apply meson  apply simp prefer 2 
  apply meson
  apply(simp add:B_write_def)
  apply presburger 
  
(*last subgoal!!!
apply (insert data_index_reduce2[where s = s])
*) 
  apply(subgoal_tac "Q_structure s
  \<and> Q_enqueue s s'
  \<and> length(q s) = numEnqs s-numDeqs s
  \<and> pre_enqueue_inv s
  \<and> numWrites s\<ge>numReads s
  \<and> numEnqs s\<ge>numDeqs s
  \<and> ownD s(numEnqs s) =B") prefer 2 
  apply(intro conjI impI)
  apply blast 
  apply simp
  apply presburger
  apply (simp add: pre_W_def)
  apply blast
  apply blast
  apply (simp add: pre_W_def pre_enqueue_inv_def)
  apply(intro conjI impI)
  apply(case_tac "ownT s = W ", simp_all)
   apply(case_tac[!] "q s=[]", simp_all )
     defer defer defer
(*4*)
  apply(subgoal_tac "q s\<noteq>[]
  \<and> Q_structure s
  \<and> Q_enqueue s s'
  \<and> numDeqs s<numEnqs s
  \<and> length(q s) = numEnqs s-numDeqs s
  \<and> pre_enqueue_inv s
  \<and> numWrites s\<ge>numReads s
  \<and> ownD s(numEnqs s) =B
  \<and> ownT s \<noteq>W") using enqueue_preserves_Q_n_n 
      apply presburger
  apply(intro conjI impI)
  apply blast
  apply blast apply simp
  apply (metis length_greater_0_conv zero_less_diff)
  apply linarith
  apply blast
  apply blast
  apply blast
  apply blast
    defer
(*3*)
  apply(subgoal_tac "q s\<noteq>[]
  \<and> Q_structure s
  \<and> Q_enqueue s s'
  \<and> numDeqs s<numEnqs s
  \<and> length(q s) = numEnqs s-numDeqs s
  \<and> pre_enqueue_inv s
  \<and> numWrites s\<ge>numReads s
  \<and> ownD s(numEnqs s) =B
  \<and> ownT s =W") prefer 2
  apply(intro conjI impI)
  apply blast
  apply blast apply simp
  apply (simp add: pre_enqueue_inv_def)
  apply linarith
  apply blast
  apply linarith
  apply linarith
  apply blast
  using enqueue_preserves_Q_n_o
proof -
assume a1: "s' = s \<lparr>ownT := Q, numEnqs := Suc (numEnqs s), ownB := \<lambda>i. if ownB s i = W then Q else ownB ((if ownT s = W then ownT_update (\<lambda>_. Q) else (\<lambda>s. s\<lparr>ownT := ownT s\<rparr>)) s \<lparr>numEnqs := Suc (numEnqs s)\<rparr>) i, pcW := idleW, q := q s @ [(offset s, Data s (numEnqs s))]\<rparr>"
assume "Q_structure s \<and> length (q s) = numEnqs s - numDeqs s \<and> pre_enqueue_inv s \<and> numReads s \<le> numWrites s \<and> numDeqs s \<le> numEnqs s \<and> ownD s (numEnqs s) = B"
assume a2: "ownT s = W"
assume "q s \<noteq> []"
  assume "q s \<noteq> [] \<and> Q_structure s \<and> Q_enqueue s s' \<and> numDeqs s < numEnqs s \<and> length (q s) = numEnqs s - numDeqs s \<and> pre_enqueue_inv s \<and> numReads s \<le> numWrites s \<and> ownD s (numEnqs s) = B \<and> ownT s = W"
  then have "Q_structure (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s), ownB := \<lambda>n. if ownB s n = W then Q else ownB ((if ownT s = W then ownT_update (\<lambda>f. Q) else (\<lambda>r. r\<lparr>ownT := ownT r\<rparr>)) s \<lparr>numEnqs := Suc (numEnqs s)\<rparr>) n, pcW := idleW, q := q s @ [(offset s, Data s (numEnqs s))]\<rparr>)"
    using a1 enqueue_preserves_Q_n_o by blast
  then show "Q_structure (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s), ownB := \<lambda>n. if ownB s n = W then Q else ownB (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s)\<rparr>) n, pcW := idleW, q := q s @ [(offset s, Data s (numEnqs s))]\<rparr>)"
    using a2 by presburger
next

  show "0 < N \<and> 0 < n \<and> n < N \<and> numEnqs s \<le> n \<and> (\<forall>i<n. Data s i \<le> N \<and> 0 < Data s i) \<Longrightarrow>
    pcw = Enqueue \<Longrightarrow>
    pre_W Enqueue s \<Longrightarrow>
    H s \<le> N \<and>
    T s \<le> N \<and>
    hW s \<le> N \<and>
    tW s \<le> N \<and>
    (H s = 0 \<longrightarrow> T s = 0) \<and>
    (\<forall>i. (i < numReads s \<longrightarrow> ownD s i = R) \<and>
         (numReads s \<le> i \<and> i < numWrites s \<longrightarrow> ownD s i = B) \<and>
         (numWrites s \<le> i \<and> i < n \<longrightarrow> ownD s i = W)) \<and>
    numReads s \<le> n \<and> numWrites s \<le> n \<and> (\<forall>i\<le>N. \<forall>j\<le>N. data_index s (i, j) < n) \<Longrightarrow>
    s' = s
    \<lparr>numEnqs := Suc (numEnqs s),
       ownB := \<lambda>i. if ownB s i = W then Q else ownB (s\<lparr>numEnqs := Suc (numEnqs s)\<rparr>) i, pcW := idleW,
       q := [(offset s, Data s (numEnqs s))]\<rparr> \<Longrightarrow>
    pcW s = Enqueue \<Longrightarrow>
    Q_structure s \<and>
    s\<lparr>numEnqs := Suc (numEnqs s),
        ownB :=
          \<lambda>i. if ownB s i = W then Q
              else ownB
                    ((if ownT s = W then ownT_update (\<lambda>_. Q) else (\<lambda>s. s\<lparr>ownT := ownT s\<rparr>)) s
                     \<lparr>numEnqs := Suc (numEnqs s)\<rparr>)
                    i,
        pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr> =
    s\<lparr>numEnqs := Suc (numEnqs s),
        ownB := \<lambda>i. if ownB s i = W then Q else ownB (s\<lparr>numEnqs := Suc (numEnqs s)\<rparr>) i, pcW := idleW,
        q := [(offset s, Data s (numEnqs s))]\<rparr> \<and>
    numEnqs s \<le> numDeqs s \<and>
    pre_enqueue_inv s \<and> numReads s \<le> numWrites s \<and> numDeqs s \<le> numEnqs s \<and> ownD s (numEnqs s) = B \<Longrightarrow>
    ownT s \<noteq> W \<Longrightarrow>
    q s = [] \<Longrightarrow>
    Q_structure
     (s\<lparr>numEnqs := Suc (numEnqs s),
          ownB :=
            \<lambda>i. if ownB s i = W then Q else ownB (s\<lparr>ownT := ownT s, numEnqs := Suc (numEnqs s)\<rparr>) i,
          pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr>)"
(*2*)
  apply(subgoal_tac "q s=[]
  \<and> Q_structure s
  \<and> Q_enqueue s s'
  \<and> numEnqs s = numDeqs s
  \<and> length(q s) = numEnqs s-numDeqs s
  \<and> pre_enqueue_inv s
  \<and> numWrites s\<ge>numReads s
  \<and> ownD s(numEnqs s) =B
  \<and> ownT s \<noteq>W") prefer 2 
    apply(intro conjI impI)
    apply blast
    apply blast 
    apply simp
    apply linarith
    apply (metis diff_is_0_eq' list.size(3))
    apply linarith
    apply blast
    apply blast
    apply blast
    using enqueue_preserves_Q_e_n
proof -
  assume a1: "s' = s \<lparr>numEnqs := Suc (numEnqs s), ownB := \<lambda>i. if ownB s i = W then Q else ownB (s\<lparr>numEnqs := Suc (numEnqs s)\<rparr>) i, pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr>"
  assume a2: "Q_structure s \<and> s\<lparr>numEnqs := Suc (numEnqs s), ownB := \<lambda>i. if ownB s i = W then Q else ownB ((if ownT s = W then ownT_update (\<lambda>_. Q) else (\<lambda>s. s\<lparr>ownT := ownT s\<rparr>)) s \<lparr>numEnqs := Suc (numEnqs s)\<rparr>) i, pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr> = s\<lparr>numEnqs := Suc (numEnqs s), ownB := \<lambda>i. if ownB s i = W then Q else ownB (s\<lparr>numEnqs := Suc (numEnqs s)\<rparr>) i, pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr> \<and> numEnqs s \<le> numDeqs s \<and> pre_enqueue_inv s \<and> numReads s \<le> numWrites s \<and> numDeqs s \<le> numEnqs s \<and> ownD s (numEnqs s) = B"
  assume a3: "ownT s \<noteq> W"
  assume "q s = []"
  assume a4: "q s = [] \<and> Q_structure s \<and> Q_enqueue s s' \<and> numEnqs s = numDeqs s \<and> length (q s) = numEnqs s - numDeqs s \<and> pre_enqueue_inv s \<and> numReads s \<le> numWrites s \<and> ownD s (numEnqs s) = B \<and> ownT s \<noteq> W"
  then have "\<forall>r. numDeqs s - numDeqs s \<noteq> length (q s) \<or> B \<noteq> ownD s (numEnqs s) \<or> Q_structure r \<or> \<not> Q_enqueue s r \<or> [] \<noteq> q s"
    by (metis (no_types) enqueue_preserves_Q_e_n)
  then have "Q_structure (s\<lparr>numEnqs := Suc (numEnqs s), ownB := \<lambda>n. if ownB s n = W then Q else ownB ((if ownT s = W then ownT_update (\<lambda>f. Q) else (\<lambda>r. r\<lparr>ownT := ownT r\<rparr>)) s \<lparr>numEnqs := Suc (numEnqs s)\<rparr>) n, pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr>)"
    using a4 a2 a1 by metis
  then show ?thesis
    using a3 by presburger
next
qed
(*1*)
  show "0 < N \<and> 0 < n \<and> n < N \<and> numEnqs s \<le> n \<and> (\<forall>i<n. Data s i \<le> N \<and> 0 < Data s i) \<Longrightarrow>
    pcw = Enqueue \<Longrightarrow>
    pre_W Enqueue s \<Longrightarrow>
    H s \<le> N \<and>
    T s \<le> N \<and>
    hW s \<le> N \<and>
    tW s \<le> N \<and>
    (H s = 0 \<longrightarrow> T s = 0) \<and>
    (\<forall>i. (i < numReads s \<longrightarrow> ownD s i = R) \<and>
         (numReads s \<le> i \<and> i < numWrites s \<longrightarrow> ownD s i = B) \<and>
         (numWrites s \<le> i \<and> i < n \<longrightarrow> ownD s i = W)) \<and>
    numReads s \<le> n \<and> numWrites s \<le> n \<and> (\<forall>i\<le>N. \<forall>j\<le>N. data_index s (i, j) < n) \<Longrightarrow>
    s' = s
    \<lparr>ownT := Q, numEnqs := Suc (numEnqs s),
       ownB :=
         \<lambda>i. if ownB s i = W then Q
             else ownB
                   ((if ownT s = W then ownT_update (\<lambda>_. Q) else (\<lambda>s. s\<lparr>ownT := ownT s\<rparr>)) s
                    \<lparr>numEnqs := Suc (numEnqs s)\<rparr>)
                   i,
       pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr> \<Longrightarrow>
    pcW s = Enqueue \<Longrightarrow>
    Q_structure s \<and>
    numEnqs s \<le> numDeqs s \<and>
    pre_enqueue_inv s \<and> numReads s \<le> numWrites s \<and> numDeqs s \<le> numEnqs s \<and> ownD s (numEnqs s) = B \<Longrightarrow>
    ownT s = W \<Longrightarrow>
    q s = [] \<Longrightarrow>
    Q_structure
     (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s),
          ownB := \<lambda>i. if ownB s i = W then Q else ownB (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s)\<rparr>) i,
          pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr>)"
  apply(subgoal_tac "q s=[]
  \<and> Q_structure s
  \<and> Q_enqueue s s'
  \<and> numDeqs s=numEnqs s
  \<and> length(q s) = numEnqs s-numDeqs s
  \<and> pre_enqueue_inv s
  \<and> ownD s(numEnqs s) =B
  \<and> ownT s =W") prefer 2 
    apply(intro conjI impI)
    apply blast 
    apply blast 
    apply simp
    apply linarith
    apply (metis diff_is_0_eq' list.size(3))
    apply linarith
    apply blast
    apply blast
    using enqueue_preserves_Q_e_o
proof -
  assume a1: "s' = s \<lparr>ownT := Q, numEnqs := Suc (numEnqs s), ownB := \<lambda>i. if ownB s i = W then Q else ownB ((if ownT s = W then ownT_update (\<lambda>_. Q) else (\<lambda>s. s\<lparr>ownT := ownT s\<rparr>)) s \<lparr>numEnqs := Suc (numEnqs s)\<rparr>) i, pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr>"
assume a2: "Q_structure s \<and> numEnqs s \<le> numDeqs s \<and> pre_enqueue_inv s \<and> numReads s \<le> numWrites s \<and> numDeqs s \<le> numEnqs s \<and> ownD s (numEnqs s) = B"
assume a3: "ownT s = W"
assume "q s = []"
assume "q s = [] \<and> Q_structure s \<and> Q_enqueue s s' \<and> numDeqs s = numEnqs s \<and> length (q s) = numEnqs s - numDeqs s \<and> pre_enqueue_inv s \<and> ownD s (numEnqs s) = B \<and> ownT s = W"
then have "Q_structure (s\<lparr>ownT := Q, numEnqs := Suc (numEnqs s), ownB := \<lambda>n. if ownB s n = W then Q else ownB ((if ownT s = W then ownT_update (\<lambda>f. Q) else (\<lambda>r. r\<lparr>ownT := ownT r\<rparr>)) s \<lparr>numEnqs := Suc (numEnqs s)\<rparr>) n, pcW := idleW, q := [(offset s, Data s (numEnqs s))]\<rparr>)"
using a2 a1 by (meson enqueue_preserves_Q_e_o)
then show ?thesis
using a3 by presburger
qed
qed






















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
  using assms 
  by (simp add: Q_tail_props)

lemma peculiar_27:
  assumes "Q_offsets_differ s"
  and "Q_gap_structure s"
  and "fst(hd(q s)) =0"
  and "tl(q s)\<noteq>[]"
shows "\<forall>i.(i<length(q s)\<and>i>1)\<longrightarrow>fst(tl(q s)!(i-1)) = end(tl(q s)!(i-2))"
  using assms
  by (smt (z3) Q_tail_props diff_diff_left diff_is_0_eq' le_numeral_extra(4) less_imp_diff_less one_add_one peculiar_25 zero_less_diff)

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





lemma more_peculiar_1:
  assumes "con_assms s"
  and "(T s\<noteq>fst(tempR s))\<longrightarrow>(\<forall>i.(T s\<le>i \<and> i<N)\<longrightarrow>ownB s i=Q)"
  and "tempR_structure s"
  and "Q_structure s"
  and "B_release s s'"
  and "tempR_describes_T s"
  and "q s\<noteq>[]"
  and "(T s\<noteq>fst(tempR s))"
shows "T s'=fst(hd(q s'))"
  using assms apply simp
  apply(simp add:Q_lemmas Q_basic_lemmas tempR_lemmas tempR_basic_lemmas)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all)
  apply(subgoal_tac "fst(tempR s) =0") 
  apply (metis hd_conv_nth length_greater_0_conv)
  apply(simp add:tempR_describes_T_def)
  apply(simp add:tempR_describes_T_def T_is_outside_Q_def)
  apply (metis hd_conv_nth length_greater_0_conv list.size(3))
  apply(simp add:tempR_describes_T_def T_is_outside_Q_def)
  by (metis hd_conv_nth length_greater_0_conv list.size(3))
  



lemma Release_doesnt_affect_outskirts:
  assumes "con_assms s"
  and "q s\<noteq>[]"
  and "fst(hd(q s)) =0"
  and "fst(tempR s) =T s"
  and "pre_Release_inv s"
  and "Q_structure s"
  and "tempR_structure s"
  and "B_release s s'"
shows "\<forall>i.(i\<ge>end(tempR s) \<and> i<N)\<longrightarrow>ownB s i=ownB s' i"
  using assms apply simp
  apply(case_tac "tR s \<noteq> T s", simp_all) apply(case_tac "ownT s = R", simp_all) apply(simp_all add:pre_Release_inv_def)
  by (metis end_simp tempR_describes_ownB_def)






lemma struct_of_wrap_1:
  assumes "con_assms s"
  and "Q_structure s"
  and "tempR_structure s"
  and "fst(hd(q s)) =0"
  and "fst(tempR s) \<noteq>0"
shows "\<forall>a b.((a, b)\<in>set(q s))\<longrightarrow>a+b<fst(tempR s)"
  using assms apply(simp add:Q_lemmas tempR_lemmas tempR_basic_lemmas Q_basic_lemmas)
  apply clarify
  apply(subgoal_tac "\<exists>i.(i<length(q s) \<and> (q s!i) =(a,b))") prefer 2
  apply (meson in_set_conv_nth) apply simp
  apply(subgoal_tac "snd(tempR s)>0") prefer 2 
  apply (metis Suc_pred gr0I le_trans less_eq_Suc_le less_nat_zero_code zero_less_diff)
  apply(subgoal_tac "\<forall>i.(i<length(q s)\<and>i>0)\<longrightarrow>fst(q s!i) =end(q s!(i-1))") prefer 2
  apply (metis One_nat_def end_simp hd_conv_nth length_pos_if_in_set list.size(3) nat_neq_iff) 
  apply clarify apply (elim conjE impE) 
  apply (metis less_nat_zero_code list.size(3))
  apply (metis less_nat_zero_code list.size(3))
  apply (metis less_nat_zero_code list.size(3))
  apply(subgoal_tac "\<forall>i<length (q s).
          (fst (tempR s) < fst (q s ! i) \<longrightarrow>
           fst (tempR s) + snd(tempR s)
           \<le> fst (q s ! i)) \<and>
          (fst (q s ! i) < fst (tempR s) \<longrightarrow>
           fst (q s ! i) + snd(q s!i)
           \<le> fst (tempR s))") prefer 2 
  apply presburger
  apply(subgoal_tac "\<forall>i<length (q s).
          (fst (q s ! i) < fst (tempR s) \<longrightarrow>
           fst (q s ! i) + snd(q s!i)
           \<le> fst (tempR s))") prefer 2 
  apply presburger
  apply(subgoal_tac "\<forall>i<length (q s).
          (fst (q s ! i) < fst (tempR s) \<longrightarrow>
           fst (q s ! i) + snd(q s!i)
           \<le> end (tempR s))") prefer 2
  apply (metis end_simp trans_le_add1) apply simp
  apply(subgoal_tac "(q s!i) =(a,b)") prefer 2 apply blast
  apply(subgoal_tac "\<forall>i.(i<length(q s)\<and> i>0)\<longrightarrow>fst(q s!i) =fst(q s!(i-1))+snd(q s!(i-1))") prefer 2
  using One_nat_def apply presburger
  apply(subgoal_tac "\<forall>i.(i<length(q s)\<and>i>0)\<longrightarrow>snd(q s!(i-1))>0") prefer 2
  apply (metis Nat.add_0_right Suc_diff_1 Suc_lessD gr0I n_not_Suc_n)
  apply(subgoal_tac "\<forall>i.(i<length(q s)\<and>i>0)\<longrightarrow>fst(q s!i)>fst(q s!(i-1))") prefer 2 
  apply (metis Nat.add_0_right nat_add_left_cancel_less)
  apply(subgoal_tac "last(q s) = (q s!(length(q s)-1))") prefer 2
  apply (metis Suc_diff_Suc Zero_not_Suc diff_0_eq_0 last_conv_nth length_0_conv)
  apply(subgoal_tac "a<fst(tempR s)\<longrightarrow>a+b\<le>fst(tempR s)") prefer 2 
  apply (metis fst_conv snd_conv)
  apply(subgoal_tac "a\<noteq>fst(tempR s)") prefer 2 
  apply (metis fst_conv)
  apply(subgoal_tac "\<forall>a b.(a,b)\<in>set(q s)\<longrightarrow>a\<noteq>fst(tempR s)") prefer 2
  apply (metis fst_conv in_set_conv_nth)
  apply(subgoal_tac "a+b = end(q s!i)") prefer 2 
  apply (metis end_simp fst_eqD snd_eqD)
  apply(subgoal_tac "\<forall>i<length (q s). fst (q s ! i) \<noteq> fst (tempR s)") prefer 2 
  apply blast
  apply(subgoal_tac "\<forall>i.(i<length(q s)\<and>i>0)\<longrightarrow>end(q s!(i-1)) = fst(q s!i)") prefer 2
  apply (metis  diff_add_inverse2 end_simp) 
  apply(subgoal_tac "(\<forall>i.(i<length(q s)\<and>i>0)\<longrightarrow>end(q s!(i-1)) =fst(q s!i))\<and> (\<forall>i<length (q s). fst (q s ! i) \<noteq> fst (tempR s))
            \<longrightarrow> (\<forall>i.(i<length(q s))\<longrightarrow>end(q s!(i-1)) \<noteq> fst(tempR s))") prefer 2
  apply (metis One_nat_def bot_nat_0.not_eq_extremum diff_is_0_eq' end_simp le_add2 less_one plus_1_eq_Suc zero_less_diff) 
  apply(subgoal_tac "\<forall>i.(i<(length(q s)-1))\<longrightarrow>end(q s!i) \<noteq> fst(tempR s)") prefer 2
  apply (metis add_diff_cancel_right' less_diff_conv)
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow>end(q s!i) \<noteq> fst(tempR s)") prefer 2 
  apply (metis Suc_lessI diff_Suc_1 end_simp)
  apply(subgoal_tac "\<forall>i.(i<length(q s))\<longrightarrow>end(q s!i) < fst(tempR s)") 
  apply metis 
  apply(subgoal_tac "fst(q s!0)<fst(tempR s)\<longrightarrow>end(q s!0)<fst(tempR s)") prefer 2
  apply (metis end_simp head_q0 le_neq_implies_less length_pos_if_in_set)
  apply(subgoal_tac "length(q s)>1 \<longrightarrow> end(q s!0) =fst(q s!1)") prefer 2
  apply (metis diff_self_eq_0 less_one)
  apply(subgoal_tac "(fst(q s!1) =end(q s!0) \<and> fst(q s!0)<fst(tempR s) \<and> length(q s)>1) \<longrightarrow> end(q s!1)<fst(tempR s)") prefer 2 
  apply (metis end_simp le_neq_implies_less)
  apply(subgoal_tac "\<forall>i.(length(q s)>i \<and> fst(q s!i) =end(q s!(i-1)) \<and> i>0 \<and> fst(q s!(i-1))<fst(tempR s))\<longrightarrow>end(q s!i)<fst(tempR s)") prefer 2
  apply (metis (no_types, lifting) Suc_diff_1 end_simp le_neq_implies_less less_Suc_eq not_less_eq)
  apply(subgoal_tac "\<forall>i.(i<length(q s) \<and> i>0)\<longrightarrow>fst(q s!i) = end(q s!(i-1))") prefer 2 
  apply metis
  apply(subgoal_tac "\<forall>i.(i<length(q s) \<and> i>0)\<longrightarrow>fst(q s!i) = end(q s!(i-1))\<longrightarrow>(length(q s)>i \<and> fst(q s!i) =end(q s!(i-1)) \<and> i>0 \<and> fst(q s!(i-1))<fst(tempR s))")                  
  apply (metis bot_nat_0.not_eq_extremum head_q0) apply clarify 
  apply(subgoal_tac "fst(q s!(ia-1))<fst(tempR s)")
  apply blast
  apply (induct_tac ia)
  apply (metis Suc_diff_Suc Zero_not_Suc diff_0_eq_0 hd_conv_nth length_0_conv)
  apply(subgoal_tac "fst(q s!(Suc na -1)) =fst(q s!na)") prefer 2
  using diff_Suc_1 apply presburger
  apply(subgoal_tac "(na-1)<length(q s) \<longrightarrow> fst(q s!(na-1))<fst(tempR s)") prefer 2
  apply blast 
  apply(case_tac "na-1<length(q s)")

  sorry

lemma Release_wrap_1:
  assumes "con_assms s"
  and "q s\<noteq>[]"
  and "fst(hd(q s)) =0"
  and "fst(tempR s) \<noteq>0"
  and "pre_Release_inv s"
  and "snd(tempR s) = Data s (numReads s -1)"
  and "data_index s (tempR s) = numReads s -1"
  and "ownT s = R"
  and "numEnqs s\<ge>numDeqs s"
  and "ownD s (numReads s -1) = R"
  and "numDeqs s\<le>n \<and> numDeqs s\<ge>1"
  and "numDeqs s = numReads s"
  and "pcR s=Release"
  and "tR s=T s"
  and "tempR_structure s"
  and "Q_structure s"
  and "B_release s s'"
shows "\<forall>a b j.((a,b)\<in>set(q s) \<and> end(tempR s)\<le>j \<and> j<N)\<longrightarrow>a+b<j"
  using assms apply simp
  apply(case_tac "tR s \<noteq> T s", simp_all add:pre_Release_inv_def)
  apply(case_tac "ownT s = R", simp_all) apply clarify 
  apply(subgoal_tac "j>fst(tempR s)")
  prefer 2 
  apply (metis Suc_le_lessD Suc_pred add_leD1 diff_add_inverse diff_is_0_eq' le_neq_implies_less le_trans less_nat_zero_code)
  apply(simp add:Q_lemmas tempR_lemmas tempR_basic_lemmas Q_basic_lemmas)
  using struct_of_wrap_1 
  by (smt (z3) assms(1) assms(15) assms(16) assms(4) less_imp_add_positive trans_less_add1)


lemma local_pre_R:
  assumes "con_assms s"
  and "pcr = pcR s"
  and "pre_R pcr s"
  and "inv s"
  and "cR_step pcr s s'"
shows "pre_R (pcR s') s'"
proof (cases "pcR s")
  case Release
  then show ?thesis 
    apply (simp add: pre_R_def)
  proof (cases "pcR s'")
    show "pcR s = Release \<Longrightarrow>
    pcR s' = Release \<Longrightarrow>
    case pcR s' of
    Release \<Rightarrow> pre_Release_inv s'
    | idleR \<Rightarrow> pre_dequeue_inv s'
    | Read \<Rightarrow> pre_Read_inv s'" 
        using assms by(simp add:cR_step_def pre_Read_inv_def pre_Release_inv_def pre_dequeue_inv_def)
    next 
      show "pcR s = Release \<Longrightarrow>
    pcR s' = Read \<Longrightarrow>
    case pcR s' of Release \<Rightarrow> pre_Release_inv s'
    | idleR \<Rightarrow> pre_dequeue_inv s' | Read \<Rightarrow> pre_Read_inv s'"
        using assms by(simp add:cR_step_def pre_Read_inv_def pre_Release_inv_def pre_dequeue_inv_def)
    next
      show "pcR s = Release \<Longrightarrow>
    pcR s' = idleR \<Longrightarrow>
    case pcR s' of Release \<Rightarrow> pre_Release_inv s'
    | idleR \<Rightarrow> pre_dequeue_inv s'
    | Read \<Rightarrow> pre_Read_inv s'"
        using assms apply(simp add:cR_step_def pre_Read_inv_def pre_Release_inv_def pre_dequeue_inv_def)
        apply (case_tac "tR s \<noteq> fst (tempR s)", simp_all)
        apply (case_tac[!] "ownT s = R", simp_all)
        apply (intro conjI impI)
        apply(simp add:cR_step_def pre_Read_inv_def pre_Release_inv_def pre_dequeue_inv_def RingBuffer_BD.inv_def pre_R_def)
        apply(simp add:cR_step_def pre_Read_inv_def pre_Release_inv_def pre_dequeue_inv_def RingBuffer_BD.inv_def pre_R_def)
        
        apply(simp add:cR_step_def pre_Read_inv_def pre_Release_inv_def pre_dequeue_inv_def RingBuffer_BD.inv_def pre_R_def)
        apply(simp add:Q_lemmas Q_basic_lemmas) 
              apply(subgoal_tac "(\<forall>a b j. (a, b) \<in> set (q s) \<and> j < N \<and> tR s \<le> j \<longrightarrow> a + b < j)")
        prefer 2 
        apply presburger
              apply(subgoal_tac "end(tempR s)<T s")
        prefer 2 
        apply (metis end_simp)
        apply(simp add:tempR_lemmas tempR_basic_lemmas)
        apply (metis add_lessD1 hd_conv_nth length_pos_if_in_set less_irrefl_nat less_nat_zero_code linorder_neqE_nat tempR_describes_T_def)
        apply(simp add:Q_describes_T_def)
        apply(simp add:cR_step_def pre_Read_inv_def pre_Release_inv_def pre_dequeue_inv_def RingBuffer_BD.inv_def pre_R_def)
        apply(simp add:tempR_lemmas tempR_basic_lemmas)
        apply (metis bot_nat_0.not_eq_extremum hd_conv_nth length_greater_0_conv not_add_less1 tempR_describes_T_def)
        apply(simp add:R_owns_no_bytes_def)
        apply(simp add:Tail_and_ownB_idleR_def)
        apply(simp add:cR_step_def pre_Read_inv_def pre_Release_inv_def pre_dequeue_inv_def RingBuffer_BD.inv_def pre_R_def)
        apply(simp add:Q_lemmas Q_basic_lemmas) 
        apply(simp add:tempR_lemmas tempR_basic_lemmas)
        apply safe[1]
        apply (metis add_less_same_cancel1 less_nat_zero_code tempR_describes_T_def)
        apply (metis end_simp tempR_describes_ownB_def)
        apply (metis not_add_less1 tempR_describes_T_def)
        apply (metis not_add_less1 tempR_describes_T_def)
        apply (metis end_simp tempR_describes_ownB_def)
        apply (metis not_add_less1 tempR_describes_T_def)
        apply clarsimp apply(simp add:Tail_and_ownB_not_idleR_1_def Tail_and_ownB_not_idleR_2_def)
        apply(simp add:tempR_describes_T_def T_is_outside_Q_def tempR_describes_ownB_def)
        apply clarify
        apply(subgoal_tac "fst(q s!0) = end(tempR s)") prefer 2
        apply (metis end_simp hd_conv_nth plus_nat.add_0)
        apply(subgoal_tac "\<forall>i. i < length (q s) \<and> 0 < i \<longrightarrow>
             fst (q s ! (i - Suc 0)) + snd (q s ! (i - Suc 0)) =
             fst (q s ! i)") prefer 2
        apply (metis (no_types, lifting) less_irrefl_nat)
        apply(subgoal_tac "fst(q s!(length(q s)-1)) = fst(last(q s))") prefer 2
        apply (metis last_conv_nth)
        apply (subgoal_tac "fst (last (q s)) + snd (last (q s)) > fst (hd (q s))")
        apply (meson less_or_eq_imp_le)
        apply (metis (no_types, lifting) diff_less le_add1 le_trans length_greater_0_conv less_one)
        apply (metis end_simp tempR_describes_ownB_def)
        apply(simp add:tempR_describes_ownB_def tempR_describes_T_def T_is_outside_Q_def Tail_and_ownB_not_idleR_1_def Tail_and_ownB_not_idleR_2_def)
        apply clarify
        apply(subgoal_tac "\<forall>i. i < length (q s) \<and> 0 < i \<longrightarrow>
             fst (q s ! (i - Suc 0)) + snd (q s ! (i - Suc 0)) =
             fst (q s ! i)") prefer 2
        apply (metis (no_types, lifting) gr_implies_not0)
  defer
        apply (metis (mono_tags, hide_lams) add_less_same_cancel1 hd_conv_nth length_0_conv less_nat_zero_code linorder_neqE_nat tempR_describes_T_def)
        apply (metis end_simp tempR_describes_ownB_def)
        apply (metis diff_less_Suc hd_conv_nth length_0_conv less_diff_conv linorder_neqE_nat not_less_eq tempR_describes_T_def zero_less_diff)
        apply(simp add:inv_def pre_R_def pre_Release_inv_def)
        prefer 2
        apply(simp add:inv_def pre_R_def pre_Release_inv_def)
        apply(intro conjI impI)
        apply(simp add:inv_def pre_R_def pre_Release_inv_def)
        apply(simp add:inv_def pre_R_def pre_Release_inv_def) 
        apply(subgoal_tac "con_assms s
  \<and> q s\<noteq>[]
  \<and> fst(hd(q s)) =0
  \<and> fst(tempR s) \<noteq>0
  \<and> pre_Release_inv s
  \<and> snd(tempR s) = Data s (numReads s -1)
  \<and> data_index s (tempR s) = numReads s -1
  \<and> ownT s = R
  \<and> numEnqs s\<ge>numDeqs s
  \<and> ownD s (numReads s -1) = R
  \<and> numDeqs s\<le>n \<and> numDeqs s\<ge>1
  \<and> numDeqs s = numReads s
  \<and> pcR s=Release
  \<and> tR s=T s
  \<and> tempR_structure s
  \<and> Q_structure s
  \<and> B_release s s'") apply(unfold pre_Release_inv_def)[1] 
        using Release_wrap_1 inv_def 
        apply (smt (z3) add_diff_inverse_nat add_lessD1 le_add_diff_inverse not_add_less1 struct_of_wrap_1)
        apply(intro conjI impI)
        using assms(1) apply blast
        using assms(1) apply blast 
        apply(simp add:inv_def pre_R_def pre_Release_inv_def tempR_lemmas) 
        apply (metis end_simp tempR_basic_struct_def tempR_gap_structure_def)
        apply(simp add:inv_def pre_R_def pre_Release_inv_def tempR_lemmas tempR_describes_T_def T_is_outside_Q_def) 
        apply (metis end_simp head_q0 length_0_conv less_nat_zero_code linorder_neqE_nat tempR_basic_struct_def tempR_gap_structure_def tempR_offsets_differ_def)
        apply (metis PCR.simps(7) pre_R_def)
        apply(simp add:inv_def pre_R_def pre_Release_inv_def tempR_lemmas tempR_describes_T_def T_is_outside_Q_def) 
        apply(simp add:inv_def pre_R_def pre_Release_inv_def tempR_lemmas tempR_describes_T_def T_is_outside_Q_def) 
        apply(simp add:inv_def pre_R_def pre_Release_inv_def tempR_lemmas tempR_describes_T_def T_is_outside_Q_def) 
        apply(simp add:inv_def pre_R_def pre_Release_inv_def tempR_lemmas tempR_describes_T_def T_is_outside_Q_def) 
        apply(simp add:inv_def pre_R_def pre_Release_inv_def tempR_lemmas tempR_describes_T_def T_is_outside_Q_def) 
        apply(simp add:inv_def pre_R_def pre_Release_inv_def tempR_lemmas tempR_describes_T_def T_is_outside_Q_def) 
        apply(simp add:inv_def pre_R_def pre_Release_inv_def tempR_lemmas tempR_describes_T_def T_is_outside_Q_def) 
        apply(simp add:inv_def pre_R_def pre_Release_inv_def tempR_lemmas tempR_describes_T_def T_is_outside_Q_def) 
        apply(simp add:inv_def pre_R_def pre_Release_inv_def tempR_lemmas tempR_describes_T_def T_is_outside_Q_def) 
        apply(simp add:inv_def pre_R_def pre_Release_inv_def tempR_lemmas tempR_describes_T_def T_is_outside_Q_def) 
        apply(simp add:inv_def pre_R_def pre_Release_inv_def tempR_lemmas tempR_describes_T_def T_is_outside_Q_def) 
        apply(simp add:inv_def pre_R_def pre_Release_inv_def tempR_lemmas tempR_describes_T_def T_is_outside_Q_def) 
        apply (metis (no_types, lifting) PCR.simps(7) assms(5) cR_step_def)
        (**)
 defer
        apply(simp add:R_owns_no_bytes_def)
        apply(simp add:Tail_and_ownB_idleR_def)
          apply(intro conjI impI) apply clarify apply(intro conjI impI)
        apply(simp add:pre_R_def pre_Release_inv_def)
        apply (metis end_simp tempR_describes_ownB_def)
        apply(simp add:pre_R_def pre_Release_inv_def tempR_describes_ownB_def Tail_and_ownB_not_idleR_1_def Tail_and_ownB_not_idleR_2_def)
        apply(subgoal_tac "fst (last (q s)) + snd (last (q s)) < T s")
        apply presburger apply(simp add:inv_def Q_lemmas Q_basic_lemmas tempR_lemmas tempR_basic_lemmas)
        apply clarify
        apply(subgoal_tac "end(q s!(length(q s)-1)) = end(last(q s))") prefer 2
        apply (metis last_conv_nth) 

(*should be solved by:
apply (smt (z3) Nat.add_0_right diff_add_inverse diff_is_0_eq' diff_less last_conv_nth le_neq_implies_less le_trans length_greater_0_conv less_numeral_extra(1) less_or_eq_imp_le nat_neq_iff)
so defer*) 
          defer
        apply simp apply(subgoal_tac "end(last(q s)) = (T s -1)") 
        apply (metis Suc_diff_1 Suc_leI bot_nat_0.extremum bot_nat_0.not_eq_extremum end_simp le_trans)
        apply (metis add_lessD1 diff_Suc_1 gr0_conv_Suc last_conv_nth le_less_Suc_eq length_greater_0_conv less_or_eq_imp_le)
        
(*1st subgoal is left to check, should be trivially solved outside of the proof*)
        sorry qed

next
  case Read
  then show ?thesis using assms apply (simp add:pre_R_def inv_def pre_Read_inv_def)
    apply(case_tac "pcR s'", simp_all add:cR_step_def)
    apply(simp add:pre_Release_inv_def)
    apply(intro conjI impI)
    apply(simp add:Q_lemmas Q_basic_lemmas)
    apply (metis Nat.add_0_right hd_conv_nth length_greater_0_conv)
    apply(simp add:Q_lemmas Q_basic_lemmas tempR_lemmas tempR_basic_lemmas)
    apply (metis (no_types, hide_lams))
    apply(simp add:tempR_describes_T_def T_is_outside_Q_def) 
    apply(simp add:tempR_describes_ownB_def)
    apply(simp add:Tail_and_ownB_not_idleR_1_def)
    apply(simp add:Tail_and_ownB_not_idleR_2_def)
    by metis
next
  case idleR
  then show ?thesis using assms apply (simp add:pre_R_def inv_def pre_dequeue_inv_def)
    apply(case_tac "pcR s'", simp_all add:cR_step_def Q_dequeue_def)
    apply(case_tac "q s=[]", simp_all) 
    apply(case_tac "q s=[]", simp_all)
    apply (metis assms(1) con_assms_def le_antisym less_eq_nat.simps(1) pre_dequeue_inv_def)
    apply(case_tac "q s=[]", simp_all)
    apply(simp add:pre_Read_inv_def)
    apply(intro conjI impI)
    apply(simp add:Q_lemmas Q_basic_lemmas)
    apply (simp add: hd_conv_nth)
    apply(simp add:Q_lemmas Q_basic_lemmas)
    apply (simp add: hd_conv_nth)
    apply (metis diff_is_0_eq' le_trans length_0_conv not_less_eq_eq)
    apply (metis Suc_leI length_greater_0_conv zero_less_diff)
    apply (metis Q_reflects_ownD_def Q_structure_def le_iff_add length_0_conv nat_less_le plus_nat.add_0)
    apply (metis Q_elem_size_def Q_reflects_writes_def Q_structure_def head_q0 length_pos_if_in_set less_SucI list.set_sel(1) not_less_eq snd_conv zero_le)
    apply(simp add:tempR_structure_def)
          apply(intro conjI impI)
             apply(simp add:tempR_basic_struct_def) apply(intro conjI impI) 
                apply(simp add:Q_lemmas Q_basic_lemmas tempR_basic_lemmas)
                apply(simp add:Q_lemmas Q_basic_lemmas tempR_basic_lemmas)
    apply(subgoal_tac "hd(q s) = (q s!0) \<and> hd(tl(q s)) = (q s!1)")
    apply (metis (no_types, lifting) One_nat_def diff_Suc_1 length_greater_0_conv length_tl less_one zero_less_diff)
    apply (metis One_nat_def hd_conv_nth length_greater_0_conv nth_tl)
    apply(simp add:tempR_offsets_differ_def)
    apply(simp add:Q_lemmas Q_basic_lemmas tempR_basic_lemmas)
    apply(subgoal_tac "\<forall>i.(i<(length(q s)-1))\<longrightarrow>fst(tl(q s)!i) = fst(q s!(i+1))")
    apply (metis (no_types, lifting) One_nat_def add_diff_inverse_nat hd_conv_nth length_greater_0_conv lessI less_add_eq_less less_diff_conv less_nat_zero_code less_numeral_extra(3))
    apply (metis Suc_eq_plus1 length_tl nth_tl)
    apply(simp add:tempR_has_no_overlaps_def)
    using peculiar_16 apply auto[1]
    apply(simp add:tempR_has_no_uroboros_def)
    using peculiar_21 apply auto[1]
    apply(simp add:tempR_holds_bytes_def)
    apply(simp add:tempR_reflects_writes_def)
    apply(simp add:Q_lemmas Q_basic_lemmas tempR_basic_lemmas)
    apply (metis Nat.add_0_right hd_conv_nth length_greater_0_conv)
    apply(simp add:tempR_elem_size_def)
    apply(simp add:Q_lemmas Q_basic_lemmas tempR_basic_lemmas)
    apply (metis add_cancel_right_right hd_conv_nth length_greater_0_conv)
    apply(simp add:tempR_describes_T_def T_is_outside_Q_def Q_describes_T_def)
    apply(simp add:Q_lemmas Q_basic_lemmas tempR_basic_lemmas)
    apply(case_tac "fst(hd(q s)) \<noteq>0")
    apply blast
    apply clarify
    apply(simp add: Tail_and_ownB_idleR_def)
    apply(subgoal_tac "fst(hd(q s)) \<noteq> T s") prefer 2
    apply linarith
    apply(subgoal_tac "last(q s) = (q s!(length(q s)-1))") prefer 2
    apply (metis last_conv_nth)
    apply (metis (no_types, lifting) One_nat_def Q_tail_props add_diff_cancel_right' add_gr_0 less_diff_conv zero_less_Suc)
    apply(simp add:tempR_describes_ownB_def)
    apply (metis R_owns_no_bytes_def zero_le)
    apply(simp add:Tail_and_ownB_not_idleR_1_def Tail_and_ownB_idleR_def R_owns_no_bytes_def Q_lemmas Q_basic_lemmas) 
    apply clarify
    apply(intro conjI impI)
    apply (metis (no_types, lifting) hd_in_set less_Suc_eq not_less_eq prod.collapse)
    apply(simp add:Q_describes_T_def)
    apply(simp add:Tail_and_ownB_not_idleR_2_def Tail_and_ownB_idleR_def Q_describes_T_def R_owns_no_bytes_def Q_lemmas Q_basic_lemmas) 
    apply (metis (no_types, lifting) add_leD1 add_less_same_cancel2 bot_nat_0.not_eq_extremum last_tl not_add_less2)
    apply (meson list.set_sel(2))
    apply(simp add:Q_lemmas Q_basic_lemmas Q_describes_T_def T_is_outside_Q_def)
    by (metis hd_conv_nth length_greater_0_conv plus_nat.add_0)
qed




lemma inv_holds_for_R: 
  assumes "con_assms s"
  and "pcr = pcR s"
  and "pre_R pcr s"
  and "inv s"
  and "cR_step pcr s s'"
shows "inv s'"
  using assms apply(simp add:inv_def Q_structure_def cR_step_def)
  apply(case_tac "pcR s", simp_all)
  apply(case_tac "tR s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "ownT s = R", simp_all)
      apply(intro conjI impI)
  apply(simp add:pre_R_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(simp add:pre_R_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(simp add:pre_R_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(simp add:pre_R_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(simp add:pre_R_def Q_basic_lemmas pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(simp add:pre_R_def Q_holds_bytes_def tempR_describes_ownB_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply clarify apply(intro conjI impI)
  apply (metis (no_types, lifting) less_Suc_eq not_less_eq)
  apply (metis F.distinct(7))
  apply(simp add:pre_R_def Q_reflects_writes_def tempR_describes_ownB_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(simp add:pre_R_def Q_elem_size_def tempR_describes_ownB_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(simp add:pre_R_def Q_reflects_ownD_def tempR_describes_ownB_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(simp add:pre_R_def Q_basic_lemmas pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(case_tac "ownT s = R", simp_all)
  apply(simp add:pre_R_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(intro conjI impI) 
  apply(simp add:pre_R_def Q_basic_lemmas pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(simp add:pre_R_def Q_holds_bytes_def tempR_describes_ownB_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(simp add:pre_R_def Q_reflects_writes_def tempR_describes_ownB_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(simp add:pre_R_def Q_elem_size_def tempR_describes_ownB_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(simp add:pre_R_def Q_reflects_ownD_def tempR_describes_ownB_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(intro conjI impI) 
  apply(simp add:Q_basic_struct_def Q_boundness_def pre_R_def pre_Release_inv_def)
  apply(simp add:Q_basic_struct_def Q_boundness_def pre_R_def pre_Release_inv_def)
  apply(simp add:Q_basic_struct_def Q_boundness_def pre_R_def pre_Release_inv_def)
  apply(simp add:pre_R_def Q_basic_lemmas pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(simp add:pre_R_def Q_holds_bytes_def tempR_describes_ownB_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(simp add:pre_R_def Q_reflects_writes_def tempR_describes_ownB_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(simp add:pre_R_def Q_elem_size_def tempR_describes_ownB_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(simp add:pre_R_def Q_reflects_ownD_def tempR_describes_ownB_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(case_tac " q s = []", simp_all) apply(case_tac "ownT s = Q", simp_all)
  apply(intro conjI impI)
  apply (metis Suc_diff_Suc Suc_pred length_greater_0_conv old.nat.inject zero_less_diff)
  apply (metis diff_is_0_eq' le_trans length_0_conv not_less_eq_eq)
  apply(simp add:Q_basic_struct_def Q_boundness_def pre_R_def pre_dequeue_inv_def)
  apply(intro conjI impI)
  apply (metis list.set_sel(2)) defer
  
  apply(simp add:pre_R_def Q_offsets_differ_def tempR_describes_ownB_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(subgoal_tac "\<forall>i.(i<length(q s)\<and>i>0)\<longrightarrow>(tl(q s)!(i-1)) =(q s!i)") prefer 2
  apply (simp add: Q_tail_props)
  apply(subgoal_tac "\<forall>j.(j<length(q s)\<and>j>0)\<longrightarrow>fst(tl(q s)!(j-1)) =fst(q s!j)") prefer 2
  apply (simp add: Q_tail_props) apply simp apply clarify
  apply(subgoal_tac "fst(q s!i) =fst(q s!j)")
  apply (smt (z3) Suc_less_eq diff_less_Suc less_trans_Suc)
using Q_offsets_differ_def
  apply (smt (z3) add_diff_cancel_right' add_gr_0 less_diff_conv zero_less_Suc)
  apply(simp add:pre_R_def Q_has_no_overlaps_def tempR_describes_ownB_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply (meson list.set_sel(2))
  apply(simp add:pre_R_def Q_has_no_uroboros_def Q_has_no_overlaps_def tempR_describes_ownB_def pre_Release_inv_def tempR_lemmas tempR_basic_lemmas tempR_describes_T_def T_is_outside_Q_def)
  apply(subgoal_tac "fst (last (tl (q s))) = fst(last(q s))") prefer 2
        apply (metis last_tl) 
apply(simp add:R_owns_no_bytes_def Q_offsets_differ_def Q_describes_T_def) 
  apply clarify using tail_preserves_Q_has_no_uroboros apply (simp add:Q_lemmas Q_basic_lemmas)
  apply (metis (no_types, hide_lams) Zero_not_Suc add_Suc_right add_eq_self_zero butlast_tl last_tl length_pos_if_in_set less_natE list.sel(2) list.set_sel(2) list.size(3))
  apply(simp add:pre_R_def)
      apply(subgoal_tac "Q_structure s \<and>
  pre_dequeue_inv s \<and>
  q s\<noteq>[] \<and>
  Q_dequeue s s' ") apply(unfold Q_dequeue_def) using Q_structure_preserved1 
  apply (smt (verit, ccfv_SIG) Q_basic_preserved2 Q_holds_bytes_def Q_structure_def off_def)
apply(intro conjI impI)
  apply (metis Q_structure_def)
 apply blast
apply blast
      apply simp
     apply(simp add:pre_R_def)
  apply(subgoal_tac "Q_structure s \<and>
  pre_dequeue_inv s \<and>
  q s\<noteq>[] \<and>
  Q_dequeue s s' ") apply(unfold Q_dequeue_def) using Q_structure_preserved1 
  apply (metis (no_types, lifting) Q_basic_preserved2 Q_reflects_writes_def Q_structure_def length_0_conv less_nat_zero_code off_def)
apply(intro conjI impI)
  apply (metis Q_structure_def)
 apply blast
apply blast apply simp
apply(simp add:pre_R_def)
  apply(subgoal_tac "Q_structure s \<and>
  pre_dequeue_inv s \<and>
  q s\<noteq>[] \<and>
  Q_dequeue s s' ") apply(unfold Q_dequeue_def) using Q_structure_preserved1 
  apply (metis (no_types, lifting) Q_basic_preserved2 Q_elem_size_def Q_structure_def length_0_conv less_nat_zero_code off_def)
  apply(intro conjI impI)
  apply (metis Q_structure_def)
 apply blast
apply blast apply simp
apply(simp add:pre_R_def)
  apply(subgoal_tac "Q_structure s \<and>
  pre_dequeue_inv s \<and>
  q s\<noteq>[] \<and>
  Q_dequeue s s' ") apply(unfold Q_dequeue_def) using Q_structure_preserved1
  apply (metis (no_types, lifting) Q_basic_preserved2 Q_reflects_ownD_def Q_structure_def end_simp length_0_conv less_nat_zero_code off_def)
  apply(intro conjI impI)
  apply (metis Q_structure_def)
 apply blast
apply blast apply simp
  apply(intro conjI impI) apply(simp add:pre_R_def) 
  apply (metis add.right_neutral add_Suc_right diff_diff_left)
  apply (metis diff_is_0_eq' le_trans length_0_conv not_less_eq_eq)
  apply(simp add:Q_basic_struct_def) 
  apply(intro conjI impI)
  apply(simp add:pre_R_def Q_boundness_def)
  apply (meson list.set_sel(2))
apply(simp add:pre_R_def)
apply(subgoal_tac "Q_structure s \<and>
  pre_dequeue_inv s \<and>
  q s\<noteq>[] \<and>
  Q_dequeue s s' ")apply(unfold Q_dequeue_def) using Q_structure_preserved1 
  apply (smt (verit, ccfv_SIG) Q_basic_struct_def Q_dequeue_def Q_gap_structure_def Q_structure_def less_nat_zero_code list.size(3))
 apply(intro conjI impI) 
  apply (meson Q_basic_struct_def Q_structure_def)
 apply blast
apply blast apply simp
apply(simp add:pre_R_def)
apply(subgoal_tac "Q_structure s \<and>
  pre_dequeue_inv s \<and>
  q s\<noteq>[] \<and>
  Q_dequeue s s' ")apply(unfold Q_dequeue_def) using Q_structure_preserved1 
  apply (metis (no_types, lifting) Q_basic_struct_def Q_dequeue_def Q_offsets_differ_def Q_structure_def length_0_conv less_nat_zero_code)
  apply(intro conjI impI) 
  apply (meson Q_basic_struct_def Q_structure_def)
 apply blast
apply blast apply simp
apply(simp add:pre_R_def Q_has_no_overlaps_def)
  apply (meson list.set_sel(2))
apply(simp add:pre_R_def Q_has_no_uroboros_def pre_dequeue_inv_def)
apply(simp add:pre_R_def pre_dequeue_inv_def Q_holds_bytes_def)
apply(simp add:pre_R_def pre_dequeue_inv_def Q_reflects_writes_def)
apply(simp add:pre_R_def pre_dequeue_inv_def Q_elem_size_def)
apply(simp add:pre_R_def pre_dequeue_inv_def Q_reflects_ownD_def)
  prefer 2
  defer
apply(simp add:pre_R_def pre_Read_inv_def)
  apply(intro conjI impI)
  apply (metis F.distinct(5) Suc_le_eq le_Suc_ex trans_less_add1)
  apply (metis F.distinct(5) Suc_leI le_neq_implies_less not_less_eq_eq)
     apply(simp add:Q_basic_lemmas)
apply(simp add:Q_lemmas)
apply(simp add:Q_lemmas)
apply(simp add:Q_lemmas)
  apply(simp add:Q_lemmas)

apply(subgoal_tac "Q_structure s \<and>
  pre_dequeue_inv s \<and>
  q s\<noteq>[] \<and>
  Q_dequeue s s' ")apply(unfold Q_dequeue_def) using Q_structure_preserved1 
  apply (smt (verit, ccfv_SIG) Q_basic_struct_def Q_dequeue_def Q_gap_structure_def Q_structure_def less_nat_zero_code list.size(3))
 apply(intro conjI impI) 
  apply (meson RingBuffer_BD.inv_def assms(4))
  apply(simp add:pre_dequeue_inv_def) 
  apply(simp add:pre_dequeue_inv_def) 
  apply(clarify)
  apply(subgoal_tac "fst(q s!0) =0\<longrightarrow>(\<forall>i.(i<length(q s)\<and>i>0 \<and> length(q s)>1)\<longrightarrow>
                            fst(q s!i)\<noteq>0)") prefer 2 
  apply (metis (no_types, hide_lams) peculiar_4)
by simp


















lemma global_pre_R: 
  assumes "con_assms s"
  and "pcr = pcR s"
  and "pcw = pcW s"
  and "pre_R pcr s"
  and "pre_W pcw s"
  and "inv s"
  and "cW_step pcw s s'"
shows "pre_R (pcR s') s'"
  sorry





lemma global_pre_W: 
  assumes "con_assms s"
  and "pcr = pcR s"
  and "pcw = pcW s"
  and "pre_R pcr s"
  and "pre_W pcw s"
  and "inv s"
  and "cR_step pcr s s'"
shows "pre_W (pcW s') s'"
  sorry


(*

preP \<and> preQ           preP \<and> inv
P                     P
preQ                  inv

preP \<and> preQ           preQ \<and> inv
Q                     Q
preP                  inv

preP                  
p
postP

preQ
Q
postQ

*)











lemma inv_init:
  assumes "init s"
  and "con_assms s"
  shows "inv \<and> preR \<and> preW"
  using assms 
  apply simp_all
  apply (simp_all add: inv_def Q_lemmas)
  apply(intro conjI impI)
  oops

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
  sorry




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
(*
\<and> right_to_addresses s
               \<and> no_ownB s
               \<and> H_T_ownB s
               \<and> Buff_entries_transfer_numDeqs s*)*)*)

(*
definition "last_q s      \<equiv> (q s!(length(q s)-1))"
definition "last_q_sum s  \<equiv> fst(last_q s)+snd(last_q s)"
definition "tempR_sum s   \<equiv> fst(tempR s)+snd(tempR s)"

definition "case_1 s      \<equiv> (H s=T s \<and> pcR s=idleR \<and> pcW s\<in>W_pre_acquire_set \<and> q s=[]
                               \<and> (\<forall>j.(j\<ge>0\<and>j<N)\<longrightarrow>ownB s j=B))"

definition "case_2 s      \<equiv> (H s>T s \<and> pcR s=idleR \<and> pcW s\<in>W_post_acquire_set \<and> q s\<noteq>[]
                               \<and>(\<forall>j.(j\<ge>H s\<and>j<N\<or>j<T s)\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.(j\<ge>hW s\<and>j<H s)\<longrightarrow>ownB s j=W)
                               \<and>(\<forall>j.(j\<ge>T s\<and>j<last_q_sum s)\<longrightarrow>ownB s j=Q)
                               \<and>(last_q_sum s =hW s))"
definition "case_3 s      \<equiv> (H s>T s \<and> pcR s\<noteq>idleR \<and> pcW s\<in>W_post_acquire_set \<and> q s\<noteq>[]
                               \<and>(\<forall>j.((j\<ge>H s\<and> j<N)\<or>(j\<ge>0\<and>j<T s))\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.(j\<ge>hW s\<and> j<H s)\<longrightarrow>ownB s j=W)
                               \<and>(\<forall>j.(j\<ge>tempR_sum s\<and> j<last_q_sum s)\<longrightarrow>ownB s j=Q)
                               \<and>(\<forall>j.(j\<ge>T s\<and>j<tempR_sum s)\<longrightarrow>ownB s j=R)
                               \<and>(last_q_sum s =hW s)
                               \<and>(tempR_sum s = fst(q s!0))
                               \<and>(T s=fst(tempR s)))"
definition "case_4 s      \<equiv> (H s>T s \<and> pcR s\<noteq>idleR \<and> pcW s\<in>W_pre_acquire_set \<and> q s\<noteq>[]
                               \<and>(\<forall>j.((j\<ge>H s\<and>j<N)\<or>(j\<ge>0\<and>j<T s))\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.(j\<ge>tempR_sum s\<and> j<last_q_sum s)\<longrightarrow>ownB s j=Q)
                               \<and>(\<forall>j.(j\<ge>T s\<and>j<tempR_sum s)\<longrightarrow>ownB s j=R)
                               \<and>(tempR_sum s = fst(q s!0))
                               \<and>(T s=fst(tempR s)))"

definition "case_5 s      \<equiv> (H s<T s \<and> pcR s=idleR \<and> pcW s\<in>W_pre_acquire_set \<and> q s\<noteq>[]
                               \<and>(\<forall>j.(j\<ge>H s\<and>j<T s)\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.((j\<ge>T s\<and> j<N)\<or>(j\<ge>0\<and>j<H s))\<longrightarrow>ownB s j=Q)
                               \<and> H s=last_q_sum s)"

definition "case_6 s      \<equiv>(H s<T s \<and> pcR s\<noteq>idleR \<and> pcW s\<in>W_pre_acquire_set \<and> q s\<noteq>[]
                               \<and>(\<forall>j.(j\<ge>H s\<and> j<T s)\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.((j\<ge>tempR_sum s \<and> j<N)\<or>(j\<ge>0 \<and> j<H s))\<longrightarrow>ownB s j=Q)
                               \<and>(\<forall>j.(j\<ge>T s\<and> j<tempR_sum s)\<longrightarrow>ownB s j=R)
                               \<and>(T s=fst(tempR s))
                               \<and>H s = last_q_sum s)"

definition "case_7 s      \<equiv>(H s<T s \<and> pcR s\<noteq>idleR \<and> pcW s\<in>W_pre_acquire_set 
                               \<and>(\<forall>j.(j\<ge>H s\<and> j<T s)\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.((j\<ge>tempR_sum s\<and> j<H s)\<or>(j\<ge>T s\<and> j<N))\<longrightarrow>ownB s j=Q)
                               \<and>(\<forall>j.(j\<ge>0 \<and> j<tempR_sum s)\<longrightarrow>ownB s j=R)
                               \<and>fst(tempR s) =0
                               \<and>T s\<noteq>fst(tempR s)
                               \<and>(q s\<noteq>[]\<longrightarrow>fst(q s!0) = tempR_sum s \<and> H s=last_q_sum s)
                               \<and>(q s=[]\<longrightarrow>H s =tempR_sum s))"

definition "case_8 s      \<equiv>(H s<T s \<and> pcR s=idleR \<and> pcW s\<in>W_post_acquire_set \<and> q s\<noteq>[]
                               \<and>(\<forall>j.(j\<ge>H s\<and> j<T s)\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.(j\<ge>hW s\<and>j<H s)\<longrightarrow>ownB s j=W)
                               \<and>(\<forall>j.((j\<ge>T s\<and> j<N)\<or>(j\<ge>0\<and>j<last_q_sum s))\<longrightarrow>ownB s j=Q)
                               \<and>(hW s=last_q_sum s)
                               \<and>offset s=hW s)"

definition "case_9 s      \<equiv>(H s<T s \<and> pcR s=idleR \<and> pcW s\<in>W_post_acquire_set \<and> q s\<noteq>[]
                               \<and>(\<forall>j.(j\<ge>H s\<and> j<T s)\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.((j\<ge>hW s\<and>j<N)\<or>(j\<ge>0 \<and>j<H s))\<longrightarrow>ownB s j=W)
                               \<and>(\<forall>j.(j\<ge>T s\<and> j<last_q_sum s)\<longrightarrow>ownB s j=Q)
                               \<and>offset s=0
                               \<and>last_q_sum s=hW s
                               \<and>T s=fst(q s!0))"

definition "case_10 s     \<equiv>(H s<T s \<and> pcR s\<noteq>idleR \<and> pcW s\<in>W_post_acquire_set \<and> q s\<noteq>[]
                               \<and>(\<forall>j.(j\<ge>H s\<and> j<T s)\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.(j\<ge>hW s\<and>j<H s)\<longrightarrow>ownB s j=W)
                               \<and>(\<forall>j.((j\<ge>0\<and>j<last_q_sum s)\<or>(j\<ge>tempR_sum s\<and>j<N))\<longrightarrow>ownB s j=Q)
                               \<and>(\<forall>j.(j\<ge>T s\<and>j<tempR_sum s)\<longrightarrow>ownB s j=R)
                               \<and>T s=fst(tempR s)
                               \<and>last_q_sum s=hW s)"

definition "case_11 s     \<equiv>(H s<T s \<and> pcR s\<noteq>idleR \<and> pcW s\<in>W_post_acquire_set \<and> q s\<noteq>[]
                               \<and>(\<forall>j.(j\<ge>H s\<and> j<T s)\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.(j\<ge>hW s\<and>j<H s)\<longrightarrow>ownB s j=W)
                               \<and>(\<forall>j.((j\<ge>tempR_sum s \<and>j<last_q_sum s)\<or>(j\<ge>T s\<and>j<N))\<longrightarrow>ownB s j=Q)
                               \<and>(\<forall>j.(j\<ge>0 \<and>j<tempR_sum s)\<longrightarrow>ownB s j=R)
                               \<and>fst(tempR s) =0
                               \<and>tempR_sum s=fst(q s!0)
                               \<and>last_q_sum s=hW s
                               \<and>T s\<noteq>fst(tempR s))"

definition "case_12 s     \<equiv>(H s<T s \<and> pcR s\<noteq>idleR \<and> pcW s\<in>W_post_acquire_set \<and> q s\<noteq>[]
                               \<and>(\<forall>j.(j\<ge>H s\<and> j<T s)\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.(j\<ge>hW s\<and>j<H s)\<longrightarrow>ownB s j=W)
                               \<and>(\<forall>j.((j\<ge>tempR_sum s \<and>j<last_q_sum s)\<or>(j\<ge>T s\<and>j<N))\<longrightarrow>ownB s j=Q)
                               \<and>(\<forall>j.(j\<ge>0 \<and>j<tempR_sum s)\<longrightarrow>ownB s j=R)
                               \<and>fst(tempR s) =0
                               \<and>tempR_sum s=fst(q s!0)
                               \<and>last_q_sum s=hW s
                               \<and>T s\<noteq>fst(tempR s))"
definition "ownB_cases s \<equiv> 
        case_1 s
       \<or>case_2 s
       \<or>case_3 s
       \<or>case_4 s
       \<or>case_5 s
       \<or>case_6 s
       \<or>case_7 s
       \<or>case_8 s
       \<or>case_9 s
       \<or>case_10 s
       \<or>case_11 s
       \<or>case_12 s"


definition "case_2_qempty s     \<equiv>(H s>T s \<and> pcR s=idleR \<and> pcW s\<in>W_post_acquire_set \<and> q s=[]
                               \<and>(\<forall>j.(j\<ge>H s\<and>j<N\<or>j<T s)\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.(j\<ge>T s\<and>j<H s)\<longrightarrow>ownB s j=W)
                               \<and> offset s=T s
                               \<and>(hW s\<noteq>tW s \<longrightarrow>offset s=hW s)
                               \<and>(hW s=tW s\<longrightarrow>offset s=0))"

definition "case_3_qempty s     \<equiv>(H s>T s \<and> pcR s\<noteq>idleR \<and> pcW s\<in>W_post_acquire_set \<and> q s=[]
                               \<and>(\<forall>j.((j\<ge>H s\<and> j<N)\<or>(j\<ge>0\<and>j<T s))\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.(j\<ge>hW s\<and> j<H s)\<longrightarrow>ownB s j=W)
                               \<and>(\<forall>j.(j\<ge>T s\<and>j<tempR_sum s)\<longrightarrow>ownB s j=R)
                               \<and>(tempR_sum s = hW s)
                               \<and>(T s=fst(tempR s)))"

definition "case_4_qempty s     \<equiv>(H s>T s \<and> pcR s\<noteq>idleR \<and> pcW s\<in>W_pre_acquire_set \<and> q s=[]
                               \<and>(\<forall>j.((j\<ge>H s\<and>j<N)\<or>(j\<ge>0\<and>j<T s))\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.(j\<ge>T s\<and>j<tempR_sum s)\<longrightarrow>ownB s j=R)
                               \<and>H s=tempR_sum s
                               \<and>(T s=fst(tempR s)))"

definition "case_7_qempty s     \<equiv>(H s<T s \<and> pcR s\<noteq>idleR \<and> pcW s\<in>W_pre_acquire_set \<and> q s=[]
                               \<and>(\<forall>j.(j\<ge>H s\<and> j<T s)\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.(j\<ge>T s\<and>j<N)\<longrightarrow>ownB s j=Q)
                               \<and>(\<forall>j.(j\<ge>0\<and> j<tempR_sum s)\<longrightarrow>ownB s j=R)
                               \<and>(T s\<noteq>fst(tempR s))
                               \<and>H s=tempR_sum s)"

definition "case_9_qempty s     \<equiv>(H s<T s \<and> pcR s=idleR \<and> pcW s\<in>W_post_acquire_set \<and> q s=[]
                               \<and>(\<forall>j.(j\<ge>H s\<and> j<T s)\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.((j\<ge>T s\<and>j<N)\<or>(j\<ge>0 \<and>j<H s))\<longrightarrow>ownB s j=W)
                               \<and>offset s=0
                               \<and>T s=hW s)"

definition "case_11_qempty s    \<equiv>(H s<T s \<and> pcR s=idleR \<and> pcW s\<in>W_post_acquire_set \<and> q s=[]
                               \<and>(\<forall>j.(j\<ge>H s\<and> j<T s)\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.((j\<ge>T s\<and>j<N)\<or>(j\<ge>0 \<and>j<H s))\<longrightarrow>ownB s j=W)
                               \<and>offset s=0
                               \<and>T s=hW s)"

definition "case_12_qempty s    \<equiv>(H s<T s \<and> pcR s=idleR \<and> pcW s\<in>W_post_acquire_set \<and> q s=[]
                               \<and>(\<forall>j.(j\<ge>H s\<and> j<T s)\<longrightarrow>ownB s j=B)
                               \<and>(\<forall>j.((j\<ge>T s\<and>j<N)\<or>(j\<ge>0 \<and>j<H s))\<longrightarrow>ownB s j=W)
                               \<and>offset s=0
                               \<and>T s=hW s)"

definition "ownB_cases_qempty s \<equiv> 
                                   case_2_qempty s
                                  \<or>case_3_qempty s
                                  \<or>case_4_qempty s
                                  \<or>case_7_qempty s
                                  \<or>case_9_qempty s
                                  \<or>case_11_qempty s
                                  \<or>case_12_qempty s"

definition "pre_acq_cases s     \<equiv> case_1 s \<or> case_4 s \<or> case_5 s \<or> case_6 s \<or> case_7 s
                                          \<or> case_4_qempty s \<or>case_7_qempty s"
lemmas pre_acq_case_lemmas = pre_acq_cases_def case_1_def case_4_def case_5_def case_6_def
                                               case_7_def case_4_qempty_def case_7_qempty_def

definition "post_acq_cases s    \<equiv> case_2 s \<or> case_3 s \<or> case_8 s \<or> case_9 s \<or> case_10 s
                                           \<or> case_11 s \<or> case_12 s \<or> case_2_qempty s
                                           \<or> case_3_qempty s \<or> case_9_qempty s \<or> case_11_qempty s
                                           \<or> case_12_qempty s"
lemmas post_acq_case_lemmas = post_acq_cases_def case_2_def case_3_def case_8_def case_9_def
                                                 case_10_def case_11_def case_12_def case_2_qempty_def
                                                 case_3_qempty_def case_9_qempty_def case_11_qempty_def
                                                 case_12_qempty_def

definition "pre_deq_cases s     \<equiv> case_1 s \<or>case_2 s \<or>case_5 s \<or>case_8 s \<or>case_9 s
                                  \<or>case_2_qempty s \<or>case_9_qempty s \<or>case_11_qempty s \<or>case_12_qempty s"
lemmas pre_deq_case_lemmas = pre_deq_cases_def case_1_def case_2_def case_5_def case_8_def
                                               case_9_def case_2_qempty_def case_9_qempty_def
                                               case_11_qempty_def case_12_qempty_def

definition "post_deq_cases s    \<equiv> case_3 s \<or>case_4 s \<or>case_6 s \<or>case_7 s \<or>case_10 s \<or>case_11 s \<or>case_12 s
                                  \<or>case_3_qempty s \<or>case_4_qempty s \<or>case_7_qempty s"
lemmas post_deq_case_lemmas = post_deq_cases_def case_3_def case_4_def case_6_def case_7_def case_11_def
                                               case_10_def case_12_def case_3_qempty_def 
                                               case_4_qempty_def case_7_qempty_def



definition "all_cases s \<equiv>ownB_cases_qempty s \<or> ownB_cases s"

lemmas all_cases_lemmas = all_cases_def last_q_def last_q_sum_def tempR_sum_def 
                          ownB_cases_qempty_def ownB_cases_def case_1_def
                          case_1_def case_2_def case_3_def case_4_def
                          case_5_def case_6_def case_7_def case_8_def
                          case_9_def case_10_def case_11_def case_12_def
                          case_2_qempty_def case_3_qempty_def case_4_qempty_def 
                          case_7_qempty_def case_9_qempty_def case_11_qempty_def
                          case_12_qempty_def
*)