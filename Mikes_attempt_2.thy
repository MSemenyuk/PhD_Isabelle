theory Mikes_attempt_2
imports Main HOL.List
begin 

datatype PCW =
  A1 | A2 | A3 | A4 | A5 | A6 | A7 | A8
| OK | idleW | OOM | FinishedW

datatype PCR =
  R1 | idleR 

datatype F = W | R | Q | B
datatype Pointer = Head | Tail
consts n :: nat   (*size of buffer, input*)
consts N :: nat   (*number of Arr\<^sub>W entries*)

definition "F1_set={W,B,Q,R}"

(*Recorded variables*)
record rb_state =
  H :: nat
  T :: nat
  hW ::  nat               (*local copy of W*)
  tW ::  nat               (*local copy of W*)
  q :: "(nat \<times> nat) list" 
  pcW :: PCW           (*records program counter of W*)
  pcR :: PCR           (*records program counter of W*)
  tempR :: "(nat \<times> nat)"          (*local copy of word by R*)
  arrayW:: "nat  \<Rightarrow> nat"     (*returns a word arrayW_i*)

  countW :: nat  (* the index of the next element of arrayW to be written  *)
  countR :: nat  (* how many words from arrayW the read has read or reading (i.e., retrieved)  *)
  ownAW :: "nat \<Rightarrow> F" (* ownership of arrayW indices *)
  ownB :: "nat \<Rightarrow> F" (* ownership of bytes in buffer *)

definition "con_assms s \<equiv>   0 < N \<and> 0<n \<and> countW s<n \<and> countR s\<le>countW s \<and> (\<forall>i.(i\<le>n)\<longrightarrow>arrayW s i<N \<and> arrayW s i>0)"

definition push_H :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`H := _" [200])
  where 
  "push_H v \<equiv> \<lambda>s. s \<lparr>H := v\<rparr>"

definition push_T :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`T := _" [200])
  where 
  "push_T v \<equiv> \<lambda>s. s \<lparr>T := v\<rparr>"

definition set_ownAW :: "nat \<Rightarrow> F \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`ownAW _ := _" [200])  where
  "set_ownAW ord v  \<equiv> \<lambda>s. s \<lparr> ownAW  := ((ownAW s) (ord := v))\<rparr>"

definition set_ownB :: "nat \<times> nat \<Rightarrow> F \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`ownB _ := _" [200])  where
  "set_ownB a v  \<equiv>  
      if fst a < snd a then 
          (\<lambda>s. s \<lparr> ownB  := \<lambda> i. if fst a \<le> i \<and> i < snd a then v else ownB s i \<rparr>)
      else 
          (\<lambda>s. s \<lparr> ownB  := \<lambda> i. if (fst a < i \<and> i \<le> snd a)\<or>(i=N) then ownB s i else v \<rparr>)"

definition transfer_ownB :: "F \<Rightarrow> F \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`transownB _ := _" [200]) where
  "transfer_ownB a b \<equiv> \<lambda>s. s \<lparr> ownB := \<lambda> i. if ((ownB s) i = a) then b else (ownB s) i\<rparr>"

definition set_hW :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`hW := _" [200])  where
  "set_hW v  \<equiv> \<lambda>s. s \<lparr> hW  := v\<rparr>"

definition set_tW :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`tW := _" [200])  where
  "set_tW v  \<equiv> \<lambda>s. s \<lparr> tW  := v\<rparr>"

definition set_tempR :: "(nat \<times> nat) \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`tempR := _" [200]) where
  "set_tempR v \<equiv> \<lambda>s. s \<lparr> tempR := v\<rparr>"

definition update_countW :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`countW := _" [200]) where
  "update_countW v\<equiv> \<lambda>s. s \<lparr> countW := v\<rparr>"

definition update_countR :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`countR := _" [200]) where
  "update_countR v\<equiv> \<lambda>s. s \<lparr> countR := v\<rparr>"

definition update_pcW :: "PCW \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`pcW := _" [200]) where
  "update_pcW v \<equiv> \<lambda>s. s \<lparr> pcW := v\<rparr>"

definition update_pcR :: "PCR \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`pcR := _" [200]) where
  "update_pcR v \<equiv> \<lambda>s. s \<lparr> pcR := v\<rparr>"

abbreviation update_b_err :: "rb_state \<Rightarrow> rb_state" ("ERROOM") where
  "update_b_err \<equiv> \<lambda>s. s \<lparr> pcW := OOM \<rparr>"

definition update_q :: "(nat \<times> nat) list \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`q := _" [200])
  where 
  "update_q v  \<equiv> \<lambda>s. s \<lparr>q := v\<rparr>"

lemmas functs [simp] = push_H_def push_T_def set_hW_def set_tW_def
                        update_countW_def update_countR_def
                        set_tempR_def 
                        update_pcW_def update_pcR_def
                        set_ownAW_def set_ownB_def
                        update_q_def transfer_ownB_def

(*  Define the if statement "guards"  *)

definition "off bo \<equiv> fst bo"
definition "len bo \<equiv> snd bo"
definition "grd1 s \<equiv> (tW s = hW s) \<and> (arrayW s (countW s) \<le> N)"
definition "grd2 s \<equiv> (tW s > hW s) \<and> (arrayW s (countW s) < (tW s - hW s))"
definition "grd3 s \<equiv> tW s < hW s"
definition "grd4 s \<equiv> arrayW s (countW s) \<le> N - hW s"
definition "grd5 s \<equiv> arrayW s (countW s) < tW s"
definition "no_space_for_word s \<equiv> (grd1 s \<longrightarrow> \<not>(arrayW s (countW s) \<le> N))\<and>
                                  (grd2 s \<longrightarrow> \<not>(arrayW s (countW s) < (tW s - hW s)))\<and>
                                  (grd3 s \<longrightarrow> \<not>(arrayW s (countW s) \<le> N - hW s \<or> arrayW s (countW s) < tW s))"
lemmas grd_simps [simp] = off_def len_def grd1_def grd2_def grd3_def grd4_def grd5_def no_space_for_word_def 
(***********************************************************************)





(*  Initial State  *)

definition "init s \<equiv> (H s = 0) \<and> (T s = 0) \<and> q s = [] \<and> (hW s = 0) \<and> (tW s = 0)
                        \<and> ( pcW s = idleW)
                        \<and> ( pcR s = idleR)
                        \<and> (\<forall>l. (l<n) \<longrightarrow>  ((arrayW s l > 0)\<and>(arrayW s l < N)))
                        \<and> (\<forall>i. (i<n) \<longrightarrow>  ownAW s i = W)
                        \<and> (\<forall>i. (i\<le>N) \<longrightarrow>  ownB s i = B)
                        \<and> (countW s = 0) \<and> (countR s = 0)
                        \<and> (tempR s = (0,0))"
(***********************************************************************)


(***********************************************************************)


(*Writer Thread Behaviour*)

fun rbW_step :: "PCW \<Rightarrow> rb_state \<Rightarrow> rb_state" where
  "rbW_step A1 s = ((`hW := (H s)) \<circ> (`tW := (T s)) \<circ> (`pcW := A2)) s "
| "rbW_step A2 s = (if grd1 s then (`pcW := A3)
                     else if grd2 s then (`pcW := A4) 
                     else if grd3 s then (`pcW := A5) 
                     else (`pcW :=A8)) s"
| "rbW_step A3 s = ((`T := 0) \<circ> (`H := (arrayW s (countW s))) \<circ> (`pcW := OK) 
                        \<circ> (`ownB (0,arrayW s (countW s)):= W)) s" 
| "rbW_step A4 s = ((`H := ((H s) + (arrayW s (countW s))))  \<circ> (`pcW := OK)
                        \<circ> (`ownB (H s,H s+arrayW s (countW s)) := W)) s"
| "rbW_step A5 s = (if grd4 s then (`pcW := A6)  
                     else if grd5 s then (`pcW := A7)
                     else (`pcW := A8)) s"
| "rbW_step A6 s = (`H := ((H s) + (arrayW s (countW s))) \<circ> (`pcW := OK)
                        \<circ> (`ownB (H s,H s+arrayW s (countW s)) := W)) s"
| "rbW_step A7 s = ((`H := (arrayW s (countW s))) \<circ> (`pcW := OK)
                        \<circ> (`ownB (H s,arrayW s (countW s)) := W)) s"
| "rbW_step A8 s = (if ((arrayW s (countW s))>N) then (ERROOM)
                        else (`pcW := idleW)) s"

definition "acq s s' \<equiv> ((pcW s \<in> {idleW})
                            \<and> (arrayW s (countW s)) > 0 
                            \<and> s' = (`pcW := A1) s)"

definition cW_step :: "PCW \<Rightarrow> rb_state \<Rightarrow> rb_state \<Rightarrow> bool" where
 "cW_step pcw s s' \<equiv> 
    case pcw of
        OK \<Rightarrow>  s' = (`q:=(append (q s) [(H s-arrayW s (countW s),arrayW s (countW s))])
                     \<circ> `ownAW (countW s):=Q
                     \<circ> `transownB W := Q 
                     \<circ> `pcW := idleW
                     \<circ> `countW := (countW s + 1)) s
      | idleW \<Rightarrow> if (countW s < n)
                      then acq s s'
                 else s' = (`pcW := FinishedW) s
      | OOM  \<Rightarrow> s = s'
      | FinishedW \<Rightarrow> s = s'
      | _  \<Rightarrow>  s' = rbW_step pcw s "
(***********************************************************************)





(*Reader Thread Behaviour*)
fun rbR_step :: "PCR \<Rightarrow> rb_state \<Rightarrow> rb_state" where
   "rbR_step R1 s = (`T := (off(tempR s) +len(tempR s)) \<circ> (`pcR := idleR) \<circ> (`tempR := (0,0))
                       \<circ> (`transownB R :=B)) s"


definition "read s s' \<equiv> (let q_hd = hd (q s) ; 
                             q_tl = tl (q s) 
                                 in s' = (`q:= q_tl 
                                          \<circ> `pcR := R1
                                          \<circ> `tempR := q_hd
                                          \<circ> `countR := ((countR s) +1)
                                          \<circ> `ownAW (countR s):=R
                                          \<circ> `ownB (T s,off(q_hd)+len(q_hd)):=R) s)"

definition cR_step :: "PCR \<Rightarrow> rb_state \<Rightarrow> rb_state \<Rightarrow> bool" where
 "cR_step pcr s s' \<equiv> 
    case pcr of
        idleR \<Rightarrow> if (q s=[]) then (s=s') else (read s s') 
      | R1 \<Rightarrow>  s' = rbR_step R1 s"
(***********************************************************************)

(*all the read stuff at the end goes here *)




(*ownAW structure - dependancy on counters*)

(*
ArrayW  = [W W W W W W W] 
          CountR = 0  
          CountW = 0 


ArrayW  = [Q W W W W W W] 
          CountR = 0  
          CountW = 1 


ArrayW  = [R R .. R    Q Q Q     W W W W] 
           0           CountR    CountW

Rely / Guarantee \<longrightarrow> 
We may need this. Q' = Q . X \<longrightarrow> X = ArrayW[CountW] This is a guarantee of the writer and also a rely of the reader.
*)



definition "inRange v \<equiv> 0 \<le> v \<and> v \<le> N"
definition "inRangeHT s \<equiv> inRange (H s) \<and> inRange (T s)"
definition "H0_T0 s \<equiv> H s = 0 \<longrightarrow> T s = 0"
definition "inRangeht s \<equiv> inRange (hW s) \<and> inRange (tW s)"
definition "basic_pointer_movement s \<equiv> inRangeHT s \<and> inRangeht s \<and> H0_T0 s "

lemmas basic_pointer_movement_lemmas [simp] = basic_pointer_movement_def inRangeHT_def inRangeht_def H0_T0_def inRange_def


definition "arrayInv s \<equiv> \<forall> i. (i<countR s \<longrightarrow> ownAW s i=R) \<and> (countR s \<le> i \<and> i < countW s \<longrightarrow> ownAW s i = Q) \<and> (countW s \<le> i \<and> i < n \<longrightarrow> ownAW s i = W) "
definition "inv_step_by_step s \<equiv> fst (tempR s) + snd (tempR s) \<le> N"
definition "q_entries_bounded s \<equiv> q s\<noteq>[]\<longrightarrow>(\<forall>i.(i<length(q s))\<longrightarrow>(fst(q s!i)+snd(q s!i)\<le>N))"
definition "counter_diff_imp s \<equiv> (countW s>countR s\<longrightarrow> H s>0)\<and> (((countW s=countR s)\<and>len(tempR s)>0)\<longrightarrow>H s>0)"
definition "T__overlap_def s \<equiv> (T s>off(hd(q s))+len(hd(q s)) \<and> snd(tempR s)\<noteq>0\<longrightarrow>(\<forall>i.(i<N \<and>i\<ge>T s\<or>i<off(hd(q s)))\<longrightarrow>ownB s i=R))\<or>(T s>off(hd(q s))+len(hd(q s)) \<and> snd(tempR s) =0\<longrightarrow>(\<forall>i.(i<N \<and>i\<ge>T s\<or>i<off(hd(q s)))\<longrightarrow>ownB s i=Q))"
definition "counter_q_rel s \<equiv> countW s-countR s=length(q s)" 

definition inv :: "PCW\<Rightarrow>PCR\<Rightarrow>rb_state \<Rightarrow> bool " where
"inv pcw pcr s \<equiv> basic_pointer_movement s 
               \<and> arrayInv s
               \<and> inv_step_by_step s
               \<and> q_entries_bounded s
               \<and> counter_diff_imp s
               \<and> T__overlap_def s
               \<and> counter_q_rel s
  \<and> (case pcw of
      A1 \<Rightarrow> countW s<n 
    | A2 \<Rightarrow> countW s<n  \<and> hW s=H s 
    | A3 \<Rightarrow> countW s<n \<and> grd1 s \<and> hW s=H s 
    | A4 \<Rightarrow> countW s<n \<and> grd2 s \<and> hW s=H s 
    | A5 \<Rightarrow> countW s<n \<and> grd3 s \<and> hW s=H s 
    | A6 \<Rightarrow> countW s<n \<and> grd4 s \<and> grd3 s \<and> hW s=H s \<and> H s+arrayW s (countW s)\<le>N 
    | A7 \<Rightarrow> countW s<n \<and> grd5 s \<and> grd3 s \<and> hW s=H s 
    | A8 \<Rightarrow> countW s<n \<and> no_space_for_word s \<and> hW s=H s 
    | OK \<Rightarrow> countW s<n \<and> H s>0
    | idleW \<Rightarrow> (countW s=0\<longrightarrow>q s=[]) 
    | OOM \<Rightarrow> True 
    | FinishedW \<Rightarrow> countW s=n) 
  \<and> (case pcr of
      R1 \<Rightarrow> countR s>0 \<and> countR s\<le>n \<and> (H s\<noteq>0)
    | idleR \<Rightarrow> countR s\<le>n+1)
"





lemmas inv_simps =  inv_def cW_step_def cR_step_def init_def

lemmas invariant_lemmas [simp] = con_assms_def arrayInv_def inv_step_by_step_def
                          q_entries_bounded_def counter_diff_imp_def
                          T__overlap_def_def counter_q_rel_def


lemma inv_init:
  assumes "init s"
  and "con_assms s"
  shows "inv idleW idleR s"
  using assms 
  by (simp add: inv_simps)





lemma if_idleR_and_countR_eq_countW:
  assumes "con_assms s"
  and "inv (pcW s) (pcR s) s"
  and "cR_step (pcR s) s s'"
  and "countR s = countW s"
shows "(pcR s=idleR \<longrightarrow> pcR s'=idleR)\<and>(pcR s=R1\<longrightarrow>pcR s'=idleR)"
  using assms
  apply(simp_all add:inv_def cR_step_def)
  by(case_tac "pcR s", simp_all)

lemma inv_local_R_int: 
  assumes "con_assms s"
  and "pcr = pcR s"
  and "pcw = pcW s"
  and "inv pcw pcr s" 
  and "cR_step pcr s s'"
shows "inv pcw (pcR s') s'"
  using assms 
  apply(simp add: inv_def)
  apply(intro conjI, elim conjE, simp_all)
  apply(case_tac[!] "pcR s", simp_all add: read_def cR_step_def)
  apply(case_tac[!] "q s = []", simp_all add:read_def Let_def)
  apply(case_tac[!] "T s < fst (hd (q s)) + snd (hd (q s))", simp_all add:hd_conv_nth nth_tl)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  by((case_tac "pcW s", simp_all, linarith, linarith, force)|auto)+



lemma writer_OK_to_idleW_count_equal:
  assumes "con_assms s"
  and "inv OK idleR s"
  and "cW_step OK s s'"
  and "countW s=countR s"
shows "countW s'>countW s \<and> pcW s'=idleW \<and> length(q s') =1 \<and> H s>0"  
  using assms
  by(simp_all add:inv_def cW_step_def)




lemma inv_local_W_int:
  assumes "con_assms s"
  and "pcr = pcR s"
  and "pcw = pcW s"
  and "inv pcw pcr s"
  and "cW_step pcw s s'"
shows "inv (pcW s') pcr s'"
  using assms
  apply(simp_all add: inv_def cW_step_def, intro conjI impI)
  apply(case_tac[!] "pcW s", simp_all, linarith)
  apply(case_tac[!] "pcR s", simp_all add:less_imp_le_nat acq_def)
  apply(case_tac "tW s=H s", simp_all ;case_tac "H s < tW s \<and> arrayW s (countW s) < tW s - H s", simp_all ;case_tac "tW s < H s", simp_all)
  apply(case_tac "tW s=H s", simp_all ;case_tac "H s < tW s", simp_all; case_tac "arrayW s (countW s) < tW s - H s", simp_all)
  apply(case_tac[1-2] "arrayW s (countW s) \<le> N - H s", simp_all,case_tac[1-2] "arrayW s (countW s) < tW s", simp_all)
  apply(metis less_imp_le less_numeral_extra(3),metis less_imp_le less_numeral_extra(3))        
  apply(case_tac[1-2] "N < arrayW s (countW s)", simp_all)
  apply(case_tac "tW s=H s", simp_all; case_tac "H s < tW s \<and> arrayW s (countW s) < tW s - H s", simp_all; case_tac "tW s < H s", simp_all)
  apply(case_tac "tW s=H s", simp_all; case_tac "H s < tW s", simp_all; case_tac "arrayW s (countW s) < tW s - H s", simp_all)
  apply(case_tac[1-2] "arrayW s (countW s) \<le> N - H s", simp_all,case_tac[1-2] "arrayW s (countW s) < tW s", simp_all)
  apply(case_tac[1-2] "N < arrayW s (countW s)", simp_all)
  apply(smt add.commute add_cancel_right_left diff_is_0_eq' fst_conv le_less_linear less_Suc0 less_SucE less_imp_le list.size(3) nth_append nth_append_length ordered_cancel_comm_monoid_diff_class.add_diff_inverse snd_conv)
  apply(smt add.commute add_cancel_right_left diff_is_0_eq' fst_conv le_less_linear less_Suc0 less_SucE less_imp_le list.size(3) nth_append nth_append_length ordered_cancel_comm_monoid_diff_class.add_diff_inverse snd_conv)
  apply(case_tac "tW s = H s", simp_all;case_tac " H s < tW s \<and> arrayW s (countW s) < tW s - H s", simp_all; case_tac "tW s < H s", simp_all)
  apply(case_tac[1-2] "N < arrayW s (countW s)", simp_all add:cW_step_def, meson le_eq_less_or_eq not_le)
  apply(case_tac "tW s = H s \<and> arrayW s (countW s) \<le> N", simp_all; case_tac "H s < tW s \<and> arrayW s (countW s) < tW s - H s", simp_all; case_tac "tW s < H s", simp_all)
  apply(case_tac "N < arrayW s (countW s)", simp_all add: Suc_diff_le)
  apply(case_tac "arrayW s (countW s) \<le> N - H s", simp_all add:Nat.le_diff_conv2)
  by(case_tac "N < arrayW s (countW s)", simp_all, force)


lemma R_doesnt_move_H:
  assumes "con_assms s"
  and "cR_step (pcR s) s s'"
shows "H s' = H s"
  using assms
  apply (simp_all add: cR_step_def)
  apply (cases "pcR s", simp_all)
  apply (case_tac "q s = []", simp_all)
  by (simp add: read_def Let_def)


lemmas moves = R_doesnt_move_H                
                    

lemma inv_counter_relationship: 
  assumes "con_assms s"
  and "inv A4 (pcR s) s"
  and "cW_step A4 s s'"
shows "hW s'= H s"
  using assms
  by (simp add: inv_def cW_step_def)  






lemma inv_global_R_int: 
  assumes "con_assms s"
  and "pcr = pcR s"
  and "pcw = pcW s"
  and "inv pcw pcr s" 
  and "cR_step pcr s s'"
shows "inv (pcW s') (pcR s') s'"
  using assms 
  apply(simp add: inv_def)
  apply(intro conjI, elim conjE)
  apply(simp add: cR_step_def)
  apply(case_tac[!] "pcR s", simp_all add: read_def)
  apply(case_tac[!] "q s = []", simp_all add: cR_step_def read_def Let_def)
  apply(case_tac[!] "T s < fst (hd (q s)) + snd (hd (q s))", simp_all add: hd_conv_nth nth_tl)
  apply force 
  apply force
  apply force
  apply force
  apply(case_tac[1-8] "pcW s", simp_all, (linarith, linarith, force)+)
  by auto+




lemma inv_global_W_int:
  assumes "con_assms s"
  and "pcr = pcR s"
  and "pcw = pcW s"
  and "countR s<countW s"
  and "inv pcw pcr s"
  and "cW_step pcw s s'"
shows "inv (pcW s') (pcR s') s'"
  using assms
  apply(simp_all add: inv_def cW_step_def, intro conjI impI)
  apply(simp_all add: cW_step_def inv_def)
  apply(case_tac[!] "pcW s", simp_all, linarith)
  apply(case_tac[!] "pcR s", simp_all add:less_imp_le_nat acq_def)
  apply(case_tac "tW s=H s", simp_all ;case_tac "H s < tW s \<and> arrayW s (countW s) < tW s - H s", simp_all ;case_tac "tW s < H s", simp_all)
  apply(case_tac "tW s=H s", simp_all ;case_tac "H s < tW s", simp_all; case_tac "arrayW s (countW s) < tW s - H s", simp_all)
  apply(case_tac[1-2] "arrayW s (countW s) \<le> N - H s", simp_all, case_tac[1-2] "arrayW s (countW s) < tW s", simp_all)
  apply(metis less_imp_le less_numeral_extra(3),metis less_imp_le less_numeral_extra(3))        
  apply(case_tac[1-2] "N < arrayW s (countW s)", simp_all)
  apply(case_tac[1-2] "tW s = H s", simp_all, case_tac[1-2] "H s < tW s \<and> arrayW s (countW s) < tW s - H s", simp_all, case_tac[1-2] "tW s < H s", simp_all)
  apply(case_tac[1-2] "arrayW s (countW s) \<le> N - H s", simp_all, case_tac[1-2] "arrayW s (countW s) < tW s", simp_all)
  apply(case_tac[1-2] "N < arrayW s (countW s)", simp_all)
  apply(smt add.commute add_cancel_right_left diff_is_0_eq' fst_conv le_less_linear less_Suc0 less_SucE less_imp_le list.size(3) nth_append nth_append_length ordered_cancel_comm_monoid_diff_class.add_diff_inverse snd_conv)
  apply(smt add.commute add_cancel_right_left diff_is_0_eq' fst_conv le_less_linear less_Suc0 less_SucE less_imp_le list.size(3) nth_append nth_append_length ordered_cancel_comm_monoid_diff_class.add_diff_inverse snd_conv)
  by linarith+




lemma pcR_stable_ext:
  "con_assms s \<Longrightarrow> cW_step (pcW s) s s' \<Longrightarrow> pcR s= pcR s'"  
  apply (simp_all add:cW_step_def )
  by(case_tac "pcW s", simp_all add:acq_def)

  
lemma pcW_stable_ext:
  "con_assms s \<Longrightarrow> cR_step (pcR s) s s' \<Longrightarrow> pcW s= pcW s'"  
  apply(simp_all add:cR_step_def)
  by(cases "pcR s", simp_all, cases"q s=[]", simp_all add:read_def Let_def)


lemma W_doesnt_move_T:
  assumes "H s\<noteq> T s"
  and "H s\<noteq>0" 
  and "cW_step (pcW s) s s'"
  and "pcW s\<noteq> A3"
shows "T s = T s'"
  using assms
  apply(simp_all add:cW_step_def)
  by(cases "pcW s", simp_all, case_tac "countW s < n", simp_all add:acq_def)






































(**********************************************************************
(* Define the states threads can find themselves in *)

definition "ACQ_PCW \<equiv> {A2, A3, A4, A5, A6, A7, A8, A1, OK}"
definition "EXT_PCW \<equiv> {OOM, idleW, FinishedW} \<union> {OK}"
definition "ACQ_PCR \<equiv> {R1}"
definition "EXT_PCR \<equiv> {idleR}"
**********************************************************************)



(*
definition "ownAW_and_countR s \<equiv> (\<forall>i.(i<countR s)\<longrightarrow>ownAW s i=R)\<and>
                                (\<forall>j.(j>countR s \<and> j<n)\<longrightarrow>(ownAW s j=Q \<or> ownAW s j=W))"

definition "ownAW_and_countW s \<equiv> (\<forall>i.((i>countW s)\<and>(i<n))\<longrightarrow>ownAW s i=W)\<and>
                                (\<forall>j.(j<countW s)\<longrightarrow>(ownAW s j=Q \<or> ownAW s j=R))"

definition "Q_has_ownAW s \<equiv> q s\<noteq>[] \<longrightarrow> (\<exists>i.(i<n \<and> ownAW s i=Q))" (* Mike says we might need this *)

definition "ownership_0 s \<equiv> ownAW_and_countR s \<and> ownAW_and_countW s \<and> Q_has_ownAW s"

lemmas ownership_0_lemmas [simp] = ownership_0_def ownAW_and_countR_def ownAW_and_countW_def Q_has_ownAW_def
*)

(*

(*Defining position of H w.r.t. ownB*)
definition "Has_this_ownB v s \<equiv> \<exists>i.(i<N \<and> ownB s i=v)" 
definition "This_ownB_no_wrap v s \<equiv> (ownB s 0=v \<and> ownB s (N-1)\<noteq>v) \<or>
                                    (ownB s 0\<noteq>v \<and> ownB s (N-1)=v) \<or>
                                    (ownB s 0\<noteq>v \<and> ownB s (N-1)\<noteq>v) \<or> 
                                    (\<forall>i.(i<N)\<longrightarrow>ownB s i=v)"
definition "H_ownB_relationship s \<equiv> 
                      if  Has_this_ownB W s then
                            if This_ownB_no_wrap W s then
                                   \<exists>i. (i<N \<and> ownB s i=W \<and> ownB s (i+1) =B  \<and> H s=i+1)
                            else (\<exists>i. (i<(N-1) \<and> (ownB s i=W)\<and>(ownB s (i+1) =B) \<and> H s=i+1))
                                               
                 else if  Has_this_ownB Q s then
                            if This_ownB_no_wrap Q s then
                                   \<exists>i. (i<N \<and> ownB s i=Q \<and> ownB s (i+1) =B  \<and> H s=i+1)
                            else (\<exists>i. (i<(N-1) \<and> (ownB s i=Q)\<and>(ownB s (i+1) =B) \<and> H s=i+1))
                                               
                 else if  Has_this_ownB R s then
                            if This_ownB_no_wrap R s then
                                   \<exists>i. (i<N \<and> ownB s i=R \<and> ownB s (i+1) =B  \<and> H s=i+1)
                            else (\<exists>i. (i<(N-1) \<and> (ownB s i=R)\<and>(ownB s (i+1) =B) \<and> H s=i+1))
                             
                  else H s\<le>N \<and> H s=T s"

(*Defining position of T w.r.t. ownB*)

definition "This_ownB_all_bytes v s \<equiv> \<forall>i.(i<N)\<longrightarrow>ownB s i=v"

definition "T_ownB_relationship s \<equiv> 
                      if  Has_this_ownB R s then 
                            if This_ownB_all_bytes R s then
                                T s=0
                            else if ownB s 0=R \<and> ownB s (N-1)\<noteq>R then
                                T s=0 \<or> T s=N
                            else
                                \<exists>i.(i>0\<and>i<N\<and> ownB s i=R \<and> ownB s (i-1) =B \<and> T s=i)
                 else if  Has_this_ownB Q s then 
                            if This_ownB_all_bytes Q s then
                                T s=0
                            else if ownB s 0=Q \<and> ownB s (N-1)\<noteq>Q then
                                T s=0 \<or> T s=N
                            else
                                \<exists>i.(i>0\<and>i<N\<and> ownB s i=Q \<and> ownB s (i-1) =B \<and> T s=i)
                 else if  Has_this_ownB W s then 
                            if This_ownB_all_bytes W s then
                                T s=0
                            else if ownB s 0=W \<and> ownB s (N-1)\<noteq>W then
                                T s=0 \<or> T s=N
                            else
                                \<exists>i.(i>0\<and>i<N\<and> ownB s i=Q \<and> ownB s (i-1) =B \<and> T s=i)
                 else T s\<le>N \<and> T s=H s"


(*the following requires careful handling of the "extra" byte - aka byte gap between T and new H*)
(*ownB structure *)
definition "B_has_enough_ownB_for v s \<equiv> ownB s N=B \<and> (if v=grd1 s then (\<forall>i.(i<N)\<longrightarrow>ownB s i=B)
                                  else if v=grd2 s then (\<forall>i.(hW s\<le>i \<and> i\<le>tempW s)\<longrightarrow>ownB s i=B)
                                  else if v=grd3 s \<and> grd4 s then (\<forall>i.(hW s\<le>i\<and> i\<le>hW s+tempW s)\<longrightarrow>ownB s i=B)
                                  else if v=grd3 s \<and> grd5 s then (\<forall>i.(hW s\<le>i\<and> i<N)\<longrightarrow>ownB s i=B)\<and>(\<forall>j.(j\<le>tempW s)\<longrightarrow>ownB s j=B)
                                  else True)"


(*Defining position of hW w.r.t. H and pcW*)
definition "hW_defined_for_pcW s \<equiv> if pcW s\<in>ACQ_PCW \<and> pcW s\<noteq>OK \<and> pcW s\<noteq>A1 then hW s=H s else hW s\<le>N"

(*Defining position of tW w.r.t. H and pcW*)
(*this has to be defined wrt grd - different pcW*)

(*Defining tempW w.r.t. countW*)
definition "tempW_defined s \<equiv> tempW s = arrayW s (countW s)\<and> tempW s>0"

(*Defining tempR w.r.t. countR and pcR*)
definition "tempR_defined s \<equiv> if (countR s>0 \<and> pcR s=R1) then 
                                        ((len(tempR s) =arrayW s (countR s -1))\<and>(if (ownB s 0=R) then 
                                                                                     off(tempR s) =0
                                                                                else (\<exists>i.(i<N \<and> i>0 \<and> ownB s i=R \<and> ownB s (i-1)\<noteq>R \<and> off(tempR s) = i))))
                            else tempR s=(0,0)\<and>(\<forall>i.(i<N)\<longrightarrow>ownB s i\<noteq>R) "

definition "tempR_ownB_exclusivity s \<equiv>(snd(tempR s)\<noteq>0)\<longrightarrow>(\<forall>i.(i<snd(tempR s))\<longrightarrow>ownB s (fst(tempR s)+i) =R)"

definition "tempR_pair_property s \<equiv> (len(tempR s) =0 \<longrightarrow>off(tempR s) =0)\<and>(len(tempR s)+off(tempR s)\<le>N)"

definition "tempR_T_ownB_relation s\<equiv> if T s\<noteq>off(tempR s)\<and> pcR s=R1 then (\<forall>i.(i<N \<and>i\<ge>T s)\<longrightarrow>ownB s i=R)
                                      else (\<forall>i.(i<T s)\<longrightarrow>ownB s i\<noteq>R)"

(*Defining arrayW*)
definition "setup_arrayW s \<equiv> \<forall>l. (l<n) \<longrightarrow>  (arrayW s l > 0 \<and> arrayW s l < N)"

definition "rb_structure s \<equiv> H_ownB_relationship s \<and> T_ownB_relationship s \<and> hW_defined_for_pcW s 
                                        \<and> tempR_defined s \<and> tempW_defined s \<and> tempR_T_ownB_relation s \<and> setup_arrayW s"

lemmas rb_structure_lemmas = rb_structure_def Has_this_ownB_def This_ownB_no_wrap_def H_ownB_relationship_def  T_ownB_relationship_def 
                              hW_defined_for_pcW_def tempR_defined_def tempW_defined_def tempR_pair_property_def tempR_T_ownB_relation_def setup_arrayW_def This_ownB_all_bytes_def

(*q structure*)
definition "q_contains_arrayW_things s \<equiv> (length(q s) = countW s-countR s)\<longrightarrow>(\<forall>i.(i<length(q s))\<longrightarrow>len(q s!i) =arrayW s (i+countR s))"

definition "at_most_one_zero_offset s \<equiv> ((len(tempR s)\<noteq>0) \<and> off(tempR s) =0 \<and> (\<not>(\<exists>i.(i<length(q s)\<and>off(q s !i) =0))))
                                       \<or>((\<exists>j.(j<length(q s)\<and>off(q s!j) =0 \<and> (\<not>(\<exists>k.(k<length(q s)\<and>k\<noteq>j\<and>off(q s!k) =0))))) \<and> (len(tempR s)\<noteq>0\<longrightarrow>off(tempR s)\<noteq>0))
                                       \<or>(\<not>(\<exists>z.(z<length(q s)\<and>off(q s!z) =0)) \<and> (len(tempR s)\<noteq>0\<longrightarrow>off(tempR s)\<noteq>0))"
definition "q_pair_property s \<equiv> \<forall>i.(i<length(q s))\<longrightarrow>len(q s!i)>0\<and>len(q s!i)\<le>N\<longrightarrow>off(q s!i)+len(q s!i)\<le>N"
definition "q_entries_dont_cross s\<equiv> (\<forall>i.(i<length(q s))\<longrightarrow>(\<forall>j.(j<length(q s)\<and>j\<noteq>i)\<longrightarrow>(off(q s!j)\<ge>off(q s!i)+len(q s!i)\<or>off(q s!i)\<ge>off(q s!j)+len(q s!j))))
                                  \<and>(\<forall>k.(k<length(q s)\<longrightarrow>(off(q s!k)\<ge>off(tempR s)+len(tempR s)\<or>off(tempR s)\<ge>off(q s!k)+len(q s!k))))"
definition "q_ownB_relationship s \<equiv> \<forall>i.((i< length (q s))\<longrightarrow>(\<forall>j.(off(q s ! i)\<le>j\<and>j<off(q s ! i)+len(q s ! i))\<longrightarrow>ownB s j=Q))"
definition "q_structure s \<equiv> q_contains_arrayW_things s \<and> at_most_one_zero_offset s \<and> tempR_pair_property s \<and> q_pair_property s
                           \<and> q_entries_dont_cross s \<and> q_ownB_relationship s" 
lemmas q_structure_lemmas = q_structure_def q_contains_arrayW_things_def at_most_one_zero_offset_def
                            q_pair_property_def q_entries_dont_cross_def q_ownB_relationship_def

(*  Constant Assumptions  *)

[!]
*)
(*
definition inv :: "PCW\<Rightarrow>PCR\<Rightarrow>rb_state \<Rightarrow> bool " where
"inv pcw pcr s \<equiv> basic_pointer_movement s 
               \<and> q_structure s
               \<and> ownership_0 s
               \<and> rb_structure s
  \<and> (case pcw of
      A1 \<Rightarrow> countW s<n \<and> \<not>Has_this_ownB W s
    | A2 \<Rightarrow> countW s<n \<and> \<not>Has_this_ownB W s \<and> hW s=H s
    | A3 \<Rightarrow> B_has_enough_ownB_for (grd1 s) s \<and> countW s<n \<and> grd1 s \<and> hW s=H s \<and> \<not>Has_this_ownB W s
    | A4 \<Rightarrow> B_has_enough_ownB_for (grd2 s) s \<and> countW s<n \<and> grd2 s \<and> hW s=H s \<and> \<not>Has_this_ownB W s
    | A5 \<Rightarrow> countW s<n \<and> grd3 s \<and> hW s=H s \<and> \<not>Has_this_ownB W s
    | A6 \<Rightarrow> B_has_enough_ownB_for (grd4 s\<and>grd3 s) s \<and> countW s<n \<and> hW s=H s \<and> \<not>Has_this_ownB W s
    | A7 \<Rightarrow> B_has_enough_ownB_for (grd5 s\<and>grd3 s) s \<and> countW s<n \<and> hW s=H s \<and> \<not>Has_this_ownB W s
    | A8 \<Rightarrow> countW s<n \<and> grd5 s \<and> hW s=H s \<and> \<not>Has_this_ownB W s

    | OK \<Rightarrow> countW s<n
    | idleW \<Rightarrow> (countW s=0\<longrightarrow>q s=[]) \<and> \<not>Has_this_ownB W s
    | OOM \<Rightarrow> True \<and> \<not>Has_this_ownB W s
    | FinishedW \<Rightarrow> countW s=n) \<and> \<not>Has_this_ownB W s
  \<and> (case pcr of
      R1 \<Rightarrow> countR s>0 \<and> countR s\<le>n \<and> (\<exists>i.(i<N\<and>ownB s i=R))
    | idleR \<Rightarrow> (q s\<noteq>[]\<longrightarrow>Has_this_ownB Q s) \<and> countR s\<le>n+1)
"*)


