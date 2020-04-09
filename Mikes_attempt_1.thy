theory Mikes_attempt_1
imports Main HOL.List
begin 
(*ensure hW,tW are not changed - not aux*)

datatype PCW =
  A1 | A2 | A3 | A4 | A5 | A6 | A7 | A8
| OK  | idleW | OOM | FinishedW

datatype PCR =
  R1 
  | idleR 


datatype Thread = W | R
datatype Pointer = Head | Tail
datatype F0 = Arr\<^sub>W | Arr\<^sub>R | W | R | Q
datatype F1 = B | W | Q | R
datatype F2 = W | Q | R
consts n :: nat   (*size of buffer, input*)
consts N :: nat   (*number of Arr\<^sub>W entries*)





(*Recorded variables*)
record rb_state =
  H :: nat
  T :: nat
  hW ::  nat               (*local copy of W*)
  tW ::  nat               (*local copy of W*)
  count :: nat
  countR :: nat
  temp :: nat         (*local copy of word by W*)
  tempR :: "nat\<times>nat"        (*local copy of word by R*)
  pcW :: PCW           (*records program counter of W*)
  pcR :: PCR           (*records program counter of W*)
  own0 :: "nat \<Rightarrow> F0"
  own1 :: "nat \<Rightarrow> F1"
  own2 :: "Pointer \<Rightarrow> F2"
  arrayW:: "nat  \<Rightarrow> nat"     (*returns a word arrayW_i*)
  arrayR:: "nat  \<Rightarrow> nat"     (*returns a word arrayR_i*)


definition "con_assms s \<equiv>   0 < N \<and> 0<n \<and> count (s)\<le>n \<and> countR (s)\<le>n
                            \<and> (\<forall>l. (l<n) \<longrightarrow>  (arrayW (s) l > 0) \<longrightarrow>  (arrayW (s) l < N)) "


definition push_H :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`H := _" [200])
  where 
  "push_H v \<equiv> \<lambda>s. s \<lparr>H := v\<rparr>"

definition push_T :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`T := _" [200])
  where 
  "push_T v \<equiv> \<lambda>s. s \<lparr>T := v\<rparr>"

definition set_own0 :: "nat \<Rightarrow> F0 \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`own0 _ := _" [200])  where
  "set_own0 ord v  \<equiv> \<lambda>s. s \<lparr> own0  := ((own0 s) (ord := v))\<rparr>"

definition set_own1 :: "nat \<Rightarrow> F1 \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`own1 _ := _" [200])  where
  "set_own1 ord v  \<equiv> \<lambda>s. s \<lparr> own1  := ((own1 s) (ord := v))\<rparr>"

definition set_own2 :: "Pointer \<Rightarrow> F2 \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`own2 _ := _" [200])  where
  "set_own2 ord v  \<equiv> \<lambda>s. s \<lparr> own2  := ((own2 s) (ord := v))\<rparr>"

definition set_hW :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`hW := _" [200])  where
  "set_hW v  \<equiv> \<lambda>s. s \<lparr> hW  := v\<rparr>"

definition set_tW :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`tW := _" [200])  where
  "set_tW v  \<equiv> \<lambda>s. s \<lparr> tW  := v\<rparr>"

definition update_count :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`count := _" [200]) where
  "update_count v\<equiv> \<lambda>s. s \<lparr> count := v\<rparr>"

definition update_countR :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`countR := _" [200]) where
  "update_countR v\<equiv> \<lambda>s. s \<lparr> countR := v\<rparr>"


definition set_temp :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`temp := _" [200]) where
  "set_temp v \<equiv> \<lambda>s. s \<lparr> temp := v\<rparr>"

definition set_tempR :: "nat\<times>nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`tempR := _" [200]) where
  "set_tempR v \<equiv> \<lambda>s. s \<lparr> tempR := v\<rparr>"

definition update_pcW :: "PCW \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`pcW := _" [200]) where
  "update_pcW v \<equiv> \<lambda>s. s \<lparr> pcW := v\<rparr>"

definition update_pcR :: "PCR \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`pcR := _" [200]) where
  "update_pcR v \<equiv> \<lambda>s. s \<lparr> pcR := v\<rparr>"

definition set_arrayR :: "nat \<Rightarrow> nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`arrayR _ := _" [200])  where
  "set_arrayR ord v  \<equiv> \<lambda>s. s \<lparr> arrayR  := ((arrayR s) (ord := v))\<rparr>"

abbreviation update_b_err :: "rb_state \<Rightarrow> rb_state" ("ERROOM") where
  "update_b_err \<equiv> \<lambda>s. s \<lparr> pcW := OOM \<rparr>"


lemmas functs  = push_H_def push_T_def set_hW_def set_tW_def
                        update_count_def update_countR_def set_temp_def set_tempR_def
                        update_pcW_def update_pcR_def set_arrayR_def 

record c_state = 
  q :: "(nat \<times> nat) list"
  rb :: rb_state




abbreviation update_q :: "(nat \<times> nat) list \<Rightarrow> c_state \<Rightarrow> c_state" ("`q := _" [200])
  where 
  "update_q v  \<equiv> \<lambda>s. s \<lparr>q := v\<rparr>"
(***********************************************************************)



(* Define the states threads can find themselves in *)

definition "ACQ_PCW \<equiv> {A2, A3, A4, A5, A6, A7, A8, A1, OK}"
definition "EXT_PCW \<equiv> {OK, OOM, idleW, FinishedW}"
definition "ACQ_PCR \<equiv> {R1}"
definition "EXT_PCR \<equiv> {idleR}"
(***********************************************************************)





(*  Define the if statement "guards"  *)

definition "off bo \<equiv> fst bo"
definition "len bo \<equiv> snd bo"
definition "grd1 s \<equiv> (tW s = hW s) \<and> (temp s \<le> N)"
definition "grd2 s \<equiv> (tW s > hW s) \<and> (temp s \<le> (tW s - hW s))"
definition "grd3 s \<equiv> tW s < hW s"
definition "grd4 s \<equiv> temp s \<le> N - hW s"
definition "grd5 s \<equiv> temp s < tW s"
lemmas grd_simps [simp] = off_def len_def grd1_def grd2_def grd3_def grd4_def grd5_def 
(***********************************************************************)





(*  Initial State  *)

definition "init s \<equiv> (H (rb s) = 0) \<and> (T (rb s) = 0) \<and> q s = []
                        \<and> ( pcW (rb s) = idleW)
                        \<and> ( pcR (rb s) = idleR)
                        \<and> (temp (rb s) = 0)
                        \<and> (tempR (rb s) = (0,0))
                        \<and> (hW (rb s) =0) \<and> (tW (rb s) =0)
                        \<and> (\<forall>l. (l<n) \<longrightarrow>  arrayR (rb s) l = 0)
                        \<and> (\<forall>i. (i<n) \<longrightarrow>  own0 (rb s) i = Arr\<^sub>W) \<and> (\<forall>j. (j<N) \<longrightarrow>  own1 (rb s) j = B)
                        \<and> (own2 (rb s) Head = W) \<and> (own2 (rb s) Tail = Q) \<and> (count (rb s) = 0)\<and> (countR (rb s) = 0)"
(***********************************************************************)

definition "bounds_of_rb_state s \<equiv> (H (rb s) \<le> N) \<and> (T (rb s) \<le> 0) 
                        \<and> (temp (rb s) \<le> N) \<and> (temp (rb s) \<ge> 0)
                        \<and> (len((tempR (rb s)))-off(tempR (rb s)) \<ge> 0) \<and> (len((tempR (rb s)))-off(tempR (rb s)) \<le> N)
                        \<and> (hW (rb s) \<le>N) \<and> (tW (rb s) \<le>N)
                        \<and> (hW (rb s) \<ge>0) \<and> (tW (rb s) \<ge>0)"




(*Writer Thread Behaviour*)

fun rbW_step :: "PCW \<Rightarrow> rb_state \<Rightarrow> rb_state" where
  "rbW_step A1 s = ((`temp := (arrayW s (count s))) 
                    \<circ> (`hW := (H s)) 
                    \<circ> (`tW := (T s)) 
                    \<circ> (`pcW := A2)) s "
| "rbW_step A2 s = (if grd1 s then (`pcW := A3)
                     else if grd2 s then (`pcW := A4) 
                     else if grd3 s then (`pcW := A5) 
                     else (`pcW :=A8)) s"
| "rbW_step A3 s = ((`T := 0) \<circ> (`H := (temp s)) \<circ> (`hW := (temp s)) \<circ> (`tW := 0) \<circ> (`pcW := OK )) s" 
| "rbW_step A4 s = ((`H := ((hW s) + (temp s)))  \<circ> (`pcW := OK)) s"
| "rbW_step A5 s = (if grd4 s then (`pcW := A6)  
                     else if grd5 s then (`pcW := A7)
                     else (`pcW := A8)) s"
| "rbW_step A6 s = (`H := ((hW s) + (temp s)) \<circ> (`hW := ((hW s) + (temp s))) \<circ> `pcW := OK) s"
| "rbW_step A7 s = ((`H := (temp s)) \<circ> (`hW := (temp s)) \<circ> `pcW := OK) s"
| "rbW_step A8 s = (if ((temp s)>N) then (ERROOM)
                        else `pcW := idleW) s"

definition "acq s s' \<equiv> ((pcW (rb s) \<in> {idleW})
                            \<and> (arrayW (rb s) (count (rb s))) > 0 
                            \<and> (rb s') = (`pcW := A1) (rb s))
                            \<and> count (rb s) < n 
                            \<and> (q s' = q s)"

definition cW_step :: "PCW \<Rightarrow> c_state \<Rightarrow> c_state \<Rightarrow> bool" where
 "cW_step pcw s s' \<equiv> 
    case pcw of
        OK \<Rightarrow>  q s' = (append (q s) [(hW (rb s),hW (rb s)+temp (rb s))]) 
                \<and> rb s'= (`temp:=0) (rb s)
                \<and> rb s' = (`pcW := idleW) (rb s)
                \<and> rb s' = (`count := (count (rb s) + 1)) (rb s)
      | idleW \<Rightarrow> if (count (rb s) < n)
                      then acq s s'
                 else (rb s') = (`pcW := FinishedW) (rb s) \<and> (q s' = q s)
      | OOM  \<Rightarrow> s = s'
      | FinishedW \<Rightarrow> s = s'
      | _  \<Rightarrow>  q s' = q s \<and> (rb s') = rbW_step pcw (rb s) "
(***********************************************************************)





(*Reader Thread Behaviour*)

fun rbR_step :: "PCR \<Rightarrow> rb_state \<Rightarrow> rb_state" where
   "rbR_step R1 s = (`T := (len (tempR s)) 
                        \<circ> (`pcR := idleR)) s"


definition "read s s' \<equiv> (pcR (rb s) \<in> {idleR})
                              \<and> (let q_hd = hd (q s) ; 
                                     q_tl = tl (q s) 
                                 in q s' =  q_tl
                                 \<and> rb s' = (`tempR := q_hd) (rb s)
                                 \<and> rb s' = (`pcR := R1) (rb s))
                                 \<and> rb s' = (`countR := ((countR (rb s)) +1)) (rb s)
                                 \<and> rb s' = (`arrayR (countR (rb s)):= (len (tempR (rb s)) - off (tempR (rb s)))) (rb s)"

definition cR_step :: "PCR \<Rightarrow> c_state \<Rightarrow> c_state \<Rightarrow> bool" where
 "cR_step pcr s s' \<equiv> 
    case pcr of
        idleR \<Rightarrow> if (q s=[]) then (s=s') else (read s s') 
      | R1  \<Rightarrow>  q s' = q s \<and> (rb s') = rbR_step R1 (rb s)"
(***********************************************************************)





definition "inRange v \<equiv> 0 \<le> v \<and> v \<le> N"

definition "inRangeHT s \<equiv> inRange (H s) \<and> inRange (T s)"

definition "H0_T0 s \<equiv> H s = 0 \<longrightarrow> T s = 0"

definition "inRangeht s \<equiv> inRange (hW s) \<and> inRange (tW s)"


(*The following describes what arrayR should look like wrt arrayW, and process ordering
using count and countR *)
definition "countR_count_relationship s \<equiv> countR s \<le> count s"

definition "arrayW_is_arrayR s \<equiv> (countR s)>0 \<longrightarrow>( \<forall>i.(i<countR s)\<longrightarrow> arrayW s i = arrayR s i)"


(*The following describes all possible combinations of items in q, which is to be preserved
if the ring buffer is to have the property of FIFO *)
definition "q_ith_is_from_arrayW s \<equiv> \<forall>i. i<(length (q s)) \<longrightarrow> (len((q s ! i) )-off((q s ! i)) = arrayW (rb s) (i+countR (rb s)) )"

definition "q_ith_follows_the_one_before s\<equiv> (length (q s)>1) \<longrightarrow> (\<forall>i.(i<(length (q s))-1) \<longrightarrow> (off(q s ! (i+1)) = len(q s ! i)) \<or> 
                                  ((off(q s ! (i+1)) = 0) \<and> off(q s ! 0)>len(q s ! (i+1))))"

definition "only_one_zero_as_offset s \<equiv> (\<forall>i.(i<length(q s))\<longrightarrow>(\<forall>j.(j<length(q s)) \<longrightarrow> (j\<noteq>i) \<longrightarrow> (off(q s ! i) =0) \<longrightarrow> (off(q s ! j) \<noteq>0)))"

definition "all_q_entries_fit s \<equiv> (\<forall>i.(i<length(q s))\<longrightarrow>(off(q s ! i)<len(q s ! i))\<longrightarrow>(len(q s ! i)<N))"

definition "size_q_less_than_n s \<equiv> (length(q s)\<le>n)"

definition "tempR_is_first_in_q s \<equiv> tempR s\<noteq>(0,0) \<longrightarrow> countR s\<le>n \<longrightarrow> len(tempR s)-off(tempR s) = arrayW s ((countR s)-1)"

definition "if_q_has_ith_then_count s\<equiv> True"


definition "sizeq_wrt_counters s \<equiv> length(q s) = (count (rb s) - countR  (rb s))"

definition "sizeq_bounds s \<equiv> length(q s) \<ge>0 \<longrightarrow> length(q s)\<le>n"



definition "tempR_is_from_array s\<equiv> (countR s)>0 \<longrightarrow> ((len(tempR s)-off(tempR s)) = arrayW s ((countR s) -1))"

definition "H_always_equal_to_hW s \<equiv> H s=hW s"

definition "T_always_located_at s \<equiv> (T (rb s)=len(tempR (rb s))\<and>(pcR (rb s)=R1))\<or>(((T (rb s)=off(tempR (rb s)))\<or>((T (rb s) =0) \<and> q s=[]))\<and>(pcR (rb s)=idleR))"

definition "H_always_located_at_givenR1 s \<equiv> ((q s=[]\<and>pcR (rb s) =R1) \<longrightarrow> ((H (rb s) =len(tempR (rb s)))
                                                    \<or>(H (rb s) =temp (rb s)+len(tempR (rb s)))
                                                    \<or>(H (rb s) =temp (rb s))))\<and>

((q s\<noteq>[]\<and>pcR (rb s) =R1) \<longrightarrow> (((H (rb s) = len(q s ! (length(q s)-1)))\<and>(pcW (rb s)\<noteq>OK)) \<or>
                               ((H (rb s) = len(q s ! (length(q s)-1))+ temp(rb s))\<and>(pcW (rb s) =OK))))"

definition "H_always_located_at_givenidleR s \<equiv> (q s=[]\<and>pcR (rb s) =R1)\<longrightarrow> True"






lemmas inv_simps [simp] = H0_T0_def inv_def inRangeHT_def inRange_def inRangeht_def
                    cW_step_def cR_step_def init_def countR_count_relationship_def
                    arrayW_is_arrayR_def con_assms_def bounds_of_rb_state_def
                    q_ith_is_from_arrayW_def
                    q_ith_follows_the_one_before_def
                    only_one_zero_as_offset_def
                    all_q_entries_fit_def
                    size_q_less_than_n_def
                    tempR_is_first_in_q_def
                    sizeq_wrt_counters_def
                    sizeq_bounds_def
                    tempR_is_from_array_def
                    H_always_equal_to_hW_def
                    T_always_located_at_def

lemmas ACQ_EXT [simp] = ACQ_PCR_def ACQ_PCW_def EXT_PCW_def EXT_PCR_def


(*********************************************************)
                    (**New Attempt**)
(*********************************************************)

definition inv :: "PCW \<Rightarrow> PCR \<Rightarrow> c_state \<Rightarrow> bool " where
"inv pcw pcr c \<equiv> 
   (let s = rb c in
    inRangeHT s \<and> H0_T0 s
    \<and> (\<forall> qb \<in> set (q c) . inRange (off qb + len qb)) 
    \<and> (pcw \<in> ACQ_PCW \<longrightarrow> (temp s = (arrayW s (count s))) \<or> (pcW s = A1))
    \<and> (countR_count_relationship s \<and> (pcr\<in>{R1} \<longrightarrow> countR s\<noteq>count s))
    \<and> arrayW_is_arrayR s 
    \<and> q_ith_is_from_arrayW c
    \<and> q_ith_follows_the_one_before c
    \<and> only_one_zero_as_offset c
    \<and> all_q_entries_fit c
    \<and> size_q_less_than_n c
    \<and> inRangeht s
    \<and> temp s \<le> N
    \<and> bounds_of_rb_state c
    \<and> tempR_is_first_in_q s
    \<and> size_of_q_is_sizeq c
    \<and> sizeq_wrt_counters s
    \<and> sizeq_bounds s
    \<and> tempR_is_from_array s
    \<and> H_always_equal_to_hW s
    \<and> T_always_located_at c
    \<and>
    (case pcw of
           A1     \<Rightarrow> arrayW s (count s) > 0 \<and> count s<n
         | A2     \<Rightarrow> count s<n
         | A3     \<Rightarrow> count s<n \<and> grd1 s
         | A4     \<Rightarrow> count s<n \<and> grd2 s \<and> \<not> grd1 s
         | A5     \<Rightarrow> count s<n \<and> grd3 s \<and> \<not> grd1 s \<and> \<not> grd2 s
         | A6     \<Rightarrow> count s<n \<and> grd4 s \<and> \<not> grd1 s \<and> \<not> grd2 s \<and> \<not> grd3 s
         | A7     \<Rightarrow> count s<n \<and> grd5 s \<and> \<not> grd1 s \<and> \<not> grd2 s \<and> \<not> grd3 s \<and> \<not> grd4 s
         | A8     \<Rightarrow> count s<n

         | OK rv  \<Rightarrow> inRange (off rv + len rv) \<and> 0 < H s \<and> count s\<le>n

         | idleW  \<Rightarrow> (q c \<noteq> [] \<longrightarrow> 0 < H s) \<and> (count s \<ge>0) \<and> count s\<le>n
         | OOM    \<Rightarrow> True
         | FinishedW \<Rightarrow> count s = n)
    \<and>
    (case pcr of
           R1 \<Rightarrow> inRange (off (tempR s) + len (tempR s)) \<and> (0 < H s) \<and> len (tempR s)>0 \<and> T s=off(tempR s)
         | idleR  \<Rightarrow> (q c \<noteq> [] \<longrightarrow> (0 < H s)) \<and>  (countR s\<le>n)) \<and> T s=len(tempR s)
  )"

lemmas new_inv [simp] = inv_def

lemma inv_init:
  assumes "con_assms (rb s)"
  and "init s"
  and "pcw = (pcW (rb s))"
  and "pcr = (pcR (rb s))"
  shows "inv pcw pcr s"
    using assms
    apply auto
    done


lemma R_doesnt_move_H2:
  assumes "con_assms (rb s)"
  and "pcr = pcR (rb s)"
  and "inv (pcW (rb s)) pcr s" 
  and "cR_step pcr s s'"
  and "pcW (rb s') = pcW (rb s)"
shows "H (rb s') = H (rb s)"
  using assms
  apply auto
  apply(unfold read_def)
  apply(unfold functs)
  apply (cases "pcW (rb s)", simp_all add: Let_def)
             apply(case_tac[!] "pcR (rb s)", simp_all add: functs)
             apply(case_tac[!] "q s=[]", simp_all)
  done


lemma inv_local_W_int: 
  assumes "con_assms (rb s)"
  and "pcw = pcW (rb s)"
  and "inv pcw (pcR (rb s)) s" 
  and "cW_step pcw s s'"
  and "count (rb s) \<le>n"
  and "pcw \<noteq> pcW (rb s')"
shows "inv (pcW (rb s')) (pcR (rb s)) s'"
  using assms 
  apply(auto)
  apply(case_tac[!] "pcW (rb s)", simp_all add:functs)
          apply(case_tac[!] "pcR (rb s)", simp_all)
  apply(case_tac[!] "tW (rb s) = hW (rb s) \<and> temp (rb s) \<le> N", simp_all)
                      apply(case_tac[!] "hW (rb s) < tW (rb s) \<and> temp (rb s) \<le> tW (rb s) - hW (rb s)", simp_all add:functs)
                      apply meson+
                      apply (meson less_imp_le)
                      apply (meson less_imp_le)
  apply (meson less_imp_le)
  apply (smt less_imp_le)
  apply (meson less_imp_le)
  apply (meson less_imp_le)
  apply (smt less_imp_le)
                      apply meson
                      apply(case_tac[!] "tW (rb s) < hW (rb s)", simp_all)
                      apply meson+
                      apply(simp_all add:Let_def) 
                  apply(case_tac[!] "pcR (rb s')", simp_all)
                      apply meson+

  apply meson




  done
          

lemma inv_local_R_int2: 
  assumes "con_assms"
  and "pcr = pcR (rb s)"
  and "pcw = pcW (rb s)" 
  and "inv pcw pcr s" 
  and "pcW (rb s) = pcW (rb s')"
  and "cR_step pcr s s'"
  and "count(rb s)<n"
  and "countR (rb s)< count (rb s)"
  and "countR (rb s)>0"
shows "inv pcw (pcR (rb s')) s'"
   using assms 
  apply auto
  apply (case_tac[!] "pcW (rb s')",  simp_all add: Let_def)
             apply(case_tac[!] "pcR (rb s)", simp_all add: functs)
                       apply(case_tac[!] "q s=[]", simp_all add:read_def functs)
                       apply(case_tac[!] "n \<le> countR (rb s)", simp_all add:read_def functs)
                       apply (simp_all add: list.set_sel(2))
                       apply meson 
   apply simp_all

  done



lemma inv_global_W_int2:
  assumes "con_assms"
  and "pcr = pcR (rb s)"
  and "pcw = pcW (rb s)"
  and "inv pcw pcr s"
  and "cR_step pcr s s'"
  and "count (rb s)\<le>n"
  and "countR (rb s)<count (rb s)"
shows "inv pcw (pcR (rb s')) s'" 
  using assms
  apply(case_tac[!] "pcW (rb s)", simp_all add:Let_def)
             apply(case_tac[!] "pcR (rb s)", simp_all add:functs)
             apply(case_tac[!] "pcW (rb s')", simp_all)
                      apply(case_tac[!] "pcR (rb s')", simp_all)
                      apply(case_tac[!] "q s=[]", simp_all)
                      apply(case_tac[!] "read s s'",simp_all add:read_def functs)
                      apply((meson list.set_sel(1) list.set_sel(2))+)

  done



lemma inv_global_R_int:
  assumes "con_assms"
  and "pcr = pcR (rb s)"
  and "pcw = pcW (rb s)"
  and "inv pcw pcr s"
  and "cW_step pcw s s'"
  and "pcR (rb s') = pcr"
  and "pcw\<notin>{idleW}\<longrightarrow>pcW (rb s')\<noteq>pcw"
  and "count (rb s) \<le>n"
shows "inv (pcW (rb s')) (pcR (rb s')) s'"
  using assms
  apply(simp_all add:Let_def)
  apply(case_tac[!] "pcW (rb s)", simp_all add:functs)
           apply(case_tac[!] "pcW (rb s')", simp_all add:functs)
             apply(case_tac[!] "pcR (rb s)", simp_all)
             apply(case_tac[!] "pcR (rb s)", simp_all)
             apply(case_tac[!] "tW (rb s) = hW (rb s) \<and> temp (rb s) \<le> N", simp_all add:functs)
             apply(case_tac[!] "hW (rb s) < tW (rb s) \<and> temp (rb s) \<le> tW (rb s) - hW (rb s)", simp_all add:functs)
             apply(case_tac[!] "tW (rb s) < hW (rb s)", simp_all add:functs)
             apply(case_tac[!] "N < temp (rb s)", simp_all add:functs)
                      apply(case_tac[!] "count (rb s)<n",simp_all)
                      apply(case_tac[!] "\<not> WFlag (rb s) (count (rb s))", simp_all)
                      apply(unfold acq_def)
                      apply(unfold functs)
                      apply(simp_all+)
                      apply linarith+
  done



lemma pcR_stable_ext:
  "con_assms \<Longrightarrow> cW_step pcw s s' \<Longrightarrow> pcR (rb s)= pcR (rb s')"  
  apply(cases "pcw", simp_all add:functs)
  apply(cases "count (rb s)", simp_all add:functs)
   apply(cases "0<n", simp_all)
    apply(cases "s=s'", simp_all add:acq_def functs)
  apply(cases "count (rb s)<n", simp_all)
   apply(cases "s=s'", simp_all add:acq_def functs)
  done


lemma pcW_stable_ext:
  "con_assms \<Longrightarrow> cR_step pcr s s' \<Longrightarrow> pcW (rb s)= pcW (rb s')"  
  apply(cases "pcr", simp_all add:functs)
  apply(cases "q s =[]", simp_all add:read_def functs)
  apply(cases "countR(rb s) =n", simp_all add:read_def functs)
  done


lemma W_doesnt_move_T:
  assumes "H (rb s)\<noteq> T (rb s)"
  and "H (rb s)\<noteq>0" 
  and "cW_step pcw s s'"
  and "pcw\<noteq>A3" 
shows "T (rb s) = T (rb s')"
  using assms
  apply(auto)
  apply(cases "pcw", simp_all add:functs)
  apply(cases "count(rb s)<n", simp_all add:functs acq_def)
  done
      

