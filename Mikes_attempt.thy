theory Mikes_attempt
imports Main HOL.List
begin 

datatype PCW =
  A1 | A2 | A3 | A4 | A5 | A6 | A7 | A8
| OK "nat\<times>nat"  | idleW | OOM | FinishedW

datatype PCR =
  R1 "nat\<times>nat" 
  | idleR 


datatype Thread = W | R
datatype Pointer = Head | Tail
datatype F0 = Arr\<^sub>W | Arr\<^sub>R | W | R | Q
datatype F1 = B | W | Q | R
datatype F2 = W | Q | R
consts n :: nat   (*size of buffer, input*)
consts N :: nat   (*number of Arr\<^sub>W entries*)


definition "con_assms \<equiv>   0 < N \<and> 0<n"


(*Recorded variables*)
record rb_state =
  H :: nat
  T :: nat
  hW ::  nat               (*local copy of W*)
  tW ::  nat               (*local copy of W*)
  count :: nat
  temp :: nat         (*local copy of word by W*)
  pcW :: PCW           (*records program counter of W*)
  pcR :: PCR           (*records program counter of W*)
  own0 :: "nat \<Rightarrow> F0"
  own1 :: "nat \<Rightarrow> F1"
  own2 :: "Pointer \<Rightarrow> F2"
  RFlag :: "nat \<Rightarrow> bool"
  WFlag :: "nat \<Rightarrow> bool"
  arrayW:: "nat  \<Rightarrow> nat"     (*returns a word arrayW_i*)
  arrayR:: "nat  \<Rightarrow> nat"     (*returns a word arrayR_i*)


definition push_H :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`H := _" [200])
  where 
  "push_H v \<equiv> \<lambda>s. s \<lparr>H := v\<rparr>"

definition push_T :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`T := _" [200])
  where 
  "push_T v \<equiv> \<lambda>s. s \<lparr>T := v\<rparr>"

definition set_WFlag :: "nat \<Rightarrow> bool \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`WFlag _ := _" [200])  where
  "set_WFlag ord v  \<equiv> \<lambda>s. s \<lparr> WFlag  := ((WFlag s) (ord := v))\<rparr>"

definition set_RFlag :: "nat \<Rightarrow> bool \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`RFlag _ := _" [200])  where
  "set_RFlag ord v  \<equiv> \<lambda>s. s \<lparr> RFlag  := ((RFlag s) (ord := v))\<rparr>"

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

definition set_temp :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`temp := _" [200]) where
  "set_temp v \<equiv> \<lambda>s. s \<lparr> temp := v\<rparr>"

definition update_pcW :: "PCW \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`pcW := _" [200]) where
  "update_pcW v \<equiv> \<lambda>s. s \<lparr> pcW := v\<rparr>"

definition update_pcR :: "PCR \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`pcR := _" [200]) where
  "update_pcR v \<equiv> \<lambda>s. s \<lparr> pcR := v\<rparr>"

definition set_arrayR :: "nat \<Rightarrow> nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`arrayR _ := _" [200])  where
  "set_arrayR ord v  \<equiv> \<lambda>s. s \<lparr> arrayR  := ((arrayR s) (ord := v))\<rparr>"

abbreviation update_b_err :: "rb_state \<Rightarrow> rb_state" ("ERROOM") where
  "update_b_err \<equiv> \<lambda>s. s \<lparr> pcW := OOM \<rparr>"


lemmas functs  = push_H_def push_T_def set_hW_def set_tW_def
                        update_count_def set_temp_def 
                        update_pcW_def update_pcR_def set_arrayR_def
                        set_WFlag_def set_RFlag_def

record c_state = 
  q :: "(nat \<times> nat) list"
  rb :: rb_state




abbreviation update_q :: "(nat \<times> nat) list \<Rightarrow> c_state \<Rightarrow> c_state" ("`q := _" [200])
  where 
  "update_q v  \<equiv> \<lambda>s. s \<lparr>q := v\<rparr>"
(***********************************************************************)



(* Define the states threads can find themselves in *)

definition "ACQ_PCW \<equiv> {A2, A3, A4, A5, A6, A7, A8, A1} \<union> {v. (\<exists> l k. v = OK (l, k))}"
definition "EXT_PCW \<equiv> {OOM, idleW, FinishedW} \<union> {v. (\<exists> l k. v = OK (l, k))}"
definition "ACQ_PCR \<equiv> {v. (\<exists> i. v = R1 i)}"
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
                        \<and> (\<forall>l. (l<n) \<longrightarrow>  arrayW (rb s) l > 0) \<and> (\<forall>l. arrayW (rb s) l < N)
                        \<and> (\<forall>l. (l<n) \<longrightarrow>  arrayR (rb s) l = 0)
                        \<and> (\<forall>p. (p<n) \<longrightarrow>\<not>WFlag (rb s) p) \<and> (\<forall>q. (q<n) \<longrightarrow>\<not>RFlag (rb s) q)
                        \<and> (\<forall>i. (i<n) \<longrightarrow>  own0 (rb s) i = Arr\<^sub>W) \<and> (\<forall>j. (j<N) \<longrightarrow>  own1 (rb s) j = B)
                        \<and> (own2 (rb s) Head = W) \<and> (own2 (rb s) Tail = Q) \<and> (count (rb s) = 0)"
(***********************************************************************)






(*Writer Thread Behaviour*)

fun rbW_step :: "PCW \<Rightarrow> rb_state \<Rightarrow> rb_state" where
  "rbW_step A1 s = ((`temp := (arrayW s (count s))) \<circ> (`hW := (H s)) \<circ> (`tW := (T s)) \<circ> (`pcW := A2)) s "
| "rbW_step A2 s = (if grd1 s then (`pcW := A3)
                     else if grd2 s then (`pcW := A4) 
                     else if grd3 s then (`pcW := A5) 
                     else (`pcW :=A8)) s"
| "rbW_step A3 s = ((`T := 0) \<circ> (`H := (temp s))  \<circ> (`pcW := (OK (0,temp s)))) s" 
| "rbW_step A4 s = ((`H := ((hW s) + (temp s)))  \<circ> (`pcW := (OK(hW s, temp s)))) s"
| "rbW_step A5 s = (if grd4 s then (`pcW := A6)  
                     else if grd5 s then (`pcW := A7)
                     else (`pcW := A8)) s"
| "rbW_step A6 s = (`H := ((hW s) + (temp s)) \<circ> `pcW := (OK(hW s, temp s))) s"
| "rbW_step A7 s = ((`H := (temp s)) \<circ> `pcW := (OK(0, temp s))) s"
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
        OK v \<Rightarrow>  q s' = (append (q s) [v]) 
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
   "rbR_step (R1 k) s = (`T := (off k + len k) \<circ> (`pcR := idleR)) s"


definition "read s s' \<equiv> (pcR (rb s) \<in> {idleR})
                              \<and> (let q_hd = hd (q s) ; 
                                     q_tl = tl (q s) 
                                 in q s' =  q_tl
                                 \<and> rb s' = (`pcR := (R1 q_hd)) (rb s))"

definition cR_step :: "PCR \<Rightarrow> c_state \<Rightarrow> c_state \<Rightarrow> bool" where
 "cR_step pcr s s' \<equiv> 
    case pcr of
        idleR \<Rightarrow> if (q s=[]) then (s=s') else (read s s') 
      | R1 k  \<Rightarrow>  q s' = q s \<and> (rb s') = rbR_step (R1 k) (rb s)"
(***********************************************************************)





definition "inRange v \<equiv> 0 \<le> v \<and> v \<le> N"

definition "inRangeHT s \<equiv> inRange (H s) \<and> inRange (T s)"

definition "H0_T0 s \<equiv> H s = 0 \<longrightarrow> T s = 0"

definition "inRangeht s \<equiv> inRange (hW s) \<and> inRange (tW s)"



definition inv :: "PCW \<Rightarrow> PCR \<Rightarrow> c_state \<Rightarrow> bool " where
"inv pcw pcr c \<equiv> 
   (let s = rb c in
    inRangeHT s \<and> H0_T0 s
    \<and> (\<forall> qb \<in> set (q c) . inRange (off qb + len qb)) 
    \<and> (pcw \<in> ACQ_PCW \<longrightarrow> (temp s > 0) \<or> (pcW s = A1))
    \<and> 
    (case pcw of
           A1     \<Rightarrow> arrayW s (count s) > 0  
         | A2     \<Rightarrow> H s = hW s \<and> inRangeht s
         | A3     \<Rightarrow> H s = hW s \<and> temp s \<le> N 
         | A4     \<Rightarrow> H s = hW s \<and> hW s + temp s \<le> N \<and> hW s + temp s > 0
         | A5     \<Rightarrow> H s = hW s \<and> tW s < hW s \<and> inRangeht s
         | A6     \<Rightarrow> H s = hW s \<and> inRangeht s \<and> hW s + temp s \<le> N \<and> hW s + temp s > 0
         | A7     \<Rightarrow> H s = hW s \<and> inRangeht s \<and> temp s < tW s 
         | A8     \<Rightarrow> H s = hW s

         | OK rv  \<Rightarrow> inRange (off rv + len rv) \<and> 0 < H s

         | idleW  \<Rightarrow> (q c \<noteq> [] \<longrightarrow> 0 < H s) 
         | OOM    \<Rightarrow> True
         | FinishedW \<Rightarrow> count s = n)
    \<and>
    (case pcr of
           R1 v  \<Rightarrow> inRange (off v + len v) \<and> (0 < H s) 
         | idleR  \<Rightarrow> (q c \<noteq> [] \<longrightarrow> (0 < H s)))
  )"


lemmas inv_simps [simp] = H0_T0_def inv_def inRangeHT_def inRange_def inRangeht_def 
                    cW_step_def cR_step_def init_def

lemmas ACQ_EXT [simp] = ACQ_PCR_def ACQ_PCW_def EXT_PCW_def EXT_PCR_def


lemma inv_init:
  assumes "init s"
    and "pcw = (pcW (rb s))"
    and "pcr = (pcR (rb s))"
  shows "inv pcw pcr s"
  using assms  by (simp)

lemma R_doesnt_move_H:
  assumes "con_assms"
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

lemmas moves = R_doesnt_move_H

                  
                    

lemma inv_local_W_int: 
  assumes "con_assms"
  and "pcw = pcW (rb s)"
  and "inv pcw (pcR (rb s)) s" 
  and "cW_step pcw s s'"
  and "count (rb s) \<le>n"
  and "pcw \<noteq> pcW (rb s')"
  and "\<forall>l. ArrW (rb s) l < N"
shows "inv (pcW (rb s')) (pcR (rb s')) s'"
  using assms 
  apply(auto)
  apply(unfold functs)
  apply(unfold acq_def)
  apply (case_tac[!] "pcW (rb s)", simp_all add: functs)
          apply (case_tac[!] "pcR (rb s)", simp_all add: functs)
          apply (case_tac[!]  "pcW (rb s')", simp_all add: functs)
               apply (case_tac[!] "tW (rb s) = hW (rb s) \<and> temp (rb s) \<le> N", simp_all add: Let_def)
               apply (case_tac[!] " hW (rb s) < tW (rb s) \<and> temp (rb s) \<le> tW (rb s) - hW (rb s)", simp_all)
               apply (case_tac[!] "temp (rb s) \<le> N - hW (rb s)", simp_all add:functs)
               apply (case_tac[!] "N < temp (rb s)", simp_all add:functs)
                      apply(case_tac[!] "tW (rb s) < hW (rb s)", simp_all add:functs, meson)
                      apply(case_tac[!] "count (rb s) < n", simp_all add:functs)
  apply(linarith+)
  done
          


lemma inv_local_R_int: 
  assumes "con_assms"
  and "pcr = pcR (rb s)"
  and "pcw = pcW (rb s)" 
  and "inv pcw pcr s" 
  and "pcW (rb s) = pcW (rb s')"
  and "cR_step pcr s s'"
shows "inv pcw (pcR (rb s')) s'"
   using assms 
  apply auto
  apply (case_tac[!] "pcW (rb s')",  simp_all add: Let_def)
             apply(case_tac[!] "pcR (rb s)", simp_all add: functs)
             apply(case_tac[!] "q s=[]", simp_all add:read_def functs)
                      apply (simp_all add: list.set_sel(2))
  done



lemma inv_global_W_int:
  assumes "con_assms"
  and "pcr = pcR (rb s)"
  and "pcw = pcW (rb s)"
  and "inv pcw pcr s"
  and "cR_step pcr s s'"
shows "inv (pcW (rb s')) (pcR (rb s')) s'"
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
