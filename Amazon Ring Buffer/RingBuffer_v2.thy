theory RingBuffer_v2
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




(*Recorded variables*)
record rb_state =
  H :: nat
  T :: nat
  hW ::  nat               (*local copy of W*)
  tW ::  nat               (*local copy of W*)
  offset :: nat
  q :: "(nat \<times> nat) list"
  data_index :: "(nat \<times> nat) \<Rightarrow> nat"   (*state of the buffer contents*)
  pcW :: PCW           (*records program counter of W*)
  pcR :: PCR           (*records program counter of W*)
  tempR :: "(nat \<times> nat)"          (*local copy of word by R*)
  Data:: "nat  \<Rightarrow> nat"     (*returns a word Data_i*)

  tR :: nat
  next_read :: nat
  has_written :: nat
  has_enqueued :: nat  (* how many words from Data the writer has enqueued  *)
  has_dequeued :: nat  (* how many words from Data the reader has retrieved *)
  ownT ::  F
  ownD :: "nat \<Rightarrow> F" (* ownership of Data indices *)
  ownB :: "F \<Rightarrow> (nat\<times>nat)" (* ownership of bytes in buffer, from - up to *)
  tries :: nat

  

definition "con_assms s \<equiv>   0 < N \<and> 0<n  \<and> N>n \<and> has_enqueued s\<le>n \<and> (has_dequeued s\<le>has_enqueued s)
                             \<and> (\<forall>i.(i<n)\<longrightarrow>Data s i\<le>N \<and> Data s i>0 \<and> tries s<N)"
definition push_H :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`H := _" [200])
  where 
  "push_H v \<equiv> \<lambda>s. s \<lparr>H := v\<rparr>"
definition push_T :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`T := _" [200])
  where 
  "push_T v \<equiv> \<lambda>s. s \<lparr>T := v\<rparr>"
definition write_data_index :: "nat \<times> nat \<Rightarrow> nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`B.write _ := _" [200])  where
  "write_data_index a v  \<equiv>  
      \<lambda>s. s \<lparr> data_index  := \<lambda> x. if  a = x  then v else data_index s x \<rparr>"  
definition change_writes :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`haswritten := _" [200])
  where 
  "change_writes v \<equiv> \<lambda>s. s \<lparr>has_written := v\<rparr>"
definition change_reads :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`hasread := _" [200])
  where 
  "change_reads v \<equiv> \<lambda>s. s \<lparr>next_read := v\<rparr>"
definition push_offset :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`offset := _" [200])
  where 
  "push_offset v \<equiv> \<lambda>s. s \<lparr>offset := v\<rparr>"
definition inc_tries :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`tries := _" [200])
  where 
  "inc_tries v \<equiv> \<lambda>s. s \<lparr>tries := v\<rparr>"

definition trans_ownT :: "F \<Rightarrow> F \<Rightarrow> rb_state \<Rightarrow> rb_state \<Rightarrow> rb_state" ("transownT [_ _ _]" [200]) where
  "trans_ownT a b s \<equiv> if ownT s = a then (\<lambda>s. s \<lparr> ownT := b \<rparr>)
                                    else (\<lambda>s. s \<lparr> ownT := ownT s\<rparr>)"
(* change this, to make it less straining*)
definition transfer_ownB :: "F \<Rightarrow> F \<Rightarrow> rb_state \<Rightarrow> rb_state" ("transownB [_ _]" [200]) where
  "transfer_ownB a b \<equiv> (\<lambda>s. s \<lparr> ownB := \<lambda> i. if i=b then (fst(ownB s b),snd(ownB s a)) else
                                             if i=a then (0,0) else ownB s i\<rparr>)"

definition set_ownB :: "F \<Rightarrow> F \<Rightarrow> nat\<times>nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("setownB [_ _ _]" [200]) where
  "set_ownB a b x \<equiv> (\<lambda>s. s \<lparr> ownB := \<lambda> i. if i=b then (fst(ownB s a),snd(x)) else 
                                          if i=a then (snd(x),snd(ownB s a)) else ownB s i\<rparr>)"

definition reset_ownB :: "nat\<times>nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`resetownB _" [200]) where
  "reset_ownB x \<equiv> (\<lambda>s. s \<lparr> ownB := \<lambda> i. if i=B then (snd(x),N+1) else
                                        if i=W then (0,snd(x)) else
                                                    (0,0)\<rparr>)"

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
definition update_has_enqueued :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`hasenqueued := _" [200]) where
  "update_has_enqueued v\<equiv> \<lambda>s. s \<lparr> has_enqueued := v\<rparr>"
definition update_has_dequeued :: "nat \<Rightarrow> rb_state \<Rightarrow> rb_state" ("`hasdequeued := _" [200]) where
  "update_has_dequeued v\<equiv> \<lambda>s. s \<lparr> has_dequeued := v\<rparr>"
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
                        update_has_enqueued_def update_has_dequeued_def
                        set_tempR_def 
                        update_pcW_def update_pcR_def
                        transfer_ownB_def transfer_ownD_def trans_ownT_def
                        update_q_def  inc_tries_def
                        push_offset_def write_data_index_def
                        change_writes_def change_reads_def
                        set_tR_def set_ownB_def reset_ownB_def





(*  Define the if statement "guards"  *)

definition "off bo \<equiv> fst bo"
definition "len bo \<equiv> snd bo"
definition "grd1 s \<equiv> (tW s = hW s) \<and> (Data s (has_enqueued s) \<le> N)"
definition "grd2 s \<equiv> (tW s > hW s) \<and> (Data s (has_enqueued s) < (tW s - hW s))"
definition "grd3 s \<equiv> tW s < hW s"
definition "grd4 s \<equiv> Data s (has_enqueued s) \<le> N - hW s"
definition "grd5 s \<equiv> Data s (has_enqueued s) < tW s"
definition "no_space_for_word s \<equiv> (grd1 s \<longrightarrow> \<not>(Data s (has_enqueued s) \<le> N))\<and>
                                  (grd2 s \<longrightarrow> \<not>(Data s (has_enqueued s) < (tW s - hW s)))\<and>
                                  (grd3 s \<longrightarrow> \<not>(Data s (has_enqueued s) \<le> N - hW s \<or> Data s (has_enqueued s) < tW s))"
lemmas grd_simps [simp] = off_def len_def grd1_def grd2_def grd3_def grd4_def grd5_def no_space_for_word_def 
(***********************************************************************)





(*  Initial State  *)

definition "init s \<equiv> (H s = 0) \<and> (T s = 0) \<and> (offset s = 0) \<and> q s = [] \<and> (hW s = 0) \<and> (tW s = 0) \<and> (tR s = 0)
                        \<and> next_read s = 0 \<and> has_written s = 0 \<and> (has_enqueued s = 0) \<and> (has_dequeued s = 0)
                        \<and> ( pcW s = idleW)
                        \<and> ( pcR s = idleR)
                        \<and> (\<forall>l. (l<n) \<longrightarrow>  ((Data s l > 0)\<and>(Data s l \<le> N)))
                        \<and> (\<forall>i. (i<n) \<longrightarrow>  ownD s i = W)
                        \<and> (ownB s B = (0,N+1) \<and> (\<forall>i.(i\<in>F1_set \<and> i\<noteq>B)\<longrightarrow>(ownB s i = (0,0))))
                        \<and> (ownT s = Q)
                        \<and> (tempR s = (0,0))
                        \<and> (tries s=0)
                        \<and> (\<forall>i. (i\<le>N)\<longrightarrow>(\<forall>j.(j\<le>N)\<longrightarrow>data_index s (i,j) <n))"
(***********************************************************************)



(*   State of the queue   *)
(*   What Q should look like   *)
definition "Q_boundness s       \<equiv> (\<forall>i.(i<length(q s))\<longrightarrow>fst(q s!i)+snd(q s!i)\<le>N)
                                  \<and> (fst(tempR s)+snd(tempR s)\<le>N)" 

definition "Q_gap_structure s   \<equiv> \<forall>i.(i<length(q s)\<and>i>0)\<longrightarrow>
              ((fst(q s!(i-1))<fst(q s!i) \<and> fst(q s!(i-1))+snd(q s!(i-1)) = fst(q s!i)) 
             \<or>(fst(q s!i) =0))"

definition "Q_offsets_differ s  \<equiv> \<forall>i.(i<length(q s))\<longrightarrow>(\<forall>j.(j>i\<and>j<length(q s))\<longrightarrow>fst(q s!i)\<noteq>fst(q s!j))"

definition "Q_elems_arent_neg s \<equiv> \<forall>i.(i<length(q s))\<longrightarrow>fst(q s!i)\<ge>0 \<and> snd(q s!i)>0"

definition "Q_has_no_overlaps s \<equiv> \<forall>i.(i<length(q s))\<longrightarrow>(\<forall>j.(j>i \<and> j<length(q s)) \<longrightarrow>       
                   ((fst(q s!i)<fst(q s!j)\<and> fst(q s!i)+snd(q s!i)\<le>fst(q s!j))
                  \<or>(fst(q s!j)+snd(q s!j)\<le> fst(q s!i))))"

definition "Q_no_overlap_tempR s\<equiv> if tempR s\<noteq>(0,0)then
                          (\<forall>i.(i<length(q s))\<longrightarrow>
                  ((fst(q s!i)>fst(tempR s)\<and>snd(tempR s)+fst(tempR s)\<le> fst(q s!i))
                  \<or>(fst(q s!i)<fst(tempR s)\<and>snd(q s!i)+fst(q s!i)<fst(tempR s))))
                                                  else True"

definition "Q_relates_tempR s   \<equiv> tempR s\<noteq>(0,0)\<longrightarrow> ((fst(tempR s)+snd(tempR s) = fst(q s!0))
                       \<or> ((fst(q s!0) = 0) \<and> (\<forall>i.(i<length(q s)\<longrightarrow>fst(tempR s)+snd(tempR s)>fst(q s!i)+
                                                                                          snd(q s!i)))))"

definition "Q_has_no_uroboros s \<equiv> fst(q s!0)\<noteq> (fst(q s!(length(q s)-1))+snd(q s!(length(q s)-1))) \<and>
                     tempR s\<noteq>(0,0)\<longrightarrow>fst(tempR s)\<noteq> (fst(q s!(length(q s)-1))+snd(q s!(length(q s)-1)))"

(*   Relating Q to other variables   *)

definition "Q_holds_bytes s     \<equiv> ownB s Q = (fst(q s!0), fst(q s!(length(q s)-1))+ snd(q s!(length(q s)-1)))"

definition "Q_reflects_writes s \<equiv> \<forall>i.(i<length(q s))\<longrightarrow>data_index s (fst(q s!i),fst(q s!i)+snd(q s!i)) 
                                            = has_dequeued s +i"

definition "Q_elem_size s       \<equiv> \<forall>i.(i<length(q s))\<longrightarrow>snd(q s!i) =Data s (has_dequeued s +i)"

definition "Q_reflects_ownD s   \<equiv> (\<forall>i.(i<length(q s))\<longrightarrow>ownD s (i+has_dequeued s) =B)"



definition "Q_dictates_pos_T s  \<equiv> (T s=fst(q s!0) \<and> tempR s=(0,0)) 
                                \<or> (T s=fst(tempR s) \<and> tempR s\<noteq>(0,0))
   \<or> ((\<forall>i.(i<length(q s))\<longrightarrow>T s>fst(q s!i)+snd(q s!i))\<and> tempR s=(0,0))
   \<or> ((\<forall>i.(i<length(q s))\<longrightarrow>T s>fst(q s!i)+snd(q s!i))\<and> snd(tempR s)\<noteq>0 \<and> fst(tempR s) =0\<and> T s>fst(tempR s))"


definition "Q_structure s \<equiv>q s\<noteq>[]\<longrightarrow>(Q_boundness s\<and> Q_gap_structure s \<and> Q_offsets_differ s \<and>
                                      Q_elems_arent_neg s \<and> Q_has_no_overlaps s \<and> Q_has_no_uroboros s \<and>
                                      Q_holds_bytes s \<and> Q_reflects_writes s \<and> Q_elem_size s \<and> 
                                      Q_reflects_ownD s \<and> Q_dictates_pos_T s \<and> 
                                      Q_no_overlap_tempR s \<and> Q_relates_tempR s)"

lemmas Q_lemmas = Q_holds_bytes_def Q_reflects_writes_def Q_reflects_ownD_def
                  Q_has_no_overlaps_def
                  Q_structure_def Q_gap_structure_def Q_has_no_uroboros_def
                  Q_dictates_pos_T_def Q_boundness_def Q_offsets_differ_def
                  Q_elems_arent_neg_def Q_elem_size_def Q_no_overlap_tempR_def
                  Q_relates_tempR_def


  
lemma Q_type_10:
  assumes "q s=[(4,1),(5,1)]"
  and "N = 10"
  and "tempR s=(2,2)"
  and "Q_structure s"
  and "has_dequeued s =1"
  and "T s=2"
  shows "ownB s Q = (4,6)"
  using assms
  by(simp_all add:Q_lemmas)
  


(*Writer Thread Behaviour*)


fun rbW_step :: "PCW \<Rightarrow> rb_state \<Rightarrow> rb_state" where
  "rbW_step A1 s = ((`hW := (H s)) \<circ> (`tW := (T s)) \<circ> (`pcW := A2)) s "
| "rbW_step A2 s = (if grd1 s then ((`pcW := A3) \<circ> (transownT [Q W s]) \<circ> resetownD)
                     else if grd2 s then (`pcW := A4) 
                     else if grd3 s then (`pcW := A5) 
                     else (`pcW :=A8)) s"
| "rbW_step A3 s = ((`T := 0) \<circ> (`H := (Data s (has_enqueued s))) \<circ> (`offset := 0) \<circ> (`pcW := Write) 
                        \<circ> setownB [Q W (0,(Data s (has_enqueued s)))]) s" 
| "rbW_step A4 s = ((`H := ((hW s) + (Data s (has_enqueued s)))) \<circ> (`offset := (hW s)) \<circ> (`pcW := Write)
                        \<circ> setownB [Q W(hW s,hW s+Data s (has_enqueued s))]) s"
| "rbW_step A5 s = (if grd4 s then (`pcW := A6)  
                     else if grd5 s then (`pcW := A7)
                     else (`pcW := A8)) s"
| "rbW_step A6 s = (`H := ((hW s) + (Data s (has_enqueued s))) \<circ> (`offset := (hW s)) \<circ> (`pcW := Write)
                        \<circ> setownB [Q W (hW s,hW s+Data s (has_enqueued s))]) s"
| "rbW_step A7 s = ((`H := (Data s (has_enqueued s))) \<circ> (`offset := 0) \<circ> (`pcW := Write)
                        \<circ> (setownB [Q W (hW s,Data s (has_enqueued s))])) s"
| "rbW_step A8 s = (if ((Data s (has_enqueued s))>N) then ERRBTS s
                        else (ERROOM \<circ> (`tW := (T s))) s)"

| "rbW_step Write s = s"
| "rbW_step Enqueue s = s"| "rbW_step idleW s = s" | "rbW_step FinishedW s = s"| "rbW_step BTS s = s"| "rbW_step OOM s = s"



definition "B_acquire s s' \<equiv> ((pcW s \<in> {idleW})
                            \<and> (Data s (has_enqueued s)) > 0 
                            \<and> s' = (`pcW := A1) s)"

definition "Q_enqueue s s' \<equiv> s' = (`q:=(append (q s) [(offset s,Data s (has_enqueued s))])
                     \<circ> `pcW := idleW
                     \<circ>  transownB [W Q]
                     \<circ> `hasenqueued := (has_enqueued s + 1)
                     \<circ> `tries := 0 
                     \<circ>  transownT [W Q s]) s"

definition "B_write s s' \<equiv> s' = ((`B.write ((offset s), (Data s (has_enqueued s))):= (has_enqueued s))
                      \<circ> (transownD [(has_written s) B]) \<circ> `pcW := Enqueue \<circ> (`haswritten := ((has_written s )+1))) s"

definition cW_step :: "PCW \<Rightarrow> rb_state \<Rightarrow> rb_state \<Rightarrow> bool" where
 "cW_step pcw s s' \<equiv> 
    case pcw of
        idleW     \<Rightarrow>  if ((has_enqueued s) < n) then B_acquire s s'
                          else s' = (`pcW := FinishedW \<circ> `tries := 0 ) s
      | Write     \<Rightarrow>  B_write s s'   
      | Enqueue   \<Rightarrow>  Q_enqueue s s'
      | OOM       \<Rightarrow>  if tW s \<noteq> T s then s' = (`pcW := idleW \<circ> `tries := (tries s + 1)) s else s = s'
      | FinishedW \<Rightarrow>  s = s'
      | BTS       \<Rightarrow>  s = s'
      | _         \<Rightarrow>  s' = rbW_step pcw s "

lemmas W_functs [simp] = B_acquire_def B_write_def Q_enqueue_def
(*---------Tailored assertions to Writer-------*)
definition "pre_acquire_inv s   \<equiv> ownT s \<noteq>W
                                \<and> T s=H s\<longrightarrow>(N-(ownB s B \<and> ownT s =Q \<and> q s=[] \<and> has_dequeued s=has_enqueued s)
                                \<and> (T s>H s \<longrightarrow> (\<forall>i.(i\<ge>H s \<and> i<T s)\<longrightarrow>ownB s i=B))
                                \<and> (T s<H s \<longrightarrow> (\<forall>i.(i\<ge>H s \<and> i\<le>N \<or> i<T s)\<longrightarrow>ownB s i=B))
                                \<and> has_written s=has_enqueued s
                                \<and> has_enqueued s\<le>n"
definition "pre_A1_inv s        \<equiv> T s=H s\<longrightarrow>((\<forall>i.(i\<ge>0 \<and> i\<le>N)\<longrightarrow>ownB s i=B) \<and> ownT s =Q \<and> q s=[])
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> ownT s \<noteq>W
                                \<and> (T s>H s \<longrightarrow> (\<forall>i.(i\<ge>H s \<and> i<T s)\<longrightarrow>ownB s i=B))
                                \<and> (T s<H s \<longrightarrow> (\<forall>i.(i\<ge>H s \<and> i\<le>N \<or> i<T s)\<longrightarrow>ownB s i=B))
                                \<and> has_written s=has_enqueued s
                                \<and> has_enqueued s<n"
definition "pre_A2_inv s        \<equiv> tW s=hW s\<longrightarrow>(\<forall>i.(i\<ge>0 \<and> i\<le>N)\<longrightarrow>ownB s i=B \<and> ownT s =Q \<and> q s=[])
                                \<and> (tW s>hW s \<longrightarrow> (\<forall>i.(i\<ge>hW s \<and> i<tW s)\<longrightarrow>ownB s i=B))
                                \<and> (tW s<hW s \<longrightarrow> (\<forall>i.(i\<ge>hW s \<and> i\<le>N \<or> i<tW s)\<longrightarrow>ownB s i=B))
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> ownT s \<noteq>W
                                \<and> has_written s=has_enqueued s \<and> has_enqueued s<n"
definition "pre_A3_inv s        \<equiv> (\<forall>i.(i\<ge>0 \<and> i\<le>N)\<longrightarrow>ownB s i=B \<and> ownT s =Q \<and> q s=[])
                                \<and> grd1 s
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> ownT s =W
                                \<and> has_written s=has_enqueued s \<and> has_enqueued s<n" 
definition "pre_A4_inv s        \<equiv> (\<forall>i.(i\<ge>hW s \<and> i<tW s)\<longrightarrow>ownB s i=B)
                                \<and> grd2 s \<and> (\<not>grd1 s)
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> ownT s \<noteq>W
                                \<and> has_written s=has_enqueued s \<and> has_enqueued s<n"
definition "pre_A5_inv s        \<equiv> (\<forall>i.(i\<ge>hW s \<and> i<N \<or> i<tW s)\<longrightarrow>ownB s i=B)
                                \<and> grd3 s \<and> (\<not>grd1 s) \<and> (\<not>grd2 s)
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> ownT s \<noteq>W
                                \<and> has_written s=has_enqueued s \<and> has_enqueued s<n"
definition "pre_A6_inv s        \<equiv> (\<forall>i.(i\<ge>hW s \<and> i<N \<or> i<tW s)\<longrightarrow>ownB s i=B)
                                \<and> grd4 s \<and> grd3 s \<and> (\<not>grd1 s) \<and> (\<not>grd2 s)
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> ownT s \<noteq>W
                                \<and> has_written s=has_enqueued s \<and> has_enqueued s<n"
definition "pre_A7_inv s        \<equiv> (\<forall>i.(i\<ge>hW s \<and> i<N \<or> i<tW s)\<longrightarrow>ownB s i=B)
                                \<and> grd5 s \<and> grd3 s \<and> (\<not>grd1 s) \<and> (\<not>grd2 s) \<and> (\<not>grd4 s)
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> ownT s \<noteq>W
                                \<and> has_written s=has_enqueued s \<and> has_enqueued s<n"
definition "pre_A8_inv s        \<equiv> (\<forall>i.(i\<ge>hW s \<and> i<N \<or> i<tW s)\<longrightarrow>ownB s i=B)
                                \<and> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> ownT s \<noteq>W
                                \<and> has_written s=has_enqueued s
                                \<and> no_space_for_word s \<and> has_enqueued s<n"
definition "pre_write_inv s     \<equiv> \<forall>i.(i\<ge>offset s \<and> i< ((offset s)+(Data s (has_enqueued s))))\<longrightarrow>ownB s i=W
                                \<and> ((tW s>hW s)\<longrightarrow>(\<forall>j.(j\<ge>((offset s)+(Data s (has_enqueued s)))\<and>j<tW s)\<longrightarrow>ownB s i =B))
                                \<and> ((tW s<hW s \<and> offset s\<noteq>0)\<longrightarrow>(\<forall>j.(j\<ge>((offset s)+(Data s (has_enqueued s))) \<and> j\<le>N\<or>j<tW s)\<longrightarrow>ownB s i =B))
                                \<and> ((tW s<hW s \<and> offset s=0)\<longrightarrow>((\<forall>j.(j\<ge>((offset s)+(Data s (has_enqueued s))) \<and> j<tW s)\<longrightarrow>ownB s i =B))\<and> (\<forall>k.(k\<ge>hW s \<and> k<N)\<longrightarrow>ownB s k=W))
                                \<and> (tW s=hW s\<longrightarrow>ownT s=W)
                                \<and> has_written s=has_enqueued s
                                \<and> has_enqueued s<n"
definition "pre_enqueue_inv s   \<equiv> \<forall>i.(i\<ge>offset s \<and> i< ((offset s)+(Data s (has_enqueued s))))\<longrightarrow>ownB s i=W
                                \<and> ((tW s>hW s)\<longrightarrow>(\<forall>j.(j\<ge>((offset s)+(Data s (has_enqueued s)))\<and>j<tW s)\<longrightarrow>ownB s i =B))
                                \<and> ((tW s<hW s \<and> offset s\<noteq>0)\<longrightarrow>(\<forall>j.(j\<ge>((offset s)+(Data s (has_enqueued s))) \<and> j\<le>N\<or>j<tW s)\<longrightarrow>ownB s i =B))
                                \<and> ((tW s<hW s \<and> offset s=0)\<longrightarrow>((\<forall>j.(j\<ge>((offset s)+(Data s (has_enqueued s))) \<and> j<tW s)\<longrightarrow>ownB s i =B))\<and> (\<forall>k.(k\<ge>hW s \<and> k<N)\<longrightarrow>ownB s k=W))
                                \<and> (tW s=hW s\<longrightarrow>ownT s=W)
                                \<and> has_written s=has_enqueued s +1
                                \<and> has_enqueued s<n"
definition "pre_OOM_inv s       \<equiv> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> ownT s \<noteq>W
                                \<and> (tW s>hW s \<longrightarrow> (\<forall>i.(i\<ge>tW s \<and> i<hW s)\<longrightarrow>ownB s i=B))
                                \<and> (tW s<hW s \<longrightarrow> (\<forall>i.(i\<ge>hW s \<and> i\<le>N \<or> i<tW s)\<longrightarrow>ownB s i=B))
                                \<and> has_written s=has_enqueued s \<and> has_enqueued s<n"
definition "pre_finished_inv s  \<equiv> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> ownT s \<noteq>W
                                \<and> has_written s=has_enqueued s
                                \<and> has_enqueued s=n"
definition "pre_BTS_inv s       \<equiv> (\<forall>j.(j\<ge>0\<and> j\<le>N)\<longrightarrow>ownB s j\<noteq>W)
                                \<and> ownT s \<noteq>W
                                \<and> has_written s=has_enqueued s
                                \<and> has_enqueued s<n"

lemmas writer_lemmas  = pre_A1_inv_def pre_A2_inv_def pre_A3_inv_def pre_A4_inv_def
                              pre_A5_inv_def pre_A6_inv_def pre_A7_inv_def pre_A8_inv_def
                              pre_BTS_inv_def pre_OOM_inv_def pre_acquire_inv_def
                              pre_finished_inv_def pre_enqueue_inv_def pre_write_inv_def
(***********************************************************************)









(*Reader Thread Behaviour*)

definition "B_release s s' \<equiv> s' = (`T := (off(tempR s) +len(tempR s)) 
                        \<circ> (`pcR := idleR) 
                        \<circ> (`tempR := (0,0))
                        \<circ> (transownB [R B]) 
                        \<circ> (if tR s\<noteq> fst(tempR s) then setownB [(tR s,N) B] else id) 
                        \<circ> transownT [R Q s]) s"

definition "B_read s s' \<equiv> s' = (((if ownD s (data_index s (tempR s)) = B then transownD [(data_index s (tempR s)) R] else id) 
                        \<circ> (`pcR := Release)) 
                        \<circ> (`hasread := ((next_read s)+1))  
                        \<circ> (`tR := (T s))) s"

definition "Q_dequeue s s' \<equiv> (let q_hd = hd (q s) ; 
                             q_tl = tl (q s) 
                                 in s' = (`q:= q_tl 
                                          \<circ> `pcR := Read
                                          \<circ> `tempR := q_hd
                                          \<circ>  transownT [Q R s]
                                          \<circ> (`hasdequeued :=(has_dequeued s+1))
                                          \<circ> (if (\<forall>i.(i\<ge>off(q_hd)\<and> i<off(q_hd)+len(q_hd))\<longrightarrow>ownB s i=Q) then 
                                                    setownB [(off(q_hd),(off(q_hd)+len(q_hd))) R] else id)) s)"

definition cR_step :: "PCR \<Rightarrow> rb_state \<Rightarrow> rb_state \<Rightarrow> bool" where
 "cR_step pcr s s' \<equiv> 
    case pcr of
        idleR \<Rightarrow> if (q s=[]) then (s=s') else (Q_dequeue s s')
      | Read \<Rightarrow>  B_read s s' 
      | Release \<Rightarrow>  B_release s s'"


lemmas R_functs [simp] = B_release_def B_read_def Q_dequeue_def
(*---------Tailored assertions to Reader-------*)
definition "pre_dequeue_inv s \<equiv> pcR s= idleR \<and> tempR s = (0,0) \<and> (q s \<noteq> [] \<longrightarrow> ownT s=Q)
                              \<and> (q s\<noteq>[]\<longrightarrow>(\<forall>i.(i\<ge>fst(hd(q s))\<and> i<fst(hd(q s))+snd(hd(q s)))\<longrightarrow>ownB s i=Q))
                              \<and> has_dequeued s\<le>n \<and> has_dequeued s\<ge>0
                              \<and> (q s\<noteq>[]\<longrightarrow>(next_read s=data_index s (hd(q s))))
                              \<and> has_dequeued s = next_read s
                             "
definition "pre_Read_inv s    \<equiv>  snd(tempR s) = Data s (next_read s)
                              \<and> (\<forall>i.(i<snd(tempR s)+fst(tempR s)\<and> i\<ge>fst(tempR s))\<longrightarrow>ownB s i=R)
                              \<and> next_read s=data_index s (tempR s) 
                              \<and> has_dequeued s\<le>n \<and> has_dequeued s\<ge>0 \<and> ownT s = R
                              \<and> next_read s+1=has_dequeued s
                              \<and> ownD s (next_read s) = B
                              \<and> (tR s\<noteq>fst(tempR s)\<longrightarrow>tR s>fst(tempR s)) \<and> H s\<ge>snd(tempR s)+fst(tempR s)
                              \<and> (tR s\<noteq>fst(tempR s)\<longrightarrow>fst(tempR s)=0)
                              \<and> ((tR s\<noteq>fst(tempR s))\<longrightarrow>(\<forall>i.(i\<ge>tR s\<and> i<N)\<longrightarrow>ownB s i=Q))"
definition "pre_Release_inv s \<equiv> (snd(tempR s) = Data s (next_read s -1))
                              \<and> data_index s (tempR s) = next_read s -1
                              \<and> (q s\<noteq>[]\<longrightarrow>(next_read s=data_index s (hd(q s))))
                              \<and> ownT s = R
                              \<and> (\<forall>i.(i<snd(tempR s)+fst(tempR s)\<and> i\<ge>fst(tempR s))\<longrightarrow>ownB s i=R)
                              \<and> tR s=T s
                              \<and> tempR s\<noteq>(0,0)
                              \<and> ownD s (next_read s -1) = R
                              \<and> has_dequeued s\<le>n \<and> has_dequeued s\<ge>1 
                              \<and> has_dequeued s = next_read s 
                              \<and> (tR s\<noteq>fst(tempR s)\<longrightarrow>tR s>fst(tempR s)) \<and> H s\<ge>snd(tempR s)+fst(tempR s)
                              \<and> (tR s\<noteq>fst(tempR s)\<longrightarrow>fst(tempR s)=0 \<and> tR s>fst(tempR s)+snd(tempR s))
                              \<and> ((tR s\<noteq>fst(tempR s))\<longrightarrow>(\<forall>i.(i\<ge>tR s\<and> i<N)\<longrightarrow>ownB s i=Q))"

definition "reader_situations s \<equiv> (pcR s = idleR \<longrightarrow> pre_dequeue_inv s)\<and>
                                  (pcR s = Read \<longrightarrow> pre_Read_inv s) \<and>
                                  (pcR s = Release \<longrightarrow> pre_Release_inv s)"

lemmas reader_lemmas [simp] = pre_Release_inv_def pre_Read_inv_def pre_dequeue_inv_def
(***********************************************************************)






definition "inRange v \<equiv> 0 \<le> v \<and> v \<le> N"
definition "inRangeHT s \<equiv> inRange (H s) \<and> inRange (T s)"
definition "H0_T0 s \<equiv> H s = 0 \<longrightarrow> T s = 0"
definition "inRangeht s \<equiv> inRange (hW s) \<and> inRange (tW s)"
definition "basic_pointer_movement s \<equiv> inRangeHT s \<and> inRangeht s \<and> H0_T0 s "

lemmas basic_pointer_movement_lemmas [simp] = basic_pointer_movement_def inRangeHT_def inRangeht_def H0_T0_def inRange_def


definition "mainInv s \<equiv> \<forall> i. (i<next_read s \<longrightarrow> ownD s i=R) \<and> (next_read s \<le> i \<and> i < has_written s \<longrightarrow> ownD s i = B) \<and> (has_written s \<le> i \<and> i < n \<longrightarrow> ownD s i = W) "
definition "counter_bounds s \<equiv> next_read s \<le>n \<and> has_written s\<le>n \<and> has_enqueued s\<le>n \<and> has_dequeued s \<le> n"
definition "counter_q_rel s \<equiv> (has_enqueued s-has_dequeued s=length(q s))\<and> has_written s\<ge>next_read s" 


(*new lemmas, take 2*)
definition "data_index_bouded s \<equiv> \<forall>i. (i\<le>N)\<longrightarrow>(\<forall>j.(j\<le>N)\<longrightarrow>data_index s (i,j)<n)" 



(*------------------------ Invariant ------------------------------------*)
definition inv :: "PCW\<Rightarrow>PCR\<Rightarrow>rb_state \<Rightarrow> bool " where
"inv pcw pcr s \<equiv> basic_pointer_movement s 
               \<and> mainInv s
               \<and> counter_q_rel s
               \<and> counter_bounds s 
                  \<and> data_index_bouded s
  \<and> (case pcw of
      A1 \<Rightarrow> pre_A1_inv s
    | A2 \<Rightarrow> pre_A2_inv s
    | A3 \<Rightarrow> pre_A3_inv s
    | A4 \<Rightarrow> pre_A4_inv s
    | A5 \<Rightarrow> pre_A5_inv s
    | A6 \<Rightarrow> pre_A6_inv s
    | A7 \<Rightarrow> pre_A7_inv s
    | A8 \<Rightarrow> pre_A8_inv s
    | Enqueue \<Rightarrow> pre_enqueue_inv s \<and> H s>0
    | Write \<Rightarrow> pre_write_inv s \<and> H s>0
    | idleW \<Rightarrow> (has_enqueued s=0\<longrightarrow>q s=[])\<and> pre_acquire_inv s
    | OOM \<Rightarrow> pre_OOM_inv s
    | BTS \<Rightarrow> pre_BTS_inv s
    | FinishedW \<Rightarrow> pre_finished_inv s) 
  \<and> (case pcr of
     Release \<Rightarrow> pre_Release_inv s \<and> has_enqueued s\<ge>has_dequeued s \<and> H s>0 \<and> H s \<noteq> T s
    | idleR \<Rightarrow> pre_dequeue_inv s
    | Read \<Rightarrow> pre_Read_inv s  \<and> has_enqueued s\<ge>has_dequeued s  \<and> H s>0 \<and> H s \<noteq> T s)
"




lemmas inv_simps =  inv_def cW_step_def cR_step_def init_def

lemmas invariant_lemmas [simp] = con_assms_def mainInv_def
                          counter_q_rel_def 
                          counter_bounds_def data_index_bouded_def






lemma inv_init:
  assumes "init s"
  and "con_assms s"
  shows "inv idleW idleR s"
  using assms 
  apply simp_all
  apply (simp_all add: inv_def Q_lemmas)
  apply(intro conjI impI)
  apply(simp_all add:init_def)
  by (simp add: pre_acquire_inv_def)

lemma inv_local_R_int: 
  assumes "con_assms s"
  and "pcr = pcR s"
  and "pcw = pcW s"
  and "Q_structure s"
  and "inv pcw pcr s"
  and "cR_step pcr s s'"
shows "inv pcw (pcR s') s'"
  using assms apply(simp add:inv_def Q_lemmas)
  apply(intro conjI impI)
  apply(case_tac[!] "pcR s", simp_all add:cR_step_def)
  apply(case_tac[!] "q s=[]", simp_all add:Let_def)
  apply(case_tac "T s \<noteq> fst (tempR s)", simp_all)
  apply(case_tac "(\<forall>i<length (q s). fst (q s ! i) + snd (q s ! i) < T s) \<and>
         0 < Data s (data_index s (hd (q s)) - Suc 0) \<and>
         fst (tempR s) = 0 \<and> fst (tempR s) < T s", simp_all)
  apply(case_tac "ownD s (data_index s (tempR s)) = B", simp_all)
  apply(case_tac "tempR s \<noteq> (0, 0)", simp_all)
  apply(case_tac "ownD s (data_index s (tempR s)) = B", simp_all)
  apply(case_tac "ownD s (data_index s (tempR s)) = B", simp_all)
  apply(case_tac "ownD s (data_index s (tempR s)) = B", simp_all)
  apply force
  apply force
  apply (metis F.distinct(5) Suc_le_eq le_Suc_ex trans_less_add1)
  apply metis
  apply (metis One_nat_def Suc_eq_plus1 diff_diff_add)
  apply (metis F.distinct(6) Suc_n_not_le_n le_less le_less_Suc_eq le_less_linear order_refl order_trans)
  apply (metis F.distinct(6) le_less not_less_eq_eq)
  apply (metis cancel_comm_monoid_add_class.diff_cancel le_antisym length_0_conv not_less_eq_eq order_trans)
           apply(case_tac "pcW s", simp)
  apply(simp add:pre_A1_inv_def)
  





  oops




(*
lemma inv_local_R_int: 
  assumes "con_assms s"
  and "inv (pcW s) (pcR s) s" 
  and "cR_step (pcR s) s s'"
shows "(case pcR s of
     Release \<Rightarrow> pre_Release_inv s \<and> has_enqueued s\<ge>has_dequeued s \<and> H s>0 \<and> H s \<noteq> T s
    | idleR \<Rightarrow> pre_dequeue_inv s
    | Read \<Rightarrow> pre_Read_inv s  \<and> has_enqueued s\<ge>has_dequeued s  \<and> H s>0 \<and> H s \<noteq> T s)"



  oops


  apply(case_tac "(\<forall>i<length (q s). fst (q s ! i) + snd (q s ! i) < T s) \<and>
          tempR s = (0, 0) \<or>
          (\<forall>i<length (q s). fst (q s ! i) + snd (q s ! i) < T s) \<and>
          0 < snd (tempR s) \<and> fst (tempR s) = 0 \<and> fst (tempR s) < T s", simp)
  apply(case_tac "tempR s \<noteq> (0, 0)", simp) (*5*)
  apply(intro conjI impI)
  apply metis
  apply metis
  apply (metis (no_types, lifting))
  apply (metis (no_types, lifting) gr_implies_not_zero length_greater_0_conv not_add_less1)
  apply (metis (no_types, hide_lams))
  apply metis
  apply (metis (no_types, lifting) gr_implies_not0 length_greater_0_conv not_add_less1)
                  apply metis
  apply(case_tac "pcW s"; simp add:writer_lemmas)
  
                      apply metis
  apply (metis (no_types, lifting))
  apply (metis (no_types, lifting) F.distinct(7) add.commute le_less_trans not_less_iff_gr_or_eq)
  apply (metis (no_types, hide_lams))
  apply metis
  apply (metis (no_types, hide_lams))  (*4*)
  apply(intro conjI impI)
  apply metis
  apply metis
  apply (metis (no_types, lifting))
  apply (metis (no_types, lifting) gr_implies_not_zero length_greater_0_conv not_add_less1)
  apply (metis (no_types, hide_lams))
  apply metis
  apply (metis (no_types, lifting) gr_implies_not0 length_greater_0_conv not_add_less1)
  apply metis
  apply metis
  apply (metis (no_types, lifting))
  apply (metis (no_types, lifting) F.distinct(7) add.commute le_less_trans not_less_iff_gr_or_eq)
  apply (metis (no_types, hide_lams))
  apply metis
  apply (metis (no_types, hide_lams))  (*3*)
  apply(case_tac "(\<forall>i<length (q s). fst (q s ! i) + snd (q s ! i) < T s) \<and>
          tempR s = (0, 0) \<or>
          (\<forall>i<length (q s). fst (q s ! i) + snd (q s ! i) < T s) \<and>
          0 < snd (tempR s) \<and> fst (tempR s) = 0 \<and> fst (tempR s) < T s", simp_all)
  apply(case_tac "tempR s \<noteq> (0, 0)", simp_all)
  apply(intro conjI impI)
  apply blast
                      apply blast
  apply blast
                      apply blast
  apply blast
                      apply blast
  apply blast
  apply metis
  apply metis
  apply (metis (no_types, hide_lams))
  apply (metis (no_types, lifting))
  apply (metis (no_types, hide_lams))
  apply(case_tac "pcW s", simp_all)
  apply(case_tac "tempR s \<noteq> (0, 0)", simp_all add:writer_lemmas)
  apply clarify
  apply (intro conjI impI)
  sledgehammer








lemma if_idleR_and_has_dequeued_eq_has_enqueued:
  assumes "con_assms s"
  and "inv (pcW s) (pcR s) s"
  and "cR_step (pcR s) s s'"
  and "has_dequeued s = has_enqueued s"
shows "(pcR s=idleR \<longrightarrow> pcR s'=idleR)\<and>(pcR s=Release\<longrightarrow>pcR s'=idleR)"
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
  apply(intro conjI)
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply clarify                   
  apply(cases " ownD s (data_index s (tempR s)) = B", simp_all)
  apply force 
  apply (case_tac "pcR s", simp_all)
  apply(case_tac "q s=[]", simp_all add:Let_def Q_structure_def Q_holds_dummy_b_def)
  apply (metis (no_types, lifting) hd_conv_nth length_greater_0_conv less_imp_le_nat less_le_trans)
  apply metis
(*10*)
  apply(intro conjI impI)
  apply(cases "pcR s", simp_all add:Q_holds_bytes_def)
  apply(case_tac "T s=fst(tempR s)", simp_all)
  apply (simp add: Q_has_dummy_bytes_def)
  apply (metis (no_types, lifting) F.distinct(7) add.commute le_less_trans not_less_iff_gr_or_eq)
  apply(cases "q s=[]", simp_all add:Let_def)
  (*19*)
  apply clarify
  apply(simp add:Q_has_no_overlaps_def)
  apply (smt One_nat_def Suc_diff_Suc Suc_mono add.commute hd_conv_nth le_less_trans length_greater_0_conv length_tl minus_nat.diff_0 not_le nth_tl zero_less_Suc)



  oops
                     
  
  apply metis
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply metis
  apply metis
  apply metis
  apply metis
  apply metis
  apply metis
  apply (metis (no_types, lifting) F.distinct(7) add.commute leD le_less_trans less_imp_le_nat)
  apply (metis (no_types, lifting) F.distinct(7) add.commute le_less_trans not_less_iff_gr_or_eq)
  apply (metis (no_types, lifting) F.distinct(7) add.commute leD le_less_trans less_imp_le_nat)
  apply clarify
  apply (case_tac "\<forall>i<length (q s). T s \<noteq> fst (q s ! i)", simp add:Q_lemmas)
  apply(case_tac "\<forall>i. i < length (q s) \<and> 0 < i \<longrightarrow>
             (fst (q s ! (i - Suc 0)) < fst (q s ! i))", simp)
  sledgehammer





  oops
  apply(case_tac "\<forall>i<length (q s). T s \<noteq> fst (q s ! i)", simp_all add:Q_lemmas)
                apply(case_tac "pcW s", simp_all)
  apply(simp_all add:writer_lemmas)
                      apply(case_tac "T s\<noteq>fst(tempR s)",simp_all)
  unfolding set_ownB_def
  sledgehammer


  oops





  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply (simp add: hd_conv_nth)+           
  apply force       
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply (simp add: nth_tl)       
  apply(cases "pcR s", simp_all add: cR_step_def)      
  apply force  
  apply(cases "q s=[]", simp_all add:Let_def)
  apply linarith                                                     
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply (metis F.distinct(6) le_eq_less_or_eq not_less_eq_eq)
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply (metis cancel_comm_monoid_add_class.diff_cancel le_antisym le_trans length_0_conv not_less_eq_eq)
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def) 
  apply (cases "pcR s", simp_all)
  apply (cases "0 < Data s (next_read s - Suc 0)", simp_all add: inv_simps)
  apply (cases "T s < fst (tempR s)", simp_all) sledgehammer
  apply linarith

      apply (cases " T s \<noteq> fst (tempR s)", simp_all)
       apply (cases "pcW s", simp_all)

  apply (cases "T s \<noteq> fst(tempR s)", simp_all)
  apply (simp add:writer_lemmas)
  sledgehammer


  oops
  apply(cases "q s=[]", simp_all add:Let_def)
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply(cases "0 < snd (hd (q s))", simp_all)
  apply (simp add: hd_conv_nth)
  apply (metis add_leD1 hd_conv_nth length_greater_0_conv)
  apply force
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply(cases "0 < snd (hd (q s))", simp_all)
  apply (simp add: nth_tl)
  apply (simp add: nth_tl)
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply (cases "T s < fst (tempR s)", simp_all)
  apply (metis F.distinct(9) Nat.diff_add_assoc2 One_nat_def Suc_eq_plus1 Suc_le_eq add.right_neutral add_diff_cancel_left' diff_Suc_1 diff_le_self leD length_0_conv length_greater_0_conv lessI less_one zero_less_diff)
  apply (metis F.distinct(9) Nat.diff_add_assoc2 One_nat_def Suc_eq_plus1 Suc_le_eq add.right_neutral add_diff_cancel_left' diff_Suc_1 diff_le_self leD length_0_conv length_greater_0_conv lessI less_one zero_less_diff)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply(cases "0 < snd (hd (q s))", simp_all)
  apply clarify
  sledgehammer



           apply(cases "q s=[]", simp_all add:Let_def)
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
  apply(cases "pcR s", simp_all add: cR_step_def)
  apply (cases "T s < fst (tempR s)", simp_all)
















              
              apply(cases "q s=[]", simp_all add:Let_def)
 apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)
apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)apply(cases "pcR s", simp_all add: cR_step_def)
  apply(cases "q s=[]", simp_all add:Let_def)

  apply linarith
         apply(case_tac "pcW s", simp_all)



                      apply(case_tac[!] "pcR s", simp_all add: cR_step_def)
  apply(case_tac[!] "q s = []", simp_all add: Let_def)
  apply(clarsimp)
  apply (intro conjI impI)
  sledgehammer



                      apply auto[1]
  apply auto[1]
  apply (metis One_nat_def Suc_eq_plus1 diff_diff_add)
  apply (metis One_nat_def Suc_eq_plus1 diff_diff_add)
  by((case_tac "pcW s", simp_all, linarith, linarith, force)|auto)+



lemma writer_Enqueue_to_idleW_count_equal:
  assumes "con_assms s"
  and "inv Enqueue idleR s"
  and "cW_step Enqueue s s'"
  and "has_enqueued s=has_dequeued s"
shows "has_enqueued s'>has_enqueued s \<and> pcW s'=idleW \<and> length(q s') =1 \<and> H s>0"  
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
  apply(case_tac[!] "pcW s=OOM \<and> tW s \<noteq> T s", simp_all)
  apply(case_tac[!] "pcR s", simp_all add:less_imp_le_nat B_acquire_def)
  apply(case_tac[1-8] "has_enqueued s<n", simp_all add:cW_step_def inv_def B_acquire_def)
  apply(case_tac "tW s=H s", simp_all ;case_tac "H s < tW s \<and> Data s (has_enqueued s) < tW s - H s", simp_all ;case_tac "tW s < H s", simp_all)
  apply(case_tac "tW s=H s", simp_all ;case_tac "H s < tW s", simp_all; case_tac "Data s (has_enqueued s) < tW s - H s", simp_all)
  apply(case_tac[1-2] "Data s (has_enqueued s) \<le> N - H s", simp_all,case_tac[1-2] "Data s (has_enqueued s) < tW s", simp_all)
  apply force
  apply force         
  apply(case_tac[1-2] "N < Data s (has_enqueued s)", simp_all)
  apply(case_tac[1-6] "has_enqueued s<n", simp_all add:cW_step_def inv_def B_acquire_def)
  apply(case_tac "tW s=H s", simp_all; case_tac "H s < tW s \<and> Data s (has_enqueued s) < tW s - H s", simp_all; case_tac "tW s < H s", simp_all)
  apply(case_tac "tW s=H s", simp_all; case_tac "H s < tW s", simp_all; case_tac "Data s (has_enqueued s) < tW s - H s", simp_all)
  apply(case_tac[1-2] "Data s (has_enqueued s) \<le> N - H s", simp_all,case_tac[1-2] "Data s (has_enqueued s) < tW s", simp_all)
  apply(case_tac[1-2] "N < Data s (has_enqueued s)", simp_all)
  apply(smt add.commute add_cancel_right_left diff_is_0_eq' fst_conv le_less_linear less_Suc0 less_SucE less_imp_le list.size(3) nth_append nth_append_length ordered_cancel_comm_monoid_diff_class.add_diff_inverse snd_conv)
  apply(smt add.commute add_cancel_right_left diff_is_0_eq' fst_conv le_less_linear less_Suc0 less_SucE less_imp_le list.size(3) nth_append nth_append_length ordered_cancel_comm_monoid_diff_class.add_diff_inverse snd_conv)
  apply(case_tac[1-2] "has_enqueued s<n", simp_all add:cW_step_def inv_def B_acquire_def)
  apply(case_tac "tW s = H s", simp_all;case_tac " H s < tW s \<and> Data s (has_enqueued s) < tW s - H s", simp_all; case_tac "tW s < H s", simp_all)
  apply(case_tac "N<Data s (has_enqueued s)", simp_all)
  apply(case_tac[1-2] "has_enqueued s<n", simp_all add:cW_step_def inv_def B_acquire_def)
  apply(case_tac "tW s = H s \<and> Data s (has_enqueued s) \<le> N", simp_all; case_tac "H s < tW s \<and> Data s (has_enqueued s) < tW s - H s", simp_all; case_tac "tW s < H s", simp_all)
  apply(case_tac "N < Data s (has_enqueued s)", simp_all add: Suc_diff_le Nat.le_diff_conv2 inv_def)
  apply(case_tac[1-4] "has_enqueued s<n", simp_all add:cW_step_def inv_def B_acquire_def)
  apply(case_tac "N < Data s (has_enqueued s)", simp_all; metis less_imp_le)
  apply(case_tac "N < Data s (has_enqueued s)", simp_all; metis less_imp_le )
  apply(case_tac[1-4] "has_enqueued s<n", simp_all add:cW_step_def inv_def B_acquire_def)
  apply force
by(case_tac "has_enqueued s<n", simp_all add:cW_step_def inv_def B_acquire_def)





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
  and "has_dequeued s<has_enqueued s"
  and "inv pcw pcr s"
  and "cW_step pcw s s'"
shows "inv (pcW s') (pcR s') s'"
  using assms
  apply(simp_all add: inv_def cW_step_def, intro conjI impI)
  apply(simp_all add: cW_step_def inv_def)
  apply(case_tac[!] "pcW s", simp_all, linarith)
  apply(case_tac[!] "pcR s", simp_all add:less_imp_le_nat B_acquire_def)
  apply(case_tac[1-2] "has_enqueued s<n", simp_all add:B_acquire_def)
  apply(case_tac[1-2] "tW s=T s", simp_all)
  apply(case_tac[1-2] "has_enqueued s<n", simp_all add:B_acquire_def)
  apply(case_tac[1-2] "tW s=T s", simp_all)
  apply(case_tac[1-2] "has_enqueued s<n", simp_all add:B_acquire_def)
  apply(case_tac[1-2] "tW s=T s", simp_all)
  apply(case_tac[1-2] "has_enqueued s<n", simp_all add:B_acquire_def)
  apply(case_tac[1-2] "tW s=T s", simp_all)
  apply(case_tac "tW s = H s", simp_all; case_tac "H s < tW s \<and> Data s (has_enqueued s) < tW s - H s", simp_all; case_tac "tW s < H s", simp_all)
  apply(case_tac "tW s=H s", simp_all ;case_tac "H s < tW s", simp_all; case_tac "Data s (has_enqueued s) < tW s - H s", simp_all)
  apply(case_tac[1-2] "Data s (has_enqueued s) \<le> N - H s", simp_all, case_tac[1-2] "Data s (has_enqueued s) < tW s", simp_all)
  apply(case_tac[!] "pcW s=OOM \<and> tW s \<noteq> T s", simp_all)
  apply auto[1]
  apply auto[1]
  apply(case_tac[1-2] "N < Data s (has_enqueued s)", simp_all)
  apply(case_tac[1-6] "has_enqueued s<n", simp_all add:B_acquire_def)
  apply(case_tac[1-2] "tW s = H s", simp_all, case_tac[1-2] "H s < tW s \<and> Data s (has_enqueued s) < tW s - H s", simp_all, case_tac[1-2] "tW s < H s", simp_all)
  apply(case_tac[1-2] "Data s (has_enqueued s) \<le> N - H s", simp_all, case_tac[1-2] "Data s (has_enqueued s) < tW s", simp_all)
  apply(case_tac[1-2] "N < Data s (has_enqueued s)", simp_all)
  apply(smt add.commute add_cancel_right_left diff_is_0_eq' fst_conv le_less_linear less_Suc0 less_SucE less_imp_le list.size(3) nth_append nth_append_length ordered_cancel_comm_monoid_diff_class.add_diff_inverse snd_conv)
  apply(smt add.commute add_cancel_right_left diff_is_0_eq' fst_conv le_less_linear less_Suc0 less_SucE less_imp_le list.size(3) nth_append nth_append_length ordered_cancel_comm_monoid_diff_class.add_diff_inverse snd_conv)
  apply(case_tac[1-6] "has_enqueued s<n", simp_all add:B_acquire_def)
  apply(linarith|case_tac "Data s (has_enqueued s) \<le> N - H s", simp_all)+
  apply(case_tac[1-2] "has_enqueued s<n", simp_all add:B_acquire_def)
  apply linarith+
  apply (case_tac "N < Data s (has_enqueued s)", simp_all, meson less_imp_le)+
by(case_tac[1-4] "has_enqueued s<n", simp_all add:B_acquire_def)

(*------------------------showing progress----------------------*)

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
  apply(case_tac "has_enqueued s < n", simp_all add:less_imp_le)
  apply(case_tac "tW s \<noteq> T s", simp_all)
  using Suc_leI apply blast
  by (meson less_imp_le_nat)


lemma when_W_moves_prog_less:
  assumes "con_assms s"
  and "inv (pcW s) (pcR s) s"
  and "cW_step (pcW s) s s'"
shows "lex_prog s s'"
proof - 
  from assms(1) have sp1: "has_enqueued s \<le> n \<and> has_dequeued s \<le> n"
    using con_assms_def by auto
  from assms show ?thesis
  apply (simp_all add:cW_step_def inv_def  progress_lemmas tries_left_def)
  apply(case_tac "pcW s", simp_all)
  apply(case_tac[!] "pcR s", simp_all)
  apply (simp_all add: diff_less_mono2)
  apply (case_tac[!] "tW s = T s", simp_all add:cW_step_def)
  apply(case_tac[1-6] "has_enqueued s < n", simp_all)
  using diff_less_mono2 by auto
qed

lemma W_counter_implies_notown:
  assumes "con_assms s"
  and "mainInv s"
shows "\<forall>i.(i<has_enqueued s)\<longrightarrow>ownD s i \<in> {R,B}"
  using assms
  apply (simp_all add:inv_def)
  by (meson le_less_linear)


lemma least_prog_W_implies:
  assumes "con_assms s"
  and "inv (pcW s) pcr s"
  and "cW_step (pcW s) s s'"
  and "inv (pcW s') pcr s'"
  and "lex_prog s s'"
shows "end_W_prog s'=True\<longrightarrow>end_W_prog s \<or> ((\<forall>i.(i<n)\<longrightarrow>ownD s' i\<noteq>W) \<and> (pcW s=idleW) \<and> has_enqueued s=n)"
  using assms W_counter_implies_notown
  apply (simp_all add: end_W_prog_def progress_lemmas tries_left_def cW_step_def inv_def)
  apply (case_tac "pcW s", simp_all)
  apply(case_tac "has_enqueued s < n", simp_all)
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

definition "state_pv s \<equiv> (2*n - has_enqueued s - has_dequeued s)"
definition "tries_left s \<equiv> N-tries s"

definition "lex_prog s s' \<equiv> s = s' \<or> 
(state_pv s' < state_pv s 
\<or> (state_pv s' = state_pv s \<and> tries_left s' < tries_left s)
\<or> (state_pv s' = state_pv s \<and> tries_left s' = tries_left s \<and> ltpcR (pcR s') (pcR s)) 
\<or> (state_pv s' = state_pv s \<and> tries_left s' = tries_left s \<and> ltpcW (pcW s') (pcW s)))"

lemmas progress_lemmas = ltpcW_def ltpcR_def state_pv_def lex_prog_def 

definition "end_W_prog s \<equiv> ((n-has_enqueued s)=0) \<and> tries_left s=N \<and> pcW s=FinishedW" 
definition "end_R_prog s \<equiv> end_W_prog s\<and> pcR s=idleR \<and> has_dequeued s=has_enqueued s"
definition "start_state_prog s\<equiv> state_pv s=2*n \<and> pcR s=idleR \<and> pcW s=idleW \<and> tries_left s=N"

(*
\<and> right_to_addresses s
               \<and> no_ownB s
               \<and> H_T_ownB s
               \<and> Buff_entries_transfer_has_dequeued s*)*)