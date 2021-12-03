theory TS_Model
imports Lib_GeneralProofRules StackSemantics TransClosure
begin

section \<open>State Definition\<close>

type_synonym address = nat

datatype PC =
  L1
| L2
| L3
| L4
| L5
| L6

consts Top :: L

record prog_state =
  pc :: "T \<Rightarrow> PC"
  n_val :: "T \<Rightarrow> address"
  n_nxt :: "T \<Rightarrow> address"
  top :: "T \<Rightarrow> address"
  ntop :: "T \<Rightarrow> address"
  res :: "T \<Rightarrow> bool"
  addr :: "address set" (*auxilary*)
  pushed_addr :: "address set" (*auxilary*)
  addr_val :: "address set" (*auxilary*)

definition "Null \<equiv> 0"

definition 
  "update_next_func a nv addf \<equiv> addf (a := nv)"

definition 
  "update_addr v nx s \<equiv> s\<lparr>addr := (addr s) \<union> {v, nx}, addr_val := (addr_val s) \<union> {v}\<rparr>"

definition 
  "update_pushed_addr a s \<equiv> s\<lparr>pushed_addr := (pushed_addr s) \<union> {a}\<rparr>"

definition 
  "update_ntop t a s \<equiv> s\<lparr>ntop := (ntop s)(t := a)\<rparr>"

definition 
  "update_pc2 t npc s \<equiv> s\<lparr>pc := (pc s)(t := npc)\<rparr>"

definition 
  "update_pc t nv pcf \<equiv> pcf (t := nv)"

definition
  "new_node v nx s \<equiv>  v \<notin> addr s \<union> {Null, Top} \<and> nx \<notin> (addr s) \<union> {Null, Top} \<and> nx = v + 1"

abbreviation new_abbr:: "prog_state \<Rightarrow> address \<Rightarrow> address \<Rightarrow> prog_state \<Rightarrow> bool" ("_ [_ _ := NEW] _" [100,100,100])
  where "s [v nx := NEW] s' \<equiv> new_node v nx s \<and> s' = s ;; update_addr v nx "

definition "same_except_for_pc s s' \<equiv> n_val s' = n_val s \<and> n_nxt s' = n_nxt s \<and> top s' = top s \<and> res s' = res s
                                  \<and> addr s' = addr s  \<and> ntop s' = ntop s \<and> pushed_addr s' = pushed_addr s \<and> addr_val s' = addr_val s"

definition "same_except_for_pc_and_top s s' \<equiv> n_val s' = n_val s \<and> n_nxt s' = n_nxt s \<and>  res s' = res s
                                  \<and> addr s' = addr s  \<and> ntop s' = ntop s \<and> pushed_addr s' = pushed_addr s
                                  \<and> addr_val s' = addr_val s"

definition "prog_state_wfs ps \<equiv> (finite (addr ps)) \<and> (0\<notin>addr ps)"

definition "addr_init t ps cls \<equiv> \<forall> a b . new_node a b ps \<longrightarrow> ([lib(a) =\<^sub>t 0] cls) \<and> [lib(b) =\<^sub>t 0] cls"

definition "written_vals cls x = lib_value cls `(lib_writes_on cls x)"

definition "addr_init_writes ps cls \<equiv> \<forall> a b . new_node a b ps  \<longrightarrow> written_vals cls a = {0} \<and>  written_vals cls b = {0}"

section \<open>Operations Model\<close>

definition lib_push :: "T \<Rightarrow> V \<Rightarrow>  prog_state \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> prog_state \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool " where
"lib_push t v ps cls ccs ps' cls' ccs' \<equiv> 
(
if (pc ps) t = L1
then
    (ps [(n_val ps' t) (n_nxt ps' t) := NEW] ps') \<and> cls' = cls \<and> ccs' = ccs \<and>
    (\<forall> t'. t' \<noteq> t \<longrightarrow> n_val ps' t' = n_val ps t' \<and> n_nxt ps' t = n_nxt ps t) \<and> \<comment> \<open> Added \<close>
    (pc ps' = update_pc t L2 (pc ps))     
else
if (pc ps) t = L2
then 
    (cls ccs [lib(n_val ps t) := v]\<^sub>t cls' ccs')  \<and>
    (pc ps' = update_pc t L3 (pc ps))  \<and> (same_except_for_pc ps ps')   
else
if (pc ps) t = L3
then 
    (cls ccs [(top ps' t) \<leftarrow>\<^sup>A lib(Top)]\<^sub>t cls' ccs')  \<and>
    (\<forall> t'. t' \<noteq> t \<longrightarrow> top ps' t' = top ps t') \<and> \<comment> \<open> Added \<close>
    (pc ps' = update_pc t L4 (pc ps)) \<and> (same_except_for_pc_and_top ps ps')     
else
if (pc ps) t = L4
then 
    (cls ccs [lib(n_nxt ps' t) := (top ps t)]\<^sub>t cls' ccs')  \<and>
    (pc ps' = update_pc t L5 (pc ps))    
    \<and> (same_except_for_pc ps ps') 
else
if (pc ps) t = L5
then 
    (cls ccs CAS\<^sup>R[lib(Top), (res ps' t), (top ps t), (n_val ps t)]\<^sub>t cls' ccs') \<and>      
    (res ps' t \<longrightarrow> (pc ps' = update_pc t L6 (pc ps)) \<and> pushed_addr ps' = pushed_addr ps \<union> {n_val ps t}) \<and>
    (\<not>(res ps' t) \<longrightarrow> (pc ps' = update_pc t L3 (pc ps)) \<and> pushed_addr ps' = pushed_addr ps) \<and>
    (n_val ps' = n_val ps \<and> n_nxt ps' = n_nxt ps \<and> top ps' = top ps \<and> addr ps' = addr ps \<and> ntop ps' = ntop ps \<and> addr_val ps' = addr_val ps)
else
False
)"


definition lib_pop :: "T \<Rightarrow> L \<Rightarrow>  prog_state \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> prog_state \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool " where
"lib_pop t l ps cls ccs ps' cls' ccs' \<equiv> 
(
if (pc ps) t = L1
then
    (cls ccs [(top ps' t) \<leftarrow>\<^sup>A lib(Top)]\<^sub>t cls' ccs')  \<and>
    (\<forall> t'. t' \<noteq> t \<longrightarrow> top ps' t' = top ps t') \<and> \<comment> \<open>Added \<close>
    (top ps' t = Null \<longrightarrow> pc ps' = update_pc t L1 (pc ps)) \<and>
    (top ps' t \<noteq> Null \<longrightarrow> pc ps' = update_pc t L2 (pc ps)) \<and>
     same_except_for_pc_and_top ps ps'
else
if (pc ps) t = L2
then 
    (cls ccs [(ntop ps' t) \<leftarrow> lib(top ps t + 1)]\<^sub>t cls' ccs')  \<and>
    (\<forall> t'. t' \<noteq> t \<longrightarrow> ntop ps' t' = ntop ps t') \<and>  \<comment> \<open>NEED TO GUARANTEE THIS\<close>
    (pc ps' = update_pc t L3 (pc ps)) \<and>
    (n_val ps' = n_val ps \<and> n_nxt ps' = n_nxt ps \<and> top ps' = top ps \<and> addr ps' = addr ps \<and> pushed_addr ps' = pushed_addr ps \<and> addr_val ps' = addr_val ps)
else
if (pc ps) t = L3
then 
    (cls ccs CAS\<^sup>R[lib(Top), (res ps' t), (top ps t), (ntop ps t)]\<^sub>t cls' ccs') \<and>
    (res ps' t \<longrightarrow> (pc ps' = update_pc t L4 (pc ps)) \<and> pushed_addr ps' = pushed_addr ps - {top ps t}) \<and>
    (\<not>(res ps' t) \<longrightarrow> (pc ps' = update_pc t L1 (pc ps)) \<and> pushed_addr ps' = pushed_addr ps) \<and>
    (n_val ps' = n_val ps \<and> n_nxt ps' = n_nxt ps \<and> top ps' = top ps \<and> addr ps' = addr ps \<and> ntop ps' = ntop ps \<and> addr_val ps' = addr_val ps) \<and>
    l = top ps t
else
False
)"

section \<open>General definitions\<close>

definition "written_addr cls \<equiv> (lib_value cls)`(lib_writes_on cls Top) - {Null}"

lemma "w\<in>lib_writes_on cls Top \<Longrightarrow> lib_value cls w \<noteq> Null \<Longrightarrow> lib_value cls w \<in> written_addr cls"
  by (simp add: written_addr_def Null_def)

definition "lastL cls a \<equiv> (lib_lastWr cls a)"

definition "lastVal cls a \<equiv> lib_value cls (lib_lastWr cls a)"

definition "lastNxtVal cls a \<equiv> lastVal cls (a + 1)"

definition "TopL cls \<equiv> (lib_lastWr cls Top)"

definition "lastTop cls \<equiv> lib_value cls (lib_lastWr cls Top)"

definition "nxt_rel ps cls \<equiv> {(a,b)| a b . a\<in>pushed_addr ps \<and> b = lastVal cls (a +1) }"

definition "clss ts cls \<equiv> (nxt_rel ts cls)\<^sup>+"

definition "agt a b ps cls \<equiv> (a,b) \<in> clss ps cls"

section \<open>Global Invariant\<close>

definition "to_p1 ps cls \<equiv> \<forall> a b . a\<in>pushed_addr ps \<and> b\<in>pushed_addr ps \<and> a\<noteq>b \<longrightarrow> agt a b ps cls \<or> agt b a ps cls"

definition "to_p2 ps cls \<equiv> \<forall> a . a\<in>pushed_addr ps \<and> lastTop cls \<noteq> a \<longrightarrow> agt (lastTop cls) a ps cls"

definition "to_p3 ps cls \<equiv> \<forall> a . a\<in>pushed_addr ps  \<longrightarrow> agt a Null ps cls"

definition "to_p4 ps cls \<equiv> \<forall> a . a\<in>pushed_addr ps  \<longrightarrow> (a,a)\<notin>clss ps cls"

definition "to ps cls \<equiv> to_p1 ps cls \<and> to_p2 ps cls \<and> to_p3 ps cls \<and> to_p4 ps cls"

definition "writen_Tops cls \<equiv> {l . \<forall> w.  w\<in>lib_writes_on cls Top \<and> l = lib_value cls w} - {Null}"

definition "glb_inv1 ps cls \<equiv> \<forall> w . w\<in>lib_writes_on cls Top \<and> lib_value cls w \<noteq> Null \<longrightarrow> lib_value cls w \<in> addr ps"

definition "glb_inv2 ps cls \<equiv> lastTop cls \<noteq> Null \<longrightarrow> lib_releasing cls (lib_lastWr cls Top)"

definition "glb_inv3 ps cls \<equiv> lastTop cls \<noteq> Null \<longrightarrow> lastTop cls \<in> pushed_addr ps"

definition "glb_inv4 ps cls \<equiv> \<forall> a . a\<in>addr_val ps \<longrightarrow> lastVal cls (a +1) \<noteq> a \<and> (a + 1) \<in> addr ps \<and> (a + 1) \<notin> addr_val ps "

definition "glb_inv5 ps cls \<equiv> pushed_addr ps \<subseteq> addr ps \<and> addr_val ps \<subseteq> addr ps"

definition "glb_inv6 ps cls \<equiv> \<forall> a1 a2 . a1\<in>pushed_addr ps  \<and>  a2\<in>pushed_addr ps \<and> a1\<noteq>a2 \<longrightarrow> lastVal cls (a1 + 1) \<noteq> lastVal cls (a2 + 1)"

definition "glb_inv7 ps cls \<equiv> \<forall> w . w\<in>lib_writes_on cls Top \<and> lib_value cls w \<noteq> Null \<longrightarrow> lib_releasing cls w"

definition "glb_inv8 ps cls \<equiv> \<forall> ad . ad\<in>pushed_addr ps \<and> lastVal cls (ad + 1) \<noteq> Null \<longrightarrow> (lastVal cls (ad + 1)) \<in> pushed_addr ps"

definition "glb_inv9 ps  \<equiv> \<forall> t .  ntop ps t \<noteq> Null \<longrightarrow> ntop ps t\<in>addr ps"

definition "glb_inv10 ps cls  \<equiv> \<forall> ad . ad\<in>pushed_addr ps \<longrightarrow> lastVal cls (ad + 1) \<noteq> lastTop cls "

definition "glb_inv12 ps cls \<equiv>  finite (pushed_addr ps)"

definition "glb_inv11 ps cls \<equiv> \<forall> ad . ad\<in>pushed_addr ps \<longrightarrow> (ad + 1)\<notin>pushed_addr ps \<and> (ad + 1)\<in>addr ps \<and> (ad + 1) \<notin> addr_val ps"

definition "glb_inv13 ps cls \<equiv> \<forall> ad . ad \<in> written_addr cls \<longrightarrow> lastNxtVal cls ad \<in> addr_val ps \<union> {Null} \<and> ad\<in>addr_val ps "

definition "glb_inv14 ps cls \<equiv> \<forall> ad . ad \<in> written_addr cls \<and> lastNxtVal cls ad \<noteq> Null \<longrightarrow> lastNxtVal cls ad \<in> written_addr cls"

definition "glb_inv15 ps \<equiv> \<forall> t t' . t \<noteq> t' \<longrightarrow> n_val ps t \<noteq> n_val ps t' \<and> n_nxt ps t \<noteq> n_nxt ps t' \<and> n_val ps t \<noteq> n_nxt ps t'"

definition "glb_inv16 ps cls \<equiv> \<forall> ad . ad \<in> written_addr cls \<and> ad \<noteq> Null  \<longrightarrow> lib_value cls `(lib_writes_on cls (Suc(ad)))\<subseteq>{Null} \<union> addr_val ps"


definition "glb ps cls \<equiv> Top \<notin> addr ps \<and> Null \<notin> addr ps "

definition "glb_inv ps cls \<equiv>  glb_inv1 ps cls  \<and> glb_inv3 ps cls
            \<and> glb_inv4 ps cls \<and> glb_inv5 ps cls \<and> glb_inv6 ps cls \<and> glb_inv7 ps cls \<and> glb_inv8 ps cls
\<and> glb_inv9 ps \<and> glb_inv10 ps cls  \<and> glb_inv12 ps cls \<and> glb_inv11 ps cls \<and> glb_inv13 ps cls \<and> glb_inv14 ps cls
 \<and> glb_inv15 ps \<and> glb_inv16 ps cls"

definition "cobs_to t ps cls ccs \<equiv>  \<forall> ad1 ad2 . ad1 \<in> pushed_addr ps \<and> ad2 \<in> pushed_addr ps \<and>
                (agt ad1 ad2 ps cls \<or> ad1=ad2) \<longrightarrow> (\<exists> vl . ([lib(Top) = ad1]\<lparr>lib(ad2) =\<^sub>t vl\<rparr> cls)) \<and> (\<exists> vl . ([lib(Top) = ad1]\<lparr>lib(Suc(ad2)) =\<^sub>t vl\<rparr> cls))"

definition "dobs_to t ps cls ccs \<equiv>  \<forall> ad . ad \<in> pushed_addr ps \<and> top ps t \<noteq> Null \<and>
                (agt (top ps t) ad ps cls  \<or> ad = top ps t) \<longrightarrow> (\<exists> vl . ([lib(ad) =\<^sub>t vl] cls)) \<and> (\<exists> vl . ([lib(Suc(ad)) =\<^sub>t vl] cls))"


section \<open>Push Invariant\<close>

definition "c_obs_Top t ps cls ccs\<equiv> \<forall> ad . ad \<in> written_addr cls \<longrightarrow> (\<exists> vl . ([lib(Top) = ad]\<lparr>lib(ad) =\<^sub>t vl\<rparr> cls))"

definition "no_Top_n_a ps cls  \<equiv> 
  \<forall> v nx w . new_node v nx ps \<and> w\<in>lib_writes_on cls Top \<longrightarrow> lib_value cls w \<noteq> v \<and> lib_value cls w \<noteq> nx"

definition "no_Top_n t ps cls  \<equiv> 
  \<forall> w .  w\<in>lib_writes_on cls Top \<longrightarrow> lib_value cls w \<noteq> n_val ps t \<and> lib_value cls w \<noteq> n_nxt ps t"

definition "push_inv t v p cls ccs  ps \<equiv> 
    (case p of
          L1 \<Rightarrow> (glb ps cls) \<and> (addr_init t ps cls) \<and> (\<exists> v' . cvd[lib(Top), v'] cls)
                 \<and> (no_Top_n_a  ps cls) \<and> (top ps t = Null) 
                 \<and> cobs_to t ps cls ccs \<and> (addr_init_writes ps cls)
               \<comment> \<open>L1: ps [(n_val ps' t) (n_nxt ps' t) := NEW] ps' \<close>
        | L2 \<Rightarrow> (glb ps cls) \<and> ([lib(n_val ps t) =\<^sub>t 0] cls) \<and> ([lib(n_nxt ps t) =\<^sub>t 0] cls)
                 \<and> (n_val ps t\<in> addr ps)  \<and> (n_val ps t\<in> addr_val ps) \<and> (n_nxt ps t\<in> addr ps)
                 \<and> (n_nxt ps t =  n_val ps t + 1) \<and> (\<exists> v' . cvd[lib(Top), v'] cls)
                 \<and> (n_val ps t \<notin> pushed_addr ps)  \<and> (n_nxt ps t \<notin> pushed_addr ps)
                 \<and> (no_Top_n t ps cls) \<and> (top ps t = Null) \<and> (n_val ps t \<notin> written_addr cls)
                 \<and> cobs_to t ps cls ccs \<and> written_vals cls (n_nxt ps t) = {0}
               \<comment> \<open>L2: (cls ccs [lib(n_val ps t) := v]t cls' ccs') \<close>
        | L3 \<Rightarrow> (glb ps cls) \<and> ([lib(n_val ps t) =\<^sub>t v] cls) \<and> (\<exists> v'. [lib(n_nxt ps t) =\<^sub>t v'] cls)
                 \<and> (n_val ps t\<in> addr ps) \<and> (n_val ps t\<in> addr_val ps) \<and> (n_nxt ps t\<in> addr ps)
                 \<and> (n_nxt ps t =  n_val ps t + 1) \<and> (\<exists> v' . cvd[lib(Top), v'] cls) \<and> (n_val ps t \<notin> pushed_addr ps)
                 \<and> (n_nxt ps t \<notin> pushed_addr ps) \<and> (no_Top_n t ps cls)
                 \<and> cobs_to t ps cls ccs \<and> (n_val ps t \<notin> written_addr cls) 
                 \<and> (\<forall> u . u \<in> written_vals cls (n_nxt ps t) \<longrightarrow> u = 0 \<or> u\<in>addr_val ps) 
               \<comment> \<open>L3: cls ccs [(top ps' t) \<leftarrow>A lib(Top)]t cls' ccs' \<close>
        | L4 \<Rightarrow> (glb ps cls) \<and> ([lib(n_val ps t) =\<^sub>t v] cls) \<and> (\<exists> v'. [lib(n_nxt ps t) =\<^sub>t v'] cls)
                 \<and> (n_val ps t\<in> addr ps) \<and> (n_val ps t\<in> addr_val ps) \<and> (n_nxt ps t\<in> addr ps)
                 \<and> (n_nxt ps t =  n_val ps t + 1) \<and> (\<exists> v' . cvd[lib(Top), v'] cls)
                 \<and> (n_val ps t \<notin> pushed_addr ps) \<and> (n_nxt ps t \<notin> pushed_addr ps) 
                 \<and> (no_Top_n t ps cls) \<and> (top ps t \<noteq> Null \<longrightarrow> top ps t \<in> written_addr cls)
                 \<and> cobs_to t ps cls ccs \<and> dobs_to t ps cls ccs \<and> (n_val ps t \<notin> written_addr cls)
                 \<and> (\<forall> u . u \<in> written_vals cls (n_nxt ps t) \<longrightarrow> u = 0 \<or> u\<in>addr_val ps) 
              \<comment> \<open>L4: cls ccs [lib(n_nxt ps' t) := (top ps t)]t cls' ccs' \<close>
        | L5 \<Rightarrow> (glb ps cls) \<and> ([lib(n_val ps t) =\<^sub>t v] cls) \<and> ([lib(n_nxt ps t) =\<^sub>t (top ps t)] cls)
                \<and> (n_val ps t\<in> addr ps) \<and> (n_val ps t\<in> addr_val ps) \<and> (n_nxt ps t\<in> addr ps)
                \<and> (n_nxt ps t =  n_val ps t + 1) \<and> (\<exists> v' . cvd[lib(Top), v'] cls)
                \<and> (lastNxtVal cls (n_val ps t) = top ps t) \<and> (n_val ps t \<notin> pushed_addr ps)
                \<and> (n_nxt ps t \<notin> pushed_addr ps) \<and> (no_Top_n t ps cls)
                \<and> cobs_to t ps cls ccs \<and> dobs_to t ps cls ccs \<and> (n_val ps t \<notin> written_addr cls)
                \<and> (top ps t \<noteq> Null \<longrightarrow> top ps t \<in> written_addr cls)
                \<and> (\<forall> u . u \<in> written_vals cls (n_nxt ps t) \<longrightarrow> u = 0 \<or> u\<in>addr_val ps) 
             \<comment> \<open>L5: cls ccs CASR[lib(Top), (res ps' t), (top ps t), (n_val ps t)]t cls' ccs' \<close>
        | L6 \<Rightarrow> (glb ps cls) \<and> ([lib(n_val ps t) =\<^sub>t v] cls) \<and> ([lib(n_nxt ps t) =\<^sub>t (top ps t)] cls)
                \<and> (n_val ps t\<in> addr ps) \<and> (n_val ps t\<in> addr_val ps) \<and> (n_nxt ps t\<in> addr ps)
                \<and> (n_nxt ps t =  n_val ps t + 1) \<and> (\<exists> v' . cvd[lib(Top), v'] cls)
                \<and> (n_nxt ps t \<notin> pushed_addr ps)
                \<and> cobs_to t ps cls ccs

    )"

section \<open>Pop Invariant\<close>

definition "c_obs_TopNxt t ps cls ccs\<equiv> \<forall> ad . ad \<in> written_addr cls \<longrightarrow> (\<exists> vl . ([lib(Top) = ad]\<lparr>lib(ad + 1) =\<^sub>t vl\<rparr> cls))"

definition "c_obs_Top_forall t ps cls ccs\<equiv> \<forall> ad ad1. ad \<in> written_addr cls \<and> ad1\<in>written_addr cls 
                                 \<and> agt ad ad1 ps cls \<longrightarrow> (\<exists> vl . ([lib(Top) = ad]\<lparr>lib(ad1) =\<^sub>t vl\<rparr> cls))"


definition "addr_nxt ps \<equiv> {v' | v v'.  v' = v +  1 \<and> v \<in> pushed_addr ps}"


definition "c_obs_addr_nxt t ps cls ccs\<equiv> 
                \<forall> ad . ad \<in> addr_nxt ps \<longrightarrow> (\<exists> v . ([lib(ad) =\<^sub>t v] cls))"



definition "pop_inv t l p cls ccs  ps \<equiv>
    (case p of
          L1 \<Rightarrow> (glb ps cls) \<and> (cobs_to t ps cls ccs)
              \<and> (\<exists> v . cvd[lib(Top), v] cls) \<and> (top ps t \<noteq> Null \<longrightarrow> top ps t \<in> written_addr cls)
         \<comment> \<open>L1: DO DO top \<leftarrow>A Top UNTIL top \<noteq> Null \<close>
        | L2 \<Rightarrow> (glb ps cls) \<and> (cobs_to t ps cls ccs) \<and> (dobs_to t ps cls ccs) \<and> top ps t \<noteq> Null
              \<and> (\<exists> v . cvd[lib(Top), v] cls) \<and> (\<exists> v . top ps t \<in> pushed_addr ps \<longrightarrow> [lib (top ps t) =\<^sub>t v] cls)
              \<and> (\<exists> v .  top ps t \<in> pushed_addr ps \<longrightarrow> ([lib (top ps t + 1) =\<^sub>t v] cls) \<and> v \<in> addr_val ps \<union> {Null}) \<and> (top ps t \<in> written_addr cls)
         \<comment> \<open>L2: ntop \<leftarrow> nxt.top \<close>
        | L3 \<Rightarrow> (glb ps cls) \<and> (cobs_to t ps cls ccs) \<and> (dobs_to t ps cls ccs) \<and> top ps t \<noteq> Null \<and> (ntop ps t \<in> addr_val ps \<union> {Null}) \<and>
                (\<exists> v . cvd[lib(Top), v] cls) \<and> (\<exists> v . top ps t \<in> pushed_addr ps \<longrightarrow> [lib (top ps t) =\<^sub>t v] cls) \<and>
                (top ps t \<in> pushed_addr ps \<longrightarrow> lastNxtVal cls (top ps t) = ntop ps t) \<and> (top ps t \<in> written_addr cls) \<and> (\<exists> v .  top ps t \<in> pushed_addr ps \<longrightarrow> ([lib (top ps t + 1) =\<^sub>t v] cls))
         \<comment> \<open>L3: CAS[Top, res, top, ntop] \<close>
        | L4 \<Rightarrow> (glb ps cls) \<and> top ps t \<noteq> Null \<and> (\<exists> v . cvd[lib(Top), v] cls) \<and>
                (\<exists> v . [lib (top ps t) =\<^sub>t v] cls)  \<and> (top ps t \<in> written_addr cls) 
    )"


lemma "lib_wfs cls ccs \<Longrightarrow>w\<in>lib_writes_on cls x \<Longrightarrow> lib_thrView cls t x = w \<Longrightarrow> lib_value cls w = l \<Longrightarrow> [lib(x) = l]\<lparr>lib(y) =\<^sub>t v\<rparr> cls \<Longrightarrow> 
 [lib(y) =\<^sub>t n] cls \<Longrightarrow> v = n"
  apply(simp add: lib_c_obs_lib_only_def lib_d_obs_t_def lib_d_obs_def lib_visible_writes_def)
  oops

section \<open>General Lemmas\<close>

lemma "new_node v nx s \<Longrightarrow> v \<noteq> Top \<and> v \<noteq> Null \<and> nx \<noteq> Top \<and> nx \<noteq> Null \<and> nx = v + 1"
  apply(simp add: new_node_def)
  done

lemma "s [v nx:= NEW] s' \<Longrightarrow> pc s' = pc s"
   apply(simp add:  update_addr_def)
  done

lemma new_address: "s [v nx := NEW] s' \<Longrightarrow> addr s' = addr s \<union> {v, nx} \<and> nx = v + 1"
  apply(simp add: new_node_def update_addr_def)
  done

lemma "s [v nx := NEW] s' \<Longrightarrow> pc s' = update_pc t nv (pc s)  \<Longrightarrow> res s' = res s \<and> pc s' t = nv"
  apply(simp add:  update_addr_def update_pc_def)  
  by (metis fun_upd_def)

lemma "pc s' = update_pc t L3 (pc s) \<Longrightarrow> s [a nx := NEW] s' \<Longrightarrow> 
            pc s' t = L3 \<and> addr s' = addr s \<union> {a, nx} \<and> res s' = res s"
  apply(simp add: update_pc_def update_addr_def)
  by (metis fun_upd_def)

lemma nn_l1: "ps [a b := NEW] ps'
              \<Longrightarrow> a\<notin>addr ps \<and> b\<notin>addr ps"
  apply simp
  apply(intro conjI)
  apply (simp add: new_node_def)
  by (meson UnI1 new_node_def)

lemma nn_l2: "ps [a b := NEW] ps'
              \<Longrightarrow> a\<in>addr ps' \<and> b\<in>addr ps'"
  apply simp
  apply(intro conjI) 
  using new_address apply fastforce
  using new_address by fastforce

lemma nn_l3: "addr_val ps \<subseteq> addr ps \<Longrightarrow> ps [a b := NEW] ps' 
              \<Longrightarrow> a\<in>addr_val ps' \<and> b\<notin>addr_val ps'"
  apply simp
  apply(intro conjI) 
   apply (simp add: update_addr_def)
   apply (simp add: update_addr_def)
    using new_node_def by auto


lemma nn_l4: " ps [a b := NEW] ps' 
              \<Longrightarrow> a\<noteq>Top \<and> b\<noteq>Top"
  apply simp
   apply (simp add: update_addr_def)
   by (simp add: new_node_def)

lemma nn_l5: " ps [a b := NEW] ps' 
              \<Longrightarrow> b = a + 1"
  apply simp
   apply (simp add: update_addr_def)
   by (simp add: new_node_def)


lemma nn_l6: " ps [a b := NEW] ps' \<Longrightarrow> c \<notin> addr_val ps \<Longrightarrow> c\<in>addr_val ps'
              \<Longrightarrow> a = c"
  apply simp
   apply (simp add: update_addr_def)
  done

lemma lib_push_L1_pushed: "pc ps t = L1 \<Longrightarrow> lib_push t v ps cls ccs ps' cls' ccs' \<Longrightarrow>pushed_addr ps' = pushed_addr ps"
  apply(simp add: lib_push_def)
  by (metis prog_state.ext_inject prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9) update_addr_def)


lemma lib_push_L1_addr_val2: "pc ps t = L1 \<Longrightarrow> lib_push t v ps cls ccs ps' cls' ccs' \<Longrightarrow>addr_val ps' = addr_val ps \<union> {n_val ps' t}"
  apply(simp add: lib_push_def)
  using prog_state.ext_inject prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9) update_addr_def
  by (metis Un_empty_right Un_insert_right)


lemma lib_push_L1_new_address_not_null: "pc ps t = L1 \<Longrightarrow> lib_push t v ps cls ccs ps' cls' ccs' \<Longrightarrow> a\<notin>addr ps \<Longrightarrow> a\<in>addr ps' \<Longrightarrow> a \<noteq> Null \<and> a \<noteq> Top"
  apply(simp add: lib_push_def update_addr_def new_node_def)
  by(metis (no_types, lifting) insert_iff prog_state.select_convs(7) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))

lemma lib_push_L1_new_address_nxt_not_null: "pc ps t = L1 \<Longrightarrow> lib_push t v ps cls ccs ps' cls' ccs' \<Longrightarrow> a\<notin>addr_val ps \<Longrightarrow> a\<in>addr_val ps' \<Longrightarrow> a \<noteq> Null \<and> a \<noteq> Top"
  apply(simp add: lib_push_def update_addr_def new_node_def)
  by (metis insertE prog_state.ext_inject prog_state.surjective prog_state.update_convs(9))

lemma lib_push_L1_addr_sub: "pc ps t = L1 \<Longrightarrow> lib_push t v ps cls ccs ps' cls' ccs' \<Longrightarrow>addr ps \<subseteq> addr ps'"
  apply(simp add: lib_push_def)
  using new_address by fastforce


lemma lib_push_L1_pc: "pc ps t' = L1 \<Longrightarrow> lib_push t' v ps cls ccs ps' cls' ccs' \<Longrightarrow> t\<noteq>t' \<Longrightarrow> top ps' t = top ps t"
  apply(simp add: lib_push_def update_addr_def new_node_def)
  by (metis (no_types, lifting) prog_state.select_convs(4) prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))

lemma lib_push_L1_addr_val: "pc ps t' = L1 \<Longrightarrow> lib_push t' v ps cls ccs ps' cls' ccs' \<Longrightarrow> t\<noteq>t' \<Longrightarrow>  addr_val ps\<subseteq>addr_val ps'"
  apply(simp add: lib_push_def update_addr_def new_node_def)
  by (metis prog_state.select_convs(9) prog_state.surjective prog_state.update_convs(9) subset_insertI)


lemma lib_push_L1_ntop: "pc ps t = L1  \<Longrightarrow> lib_push t v ps cls ccs ps' cls' ccs' \<Longrightarrow>ntop ps' = ntop ps"
  apply(simp add: lib_push_def update_addr_def) 
  by (metis (no_types, lifting) prog_state.ext_inject prog_state.surjective prog_state.update_convs(7) prog_state.update_convs(9))

lemma "lib_pop t l ps cls ccs ps' cls' ccs' \<Longrightarrow> pc ps t = L1 \<Longrightarrow> pushed_addr ps = pushed_addr ps'"
  apply(simp add: lib_pop_def update_ntop_def update_pc_def)
  using same_except_for_pc_and_top_def by auto

lemma lib_pop_pushed_same_L2: "lib_pop t l ps cls ccs ps' cls' ccs' \<Longrightarrow> pc ps t = L2 \<Longrightarrow> pushed_addr ps = pushed_addr ps'"
  apply(simp add: lib_pop_def update_ntop_def update_pc_def)
  done

lemma no_Top_n_implies_no_p_obs: "no_Top_n t ps cls \<Longrightarrow> \<not>[lib(Top) \<approx>\<^sub>t' (n_val ps t)] cls \<and>  \<not>[lib(Top) \<approx>\<^sub>t' (n_nxt ps t)] cls"
  apply(simp add: no_Top_n_def lib_p_obs_def lib_visible_writes_def)
  by force



lemmas [simp] = glb_def Null_def update_pc_def addr_init_def update_addr_def  lastNxtVal_def lastVal_def lib_push_def same_except_for_pc_and_top_def same_except_for_pc_def   update_ntop_def
lemmas globals = glb_inv_def glb_inv1_def glb_inv2_def glb_inv3_def glb_inv4_def  glb_inv5_def  glb_inv6_def glb_inv7_def  glb_inv8_def glb_inv9_def
 glb_inv12_def glb_inv11_def to_def to_p1_def glb_inv10_def lastTop_def glb_inv13_def  glb_inv14_def glb_inv15_def


end