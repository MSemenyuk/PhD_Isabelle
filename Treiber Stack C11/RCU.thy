theory RCU
imports Main PSem
begin 
(*do a search on CHECK*)

datatype PC = I1 | I2 | I3 | I4 | I5 | I6 | I7 | I8 | I9 | I10 | I11 | I12 | I13 | I14 | I15 
            | R1 | R2 | R3 | R4 | R5 | R6 | R7  
            | S1 | S2 | S3 | S4 | S5 | S6 | S7 | S8 | S9 

(**)
consts rcu_0 ::address (*first location of rcu array*)
consts F::nat
consts T_max::nat (*max_thread ID*)
consts C :: nat     (*just referred to by its location in A(1) = (C,pointer) where C = nat*)
definition "set_T \<equiv> {n . n\<ge>1 \<and> n<T_max}"
definition "rcu_addrs \<equiv> {n . n\<ge>rcu_0 \<and> n < rcu_0+T_max-1}"
definition "something  \<equiv> F \<notin> rcu_addrs"




(*Recorded variables partial function*)
record mstate =
  pc :: "T \<Rightarrow> PC"
  r :: "T \<Rightarrow> nat \<Rightarrow> nat"        (*local copy of rcu*)
  v :: "T \<Rightarrow> V"
  n :: "T \<Rightarrow> id option"
  n_val :: "T \<Rightarrow> nat option"
  s :: "T \<Rightarrow> id option"
  s_val :: "T \<Rightarrow> nat option"
  C_val :: "T \<Rightarrow> nat option"
  (*old :: "T \<Rightarrow> id"          object to which s is pointing, as seen by thread T*)
  (*new :: "T \<Rightarrow> id option"          object to which n is pointing, per thread T*)
  det :: "T \<Rightarrow> L list"   (*detached list*)
  for_ctr :: "T \<Rightarrow> nat"        (* aux *)
  res :: "T \<Rightarrow> nat"           (*return v*)
  reg :: "T \<Rightarrow> nat"            (*0 or 1 - local copy of rcu\<^sub>i where i is thread index - is i in rcu or not? *)
  nondet_val :: "T \<Rightarrow> bool"    (* result of function nondet() *)
  CAS_succ :: "T \<Rightarrow> bool"      (*CAS succ, aux*)

(*for pointers we will have A(0) = (x58,pointer) which is equivalent to   A(order) = (address,pointer)
  for variables  --//---    A(1) = (x78,variable) --//--    --//--        A(order) = (address,variable)*)
  

(* start state must take out rcu_addrs  from free_addrs *)


(*---------------- basic functional definitons ----------------------*)

(*int v*)
definition v_allocation :: "mstate \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> bool" ("_ int\<^sub>v[_] _" [200,200])           \<comment>\<open>int v, note v is a local variable\<close>
  where                                                                                           \<comment>\<open>  and doesn't need allocation\<close>
  "v_allocation ms t ms' \<equiv>  ms' =ms \<lparr>v := (v ms) (t := 0),
                                    pc := (pc ms) (t := I4)\<rparr>"
(*int *n*)
definition int_star_n :: "mstate \<Rightarrow> posem \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> bool" ("_ _ int *n\<^sub>_ _ _" [200,200,200,200,200])           \<comment>\<open>int *n\<close>
  where
  "int_star_n ms ps t ms' ps' \<equiv> \<exists> loc prov . (allocate_object ps loc prov ps' 
                                                \<and> ms' = ms \<lparr>n := (n ms) (t := Some (prov)),
                                                           pc := (pc ms) (t := I4) \<rparr>)"
(*int *s*)
definition int_star_s :: "mstate \<Rightarrow> posem \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> bool" ("_ _ int *s\<^sub>_ _ _" [200,200,200,200,200])           \<comment>\<open>int *s\<close>
  where
  "int_star_s ms ps t ms' ps' \<equiv> \<exists> loc prov . (allocate_object ps loc prov ps' 
                                                \<and> ms' = ms \<lparr>s := (s ms) (t := Some (prov)),
                                                           pc := (pc ms) (t := I4) \<rparr>)"


lemma test1:
  assumes "ms ps int *n\<^sub>t ms' ps'"
  assumes "n ms' t = Some 2"
  shows "2 \<notin> dom(A ps)"
  using assms apply (simp add:int_star_n_def allocate_object_def)
  apply clarify
  by(simp add:isfree_addr_def)

lemma test2:
  assumes "ms ps int *n\<^sub>t ms' ps'"
  assumes "n ms' t = Some 2"
  shows "A ps' 2 \<noteq> None"
  using assms apply (simp add:int_star_n_def allocate_object_def)
  apply clarify
  by(simp add:isfree_addr_def)

lemma test3:
  assumes "ms ps int *n\<^sub>t ms' ps'"
  assumes "n ms' t = Some 2"
  shows "(\<exists>x. A ps' 2 =Some x \<and> fst(x) \<notin>alloc_addrs ps)"
  using assms apply (simp add:int_star_n_def allocate_object_def)
  apply clarify 
  by(simp add:isfree_addr_def)




(*******   n = new int   split**********CHECK*)
definition new_int :: "mstate \<Rightarrow> posem \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> bool" ( "_ _ new int\<^sub>_ _ _" [200,200,200,200,200])
  where
  "new_int ms ps t ms' ps' \<equiv> \<exists> loc prov . (allocate_object ps loc prov ps' 
                                                \<and> ms' = ms \<lparr>n_val := (n_val ms) (t := Some (loc)),
                                                           pc := (pc ms) (t := I4) \<rparr>)"
definition point_n_to_newint :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ _ n\<^sub>_ = &newint _ _ _ " [200,200,200,200,200,200,200])
  where   \<comment>\<open> global point n to newint\<close>
  "point_n_to_newint ms ps \<sigma> t ms' ps' \<sigma>' \<equiv> (\<exists>x y.  A ps y = Some x
                                                        \<and> n ms t = Some (fst(x))
                                                        \<and> n_val ms t = Some y
                                      \<and> \<sigma> [fst(x) := y]\<^sub>t \<sigma>'
                                      \<and>  ms' = ms \<lparr> pc := (pc ms) (t := I4)\<rparr>)"

(*******   s = C   split**********)
definition get_C_val :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ _ _ loadsfrom &C   _ _ _" [200,200,200,200,200,200,200])
  where
  "get_C_val ms ps \<sigma> t ms' ps' \<sigma>' \<equiv> (\<exists>x y z.  (fst(y) = C) \<and> A ps x = Some y 
                                      \<and> \<sigma> [z \<leftarrow> fst(y)]\<^sub>t \<sigma>'
                                      \<and> ms' = ms \<lparr> C_val := (C_val ms) (t := Some z),
                                                      pc := (pc ms) (t := I4)\<rparr>)"  
definition change_what_s_points_to :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ _ writeto &s\<^sub>_  _ _ _" [200,200,200,200,200,200,200])
  where
  "change_what_s_points_to ms ps \<sigma> t ms' ps' \<sigma>' \<equiv> (\<exists>x y z.  (s ms t = Some x) 
                                                          \<and> A ps x = Some y 
                                                          \<and> C_val ms t = Some z
                                      \<and> \<sigma> [fst(y) := z]\<^sub>t \<sigma>'
                                      \<and> ms' = ms \<lparr>pc := (pc ms) (t := I4)\<rparr>)" 

(*******   v=*s   split**********)
definition get_s_val :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ _ loadfrom &s\<^sub>_  _ _ _" [200,200,200,200,200,200,200])
  where
  "get_s_val ms ps \<sigma> t ms' ps' \<sigma>' \<equiv> (\<exists>x y z.  (s ms t = Some x) \<and> A ps x = Some y 
                                      \<and> \<sigma> [z \<leftarrow> fst(y)]\<^sub>t \<sigma>'
                                      \<and> ms' = ms \<lparr> s_val := (s_val ms) (t := Some z),
                                                      pc := (pc ms) (t := I4)\<rparr>)" 
definition update_v :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> T \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ _ v\<^sub>_:=*s\<^sub>_ _ _ _ " [200,200,200,200,200,200,200,200])
  where   \<comment>\<open> global read of *s\<close>
  "update_v ms ps \<sigma> t t' ms' ps' \<sigma>' \<equiv> t = t' \<and> (\<exists>x y z.  A ps y = Some x
                                                        \<and> s_val ms t = Some (fst(x))
                                      \<and> \<sigma> [z \<leftarrow> fst(x)]\<^sub>t \<sigma>'
                                      \<and>  ms' = ms \<lparr> v := (v ms) (t := z),
                                                    pc := (pc ms) (t := I4)\<rparr>)"



(*******   *n = v+1   split**********)
definition get_n_val :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ _ loadfrom &n\<^sub>_  _ _ _" [200,200,200,200,200,200,200])
  where
  "get_n_val ms ps \<sigma> t ms' ps' \<sigma>' \<equiv> (\<exists>x y z.  (n ms t = Some x) \<and> A ps x = Some y 
                                      \<and> \<sigma> [z \<leftarrow> fst(y)]\<^sub>t \<sigma>'
                                      \<and> ms' = ms \<lparr> n_val := (n_val ms) (t := Some z),
                                                      pc := (pc ms) (t := I4)\<rparr>)"  
definition writeto_star_n :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ _ writeto *n\<^sub>_ newv _ _ _" [200,200,200,200,200,200,200])
  where
  "writeto_star_n ms ps \<sigma> t ms' ps' \<sigma>' \<equiv> (\<exists>x y.  A ps x = Some y 
                                                           \<and> n_val ms t = Some (fst(y))
                                      \<and> \<sigma> [fst(y) := (v ms t + 1)]\<^sub>t \<sigma>'
                                      \<and>  ms' = ms \<lparr>pc := (pc ms) (t := I4)\<rparr>)"   







(********* free(pop(detached))    idea******************)
definition pop_address :: "mstate \<Rightarrow> posem \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> bool" ("_ _ free(pop[detached(_)]) _ _" [200,200,200,200,200])    \<comment>\<open>pop(detached[tid-1])\<close>
  where
  "pop_address ms ps t ms' ps' \<equiv> (\<exists>i. (A ps i = Some (hd((det ms) t), variable) \<and>
                                       kill ps i ps')) \<and> 
                        ms' = ms\<lparr> det := (det ms) (t:= tl ((det ms) t)),
                                  pc := (pc ms) (t := S2) \<rparr> "

                         (* wr_cap := (wr_cap ms) (hd((det ms) t):=None) \<comment>\<open> let go off wr_cap\<close>\<rparr>"    *)


(*******   r[i] = rcu[i]   split**********)
definition load_rcu_to_r :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> T \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ _ r\<^sub>_[_] = rcu[_] _ _ _" [200,200,200,200,200,200,200,200,200])
  where
  "load_rcu_to_r ms ps \<sigma> t ctr1 ctr2 ms' ps' \<sigma>' \<equiv> ctr1 = ctr2 \<and> 
                                    (\<exists>x y.  (A ps y = Some (rcu_0, pointer)) 
                                      \<and> \<sigma> [x \<leftarrow>(rcu_0 + ctr1)]\<^sub>t \<sigma>'
                                      \<and> ms' = ms \<lparr> r := (r ms) (t := ((r ms) t) (ctr1 :=x)),
                                                      pc := (pc ms) (t := I4) \<rparr>)"

definition enter_rcu :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ _ rcuenter(_) _ _ _" [200,200,200,200,200,200,200])
  where
  "enter_rcu ms ps \<sigma> t ms' ps' \<sigma>' \<equiv>  (\<exists>x.  (A ps x = Some (rcu_0, pointer))
                                      \<and> (\<sigma> [ (rcu_0+t) := 1 ]\<^sub>t \<sigma>')
                                      \<and> (ms' = ms \<lparr> pc := (pc ms) (t := I4) \<rparr>))" 

definition exit_rcu :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ _ rcuexit(_) _ _ _" [200,200,200,200,200,200,200])
  where
  "exit_rcu ms ps \<sigma> t ms' ps' \<sigma>' \<equiv>  (\<exists>x.  (A ps x = Some (rcu_0, pointer))
                                      \<and> (\<sigma> [ (rcu_0+t) := 0 ]\<^sub>t \<sigma>')
                                      \<and> (ms' = ms \<lparr> pc := (pc ms) (t := I4) \<rparr>))" 

definition setup_r :: "mstate \<Rightarrow> T \<Rightarrow>  mstate \<Rightarrow> bool" ("_ r[N]\<^sub>_ := _" [200])    \<comment>\<open>r[N] = {0}\<close>
  where
  "setup_r  ms t ms' \<equiv> ms' = ms\<lparr>r := \<lambda> x n. if x = t then 0 else r ms x n\<rparr>"












(*\<forall>i. (i\<in> free_addrs) \<longleftrightarrow> rd_cap ms i = {} *)
(*cannot take set wr_cap l ms :=t if wr_cap l ms=t*)
(*must have rd_cap on l (t\<in>rd_cap l ms) to perform wr_cap l ms := t*)
(*capabilities stuff
definition relinquish_rd_cap :: "T \<Rightarrow> mstate \<Rightarrow> mstate" ("give\<^sub>u\<^sub>p _" [200])
  where 
  "relinquish_rd_cap t ms \<equiv> ms \<lparr> rd_cap := \<lambda> x. if  t\<in>rd_cap ms x  then rd_cap ms x - {t} else rd_cap ms x \<rparr>"

definition take_rd_cap :: "L \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> mstate" ("take\<^sub>_ _" [200,200])
  where 
  "take_rd_cap l t ms \<equiv> ms \<lparr> rd_cap := (rd_cap ms) (l := ((rd_cap ms l) \<union> {t})) \<rparr>"
*)(*decide where to put this^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)












definition insert_address :: " T \<Rightarrow> nat \<Rightarrow> mstate \<Rightarrow> mstate" ("insert[detached(_),_]" [200,200])    \<comment>\<open>insert(_, s)\<close>
  where
  "insert_address loc t ms  \<equiv> ms\<lparr> det := (det ms) (t:= (((det ms) t) @ [loc])) \<rparr>"


definition nondet :: " T \<Rightarrow> bool \<Rightarrow> mstate \<Rightarrow> mstate" ("nondet[_,_]" [200])    \<comment>\<open>nondet()\<close>
  where
  "nondet t b ms \<equiv> (ms \<lparr> nondet_val := (nondet_val ms) (t:= b)\<rparr>) "

definition update_pc :: "T \<Rightarrow> PC \<Rightarrow> mstate \<Rightarrow>  mstate" ( "pc[_]:=_" [200,200])
  where
  "update_pc t pc_val ms \<equiv>  ms \<lparr> pc := (pc ms) (t:=pc_val) \<rparr> "












abbreviation inc_ctr :: "T \<Rightarrow> mstate \<Rightarrow> mstate" ( "ctr[_]++" [200])
  where
  "inc_ctr t ms \<equiv>  ms \<lparr> for_ctr := (for_ctr ms) (t:=(for_ctr ms t)+1) \<rparr> "

abbreviation update_ctr :: "T \<Rightarrow> nat \<Rightarrow> mstate \<Rightarrow> mstate" ( "ctr[_]:=_" [200,200])
  where
  "update_ctr t ctr_val ms \<equiv> ms \<lparr> for_ctr := (for_ctr ms) (t:=ctr_val) \<rparr> "

abbreviation rcu_temp_copy :: "mstate \<Rightarrow> surrey_state \<Rightarrow> nat \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ load(_)\<^sub>_ _ _" [200,200,200,200,200,200])
  where
  "rcu_temp_copy ms \<sigma> ctr_val t ms' \<sigma>'\<equiv> \<exists> v. ((\<sigma> [ v \<leftarrow> (rcu_0 + ctr_val)]\<^sub>t \<sigma>')     \<comment>\<open>read rcu[i]\<close>
                                        \<and> (ms' = ms\<lparr>reg := (reg ms) (t := v),
                                                    pc := (pc ms) (t := S8)\<rparr>)) "

definition cas_step_rcu :: "mstate \<Rightarrow> surrey_state \<Rightarrow>T \<Rightarrow> L \<Rightarrow> V \<Rightarrow> V \<Rightarrow> mstate \<Rightarrow>  surrey_state \<Rightarrow> bool" 
 where
    "cas_step_rcu ms \<sigma> t l cv nv ms' \<sigma>'\<equiv>           \<comment>\<open>CAS(&C,s,n)\<close>
       \<exists> w ts'. w \<in> visible_writes \<sigma> t l \<and>
               w \<notin> covered \<sigma> \<and>
               valid_fresh_ts \<sigma> w ts' \<and>
       \<sigma>' = fst(CAS t w cv nv \<sigma> ts')
       \<and> (ms' = ms\<lparr>CAS_succ := (CAS_succ ms) (t := snd(CAS t w cv nv \<sigma> ts')),
                         pc := (pc ms) (t := I12),
                         wr_cap := (wr_cap ms) (cv := Some t)\<rparr>)"           \<comment>\<open>acquire wr_cap on location\<close>











(*==========================   Thread behaviour   =================================*)

section \<open>Reclaim Method\<close>
definition reclaim :: "PC \<Rightarrow> T \<Rightarrow> L \<Rightarrow>  mstate \<Rightarrow> surrey_state \<Rightarrow> mstate \<Rightarrow> surrey_state \<Rightarrow> bool " where
"reclaim pcr t loc ms \<sigma> ms' \<sigma>' \<equiv> 
case pcr of 
   R1 \<Rightarrow> (ms' = ((insert[detached(t),loc]) \<circ> (pc[t]:=R2)) ms) \<and> \<sigma> =\<sigma>'
|  R2 \<Rightarrow> (\<exists>b. (b\<in>{True,False} \<and> ms' = (nondet[t,b] \<circ> pc[t]:=R2) ms)) \<and> \<sigma> =\<sigma>'
|  R3 \<Rightarrow> if (nondet_val ms t) = True 
            then ms' = (pc[t]:=S1)  ms    \<and> \<sigma> =\<sigma>'  
               \<comment>\<open> sync() \<close>
            else ms' = (pc[t]:=I14) ms    \<and> \<sigma> =\<sigma>'    \<comment>\<open> return to inc() \<close>
|  R4 \<Rightarrow> if (det ms t \<noteq> [])
            then ms' = (pc[t]:=R5)  ms    \<and> \<sigma> =\<sigma>'
            else ms' = (pc[t]:=I14) ms    \<and> \<sigma> =\<sigma>'    \<comment>\<open> return to inc() \<close>
|  R5 \<Rightarrow> (ms'= ((pop[detached(t)]) \<circ> (pc[t]:=R4)) ms)  \<and> \<sigma> =\<sigma>'"


section \<open>Sync Method\<close>
definition synch :: "PC \<Rightarrow> T \<Rightarrow>  mstate \<Rightarrow> surrey_state \<Rightarrow> mstate \<Rightarrow> surrey_state \<Rightarrow> bool " where
"synch pcr t ms \<sigma> ms' \<sigma>' \<equiv> 
case pcr of
   S1 \<Rightarrow> ms' = ((r[N]\<^sub>t := 0) \<circ> ctr[t]:=0 \<circ> pc[t]:=S2) ms'    \<and> \<sigma> =\<sigma>'
|  S2 \<Rightarrow> if (for_ctr ms t < T_max)
            then ms' = (pc[t]:=S3) ms    \<and> \<sigma> =\<sigma>'
            else ms' = (pc[t]:=S4) ms    \<and> \<sigma> =\<sigma>'
|  S3 \<Rightarrow> (ms \<sigma> r[t,(for_ctr ms t)]:=rcuequiv ms' \<sigma>')
|  S4 \<Rightarrow> ms' = (ctr[t]:=0 \<circ> pc[t]:=S5) ms    \<and> \<sigma> =\<sigma>'
|  S5 \<Rightarrow> if (for_ctr ms t < T_max)
            then ms' = (pc[t]:=S6) ms    \<and> \<sigma> =\<sigma>'
            else ms' = (pc[t]:=R4) ms    \<and> \<sigma> =\<sigma>'        \<comment>\<open> return to Reclaim (R4)\<close>
|  S6 \<Rightarrow> if r ms t (for_ctr ms t) = 0
            then ms' = (pc[t]:=S7) ms    \<and> \<sigma> =\<sigma>'
            else ms' = (pc[t]:=S8) ms    \<and> \<sigma> =\<sigma>'
|  S7 \<Rightarrow> ms \<sigma> load(for_ctr ms t)\<^sub>t ms' \<sigma>'         \<comment>\<open> load \<langle>rcu[i]\<rangle> into reg, increment pc\<close>
|  S8 \<Rightarrow> if reg ms t = 1                         \<comment>\<open> test while \<langle>rcu[i]\<rangle>\<close>
            then True
            else ms' = (ctr[t]++ \<circ> pc[t]:=S5) ms    \<and> \<sigma> =\<sigma>'"

section \<open>Increment Method\<close>
definition increment :: "PC \<Rightarrow> T \<Rightarrow>  mstate \<Rightarrow> surrey_state \<Rightarrow> mstate \<Rightarrow> surrey_state \<Rightarrow> bool " where
"increment pcr t ms \<sigma> ms' \<sigma>' \<equiv> 
case pcr of
   I1  \<Rightarrow> (ms int\<^sub>v[t] ms') \<and> \<sigma> = \<sigma>'       \<comment>\<open> int v, v=0\<close>
|  I2  \<Rightarrow> (ms int\<^sub>n[t] ms') \<and> \<sigma> = \<sigma>'       \<comment>\<open> int n\<close>
|  I3  \<Rightarrow> (ms int\<^sub>s[t] ms') \<and> \<sigma> = \<sigma>'       \<comment>\<open> int s\<close>
|  I4  \<Rightarrow> (ms \<sigma> newint[*n, t] ms' \<sigma>')     \<comment>\<open> *n=new int\<close>
|  I5  \<Rightarrow> (\<sigma> enter[t] \<sigma>) \<and> (ms' = (pc[t]:=I6) ms)                \<comment>\<open> rcu_enter()\<close>
|  I6  \<Rightarrow> (\<sigma> exit[t] \<sigma>)  \<and> (ms' = ((pc[t]:=I7) \<circ> (give\<^sub>u\<^sub>p t)) ms)  \<comment>\<open> rcu_exit()     relinquish all read capabilities\<close>
|  I7  \<Rightarrow> (\<sigma> enter[t] \<sigma>) \<and> (ms' = (pc[t]:=I8) ms)                \<comment>\<open> rcu_enter()\<close>
|  I8  \<Rightarrow> ms \<sigma> load[(s ms t),C,t] ms' \<sigma>'                                \<comment>\<open> s=C \<close>
|  I9  \<Rightarrow> (ms' = ((pc[t]:=I10)\<circ> (v[t]:=(s ms t))) ms)     \<and> \<sigma> = \<sigma>'      \<comment>\<open> v=*s ******    redundant step, if we assume Allocation map to not have weak behaviour\<close>
|  I10 \<Rightarrow> (ms' = ((pc[t]:=I11)\<circ> (*n[t]:=(v ms t + 1))) ms) \<and> \<sigma> = \<sigma>'      \<comment>\<open> *n=v+1 ****** \<close>
|  I11 \<Rightarrow> cas_step_rcu ms \<sigma> t C (s ms t) (n ms t) ms' \<sigma>'          \<comment>\<open> CAS(&C,s,n) \<close>
|  I12 \<Rightarrow> if CAS_succ ms t
            then (ms' = (pc[t]:=I13) ms)
            else (ms' = (pc[t]:=I6) ms)
|  I13 \<Rightarrow> (\<sigma> exit[t] \<sigma>) \<and> (ms' = ((pc[t]:=R1) \<circ> (give\<^sub>u\<^sub>p t)) ms)    \<comment>\<open> rcu_exit()     relinquish all read capabilities\<close>
        \<comment>\<open>reclaim(s)\<close>
|  I14 \<Rightarrow> (ms' = (pc[t]:=I15) ms) \<and> \<sigma> = \<sigma>'   \<comment>\<open> return(v) \<close>"


definition "init ms  \<equiv>  (\<forall>t. (t<T_max)\<longrightarrow> pc ms t = I1
                                        \<and> v ms t = 0
                                        \<and> n ms t = 0
                                        \<and> s ms t = 0
                                        \<and> det ms t = []
                                        \<and> for_ctr ms t = 0
                                        \<and> res ms t = False
                                        \<and> reg ms t = 0
                                       
                                        \<and> nondet_val ms t = False
                                        \<and> CAS_succ ms t = False
                                        \<and> rd_cap ms t = {}
                                        \<and> wr_cap ms t = None)
\<comment>\<open> free_addrs ms t = ?)\<close>
                     \<and> (\<forall>t i. (t<T_max \<and> i<T_max)\<longrightarrow> r ms t i = 0)"



(*load stores value to a location in weak memory
s=C \<longrightarrow> s.next = C.next
v=*s \<longrightarrow> v = s.next.val
n_star <--_t fst(A(n ms t))
n_star =_t v+1
n*=v+1 \<longrightarrow> n.next.val = v+1

memory model:   ____________C____s____n________old__new_____________n2________________
             ...|___||___||x52||x54||x56||___||x78||x80||___||___||x90||___||___||___|
                |___||___||x78||x78||x80||___||_0_||_x_||___||___||___||___||___||___| ...
                ____________C____s____n1_______old__new_____________n2________________
             ...|___||___||_C_||_s_||_n1||___||x78||x80||___||___||x90||___||___||___|
                |___||___||x80||___||x80||___||Nul||_1_||___||___||___||___||___||___| ...
 

[(s ms t) :=  C] 
[v <-_t (s ms t)]
[fst(A(n ms t)) :=_t v+1]


    ____                          ______
    |__|  <-- Location            |0x52|
C=  |__|  <-- C.next    (C.val)   |0x78|    <-- old.loc
    ____                          ______
    |__|  <-- Location            |0x54|
s=  |__|  <-- s.next    (s.val)   |0x80|
    ____                          ______
    |__|  <-- Location = s.next   |0x80| 
v=  |__|  <-- v.val               |__2_|
    ____                          ______
    |__|  <-- Location            |0x56|
n=  |__|  <-- n.next    (n.val)   |0x80|



rd_cap(i) \<noteq> {} \<longrightarrow> A(i) --\\<longrightarrow> none
wr_cap(i) \<noteq> {} \<longrightarrow> A(i) --\\<longrightarrow> none
wr_cap(i) \<noteq> {} \<longrightarrow> cannot acquire rd_cap(i)

A(0) = (x52,pointer)
A(1) = (x78, variable)


A(0) = (x52,pointer)
A(1) = (x78,variable)

*A(0) = 0
M(x78,variable) = 0
M(x52,pointer) = x78


[load_C ms t <--_t C]     <---- returns C
*A(0) = {x | \<exists>i. i=x \<and> fst(A(i)) = load_C}

***or equivalently***

\<exists>j. A(j) = (load_C, variable)
[load_old ms t <--_t load_C]    <---- returns old


*)



lemma "reclaim R2 t l ms \<sigma> ms' \<sigma>' 
  \<Longrightarrow>  (nondet_val ms' t) \<in>{True,False}"
  by simp


