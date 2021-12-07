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
  v :: "T \<Rightarrow> bool"
  n :: "T \<Rightarrow> bool"        (*now modelled as local pointer allocation - True/False*)
  s :: "T \<Rightarrow> bool"        (*now modelled as local pointer allocation - True/False*)
  v_val :: "T \<Rightarrow> nat option"        (*now modelled as local value - so M(&v)*)
  n_val :: "T \<Rightarrow> nat option"        (*now modelled as local value - so M(&n)*)
  s_val :: "T \<Rightarrow> nat option"        (*now modelled as local value - so M(&s)*)
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
definition v_allocation :: "mstate \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> bool" ("_ int[v\<^sub>_] _" [200,200])           \<comment>\<open>int v, note v is a local variable\<close>
  where                                                                                           \<comment>\<open>  and doesn't need allocation\<close>
  "v_allocation ms t ms' \<equiv>  ms' =ms \<lparr>v := (v ms) (t := True),
                                 v_val := (v_val ms) (t := None),
                                    pc := (pc ms) (t := I4)\<rparr>"
(*int *n*)
definition int_star_n :: "mstate \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> bool" ("_ int[*n\<^sub>_] _" [200,200,200])           \<comment>\<open>int *n\<close>
  where
  "int_star_n ms t ms' \<equiv> ms' = ms \<lparr>n := (n ms) (t := True),
                               n_val := (n_val ms) (t := None),
                                  pc := (pc ms) (t := I4)\<rparr>"
(*int *s*)
definition int_star_s :: "mstate \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> bool" ("_ int[*s\<^sub>_] _" [200,200,200])           \<comment>\<open>int *s\<close>
  where
  "int_star_s ms t ms' \<equiv> ms' = ms \<lparr>s := (s ms) (t := True),
                               s_val := (s_val ms) (t := None),
                                  pc := (pc ms) (t := I4) \<rparr>"




(*******   n = new int  **********)
definition new_int :: "mstate \<Rightarrow> posem \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> bool" ( "_ _ n:=newint _ _ _" [200,200,200,200,200])
  where
  "new_int ms ps t ms' ps' \<equiv> ps = ps' \<and>(\<exists> loc prov . (allocate_object ps loc prov ps' 
                                                \<and> ms' = ms \<lparr>n_val := (n_val ms) (t := Some (loc)),
                                                               pc := (pc ms) (t := I4) \<rparr>))"


(*******   s = C   **********)
definition get_C_val :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ _ s:=C _ _ _ _" [200,200,200,200,200,200,200])
  where
  "get_C_val ms ps \<sigma> t ms' ps' \<sigma>' \<equiv> ps = ps' \<and> (\<exists>x y z.  (fst(y) = C) \<and> A ps x = Some y 
                                      \<and> \<sigma> [z \<leftarrow> fst(y)]\<^sub>t \<sigma>'
                                      \<and> ms' = ms \<lparr> s_val := (s_val ms) (t := Some z),
                                                      pc := (pc ms) (t := I4)\<rparr>)" 

(*******   v=*s   **********)
definition get_s_val :: "mstate \<Rightarrow> surrey_state \<Rightarrow> T  \<Rightarrow> mstate \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ v:=*s _ _ _" [200,200,200,200,200])
  where
  "get_s_val ms \<sigma> t ms' \<sigma>' \<equiv>  (\<exists>x z.  (s_val ms t = Some x)
                                      \<and> \<sigma> [z \<leftarrow> x]\<^sub>t \<sigma>'
                                      \<and> ms' = ms \<lparr> v_val := (v_val ms) (t := Some z),
                                                      pc := (pc ms) (t := I4)\<rparr>)" 


(*******   *n = v+1   **********) 
definition writeto_star_n :: "mstate \<Rightarrow> surrey_state \<Rightarrow> T  \<Rightarrow> mstate \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ *n:=newv _ _ _" [200,200,200,200,200])
  where
  "writeto_star_n ms \<sigma> t ms' \<sigma>' \<equiv>  (\<exists>x y.   n_val ms t = Some (y)
                                                   \<and> v_val ms t = Some (x)
                                          \<and> \<sigma> [y := (x + 1)]\<^sub>t \<sigma>'
                                          \<and>  ms' = ms \<lparr>pc := (pc ms) (t := I4)\<rparr>)"   







(********* free(pop(detached)) ******************)
definition pop_address :: "mstate \<Rightarrow> posem \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> bool" ("_ _ free[pop[detached[_]]] _ _" [200,200,200,200,200])    \<comment>\<open>pop(detached[tid-1])\<close>
  where
  "pop_address ms ps t ms' ps' \<equiv> (\<exists>i. (A ps i = Some (hd((det ms) t), variable) \<and>
                                       kill ps i ps')) \<and> 
                        ms' = ms\<lparr> det := (det ms) (t:= tl ((det ms) t)),
                                  pc := (pc ms) (t := S2) \<rparr> "

                         (* wr_cap := (wr_cap ms) (hd((det ms) t):=None) \<comment>\<open> let go off wr_cap\<close>\<rparr>"    *)


(*******   r[i] = rcu[i]   **********)
definition load_rcu_to_r :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow>  T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ _ r[i]:=rcu[i] _ _ _ _" [200,200,200,200,200])
  where
  "load_rcu_to_r ms ps \<sigma> t ms' ps' \<sigma>' \<equiv> ps = ps' \<and> (\<exists>x y.  (A ps y = Some (rcu_0, pointer)) 
                                      \<and> \<sigma> [x \<leftarrow>(rcu_0 + (for_ctr ms t))]\<^sub>t \<sigma>'
                                      \<and> ms' = ms \<lparr> r := (r ms) (t := ((r ms) t) ((for_ctr ms t) :=x)),
                                                      pc := (pc ms) (t := I4) \<rparr>)"

definition enter_rcu :: "posem \<Rightarrow> surrey_state \<Rightarrow> T \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ rcuenter[] _ _ _" [200,200,200,200,200])
  where
  "enter_rcu ps \<sigma> t  ps' \<sigma>' \<equiv>  ps = ps' \<and> (\<exists>x.  (A ps x = Some (rcu_0, pointer))
                                      \<and> (\<sigma> [ (rcu_0+t) := 1 ]\<^sub>t \<sigma>'))" 

definition exit_rcu :: "posem \<Rightarrow> surrey_state \<Rightarrow> T \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ rcuexit[] _ _ _" [200,200,200,200,200])
  where
  "exit_rcu ps \<sigma> t ps' \<sigma>' \<equiv>  ps = ps' \<and> (\<exists>x.  (A ps x = Some (rcu_0, pointer))
                                      \<and> (\<sigma> [ (rcu_0+t) := 0 ]\<^sub>t \<sigma>'))" 

definition setup_r :: "mstate \<Rightarrow> T \<Rightarrow>  mstate \<Rightarrow> bool" ("_ r[N]:={0} _ _" [200])    \<comment>\<open>r[N] = {0}\<close>
  where
  "setup_r  ms t ms' \<equiv> ms' = ms\<lparr>r := \<lambda> x n. if x = t then 0 else r ms x n,
                                  pc := (pc ms) (t := S2)\<rparr>"












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



definition insert_address :: " mstate \<Rightarrow> T \<Rightarrow> nat \<Rightarrow> mstate \<Rightarrow> bool" ("_ insert[detached[_],_] _" [200,200,200,200])    \<comment>\<open>insert(_, s)\<close>
  where
  "insert_address ms loc t ms' \<equiv> ms' = ms\<lparr> det := (det ms) (t:= (((det ms) t) @ [loc])),
                                            pc := (pc ms) (t := S2) \<rparr>"


definition nondet :: "mstate \<Rightarrow> T \<Rightarrow> bool \<Rightarrow> mstate \<Rightarrow> bool" ("_ nondet[_,_] _" [200,200,200,200])    \<comment>\<open>nondet()\<close>
  where
  "nondet ms t b ms' \<equiv> ms' = ms \<lparr> nondet_val := (nondet_val ms) (t:= b),
                                          pc := (pc ms) (t := S2)\<rparr>"


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
                         pc := (pc ms) (t := I12)\<rparr>)"           \<comment>\<open>acquire wr_cap on location\<close>










abbreviation inc_ctr :: "T \<Rightarrow> mstate \<Rightarrow> mstate" ( "ctr[_]++" [200])
  where
  "inc_ctr t ms \<equiv>  ms \<lparr> for_ctr := (for_ctr ms) (t:=(for_ctr ms t)+1) \<rparr> "

abbreviation update_ctr :: "T \<Rightarrow> nat \<Rightarrow> mstate \<Rightarrow> mstate" ( "ctr[_]:=_" [200,200])
  where
  "update_ctr t ctr_val ms \<equiv> ms \<lparr> for_ctr := (for_ctr ms) (t:=ctr_val) \<rparr> "

definition update_pc :: "T \<Rightarrow> PC \<Rightarrow> mstate \<Rightarrow>  mstate" ( "pc[_]:=_" [200,200])
  where
  "update_pc t pc_val ms \<equiv>  ms \<lparr> pc := (pc ms) (t:=pc_val) \<rparr> "











(*==========================   Thread behaviour   =================================*)

section \<open>Reclaim Method\<close>
definition reclaim :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow>  PC \<Rightarrow> T \<Rightarrow> L \<Rightarrow>  mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool " where
"reclaim ms ps \<sigma> pcr t loc ms' ps' \<sigma>' \<equiv> 
case pcr of 
   R1 \<Rightarrow> (ms insert[detached[t],the (s_val ms t)] ms') \<and> ps = ps' \<and> \<sigma> =\<sigma>' 
|  R2 \<Rightarrow> (\<exists>b. (b\<in>{True,False} \<and> (ms nondet[t,b] ms'))) \<and> ps = ps' \<and> \<sigma> =\<sigma>' 
|  R3 \<Rightarrow> if (nondet_val ms t) = True 
            then ms' = (pc[t]:=S1) ms  \<and> ps = ps' \<and> \<sigma> =\<sigma>'  
               \<comment>\<open> sync() \<close>
            else ms' = (pc[t]:=I14) ms  \<and> ps = ps' \<and> \<sigma> =\<sigma>'  
               \<comment>\<open> return to inc() \<close>
|  R4 \<Rightarrow> if (det ms t \<noteq> [])
            then ms' = (pc[t]:=R5)  ms  \<and> ps = ps' \<and> \<sigma> =\<sigma>'  
            else ms' = (pc[t]:=I14) ms  \<and> ps = ps' \<and> \<sigma> =\<sigma>'     \<comment>\<open> return to inc() \<close>
|  R5 \<Rightarrow> (ms ps free[pop[detached[the (s_val ms t)]]] ms' ps')  \<and> \<sigma> =\<sigma>'"


section \<open>Sync Method\<close>
definition synch :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> PC \<Rightarrow> T \<Rightarrow>  mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool " where
"synch ms ps \<sigma> pcr t ms' ps' \<sigma>' \<equiv> 
case pcr of
   S1 \<Rightarrow> (ms r[N]:={0} t ms) \<and> ps = ps'  \<and> \<sigma> = \<sigma>'
|  S2 \<Rightarrow> if (for_ctr ms t < T_max)
            then ms' = (pc[t]:=S3) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
            else ms' = (pc[t]:=S4) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
|  S3 \<Rightarrow> (ms ps \<sigma> r[i]:=rcu[i] t ms' ps' \<sigma>')
|  S4 \<Rightarrow> ms' = (ctr[t]:=0 \<circ> pc[t]:=S5) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
|  S5 \<Rightarrow> if (for_ctr ms t < T_max)
            then ms' = (pc[t]:=S6) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
            else ms' = (pc[t]:=R4) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'        \<comment>\<open> return to Reclaim (R4)\<close>
|  S6 \<Rightarrow> if r ms t (for_ctr ms t) = 0
            then ms' = (pc[t]:=S7) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
            else ms' = (pc[t]:=S8) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
|  S7 \<Rightarrow> ms \<sigma> load(for_ctr ms t)\<^sub>t ms' \<sigma>' \<and> ps = ps'  \<comment>\<open> load \<langle>rcu[i]\<rangle> into reg, increment pc\<close>
|  S8 \<Rightarrow> if reg ms t = 1                             \<comment>\<open> test while \<langle>rcu[i]\<rangle>\<close>
            then True
            else ms' = (ctr[t]++ \<circ> pc[t]:=S5) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'"

section \<open>Increment Method\<close>
definition increment :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> PC \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool " where
"increment ms ps \<sigma> pcr t ms' ps' \<sigma>' \<equiv> 
case pcr of
   I1  \<Rightarrow> (ms int[v\<^sub>t] ms')  \<and> ps = ps' \<and> \<sigma> = \<sigma>'
|  I2  \<Rightarrow> (ms int[*n\<^sub>t] ms') \<and> ps = ps' \<and> \<sigma> = \<sigma>'
|  I3  \<Rightarrow> (ms int[*s\<^sub>t] ms') \<and> ps = ps' \<and> \<sigma> = \<sigma>'
|  I4  \<Rightarrow> (ms ps n:=newint t ms' ps')  \<and> \<sigma> = \<sigma>'
|  I5  \<Rightarrow> (ps \<sigma> rcuenter[] t ps' \<sigma>') \<and> (ms' = (pc[t]:=I6) ms)
|  I6  \<Rightarrow> (ps \<sigma> rcuexit[] t ps' \<sigma>')  \<and> (ms' = (pc[t]:=I7) ms)  \<comment>\<open> relinquish all read capabilities\<close>
|  I7  \<Rightarrow> (ps \<sigma> rcuenter[] t ps' \<sigma>') \<and> (ms' = (pc[t]:=I8) ms)
|  I8  \<Rightarrow> (ms ps \<sigma> s:=C t ms' ps' \<sigma>')
|  I9  \<Rightarrow> (ms \<sigma> v:=*s t ms' \<sigma>')      \<and> ps = ps'     
|  I10 \<Rightarrow> (ms \<sigma> *n:=newv t ms' \<sigma>')   \<and> ps = ps'
|  I11 \<Rightarrow> cas_step_rcu ms \<sigma> t C (the (s_val ms t)) (the (n_val ms t)) ms' \<sigma>' \<and> ps = ps'
|  I12 \<Rightarrow> if CAS_succ ms t
            then (ms' = (pc[t]:=I13) ms)
            else (ms' = (pc[t]:=I6) ms)
|  I13 \<Rightarrow> (ps \<sigma> rcuexit[] t ps' \<sigma>') \<and> (ms' = ((pc[t]:=R1)) ms) \<comment>\<open>relinquish all read capabilities\<close>
        \<comment>\<open>reclaim(s)\<close>
|  I14 \<Rightarrow> (ms' = (pc[t]:=I15) ms) \<and> \<sigma> = \<sigma>'   \<comment>\<open> return(v) \<close>"


definition "init ms ps \<equiv>  (\<forall>t. (t<T_max)\<longrightarrow> pc ms t = I1
                         \<and> v ms t = False
                         \<and> n ms t = False
                         \<and> s ms t = False
                         \<and> v_val ms t = Some (0)
                         \<and> n_val ms t = Some (0)
                         \<and> s_val ms t = Some (0) 
                         \<and> det ms t = []
                         \<and> for_ctr ms t = 0
                         \<and> res ms t = 0
                         \<and> reg ms t = 0
                         \<and> nondet_val ms t = False
                         \<and> CAS_succ ms t = False)
                         \<and> (\<forall>t k. (t<T_max \<and> k<T_max) \<longrightarrow> 
                                          r ms t k = 0)
        \<and> (\<forall>i j. (i\<ge>0 \<and> j\<ge>0) \<longrightarrow> 
                       A ps i = None
                     \<and> rd_cap ps j = {}
                     \<and> wr_cap ps j = None)
                     \<and> alloc_addrs ps = {}"






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



*)

