theory RCU
imports Main PSem
begin 
(*weaken invariant own\<^sub>w rather than own\<^sub>R *)
(*add statement on n:=newint (ABA invariant)*)



datatype PC = I1 | I2 | I3 | I4 | I5 | I6 | I7 | I8 | I9 | I10 | I11 | I12 | I13 | I14 |  cas_res | finished
            | R1 | R2 | R3 | R4 | R5 
            | S1 | S2 | S3 | S4 | S5 | S6 | S7 


consts rcu_0 ::address (*first location of rcu array*)
consts F::nat
consts T_max::nat (*max_thread ID - 1*)
consts C :: nat     (*just referred to by its location in A(1) = (C,pointer) where C = nat*)
consts casloc :: nat
definition "set_T \<equiv> {n . n\<ge>0 \<and> n<T_max}"
definition "rcu_addrs \<equiv> {n . n\<ge>rcu_0 \<and> n < rcu_0+T_max}"
definition "something  \<equiv> F \<notin> rcu_addrs \<and> F \<noteq> C \<and> F \<noteq> casloc"

lemma test:
  assumes "F = i"
  and "something"
  shows "C \<noteq> i"
  using assms 
  by(simp add:something_def) 






(*Recorded variables partial function*)
record mstate =
  pc :: "T \<Rightarrow> PC"
  r :: "T \<Rightarrow> nat \<Rightarrow> nat"        (*local copy of rcu*)
  n_alloc :: "T \<Rightarrow> bool"        (*now modelled as local pointer allocation - True/False*)
  s_alloc :: "T \<Rightarrow> bool"        (*now modelled as local pointer allocation - True/False*)
  v :: "T \<Rightarrow> nat option"        (*now modelled as local value - so M(&v)*)
  n :: "T \<Rightarrow> nat option"        (*now modelled as local value - so M(&n)*)
  s :: "T \<Rightarrow> nat option"        (*now modelled as local value - so M(&s)*)
  det :: "T \<Rightarrow> L list"   (*detached list*)
  CTRsync\<^sub>1 :: "T \<Rightarrow> nat"
  CTRsync\<^sub>2 :: "T \<Rightarrow> nat"
  res :: "T \<Rightarrow> nat"           (*return v*)
  reg :: "T \<Rightarrow> nat"            (*says whether a thread is locally in RCU or not*)
  nondet_val :: "T \<Rightarrow> bool"    (* result of function nondet() *)
  CAS_succ :: "T \<Rightarrow> bool"      (*CAS succ, aux*)
  repeat :: "T \<Rightarrow> bool"              (*says whether the CAS has failed*)

  own\<^sub>R :: "nat \<Rightarrow> nat set"      (* own\<^sub>R ms i = { ... 2, 3, 6, ...}*)
  own\<^sub>W :: "nat \<Rightarrow> nat option"   (* own\<^sub>W ms i = Some 1 or own\<^sub>W ms i = None*)


(*for pointers we will have A(0) = (x58,pointer) which is equivalent to   A(order) = (address,pointer)
  for variables  --//---    A(1) = (x78,variable) --//--    --//--        A(order) = (address,variable)*)
  

(* start state must take out rcu_addrs  from free_addrs *)

(*---------------- ownership transfer functions ---------------------*)

definition take_read_ownership :: "T \<Rightarrow> nat \<Rightarrow> mstate \<Rightarrow> mstate" ("takesRown[_,_]" [200,200])
  where
  "take_read_ownership t loc ms \<equiv>  ms \<lparr> own\<^sub>R := (own\<^sub>R ms) (loc:=own\<^sub>R ms loc \<union> {t}) \<rparr>"

definition giveup_readandwrite_ownership :: "T \<Rightarrow> nat \<Rightarrow> mstate \<Rightarrow> mstate" ("givesupRown[_,_]" [200,200])
  where
  "giveup_readandwrite_ownership t loc ms \<equiv>  if own\<^sub>W ms loc \<noteq> Some t 
                                            then ms \<lparr> own\<^sub>R := (own\<^sub>R ms) (loc:=own\<^sub>R ms loc - {t}) \<rparr>
                                            else ms \<lparr> own\<^sub>R := (own\<^sub>R ms) (loc:=own\<^sub>R ms loc - {t}),
                                                      own\<^sub>W := (own\<^sub>W ms) (loc:=None)\<rparr>"

definition take_write_ownership :: "T \<Rightarrow> nat \<Rightarrow> mstate \<Rightarrow> mstate" ("takesWown[_,_]" [200,200])
  where
  "take_write_ownership t loc ms \<equiv>   ms \<lparr> own\<^sub>R := (own\<^sub>R ms) (loc:=own\<^sub>R ms loc \<union> {t}),
                                          own\<^sub>W := (own\<^sub>W ms) (loc:=Some t)\<rparr>"




(*---------------- basic functional definitons ----------------------*)

(*int v*)
definition v_allocation :: "mstate \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> bool" ("_ int[v\<^sub>_] _" [200,200])           \<comment>\<open>int v, note v is a local variable\<close>
  where                                                                                           \<comment>\<open>  and doesn't need allocation\<close>
  "v_allocation ms t ms' \<equiv>  ms' =ms \<lparr>v := (v ms) (t := None),
                                    pc := (pc ms) (t := I2)\<rparr>"
(*int *n*)
definition int_star_n :: "mstate \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> bool" ("_ int[*n\<^sub>_] _" [200,200,200])           \<comment>\<open>int *n\<close>
  where
  "int_star_n ms t ms' \<equiv> ms' = ms \<lparr>n_alloc := (n_alloc ms) (t := True),
                               n := (n ms) (t := None),
                                  pc := (pc ms) (t := I3)\<rparr>"
(*int *s*)
definition int_star_s :: "mstate \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> bool" ("_ int[*s\<^sub>_] _" [200,200,200])           \<comment>\<open>int *s\<close>
  where
  "int_star_s ms t ms' \<equiv> ms' = ms \<lparr>s_alloc := (s_alloc ms) (t := True),
                               s := (s ms) (t := None),
                                  pc := (pc ms) (t := I4) \<rparr>"




(*******   n = new int  **********)
definition new_int :: "mstate \<Rightarrow> posem \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> bool" ( "_ _ n:=newint _ _ _" [200,200,200,200,200])
  where
  "new_int ms ps t ms' ps' \<equiv> (\<exists> loc prov . (allocate_object ps loc prov ps' 
                                    \<and> ms' = ms \<lparr>n := (n ms) (t := Some loc),
                                                 own\<^sub>R := (own\<^sub>R ms) (loc:=own\<^sub>R ms loc \<union> {t}),
                                                 own\<^sub>W := (own\<^sub>W ms) (loc:=Some t),
                                                   pc := (pc ms) (t := I5) \<rparr>))"


(*******   s = C   **********)
definition get_C_val :: "mstate \<Rightarrow> surrey_state \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ s:=\<^sup>FC _ _ _" [200,200,200,200,200])
  where
  "get_C_val ms \<sigma> t ms' \<sigma>' \<equiv> (\<exists> w ts'.
                                      w \<in> visible_writes \<sigma> t C \<and>
                                      w \<notin> covered \<sigma> \<and>
                                      valid_fresh_ts \<sigma> w ts' \<and>
              \<sigma>' = fst(FAAZ t w \<sigma> ts')
           \<and> ms' = ms \<lparr> s := (s ms) (t := Some (snd(FAAZ t w \<sigma> ts'))),
                       pc := (pc ms) (t := I9),
                     own\<^sub>R := (own\<^sub>R ms) ((snd(FAAZ t w \<sigma> ts')):=own\<^sub>R ms (snd(FAAZ t w \<sigma> ts')) \<union> {t})\<rparr>)" 

(*******   v=*s   **********)
definition get_s :: "mstate \<Rightarrow> surrey_state \<Rightarrow> T  \<Rightarrow> mstate \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ v:=*s _ _ _" [200,200,200,200,200])
  where
  "get_s ms \<sigma> t ms' \<sigma>' \<equiv>  (\<exists>z.  \<sigma> [z \<leftarrow> the (s ms t)]\<^sub>t \<sigma>'
                                      \<and> ms' = ms \<lparr> v := (v ms) (t := Some z),
                                                      own\<^sub>R := ( own\<^sub>R ms ) (z := own\<^sub>R ms z \<union> {t}),
                                                      pc := (pc ms) (t := I10)\<rparr>)" 


(*******   *n = v+1   **********) 
definition writeto_star_n :: "mstate \<Rightarrow> surrey_state \<Rightarrow> T  \<Rightarrow> mstate \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ *n:=newv _ _ _" [200,200,200,200,200])
  where
  "writeto_star_n ms \<sigma> t ms' \<sigma>' \<equiv>  \<sigma> [the(n ms t) := (the (v ms t) + 1)]\<^sub>t \<sigma>'
                                          \<and>  ms' = ms \<lparr>pc := (pc ms) (t := I11)\<rparr>"   







(********* free(pop(detached)) ******************)
definition pop_address :: "mstate \<Rightarrow> posem \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> bool" ("_ _ free[pop[detached[_]]] _ _" [200,200,200,200,200])    \<comment>\<open>pop(detached[tid-1])\<close>
  where
  "pop_address ms ps t ms' ps' \<equiv> (\<exists>i. (A ps i = Some (hd((det ms) t), variable) \<and>
                                       kill ps i ps')) \<and> 
                        ms' = ms\<lparr> det := (det ms) (t:= tl ((det ms) t)),
                                 own\<^sub>R := (own\<^sub>R ms) ((hd((det ms) t)):=(own\<^sub>R ms (hd((det ms) t))) - {t}),
                                 own\<^sub>W := (own\<^sub>W ms) ((hd((det ms) t)):=None),
                                  pc := (pc ms) (t := R4)\<rparr> "



(*******   r[i] = rcu[i]   **********)
definition load_rcu_to_r :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow>  T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ _ r[i]:=rcu[i] _ _ _ _" [200,200,200,200,200])
  where
  "load_rcu_to_r ms ps \<sigma> t ms' ps' \<sigma>' \<equiv> ps = ps' \<and> (\<exists>x y.  (A ps y = Some (rcu_0, pointer)) 
                                      \<and> \<sigma> [x \<leftarrow>(rcu_0 + (CTRsync\<^sub>1 ms t))]\<^sub>t \<sigma>'
                                      \<and> ms' = ms \<lparr> r := (r ms) (t := ((r ms) t) ((CTRsync\<^sub>1 ms t) :=x)),
                                                  pc := (pc ms) (t := S2) \<rparr>)"

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
                                            pc := (pc ms) (t := R2), 
                                             s_alloc := (s_alloc ms) (t := False)\<rparr>"


definition nondet :: "mstate \<Rightarrow> T \<Rightarrow> bool \<Rightarrow> mstate \<Rightarrow> bool" ("_ nondet[_,_] _" [200,200,200,200])    \<comment>\<open>nondet()\<close>
  where
  "nondet ms t b ms' \<equiv> ms' = ms \<lparr> nondet_val := (nondet_val ms) (t:= b),
                                          pc := (pc ms) (t := R3)\<rparr>"


definition rcu_temp_copy :: "mstate \<Rightarrow> surrey_state \<Rightarrow> nat \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ load(_)\<^sub>_ _ _" [200,200,200,200,200,200])
  where
  "rcu_temp_copy ms \<sigma> ctr_val t ms' \<sigma>'\<equiv> \<exists> v. ((\<sigma> [ v \<leftarrow> (rcu_0 + ctr_val)]\<^sub>t \<sigma>')     \<comment>\<open>read rcu[i]\<close>
                                        \<and> (ms' = ms\<lparr>reg := (reg ms) (t := v),
                                                    pc := (pc ms) (t := S7)\<rparr>)) "

definition cas_step_rcu :: "mstate \<Rightarrow> surrey_state \<Rightarrow>T \<Rightarrow> L \<Rightarrow> V \<Rightarrow> V \<Rightarrow> mstate \<Rightarrow>  surrey_state \<Rightarrow> bool" 
 where
    "cas_step_rcu ms \<sigma> t l cv nv ms' \<sigma>'\<equiv>           \<comment>\<open>CAS(&C,s,n)\<close>
       \<exists> w ts'. w \<in> visible_writes \<sigma> t l \<and>
               w \<notin> covered \<sigma> \<and>
               valid_fresh_ts \<sigma> w ts' \<and>
       \<sigma>' = fst(CAS t w cv nv \<sigma> ts')    
       \<and> 
(snd(CAS t w cv nv \<sigma> ts') = True \<longrightarrow>(ms' = ms\<lparr>CAS_succ := (CAS_succ ms) (t := snd(CAS t w cv nv \<sigma> ts')),
                                                  own\<^sub>W := (own\<^sub>W ms) (cv:=Some t),        \<comment>\<open>acquire wr_cap on location\<close>
                                                  own\<^sub>W := (own\<^sub>W ms) (nv:=None),          \<comment>\<open>let go of wr_cap on location\<close>
                                                   pc := (pc ms) (t := cas_res)\<rparr>))
       \<and> 
(snd(CAS t w cv nv \<sigma> ts') = False \<longrightarrow>(ms' = ms\<lparr>CAS_succ := (CAS_succ ms) (t := snd(CAS t w cv nv \<sigma> ts')),
                                                   pc := (pc ms) (t := cas_res)\<rparr>))"           






definition inc_ctr1 :: "T \<Rightarrow> mstate \<Rightarrow> mstate" ( "CTRsync\<^sub>1[_]++" [200])
  where
  "inc_ctr1 t ms \<equiv>  ms \<lparr> CTRsync\<^sub>1 := (CTRsync\<^sub>1 ms) (t:=(CTRsync\<^sub>1 ms t)+1) \<rparr> "

definition inc_ctr2 :: "T \<Rightarrow> mstate \<Rightarrow> mstate" ( "CTRsync\<^sub>2[_]++" [200])
  where
  "inc_ctr2 t ms \<equiv>  ms \<lparr> CTRsync\<^sub>2 := (CTRsync\<^sub>2 ms) (t:=(CTRsync\<^sub>2 ms t)+1) \<rparr> "

definition update_ctr1 :: "T \<Rightarrow> nat \<Rightarrow> mstate \<Rightarrow> mstate" ( "CTRsync\<^sub>1[_]:=_" [200,200])
  where
  "update_ctr1 t ctr_val ms \<equiv> ms \<lparr> CTRsync\<^sub>1 := (CTRsync\<^sub>1 ms) (t:=ctr_val) \<rparr> "

definition update_ctr2 :: "T \<Rightarrow> nat \<Rightarrow> mstate \<Rightarrow> mstate" ( "CTRsync\<^sub>2[_]:=_" [200,200])
  where
  "update_ctr2 t ctr_val ms \<equiv> ms \<lparr> CTRsync\<^sub>2 := (CTRsync\<^sub>2 ms) (t:=ctr_val) \<rparr> "

definition update_pc :: "T \<Rightarrow> PC \<Rightarrow> mstate \<Rightarrow>  mstate" ( "pc[_]:=_" [200,200])
  where
  "update_pc t pc_val ms \<equiv>  ms \<lparr> pc := (pc ms) (t:=pc_val) \<rparr> "

definition repetition :: "T \<Rightarrow> bool \<Rightarrow> mstate \<Rightarrow>  mstate" ( "repeat[_]:=_" [200,200])
  where
  "repetition t b ms \<equiv>  ms \<lparr> repeat := (repeat ms) (t:=b) \<rparr> "

definition nallocdef :: "T \<Rightarrow> bool \<Rightarrow> mstate \<Rightarrow> mstate" ( "n[_]:=_" [200,200])
  where
  "nallocdef t b ms \<equiv>  ms \<lparr> n_alloc := (n_alloc ms) (t:=b) \<rparr> "

definition sallocdef :: "T \<Rightarrow> bool \<Rightarrow> mstate \<Rightarrow> mstate" ( "s[_]:=_" [200,200])
  where
  "sallocdef t b ms \<equiv>  ms \<lparr> s_alloc := (s_alloc ms) (t:=b) \<rparr> "

definition SC_fence :: "surrey_state \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool " ("_ Fence _ _" [200,200,200])
  where
  "SC_fence \<sigma> t \<sigma>' \<equiv> 
       \<exists> w ts'. w \<in> visible_writes \<sigma> t casloc \<and>
               w \<notin> covered \<sigma> \<and>
               valid_fresh_ts \<sigma> w ts' \<and>
       \<sigma>' = fst(CAS t w (value \<sigma> w) (value \<sigma> w) \<sigma> ts')"





lemmas abbr = v_allocation_def int_star_n_def int_star_s_def
                new_int_def get_C_val_def get_s_def writeto_star_n_def
                pop_address_def
                load_rcu_to_r_def 
                enter_rcu_def exit_rcu_def
                setup_r_def
                insert_address_def nondet_def
                rcu_temp_copy_def cas_step_rcu_def
                inc_ctr1_def inc_ctr2_def update_ctr1_def update_ctr2_def update_pc_def
                repetition_def SC_fence_def
                sallocdef_def nallocdef_def
                giveup_readandwrite_ownership_def



(*==========================   Thread behaviour   =================================*)

section \<open>Program step\<close>
definition step :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow>  PC \<Rightarrow> T \<Rightarrow>  mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool " where
"step ms ps \<sigma> pcr t ms' ps' \<sigma>' \<equiv> 
case pcr of 
   R1 \<Rightarrow> (ms insert[detached[t],the (s ms t)] ms') \<and> ps = ps' \<and> \<sigma> =\<sigma>' 
|  R2 \<Rightarrow> (\<exists>b. (b\<in>{True,False} \<and> (ms nondet[t,b] ms'))) \<and> ps = ps' \<and> \<sigma> =\<sigma>' 
|  R3 \<Rightarrow> if (nondet_val ms t) = True 
            then ms' = (pc[t]:=S1) ms  \<and> ps = ps' \<and> \<sigma> =\<sigma>'  
               \<comment>\<open> sync() \<close>
            else ms' = (pc[t]:=I13) ms  \<and> ps = ps' \<and> \<sigma> =\<sigma>'  
               \<comment>\<open> return to inc() \<close>
|  R4 \<Rightarrow> if (det ms t \<noteq> [])
            then ms' = (pc[t]:=R5)  ms  \<and> ps = ps' \<and> \<sigma> =\<sigma>'  
            else ms' = (pc[t]:=I13) ms  \<and> ps = ps' \<and> \<sigma> =\<sigma>'     \<comment>\<open> return to inc() \<close>
|  R5 \<Rightarrow> (ms ps free[pop[detached[t]]] ms' ps')  \<and> \<sigma> =\<sigma>'                  \<comment>\<open> ownW ps hd(det ps t) := None \<close>

|  S1 \<Rightarrow> (ms r[N]:={0} t ms) \<and> ps = ps'  \<and> \<sigma> = \<sigma>'
|  S2 \<Rightarrow> if (CTRsync\<^sub>1 ms t < T_max)
            then ms' = (CTRsync\<^sub>1[t]++ \<circ> pc[t]:=S3) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
            else ms' = (pc[t]:=S4) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
|  S3 \<Rightarrow> (ms ps \<sigma> r[i]:=rcu[i] t ms' ps' \<sigma>')
|  S4 \<Rightarrow> if (CTRsync\<^sub>2 ms t < T_max)
            then ms' = (pc[t]:=S5) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
            else ms' = (pc[t]:=R4) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'        \<comment>\<open> return to Reclaim (R4)\<close>
|  S5 \<Rightarrow> if r ms t (CTRsync\<^sub>2 ms t) = 0
            then ms' = (CTRsync\<^sub>2[t]++ \<circ> pc[t]:=S4) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
            else ms' = (pc[t]:=S6) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
|  S6 \<Rightarrow> ms \<sigma> load(CTRsync\<^sub>2 ms t)\<^sub>t ms' \<sigma>' \<and> ps = ps'  \<comment>\<open> load \<langle>rcu[i]\<rangle> into reg, increment pc\<close>
|  S7 \<Rightarrow> if reg ms t = 1                             \<comment>\<open> test while \<langle>rcu[i]\<rangle>\<close>
            then ms' = (pc[t]:=S6) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
            else ms' = (CTRsync\<^sub>2[t]++ \<circ> pc[t]:=S4) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'


|  I1  \<Rightarrow> (ms int[v\<^sub>t] ms')  \<and> ps = ps' \<and> \<sigma> = \<sigma>'
|  I2  \<Rightarrow> (ms int[*n\<^sub>t] ms') \<and> ps = ps' \<and> \<sigma> = \<sigma>'
|  I3  \<Rightarrow> (ms int[*s\<^sub>t] ms') \<and> ps = ps' \<and> \<sigma> = \<sigma>'
|  I4  \<Rightarrow> (ms ps n:=newint t ms' ps')  \<and> \<sigma> = \<sigma>'                                           \<comment>\<open> takes raw cap on n\<close>
|  I5  \<Rightarrow> (ps \<sigma> rcuenter[] t ps' \<sigma>') \<and> (ms' = (pc[t]:=I6) ms)
|  I6  \<Rightarrow> (ps \<sigma> rcuexit[] t ps' \<sigma>')  \<and> (ms' = (pc[t]:=I7 \<circ> givesupRown[t,the (s ms t)]) ms)   \<comment>\<open> lets go of raw cap on s\<close>
|  I7  \<Rightarrow> (ps \<sigma> rcuenter[] t ps' \<sigma>') \<and> (ms' = (pc[t]:=I8) ms)
\<comment>\<open>|  fence \<Rightarrow>  (\<sigma> Fence t \<sigma>') \<and> ps = ps' \<and> (ms' = (pc[t]:=I8) ms)   SC fence \<close> 
|  I8  \<Rightarrow> (ms \<sigma> s:=\<^sup>FC t ms' \<sigma>')       \<and> ps = ps'          \<comment>\<open> Fetch and Add 0 \<close>            \<comment>\<open> takes r cap on s (C weak read)\<close>
|  I9  \<Rightarrow> (ms \<sigma> v:=*s t ms' \<sigma>')      \<and> ps = ps'     
|  I10 \<Rightarrow> (ms \<sigma> *n:=newv t ms' \<sigma>')   \<and> ps = ps'                  \<comment>\<open> (ownW ps n) = t \<close>
|  I11 \<Rightarrow> cas_step_rcu ms \<sigma> t C (the (s ms t)) (the (n ms t)) ms' \<sigma>' \<and> ps = ps'           \<comment>\<open> swaps wr cap from n to s\<close>
|  cas_res \<Rightarrow> if CAS_succ ms t 
            then (ms' = (pc[t]:=I12) ms)
            else (ms' = (pc[t]:=I6 \<circ> repeat[t]:=True) ms)
|  I12 \<Rightarrow> (ps \<sigma> rcuexit[] t ps' \<sigma>') \<and> (ms' = ((pc[t]:=R1 \<circ> n[t]:=False \<circ> givesupRown[t,the (n ms t)])) ms)  \<comment>\<open> lets go of raw cap on n\<close>
        \<comment>\<open>reclaim(s)\<close>                                            \<comment>\<open> (ownW ps s) = t \<close>            \<comment>\<open> lets go of raw cap on s\<close>
|  I13 \<Rightarrow> (ms' = (pc[t]:=I14) ms) \<and> \<sigma> = \<sigma>' \<and> ps = ps'   
|  I14 \<Rightarrow> ms' = (repeat[t]:=False) ms \<and> \<sigma> = \<sigma>' \<and> ps = ps'  \<comment>\<open> return(v) \<close> 
| finished \<Rightarrow> ms = ms' \<and> ps=ps' \<and> \<sigma>=\<sigma>'
" 




(*------- todo ----------
  r :: "T \<Rightarrow> nat \<Rightarrow> nat"          
  det :: "T \<Rightarrow> L list"        
-------------------------*)



definition "Rcap ms t addrs \<equiv> \<forall>i. (i\<in>addrs) \<longleftrightarrow> (t\<in>own\<^sub>R ms i)"
definition "Wcap ms t addrs \<equiv> \<forall>i. (i\<in>addrs) \<longleftrightarrow> (the(own\<^sub>W ms i)=t)"

definition "inlist a lst \<equiv> \<exists>j.(j<length(lst) \<and> lst!j = a)"
definition "detaddrs ms t \<equiv> {i. inlist i (det ms t)}"
definition "n_pointer ms t\<equiv> the(n ms t)"
definition "s_pointer ms t\<equiv> the(s ms t)"
definition "s_and_n ms t \<equiv> {n_pointer ms t,s_pointer ms t}"
definition "just_n ms t \<equiv> {n_pointer ms t}"
definition "just_s ms t \<equiv> {s_pointer ms t}"

lemmas names [simp] = n_pointer_def s_pointer_def s_and_n_def just_n_def just_s_def
                      inlist_def detaddrs_def
lemmas names_2      = Rcap_def Wcap_def


(*------------structure lemmas---------------*)

definition "addr_allocated ms ps \<equiv> \<forall>addr t . addr \<in> detaddrs ms t \<longrightarrow> 
                                 (\<exists>prov. (A ps prov = Some (addr, pointer)))"

definition "nptr_true_imp ms ps \<equiv> \<forall>t . (n_alloc ms t = True \<and> n ms t\<noteq>None) \<longrightarrow>
                          (\<exists>prov. (A ps prov = Some (the (n ms t), pointer)))"

definition "sptr_true_imp ms ps \<equiv> \<forall>t . (s_alloc ms t = True \<and> s ms t\<noteq>None) \<longrightarrow>
                          (\<exists>prov. (A ps prov = Some (the (s ms t), pointer)))"


(*------- careful observation of preCond per thread ----------*)
definition "pre_I1 ms t \<equiv>
                         Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(* s ms t = None
                        \<and> n ms t = None 
                        \<and> v ms t = None
                        \<and> s ms t = False 
                        \<and> n ms t = False 
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = False \<and> repeat ms t = False
                        \<and> *)
definition "pre_I2 ms t \<equiv>
                          Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(*s ms t = None 
                        \<and> n ms t = None 
                        \<and> v ms t = None
                        \<and> s ms t = False 
                        \<and> n ms t = False 
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = False \<and> repeat ms t = False
                        \<and> *)
definition "pre_I3 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(*s ms t = None 
                        \<and> n ms t = None 
                        \<and> v ms t = None
                        \<and> s ms t = False
                        \<and> n ms t = True 
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = False \<and> repeat ms t = False
                        \<and>*)
definition "pre_I4 ms t \<equiv>
                          Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(*s ms t = None
                        \<and> n ms t = None
                        \<and> v ms t = None
                        \<and> s ms t = True
                        \<and> n ms t = True
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = False \<and> repeat ms t = False
                        \<and> *)
definition "pre_I5 ms t \<equiv>
                           Rcap ms t (detaddrs ms t \<union> just_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)"
(*s ms t = None
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> v ms t = None
                        \<and> s ms t = True
                        \<and> n ms t = True
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = False \<and> repeat ms t = False
                        \<and>*)
definition "pre_I6 ms t \<equiv>
                           Wcap ms t (detaddrs ms t \<union> just_n ms t)"
(*(repeat ms t  \<longrightarrow> (\<exists>j k. s ms t = Some j \<and> v ms t = Some k)
                                          \<and> Rcap ms t (detaddrs ms t \<union> s_and_n ms t))
                        \<and> (\<not>repeat ms t \<longrightarrow> s ms t = None \<and> v ms t = None
                                          \<and> Rcap ms t (detaddrs ms t \<union> just_n ms t))
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> s ms t = True
                        \<and> n ms t = True
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = False 
                        \<and>*)
definition "pre_I7 ms t \<equiv>
                          Rcap ms t (detaddrs ms t \<union> just_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)"
(*(\<not>repeat ms t \<longrightarrow> s ms t = None \<and> v ms t = None)
                        \<and> (repeat ms t \<longrightarrow> (\<exists>j k. s ms t = Some j \<and> v ms t = Some k))
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> s ms t = True
                        \<and> n ms t = True
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = False 
                        \<and> *)
definition "pre_I8 ms t \<equiv> 
                           Rcap ms t (detaddrs ms t \<union> just_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)"
(*(\<not>repeat ms t \<longrightarrow> s ms t = None \<and> v ms t = None)
                        \<and> (repeat ms t \<longrightarrow> (\<exists>j k. s ms t = Some j \<and> v ms t = Some k))
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> s ms t = True
                        \<and> n ms t = True
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = False
                        \<and>*)
definition "pre_I9 ms t \<equiv> 
                           Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)"
(*(\<not>repeat ms t \<longrightarrow>  v ms t = None)
                        \<and> (repeat ms t \<longrightarrow> (\<exists>k. v ms t = Some k))
                        \<and> (\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> s ms t = True
                        \<and> n ms t = True
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = False 
                        \<and>*)
definition "pre_I10 ms t \<equiv>
                           Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = True
                        \<and> n ms t = True
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = False
                        \<and>*)
definition "pre_I11 ms t \<equiv>
                          Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = True
                        \<and> n ms t = True
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = False
                        \<and> *)
definition "pre_cas_res ms t \<equiv>
                          (CAS_succ ms t \<longrightarrow> Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_s ms t))
                        \<and> (\<not>CAS_succ ms t\<longrightarrow> Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t))"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = True
                        \<and> n ms t = True
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False 
                        \<and> *)
definition "pre_I12 ms t \<equiv>
                           Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_s ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = True
                        \<and> n ms t = True
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = True
                        \<and>*)
\<comment>\<open> start to reclaim() \<close>
definition "pre_I13 ms t \<equiv>
                          Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = False
                        \<and> n ms t = False
                        \<and> CTRsync\<^sub>1 ms t = T_max \<and> CTRsync\<^sub>2 ms t = T_max
                        \<and> res ms t = 0 
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = True
                        \<and> *)
definition "pre_I14 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = False
                        \<and> n ms t = False
                        \<and> CTRsync\<^sub>1 ms t = T_max \<and> CTRsync\<^sub>2 ms t = T_max
                        \<and> res ms t = 0 
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = True
                        \<and>*)


definition "pre_R1 ms t \<equiv>  
                           Rcap ms t (detaddrs ms t \<union> just_s ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_s ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = True
                        \<and> n ms t = False
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = True
                        \<and>*)
definition "pre_R2 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = False
                        \<and> n ms t = False
                        \<and> just_s ms t \<in> {detaddrs ms t}         \<comment> \<open>s union detatched addresses\<close>
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = True
                        \<and>*)
definition "pre_R3 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = False
                        \<and> n ms t = False
                        \<and> just_s ms t \<in> {detaddrs ms t}         \<comment> \<open>s union detatched addresses\<close>
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> CAS_succ ms t = True                  \<comment> \<open>random nondet_val picked\<close>
                        \<and>*)
\<comment>\<open> start to sync() \<close>
\<comment>\<open> or return to inc() \<close>
definition "pre_R4 ms t \<equiv>  
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = False
                        \<and> n ms t = False
                        \<and> CTRsync\<^sub>1 ms t = T_max \<and> CTRsync\<^sub>2 ms t = T_max 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = True \<and> CAS_succ ms t = True                  \<comment> \<open>random nondet_val picked\<close>
                        \<and>*)
\<comment>\<open> return to inc() \<close>
definition "pre_R5 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = False
                        \<and> n ms t = False
                        \<and> det ms t \<noteq> []
                        \<and> CTRsync\<^sub>1 ms t = T_max \<and> CTRsync\<^sub>2 ms t = T_max 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = True \<and> CAS_succ ms t = True                  \<comment> \<open>random nondet_val picked\<close>
                        \<and>*)


definition "pre_S1 ms t \<equiv>  
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = False
                        \<and> n ms t = False
                        \<and> just_s ms t \<in> {detaddrs ms t}         \<comment> \<open>s union detatched addresses\<close>
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = True \<and> CAS_succ ms t = True 
                        \<and>*)
definition "pre_S2 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = False
                        \<and> n ms t = False
                        \<and> just_s ms t \<in> {detaddrs ms t}         \<comment> \<open>s union detatched addresses\<close>
                        \<and> CTRsync\<^sub>1 ms t \<le> T_max \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = True \<and> CAS_succ ms t = True 
                        \<and> (\<forall>i. (i>CTRsync\<^sub>1 ms t \<and> i\<le>T_max) \<longrightarrow> r ms t i = 0)        \<comment> \<open>local rcu register\<close>
                        \<and>*)
definition "pre_S3 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = False
                        \<and> n ms t = False
                        \<and> just_s ms t \<in> {detaddrs ms t}         \<comment> \<open>s union detatched addresses\<close>
                        \<and> CTRsync\<^sub>1 ms t \<le> T_max \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = True \<and> CAS_succ ms t = True 
                        \<and> (\<forall>i. (i\<ge>CTRsync\<^sub>1 ms t \<and> i\<le>T_max) \<longrightarrow> r ms t i = 0)        \<comment> \<open>local rcu register\<close>
                        \<and>*)
definition "pre_S4 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = False
                        \<and> n ms t = False
                        \<and> just_s ms t \<in> {detaddrs ms t}         \<comment> \<open>s union detatched addresses\<close>
                        \<and> CTRsync\<^sub>1 ms t = T_max \<and> CTRsync\<^sub>2 ms t \<le> T_max 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = True \<and> CAS_succ ms t = True 
                        \<and> (\<forall>i. (i\<ge>CTRsync\<^sub>1 ms t \<and> i\<le>T_max) \<longrightarrow> r ms t i = 0)        \<comment> \<open>careful, here is smth to do with observations in wm\<close>
                        \<and>*)
definition "pre_S5 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = False
                        \<and> n ms t = False
                        \<and> just_s ms t \<in> {detaddrs ms t}         \<comment> \<open>s union detatched addresses\<close>
                        \<and> CTRsync\<^sub>1 ms t = T_max \<and> CTRsync\<^sub>2 ms t \<le> T_max 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = True \<and> CAS_succ ms t = True 
                        \<and> (\<forall>i. (i\<ge>CTRsync\<^sub>1 ms t \<and> i\<le>T_max) \<longrightarrow> r ms t i = 0)        \<comment> \<open>careful, here is smth to do with observations in wm\<close>
                        \<and>*)
definition "pre_S6 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = False
                        \<and> n ms t = False
                        \<and> just_s ms t \<in> {detaddrs ms t}         \<comment> \<open>s union detatched addresses\<close>
                        \<and> CTRsync\<^sub>1 ms t = T_max \<and> CTRsync\<^sub>2 ms t \<le> T_max 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = True \<and> CAS_succ ms t = True 
                        \<and> (\<forall>i. (i\<ge>CTRsync\<^sub>1 ms t \<and> i\<le>T_max) \<longrightarrow> r ms t i = 0)        \<comment> \<open>careful, here is smth to do with observations in wm\<close>
                        \<and> r ms t (CTRsync\<^sub>2 ms t) = 1
                        \<and>*)
definition "pre_S7 ms t \<equiv>
                          Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)"
(*(\<exists>j. s ms t = Some j)
                        \<and> (\<exists>i. n ms t = Some i)
                        \<and> (\<exists>k. v ms t = Some k)
                        \<and> s ms t = False
                        \<and> n ms t = False
                        \<and> just_s ms t \<in> {detaddrs ms t}         \<comment> \<open>s union detatched addresses\<close>
                        \<and> CTRsync\<^sub>1 ms t = T_max \<and> CTRsync\<^sub>2 ms t \<le> T_max 
                        \<and> res ms t = 0 
                        \<and> (reg ms t = 0 \<or> reg ms t = 1) \<comment> \<open>this is basically TRUE/FALSE\<close>
                        \<and> nondet_val ms t = True \<and> CAS_succ ms t = True 
                        \<and> (\<forall>i. (i\<ge>CTRsync\<^sub>1 ms t \<and> i\<le>T_max) \<longrightarrow> r ms t i = 0)        \<comment> \<open>careful, here is smth to do with observations in wm\<close>
                        \<and> r ms t (CTRsync\<^sub>2 ms t) = 1
                        \<and> *)




definition preCond :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> PC \<Rightarrow> T \<Rightarrow> bool" where
"preCond ms ps \<sigma> pcr t \<equiv> 
case pcr of
   I1 \<Rightarrow> pre_I1 ms t
|  I2 \<Rightarrow> pre_I2 ms t
|  I3 \<Rightarrow> pre_I3 ms t
|  I4 \<Rightarrow> pre_I4 ms t
|  I5 \<Rightarrow> pre_I5 ms t
|  I6 \<Rightarrow> pre_I6 ms t
|  I7 \<Rightarrow> pre_I7 ms t
\<comment>\<open>|  fence \<Rightarrow> pre_fence ms t\<close>
|  I8 \<Rightarrow> pre_I8 ms t
|  I9 \<Rightarrow> pre_I9 ms t
|  I10 \<Rightarrow> pre_I10 ms t
|  I11 \<Rightarrow> pre_I11 ms t
|  cas_res \<Rightarrow> pre_cas_res ms t
|  I12 \<Rightarrow> pre_I12 ms t
|  I13 \<Rightarrow> pre_I13 ms t
|  I14 \<Rightarrow> pre_I14 ms t
|  finished \<Rightarrow> True

|  R1 \<Rightarrow> pre_R1 ms t
|  R2 \<Rightarrow> pre_R2 ms t
|  R3 \<Rightarrow> pre_R3 ms t
|  R4 \<Rightarrow> pre_R4 ms t
|  R5 \<Rightarrow> pre_R5 ms t

|  S1 \<Rightarrow> pre_S1 ms t
|  S2 \<Rightarrow> pre_S2 ms t
|  S3 \<Rightarrow> pre_S3 ms t
|  S4 \<Rightarrow> pre_S4 ms t
|  S5 \<Rightarrow> pre_S5 ms t
|  S6 \<Rightarrow> pre_S6 ms t
|  S7 \<Rightarrow> pre_S7 ms t

"

lemmas pre_conds [simp] = pre_I1_def pre_I2_def pre_I3_def pre_I4_def pre_I5_def
                   pre_I6_def pre_I7_def pre_I8_def pre_I9_def pre_I10_def
                   pre_I11_def pre_I12_def pre_I13_def pre_I14_def 
                   pre_cas_res_def 
                   pre_R1_def pre_R2_def pre_R3_def pre_R4_def pre_R5_def
                   pre_S1_def pre_S2_def pre_S3_def pre_S4_def pre_S5_def 
                   pre_S6_def pre_S7_def 




(*
@I5 .. I11 \<forall>t'. t \<noteq> t' \<longrightarrow> t'\<notin>ownR ps n
*)

definition "init ms ps \<equiv>  (\<forall>t. (t<T_max)\<longrightarrow> pc ms t = I1
                         \<and> n_alloc ms t = False
                         \<and> s_alloc ms t = False
                         \<and> v ms t = None
                         \<and> n ms t = None
                         \<and> s ms t = None
                         \<and> det ms t = []
                         \<and> CTRsync\<^sub>1 ms t = 0
                         \<and> CTRsync\<^sub>2 ms t = 0
                         \<and> res ms t = 0
                         \<and> reg ms t = 0
                         \<and> nondet_val ms t = False
                         \<and> CAS_succ ms t = False
                         \<and> repeat ms t = False)
                         \<and> (\<forall>t k. (t<T_max \<and> k<T_max) \<longrightarrow> 
                                          r ms t k = 0)
        \<and> (\<forall>i. (i\<ge>0) \<longrightarrow> A ps i = None \<and> own\<^sub>R ms i = {} \<and> own\<^sub>W ms i = None)
        \<and> alloc_addrs ps = {}"

(* Global invariant = some general properties + what do we want to guarantee?*)

(* Preconditions (local invariant) = pc = ... \<longrightarrow> P *)


(* old main invariant version
definition "main_invariant_1 ms \<equiv> \<forall>k t t'. ( k<length (det ms t) \<and> t'\<noteq>t \<and> t'<CTRsync\<^sub>1 ms t \<and> (r ms t t') = 0)
                                           \<longrightarrow> t' \<notin> own\<^sub>R ms ((det ms t) ! k)"

definition "main_invariant_2 ms \<equiv> \<forall>k t t'. ( k<length (det ms t) \<and> t'\<noteq>t \<and> t'<CTRsync\<^sub>2 ms t)
                                           \<longrightarrow> t' \<notin> own\<^sub>R ms ((det ms t) ! k)"

definition "main_invariant_3 ms \<sigma> \<equiv> \<forall>k t t'. ( k<length (det ms t) \<and> t'\<noteq>t \<and> CTRsync\<^sub>2 ms t < T_max 
                                                 \<and> t'=CTRsync\<^sub>2 ms t \<and> [(rcu_0+t') \<approx>\<^sub>t 0] \<sigma>)
                                           \<longrightarrow> t' \<notin> own\<^sub>R ms ((det ms t) ! k)"
*)

(* Main Invariant *)
definition "main_inv ms \<equiv>\<forall>t. (t\<le>T_max \<and> n_alloc ms t = True
                                         \<and> n ms t \<noteq> None)\<longrightarrow>
                                    own\<^sub>R ms (the (n ms t)) = {t}"

lemmas new_main_inv [simp] = main_inv_def

(*supporting structure invariants*)
definition "allocated_s_addr ms ps \<equiv> \<forall>t. (t\<le>T_max \<and> (s ms t)\<noteq>None)\<longrightarrow> \<not>(isfree_addr (the(s ms t)) ps)"
definition "allocated_n_addr ms ps \<equiv> \<forall>t. (t\<le>T_max \<and> (n ms t)\<noteq>None)\<longrightarrow> \<not>(isfree_addr (the(n ms t)) ps)"
definition "s_differs_from_n ms \<equiv> \<forall>t. (t\<le>T_max \<and> (s ms t)\<noteq>None \<and> (n ms t)\<noteq>None) \<longrightarrow> the(s ms t) \<noteq> the(n ms t)"
definition "st_differs_from_sta ms\<equiv> \<forall>t t'. (t\<le>T_max \<and> t'\<le>T_max \<and> (s ms t)\<noteq>None \<and> (s ms t')\<noteq>None) 
                                \<longrightarrow> the(s ms t) \<noteq> the(s ms t')"
definition "nt_differs_from_nta ms \<equiv> \<forall>t t'. (t\<le>T_max \<and> t'\<le>T_max \<and> (n ms t)\<noteq>None \<and> (n ms t')\<noteq>None) 
                                \<longrightarrow> the(n ms t) \<noteq> the(n ms t')"   
definition "nt_differs_from_sta ms \<equiv> \<forall>t t'. (t\<le>T_max \<and> t'\<le>T_max \<and> (n ms t)\<noteq>None \<and> (s ms t')\<noteq>None) 
                                \<longrightarrow> the(n ms t) \<noteq> the(s ms t')"
definition "st_differs_from_nta ms \<equiv> \<forall>t t'. (t\<le>T_max \<and> t'\<le>T_max \<and> (s ms t)\<noteq>None \<and> (n ms t')\<noteq>None) 
                                \<longrightarrow> the(s ms t) \<noteq> the(n ms t')"  
definition "st_differs_from_detall ms\<equiv> \<forall>t ta. t\<le>T_max\<and>ta\<le>T_max\<and>s_alloc ms t \<longrightarrow> the(s ms t) \<notin> (detaddrs ms ta)"
definition "nt_differs_from_detall ms\<equiv> \<forall>t ta. t\<le>T_max\<and>ta\<le>T_max\<and>n_alloc ms t \<longrightarrow> the(n ms t) \<notin> (detaddrs ms ta)"

definition "unique_allocs ms ps \<equiv> s_differs_from_n ms \<and> st_differs_from_sta ms \<and> nt_differs_from_nta ms
                              \<and> nt_differs_from_sta ms \<and> st_differs_from_nta ms
                              \<and> st_differs_from_detall ms \<and> nt_differs_from_detall ms"

lemma differences:
  assumes "s ms 0 = Some 5"
  and "s ms 1 = Some 4" 
  and "T_max = 1"
shows "the(s ms 0) \<noteq> the(s ms 1)"
  using assms by(simp add:st_differs_from_sta_def)


lemmas allocated [simp] = allocated_n_addr_def
                          s_differs_from_n_def 
                          st_differs_from_sta_def
                          nt_differs_from_nta_def
                          nt_differs_from_sta_def
                          st_differs_from_nta_def
                          st_differs_from_detall_def
                          nt_differs_from_detall_def
                          unique_allocs_def


lemma main_invariant_Correctness:
  assumes "preCond ms ps \<sigma> pcr t"
  and "main_inv ms"
  and "pcr = pc ms t"
  and "step ms ps \<sigma> pcr t ms' ps' \<sigma>'"
  and "allocated_n_addr ms ps "
  and "unique_allocs ms ps"
  and "pcr' = pc ms' t"
  and "pcr \<notin> {I8, I9, I10, I11, cas_res}"
shows "main_inv ms'"
  using assms apply (simp add:preCond_def step_def)
  apply(case_tac[!] "pc ms t", simp_all add:abbr) 
  defer 
  apply metis 
  apply metis apply(subgoal_tac "\<not>n_alloc ms t") apply(simp add:names_2) 
  apply(elim conjE impE exE) 
  apply(subgoal_tac "\<not>n_alloc ms t") prefer 2
  apply force
  apply(subgoal_tac "\<forall>t. t \<le> T_max \<and> n_alloc ms t \<and> (\<exists>y. n ms t = Some y) \<longrightarrow>
             own\<^sub>R ms (the (n ms t)) = {t}") prefer 2 
  apply blast
  apply(subgoal_tac "\<forall>t. t\<noteq>t'

              defer

  
  
  
  
  sorry




lemma from_int_to_I1:
  assumes "init ms ps"
  and "wfs \<sigma>"
  and "step ms ps \<sigma> I1 1 ms' ps' \<sigma>'"
shows "pc ms' 1 = I2"
  using assms apply(simp add:step_def init_def)
  by(simp add:v_allocation_def)

lemma check1:
  assumes "preCond ms ps \<sigma> pcr t"
  and "init ms ps"
  and "t=1"
  shows "Rcap ms t {}"
  using preCond_def Rcap_def assms init_def
  apply simp
  apply(case_tac "pcr", simp_all add:init_def)
  by (simp_all add: Rcap_def)

lemma check2:
  assumes "preCond ms ps \<sigma> pcr t"
  and "init ms ps"
  and "t=1"
  shows "\<nexists>i.(t\<in>own\<^sub>R ms i) "
  using assms check1 [where ms=ms and ps=ps and \<sigma>=\<sigma> and pcr=pcr and t=t] 
  using Rcap_def by auto

lemma check3:
  assumes "preCond ms ps \<sigma> pcr t"
  and "pcr = I14"
  and "det ms t=[]"
shows "\<nexists>i.(t\<in>own\<^sub>R ms i) "
  using assms preCond_def
  apply simp apply (cases "pcr", simp_all)
  by (simp add: Rcap_def)
  
lemma check4:
  assumes "preCond ms ps \<sigma> pcr t"
  and "pcr = I14"
  and "det ms t=[]"
shows "\<nexists>i.(the(own\<^sub>W ms i) = t) "
  using assms preCond_def
  apply simp apply (cases "pcr", simp_all)
  by (simp add: Wcap_def)

lemma check5:
  assumes "preCond ms ps \<sigma> pcr t"
  and "pcr = I14"
  and "det ms t\<noteq>[]"
  and "(the(own\<^sub>W ms i) = t)"
shows "\<exists>a. (det ms t ! a) = i "
  using assms preCond_def
  apply simp apply (cases "pcr", simp_all add:Wcap_def)
  apply clarify 
  by blast
          
(*
OWNERSHIP IDEAS:


\<forall>i. (i\<in>addrs) \<longleftrightarrow> (the(own\<^sub>W ms i)=t)


We have to get to this stage after sync():
\<forall>s i j. (s\<in>det\<^sub>i \<and> i\<noteq>j) \<longrightarrow> T\<^sub>j \<notin> own\<^sub>R(s)

because:
 T\<^sub>j \<notin> own\<^sub>R(s) \<longrightarrow> T\<^sub>j \<noteq> own\<^sub>W(s)

This allows for pop() operation to guarantee that no thread could allocate n:=newint as n:=s
unless:

own\<^sub>W(s) = T\<^sub>i \<and> own\<^sub>R(s) = { T\<^sub>i }
pop()
own\<^sub>W(s) = None \<and> own\<^sub>R(s) = {}


(Call threads t, t...)

This is absolutely guaranteed if sync() occurs deterministically:
\<forall>j. j<N \<longrightarrow> |det\<^sub>j| \<le> 1
\<forall>s j i. (s\<in>det\<^sub>j \<and> i\<noteq>j \<and> i<CTRsync\<^sub>1(j) \<and> r[i] = 0) \<longrightarrow> T\<^sub>i \<notin> own\<^sub>R(s)     (backward sync)
\<forall>s j i. (s\<in>det\<^sub>j \<and> i\<noteq>j \<and> i<CTRsync\<^sub>2(j)) \<longrightarrow> T\<^sub>i \<notin> own\<^sub>R(s)                (backward sync)
\<forall>s j i. (s\<in>det\<^sub>j \<and> i\<noteq>j \<and> CTRsync\<^sub>2(j) < N \<and> i = CTRsync\<^sub>2(j) \<and> [rcu[i] \<approx> 0]\<^sub>j) \<longrightarrow> T\<^sub>i \<notin> own\<^sub>R(s)                (backward sync)
No thread i. (j\<noteq>i) can allocate n:=newint to have address s, since own\<^sub>W(s) = T\<^sub>j
If a thread i attemps to read s=C while in rcu[i] (weak memory), this can only happen if:
CTRsync\<^sub>1 = N \<and> r[i] = 1 \<and> i\<ge>CTRsync\<^sub>2
In that case, it should be impossible for CAS\<^sub>j to succeed, resulting in eventual rcu_exit() by j with no swap,
(no matter how many times j performs rcu_enter()/rcu_exit()       ***careful in WM setting - fence*** )
which should cause {while rcu[j]} to terminate and perform CTRsync\<^sub>2++

Nondeterministically:
\<forall>j. j<N \<longrightarrow> |det\<^sub>j| \<ge> 0
\<forall>s j i. (s\<in>det\<^sub>j \<and> i\<noteq>j \<and> i<CTRsync\<^sub>2) \<longrightarrow> T\<^sub>i \<notin> own\<^sub>R(s)                (backward sync)
\<forall>s j i. (s\<in>det\<^sub>j \<and> i\<noteq>j \<and> i<CTRsync\<^sub>1 \<and> r[i] = 0) \<longrightarrow> T\<^sub>i \<notin> own\<^sub>R(s)     (backward sync)

only requirement is that own\<^sub>W(s) = T\<^sub>j to limit allocation of n:=newint to s by T\<^sub>i
T\<^sub>j faces the same problem, since n:=newint, where newint=s, requires own\<^sub>W(s) = Null.



REASONS FOR OWNERSHIP OVER NO-OWNERSHIP:
limited in Deterministic setting.
no requirement of insert(det\<^sub>j) to track order of insertion.
ease of visualisation when n:=newint happens


pop of A\<^sub>2 doesnt occur.
*)

(*definition "FAAZ t w \<sigma> ts' \<equiv> 
        (update_trans t w (value \<sigma> w) \<sigma> ts', value \<sigma> w)"*)



