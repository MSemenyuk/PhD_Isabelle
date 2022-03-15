theory RCU
imports Main PSem
begin 



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
  n_dec :: "T \<Rightarrow> bool"        (*now modelled as local pointer allocation - True/False*)
  s_dec :: "T \<Rightarrow> bool"        (*now modelled as local pointer allocation - True/False*)
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
  "giveup_readandwrite_ownership t loc ms \<equiv>  ms \<lparr> own\<^sub>R := (own\<^sub>R ms) (loc:=own\<^sub>R ms loc - {t}) \<rparr>"

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
  "int_star_n ms t ms' \<equiv> ms' = ms \<lparr>n_dec := (n_dec ms) (t := True),
                               n := (n ms) (t := None),
                                  pc := (pc ms) (t := I3)\<rparr>"
(*int *s*)
definition int_star_s :: "mstate \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> bool" ("_ int[*s\<^sub>_] _" [200,200,200])           \<comment>\<open>int *s\<close>
  where
  "int_star_s ms t ms' \<equiv> ms' = ms \<lparr>s_dec := (s_dec ms) (t := True),
                               s := (s ms) (t := None),
                                  pc := (pc ms) (t := I4) \<rparr>"




(*******   n = new int  **********)
definition new_int :: "mstate \<Rightarrow> posem \<Rightarrow> T \<Rightarrow> mstate \<Rightarrow> posem \<Rightarrow> bool" ( "_ _ n:=newint _ _ _" [200,200,200,200,200])
  where
  "new_int ms ps t ms' ps' \<equiv>  (\<exists>loc prov. (allocate_object ps loc prov ps' variable 
                                    \<and> ms' = ms \<lparr>n := (n ms) (t := Some loc),
                                                 own\<^sub>R := (own\<^sub>R ms) (loc:=own\<^sub>R ms loc \<union> {t}),
                                                 own\<^sub>W := (own\<^sub>W ms) (loc:=Some t),
                                                   pc := (pc ms) (t := I5) \<rparr>))"

lemma switch:
  "prov\<notin> dom(A ps) \<longrightarrow> A ps prov = None"
  by auto

lemma switch2:
  "n ms t = None \<Longrightarrow> \<exists>prov loc. (allocate_object ps loc prov ps' variable  
                                    \<and> ms' = ms \<lparr>n := (n ms) (t := Some loc),
                                             own\<^sub>R := (own\<^sub>R ms) (loc:=own\<^sub>R ms loc \<union> {t}),
                                             own\<^sub>W := (own\<^sub>W ms) (loc:=Some t),
                                               pc := (pc ms) (t := I5) \<rparr>) 
      \<Longrightarrow> n ms' t\<noteq> None"
  apply(simp add:new_int_def) apply clarify
  by simp

lemma switch3:
  "n ms t = None \<Longrightarrow> \<exists>prov loc. (allocate_object ps loc prov ps' variable  
                                    \<and> ms' = ms \<lparr>n := (n ms) (t := Some loc),
                                             own\<^sub>R := (own\<^sub>R ms) (loc:=own\<^sub>R ms loc \<union> {t}),
                                             own\<^sub>W := (own\<^sub>W ms) (loc:=Some t),
                                               pc := (pc ms) (t := I5) \<rparr>) 
    \<Longrightarrow> own\<^sub>W ms' (the(n ms' t)) =Some  t"
  apply(simp add:new_int_def) apply clarify 
  by clarsimp









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
  "setup_r  ms t ms' \<equiv> ms' = ms \<lparr> r := (r ms) (t := \<lambda> i . 0),
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
  "insert_address ms t loc ms' \<equiv> ms' = ms\<lparr> det := (det ms) (t:= (((det ms) t) @ [loc])),
                                            pc := (pc ms) (t := R2), 
                                             s_dec := (s_dec ms) (t := False),
                                             s := (s ms) (t := None)\<rparr>"


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
                                                 n_dec := (n_dec ms) (t := False),
                                                  own\<^sub>W := (own\<^sub>W ms) (cv:=Some t),        \<comment>\<open>acquire wr_cap on location\<close>
                                                  own\<^sub>W := (own\<^sub>W ms) (nv:=None),          \<comment>\<open>let go of wr_cap on location\<close>
                                                   pc  := (pc ms) (t := cas_res)\<rparr>))
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
  "nallocdef t b ms \<equiv>  ms \<lparr> n_dec := (n_dec ms) (t:=b) \<rparr> "

definition sallocdef :: "T \<Rightarrow> bool \<Rightarrow> mstate \<Rightarrow> mstate" ( "s[_]:=_" [200,200])
  where
  "sallocdef t b ms \<equiv>  ms \<lparr> s_dec := (s_dec ms) (t:=b) \<rparr> "

definition SC_fence :: "surrey_state \<Rightarrow> T \<Rightarrow> surrey_state \<Rightarrow> bool " ("_ Fence _ _" [200,200,200])
  where
  "SC_fence \<sigma> t \<sigma>' \<equiv> 
       \<exists> w ts'. w \<in> visible_writes \<sigma> t casloc \<and>
               w \<notin> covered \<sigma> \<and>
               valid_fresh_ts \<sigma> w ts' \<and>
       \<sigma>' = fst(CAS t w (value \<sigma> w) (value \<sigma> w) \<sigma> ts')"





lemmas abbr = v_allocation_def int_star_n_def int_star_s_def
                new_int_def get_s_def writeto_star_n_def
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
\<comment>\<open> \<close>
|  R5 \<Rightarrow> (ms ps free[pop[detached[t]]] ms' ps')  \<and> \<sigma> =\<sigma>'                  \<comment>\<open> ownW ps hd(det ps t) := None \<close>
\<comment>\<open> \<close>
|  S1 \<Rightarrow> (ms r[N]:={0} t ms') \<and> ps = ps'  \<and> \<sigma> = \<sigma>'
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
            then (ms' = (pc[t]:=I12) ms) \<and> ps = ps' \<and> \<sigma> = \<sigma>'
            else (ms' = (pc[t]:=I6 \<circ> repeat[t]:=True) ms) \<and> ps = ps' \<and> \<sigma> = \<sigma>'
|  I12 \<Rightarrow> (ps \<sigma> rcuexit[] t ps' \<sigma>') \<and> (ms' = ((pc[t]:=R1 \<circ> n[t]:=False \<circ> givesupRown[t,the (n ms t)])) ms)  \<comment>\<open> lets go of raw cap on n\<close>
        \<comment>\<open>reclaim(s)\<close>                                            \<comment>\<open> (ownW ps s) = t \<close>            \<comment>\<open> lets go of raw cap on s\<close>
|  I13 \<Rightarrow> (ms' = (pc[t]:=I14) ms) \<and> \<sigma> = \<sigma>' \<and> ps = ps'   
|  I14 \<Rightarrow> ms' = (repeat[t]:=False) ms \<and> \<sigma> = \<sigma>' \<and> ps = ps'  \<comment>\<open> return(v) \<close> 
| finished \<Rightarrow> ms = ms' \<and> ps=ps' \<and> \<sigma>=\<sigma>'
" 

lemma "n ms' t \<noteq> i \<Longrightarrow> (SOME loc. (the(n ms' t) = loc)) \<equiv> the(n ms' t)"
  by simp
  

  
lemma " \<exists> x. (x=2 \<and> x = p) \<Longrightarrow>  (SOME x.  x)  \<equiv> p=2 "
  by (simp add: some_equality)







definition "Rcap ms t addrs \<equiv> \<forall>i. (i\<in>addrs) \<longleftrightarrow> (t\<in>own\<^sub>R ms i)"
definition "Wcap ms t addrs \<equiv> \<forall>i. (i\<in>addrs) \<longleftrightarrow> (the(own\<^sub>W ms i)=t)"

definition "inlist a lst \<equiv> \<exists>j.(j<length(lst) \<and> lst!j = a)"
definition "detaddrs ms t \<equiv> {i. inlist i (det ms t)}"
definition "tail_detaddrs ms t \<equiv> {i. inlist i (det ms t)}"
definition "n_pointer ms t\<equiv> the(n ms t)"
definition "s_pointer ms t\<equiv> the(s ms t)"
definition "s_and_n ms t \<equiv> {n_pointer ms t,s_pointer ms t}"
definition "just_n ms t \<equiv> {n_pointer ms t}"
definition "just_s ms t \<equiv> {s_pointer ms t}"

(*\<forall>t loc. t\<le>T_max \<and> loc\<noteq>s_t \<and> loc\<noteq>n_t \<and> loc \<notin> detaddrs ms t \<and> loc\<noteq>C \<and> loc\<noteq>rcu[t]\<longrightarrow> loc\<in>free *)
(*\<forall>loc. loc\<in>free \<longrightarrow> own\<^sub>R ms loc = {}*)
lemmas names [simp] = n_pointer_def s_pointer_def s_and_n_def just_n_def just_s_def
                      inlist_def detaddrs_def tail_detaddrs_def
lemmas names_2      = Rcap_def Wcap_def


(*------------structure lemmas---------------*)

definition "addr_allocated ms ps \<equiv> \<forall>addr t . addr \<in> detaddrs ms t \<longrightarrow> 
                                 (\<exists>prov. (A ps prov = Some (addr, pointer)))"

definition "nptr_true_imp ms ps \<equiv> \<forall>t . (n_dec ms t = True \<and> n ms t\<noteq>None) \<longrightarrow>
                          (\<exists>prov. (A ps prov = Some (the (n ms t), pointer)))"

definition "sptr_true_imp ms ps \<equiv> \<forall>t . (s_dec ms t = True \<and> s ms t\<noteq>None) \<longrightarrow>
                          (\<exists>prov. (A ps prov = Some (the (s ms t), pointer)))"

(*-----------observation lemmas --------------*)






(*------- careful observation of preCond per thread ----------*)
definition "pre_I1 ms t \<equiv>
                         Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> n ms t = None 
                       \<and> n_dec ms t = False
"

(* s ms t = None
                        
                        \<and> v ms t = None
                        \<and> s ms t = False 
                        \<and> n ms t = False 
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = False \<and> repeat ms t = False
                        \<and> *)
definition "pre_I2 ms t \<equiv>
                          Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                        \<and> n ms t = None 
                        \<and> n_dec ms t = True
"
(*s ms t = None 
                        \<and> n ms t = None 
                        \<and> v ms t = None
                        \<and> s ms t = False 
                        \<and> n_dec ms t = False 
                        \<and> CTRsync\<^sub>1 ms t = 0 \<and> CTRsync\<^sub>2 ms t = 0 
                        \<and> res ms t = 0 \<and> reg ms t = 0
                        \<and> nondet_val ms t = False \<and> CAS_succ ms t = False \<and> repeat ms t = False
                        \<and> *)
definition "pre_I3 ms t \<equiv>
                         Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> n ms t = None 
                       \<and> n_dec ms t = True
"
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
                          Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> n ms t = None 
                       \<and> n_dec ms t = True
"
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
                           Rcap ms t (detaddrs ms t \<union> just_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)
                       \<and> n ms t \<noteq> None 
                       \<and> n_dec ms t = True
"
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
                         Wcap ms t (detaddrs ms t \<union> just_n ms t) 
                \<and>  repeat ms t  \<longrightarrow>(s ms t \<noteq> None \<and> Rcap ms t (detaddrs ms t \<union> s_and_n ms t))
                \<and> \<not>repeat ms t  \<longrightarrow>(s ms t = None \<and> Rcap ms t (detaddrs ms t \<union> just_n ms t))
                       \<and> n ms t \<noteq> None 
                       \<and> n_dec ms t = True
"
(*(repeat ms t  \<longrightarrow> (\<exists>j k. s ms t = Some j \<and> v ms t = Some k))
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
                          Rcap ms t (detaddrs ms t \<union> just_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)
                       \<and> n ms t \<noteq> None 
                       \<and> n_dec ms t = True
"
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
                           Rcap ms t (detaddrs ms t \<union> just_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)
                       \<and> n ms t \<noteq> None 
                       \<and> n_dec ms t = True
"
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
                           Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)
                       \<and> n ms t \<noteq> None 
                       \<and> n_dec ms t = True
"
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
                           Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)
                       \<and> n ms t \<noteq> None 
                       \<and> n_dec ms t = True
"
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
                          Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)
                       \<and> n ms t \<noteq> None 
                       \<and> n_dec ms t = True
"
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
                          (CAS_succ ms t \<longrightarrow> Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_s ms t)
                       \<and> n_dec ms t)
                        \<and> (\<not>CAS_succ ms t\<longrightarrow> Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)
                       \<and> \<not>n_dec ms t)
                       \<and> n ms t \<noteq> None 
"
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
                           Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_s ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
"
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
                          Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
"
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
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
"
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
                           Rcap ms t (detaddrs ms t \<union> just_s ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_s ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
"
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
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
"
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
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
"
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
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
"
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
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
"
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
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
"
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
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
"
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
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
"
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
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
"
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
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
"
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
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
"
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
                          Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
"
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
                         \<and> n_dec ms t = False
                         \<and> s_dec ms t = False
                         \<and> v ms t = None
                         \<and> n ms t = None
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
definition "main_inv ms \<equiv>\<forall>t. (t\<le>T_max 
                            \<and> n_dec ms t = True
                            \<and> n ms t \<noteq> None)
                  \<longrightarrow> own\<^sub>R ms (the (n ms t)) = {t}"

definition "main_inv_2 ms ps\<equiv> \<forall>loc. isfree_addr loc ps \<longrightarrow> own\<^sub>R ms loc = {}"
definition "main_inv_3 ms ps\<equiv> \<forall>loc t. t\<notin>own\<^sub>R ms loc \<longrightarrow> own\<^sub>W ms loc \<noteq> Some t"



lemma "main_inv_2 ms ps \<Longrightarrow> main_inv_3 ms ps \<Longrightarrow> isfree_addr loc ps \<Longrightarrow>
          own\<^sub>R ms loc = {} \<Longrightarrow> own\<^sub>W ms loc = None"
  apply (simp add:main_inv_2_def main_inv_3_def) 
  by (metis empty_iff option.exhaust)



definition "observation_lemma_ms ms ps \<equiv> \<forall>t loc .( (t\<le>T_max \<and> the(own\<^sub>W ms (loc)) = t)) \<longrightarrow>
                              (loc \<in> (detaddrs ms t \<union> s_and_n ms t))"

definition "observation_lemma_sig ms ps \<sigma> \<equiv> \<forall>t loc .( (t\<le>T_max \<and> the(own\<^sub>W ms (loc)) = t)
                                                      \<or> \<not>isfree_addr loc ps) \<longrightarrow>
                               (\<exists>val . cvd[C, val] \<sigma> \<longrightarrow> val \<noteq> loc)"

                                              
lemmas new_main_inv [simp] = main_inv_def main_inv_2_def main_inv_3_def

(*supporting structure invariants*)
definition "allocated_s_addr ms ps \<equiv> \<forall>t. (t\<le>T_max \<and> (s ms t)\<noteq>None \<and> t\<in>own\<^sub>R ms (the(s ms t)))\<longrightarrow> \<not>(isfree_addr (the(s ms t)) ps)"
definition "allocated_n_addr ms ps \<equiv> \<forall>t. (t\<le>T_max \<and> (n ms t)\<noteq>None \<and> (n_dec ms t))\<longrightarrow> \<not>(isfree_addr (the(n ms t)) ps)"
definition "allocated_det_addr ms ps \<equiv> \<forall>t i. (t\<le>T_max \<and> det ms t\<noteq>[] \<and> i<length(det ms t))\<longrightarrow> \<not>(isfree_addr (det ms t ! i) ps)"

definition "allocated_rcuandC_addr ms ps \<equiv> (\<not>(isfree_addr (C) ps)) \<and> (\<forall>i. i<T_max \<longrightarrow> \<not>(isfree_addr (rcu_0+i) ps))"

definition "allocated_addresses ms ps \<equiv> allocated_s_addr ms ps \<and> allocated_n_addr ms ps \<and> 
                                        allocated_det_addr ms ps \<and> allocated_rcuandC_addr ms ps"
lemmas allocation_lemmas = allocated_addresses_def
                           allocated_s_addr_def allocated_n_addr_def
                           allocated_det_addr_def allocated_rcuandC_addr_def

definition "n_is_a_unique_loc ms \<equiv> \<forall>t ta. (t\<le>T_max \<and> ta\<le>T_max \<and> ta\<noteq>t
                                        \<and> n_dec ms t \<and> n ms t \<noteq> None) 
                      \<longrightarrow> the(n ms t) \<notin> ({the(s ms ta),the(n ms ta)}\<union>detaddrs ms ta)"

definition "n_is_a_unique_local_loc ms \<equiv> \<forall>t. (t\<le>T_max \<and> n_dec ms t \<and> n ms t \<noteq> None) 
                      \<longrightarrow> the(n ms t) \<notin> ({the(s ms t)}\<union>detaddrs ms t)"

definition "n_uniqueness ms \<equiv> n_is_a_unique_loc ms \<and> n_is_a_unique_local_loc ms"

definition "s_loc_rule ms \<equiv> \<forall>t ta. (t\<le>T_max \<and> ta\<le>T_max 
                                        \<and> s ms t \<noteq> None \<and> t\<in> own\<^sub>R ms (the(s ms t)))
                      \<longrightarrow> the(s ms t) \<notin> (detaddrs ms ta)"


definition "general_structure ms \<equiv> n_uniqueness ms \<and> s_loc_rule ms"
                                       
lemmas general_structure_lemmas = general_structure_def
                                  n_uniqueness_def s_loc_rule_def
                                  n_is_a_unique_loc_def n_is_a_unique_local_loc_def

lemma s_allocs_differs_from_n_allocs:
  " general_structure ms\<Longrightarrow> 
(t\<le>T_max \<and> ta\<le>T_max\<and> n_dec ms ta \<and> n ms ta \<noteq> None) \<Longrightarrow>
                      the(s ms t) \<noteq> the(n ms ta) "
  apply (simp_all add:general_structure_lemmas) 
  by metis





lemma differences:
  assumes "s ms 0 = Some 5"
  and "s ms 1 = Some 4" 
  and "T_max = 1"
shows "s ms 0 \<noteq> s ms 1"
  using assms
  by auto


lemmas allocated [simp] = allocated_n_addr_def

lemma ms_observation_lemma_Correctness_supp_1:
  assumes "preCond ms ps \<sigma> (pc ms t) t"
  and "t \<le> T_max"
  and "ta \<le> T_max"
  and "step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "ta \<noteq> t"
shows "n ms ta = n ms' ta"
  using assms
  apply(simp add:step_def)
  apply(simp add:preCond_def)
  apply(case_tac "pc ms t", simp_all)
  apply(simp_all add:abbr)
  apply clarify
  apply(simp_all add:general_structure_lemmas) apply(simp add:get_C_val_def)
  apply(simp add:FAAZ_def)
  apply(simp add: visible_writes_def) 
  apply(subgoal_tac "n ms t \<noteq> n ms ta") prefer 2 
  apply metis
  apply clarsimp
  apply(clarsimp)
  apply clarify
  apply(case_tac "snd (CAS t (a, b) (the (s ms t)) (the (n ms t)) \<sigma> ts')", simp_all)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply(clarsimp)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply(clarsimp)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply(clarsimp)
  by(case_tac "reg ms t = Suc 0", simp_all add:abbr)


lemma ms_observation_lemma_Correctness_supp_2:
  assumes "preCond ms ps \<sigma> (pc ms t) t"
  and "t \<le> T_max"
  and "ta \<le> T_max"
  and "step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "ta \<noteq> t"
shows "s ms ta = s ms' ta"
  using assms 
  apply(simp add:step_def)
  apply(simp add:preCond_def)
  apply(case_tac "pc ms t", simp_all)
  apply(simp_all add:abbr)
  apply clarify
  apply(simp_all add:general_structure_lemmas)apply(simp add:get_C_val_def)
  apply(simp add:FAAZ_def)
  apply(simp add: visible_writes_def) 
  apply(subgoal_tac "n ms t \<noteq> n ms ta") prefer 2 
  apply metis
  apply clarsimp
  apply(clarsimp)
  apply clarify
  apply(case_tac "snd (CAS t (a, b) (the (s ms t)) (the (n ms t)) \<sigma> ts')", simp_all)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply(clarsimp)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply(clarsimp)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply(clarsimp)
  by(case_tac "reg ms t = Suc 0", simp_all add:abbr)

lemma ms_observation_lemma_Correctness_supp_3:
  assumes "preCond ms ps \<sigma> (pc ms t) t"
  and "t \<le> T_max"
  and "ta \<le> T_max"
  and "step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "ta \<noteq> t"
shows "det ms ta = det ms' ta"
  using assms
  apply(simp add:step_def)
  apply(simp add:preCond_def)
  apply(case_tac "pc ms t", simp_all)
  apply(simp_all add:abbr)
  apply clarify
  apply(simp_all add:general_structure_lemmas)apply(simp add:get_C_val_def)
  apply(simp add:FAAZ_def)
  apply(simp add: visible_writes_def) 
  apply(subgoal_tac "n ms t \<noteq> n ms ta") prefer 2 
  apply metis
  apply clarsimp
  apply(clarsimp)
  apply clarify
  apply(case_tac "snd (CAS t (a, b) (the (s ms t)) (the (n ms t)) \<sigma> ts')", simp_all)
  apply(case_tac "CAS_succ ms t", simp_all add:abbr)
  apply(clarsimp)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all add:abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  apply(clarsimp)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  apply(clarsimp)
  by(case_tac "reg ms t = Suc 0", simp_all add:abbr)

lemma "\<exists>a b. A ps prov = Some (a, b) \<Longrightarrow>prov \<in> dom(A ps)"
  by (simp add: domIff)





lemma ms_observation_lemma_Correctness_supp_4:
  assumes "preCond ms ps \<sigma> (pc ms t) t"
  and "t \<le> T_max"
  and "ta \<le> T_max"
  and "step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "ta \<noteq> t" 
  and "the (own\<^sub>W ms loc) = ta"
  and "\<not>isfree_addr loc ps"
  and "loc \<noteq> hd (det ms t)"
shows "the (own\<^sub>W ms' loc) = ta"
  using assms apply (simp_all)
  apply(simp add:step_def)
  apply(simp add:preCond_def)
  apply(case_tac "pc ms t", simp_all)
  apply(simp_all add:abbr)
  apply clarify
  apply(simp_all add:general_structure_lemmas)
  apply(subgoal_tac "loc\<noteq>loca", simp_all add:Rcap_def Wcap_def)  apply clarsimp apply(simp add:get_C_val_def)     
  apply(simp add:FAAZ_def)
  apply(simp add: visible_writes_def)  apply clarsimp 
  apply clarsimp 
  apply(simp add: visible_writes_def)   apply clarsimp
  apply(case_tac "(snd (CAS t (a, b) (the (s ms t)) (the (n ms t)) \<sigma> ts'))", simp_all)
  apply metis
  apply(case_tac "CAS_succ ms t", simp_all add:abbr) apply clarsimp
  apply(case_tac "nondet_val ms t", simp_all add:abbr) apply clarsimp
  apply(case_tac "det ms t", simp_all add:abbr)apply clarify
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr) apply clarify
  apply(case_tac "x = 0", simp_all)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr) apply clarify
  apply(case_tac "v = 0", simp_all)
  by(case_tac "reg ms t = 1", simp_all add:abbr)




lemma ms_observation_lemma_Correctness:
  assumes "preCond ms ps \<sigma> pcr t"
  and "t \<le> T_max"
  and "main_inv ms"
  and "main_inv_2 ms ps"
  and "main_inv_3 ms ps"
  and "pcr = pc ms t"
  and "step ms ps \<sigma> pcr t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "pcr' = pc ms' t"
  and "ta \<le> T_max \<and> the (own\<^sub>W ms loc) = ta"
  and "observation_lemma_ms ms ps"
  and "ta \<noteq> t"
shows "loc \<in> (detaddrs ms' ta \<union> s_and_n ms' ta)"
  using assms 
  apply(subgoal_tac "(det ms' ta) = (det ms ta)") prefer 2 
  using ms_observation_lemma_Correctness_supp_3 
  apply force
  apply(subgoal_tac "the (s ms' ta) = the (s ms ta)") prefer 2 
  using ms_observation_lemma_Correctness_supp_2 
  apply force
  apply(subgoal_tac "the (n ms' ta) = the (n ms ta)") prefer 2 
  using ms_observation_lemma_Correctness_supp_1
  apply force
  apply(simp add:observation_lemma_ms_def)
  by meson


lemma ms_observation_lemma_Correctness_2:
  assumes "preCond ms ps \<sigma> pcr t"
  and "t \<le> T_max"
  and "main_inv ms"
  and "main_inv_2 ms ps"
  and "main_inv_3 ms ps"
  and "pcr = pc ms t"
  and "step ms ps \<sigma> pcr t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "pcr' = pc ms' t"
  and "ta \<le> T_max \<and> the (own\<^sub>W ms loc) = ta"
  and "observation_lemma_ms ms ps"
  and "ta \<noteq> t"
  and "\<not>isfree_addr loc ps"
  and "loc \<noteq> hd (det ms t)"
shows "observation_lemma_ms ms' ps'"
  using assms 
  apply(subgoal_tac "(det ms' ta) = (det ms ta)") prefer 2 
  using ms_observation_lemma_Correctness_supp_3 
  apply force
  apply(subgoal_tac "the (s ms' ta) = the (s ms ta)") prefer 2 
  using ms_observation_lemma_Correctness_supp_2 
  apply force
  apply(subgoal_tac "the (n ms' ta) = the (n ms ta)") prefer 2 
  using ms_observation_lemma_Correctness_supp_1
  apply force
  apply(case_tac "the (own\<^sub>W ms loc) = ta") prefer 2
  apply linarith 
  apply(subgoal_tac "the (own\<^sub>W ms' loc) = ta") prefer 2 
  using ms_observation_lemma_Correctness_supp_4 
  apply meson
  apply(subgoal_tac "loc \<in> (detaddrs ms' ta \<union> s_and_n ms' ta)") prefer 2
  using ms_observation_lemma_Correctness apply blast
  apply(simp add:observation_lemma_ms_def)
  apply(simp add:observation_lemma_ms_def)
  sorry











lemma sigma_observation_lemma_Correctness:
  assumes "preCond ms ps \<sigma> (pc ms t) t"
  and "wfs \<sigma>"
  and "t \<le> T_max"
  and "step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "observation_lemma_ms ms ps"
  and "observation_lemma_sig ms ps \<sigma>"
  and "main_inv ms"
  and "main_inv_2 ms ps"
  and "main_inv_3 ms ps"
  and "cvd[C,vala] \<sigma>"
shows "observation_lemma_sig ms' ps' \<sigma>'"
  using assms apply (simp_all)
  apply(simp add:preCond_def RCU.step_def)
  apply(case_tac "pc ms t", simp_all add:abbr)
  apply(simp add:covered_v_def general_structure_lemmas )
  apply clarify
  apply(unfold observation_lemma_sig_def observation_lemma_ms_def)
  by (metis (full_types))+



lemma ms_observation_lemma_Correctnesssss:
  assumes "preCond ms ps \<sigma> (pc ms t) t"
  and "wfs \<sigma>"
  and "t \<le> T_max"
  and "step ms ps \<sigma> (pc ms t) t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "observation_lemma_ms ms ps"
  and "observation_lemma_sig ms ps \<sigma>"
  and "main_inv ms"
  and "main_inv_2 ms ps"
  and "main_inv_3 ms ps"
  and "cvd[C,vala] \<sigma>"
shows "observation_lemma_ms ms' ps'"
  using assms apply (simp_all)
  apply(simp add:preCond_def RCU.step_def)
  apply(case_tac "pc ms t", simp_all add:abbr)
  apply(simp add:covered_v_def general_structure_lemmas )
  apply clarify
  apply(unfold observation_lemma_sig_def observation_lemma_ms_def)
  apply(subgoal_tac "\<forall>loc t. t\<le>T_max \<and> own\<^sub>W ms' loc  = Some t
  \<longrightarrow> loc\<in>(detaddrs ms' t \<union> s_and_n ms' t) ") 
  sorry











lemma main_invariant_Correctness:
  assumes "preCond ms ps \<sigma> pcr t"
  and "t \<le> T_max"
  and "main_inv ms"
  and "main_inv_2 ms ps"
  and "pcr = pc ms t"
  and "step ms ps \<sigma> pcr t ms' ps' \<sigma>'"    
  and "general_structure ms"
  and "pcr' = pc ms' t"
  and "observation_lemma_ms ms ps"
  and "observation_lemma_sig ms ps \<sigma>"
shows "main_inv ms'"
  using assms apply (simp add:preCond_def step_def)
  apply(case_tac[!] "pc ms t", simp_all add:abbr) 
  apply(intro allI)
  apply(intro impI) apply(elim conjE exE) apply(simp add:isfree_addr_def) 
  apply (metis insert_not_empty option.sel) 
  apply(intro allI)
  apply(simp add:general_structure_lemmas)
  apply metis
  defer (*I8*)
  defer (*I9*)
  defer (*I11*)
  apply(simp add:general_structure_lemmas)
  apply metis 
  apply(case_tac "CAS_succ ms t", simp_all)
  apply(simp_all add:abbr)
  defer (*R2*)
  apply(simp add:general_structure_lemmas) apply(case_tac "nondet_val ms t = True", simp_all)
  apply(simp_all add:abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all) 
  apply(simp_all add:abbr)
  apply(simp add:general_structure_lemmas)
  apply (metis Diff_empty Diff_insert0 insert_absorb insert_iff)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(simp_all add:abbr)
  defer (*S3*)
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all)
  apply(simp_all add:abbr)
  defer (*S6*)
  apply(case_tac "reg ms t = Suc 0", simp_all)
  apply(simp add:abbr)
  apply(simp add:abbr)
  apply(clarify) 
  apply(simp add:get_C_val_def) 
  apply(subgoal_tac "(snd (FAAZ t (a, b) \<sigma> ts')) \<noteq> the(n ms ta)", simp add:FAAZ_def) (*need this as pre_cond*)
  
        apply (metis option.sel)
  defer
  apply clarify
  apply(subgoal_tac "own\<^sub>R ms (the(n ms ta)) = {ta}") prefer 2
  apply(simp add:general_structure_lemmas) 
  apply (metis option.sel)
  apply(simp add:general_structure_lemmas)  
  apply clarify
  apply(case_tac "snd (CAS t (a, b) (the (s ms t)) (the (n ms t)) \<sigma> ts') ")
  apply(subgoal_tac "n_dec ms' t = False") prefer 2
  apply(simp add:general_structure_lemmas)
  apply(simp add:general_structure_lemmas)  
  apply (metis option.sel)
  apply(simp add:general_structure_lemmas)  
  apply (metis option.sel)                      
  apply(simp add:general_structure_lemmas)  
  apply clarify
  apply(case_tac "b", simp_all) prefer 2 
  apply (metis option.sel) 
  apply (metis option.sel)                     
  apply(simp add:general_structure_lemmas)
  apply clarify apply(simp add:names_2)
  apply (metis option.sel)                  
  apply(simp add:general_structure_lemmas)
  apply clarify
  apply(case_tac "v", simp_all) prefer 2
  apply (metis option.sel)
  apply (metis option.sel)
  apply(simp add: visible_writes_def) 
  apply(simp add:observation_lemma_def general_structure_lemmas covered_v_def FAAZ_def)  
  apply(simp add:Wcap_def)
  by (metis option.sel)
  




lemma main_invariant_2_Correctness:
  assumes "preCond ms ps \<sigma> pcr t"
  and "t \<le> T_max"
  and "main_inv ms"
  and "main_inv_2 ms ps"
  and "pcr = pc ms t"
  and "step ms ps \<sigma> pcr t ms' ps' \<sigma>'"       (*and "allocated_n_addr ms ps "     seems redundant*)
  and "general_structure ms"
  and "pcr' = pc ms' t"
  and "observation_lemma \<sigma> ms"
shows "main_inv_2 ms' ps'"
  using assms apply simp
  apply(simp add:step_def) apply(case_tac "pc ms t", simp_all add:abbr)     
  apply(simp add:general_structure_lemmas preCond_def)
  apply(elim conjE exE, intro allI impI)
  apply(simp add:names_2)    
  (*FAAZ*)
  defer     
  apply(simp add:general_structure_lemmas preCond_def)
  apply(elim conjE exE, intro allI impI)
  apply(simp add:names_2)       
  apply(simp add:general_structure_lemmas preCond_def)
  apply(elim conjE exE, intro allI impI)
  apply(simp add:names_2)  
  apply(case_tac "snd (CAS t (a, b) (the (s ms t)) y \<sigma> ts') ") prefer 2
  apply simp
  apply simp
  apply(case_tac "CAS_succ ms t", simp_all)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(elim conjE exE, intro allI impI)
  apply(simp add:names_2)       
  apply(case_tac "nondet_val ms t", simp_all)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(case_tac "det ms t \<noteq> []", simp_all)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(elim conjE exE, intro allI impI)
  apply(simp add:names_2)       
  (*show that own\<^sub>R ms i \<in> det ms t \<longrightarrow> at some point is only held by {t}*)
  defer
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(elim conjE exE, intro allI impI)
  apply(simp add:names_2)     
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(elim conjE exE, intro allI impI)
  apply(simp add:names_2)         
  apply(case_tac "reg ms t = Suc 0", simp_all)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  (*FAAZ*)
  apply(simp add:general_structure_lemmas preCond_def abbr)
  apply(elim conjE exE, intro allI impI)
  apply(simp add:names_2)   
   defer
  
  sledgehammer
  oops



lemma General_Structure_Correctness:
  assumes "preCond ms ps \<sigma> pcr t"
  and "t \<le> T_max"
  and "main_inv ms"
  and "main_inv_2 ms ps"
  and "pcr = pc ms t"
  and "step ms ps \<sigma> pcr t ms' ps' \<sigma>'"       
  and "general_structure ms"
  and "pcr' = pc ms' t"
  and "observation_lemma \<sigma> ms"
  and "\<exists>prov loc. prov \<notin> dom(A ps) \<and> isfree_addr loc ps"
shows "general_structure ms'"
  using assms apply simp
  apply(simp add:step_def) apply(case_tac "pc ms t", simp_all add:abbr)     
  apply(simp_all add:general_structure_lemmas preCond_def names_2)
  apply metis
  apply metis 
  defer
  apply metis 
  defer
  defer
  defer
  apply metis
  defer
  defer
  apply(elim conjE exE)
  apply(case_tac "b", simp_all)
  apply(case_tac "nondet_val ms t", simp_all add:abbr)
  apply(case_tac "det ms t = []", simp_all add:abbr)
  defer
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all add:abbr)
  defer
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all add:abbr)
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all add:abbr)
  defer
  apply(case_tac "reg ms t = Suc 0", simp_all add:abbr)
  prefer 2
  apply(simp add:FAAZ_def)
  apply(simp add:allocated_addresses_def observation_lemma_def)
  apply (metis option.sel)
  apply(intro conjI impI) prefer 2
  apply clarify
  apply(case_tac "ta = t", simp_all) prefer 2
  apply (metis option.sel) apply clarify
  apply(intro conjI impI)
  apply(subgoal_tac "y \<notin> alloc_addrs ps") prefer 2
  apply blast
  apply(subgoal_tac "the (s ms t) \<in> alloc_addrs ps") 
  apply blast
  apply(subgoal_tac "allocated_addresses ms ps", simp_all add:allocation_lemmas)
  oops




lemma Global_Correctness:
  assumes "preCond ms ps \<sigma> pcr\<^sub>t t"
  and "preCond ms ps \<sigma> pcr\<^sub>t\<^sub>' t'"  
  and "pcr\<^sub>t = pc ms t"
  and "pcr\<^sub>t\<^sub>' = pc ms t'"
  and "t \<noteq> t'"
  and "main_inv ms"
  and "main_inv_2 ms ps"
  and "step ms ps \<sigma> pcr\<^sub>t t ms' ps' \<sigma>'"       (*and "allocated_n_addr ms ps "     seems redundant*)
  and "general_structure ms"
  and "pcr' = pc ms' t"
shows "preCond ms' ps' \<sigma>' pcr\<^sub>t\<^sub>' t'"
  using assms apply simp
  apply(simp add:step_def) apply(case_tac "pc ms t", simp_all add:abbr)     
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2) 
  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis        
 
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)  
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis        
  
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis  

  (*existential complication*) defer
  apply(simp add:general_structure_lemmas preCond_def) 
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)  
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis        
  
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis  
  
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis  
  
  (*existential complication, FAAZ*) defer
  (*weak memory read s*)defer
  
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  
  (*existential complication, CAS*)defer
   
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)  
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
   
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)  
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
   
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)  
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis

  apply(case_tac "CAS_succ ms t", simp_all)
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)  
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis

  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis 
  
  apply(simp add:general_structure_lemmas preCond_def)
  apply(elim conjE impE exE)
  apply(case_tac "b", simp_all)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2) 
 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis 
  apply(case_tac "pc ms t'", simp_all add:abbr names_2) 
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis

  apply(case_tac "nondet_val ms t", simp_all)
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  
  apply(case_tac "det ms t \<noteq> []", simp_all)
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  
  (*existential complication, kill(x)*)defer
  
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  
  apply(case_tac "CTRsync\<^sub>1 ms t < T_max", simp_all)
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  
  (*existential complication, (rcu_0 + CTRsync\<^sub>1) weak memory read*)defer
  
  apply(case_tac "CTRsync\<^sub>2 ms t < T_max", simp_all)
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  
  apply(case_tac "r ms t (CTRsync\<^sub>2 ms t) = 0", simp_all)
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  
  defer

  apply(case_tac "reg ms t = Suc 0", simp_all) 
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis
  apply(simp add:general_structure_lemmas preCond_def)
  apply(case_tac "pc ms t'", simp_all add:abbr names_2)
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis    apply metis  
  apply metis   apply metis    apply metis    apply metis    apply metis

(*weak memory guarantees needed, I think (maybe I'm wrong)*)
  oops







(*lemma test2:
  assumes "wfs \<sigma>"
  and "get_C_val ms \<sigma> t ms' \<sigma>'"
  and "cvd[C,u] \<sigma>"
shows "cvd[C,u] \<sigma>'"
  using assms apply (simp add:get_C_val_def FAAZ_def) apply(clarify) 
  apply(simp add:update_trans_def covered_v_def Let_def rev_app_def add_cv_def update_mods_def update_modView_def
      update_thrView_def)
  apply(unfold writes_on_def value_def lastWr_def) apply safe
  apply (metis fst_conv var_def)
  apply (metis fst_conv var_def visible_var)
  apply (metis fst_conv var_def visible_var)
  apply (metis fst_conv var_def)
  apply(simp add:visible_writes_def tst_def var_def valid_fresh_ts_def)
  apply(unfold writes_on_def value_def lastWr_def wfs_def var_def) apply safe
  (*ts; is max, nempty \<and> finite*) defer
  apply auto[1]    
  apply(simp) apply(intro conjI)
  apply (meson subset_iff visible_writes_in_writes)
  apply presburger
  apply (metis fst_conv)
  apply (metis fst_conv var_def visible_var)
  apply (metis fst_conv var_def visible_var)
  apply (metis fst_conv)
  (*ts; is max*) defer    
  apply(simp) apply(intro conjI)
  apply (meson subset_iff visible_writes_in_writes)
  apply presburger
  sorry*)




          
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



