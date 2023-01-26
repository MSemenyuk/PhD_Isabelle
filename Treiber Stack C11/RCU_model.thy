theory RCU_model
imports Main PSem OpSem_Proof_Rules OpSem_definite
begin 



datatype PC = I1 | I2 | I3 | I4 | I5 | I6 | I7 | I8 | I9 | I10 | I11 | I12 | I13 | I14 |  cas_res | finished
            | R1 | R2 | R3 | R4 | R5 
            | S1 | S2 | S3 | S4 | S5 | S6 | S7 



consts rcu_0 ::address (*first location of rcu array*)
consts F::nat
consts T_max::nat (*max_thread ID + 1*)
consts C :: nat     (*just referred to by its location in A(1) = (C,pointer) where C = nat*)
consts casloc :: nat
definition "set_T \<equiv> {n . n\<ge>0 \<and> n<T_max}"
definition "rcu_addrs \<equiv> {n . n\<ge>rcu_0 \<and> n < rcu_0+T_max}"
definition "something  \<equiv> F \<notin> rcu_addrs \<and> F \<noteq> C \<and> F \<noteq> casloc"

definition "con_assms_shared \<equiv> T_max >0 \<and> (\<forall>t. t<T_max \<longrightarrow> C \<noteq> rcu_0+t)"
lemma showsss: "con_assms_shared \<Longrightarrow> C \<noteq> rcu_0" 
  apply(simp add:con_assms_shared_def)
  by (metis Nat.add_0_right)




lemma test:
  assumes "F = i"
  and "something"
  shows "C \<noteq> i"
  using assms 
  by(simp add:something_def) 


(*
definition
  "wfs_2 \<sigma> \<equiv>
      wfs \<sigma> \<and> (\<forall> x. lastWr \<sigma> x \<notin> covered \<sigma>)"*)





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
definition load_rcu_to_r :: "mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow>  nat \<Rightarrow> T \<Rightarrow>  mstate \<Rightarrow> posem \<Rightarrow> surrey_state \<Rightarrow> bool" ( "_ _ _ r[i]:=rcu[_] _ _ _ _" [200,200,200,200,200])
  where
  "load_rcu_to_r ms ps \<sigma> i t ms' ps' \<sigma>' \<equiv> ps = ps' \<and> (\<exists>x y.  (A ps y = Some (rcu_0, pointer)) 
                                      \<and> \<sigma> [x \<leftarrow>(rcu_0 + i)]\<^sub>t \<sigma>'
                                      \<and> ms' = ms \<lparr> r := (r ms) (t := ((r ms) t) (i := x)),
                                                  pc := (pc ms) (t := S2),
                                                  CTRsync\<^sub>1 := (CTRsync\<^sub>1 ms) (t:=(CTRsync\<^sub>1 ms t)+1) \<rparr>)"

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
  "rcu_temp_copy ms \<sigma> i t ms' \<sigma>'\<equiv> \<exists> v. ((\<sigma> [ v \<leftarrow> (rcu_0 + i)]\<^sub>t \<sigma>')     \<comment>\<open>read rcu[i]\<close>
                                        \<and> (ms' = ms\<lparr>reg := (reg ms) (t := v),
                                                    pc := (pc ms) (t := S7)\<rparr>)) "


definition cas_step_rcu :: "mstate \<Rightarrow> surrey_state \<Rightarrow>T \<Rightarrow> L \<Rightarrow> V \<Rightarrow> V \<Rightarrow> mstate \<Rightarrow>  surrey_state \<Rightarrow> bool"
 where
    "cas_step_rcu ms \<sigma> t l cv nv ms' \<sigma>'\<equiv>  \<exists> w ts'. w \<in> visible_writes \<sigma> t l \<and>
               w \<notin> covered \<sigma> \<and>
               valid_fresh_ts \<sigma> w ts' \<and> (let (a, b) = CAS t w cv nv \<sigma> ts' in 

         \<comment>\<open>CAS(&C,s,n)\<close>
      
       \<sigma>' = a    
       \<and> 
(b \<longrightarrow>(ms' = ms\<lparr>CAS_succ := (CAS_succ ms) (t := b),
                                                 n_dec := (n_dec ms) (t := False),        \<comment>\<open>acquire wr_cap on location\<close>
                                                  own\<^sub>W := (own\<^sub>W ms) (nv:=None , cv:= Some t),          \<comment>\<open>let go of wr_cap on location\<close>
                                                   pc  := (pc ms) (t := cas_res)\<rparr>))
       \<and> 
(\<not> b \<longrightarrow>(ms' = ms\<lparr>CAS_succ := (CAS_succ ms) (t := b),
                                                   pc := (pc ms) (t := cas_res)\<rparr>)))"           






definition inc_ctr1 :: "T \<Rightarrow> mstate \<Rightarrow> mstate" ( "CTRsync\<^sub>1[_]++" [200])
  where
  "inc_ctr1 t ms \<equiv>  ms \<lparr> CTRsync\<^sub>1 := (CTRsync\<^sub>1 ms) (t:=(CTRsync\<^sub>1 ms t)+1) \<rparr> "

definition inc_ctr2 :: "T \<Rightarrow> mstate \<Rightarrow> mstate" ( "CTRsync\<^sub>2[_]++" [200])
  where
  "inc_ctr2 t ms \<equiv>  ms \<lparr> CTRsync\<^sub>2 := (CTRsync\<^sub>2 ms) (t:=(CTRsync\<^sub>2 ms t)+1) \<rparr> "

definition regreset :: "T \<Rightarrow> mstate \<Rightarrow> mstate" ( "regreset[_]" [200])
  where
  "regreset t ms \<equiv> ms \<lparr> reg := (reg ms) (t:=0) \<rparr>"

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
                rcu_temp_copy_def
                inc_ctr1_def inc_ctr2_def update_ctr1_def update_ctr2_def update_pc_def
                repetition_def SC_fence_def
                sallocdef_def nallocdef_def
                giveup_readandwrite_ownership_def regreset_def



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
|  R5 \<Rightarrow> (ms ps free[pop[detached[t]]] ms' ps')  \<and> \<sigma> =\<sigma>'     \<comment>\<open> ownW ps hd(det ps t) := None \<close>
\<comment>\<open> \<close>
|  S1 \<Rightarrow> (ms r[N]:={0} t ms') \<and> ps = ps'  \<and> \<sigma> = \<sigma>'
|  S2 \<Rightarrow> if (CTRsync\<^sub>1 ms t < T_max)
            then (if CTRsync\<^sub>1 ms t = t 
                    then ms' = (pc[t]:=S2 \<circ> CTRsync\<^sub>1[t]++) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
                    else ms' = (pc[t]:=S3) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>')
            else ms' = (pc[t]:=S4) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
|  S3 \<Rightarrow> (ms ps \<sigma> r[i]:=rcu[CTRsync\<^sub>1 ms t] t ms' ps' \<sigma>')
|  S4 \<Rightarrow> if (CTRsync\<^sub>2 ms t < T_max)
            then ms' = (pc[t]:=S5) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
            else ms' = (pc[t]:=R4) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'        \<comment>\<open> return to Reclaim (R4)\<close>
|  S5 \<Rightarrow> if r ms t (CTRsync\<^sub>2 ms t) = 0
            then ms' = (CTRsync\<^sub>2[t]++ \<circ> pc[t]:=S4) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
            else ms' = (pc[t]:=S6) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
|  S6 \<Rightarrow> ms \<sigma> load((CTRsync\<^sub>2 ms t))\<^sub>t ms' \<sigma>' \<and> ps = ps'  \<comment>\<open> load \<langle>rcu[i]\<rangle> into reg, increment pc\<close>
|  S7 \<Rightarrow> if reg ms t = 1                             \<comment>\<open> test while \<langle>rcu[i]\<rangle>\<close>
            then ms' = (pc[t]:=S6 \<circ> regreset[t]) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'
            else ms' = (CTRsync\<^sub>2[t]++ \<circ> pc[t]:=S4 \<circ> regreset[t]) ms \<and> ps = ps' \<and> \<sigma> =\<sigma>'


|  I1  \<Rightarrow> (ms int[v\<^sub>t] ms')  \<and> ps = ps' \<and> \<sigma> = \<sigma>'
|  I2  \<Rightarrow> (ms int[*n\<^sub>t] ms') \<and> ps = ps' \<and> \<sigma> = \<sigma>'
|  I3  \<Rightarrow> (ms int[*s\<^sub>t] ms') \<and> ps = ps' \<and> \<sigma> = \<sigma>'
|  I4  \<Rightarrow> (ms ps n:=newint t ms' ps')  \<and> \<sigma> = \<sigma>'                                           \<comment>\<open> takes raw cap on n\<close>
|  I5  \<Rightarrow> (ps \<sigma> rcuenter[] t ps' \<sigma>') \<and> (ms' = (pc[t]:=I6) ms)
|  I6  \<Rightarrow> (ps \<sigma> rcuexit[] t ps' \<sigma>')  \<and> (repeat ms t \<longrightarrow> ms' = (pc[t]:=I7 \<circ> givesupRown[t,the (s ms t)]) ms)   \<comment>\<open> lets go of raw cap on s\<close>
                                     \<and> (\<not>repeat ms t \<longrightarrow> ms' = (pc[t]:=I7) ms)
|  I7  \<Rightarrow> (ps \<sigma> rcuenter[] t ps' \<sigma>') \<and> (ms' = (pc[t]:=I8) ms)
\<comment>\<open>|  fence \<Rightarrow>  (\<sigma> Fence t \<sigma>') \<and> ps = ps' \<and> (ms' = (pc[t]:=I8) ms)   SC fence \<close> 
|  I8  \<Rightarrow> (ms \<sigma> s:=\<^sup>FC t ms' \<sigma>')       \<and> ps = ps'          \<comment>\<open> Fetch and Add 0 \<close>            \<comment>\<open> takes r cap on s (C weak read)\<close>
|  I9  \<Rightarrow> (ms \<sigma> v:=*s t ms' \<sigma>')      \<and> ps = ps'     
|  I10 \<Rightarrow> (ms \<sigma> *n:=newv t ms' \<sigma>')   \<and> ps = ps'                  \<comment>\<open> (ownW ps n) = t \<close>
|  I11 \<Rightarrow> cas_step_rcu ms \<sigma> t C (the (s ms t)) (the (n ms t)) ms' \<sigma>' \<and> ps = ps'           \<comment>\<open> swaps wr cap from n to s\<close>
|  cas_res \<Rightarrow> if CAS_succ ms t 
            then (ms' = (pc[t]:=I12) ms) \<and> ps = ps' \<and> \<sigma> = \<sigma>'
            else (ms' = (pc[t]:=I6 \<circ> repeat[t]:=True) ms) \<and> ps = ps' \<and> \<sigma> = \<sigma>'
|  I12 \<Rightarrow> (ps \<sigma> rcuexit[] t ps' \<sigma>') \<and> (ms' = ((pc[t]:=R1 \<circ> givesupRown[t,the (n ms t)])) ms)  \<comment>\<open> lets go of raw cap on n\<close>
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
definition "Wcap ms t addrs \<equiv> \<forall>i. (i\<in>addrs) \<longleftrightarrow> ((own\<^sub>W ms i) = Some t)"

definition "inlist a lst \<equiv> \<exists>j.(j<length(lst) \<and> lst!j = a)"
definition "detaddrs ms t \<equiv> {i. inlist i (det ms t)}"
definition "tail_detaddrs ms t \<equiv> {i. inlist i (det ms t)}"
definition "n_pointer ms t\<equiv> the(n ms t)"
definition "s_pointer ms t\<equiv> the(s ms t)"
definition "s_and_n ms t \<equiv> {n_pointer ms t,s_pointer ms t}"
definition "just_n ms t \<equiv> {n_pointer ms t}"
definition "just_s ms t \<equiv> {s_pointer ms t}"

(*\<forall>t loc. t<T_max \<and> loc\<noteq>s_t \<and> loc\<noteq>n_t \<and> loc \<notin> detaddrs ms t \<and> loc\<noteq>C \<and> loc\<noteq>rcu[t]\<longrightarrow> loc\<in>free *)
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



lemma testingthisonebecauseofreasons:
  "Rcap ms t (detaddrs ms t) \<Longrightarrow> 
  Wcap ms t (detaddrs ms t) \<Longrightarrow>
Rcap ms t' (detaddrs ms t') \<Longrightarrow>
t\<noteq>t' \<Longrightarrow>
2 \<notin> detaddrs ms t \<Longrightarrow>
 Wcap ms t' (detaddrs ms t') \<Longrightarrow>
ms' = ms \<lparr> s := (s ms) (t := Some 2),
                       pc := (pc ms) (t := I9),
                     own\<^sub>R := (own\<^sub>R ms) (2:= own\<^sub>R ms 2 \<union> {t})\<rparr>
\<Longrightarrow> Rcap ms' t' (detaddrs ms' t') 
" by (simp add:Rcap_def)



(*------- careful observation of preCond per thread ----------*)
definition "pre_I1 ms t \<equiv>
                         Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> n ms t = None 
                       \<and> n_dec ms t = False
                       \<and> s ms t = None
                       \<and> \<not>repeat ms t 
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
"

definition "pre_I2 ms t \<equiv>
                          Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                        \<and> n ms t = None 
                        \<and> n_dec ms t = False
                       \<and> s ms t = None
                       \<and> \<not>repeat ms t 
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
"

definition "pre_I3 ms t \<equiv>
                         Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> n ms t = None 
                       \<and> n_dec ms t = True
                       \<and> s ms t = None
                       \<and> \<not>repeat ms t 
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
"

definition "pre_I4 ms t \<equiv>
                          Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> n ms t = None 
                       \<and> n_dec ms t = True
                       \<and> s ms t = None
                       \<and> \<not>repeat ms t 
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
"

definition "pre_I5 ms t \<equiv>
                           Rcap ms t (detaddrs ms t \<union> just_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)
                       \<and> n ms t \<noteq> None 
                       \<and> n_dec ms t = True
                       \<and> s ms t = None
                       \<and> \<not>repeat ms t 
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
"

definition "pre_I6 ms t \<equiv>
                         Wcap ms t (detaddrs ms t \<union> just_n ms t) 
                \<and>  (repeat ms t  \<longrightarrow>(s ms t \<noteq> None \<and> Rcap ms t (detaddrs ms t \<union> s_and_n ms t)))
                \<and>  (\<not>repeat ms t \<longrightarrow>(s ms t = None \<and> Rcap ms t (detaddrs ms t \<union> just_n ms t)))
                       \<and> n ms t \<noteq> None 
                       \<and> n_dec ms t = True
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
"

definition "pre_I7 ms t \<equiv>
                           Rcap ms t (detaddrs ms t \<union> just_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)
                \<and>  (repeat ms t \<longrightarrow> s ms t \<noteq> None )
                \<and> (\<not>repeat ms t \<longrightarrow> s ms t = None )
                       \<and> n ms t \<noteq> None 
                       \<and> n_dec ms t = True
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
"

definition "pre_I8 ms t \<equiv> 
                           Rcap ms t (detaddrs ms t \<union> just_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)
                \<and>  (repeat ms t \<longrightarrow> s ms t \<noteq> None )
                \<and> (\<not>repeat ms t \<longrightarrow> s ms t = None )
                       \<and> n ms t \<noteq> None 
                       \<and> n_dec ms t = True
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
"

definition "pre_I9 ms t \<equiv> 
                           Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)
                       \<and> n ms t \<noteq> None 
                       \<and> n_dec ms t = True
                       \<and> s ms t \<noteq> None 
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
"

definition "pre_I10 ms t \<equiv>
                           Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)
                       \<and> n ms t \<noteq> None 
                       \<and> n_dec ms t = True
                       \<and> s ms t \<noteq> None 
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
                       
"

definition "pre_I11 ms t \<equiv>
                          Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)
                       \<and> n ms t \<noteq> None 
                       \<and> n_dec ms t = True
                       \<and> s ms t \<noteq> None 
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
"

definition "pre_cas_res ms t \<equiv>
                          (CAS_succ ms t \<longrightarrow> Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_s ms t)
                       \<and> \<not>n_dec ms t)
                        \<and> (\<not>CAS_succ ms t\<longrightarrow> Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_n ms t)
                       \<and> n_dec ms t)
                       \<and> n ms t \<noteq> None 
                       \<and> s ms t \<noteq> None 
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
"

definition "pre_I12 ms t \<equiv>
                           Rcap ms t (detaddrs ms t \<union> s_and_n ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_s ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
                       \<and> s ms t \<noteq> None 
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
"

\<comment>\<open> start to reclaim() \<close>
definition "pre_I13 ms t \<equiv>
                          Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
                       \<and> s ms t = None 
                       \<and> (CTRsync\<^sub>1 ms t = T_max \<or> CTRsync\<^sub>1 ms t = 0)
                       \<and> (CTRsync\<^sub>2 ms t = T_max \<or> CTRsync\<^sub>2 ms t = 0)
"

definition "pre_I14 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
                       \<and> s ms t = None 
                       \<and> (CTRsync\<^sub>1 ms t = T_max \<or> CTRsync\<^sub>1 ms t = 0)
                       \<and> (CTRsync\<^sub>2 ms t = T_max \<or> CTRsync\<^sub>2 ms t = 0)
"

definition "pre_R1 ms t \<equiv>  
                           Rcap ms t (detaddrs ms t \<union> just_s ms t) \<and> Wcap ms t (detaddrs ms t \<union> just_s ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
                       \<and> s ms t \<noteq> None 
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
"

definition "pre_R2 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
                       \<and> s ms t = None 
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
"

definition "pre_R3 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
                       \<and> s ms t = None 
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
"

\<comment>\<open> start to sync() \<close>
\<comment>\<open> or return to inc() \<close>
definition "pre_R4 ms t \<equiv>  
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
                       \<and> s ms t = None 
                       \<and> CTRsync\<^sub>1 ms t = T_max
                       \<and> CTRsync\<^sub>2 ms t = T_max
"

\<comment>\<open> return to inc() \<close>
definition "pre_R5 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
                       \<and> det ms t \<noteq> []
                       \<and> s ms t = None 
                       \<and> (\<forall>loc. loc\<in>detaddrs ms t \<longrightarrow> own\<^sub>R ms loc = {t})
                       \<and> CTRsync\<^sub>1 ms t = T_max
                       \<and> CTRsync\<^sub>2 ms t = T_max
"

definition "pre_S1 ms t \<equiv>  
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
                       \<and> s ms t = None 
                       \<and> CTRsync\<^sub>1 ms t = 0
                       \<and> CTRsync\<^sub>2 ms t = 0
"

definition "pre_S2 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
                       \<and> s ms t = None 
                       \<and> CTRsync\<^sub>1 ms t \<le> T_max
                       \<and> CTRsync\<^sub>2 ms t = 0
"

definition "pre_S3 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
                       \<and> s ms t = None 
                       \<and> CTRsync\<^sub>1 ms t < T_max
                       \<and> CTRsync\<^sub>2 ms t = 0
"

definition "pre_S4 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
                       \<and> s ms t = None 
                       \<and> CTRsync\<^sub>1 ms t = T_max
                       \<and> CTRsync\<^sub>2 ms t \<le> T_max
"

definition "pre_S5 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
                       \<and> s ms t = None 
                       \<and> CTRsync\<^sub>1 ms t = T_max
                       \<and> CTRsync\<^sub>2 ms t < T_max
"

definition "pre_S6 ms t \<equiv>
                           Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
                       \<and> s ms t = None 
                       \<and> CTRsync\<^sub>1 ms t = T_max
                       \<and> CTRsync\<^sub>2 ms t < T_max
"

definition "pre_S7 ms t \<equiv>
                          Rcap ms t (detaddrs ms t) \<and> Wcap ms t (detaddrs ms t)
                       \<and> \<not>n_dec ms t
                       \<and> n ms t \<noteq> None 
                       \<and> s ms t = None 
                       \<and> CTRsync\<^sub>1 ms t = T_max
                       \<and> CTRsync\<^sub>2 ms t < T_max
"





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
                         \<and> (\<forall>t t'. (t<T_max \<and> t'<T_max) \<longrightarrow> 
                                          r ms t t' = 0)
        \<and> (\<forall>i. (i\<ge>0) \<longrightarrow> A ps i = None \<and> own\<^sub>R ms i = {} \<and> own\<^sub>W ms i = None)
        \<and> alloc_addrs ps = {}"


(* old main invariant version
definition "main_invariant_1 ms \<equiv> \<forall>k t t'. ( k<length (det ms t) \<and> t'\<noteq>t \<and> t'<CTRsync\<^sub>1 ms t \<and> (r ms t t') = 0)
                                           \<longrightarrow> t' \<notin> own\<^sub>R ms ((det ms t) ! k)"

definition "main_invariant_2 ms \<equiv> \<forall>k t t'. ( k<length (det ms t) \<and> t'\<noteq>t \<and> t'<CTRsync\<^sub>2 ms t)
                                           \<longrightarrow> t' \<notin> own\<^sub>R ms ((det ms t) ! k)"

definition "main_invariant_3 ms \<sigma> \<equiv> \<forall>k t t'. ( k<length (det ms t) \<and> t'\<noteq>t \<and> CTRsync\<^sub>2 ms t < T_max 
                                                 \<and> t'=CTRsync\<^sub>2 ms t \<and> [(rcu_0+t') \<approx>\<^sub>t 0] \<sigma>)
                                           \<longrightarrow> t' \<notin> own\<^sub>R ms ((det ms t) ! k)"*)



(*-------------------------- Main Invariant --------------------------*)
definition "main_inv_1 ms \<equiv>\<forall>t. (t<T_max 
                            \<and> n_dec ms t = True
                            \<and> n ms t \<noteq> None)
                  \<longrightarrow> own\<^sub>R ms (the (n ms t)) = {t}"
definition "main_inv_2 ms ps\<equiv> \<forall>loc. isfree_addr loc ps \<longrightarrow> own\<^sub>R ms loc = {}"
definition "main_inv_3 ms ps\<equiv> \<forall>loc t. t\<notin>own\<^sub>R ms loc  \<longrightarrow> own\<^sub>W ms loc \<noteq> Some t"


lemma not_some_may_mean_none:
  "s ms t \<noteq> Some loc  \<Longrightarrow> \<exists>loca. loca\<noteq> loc \<and> (s ms t = Some loca) \<or> (s ms t = None)"
  by fastforce

definition "main_inv ms ps \<equiv> main_inv_1 ms \<and> main_inv_2 ms ps \<and> main_inv_3 ms ps"

lemmas main_inv_lemmas = main_inv_def main_inv_1_def main_inv_2_def main_inv_3_def

lemma "main_inv_2 ms ps \<Longrightarrow> main_inv_3 ms ps \<Longrightarrow> isfree_addr loc ps \<Longrightarrow>
          own\<^sub>R ms loc = {} \<Longrightarrow> own\<^sub>W ms loc = None"
  apply (simp add:main_inv_2_def main_inv_3_def) 
  by (metis empty_iff option.exhaust)




(*-------------------------- Supporting Invariant --------------------------*)
definition "observation_inv_ms ms \<equiv> \<forall>t loc .( (t<T_max \<and> (own\<^sub>W ms (loc)) = Some t)) \<longrightarrow>
                              (loc \<in> (detaddrs ms t) \<or> 
                          Some loc = s ms t \<or>
                          (Some loc = n ms t \<and> n_dec ms t))"

definition "observation_inv_sig ms ps \<sigma> \<equiv> \<forall>t loc val .(( (t<T_max \<and> (own\<^sub>W ms (loc)) = Some t)
                                                      \<or> isfree_addr loc ps) \<and> cvd[C, val] \<sigma>) 
                                      \<longrightarrow> val \<noteq> loc"








(*-------------supporting structure invariants----------------*)

(*allocated_addresses_lemmas*)
definition "allocated_n_addr ms ps \<equiv> \<forall>t i. (t<T_max \<and> (n ms t) = Some i \<and> (n_dec ms t))\<longrightarrow> \<not>(isfree_addr i ps)"
definition "allocated_det_addr ms ps \<equiv> \<forall>t i. (t<T_max \<and> det ms t\<noteq>[] \<and> i<length(det ms t))\<longrightarrow> \<not>(isfree_addr (det ms t ! i) ps)"
definition "allocated_s_addr ms ps \<equiv> \<forall>i t. t<T_max \<and> t \<in> own\<^sub>R ms i \<and> s ms t = Some i  \<longrightarrow>  \<not>isfree_addr i ps  "

definition "allocated_addresses ms ps \<equiv> allocated_s_addr ms ps \<and> allocated_n_addr ms ps \<and> 
                                        allocated_det_addr ms ps "
lemmas allocated_addresses_lemmas = allocated_addresses_def
                           allocated_s_addr_def allocated_n_addr_def
                           allocated_det_addr_def



(*general_structure_lemmas*)

definition "n_differ ms \<equiv> \<forall>i t ta . t<T_max \<and> ta<T_max \<and> t\<noteq>ta 
                                \<and> n_dec ms t \<and> n_dec ms ta \<and> n ms t = Some i 
                                    \<longrightarrow> n ms ta \<noteq> Some i"


definition "n_differ_from_s_outside ms \<equiv> \<forall>i t ta . t<T_max \<and> ta<T_max \<and> t\<noteq>ta \<and> 
                                      n_dec ms t \<and> n ms t = Some i \<longrightarrow>
                                    (ta \<notin> own\<^sub>R ms i)"

definition "n_differ_from_s_inside ms \<equiv> \<forall>i t . t<T_max \<and> 
                                    (n_dec ms t \<and> n ms t = Some i) 
                                    \<longrightarrow> s ms t \<noteq> Some i"

definition "s_differ_from_det_inside ms \<equiv> \<forall>j i t . t<T_max  \<and> 
                                (t \<in> own\<^sub>R ms i \<and> s ms t =Some i) 
                                    \<and> det ms t\<noteq>[] \<and> j<length(det ms t) 
                            \<longrightarrow> det ms t ! j \<noteq> the(s ms t)"

definition "n_differ_from_det ms \<equiv> \<forall>i loc t ta . t<T_max \<and> ta<T_max \<and>
                                    n_dec ms t \<and> n ms t = Some loc \<and>
                                    det ms ta \<noteq> [] \<and> i<length(det ms ta)
                           \<longrightarrow> det ms ta ! i \<noteq> loc"

definition "det_differ_from_det ms \<equiv> \<forall>i j t ta . t<T_max \<and> ta<T_max \<and> t\<noteq>ta \<and>
                                    det ms t \<noteq> [] \<and> det ms ta \<noteq> [] 
                                    \<and> i<length(det ms t) \<and> j<length(det ms ta)
                           \<longrightarrow>  det ms t ! i \<noteq> det ms ta ! j"

definition "det_differ_inside ms \<equiv> \<forall>i j t . t<T_max \<and> det ms t \<noteq> [] \<and>
                                    i<length(det ms t) \<and> j<length(det ms t) \<and> j\<noteq>i
                           \<longrightarrow> det ms t ! i \<noteq> det ms t ! j"

definition "own\<^sub>W_and_det_things ms \<equiv> \<forall> t i. t<T_max \<and> i<length(det ms t) \<and> det ms t \<noteq> []\<longrightarrow>
                                    own\<^sub>W ms (det ms t!i) = Some t"

(*!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!missing!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
definition "s_loc_rule ms \<equiv> \<forall>t ta. t<T_max \<and> ta<T_max
                                 \<and> (s ms t \<noteq> None \<and> t\<in> own\<^sub>R ms (the(s ms t)))
                            \<longrightarrow> the(s ms t) \<notin> (detaddrs ms ta)"
(*!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!missing!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)

definition "general_structure ms \<equiv> n_differ ms
                                   \<and> n_differ_from_s_outside ms 
                                   \<and> n_differ_from_s_inside ms 
                                   \<and> s_differ_from_det_inside ms 
                                   \<and> n_differ_from_det ms 
                                   \<and> det_differ_from_det ms 
                                   \<and> det_differ_inside ms 
                                   \<and> own\<^sub>W_and_det_things ms"
                                       
lemmas general_structure_lemmas = general_structure_def
                                  s_loc_rule_def s_differ_from_det_inside_def
                                  n_differ_def n_differ_from_s_outside_def 
                                  n_differ_from_s_inside_def
                                  n_differ_from_det_def
                                  det_differ_from_det_def det_differ_inside_def
                                  own\<^sub>W_and_det_things_def


definition "testingtesting ms \<equiv> \<forall>t. n ms t \<noteq>None \<longrightarrow> (Some t = own\<^sub>W ms (the(n ms t)) \<longleftrightarrow> n_dec ms t)"

lemma testttt1: "n ms t \<noteq> None  \<and> the(n ms t) = L \<Longrightarrow> n ms t = Some L" 
  by fastforce

lemma testttt2: " n ms t = Some L \<Longrightarrow> (\<exists>y. n ms t = Some y)  \<and> the(n ms t) = L" 
  by fastforce





(*write_capability ownership constraints*)

definition "own\<^sub>W_n_by_t_imp ms \<equiv> \<forall>t loc . (t<T_max \<and> n ms t = Some loc) \<longrightarrow> 
                           (n_dec ms t \<longleftrightarrow> own\<^sub>W ms loc = Some t)"

lemma "((n_dec ms t \<and> n ms t \<noteq> None) \<longrightarrow> own\<^sub>W ms (the(n ms t)) = Some t) 
                                      =  
    ((own\<^sub>W ms (the(n ms t)) \<noteq> Some t) \<longrightarrow> (\<not>n_dec ms t \<or> n ms t = None))"
  apply simp
  by auto

lemma "allocated_addresses ms ps \<Longrightarrow> isfree_addr loc ps \<Longrightarrow>
  \<forall>t. t<T_max \<longrightarrow> ((n ms t) \<noteq> Some loc \<or>(\<not>n_dec ms t))"
  apply(simp add:allocated_addresses_lemmas) 
  by auto

lemma pecpec1: "isfree_addr loc ps \<Longrightarrow>own\<^sub>W_n_by_t_imp ms \<Longrightarrow>
 allocated_n_addr ms ps \<Longrightarrow> n_dec ms t \<Longrightarrow> n ms t \<noteq> None \<Longrightarrow> t<T_max \<Longrightarrow> n ms t \<noteq> Some loc"
  apply (simp add:allocated_addresses_lemmas own\<^sub>W_n_by_t_imp_def)
  by blast



definition "counter2_rule ms \<equiv> \<forall>ta loc t. ta < T_max \<and> t<T_max \<and> ta\<noteq>t 
                                        \<and> ta<CTRsync\<^sub>2 ms t \<and> loc\<in>detaddrs ms t
                                     \<longrightarrow> ta\<notin>own\<^sub>R ms loc"



definition "counter1_rule ms \<equiv> \<forall>t t' loc. t\<noteq>t' \<and> t<T_max \<and> t'<T_max 
                              \<and> t'<CTRsync\<^sub>1 ms t \<and> r ms t t' = 0 \<and> loc\<in>detaddrs ms t
                        \<longrightarrow> t' \<notin> own\<^sub>R ms loc"

definition "CTRsync_2_wm_rule ms \<sigma>\<equiv> \<forall>t t' loc. t'\<noteq> t \<and> t'<T_max \<and> t<T_max
                                              \<and> t'\<ge>CTRsync\<^sub>2 ms t \<and> loc\<in>detaddrs ms t 
                                              \<and> [(rcu_0+t') =\<^sub>t 0] \<sigma>
                  \<longrightarrow>  t' \<notin> own\<^sub>R ms loc"

definition "CTRsync_1_wm_rule ms \<sigma>\<equiv> \<forall>t t' loc. t'\<noteq> t \<and> t'<T_max \<and> t<T_max
                                              \<and> t'\<ge>CTRsync\<^sub>1 ms t \<and> loc\<in>detaddrs ms t 
                                              \<and> [(rcu_0+t') =\<^sub>t 0] \<sigma>
                  \<longrightarrow>  t' \<notin> own\<^sub>R ms loc"



lemma checkRown:
  "counter2_rule ms \<Longrightarrow> t<T_max \<Longrightarrow> 
t\<in>own\<^sub>R ms loc \<Longrightarrow> CTRsync\<^sub>2 ms t = T_max \<Longrightarrow> loc\<in>detaddrs ms t 
  \<Longrightarrow> \<nexists>t. t\<ge>T_max \<and> t\<in> own\<^sub>R ms loc
  \<Longrightarrow> own\<^sub>R ms loc = {t}"
  apply(simp add:counter2_rule_def) 
  by (metis insert_absorb is_singletonI' is_singleton_the_elem nat_le_linear nat_less_le singleton_insert_inj_eq)



(*
\<lbrace> [rcu[t] =\<^sub>t 0] \<rbrace>

 rcu[t] := 1                     **I5**         \<parallel>
                                                \<parallel>
   \<lbrace> [rcu[t] =\<^sub>t 1] \<rbrace>                            \<parallel>
                                                \<parallel>
  rcu[t] := 0                    **I6**         \<parallel>     rcu[t'] := 0
                                                \<parallel>
   \<lbrace> [rcu[t] =\<^sub>t 0] \<rbrace>                             \<parallel>       
                                                \<parallel>
  rcu[t] := 1                    **I7**         \<parallel>     rcu[t'] := 1 
                                                \<parallel>
  \<lbrace> [rcu[t] =\<^sub>t 1]  \<rbrace>                             \<parallel>    \<lbrace> [rcu[t'] =\<^sub>t\<^sub>' 1] \<rbrace>
                                                \<parallel>
  \<lbrace> \<forall> t' u. cvd(C, u)                           \<parallel>    \<lbrace> \<forall> t'' u. cvd(C, v) 
        \<and> t'\<in> own\<^sub>R ms u \<longrightarrow>                     \<parallel>          \<and> t''\<in> own\<^sub>R ms v \<longrightarrow>    
        [[C = u]]_t\<lparr>rcu[t'] =\<^sub>t 1\<rparr>   \<rbrace>            \<parallel>          [[C = v]]_t\<lparr>rcu[t''] =\<^sub>t\<^sub>' 1\<rparr>   \<rbrace>
                                                \<parallel>
                                                \<parallel>
  s\<^sub>t \<longleftarrow>\<^sup>F\<^sup>A\<^sup>A\<^sup>Z C                     **I8**        \<parallel>      s\<^sub>t\<^sub>' \<longleftarrow>\<^sup>F\<^sup>A\<^sup>A\<^sup>Z C 
                                                \<parallel>
  \<lbrace> [rcu[t] =\<^sub>t 1] \<rbrace>                             \<parallel>    \<lbrace> [rcu[t'] =\<^sub>t\<^sub>' 1] \<rbrace>  
                                                \<parallel>
  \<lbrace> (t'\<in> own\<^sub>R ms s\<^sub>t \<longrightarrow> [rcu[t'] =\<^sub>t 1])          \<parallel>   \<lbrace> (t''\<in> own\<^sub>R ms s\<^sub>t\<^sub>' \<longrightarrow> [rcu[t''] =\<^sub>t\<^sub>' 1])
     \<and> (\<forall> t' u. cvd(C, u)                       \<parallel>      \<and> (\<forall> t'' u. cvd(C, u)       
               \<and> t'\<in> own\<^sub>R ms u \<longrightarrow>              \<parallel>                \<and> t''\<in> own\<^sub>R ms u \<longrightarrow>    
                  [[C = u]]_t\<lparr>rcu[t'] =\<^sub>t 1\<rparr>)\<rbrace>    \<parallel>                   [[C = u]]_t\<lparr>rcu[t''] =\<^sub>t\<^sub>' 1\<rparr>)\<rbrace>
                                                \<parallel>
   CAS\<^sup>R\<^sup>A( &C, s\<^sub>t, n\<^sub>t)              **I11**       \<parallel>      CAS\<^sup>R\<^sup>A( &C, s\<^sub>t\<^sub>', n\<^sub>t\<^sub>')
                                                \<parallel>
  \<lbrace> [rcu[t] =\<^sub>t 1] \<rbrace>                             \<parallel>    \<lbrace> [rcu[t'] =\<^sub>t\<^sub>' 1] \<rbrace>  
                                                \<parallel>
  \<lbrace> t'\<in> own\<^sub>R ms s\<^sub>t \<longrightarrow> [rcu[t'] =\<^sub>t 1] \<rbrace>          \<parallel>   \<lbrace> t''\<in> own\<^sub>R ms s\<^sub>t\<^sub>' \<longrightarrow> [rcu[t''] =\<^sub>t\<^sub>' 1] \<rbrace>
                                                \<parallel>
                                                \<parallel>
  rcu[t] := 0                    **I12**        \<parallel>     rcu[t'] := 0
                                                \<parallel>
                                                \<parallel>
  \<lbrace> t'\<in> own\<^sub>R ms s\<^sub>t \<longrightarrow> [rcu[t'] =_t 1] \<rbrace>         \<parallel>
                                                \<parallel>
 4 reg\<^sub>t <-- rcu[t']              **S3**         \<parallel>     reg\<^sub>t' <-- rcu[t]       








    d := 0            ||        e := 0   
                      ||
    d := 1            ||        e := 1     
                      ||
  1  Fenced_Chunk (f) ||    2  3  Fenced_Chunk (s)   ****version 1****
  2  Fenced_Chunk (f) ||    1  3  Fenced_Chunk (s)   ****version 2****
                      ||
    d := 0            ||        e := 0   
                      ||
                      ||        while reg = 1
                      ||          reg \<leftarrow> d
                      ||
    d := 1            ||
                      ||
    Fenced_Chunk (f/s)||
                      ||
    d := 0            ||


Fenced_Chunk starts on line I8 and finished with execution of line I11
hence:  {Pre(I8)}   \<equiv> {Pre(Fenced_Chunk)}
and:    {Post(I11)} \<equiv> {Post(Fenced_Chunk)}


Pre(I8) in WM is two-fold:


shows_WM_local_corr_1
\<lbrace> [rcu[t] =\<^sub>t 1] \<rbrace>                                                         ""local""
\<lbrace> \<forall> t' u. cvd(C, u) \<and> t'\<in> own\<^sub>R ms u \<longrightarrow> [C = u]\<lparr>rcu[t'] =\<^sub>t 1\<rparr>  \<rbrace>          ""global""



Chunk invariant:

shows_WM_local_corr_1
\<lbrace> [rcu[t] =\<^sub>t 1] \<rbrace>                                                         ""local""
\<lbrace> (\<forall> t' u. cvd(C, u) \<and> t'\<in> own\<^sub>R ms u \<longrightarrow> [C = u]\<lparr>rcu[t'] =\<^sub>t 1\<rparr>)           ""global""
   \<or> (\<forall>t'. cvd(C,s\<^sub>t) \<and> t'\<in> own\<^sub>R ms s\<^sub>t\<longrightarrow> [rcu[t'] =\<^sub>t 1])  \<rbrace>


Post(I11) in WM is two-fold:

shows_WM_local_corr_1
\<lbrace> [rcu[t] =\<^sub>t 1] \<rbrace>                                                         ""local""
\<lbrace> \<forall>t'. t'\<in> own\<^sub>R ms s\<^sub>t \<longrightarrow> [rcu[t'] =\<^sub>t 1] \<rbrace>                                     ""global""


*)


lemma Failed_CAS_preserves_d_obs_1:
  assumes "[x =\<^sub>t u] \<sigma>"
    and "\<sigma>' = read_trans t False w \<sigma>"
    and "w \<in> visible_writes \<sigma> t l"
    and "x \<noteq> l"
  shows "[x =\<^sub>t u] \<sigma>'"
  using assms
  apply(simp add:cas_step_def CAS_def) 
  apply(simp add:d_obs_t_def d_obs_def)
  by (metis lastWr_read_pres)



lemma Failed_CAS_preserves_d_obs_3:
  assumes "[x =\<^sub>t u] \<sigma>"
  and " w \<in> visible_writes \<sigma> t l "
  and "l \<noteq> x"
  and "\<sigma>' = read_trans t False w \<sigma>"
shows "[x =\<^sub>t u] \<sigma>'"
  using assms 
  by (metis Failed_CAS_preserves_d_obs_1)
  


lemma relating_step_to_update_trans_1:
  assumes "\<sigma>' = update_trans t w nv' \<sigma> ts'"
  and "k = value \<sigma> w"
  and "w \<notin> covered \<sigma>"
  and "valid_fresh_ts \<sigma> w ts'"
  and "w \<in> visible_writes \<sigma> t l"
  shows "OpSem.step t (Update l k nv') \<sigma> \<sigma>'"
  using assms apply (simp add:OpSem.step_def) 
  by (metis prod.exhaust_sel)
  


lemma d_obs_other_representation_2: \<comment> \<open>Rule: DV-Other\<close>
  assumes "wfs \<sigma>"
  and "[x =\<^sub>t u] \<sigma>"
  and "w \<in> visible_writes \<sigma> t l"
  and "w \<notin> covered \<sigma>"
  and "valid_fresh_ts \<sigma> w ts'"
  and "\<sigma>' = update_trans t w nv' \<sigma> ts'" 
  and "l \<noteq> x"
  shows "[x =\<^sub>t u] \<sigma>'"
  using assms d_obs_other
  by (metis avar.simps(3) relating_step_to_update_trans_1) 


lemma Succ_CAS_preserves_d_obs_1:
  assumes "[x =\<^sub>t u] \<sigma>"
    and " w \<in> visible_writes \<sigma> t l"
    and " w \<notin> covered \<sigma>"
    and "valid_fresh_ts \<sigma> w ts'"
    and "wfs \<sigma>"
    and "\<sigma>' = update_trans t w nv' \<sigma> ts'"
    and "x \<noteq> l"
  shows "[x =\<^sub>t u] \<sigma>'"
  using assms 
  by (metis d_obs_other_representation_2)








lemma CAS_preserves_d_obs_7:
  assumes "[(rcu_0 + t) =\<^sub>t u] \<sigma>"
  and "cas_step t C cv nv \<sigma> \<sigma>'"
  and "C \<noteq> (rcu_0 + t)"
  and "wfs \<sigma>"
shows "[(rcu_0 + t) =\<^sub>t u] \<sigma>'"
  using assms apply(simp add:cas_step_def CAS_def) apply clarsimp
  apply(case_tac "value \<sigma> (a, b) = cv", simp_all)
  prefer 2 
  apply (meson Failed_CAS_preserves_d_obs_3) 
  using d_obs_other_representation_2 by blast


lemma CAS_preserves_d_obs_8:
  assumes "[(rcu_0 + t) =\<^sub>t u] \<sigma>"
  and "cas_step_rcu ms \<sigma> t l cv nv ms' \<sigma>'"
  and "C \<noteq> (rcu_0 + t)"
  and "wfs \<sigma>"
shows "cas_step t l cv nv \<sigma> \<sigma>'"
  using assms apply(simp add:cas_step_rcu_def cas_step_def CAS_def) apply clarsimp
  apply(case_tac "value \<sigma> (a, b) = cv", simp_all)
  prefer 2 
  apply (meson Failed_CAS_preserves_d_obs_3) 
  apply blast  
  by blast



lemma CAS_preserves_d_obs_9:
  assumes "[(rcu_0 + t) =\<^sub>t u] \<sigma>"
  and "cas_step_rcu ms \<sigma> t C cv nv ms' \<sigma>'"
  and "C \<noteq> (rcu_0 + t)"
  and "wfs \<sigma>"
shows "[(rcu_0 + t) =\<^sub>t u] \<sigma>'"
  using assms apply(subgoal_tac "cas_step t C cv nv \<sigma> \<sigma>'", simp_all)
  using CAS_preserves_d_obs_7 apply blast
  by (simp add: CAS_preserves_d_obs_8)







lemma shows_WM_local_corr_1:
  " pre_cond \<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>' \<Longrightarrow>
  wfs \<sigma> \<Longrightarrow> cvd[C, u] \<sigma> \<Longrightarrow> the (n ms t)\<noteq>(rcu_0+t) \<Longrightarrow> C \<noteq> (rcu_0 + t) \<Longrightarrow>
((pre_step \<in> {I5,I7}         \<and> pre_cond = [(rcu_0 + t) =\<^sub>t 0] \<sigma>) \<longrightarrow>  [(rcu_0 + t) =\<^sub>t 1] \<sigma>') \<and>
((pre_step \<in> {I6}            \<and> pre_cond = [(rcu_0 + t) =\<^sub>t 1] \<sigma>) \<longrightarrow>  [(rcu_0 + t) =\<^sub>t 0] \<sigma>') \<and>
((pre_step \<in> {I8,I9,I10,I11} \<and> pre_cond = [(rcu_0 + t) =\<^sub>t 1] \<sigma>) \<longrightarrow>  [(rcu_0 + t) =\<^sub>t 1] \<sigma>')"
  apply(simp add:step_def abbr)
  apply(case_tac pre_step, simp_all add:abbr)
  apply (metis d_obs_WrX_set)
  apply (meson d_obs_WrX_set)
  using d_obs_WrX_set apply blast
     defer
  apply (metis d_obs_RdX_other d_obs_RdX_pres)
  apply (metis d_obs_WrX_other)
  apply(clarify)
  using CAS_preserves_d_obs_9 apply blast
  apply(simp add:get_C_val_def)
  by (metis FAAZ_def d_obs_other_representation_2 fst_conv)






lemma shows_WM_local_corr_2:
  " cvd[C, u] \<sigma> \<and> ta\<in> own\<^sub>R ms u \<longrightarrow>  [[C = u]]\<^sub>t\<lparr>(rcu_0+ta) = 1\<rparr> \<sigma>  
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>' \<Longrightarrow>
  wfs_2 \<sigma> \<Longrightarrow> cvd[C, u] \<sigma> \<Longrightarrow>
pre_step \<in> {I7} \<Longrightarrow> (rcu_0 + t) \<noteq> C \<Longrightarrow> (rcu_0 + ta) \<noteq> C \<Longrightarrow> t \<noteq> ta
  \<Longrightarrow>  cvd[C, u] \<sigma>' \<and> ta\<in> own\<^sub>R ms' u \<Longrightarrow>  [[C = u]]\<^sub>t\<lparr>(rcu_0+ta) = 1\<rparr> \<sigma>'"
  apply (simp_all add:step_def abbr wfs_2_def)
  apply safe 
  by (metis add_left_cancel c_obs_last_WrX_diff_pres wfs_2_def)





lemma testingthisone3:
  "[C =\<^sub>t u] \<sigma> \<Longrightarrow> wfs \<sigma> \<Longrightarrow>
  \<forall> w \<in> visible_writes \<sigma> t C . value \<sigma> w = u"
  using d_obs_p_obs_agree p_obs_def by blast


lemma testingthisone4:
  "[C =\<^sub>t u] \<sigma> \<Longrightarrow> wfs \<sigma> \<Longrightarrow> \<forall> w \<in> visible_writes \<sigma> t C. value \<sigma> w = u \<longrightarrow>
                         d_obs \<sigma> (modView \<sigma> w) y k \<Longrightarrow>
  \<forall> w \<in> visible_writes \<sigma> t C. d_obs \<sigma> (modView \<sigma> w) y k"
  using testingthisone3 by auto


lemma testingthisone5:
  "[C =\<^sub>t u] \<sigma> \<Longrightarrow> wfs \<sigma> \<Longrightarrow> [[C = u]]\<^sub>t\<lparr>y = k\<rparr> \<sigma> \<Longrightarrow>
  \<forall> w \<in> visible_writes \<sigma> t C. d_obs \<sigma> (modView \<sigma> w) y k" 
  by (metis c_obs_last_def d_obs_lastWr_visible testingthisone3)

lemma testingthisone6:
  "[C =\<^sub>t u] \<sigma> \<Longrightarrow> wfs \<sigma> \<Longrightarrow> [[C = u]]\<^sub>t\<lparr>y = k\<rparr> \<sigma> \<Longrightarrow>
view y = (lastWr \<sigma> y) \<Longrightarrow>
  d_obs \<sigma> view y k"
  by (simp add: c_obs_last_def d_obs_def d_obs_t_def)


lemma testingthisone7:
  "[x =\<^sub>t u] \<sigma> \<Longrightarrow> wfs \<sigma> \<Longrightarrow> [[x = u]]\<^sub>t\<lparr>y = k\<rparr> \<sigma> \<Longrightarrow>
(thrView \<sigma> t) y = (lastWr \<sigma> y) \<Longrightarrow>
  d_obs_t \<sigma> t y k" 
  by (simp add: c_obs_last_def d_obs_def d_obs_t_def)

lemma testingthisone8:
  "\<exists> w ts'.
                                      w \<in> visible_writes \<sigma> t x \<and>
                                      w \<notin> covered \<sigma> \<and>
                                      valid_fresh_ts \<sigma> w ts' \<and>
update_trans t w (value \<sigma> w) \<sigma> ts' = \<sigma>' \<Longrightarrow>
  [x =\<^sub>t u] \<sigma> \<Longrightarrow> wfs \<sigma> \<Longrightarrow> [[x = u]]\<^sub>t\<lparr>y = k\<rparr> \<sigma> \<Longrightarrow>
(thrView \<sigma>' t) y = (lastWr \<sigma>' y) " 
  by (metis c_obs_UpRA_d_obs c_obs_def c_obs_last_def d_obs_RMW_set d_obs_def d_obs_lastWr_visible d_obs_t_def relating_step_to_update_trans_1)
  


lemma testingthisone10:
  "get_C_val ms \<sigma> t ms' \<sigma>' \<Longrightarrow> [C =\<^sub>t u] \<sigma> \<Longrightarrow> [[C = u]]\<^sub>t\<lparr>y = k\<rparr> \<sigma>  \<Longrightarrow> wfs \<sigma> 
\<Longrightarrow> (thrView \<sigma>' t) y = (lastWr \<sigma>' y) "
  apply (simp add:get_C_val_def FAAZ_def)
  using testingthisone8 [where x = C]
  by blast




lemma FAAZ_expanded_is_Up:
  "wfs \<sigma> \<Longrightarrow> 
w \<in> visible_writes \<sigma> t x \<Longrightarrow> 
w \<notin> covered \<sigma> \<Longrightarrow> 
valid_fresh_ts \<sigma> w ts' \<Longrightarrow> 
\<sigma>' = update_trans t w u \<sigma> ts'
\<Longrightarrow> cvd[x, u] \<sigma> 
\<Longrightarrow>  OpSem.step t (Update x u u) \<sigma> \<sigma>'"
  apply(simp add:OpSem.step_def)
  by (metis Up_reads_cvd_v eq_fst_iff relating_step_to_update_trans_1)
  
lemma FAAZ_step_is_Up:
  "wfs \<sigma> \<Longrightarrow> 
get_C_val ms \<sigma> t ms' \<sigma>'
\<Longrightarrow> cvd[C, u] \<sigma> 
\<Longrightarrow>  OpSem.step t (Update C u u) \<sigma> \<sigma>'"
  apply(simp add:get_C_val_def FAAZ_def)
  using Up_reads_cvd_v relating_step_to_update_trans_1 by blast






lemma shows_WM_local_corr_supp2:
  " cvd[C, u] \<sigma> \<longrightarrow>  [[C = u]]\<^sub>t\<lparr>y = k\<rparr> \<sigma>  
\<Longrightarrow> OpSem.step t (Update C u u') \<sigma> \<sigma>'
\<Longrightarrow> wfs_2 \<sigma> 
\<Longrightarrow> y\<noteq> C
\<Longrightarrow> cvd[C, u] \<sigma> 
\<Longrightarrow> [y =\<^sub>t k] \<sigma>'"
  apply (simp_all add:step_def abbr get_C_val_def FAAZ_def) 
  using c_obs_last_UpRA_d_obs by auto

lemma shows_WM_local_corr_supp3:
  " cvd[C, u] \<sigma> \<and> ta\<in>own\<^sub>R ms u\<longrightarrow>  [[C = u]]\<^sub>t\<lparr>(rcu_0+ta) = k\<rparr> \<sigma>  
\<Longrightarrow> OpSem.step t (Update C u u) \<sigma> \<sigma>'
\<Longrightarrow> wfs_2 \<sigma> 
\<Longrightarrow> (rcu_0+ta)\<noteq> C
\<Longrightarrow> (rcu_0+t)\<noteq> C
\<Longrightarrow> t\<noteq>ta
\<Longrightarrow> cvd[C, u] \<sigma> 
\<Longrightarrow> ta\<in>own\<^sub>R ms u
\<Longrightarrow> [(rcu_0+ta) =\<^sub>t k] \<sigma>'"
  apply (simp_all add:step_def abbr get_C_val_def FAAZ_def) 
  using shows_WM_local_corr_supp2 by auto



lemma shows_WM_local_corr_supp4:
  " cvd[C, u] \<sigma> \<and> ta\<in>own\<^sub>R ms u\<longrightarrow>  [[C = u]]\<^sub>t\<lparr>(rcu_0+ta) = k\<rparr> \<sigma>  
\<Longrightarrow> get_C_val ms \<sigma> t ms' \<sigma>'
\<Longrightarrow> wfs_2 \<sigma> 
\<Longrightarrow> (rcu_0+ta)\<noteq> C
\<Longrightarrow> (rcu_0+t)\<noteq> C
\<Longrightarrow> t\<noteq>ta
\<Longrightarrow> cvd[C, u] \<sigma> 
\<Longrightarrow> ta\<in>own\<^sub>R ms u
\<Longrightarrow> [(rcu_0+ta) =\<^sub>t k] \<sigma>'"
  apply (simp_all add:step_def abbr get_C_val_def FAAZ_def) 
  using shows_WM_local_corr_supp2 
  by (metis Up_reads_cvd_v relating_step_to_update_trans_1)


lemma shows_WM_local_corr_3:
  " cvd[C, u] \<sigma> \<and> ta\<in>own\<^sub>R ms u\<longrightarrow>  [[C = u]]\<^sub>t\<lparr>(rcu_0+ta) = 1\<rparr> \<sigma>  
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>' \<Longrightarrow>
pre_step \<in> {I8}
\<Longrightarrow> wfs_2 \<sigma> 
\<Longrightarrow> (rcu_0+ta)\<noteq> C
\<Longrightarrow> (rcu_0+t)\<noteq> C
\<Longrightarrow> t\<noteq>ta
\<Longrightarrow> cvd[C, u] \<sigma> 
\<Longrightarrow> ta\<in>own\<^sub>R ms u
\<Longrightarrow> [(rcu_0+ta) =\<^sub>t 1] \<sigma>'"
  apply (simp_all add:step_def abbr get_C_val_def FAAZ_def) 
  using shows_WM_local_corr_supp2 
  by (metis Up_reads_cvd_v relating_step_to_update_trans_1)

lemma c_obs_tdash_Rd_pres_c_obs:
"wfs_2 \<sigma> \<Longrightarrow> cvd[x, u] \<sigma> \<Longrightarrow> [[x = u]]\<^sub>t\<lparr>y = k\<rparr> \<sigma> \<Longrightarrow> z\<noteq>x \<Longrightarrow>
x\<noteq>y \<Longrightarrow>  \<sigma> [w \<leftarrow> z]\<^sub>t' \<sigma>' \<Longrightarrow> [[x = u]]\<^sub>t\<lparr>y = k\<rparr> \<sigma>'" 
  using c_obs_last_RdX_pres 
  by (smt (z3) c_obs_last_def) 

lemma c_obs_t_Rd_pres_c_obs:
"wfs_2 \<sigma> \<Longrightarrow> cvd[x, u] \<sigma> \<Longrightarrow> [[x = u]]\<^sub>t\<lparr>y = k\<rparr> \<sigma> \<Longrightarrow> 
x\<noteq>y \<Longrightarrow>  \<sigma> [w \<leftarrow> y]\<^sub>t' \<sigma>' \<Longrightarrow> [[x = u]]\<^sub>t\<lparr>y = k\<rparr> \<sigma>'" 
  using c_obs_last_RdX_pres 
  by (metis c_obs_tdash_Rd_pres_c_obs)

(*dealing with CAS, has 2 possible outcomes: (pre_block) if fail and (post_block) if succ*)







definition "pre_block t t' u ms \<sigma> \<equiv> cvd[C,u] \<sigma> \<and> t'\<in>own\<^sub>R ms u  \<longrightarrow> [[C = u]]\<^sub>t\<lparr>(rcu_0 + t') = 1\<rparr> \<sigma>"

definition "post_block t t' ms \<sigma> \<equiv> t'\<in> own\<^sub>R ms (the (s ms t)) \<longrightarrow> [(rcu_0+t') =\<^sub>t 1] \<sigma>"

definition "in_block t t' u ms \<sigma> \<equiv> pre_block t t' u ms \<sigma> \<and> post_block t t' ms \<sigma>"



(*
THE FOLLOWING ARE WM OPERATIONS INSIDE CRIT. REGION
AND THEIR PRE/POST CONDITIONS.


FIRST TRY               REPEAT TRY              CAS SUCC

pre_block
I5                                                                          rcu_enter()
pre_block


pre_block               in_block
I6                      I6                                                  rcu_exit()
pre_block               in_block


pre_block               in_block
I7                      I7                                                  rcu_enter()
pre_block               in_block


pre_block               in_block
I8                      I8                                                  FAAZ
in_block                in_block



in_block                in_block                in_block
I11                     I11                     I11                         CAS
in_block                in_block                post_block


                                                in_block
                                                I12                         rcu_exit()
                                                post_block










*)























(*
lemma wmr_unsynced_doesnt_influence_cond:
  "wfs_2 \<sigma> 
\<Longrightarrow> w \<in> visible_writes \<sigma> t C 
\<Longrightarrow> w \<notin> covered \<sigma> 
\<Longrightarrow> valid_fresh_ts \<sigma> w ts' 
\<Longrightarrow> cvd[C,k] \<sigma>
\<Longrightarrow> \<sigma>' = read_trans t False w \<sigma> 
\<Longrightarrow> \<sigma> [u \<leftarrow> C]\<^sub>t \<sigma>'"

*)



(*

dealing with LEAVING the critical region

*)

lemma succ_CAS_I11_pres_post:
" in_block t ta l ms \<sigma>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>' \<Longrightarrow>
pre_step \<in> {I11}
\<Longrightarrow> wfs_2 \<sigma> 

\<Longrightarrow> l = the(s ms t)
\<Longrightarrow> (rcu_0+ta)\<noteq> C
\<Longrightarrow> (rcu_0+t)\<noteq> C
\<Longrightarrow> t\<noteq>ta
\<Longrightarrow> cvd[C, l] \<sigma> 
\<Longrightarrow> CAS_succ ms' t 
\<Longrightarrow> post_block t ta ms' \<sigma>' "
  apply(simp add:step_def cas_step_rcu_def post_block_def)
  apply(simp add:in_block_def wfs_2_def)
  apply(subgoal_tac "post_block t ta ms \<sigma>") prefer 2
  apply blast apply(thin_tac "pre_block t ta (the (s ms t)) ms \<sigma> \<and>
    post_block t ta ms \<sigma>")
  apply clarify apply(simp add:CAS_def) apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  by (metis One_nat_def d_obs_other_representation_2 post_block_def)

lemma fail_CAS_I11_pres_pre:
" in_block t ta l ms \<sigma>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>' \<Longrightarrow>
pre_step \<in> {I11}
\<Longrightarrow> wfs_2 \<sigma> 
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> l \<noteq> the(s ms t)
\<Longrightarrow> (rcu_0+ta)\<noteq> C \<and> (rcu_0+t)\<noteq> C \<and>  t\<noteq>ta
\<Longrightarrow> cvd[C, l] \<sigma> 
\<Longrightarrow> \<not>CAS_succ ms' t 
\<Longrightarrow> pre_block t ta l ms' \<sigma>' "
  apply(simp add:step_def cas_step_rcu_def pre_block_def in_block_def)
  apply clarify apply(simp add:CAS_def) apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all add:wfs_2_def)
  apply(thin_tac "post_block t ta ms \<sigma>")
  apply(subgoal_tac "OpSem.step t (RdX C l) \<sigma> \<sigma>'") prefer 2
  apply(simp add:OpSem.step_def)
  apply clarify apply(case_tac "RdX C l", simp_all)
   apply(simp_all add:read_trans_def rev_app_def Let_def)
  apply (metis RdX_def action.inject(1) covered_v_def subset_iff syncing_def visible_var visible_writes_in_writes wfs_def)
  apply (metis RdX_def isRd.simps(1) isRd.simps(2))
  apply auto
  apply (metis RdX_def isUp.simps(1) isUp.simps(3))
  by (metis RdX_def c_obs_last_Rd_pres c_obs_last_def isRA.simps(1) isRd.simps(1) wfs_2_def)
  
  


lemma fail_CAS_I11_pres_post:
" in_block t ta l ms \<sigma>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>' \<Longrightarrow>
pre_step \<in> {I11}
\<Longrightarrow> wfs_2 \<sigma> 
\<Longrightarrow> l \<noteq> the(s ms t)
\<Longrightarrow> (rcu_0+ta)\<noteq> C
\<Longrightarrow> (rcu_0+t)\<noteq> C
\<Longrightarrow> t\<noteq>ta
\<Longrightarrow> cvd[C, l] \<sigma> 
\<Longrightarrow> \<not>CAS_succ ms' t 
\<Longrightarrow> post_block t ta ms' \<sigma>' "
  apply(simp add:step_def cas_step_rcu_def pre_block_def post_block_def in_block_def)
  apply clarify apply(simp add:CAS_def) apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all) 
  by (meson Failed_CAS_preserves_d_obs_1)

lemma CAS_I11_pres_inblock_or_post:
" in_block t ta l ms \<sigma>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>' 
\<Longrightarrow> pre_step \<in> {I11}
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> wfs_2 \<sigma> 
\<Longrightarrow> (rcu_0+ta)\<noteq> C
\<Longrightarrow> (rcu_0+t)\<noteq> C
\<Longrightarrow> t\<noteq>ta
\<Longrightarrow> cvd[C, l] \<sigma> 
\<Longrightarrow> in_block t ta l ms' \<sigma>' \<or> post_block t ta ms' \<sigma>'"
  apply(case_tac "CAS_succ ms' t")
  apply(subgoal_tac "post_block t ta ms' \<sigma>'") 
  apply blast 
  apply(case_tac "l = the(s ms t) ") 
  using succ_CAS_I11_pres_post
  apply blast
  apply(subgoal_tac "\<not>CAS_succ ms' t ", simp_all)
  apply(simp add:step_def cas_step_rcu_def CAS_def)
  apply clarify
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all)
  apply (simp add: covered_v_def visible_writes_def)
  apply(subgoal_tac "in_block t ta l ms' \<sigma>'", simp_all)
  apply(subgoal_tac "post_block t ta ms' \<sigma>' \<and> pre_block t ta l ms' \<sigma>' ")
  using in_block_def apply blast
  apply(subgoal_tac "l\<noteq>the(s ms t)") prefer 2
  apply(simp add:step_def cas_step_rcu_def CAS_def)
  apply clarify
  apply(case_tac "value \<sigma> (a, b) = the (s ms t)", simp_all) 
  apply (simp add: covered_v_def visible_writes_def)
  apply(intro conjI)
  using fail_CAS_I11_pres_post 
  apply blast
  using fail_CAS_I11_pres_pre
  by blast


(*

dealing with ENTERING the critical region

*)


lemma FAAZ_returns_l_on_s:
" wfs_2 \<sigma> \<Longrightarrow> cvd[C, l] \<sigma>
\<Longrightarrow> w \<in> visible_writes \<sigma> t l 
\<Longrightarrow> valid_fresh_ts \<sigma> w ts'
\<Longrightarrow> w \<notin> covered \<sigma> 
\<Longrightarrow> \<sigma>' = update_trans t w l \<sigma> ts'
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> cvd[C,l] \<sigma>'"
  apply simp using wfs_2_def
  by (metis avar.simps(3) covered_diff_var_pres cvd_RMW_new_cvd relating_step_to_update_trans_1)


lemma I8_first_preserves_pre_block:
  "pre_block t ta l ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> cvd[C, l] \<sigma>          \<comment> \<open>\<not>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I8}
\<Longrightarrow> C \<noteq> (rcu_0 + t) \<and> C \<noteq> (rcu_0 + ta) \<and> ta\<noteq>t  
\<Longrightarrow> pre_block t ta l ms' \<sigma>'
" 
  apply(simp add:pre_block_def step_def) 
  apply(case_tac "ta \<in> own\<^sub>R ms l", simp_all) prefer 2
  apply(subgoal_tac "ta \<notin> own\<^sub>R ms' l", simp_all)
  apply(simp add:get_C_val_def FAAZ_def) apply clarify
  apply(subgoal_tac "value \<sigma> (a, b) = l") prefer 2
  apply(simp add:covered_v_def)
  apply metis
  apply(subgoal_tac "own\<^sub>R ms' l= {x. x = t \<or> x \<in> own\<^sub>R ms l}")
  apply clarify
  apply blast apply simp
  apply(subgoal_tac "ta \<in> own\<^sub>R ms' l", simp_all) prefer 2
  apply(simp add:get_C_val_def FAAZ_def) apply clarify
  apply(subgoal_tac "value \<sigma> (a, b) = l") prefer 2
  apply(simp add:covered_v_def)
  apply (simp add: visible_writes_def)
  apply(subgoal_tac "own\<^sub>R ms' l= {x. x = t \<or> x \<in> own\<^sub>R ms l}")
  apply clarify
  apply blast
  apply simp
  apply blast
  apply(subgoal_tac "cvd[C, l] \<sigma>'") apply clarify
  apply(subgoal_tac "\<sigma> RMW[C,l,l]\<^sub>t \<sigma>'") 
  apply (metis c_obs_last_Up_same_loc_pres_col_global c_obs_last_def x_has_lastWr)
  using FAAZ_step_is_Up wfs_2_def apply blast
  using FAAZ_step_is_Up cvd_RMW_new_cvd wfs_2_def by blast




lemma I8_first_preserves_post_block:
  "pre_block t ta l ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> cvd[C, l] \<sigma>          \<comment> \<open>\<not>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I8}
\<Longrightarrow> C \<noteq> (rcu_0 + t) \<and> C \<noteq> (rcu_0 + ta) \<and> ta\<noteq>t  
\<Longrightarrow> post_block t ta ms' \<sigma>'
" 
  apply(simp add:pre_block_def post_block_def step_def) 
  apply(subgoal_tac "the (s ms' t) = l") prefer 2 apply(simp add:get_C_val_def FAAZ_def)
  apply(simp add:update_trans_def rev_app_def Let_def)
   apply(simp add: These_writes_releasing_def) apply clarify
  apply(case_tac "releasing \<sigma> (a,b)", simp_all) 
  apply (simp add: covered_v_def visible_writes_def)
  apply (simp add: visible_writes_def)
  apply(case_tac "ta \<in> own\<^sub>R ms l", simp_all)
  apply (metis shows_WM_local_corr_supp4)
  apply(subgoal_tac "ta\<notin> own\<^sub>R ms' l")
  apply blast
  apply(simp add:get_C_val_def FAAZ_def)
  by auto
   





lemma I8_second_preserves_pre_block:
  "in_block t ta l ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> cvd[C, l] \<sigma>          \<comment> \<open>repeat\<close>
\<Longrightarrow> l\<noteq>the(s ms t)
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I8}
\<Longrightarrow> C \<noteq> (rcu_0 + t) \<and> C \<noteq> (rcu_0 + ta) \<and> ta\<noteq>t  
\<Longrightarrow> pre_block t ta l ms' \<sigma>'
"  
  using in_block_def I8_first_preserves_pre_block by blast
  

lemma I8_second_preserves_post_block:
  "in_block t ta l ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> cvd[C, l] \<sigma>          \<comment> \<open>repeat\<close>
\<Longrightarrow> l\<noteq>the(s ms t)
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I8}
\<Longrightarrow> C \<noteq> (rcu_0 + t) \<and> C \<noteq> (rcu_0 + ta) \<and> ta\<noteq>t  
\<Longrightarrow> post_block t ta ms' \<sigma>'
"  
  using in_block_def I8_first_preserves_post_block by blast


lemma I8_second_preserves_in_block:
  "in_block t ta l ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> cvd[C, l] \<sigma>          \<comment> \<open>repeat\<close>
\<Longrightarrow> l\<noteq>the(s ms t)
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I8}
\<Longrightarrow> C \<noteq> (rcu_0 + t) \<and> C \<noteq> (rcu_0 + ta) \<and> ta\<noteq>t  
\<Longrightarrow> in_block t ta l ms' \<sigma>'
"  apply (simp add:in_block_def) apply(intro conjI impI)
  using I8_first_preserves_pre_block apply blast
  using I8_first_preserves_post_block by blast







lemma I5_preserves_pre_block:
  "pre_block t ta l ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> cvd[C, l] \<sigma>      
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I5}
\<Longrightarrow> s ms t = None
\<Longrightarrow> C \<noteq> (rcu_0 + t) \<and> C \<noteq> (rcu_0 + ta) \<and> ta\<noteq>t  
\<Longrightarrow> pre_block t ta l ms' \<sigma>'
"  
  apply(simp add:step_def enter_rcu_def)
  apply(simp add:pre_block_def) 
  apply(case_tac "ta \<in> own\<^sub>R ms l", simp_all)
  apply(subgoal_tac " ta \<in> own\<^sub>R ms' l", simp_all)
  apply (metis add_left_imp_eq c_obs_last_WrX_diff_pres)
  using update_pc_def by auto 
  






lemma I6_first_preserves_pre_block:
  "pre_block t ta l ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> cvd[C, l] \<sigma>          \<comment> \<open>\<not>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I6}
\<Longrightarrow> s ms t = None
\<Longrightarrow> \<not>repeat ms t
\<Longrightarrow> C \<noteq> (rcu_0 + t) \<and> C \<noteq> (rcu_0 + ta) \<and> ta\<noteq>t  
\<Longrightarrow> pre_block t ta l ms' \<sigma>'
" apply(simp add:step_def enter_rcu_def)
  apply(simp add:pre_block_def) 
  apply(case_tac "ta \<in> own\<^sub>R ms l", simp_all)
  apply(subgoal_tac " ta \<in> own\<^sub>R ms' l", simp_all) 
  apply (metis abbr(10) add_left_imp_eq c_obs_last_WrX_diff_pres)
  using exit_rcu_def update_pc_def by auto




lemma I6_second_preserves_pre_block:
  "in_block t ta l ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> cvd[C, l] \<sigma>          \<comment> \<open>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I6}
\<Longrightarrow> repeat ms t
\<Longrightarrow> C \<noteq> (rcu_0 + t) \<and> C \<noteq> (rcu_0 + ta) \<and> ta\<noteq>t  
\<Longrightarrow> pre_block t ta l ms' \<sigma>'
" apply(simp add:in_block_def) 
  apply(simp add:step_def enter_rcu_def)
  apply(simp add:pre_block_def) 
  apply(case_tac "ta \<in> own\<^sub>R ms l", simp_all)
  apply(subgoal_tac " ta \<in> own\<^sub>R ms' l", simp_all) 
  apply (metis abbr(10) add_left_imp_eq c_obs_last_WrX_diff_pres)
  using exit_rcu_def giveup_readandwrite_ownership_def update_pc_def by auto


lemma I6_second_preserves_post_block:
  "in_block t ta l ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> cvd[C, l] \<sigma>          \<comment> \<open>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I6}
\<Longrightarrow> repeat ms t
\<Longrightarrow> C \<noteq> (rcu_0 + t) \<and> C \<noteq> (rcu_0 + ta) \<and> ta\<noteq>t  
\<Longrightarrow> post_block t ta ms' \<sigma>'
" apply(simp add:in_block_def) 
  apply(simp add:step_def enter_rcu_def)
  apply(simp add:post_block_def) 
  apply(case_tac "ta \<in> own\<^sub>R ms (the (s ms t))", simp_all)
  apply(subgoal_tac " ta \<in> own\<^sub>R ms' (the (s ms t))", simp_all) 
  apply (meson abbr(10) add_left_imp_eq d_obs_WrX_other wfs_2_def)
  using exit_rcu_def giveup_readandwrite_ownership_def update_pc_def by auto
  

lemma I6_second_preserves_in_block:
  "in_block t ta l ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> cvd[C, l] \<sigma>          \<comment> \<open>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I6}
\<Longrightarrow> repeat ms t
\<Longrightarrow> C \<noteq> (rcu_0 + t) \<and> C \<noteq> (rcu_0 + ta) \<and> ta\<noteq>t  
\<Longrightarrow> in_block t ta l ms' \<sigma>'
" apply(simp add:in_block_def)
  apply(intro conjI impI)
  using I6_second_preserves_pre_block apply auto 
  using in_block_def apply blast
  using I6_second_preserves_post_block apply auto 
  by (meson in_block_def)




















lemma I7_first_preserves_pre_block:
  "pre_block t ta l ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> cvd[C, l] \<sigma>          \<comment> \<open>\<not>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I7}
\<Longrightarrow> \<not>repeat ms t
\<Longrightarrow> C \<noteq> (rcu_0 + t) \<and> C \<noteq> (rcu_0 + ta) \<and> ta\<noteq>t  
\<Longrightarrow> pre_block t ta l ms' \<sigma>'
" apply(simp add:step_def enter_rcu_def)
  apply(simp add:pre_block_def) 
  apply(case_tac "ta \<in> own\<^sub>R ms l", simp_all)
  apply(subgoal_tac " ta \<in> own\<^sub>R ms' l", simp_all)
  apply (metis add_left_imp_eq c_obs_last_WrX_diff_pres)
  using update_pc_def by auto 




lemma I7_second_preserves_pre_block:
  "in_block t ta l ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> cvd[C, l] \<sigma>          \<comment> \<open>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I7}
\<Longrightarrow> repeat ms t
\<Longrightarrow> C \<noteq> (rcu_0 + t) \<and> C \<noteq> (rcu_0 + ta) \<and> ta\<noteq>t  
\<Longrightarrow> pre_block t ta l ms' \<sigma>'
" apply(simp add:in_block_def)
  apply(simp add:step_def enter_rcu_def)
  apply(simp add:pre_block_def post_block_def) 
  apply(case_tac "ta \<in> own\<^sub>R ms l", simp_all)
  apply(subgoal_tac " ta \<in> own\<^sub>R ms' l", simp_all)
  apply (metis add_left_imp_eq c_obs_last_WrX_diff_pres)
  using update_pc_def by auto 



lemma I7_second_preserves_post_block:
  "in_block t ta l ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> cvd[C, l] \<sigma>          \<comment> \<open>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I7}
\<Longrightarrow> repeat ms t
\<Longrightarrow> C \<noteq> (rcu_0 + t) \<and> C \<noteq> (rcu_0 + ta) \<and> ta\<noteq>t  
\<Longrightarrow> post_block t ta ms' \<sigma>'
" apply(simp add:in_block_def)
  apply(simp add:step_def enter_rcu_def)
  apply(simp add:pre_block_def post_block_def) 
  apply(case_tac "ta \<in> own\<^sub>R ms (the (s ms t))", simp_all)
  apply(subgoal_tac " ta \<in> own\<^sub>R ms' (the (s ms t))", simp_all)  
  apply (metis add_left_imp_eq d_obs_WrX_other wfs_2_def)
  using update_pc_def by auto 


lemma I7_second_preserves_in_block:
  "in_block t ta l ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> cvd[C, l] \<sigma>          \<comment> \<open>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I7}
\<Longrightarrow> repeat ms t
\<Longrightarrow> C \<noteq> (rcu_0 + t) \<and> C \<noteq> (rcu_0 + ta) \<and> ta\<noteq>t  
\<Longrightarrow> in_block t ta l ms' \<sigma>'
" apply(simp add:in_block_def)
  apply(intro conjI impI)
  using I7_second_preserves_pre_block in_block_def apply blast
  using I7_second_preserves_post_block in_block_def by blast
  






lemma I12_preserves_post_block:
  "post_block t ta ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> These_writes_releasing \<sigma> C
\<Longrightarrow> cvd[C, l] \<sigma>          \<comment> \<open>repeat\<close>
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> pre_step \<in> {I12}
\<Longrightarrow> C \<noteq> (rcu_0 + t) \<and> C \<noteq> (rcu_0 + ta) \<and> ta\<noteq>t  
\<Longrightarrow> post_block t ta ms' \<sigma>'
" apply(simp add:in_block_def)
  apply(simp add:step_def enter_rcu_def)
  apply(simp add:pre_block_def post_block_def)
  apply(case_tac "ta \<in> own\<^sub>R ms (the (s ms t))", simp_all)
  apply(subgoal_tac " ta \<in> own\<^sub>R ms' (the (s ms t))", simp_all)  
  apply (meson abbr(10) add_left_imp_eq d_obs_WrX_other wfs_2_def)
  using update_pc_def giveup_readandwrite_ownership_def by auto


(*weak memory invariant during reclamation/synchronisation*)


lemma S3_corr_val_preserves_post_block:
  "post_block t ta ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> pre_step \<in> {S3}
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> ta\<noteq>t  
\<Longrightarrow> post_block t ta ms' \<sigma>'"
  apply(case_tac "ta = (CTRsync\<^sub>1 ms t)")
  apply(simp add:step_def load_rcu_to_r_def post_block_def wfs_2_def)
  apply(case_tac "CTRsync\<^sub>1 ms t \<in> own\<^sub>R ms' (the (s ms' t))", simp_all)
  apply clarify apply auto
  apply (meson d_obs_RdX_pres)
  apply(simp add:step_def load_rcu_to_r_def post_block_def wfs_2_def)
  apply clarify apply auto
  by (meson add_left_imp_eq d_obs_RdX_other)


lemma S3_corr_val_preserves_post_sc:
  "post_block t ta ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> pre_step \<in> {S3}
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> ta\<noteq>t  
\<Longrightarrow> r ms t ta = 0
\<Longrightarrow> CTRsync\<^sub>1 ms t = ta
\<Longrightarrow> ta\<in> own\<^sub>R ms (the (s ms t)) \<longrightarrow> r ms' t ta = 1"
  apply(simp add:step_def load_rcu_to_r_def post_block_def wfs_2_def)
  apply(case_tac "CTRsync\<^sub>1 ms t \<in> own\<^sub>R ms' (the (s ms' t))", simp_all)
  apply clarify apply auto
  by (meson d_obs_read_value)


(*do the same for S6*)



lemma S6_corr_val_preserves_post_sc:
  "r ms t t' = 1 \<longrightarrow> post_block t t' ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> pre_step \<in> {S6}
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> r ms' t t' = 1 \<longrightarrow> post_block t t' ms' \<sigma>'"
  apply(simp add:step_def load_rcu_to_r_def post_block_def wfs_2_def rcu_temp_copy_def)
  apply clarify apply auto 
  by (metis d_obs_RdX_other d_obs_RdX_pres)
  

lemma S6_corr_val_preserves_post_sc_2:
  "r ms t ta = 1 \<longrightarrow> post_block t ta ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> pre_step \<in> {S6}
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> r ms t ta = 1 
\<Longrightarrow> post_block t ta ms' \<sigma>'"
  apply(subgoal_tac "r ms' t ta = 1") prefer 2
  apply(simp add:step_def rcu_temp_copy_def) apply auto
  by (metis One_nat_def S6_corr_val_preserves_post_sc insertI1)


lemma S6_corr_val_preserves_post_sc_3:
  "r ms t ta = 1 \<longrightarrow> post_block t ta ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> pre_step \<in> {S6}
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> r ms t ta = 1 
\<Longrightarrow> ta \<in> own\<^sub>R ms (the (s ms t))
\<Longrightarrow> [(rcu_0+ta) =\<^sub>t 1] \<sigma>'"
  apply (simp add:post_block_def) 
  apply(subgoal_tac "r ms' t ta = 1") prefer 2 apply(simp add:step_def rcu_temp_copy_def) apply auto
  apply(subgoal_tac "ta \<in> own\<^sub>R ms' (the (s ms' t))") prefer 2 apply(simp add:step_def rcu_temp_copy_def) apply auto
  by (metis One_nat_def S6_corr_val_preserves_post_sc insertI1 post_block_def)
  

lemma S6_corr_val_preserves_post_sc_4:
  "r ms t ta = 1 \<longrightarrow> post_block t ta ms \<sigma>
\<Longrightarrow> wfs_2 \<sigma>
\<Longrightarrow> pre_step \<in> {S6}
\<Longrightarrow> step ms ps \<sigma> (pre_step) t ms' ps' \<sigma>'
\<Longrightarrow> r ms t ta = 1  
\<Longrightarrow> ta = CTRsync\<^sub>2 ms t
\<Longrightarrow> ta \<in> own\<^sub>R ms (the (s ms t)) \<longrightarrow> reg ms' t = 1"
  apply simp
  apply(case_tac "ta \<in> own\<^sub>R ms (the (s ms t))")
  apply(simp add:step_def rcu_temp_copy_def post_block_def wfs_2_def)
  apply(subgoal_tac "[(rcu_0+ta) =\<^sub>t 1] \<sigma>", simp_all add:d_obs_t_def OpSem.step_def)
  apply clarify
  apply(case_tac "RdX (rcu_0 + CTRsync\<^sub>2 ms t) v", simp_all) 
  apply (metis RdX_def action.inject(1) d_obs_p_obs_agree d_obs_t_def p_obs_def)
  apply (metis RdX_def action.distinct(1))
  by (metis RdX_def action.simps(7))

(*the S6 and S3 dependencies MIGHT need revisiting*)








(*-------------------------------------------------------------*)
(*-------------------------------------------------------------*)
(*-----------------RCU free(pop(det)) stuff--------------------*)
(*-------------------------------------------------------------*)
(*-------------------------------------------------------------*)












end