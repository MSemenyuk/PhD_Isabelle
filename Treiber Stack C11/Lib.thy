theory Lib
imports OpSem 
begin

datatype VARS = CVARS | LVARS

record lib_write_record =
  lib_val :: V
  lib_rel :: bool

record lib_state =
  lib_writes :: "(L \<times> TS) set"
  lib_thrView :: "T \<Rightarrow> L \<Rightarrow> (L \<times> TS)"
  lib_modView :: "(L \<times> TS) \<Rightarrow> VARS \<Rightarrow> L \<Rightarrow> (L \<times> TS)"
  lib_mods :: "(L \<times> TS) \<Rightarrow> lib_write_record"
  lib_covered :: "(L \<times> TS) set"

definition 
  "lib_update_thrView t nv \<sigma> \<equiv> \<sigma> \<lparr> lib_thrView := (lib_thrView \<sigma>)(t := nv)\<rparr>"

definition 
  "lib_update_modView w cv lv \<sigma> \<equiv> \<sigma> \<lparr>lib_modView  := (lib_modView \<sigma>)(w := (lib_modView \<sigma> w) (CVARS := cv, LVARS := lv))\<rparr>"

definition 
  "lib_update_mods w nwr \<sigma> \<equiv> \<sigma> \<lparr> lib_mods := (lib_mods \<sigma>)(w := nwr)\<rparr> \<lparr>lib_writes := lib_writes \<sigma> \<union> {w}\<rparr>"

definition 
  "lib_add_cv w \<sigma> \<equiv> \<sigma> \<lparr> lib_covered := lib_covered \<sigma> \<union> {w}\<rparr>"



definition "lib_value \<sigma> w \<equiv>  lib_val (lib_mods \<sigma> w)"
definition "lib_releasing \<sigma> w \<equiv>  lib_rel (lib_mods \<sigma> w)"
definition "lib_syncing \<sigma> w b \<equiv> lib_releasing \<sigma> w \<and> b"
definition "lib_writes_on \<sigma> x = {w . var w = x \<and> w \<in> lib_writes \<sigma>}"
definition "lib_visible_writes \<sigma> t x \<equiv> {w \<in> lib_writes_on \<sigma> x . tst(lib_thrView \<sigma> t x) \<le> tst w}"
definition "lib_valid_fresh_ts \<sigma> w ts' \<equiv> tst w < ts' \<and> (\<forall> w' \<in> lib_writes_on \<sigma> (var w). tst w < tst w' \<longrightarrow> ts' < tst w')"
definition "lib_lastWr \<sigma> x \<equiv> (x, Max (tst`(lib_writes_on \<sigma> x)))"

definition
  "lib_wfs \<sigma>\<^sub>L \<sigma>\<^sub>C \<equiv>
      (\<forall> t x. lib_thrView \<sigma>\<^sub>L t x \<in> lib_writes_on \<sigma>\<^sub>L x) \<and>
      (\<forall> w x. lib_modView \<sigma>\<^sub>L w CVARS x \<in> writes_on \<sigma>\<^sub>C x) \<and>
      (\<forall> w x. lib_modView \<sigma>\<^sub>L w LVARS x \<in> lib_writes_on \<sigma>\<^sub>L x) \<and>
      (\<forall> x . finite(lib_writes_on \<sigma>\<^sub>L x)) \<and>
      (lib_covered \<sigma>\<^sub>L \<subseteq> lib_writes \<sigma>\<^sub>L) \<and>
      (\<forall> w. w \<in> lib_writes \<sigma>\<^sub>L \<longrightarrow> lib_modView \<sigma>\<^sub>L w  LVARS (var w) = w) \<and>
      (\<forall> w x . w = lib_lastWr \<sigma>\<^sub>L x \<longrightarrow> w \<notin> lib_covered \<sigma>\<^sub>L) \<and>
      (\<forall> w l . tst(lib_modView \<sigma>\<^sub>L w CVARS l) \<le> tst(lastWr \<sigma>\<^sub>C l))"

definition "lib_write t b w v \<sigma>\<^sub>L \<sigma>\<^sub>C ts' \<equiv>
           \<sigma>\<^sub>L ;; lib_update_thrView t ((lib_thrView \<sigma>\<^sub>L t)(var w := (var w, ts')))
              ;; lib_update_modView (var w, ts') (thrView \<sigma>\<^sub>C t) ((lib_thrView \<sigma>\<^sub>L t)(var w := (var w, ts')))
              ;; lib_update_mods (var w, ts') \<lparr>lib_val = v, lib_rel = b\<rparr>" 




definition "lib_read t b w \<sigma>\<^sub>L \<sigma>\<^sub>C \<equiv>
           let new_thr_idx = (lib_thrView \<sigma>\<^sub>L t)(var w := w) in
            let 
              new_thr_view_client =  if lib_syncing \<sigma>\<^sub>L w b then  ts_oride (thrView \<sigma>\<^sub>C t) (lib_modView \<sigma>\<^sub>L w CVARS) else (thrView \<sigma>\<^sub>C t);
              new_thr_view_lib =  if lib_syncing \<sigma>\<^sub>L w b then  ts_oride new_thr_idx (lib_modView \<sigma>\<^sub>L w LVARS) else new_thr_idx
            in
              (\<sigma>\<^sub>L ;; lib_update_thrView t new_thr_view_lib, \<sigma>\<^sub>C ;; update_thrView t new_thr_view_client)"


definition "lib_update t w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts' \<equiv> 
       let new_thr_idx = (lib_thrView \<sigma>\<^sub>L t)(var w := (var w, ts')) in
         let new_thr_lib =  if lib_releasing \<sigma>\<^sub>L w then ts_oride new_thr_idx (lib_modView \<sigma>\<^sub>L w LVARS) else new_thr_idx;
             new_thr_client =  if lib_releasing \<sigma>\<^sub>L w then ts_oride (thrView \<sigma>\<^sub>C t)  (lib_modView \<sigma>\<^sub>L w CVARS) else (thrView \<sigma>\<^sub>C t)
         in
              (\<sigma>\<^sub>L ;; lib_update_thrView t new_thr_lib
                  ;; lib_update_modView (var w, ts') new_thr_client new_thr_lib 
                  ;; lib_update_mods (var w, ts') \<lparr>lib_val = v', lib_rel= True\<rparr>
                  ;; lib_add_cv w
              , \<sigma>\<^sub>C ;; update_thrView t new_thr_client)"

definition "lib_update_r t w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts' \<equiv> 
       let new_thr_idx = (lib_thrView \<sigma>\<^sub>L t)(var w := (var w, ts')) in
         let new_thr_lib =  new_thr_idx;
             new_thr_client = (thrView \<sigma>\<^sub>C t)
         in
              (\<sigma>\<^sub>L ;; lib_update_thrView t new_thr_lib
                  ;; lib_update_modView (var w, ts') new_thr_client new_thr_lib 
                  ;; lib_update_mods (var w, ts') \<lparr>lib_val = v', lib_rel= True\<rparr>
                  ;; lib_add_cv w
              , \<sigma>\<^sub>C ;; update_thrView t new_thr_client)"


definition "lib_update_a t w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts' \<equiv> 
       let new_thr_idx = (lib_thrView \<sigma>\<^sub>L t)(var w := (var w, ts')) in
         let new_thr_lib =  if lib_releasing \<sigma>\<^sub>L w then ts_oride new_thr_idx (lib_modView \<sigma>\<^sub>L w LVARS) else new_thr_idx;
             new_thr_client =  if lib_releasing \<sigma>\<^sub>L w then ts_oride (thrView \<sigma>\<^sub>C t)  (lib_modView \<sigma>\<^sub>L w CVARS) else (thrView \<sigma>\<^sub>C t)
         in
              (\<sigma>\<^sub>L ;; lib_update_thrView t new_thr_lib
                  ;; lib_update_modView (var w, ts') new_thr_client new_thr_lib 
                  ;; lib_update_mods (var w, ts') \<lparr>lib_val = v', lib_rel= False\<rparr>
                  ;; lib_add_cv w
              , \<sigma>\<^sub>C ;; update_thrView t new_thr_client)"


definition "lib_update_rx t w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts' \<equiv> 
       let new_thr_idx = (lib_thrView \<sigma>\<^sub>L t)(var w := (var w, ts')) in
         let new_thr_lib =  new_thr_idx;
             new_thr_client = thrView \<sigma>\<^sub>C t
         in
              (\<sigma>\<^sub>L ;; lib_update_thrView t new_thr_lib
                  ;; lib_update_modView (var w, ts') new_thr_client new_thr_lib 
                  ;; lib_update_mods (var w, ts') \<lparr>lib_val = v', lib_rel= False\<rparr>
                  ;; lib_add_cv w
              , \<sigma>\<^sub>C ;; update_thrView t new_thr_client)"


definition "lib_update_gen rel acq t w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts' \<equiv>  if rel \<and> acq then
                                                          lib_update t w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts'
                                                        else 
                                                        if rel \<and> \<not>acq 
                                                        then 
                                                          lib_update_r t w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts' 
                                                        else
                                                        if \<not>rel \<and> acq 
                                                        then
                                                          lib_update_a t w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts'
                                                        else
                                                          lib_update_rx t w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts'"


definition "lib_write_step t x  b \<sigma>\<^sub>L \<sigma>\<^sub>C  \<sigma>\<^sub>L' \<sigma>\<^sub>C' v \<equiv> 
            \<exists> w ts'. w \<in> lib_visible_writes \<sigma>\<^sub>L t x \<and>
             w \<notin> lib_covered \<sigma>\<^sub>L \<and>
             lib_valid_fresh_ts \<sigma>\<^sub>L w ts' \<and>
             \<sigma>\<^sub>L' = lib_write t b w v \<sigma>\<^sub>L \<sigma>\<^sub>C ts' \<and>
             \<sigma>\<^sub>C' =  \<sigma>\<^sub>C"

definition "lib_read_step t x b \<sigma>\<^sub>L \<sigma>\<^sub>C \<sigma>\<^sub>L' \<sigma>\<^sub>C' v \<equiv> 
            \<exists> w . w \<in> lib_visible_writes \<sigma>\<^sub>L t x \<and>
             \<sigma>\<^sub>L' = fst(lib_read t b w \<sigma>\<^sub>L \<sigma>\<^sub>C) \<and>
             \<sigma>\<^sub>C' = snd(lib_read t b w \<sigma>\<^sub>L \<sigma>\<^sub>C) \<and>
             v = lib_value \<sigma>\<^sub>L w"

definition "lib_update_step t x \<sigma>\<^sub>L \<sigma>\<^sub>C  \<sigma>\<^sub>L' \<sigma>\<^sub>C' v v' \<equiv> 
            \<exists> w ts'. w \<in> lib_visible_writes \<sigma>\<^sub>L t x \<and>
             w \<notin> lib_covered \<sigma>\<^sub>L \<and>
             lib_valid_fresh_ts \<sigma>\<^sub>L w ts' \<and>
             lib_value \<sigma>\<^sub>L w = v \<and>
             \<sigma>\<^sub>L' = fst(lib_update t w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts') \<and>
             \<sigma>\<^sub>C' = snd(lib_update t w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts')"

definition "lib_CAS_step t x \<sigma>\<^sub>L \<sigma>\<^sub>C  \<sigma>\<^sub>L' \<sigma>\<^sub>C' v v' res \<equiv> 
            \<exists> w ts'. w \<in> lib_visible_writes \<sigma>\<^sub>L t x \<and>
             w \<notin> lib_covered \<sigma>\<^sub>L \<and>
             lib_valid_fresh_ts \<sigma>\<^sub>L w ts' \<and>
             (if lib_value \<sigma>\<^sub>L w = v 
              then
                 \<sigma>\<^sub>L' = fst(lib_update t w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts') \<and>
                 \<sigma>\<^sub>C' = snd(lib_update t w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts') \<and>
                 res = True
              else
                 \<sigma>\<^sub>L' = fst(lib_read  t False w \<sigma>\<^sub>L \<sigma>\<^sub>C) \<and>
                 \<sigma>\<^sub>C' = snd(lib_read  t False w \<sigma>\<^sub>L \<sigma>\<^sub>C) \<and>
                 res = False)"

definition "lib_CAS_Rel_step t x \<sigma>\<^sub>L \<sigma>\<^sub>C  \<sigma>\<^sub>L' \<sigma>\<^sub>C' v v' res \<equiv> 
            \<exists> w ts'. w \<in> lib_visible_writes \<sigma>\<^sub>L t x \<and>
             w \<notin> lib_covered \<sigma>\<^sub>L \<and>
             lib_valid_fresh_ts \<sigma>\<^sub>L w ts' \<and>
             (if lib_value \<sigma>\<^sub>L w = v 
              then
                 \<sigma>\<^sub>L' = fst(lib_update_r t w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts') \<and>
                 \<sigma>\<^sub>C' = snd(lib_update_r t w v' \<sigma>\<^sub>L \<sigma>\<^sub>C ts') \<and>
                 res = True
              else
                 \<sigma>\<^sub>L' = fst(lib_read  t False w \<sigma>\<^sub>L \<sigma>\<^sub>C) \<and>
                 \<sigma>\<^sub>C' = snd(lib_read  t False w \<sigma>\<^sub>L \<sigma>\<^sub>C) \<and>
                 res = False)"

definition "lib_fetch_and_inc_step t x \<sigma>\<^sub>L \<sigma>\<^sub>C  \<sigma>\<^sub>L' \<sigma>\<^sub>C' res \<equiv> 
            \<exists> w ts' v. w \<in> lib_visible_writes \<sigma>\<^sub>L t x \<and>
             w \<notin> lib_covered \<sigma>\<^sub>L \<and>
             lib_valid_fresh_ts \<sigma>\<^sub>L w ts' \<and>
             lib_value \<sigma>\<^sub>L w = v \<and>
             \<sigma>\<^sub>L' = fst(lib_update t w (v+1) \<sigma>\<^sub>L \<sigma>\<^sub>C ts') \<and>
             \<sigma>\<^sub>C' = snd(lib_update t w (v+1) \<sigma>\<^sub>L \<sigma>\<^sub>C ts') \<and>
             res = v"             



abbreviation lib_WrX_state_abbr:: "lib_state \<Rightarrow> surrey_state \<Rightarrow> L \<Rightarrow> V \<Rightarrow> T \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool" ("_ _ [lib(_) := _]\<^sub>_ _ _" [100,100,100,100,100,100,100])
  where "\<sigma>\<^sub>L \<sigma>\<^sub>C [lib(x) := v]\<^sub>t \<sigma>\<^sub>L' \<sigma>\<^sub>C' \<equiv> lib_write_step t x False \<sigma>\<^sub>L \<sigma>\<^sub>C  \<sigma>\<^sub>L' \<sigma>\<^sub>C' v"

abbreviation  lib_WrR_state_abbr:: "lib_state \<Rightarrow> surrey_state \<Rightarrow> L \<Rightarrow> V \<Rightarrow> T \<Rightarrow> lib_state \<Rightarrow>surrey_state \<Rightarrow> bool" ("_ _ [lib(_) :=\<^sup>R _]\<^sub>_ _ _" [100,100,100,100,100,100])
  where "\<sigma>\<^sub>L \<sigma>\<^sub>C [lib(x) :=\<^sup>R v]\<^sub>t \<sigma>\<^sub>L' \<sigma>\<^sub>C' \<equiv> lib_write_step t x True \<sigma>\<^sub>L \<sigma>\<^sub>C  \<sigma>\<^sub>L' \<sigma>\<^sub>C' v"

abbreviation  lib_RdX_state_abbr:: "lib_state \<Rightarrow> surrey_state \<Rightarrow> V \<Rightarrow> L \<Rightarrow>  T \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool" ("_ _[_ \<leftarrow> lib(_)]\<^sub>_ _ _" [100,100,100,100,100,100])
  where "\<sigma>\<^sub>L \<sigma>\<^sub>C [r \<leftarrow> lib(x)]\<^sub>t \<sigma>\<^sub>L' \<sigma>\<^sub>C' \<equiv> lib_read_step t x False \<sigma>\<^sub>L \<sigma>\<^sub>C \<sigma>\<^sub>L' \<sigma>\<^sub>C' r"

abbreviation  lock_RdA_state_abbr:: "lib_state \<Rightarrow> surrey_state \<Rightarrow> V \<Rightarrow> L \<Rightarrow>  T \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool" ("_ _ [_ \<leftarrow>\<^sup>A lib(_)]\<^sub>_ _ _" [100,100,100,100,100,100,100])
  where "\<sigma>\<^sub>L \<sigma>\<^sub>C [r \<leftarrow>\<^sup>A lib(x)]\<^sub>t \<sigma>\<^sub>L' \<sigma>\<^sub>C' \<equiv> lib_read_step t x True \<sigma>\<^sub>L \<sigma>\<^sub>C \<sigma>\<^sub>L' \<sigma>\<^sub>C' r"

abbreviation  lock_Up_state_abbr:: "lib_state \<Rightarrow> surrey_state \<Rightarrow> L \<Rightarrow> V \<Rightarrow> V \<Rightarrow> T \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool" ("_ _ RMW[lib(_), _, _]\<^sub>_ _ _" [100,100,100,100,100,100,100,100])
  where "\<sigma>\<^sub>L \<sigma>\<^sub>C RMW[lib(x), v, v']\<^sub>t \<sigma>\<^sub>L' \<sigma>\<^sub>C' \<equiv> lib_update_step t x \<sigma>\<^sub>L \<sigma>\<^sub>C  \<sigma>\<^sub>L' \<sigma>\<^sub>C' v v'"

abbreviation  lock_CAS_state_abbr:: "lib_state \<Rightarrow> surrey_state \<Rightarrow> L \<Rightarrow> bool \<Rightarrow>  V \<Rightarrow> V \<Rightarrow> T \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool" ("_ _ CAS[lib(_), _, _, _]\<^sub>_ _ _" [100,100,100,100,100,100,100,100,100])
  where "\<sigma>\<^sub>L \<sigma>\<^sub>C CAS[lib(x), res, v, v']\<^sub>t \<sigma>\<^sub>L' \<sigma>\<^sub>C' \<equiv> lib_CAS_step t x \<sigma>\<^sub>L \<sigma>\<^sub>C  \<sigma>\<^sub>L' \<sigma>\<^sub>C' v v' res"

abbreviation  lock_CAS_Rel_state_abbr:: "lib_state \<Rightarrow> surrey_state \<Rightarrow> L \<Rightarrow> bool \<Rightarrow>  V \<Rightarrow> V \<Rightarrow> T \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool" ("_ _ CAS\<^sup>R[lib(_), _, _, _]\<^sub>_ _ _" [100,100,100,100,100,100,100,100,100])
  where "\<sigma>\<^sub>L \<sigma>\<^sub>C CAS\<^sup>R[lib(x), res, v, v']\<^sub>t \<sigma>\<^sub>L' \<sigma>\<^sub>C' \<equiv> lib_CAS_Rel_step t x \<sigma>\<^sub>L \<sigma>\<^sub>C  \<sigma>\<^sub>L' \<sigma>\<^sub>C' v v' res"

abbreviation lib_Swap_state_abbr:: "lib_state \<Rightarrow> surrey_state \<Rightarrow> L \<Rightarrow> V \<Rightarrow> T \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool" ("_ _ SWAP[lib(_), _]\<^sub>_ _ _" [100,100,100,100,100,100,100])
  where "\<sigma>\<^sub>L \<sigma>\<^sub>C SWAP[lib(x), v]\<^sub>t \<sigma>\<^sub>L' \<sigma>\<^sub>C' \<equiv> \<exists> u . lib_update_step t x \<sigma>\<^sub>L \<sigma>\<^sub>C  \<sigma>\<^sub>L' \<sigma>\<^sub>C' u v"

abbreviation  lock_FAE_state_abbr:: "lib_state \<Rightarrow> surrey_state \<Rightarrow> V \<Rightarrow>  L \<Rightarrow>  T \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool" ("_ _ fetch-and-inc[_ \<leftarrow> lib(_)]\<^sub>_ _ _" [100,100,100,100,100,100,100])
  where "\<sigma>\<^sub>L \<sigma>\<^sub>C fetch-and-inc[res \<leftarrow> lib(x)]\<^sub>t \<sigma>\<^sub>L' \<sigma>\<^sub>C' \<equiv> lib_fetch_and_inc_step t x \<sigma>\<^sub>L \<sigma>\<^sub>C  \<sigma>\<^sub>L' \<sigma>\<^sub>C' res"



definition "lib_p_obs \<sigma>\<^sub>L t x u \<equiv> \<exists> w. w \<in> lib_visible_writes \<sigma>\<^sub>L t x \<and> u = lib_value \<sigma>\<^sub>L w" 

definition "lib_d_obs \<sigma>\<^sub>L view x u \<equiv> view x = lib_lastWr \<sigma>\<^sub>L x \<and> lib_value \<sigma>\<^sub>L (lib_lastWr \<sigma>\<^sub>L x) = u"

definition "lib_d_obs_t \<sigma>\<^sub>L t x u \<equiv> lib_d_obs \<sigma>\<^sub>L (lib_thrView \<sigma>\<^sub>L t) x u"

definition "lib_c_obs \<sigma>\<^sub>L \<sigma>\<^sub>C x u t y v \<equiv> 
              \<forall> w \<in> lib_visible_writes \<sigma>\<^sub>L t x. lib_value \<sigma>\<^sub>L w = u \<longrightarrow>
                         d_obs \<sigma>\<^sub>C (lib_modView \<sigma>\<^sub>L w CVARS) y v \<and>
                         lib_releasing \<sigma>\<^sub>L w"

definition "lib_c_obs_lib_only \<sigma> x u t y v \<equiv> 
              \<forall> w \<in> lib_visible_writes \<sigma> t x. lib_value \<sigma> w = u \<longrightarrow>
                         lib_d_obs \<sigma> (lib_modView \<sigma> w LVARS) y v \<and>
                         lib_releasing \<sigma> w"

definition "lib_covered_v \<sigma>\<^sub>L x v \<equiv> 
              \<forall> w .  w \<in> lib_writes_on \<sigma>\<^sub>L x \<and> w \<notin> lib_covered \<sigma>\<^sub>L
                           \<longrightarrow> w = lib_lastWr \<sigma>\<^sub>L x \<and> lib_value \<sigma>\<^sub>L w = v"


definition "lib_p_vorder \<sigma> x u v \<equiv> \<exists> w w'.  w \<in> lib_writes_on \<sigma> x \<and>  w' \<in>lib_writes_on \<sigma> x \<and>
                                        lib_value \<sigma> w = u \<and> lib_value \<sigma> w' = v \<and>
                                        tst w < tst w'"

definition "lib_d_vorder \<sigma> u x v \<equiv> (\<forall> w w'.  w \<in> lib_writes_on \<sigma> x  \<and>  w' \<in> lib_writes_on \<sigma> x \<and>
                                        lib_value \<sigma> w = u \<and> lib_value \<sigma> w' = v \<longrightarrow>
                                        mo w w') \<and> lib_p_vorder \<sigma> u x v"


definition "lib_init_val \<sigma> x v \<equiv> 
  \<exists> w . w \<in> lib_writes_on \<sigma> x \<and> 
        (\<forall> w'\<in> lib_writes_on \<sigma> x .  w \<noteq> w' \<longrightarrow>  tst w < tst w') \<and> 
        lib_value \<sigma> w = v"

definition "lib_amo \<sigma> x u \<equiv> \<not> lib_p_vorder \<sigma> x u u"

definition "lib_no_val \<sigma> x i u \<equiv> lib_init_val \<sigma> x i \<and> \<not> lib_p_vorder \<sigma> x i u"

abbreviation lib_init_abbr:: "L \<Rightarrow> V  \<Rightarrow> lib_state \<Rightarrow> bool" ("[init lib(_) _] _" [100, 100,100])
  where "[init lib(x) v] \<sigma> \<equiv> lib_init_val \<sigma> x v"

abbreviation lib_covered_v_abbr:: "L \<Rightarrow> nat \<Rightarrow> lib_state \<Rightarrow> bool" ("cvd[lib(_), _] _" [100, 100, 100])
  where "cvd[lib(x), u] \<sigma> \<equiv> lib_covered_v \<sigma> x u"

abbreviation lib_dobs_abbr:: "L \<Rightarrow>  T \<Rightarrow> nat \<Rightarrow> lib_state \<Rightarrow> bool" ("[lib(_) =\<^sub>_ _] _" [100, 100, 100])
  where "[lib(x) =\<^sub>t u] \<sigma> \<equiv> lib_d_obs_t \<sigma> t x u"

abbreviation lib_p_obs_abbr:: "L \<Rightarrow> T \<Rightarrow> V \<Rightarrow>  lib_state \<Rightarrow> bool" ("[lib(_) \<approx>\<^sub>_ _] _" [100, 100, 100, 100])
  where "[lib(x) \<approx>\<^sub>t u] \<sigma>\<^sub>L \<equiv> lib_p_obs \<sigma>\<^sub>L t x u"

abbreviation lib_c_obs_abbr:: "L \<Rightarrow> V \<Rightarrow>  L \<Rightarrow> T \<Rightarrow> V \<Rightarrow> lib_state \<Rightarrow> surrey_state \<Rightarrow> bool" ("[lib(_) = _]\<lparr>_ =\<^sub>_ _ \<rparr> _ _" [100, 100, 100,100, 100, 100])
  where "[lib(x) = u]\<lparr>y =\<^sub>t v\<rparr> \<sigma>\<^sub>L \<sigma>\<^sub>C \<equiv> lib_c_obs \<sigma>\<^sub>L \<sigma>\<^sub>C x u t y v"


abbreviation lib_c_obs_lib_only_abbr:: "L \<Rightarrow> V \<Rightarrow>  L \<Rightarrow> T \<Rightarrow> V \<Rightarrow> lib_state  \<Rightarrow> bool" ("[lib(_) = _]\<lparr>lib(_) =\<^sub>_ _ \<rparr> _" [100, 100, 100,100, 100, 100])
  where "[lib(x) = u]\<lparr>lib(y) =\<^sub>t v\<rparr> \<sigma>\<^sub>L \<equiv> lib_c_obs_lib_only \<sigma>\<^sub>L x u t y v"


abbreviation lib_no_abbr:: "L \<Rightarrow> V \<Rightarrow> V \<Rightarrow> lib_state \<Rightarrow> bool" ("[\<zero>lib(_), _]\<^sub>_ _" [100,100,100, 100])
  where "[\<zero>lib(x), u]\<^sub>i \<sigma> \<equiv> lib_no_val \<sigma> x i u"

abbreviation lib_p_vorder_abbr:: "V  \<Rightarrow> L \<Rightarrow> V \<Rightarrow>  lib_state \<Rightarrow> bool" ("[_ lib\<leadsto>\<^sub>_ _] _" [100,100,100,100])
  where "[u lib\<leadsto>\<^sub>x v] \<sigma> \<equiv> lib_p_vorder \<sigma> u x v"

abbreviation lib_d_vorder_abbr:: "V  \<Rightarrow> L \<Rightarrow> V \<Rightarrow>  lib_state \<Rightarrow> bool" ("[_ lib\<hookrightarrow>\<^sub>_ _] _" [100,100,100,100])
  where "[u lib\<hookrightarrow>\<^sub>x v] \<sigma> \<equiv> lib_d_vorder \<sigma> u x v"


definition "lib_enc \<sigma> view x u \<equiv> \<exists> w . w \<in> lib_writes_on \<sigma> x \<and> tst(w) \<le> tst(view x) \<and> lib_value \<sigma> w = u"

definition "lib_enc_t \<sigma> t x u \<equiv>  lib_enc \<sigma> (lib_thrView \<sigma> t) x u"

abbreviation lib_enc_abbr:: "L \<Rightarrow> V \<Rightarrow> T \<Rightarrow> lib_state \<Rightarrow> bool" ("en[lib(_), _]\<^sub>_ _" [100,100,100,100])
  where "en[lib(x), u]\<^sub>t \<sigma> \<equiv> lib_enc_t \<sigma> t x u"

lemmas all_updates_l = lib_add_cv_def lib_update_thrView_def lib_update_modView_def lib_update_mods_def update_thrView_def
lemmas all_updates_c = add_cv_def update_thrView_def update_modView_def update_mods_def


end